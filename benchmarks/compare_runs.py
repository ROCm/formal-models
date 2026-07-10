#!/usr/bin/env python3
"""Compare benchmark CSV results to a baseline CSV, reporting median duration changes."""

# TODO There is potential to do more statistically meaningful things here.

import argparse
import csv
import sys
from collections import defaultdict
from statistics import median

import logging

logger = logging.getLogger(__name__)


def read_median_durations(path, epsilon=0.0):
    """
    Read CSV and return dict: alloy_file -> median(duration_secs)
    over successful repetitions.
    Skips any alloy_file/solver combination where any individual run differs
    from the median by at least epsilon (relative fraction).
    """
    num_failed_to_parse = 0
    num_invalid = 0
    data = defaultdict(list)
    try:
        with open(path) as f:
            reader = csv.DictReader(f)
            for row in reader:
                # Tolerate missing fields.
                alloy_file = (
                    row.get("alloy_file") or row.get("alloyfile") or row.get("file")
                )
                solver = row.get("solver") or ""
                dur = row.get("duration_secs")
                success = row.get("success", "True")
                if not alloy_file or dur is None:
                    num_failed_to_parse += 1
                    continue
                # Accept common truthy success markers.
                if str(success).lower() not in ("true", "1", "yes", "y", "t"):
                    num_invalid += 1
                    continue
                try:
                    d = float(dur)
                except ValueError:
                    num_failed_to_parse += 1
                    continue
                # key = (alloy_file, solver)
                key = alloy_file
                data[key].append(d)
    except FileNotFoundError:
        logger.error(f"file not found: {path}")
        sys.exit(2)

    num_unstable = 0
    # Compute medians, and skip configs with outliers relative to the median.
    medians = {}
    for k, vals in data.items():
        if not vals:
            continue
        m = median(vals)
        skip = False
        if epsilon > 0.0:
            for v in vals:
                if m == 0.0:
                    if v != 0.0:
                        num_unstable += 1
                        logger.debug(
                            f"skipping {format_key(k)} because run value {v:.6f}s differs from median {m:.6f}s"
                        )
                        skip = True
                else:
                    rel = abs(v - m) / m
                    if rel >= epsilon:
                        num_unstable += 1
                        logger.debug(
                            f"skipping {format_key(k)} because run value {v:.6f}s differs from median {m:.6f}s by {rel:.1%} >= {epsilon:.1%}"
                        )
                        skip = True
        if not skip:
            medians[k] = m

    error_msgs = []
    if num_failed_to_parse > 0:
        error_msgs.append(f"  - failed to parse {num_failed_to_parse} rows")
    if num_invalid > 0:
        error_msgs.append(f"  - skipped {num_invalid} rows with unsuccessful runs")
    if num_unstable > 0:
        error_msgs.append(
            f"  - skipped {num_unstable} unstable configs that differed from median by >= {epsilon:.1%}"
        )

    if error_msgs:
        logger.warning(f"while reading '{path}':\n" + "\n".join(error_msgs))

    return medians


def format_change(base, cur):
    if base == 0:
        return "base=0 -> change=inf"
    pct = (cur - base) / base * 100.0
    return f"{pct:+.1f}%"


def format_key(k, common_prefix=None):
    if isinstance(k, tuple):
        alloy_file = k[0]
        other_parts = k[1:]
    else:
        alloy_file = k
        other_parts = []

    if common_prefix and alloy_file.startswith(common_prefix):
        alloy_file = alloy_file[len(common_prefix) :]
    parts = [alloy_file] + other_parts
    return "|".join(parts)


def main():
    default_loglevel = "info"
    loglevels = ["debug", "info", "warning", "error"]

    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("contender", help="CSV file for contender run")
    ap.add_argument("-b", "--baseline", required=True, help="CSV file for baseline run")
    ap.add_argument(
        "--epsilon",
        type=float,
        default=0.05,
        help="relative threshold (fraction) to report differences and to require for reporting (e.g. 0.05 = 5%%).",
    )
    ap.add_argument(
        "-l",
        "--loglevel",
        choices=loglevels,
        default=default_loglevel,
        help="configures the amount of logging information to print",
    )
    args = ap.parse_args()

    # Init logging
    loglevel = args.loglevel
    numeric_level = getattr(logging, loglevel.upper(), None)
    if not isinstance(numeric_level, int):
        raise ValueError("Invalid log level: {}".format(loglevel))

    logging.basicConfig(
        format="%(asctime)s - %(levelname)s:%(name)s: %(message)s", level=numeric_level
    )

    contender = read_median_durations(args.contender, epsilon=args.epsilon)
    base = read_median_durations(args.baseline, epsilon=args.epsilon)

    all_alloy_files = set(k if isinstance(k, str) else k[0] for k in contender.keys())
    all_alloy_files |= set(k if isinstance(k, str) else k[0] for k in base.keys())
    common_prefix = None
    for f in all_alloy_files:
        prefix_parts = f.split("/")[:-1]
        if common_prefix is None:
            common_prefix = prefix_parts
        else:
            # Update common prefix
            new_prefix = []
            for p1, p2 in zip(common_prefix, prefix_parts):
                if p1 == p2:
                    new_prefix.append(p1)
                else:
                    break
            common_prefix = new_prefix
    common_prefix_str = "/".join(common_prefix) + "/" if common_prefix else ""

    only_contender = sorted(set(contender) - set(base))
    only_base = sorted(set(base) - set(contender))
    common = sorted(set(contender) & set(base))

    faster = []
    slower = []
    for k in common:
        baseline_v = base[k]
        contender_v = contender[k]
        if baseline_v == 0:
            if contender_v == 0:
                continue
            else:
                slower.append((float("inf"), k, baseline_v, contender_v))
                continue
        rel_difference = (contender_v - baseline_v) / baseline_v
        # require magnitude >= epsilon to report
        if rel_difference <= -args.epsilon:
            faster.append((rel_difference, k, baseline_v, contender_v))
        elif rel_difference >= args.epsilon:
            slower.append((rel_difference, k, baseline_v, contender_v))

    # sort: biggest improvements first (most negative), biggest regressions first
    faster.sort(key=lambda x: x[0])  # most negative first
    slower.sort(key=lambda x: -x[0])  # largest positive first

    print(f"baseline file: {args.baseline}")
    print(f"contender file: {args.contender}")
    print(f"epsilon: {args.epsilon}")
    print()
    print(f"Common tests: {len(common)}")
    print(f"Faster: {len(faster)}")
    print(f"Slower: {len(slower)}")
    print(f"Only in contender: {len(only_contender)}")
    print(f"Only in baseline: {len(only_base)}")
    print()

    if faster:
        print("Faster (contender < baseline):")
        for pct, k, bv, cv in faster:
            disp = format_change(bv, cv)
            print(
                f"{format_key(k, common_prefix=common_prefix_str)}:  baseline={bv:.3f}s  contender={cv:.3f}s  ({disp})"
            )
        print()

    if slower:
        print("Slower (contender > baseline):")
        for pct, k, bv, cv in slower:
            disp = format_change(bv, cv)
            print(
                f"{format_key(k, common_prefix=common_prefix_str)}:  baseline={bv:.3f}s  contender={cv:.3f}s  ({disp})"
            )
        print()

    if only_contender:
        print("Only in contender run (no baseline):")
        for k in only_contender:
            print(
                f"{format_key(k, common_prefix=common_prefix_str)}:  contender={contender[k]:.3f}s"
            )
        print()

    if only_base:
        print("Only in baseline (missing in contender run):")
        for k in only_base:
            print(
                f"{format_key(k, common_prefix=common_prefix_str)}:  baseline={base[k]:.3f}s"
            )
        print()


if __name__ == "__main__":
    main()
