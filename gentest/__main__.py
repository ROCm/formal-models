"""Entry point for the memory consistency test generator CLI.

Usage (in top-level directory):
    python -m gentest <general args> <model> <model args>
"""

import sys

from gentest.cli import main

if __name__ == "__main__":
    sys.exit(main())
