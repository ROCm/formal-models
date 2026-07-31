# Contributing to formal-models

Thanks for your interest in contributing.

**Security vulnerabilities — do not open a public GitHub Issue.** See [SECURITY.md](SECURITY.md) for the private reporting process.

For setup details, workflows, and CLI usage, see [README.md](README.md).

## Reporting Issues

Use [GitHub Issues](../../issues) to report bugs or request features.

Please include:

- A clear description of the problem or requested behaviour
- Steps to reproduce (commands, scripts, or config files)
- **formal-models revision** and **LLVM revision** (if applicable):
  - formal-models: commit hash or tag (for example `git rev-parse HEAD` in your formal-models checkout)
  - LLVM: commit hash, tag, or PR number (for example `git rev-parse HEAD` in your `llvm-project` checkout, or the Docker image tag if you used one)
- Your environment:
  - OS, Java and Python versions
- Relevant logs or output files

Search existing issues before opening a new one. If your report matches an open issue, add a comment there instead of filing a duplicate.

## Pull requests

When you create a pull request, target the **`main`** branch.

1. Identify the issue you want to address (open a [GitHub Issue](../../issues) first if one does not exist).
2. Create a branch from `main`, make your changes, and run the relevant tests locally. Follow the [coding guidelines](./docs/coding-guidelines.md).
3. Target the **`main`** branch when opening the pull request.
4. Ensure all CI workflows pass. Pull requests run security scans (gitleaks, zizmor, bandit, and trivy).
5. Submit your PR and work with the reviewer or maintainer to get it approved.

Keep changes focused and update [README.md](README.md) when you change user-facing behaviour. Do not commit generated artifacts, large corpora, or local build trees.

By submitting a pull request, you agree that your contribution is licensed under the terms of [LICENCE.txt](LICENCE.txt) (Apache License v2.0 with LLVM Exceptions).
