#!/bin/sh

# The steps in this script need to be performed once to set up the Alloy
# analyzer.

set -e

# Cleanup build directory
rm -rf build
mkdir build
cd build

# Download Alloy jar
echo "Downloading Alloy"
wget -q https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v6.2.0/org.alloytools.alloy.dist.jar

# Check for additional requirements
if ! command -v java >/dev/null 2>&1; then
  echo 'Warning: java is not installed. It is required to run the Alloy analyzer.'
fi

if ! command -v python3 >/dev/null 2>&1; then
  echo 'Warning: python3 is not installed. It is required to use the domain-specific language for litmus test.'
fi

if ! command -v llvm-lit >/dev/null 2>&1; then
  echo 'Warning: llvm-lit is not installed. It is required to run the test suite.'
fi

