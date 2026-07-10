.PHONY: format check check-gentest check-% install-dev

format:
	black $(shell git ls-files "*.py")

mypy:
	mypy $(shell git ls-files "*.py")

mypy-strict:
	mypy --strict $(shell git ls-files "*.py")

check-gentest:
	pytest gentest/test.py
	pytest gentest/test_amdgpu.py

check-%:
	llvm-lit -v $*/test

check:
	$(MAKE) check-gentest
	$(MAKE) check-llvm

install-dev:
	python3 -m pip install -r gentest/requirements-dev.txt
