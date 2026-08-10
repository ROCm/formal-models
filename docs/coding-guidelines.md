# Coding Guidelines

## Alloy

### Documentation

- Add comments to document what signatures, relations, facts, and predicates encode.
- When a constraint encodes a rule from an external specification, cite the source.

### Formatting

- Indent with 2 spaces; no tabs.
- Wrap comment lines within 80 columns.
- Keep expression lines reasonably short, wrap to improve readability.

### Naming

- Prefer descriptive identifiers, especially for non-standard concepts (e.g., `compatible_scope` rather than `cs`).
- Use UpperCamelCase for identifiers for sets/unary relations (independent of whether they are `sig`s or `fun`s without parameters).
- Use snake_case for identifiers for anything else: relations with arity 2 or higher, `fun`s with parameters, `pred`s, `fact`s, `run` commands, module names.


## Python

Follow [PEP 8](https://peps.python.org/pep-0008/), use [black](https://pypi.org/project/black/) (e.g., via `make format`) to format.
Add type annotations where reasonable and check them with [mypy](https://mypy-lang.org/) (e.g., via `make mypy`).
