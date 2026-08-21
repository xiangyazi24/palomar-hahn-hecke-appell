# Hahn-series Hecke--Appell formalization

This is a local pre-submission repository for a possible
[Palomar](https://palomar-registry.org/) entry associated with
*A Hahn-Series Coefficientwise Proof of the Hickerson--Mortenson
Hecke--Appell Identities*.

The repository is self-contained apart from its pinned Mathlib dependency. It
extracts only the 36 Lean modules needed for:

- the fully verified `f_{2,3,2}` Hecke--Appell identity; and
- the general row-exponent, branch-sign, parity, and wall-involution mechanism.

The full general `(n,p)` Hecke--Appell assembly in the paper is not formalized.
The extracted development is synchronized from the internal Q-series source at
commit `fb10c7090cc9617c078c66002a3fd725d8a0f9cd`.

## Current state

The present `Challenge.lean` advertises only the general row-exponent identity.
It is a packaging and Comparator test, not yet the intended final registry
entry. Before submission, the Challenge must expose the mathematically
substantive `f_{2,3,2}` identity or the public description must be narrowed to
the declarations actually compared.

## Repository map

- `Challenge.lean`: small Mathlib-only statement surface.
- `Solution.lean`: matching declaration proved from the extracted development.
- `QseriesFormalization/`: substantive proof dependency closure.
- `comparator.json`: declarations and permitted axioms checked by Comparator.
- `formalization.yaml`: scope, provenance, automation, fidelity, and review.

## Verification

Run the full checks on Linux:

```text
lake exe cache get
lake build
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

The final fixed commit is submitted through
[Palomar's submission form](https://submit.palomar-registry.org/). No Palomar
account is needed; the form authenticates through a GitHub account with write
access to the public repository.
