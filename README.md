# Hahn-series Hecke--Appell formalization

This repository prepares a
[Palomar](https://palomar-registry.org/) entry associated with
*A Hahn-Series Coefficientwise Proof of the Hickerson--Mortenson
Hecke--Appell Identities*.

The repository is self-contained apart from its pinned Mathlib dependency. It
extracts two substantive Lean modules from the private Q-series development:
the general root-pair algebra and the general coefficientwise Hahn proof. The
source snapshot is synchronized from private commit
`636a293`.

## Registered statement surface

`Challenge.lean` states the general coefficientwise boundary-cleared identity
for every positive pair `(n,p)` and every exponent triple `(e,r,s)`. It equates
the Hecke coefficient with the two finite families of cleared Appell residue
rows plus the wall correction. The signed Hahn branch, original residue-row
exponents, and correction coefficient are all explicit in the Challenge.

The statement is coefficientwise by design. For `n ≥ 2`, the wall correction
need not itself be an element of the q-first Hahn ring, while every fixed
coefficient is a finite sum.

## Repository map

- `Challenge.lean`: small Mathlib-only statement surface.
- `Solution.lean`: matching declaration proved from the extracted development.
- `QseriesFormalization/`: the two-module substantive proof.
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
