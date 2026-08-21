# Hahn-series Hecke--Appell formalization

This repository prepares a
[Palomar](https://palomar-registry.org/) entry associated with
*A Hahn-Series Coefficientwise Proof of the Hickerson--Mortenson
Hecke--Appell Identities*.

The repository is self-contained apart from its pinned Mathlib dependency. It
contains the exact transitive source closure of the proof extracted from the
canonical internal Q-series development, together with the signed paper
snapshot in `paper/`.

## Registered statement surface

`Challenge.lean` states two results. The first is the cleared coefficientwise
Kronecker partial-fraction identity used in Appendix A. The second is the
general boundary-cleared identity for every positive pair `(n,p)` and every
exponent triple `(e,r,s)`: it equates the Hecke coefficient with the two finite
families of cleared Appell residue rows plus the source-expanded printed
Hickerson--Mortenson correction. The signed Hahn branch, original residue-row
exponents, finite HM residue variables, and all three bilateral indices are
explicit in the Challenge.

The statement is coefficientwise by design. Every fixed coefficient is a
finite sum. The formalization does not claim a global well-ordered-support
theorem or a series-valued Hahn wrapper for the assembled wall family.

The registered coefficient functions are `ℚ`-valued. The paper's displayed
kernels are integer-valued, but integrality and general-ring base change are
not separate registered Lean theorems.

## Repository map

- `Challenge.lean`: small Mathlib-only statement surface.
- `Solution.lean`: matching declaration proved from the extracted development.
- `QseriesFormalization/`: the exact 19-file substantive proof-and-audit closure.
- `paper/`: signed TeX source, bibliography, and compiled PDF.
- `comparator.json`: declarations and permitted axioms checked by Comparator.
- `formalization.yaml`: scope, provenance, automation, fidelity, and review.

This standalone repository and its fixed commit are the authoritative public
source for the Palomar entry; no external development repository is needed to
reconstruct the registered proof.

## Verification

Run the full checks on Linux:

```text
lake exe cache get
lake build
ruby scripts/validate-formalization.rb
./test/landrun_wrapper_test.sh
./test/validate_formalization_test.rb
./scripts/verify-comparator.sh
```

The final fixed commit is submitted through
[Palomar's submission form](https://submit.palomar-registry.org/). No Palomar
account is needed; the form authenticates through a GitHub account with write
access to the public repository.
