import QseriesFormalization.Pending.Chapter10_KroneckerCoeff
import QseriesFormalization.Pending.Chapter10_HMComparison

/-!
# The general Hahn-series Hecke--Appell theorem

This module assembles the two independent parts of
`paper/root-pair-involution/root_pair_note.tex`:

* the general positive-`n,p` coefficient proof of the boundary-cleared
  Hecke--Appell identity; and
* the coefficientwise Kronecker expansion and residue reconstruction that
  identify the boundary term with the printed Hickerson--Mortenson correction.

All statements are coefficientwise.  The development proves local finiteness
for every fixed coefficient and does not assert a global Hahn-support theorem
for the assembled wall family.
-/

namespace QseriesFormalization.Pending.Ch10HahnHeckeAppell

open QseriesFormalization.Pending.Chapter10PF
open QseriesFormalization.Pending.Ch10KroneckerCoeff
open QseriesFormalization.Pending.Ch10GeneralHahnCoeff
open QseriesFormalization.Pending.Ch10HMComparison

/-!
## Main theorem with the printed HM correction
-/

/--
The boundary-cleared Hickerson--Mortenson Hecke--Appell identity for every
positive pair `n,p`, coefficient by coefficient.  The two Appell terms retain
the explicit finite residue families from the printed row decomposition, and
`hmExpandedCoefficient` retains the printed residue variables and all three
bilateral indices after the formally verified Kronecker/Jacobi expansion.
-/
theorem general_boundary_cleared_hm_coefficient
    (n p e r s : ℤ) (hn : 0 < n) (hp : 0 < p) :
    heckeCoefficient n p e r s =
      sRowResidueCoefficient n p e r s + rRowResidueCoefficient n p e r s +
        hmExpandedCoefficient n p e r s := by
  rw [hmExpandedCoefficient_eq_thetaCoefficient n p e r s hn hp]
  exact general_boundary_cleared_residue_coefficient n p e r s hn hp

/--
A single theorem collecting the full formal proof surface of the paper:
Kronecker partial fractions, the Jacobi-cube PF identity, and the general
positive-`n,p` Hecke--Appell coefficient identity with HM's printed correction.
-/
theorem hahn_hecke_appell_full_certificate :
    (∀ E A B : ℤ,
      jMulKroneckerCoeff E A B =
        negOnePowIntPF ℤ B * pfCoeff (E - triIntPF (B - 1)) (A - B)) ∧
    thetaMulPFSeriesCoeffPF = qPochInfPSCubeUPowerCoeffPF ∧
    (∀ n p e r s : ℤ, 0 < n → 0 < p →
      heckeCoefficient n p e r s =
        sRowResidueCoefficient n p e r s + rRowResidueCoefficient n p e r s +
          hmExpandedCoefficient n p e r s) := by
  constructor
  · exact kronecker_partial_fraction_cleared_coefficient
  constructor
  · exact thetaMul_PF_eq_qPochInfPS_pow_three
  · intro n p e r s hn hp
    exact general_boundary_cleared_hm_coefficient n p e r s hn hp

end QseriesFormalization.Pending.Ch10HahnHeckeAppell
