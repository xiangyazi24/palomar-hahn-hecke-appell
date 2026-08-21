import Mathlib

/-!
# General Hahn-series coefficientwise Hecke--Appell identity

For arbitrary positive integers `n,p`, this file states the boundary-cleared
coefficient identity from *A Hahn-Series Coefficientwise Proof of the
Hickerson--Mortenson Hecke--Appell Identities*.

The finite residue sums are the two groups of `n` cleared Appell rows. Their
denominators use the signed geometric branch selected by the leading
q-exponent. The correction is stated coefficientwise because, for `n ≥ 2`,
it need not itself belong to the q-first Hahn ring.
-/

namespace PalomarHahnHeckeAppell

open scoped Classical
noncomputable section

/-- Integer sign with the convention `sg(0)=1`. -/
def intSign (z : ℤ) : ℤ := if 0 ≤ z then 1 else -1

/-- The parity sign `(-1)^z` for an integer exponent. -/
def negOnePow (z : ℤ) : ℚ := (-1 : ℚ) ^ z.natAbs

/-- The integral polynomial binomial coefficient `z choose 2`. -/
def chooseTwo (z : ℤ) : ℤ := z * (z - 1) / 2

/-- `p(2n+p)`. -/
def discriminant (n p : ℤ) : ℤ := p * (2 * n + p)

/-- The common theta modulus `np(2n+p)`. -/
def thetaModulus (n p : ℤ) : ℤ := n * discriminant n p

/-- The integral constant `np(2n+p+1)/2` in every Appell row. -/
def rowConstant (n p : ℤ) : ℤ := n * p * (2 * n + p + 1) / 2

/-- The Hecke quadratic exponent for `f_{n,n+p,n}`. -/
def heckeExponent (n p r s : ℤ) : ℤ :=
  n * chooseTwo r + (n + p) * r * s + n * chooseTwo s

/-- Twice the leading q-exponent of a row denominator. -/
def denominatorExponentTwice (n p t k : ℤ) : ℤ :=
  2 * thetaModulus n p * (k - 1) + n * p * (2 * n + p + 1) -
    2 * t * discriminant n p

/-- Coefficient of the signed Hahn geometric branch. -/
def branchCoefficient (gammaTwice ell : ℤ) : ℚ :=
  if 0 < gammaTwice then
    if 0 ≤ ell then 1 else 0
  else if gammaTwice < 0 then
    if ell < 0 then -1 else 0
  else 0

/-- Common exponent of a fixed theta shell. -/
def shellExponent (n p r s w : ℤ) : ℤ :=
  heckeExponent n p r s + thetaModulus n p * chooseTwo (w + 1)

/-- Indicator of the theta shell at q-degree `e`. -/
def shellIndicator (n p e r s w : ℤ) : ℚ :=
  if e = shellExponent n p r s w then 1 else 0

/-- Original q-exponent in one cleared `s`-residue row. -/
def sRowResidueExponent (n p t u ell k : ℤ) : ℤ :=
  n * chooseTwo t + n * chooseTwo u + (n + p) * t * u +
    thetaModulus n p * chooseTwo k +
      ell * (thetaModulus n p * (k - 1) + rowConstant n p -
        t * discriminant n p)

/-- Contribution of residue `t` to the cleared `s`-row coefficient. -/
def sRowResidueKernel (n p e r s t k : ℤ) : ℚ :=
  let ell := (s - t) / n
  let u := r + (n + p) * ell
  if 0 ≤ t ∧ t < n ∧ s = n * ell + t then
    negOnePow (t + u + n * ell - (n + p) * ell) *
      branchCoefficient (denominatorExponentTwice n p t k) ell *
        (if e = sRowResidueExponent n p t u ell k then 1 else 0)
  else 0

/-- Coefficient of all `n` cleared `s`-residue rows. -/
def sRowResidueCoefficient (n p e r s : ℤ) : ℚ :=
  ∑ t ∈ Finset.Icc (0 : ℤ) (n - 1), ∑ᶠ k : ℤ, sRowResidueKernel n p e r s t k

/-- Original q-exponent in one cleared symmetric `r`-residue row. -/
def rRowResidueExponent (n p t v ell k : ℤ) : ℤ :=
  n * chooseTwo t + n * chooseTwo v + (n + p) * t * v +
    thetaModulus n p * chooseTwo k +
      ell * (thetaModulus n p * (k - 1) + rowConstant n p -
        t * discriminant n p)

/-- Contribution of residue `t` to the cleared symmetric `r`-row coefficient. -/
def rRowResidueKernel (n p e r s t k : ℤ) : ℚ :=
  let ell := (r - t) / n
  let v := s + (n + p) * ell
  if 0 ≤ t ∧ t < n ∧ r = n * ell + t then
    negOnePow (t + v + n * ell - (n + p) * ell) *
      branchCoefficient (denominatorExponentTwice n p t k) ell *
        (if e = rRowResidueExponent n p t v ell k then 1 else 0)
  else 0

/-- Coefficient of all `n` cleared symmetric `r`-residue rows. -/
def rRowResidueCoefficient (n p e r s : ℤ) : ℚ :=
  ∑ t ∈ Finset.Icc (0 : ℤ) (n - 1), ∑ᶠ k : ℤ, rRowResidueKernel n p e r s t k

/-- Same-sign cone coefficient in rational form. -/
def sameSignCoefficient (a b : ℤ) : ℚ :=
  ((intSign a + intSign b : ℤ) : ℚ) / 2

/-- Coefficient of the boundary-cleared Hecke sum. -/
def heckeCoefficient (n p e r s : ℤ) : ℚ :=
  ∑ᶠ w : ℤ,
    negOnePow (r + s) * sameSignCoefficient r s *
      shellIndicator n p e r s w

/-- Coefficient function of the wall correction. -/
def thetaCoefficient (n p e r s : ℤ) : ℚ :=
  ∑ᶠ w : ℤ,
    negOnePow (r + s) *
      sameSignCoefficient
        (2 * r + 2 * n * w + n - 1)
        (2 * s - 2 * n * w - n - 1) *
      shellIndicator n p e r s w

/--
For every positive `n,p` and every monomial `q^e x^r y^s`, the coefficient
of the boundary-cleared Hecke sum equals the coefficients of the two finite
families of cleared Appell rows plus the wall correction.
-/
theorem general_boundary_cleared_coefficient
    (n p e r s : ℤ) (hn : 0 < n) (hp : 0 < p) :
    heckeCoefficient n p e r s =
      sRowResidueCoefficient n p e r s + rRowResidueCoefficient n p e r s +
        thetaCoefficient n p e r s := by
  sorry

end
end PalomarHahnHeckeAppell
