import Mathlib
import QseriesFormalization.Chapter03
import QseriesFormalization.Chapter04_T43
import QseriesFormalization.Chapter19_JacobiTripleSignChar
import QseriesFormalization.Pending.JacobiCubeAnalyticToFormal
import QseriesFormalization.Pending.JTP_FormalPS_Pentagonal
import QseriesFormalization.Chapter19

/-!
# Chapter 10 PF: coefficient core for the partial-fraction theta expansion

This file is deliberately independent of `Pending/Chapter10_HM.lean`.

The partial-fraction identity

`∑ k, (-1)^k q^(k(k+1)/2) / (1 - q^k u) = J^3 / j(u;q)`

is most naturally read in the lexicographic Hahn/annulus expansion where
`q` is the primary valuation and `u` is the secondary one.  The local inverse
of `1 - q^k u` then uses the positive `u` branch for `k ≥ 0` and the negative
`u` branch for `k < 0`.

The fully formal Hahn-series equality still needs a reusable two-variable
Hahn support wrapper.  The closed lemmas below prove the algebraic coefficient
core used by that wrapper:

* the branch coefficients really invert `1 - q^k u`;
* the `u^0` coefficient of `j(u;q)` times the partial-fraction side is the
  Jacobi cube coefficient `(-1)^h(2h+1)` at triangular exponents.

The final section connects these coefficient formulas to the repository's
formal Jacobi cube identity, so the right-hand side is the actual
`(qPochInfPS ℤ)^3`.
-/

namespace QseriesFormalization
namespace Pending
namespace Chapter10PF

open Finset
open PowerSeries

/-! ## Local theta and q-Pochhammer shells -/

/-- Local copy of `(q;q)_∞`, mirrored from Chapter 19 without importing HM code. -/
noncomputable def qPochPF (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.invOfUnit (QseriesFormalization.PartIV.Ch19.partitionGenFun R) 1

theorem qPochPF_eq_qPochInfPS (R : Type*) [CommRing R] :
    qPochPF R = QseriesFormalization.PartIV.Ch19.qPochInfPS R := rfl

/-- `(-1)^n` for an integer exponent, represented with `natAbs`. -/
def negOnePowIntPF (R : Type*) [CommRing R] (n : ℤ) : R :=
  (-1 : R) ^ n.natAbs

/-- The exponent `n(n-1)/2` in `j(u;q)`. -/
def jExpPF (n : ℤ) : ℕ :=
  (n * (n - 1) / 2).toNat

/-- The exponent `k(k+1)/2` in the partial-fraction numerator. -/
def pfNumExpPF (k : ℤ) : ℕ :=
  (k * (k + 1) / 2).toNat

/--
Coefficient definition of `j(u;q) = ∑_n (-1)^n q^(n(n-1)/2) u^n`.

`jCoeffPF N r` is the coefficient of `q^N u^r`.
-/
def jCoeffPF (N : ℕ) (r : ℤ) : ℤ :=
  if jExpPF r = N then negOnePowIntPF ℤ r else 0

/-- The actual coefficient of `q^N u^r` in `j(u;q) = ∑_r (-1)^r q^(r(r-1)/2)u^r`. -/
def jacobiThetaCoeffPF (N : ℕ) (r : ℤ) : ℤ :=
  if jExpPF r = N then negOnePowIntPF ℤ r else 0

theorem jCoeffPF_eq_jacobiThetaCoeffPF (N : ℕ) (r : ℤ) :
    jCoeffPF N r = jacobiThetaCoeffPF N r := rfl

/-- The `q`-series coefficient family of the actual theta series at fixed `u^r`. -/
noncomputable def jacobiThetaUPowerCoeffPF (r : ℤ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun N => jacobiThetaCoeffPF N r

@[simp] theorem coeff_jacobiThetaUPowerCoeffPF (N : ℕ) (r : ℤ) :
    (jacobiThetaUPowerCoeffPF r).coeff N = jCoeffPF N r := by
  simp [jacobiThetaUPowerCoeffPF, jacobiThetaCoeffPF, jCoeffPF]

@[simp] theorem jCoeffPF_of_exp {N : ℕ} {r : ℤ} (h : jExpPF r = N) :
    jCoeffPF N r = negOnePowIntPF ℤ r := by
  simp [jCoeffPF, h]

@[simp] theorem jCoeffPF_of_ne_exp {N : ℕ} {r : ℤ} (h : jExpPF r ≠ N) :
    jCoeffPF N r = 0 := by
  simp [jCoeffPF, h]

theorem negOnePowIntPF_eq_negOnePow (n : ℤ) :
    negOnePowIntPF ℤ n = (n.negOnePow : ℤ) := by
  unfold negOnePowIntPF
  rw [← Int.coe_negOnePow_natCast n.natAbs]
  simp

theorem negOnePowIntPF_add_eq_sub (h : ℕ) (z : ℤ) :
    negOnePowIntPF ℤ ((h : ℤ) + z) =
      negOnePowIntPF ℤ ((h : ℤ) - z) := by
  rw [negOnePowIntPF_eq_negOnePow, negOnePowIntPF_eq_negOnePow]
  congr 1
  rw [Int.negOnePow_eq_iff]
  have heq : (h : ℤ) + z - ((h : ℤ) - z) = 2 * z := by ring
  rw [heq]
  exact ⟨z, by ring⟩

theorem negOnePowIntPF_add (m n : ℤ) :
    negOnePowIntPF ℤ (m + n) =
      negOnePowIntPF ℤ m * negOnePowIntPF ℤ n := by
  rw [negOnePowIntPF_eq_negOnePow, negOnePowIntPF_eq_negOnePow,
    negOnePowIntPF_eq_negOnePow]
  rw [Int.negOnePow_add]
  norm_num

theorem negOnePowIntPF_eq_of_even_sub {m n : ℤ} (h : Even (m - n)) :
    negOnePowIntPF ℤ m = negOnePowIntPF ℤ n := by
  rw [negOnePowIntPF_eq_negOnePow, negOnePowIntPF_eq_negOnePow]
  exact_mod_cast ((Int.negOnePow_eq_iff m n).mpr h)

/-! ## Valuation-compatible inverse branches for `1 - q^k u` -/

/--
The `u^m` coefficient of the lexicographic branch of `(1 - q^k u)⁻¹`,
with the accompanying `q` exponent forced to be `k*m`.

For `k ≥ 0` this is `∑_{m≥0} q^(k m) u^m`; for `k < 0` this is
`-∑_{m<0} q^(k m) u^m`.
-/
def branchInvCoeffPF (k m : ℤ) : ℤ :=
  if 0 ≤ k ∧ 0 ≤ m then 1
  else if k < 0 ∧ m < 0 then -1
  else 0

/-- Coefficient of `q^a u^b` in the branch inverse of `1 - q^k u`. -/
def branchInvCoeffAtPF (k a b : ℤ) : ℤ :=
  if 0 ≤ k then
    if 0 ≤ b ∧ a = k * b then 1 else 0
  else
    if b < 0 ∧ a = k * b then -1 else 0

theorem branchInvCoeffPF_eq_branchInvCoeffAtPF (k m : ℤ) :
    branchInvCoeffPF k m = branchInvCoeffAtPF k (k * m) m := by
  by_cases hk : 0 ≤ k
  · by_cases hm : 0 ≤ m
    · simp [branchInvCoeffPF, branchInvCoeffAtPF, hk, hm]
    · have hm_neg : m < 0 := by omega
      have hk_not_lt : ¬ k < 0 := by omega
      simp [branchInvCoeffPF, branchInvCoeffAtPF, hk, hm, hm_neg, hk_not_lt]
  · have hklt : k < 0 := by omega
    by_cases hm : m < 0
    · simp [branchInvCoeffPF, branchInvCoeffAtPF, hk, hklt, hm]
    · have hm_nonneg : 0 ≤ m := by omega
      simp [branchInvCoeffPF, branchInvCoeffAtPF, hk, hklt, hm, hm_nonneg]

@[simp] theorem branchInvCoeffPF_nonneg {k m : ℤ} (hk : 0 ≤ k) (hm : 0 ≤ m) :
    branchInvCoeffPF k m = 1 := by
  simp [branchInvCoeffPF, hk, hm]

@[simp] theorem branchInvCoeffPF_neg {k m : ℤ} (hk : k < 0) (hm : m < 0) :
    branchInvCoeffPF k m = -1 := by
  simp [branchInvCoeffPF, not_le_of_gt hk, hk, hm]

@[simp] theorem branchInvCoeffAtPF_zero_of_nonneg (k : ℤ) (hk : 0 ≤ k) :
    branchInvCoeffAtPF k 0 0 = 1 := by
  simp [branchInvCoeffAtPF, hk]

theorem branchInvCoeffAtPF_sub_cancel_of_nonneg
    {k a b : ℤ} (hk : 0 ≤ k) (hb : 1 ≤ b) :
    branchInvCoeffAtPF k a b - branchInvCoeffAtPF k (a - k) (b - 1) = 0 := by
  by_cases ha : a = k * b
  · have hkb : k * b - k = k * (b - 1) := by ring
    have hb0 : 0 ≤ b := by omega
    have hb10 : 0 ≤ b - 1 := by omega
    simp [branchInvCoeffAtPF, ha, hkb, hk, hb, hb0]
  · have ha' : a - k ≠ k * (b - 1) := by
      intro h
      apply ha
      calc
        a = (a - k) + k := by ring
        _ = k * (b - 1) + k := by rw [h]
        _ = k * b := by ring
    simp [branchInvCoeffAtPF, ha, ha']

theorem branchInvCoeffAtPF_sub_cancel_of_neg
    {k a b : ℤ} (hk : k < 0) (hb : b < 0) :
    branchInvCoeffAtPF k a b - branchInvCoeffAtPF k (a - k) (b - 1) = 0 := by
  by_cases ha : a = k * b
  · have hkb : k * b - k = k * (b - 1) := by ring
    have hb1 : b - 1 < 0 := by omega
    have hkn : ¬ 0 ≤ k := by omega
    simp [branchInvCoeffAtPF, ha, hkb, hkn, hb, hb1]
  · have ha' : a - k ≠ k * (b - 1) := by
      intro h
      apply ha
      calc
        a = (a - k) + k := by ring
        _ = k * (b - 1) + k := by rw [h]
        _ = k * b := by ring
    simp [branchInvCoeffAtPF, ha, ha']

/--
Coefficient-level inverse statement for the valuation-compatible branch:

`(1 - q^k u) * branchInv(k) = 1`.
-/
theorem denom_mul_branchInvCoeffAtPF (k a b : ℤ) :
    branchInvCoeffAtPF k a b - branchInvCoeffAtPF k (a - k) (b - 1) =
      if a = 0 ∧ b = 0 then 1 else 0 := by
  by_cases hk : 0 ≤ k
  · by_cases hb0 : b = 0
    · subst b
      by_cases ha0 : a = 0
      · subst a
        simp [branchInvCoeffAtPF, hk]
      · simp [branchInvCoeffAtPF, hk, ha0]
    · by_cases hbpos : 0 < b
      · have hb_nonneg : 0 ≤ b := by omega
        have hbge1 : 1 ≤ b := by omega
        rw [branchInvCoeffAtPF_sub_cancel_of_nonneg hk hbge1]
        simp [hb0]
      · have hbneg : b < 0 := by omega
        have hb_not_nonneg : ¬ 0 ≤ b := by omega
        have hb_pred_not_nonneg : ¬ 0 ≤ b - 1 := by omega
        have hb_not_one_le : ¬ 1 ≤ b := by omega
        simp [branchInvCoeffAtPF, hk, hb_not_nonneg, hb_not_one_le, hb0]
  · have hkn : ¬ 0 ≤ k := hk
    by_cases hb0 : b = 0
    · subst b
      by_cases ha0 : a = 0
      · subst a
        simp [branchInvCoeffAtPF, hkn]
      · have ha' : a - k ≠ k * (-1 : ℤ) := by
          intro h
          apply ha0
          omega
        simp [branchInvCoeffAtPF, hkn, ha0]
    · by_cases hbneg : b < 0
      · have hb_pred_neg : b - 1 < 0 := by omega
        have hklt : k < 0 := by omega
        rw [branchInvCoeffAtPF_sub_cancel_of_neg hklt hbneg]
        simp [hb0]
      · have hbpos : 0 < b := by omega
        have hb_not_neg : ¬ b < 0 := by omega
        have hb_pred_not_neg : ¬ b - 1 < 0 := by omega
        simp [branchInvCoeffAtPF, hkn, hb_not_neg, hb_pred_not_neg, hb0]

/-! ## The constant coefficient of `j` times the PF side -/

/-- Triangular exponent `h(h+1)/2`, i.e. the Jacobi cube support. -/
def triPF (h : ℕ) : ℕ :=
  h * (h + 1) / 2

/--
Compressed `u^0` coefficient of `j(u;q)` times the PF side at `q^N`.

The first summand is the `k ≥ 0, n ≤ 0` branch: for fixed `h=s+k` it has
`h+1` contributions.  The second is the `k < 0, n > 0` branch: for fixed
`h=a+b-1` it has `h` contributions.
-/
def thetaMulPFConstCoeffPF (N : ℕ) : ℤ :=
  (∑ h ∈ Finset.range (N + 1),
      ((h + 1 : ℕ) : ℤ) * if triPF h = N then (-1 : ℤ) ^ h else 0) +
    ∑ h ∈ Finset.range (N + 1),
      (h : ℤ) * if triPF h = N then (-1 : ℤ) ^ h else 0

/-- The Jacobi cube coefficient `∑_h (-1)^h(2h+1) q^(h(h+1)/2)`. -/
def jacobiCubeCoeffPF (N : ℕ) : ℤ :=
  ∑ h ∈ Finset.range (N + 1),
    if triPF h = N then (-1 : ℤ) ^ h * (2 * (h : ℤ) + 1) else 0

theorem thetaMulPFConstCoeffPF_eq_jacobiCubeCoeffPF (N : ℕ) :
    thetaMulPFConstCoeffPF N = jacobiCubeCoeffPF N := by
  unfold thetaMulPFConstCoeffPF jacobiCubeCoeffPF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro h _hh
  by_cases ht : triPF h = N
  · simp [ht]
    ring
  · simp [ht]

/-- First PF branch count: the antidiagonal `s+k=h` has `h+1` points. -/
theorem firstBranchMultiplicityPF (h : ℕ) :
    ((Finset.antidiagonal h).card : ℤ) = (h + 1 : ℕ) := by
  rw [Finset.Nat.card_antidiagonal]

/-! ## Full `u`-coefficient bookkeeping for the cleared PF product -/

/-- Integer triangular exponent `r(r+1)/2`, used after the PF reindexing. -/
def triIntPF (r : ℤ) : ℤ :=
  r * (r + 1) / 2

/-- Integer q-exponent `r(r-1)/2` in the raw theta factor. -/
def jExpIntPF (r : ℤ) : ℤ :=
  triIntPF (r - 1)

/-- Integer q-exponent `k(k+1)/2` in the raw PF numerator. -/
def pfNumExpIntPF (k : ℤ) : ℤ :=
  triIntPF k

@[simp] theorem triIntPF_natCast (h : ℕ) :
    triIntPF (h : ℤ) = (triPF h : ℤ) := by
  unfold triIntPF triPF
  norm_num

theorem two_mul_triIntPF (r : ℤ) :
    2 * triIntPF r = r * (r + 1) := by
  unfold triIntPF
  rw [mul_comm]
  exact Int.ediv_mul_cancel (Int.two_dvd_mul_add_one r)

theorem triIntPF_add_eq_sub_add (h z : ℤ) :
    triIntPF (h + z) = triIntPF (h - z) + z * (2 * h + 1) := by
  apply (mul_right_injective₀ (show (2 : ℤ) ≠ 0 by norm_num))
  change 2 * triIntPF (h + z) =
    2 * (triIntPF (h - z) + z * (2 * h + 1))
  rw [mul_add, two_mul_triIntPF, two_mul_triIntPF]
  ring

/--
Finite window for the coefficient formulas below.

For `z = 0` this is exactly the old Jacobi-cube window.  For `z ≠ 0` it is
large enough for the valuation-branch coefficient at q-degree `N`; proving
window-independence is part of the remaining lattice cancellation step.
-/
def thetaMulPFWindowPF (N : ℕ) (z : ℤ) : ℕ :=
  if z = 0 then N + 1 else N + z.natAbs + 2

/--
The `k ≥ 0, m ≥ 0` valuation branch of the coefficient of
`j(u;q) * PF(u)` at `q^N u^z`.

With `h = k + m`, the q-exponent is
`T_{h-z} + k z`, and the sign is `(-1)^(h-z)`.
-/
def thetaMulPFPositiveCoeffPF (N : ℕ) (z : ℤ) : ℤ :=
  ∑ h ∈ Finset.range (thetaMulPFWindowPF N z),
    ∑ k ∈ Finset.range (h + 1),
      if triIntPF ((h : ℤ) - z) + (k : ℤ) * z = (N : ℤ) then
        negOnePowIntPF ℤ ((h : ℤ) - z)
      else
        0

/--
The `k < 0, m < 0` valuation branch of the coefficient of
`j(u;q) * PF(u)` at `q^N u^z`.

Writing `k = -c-1`, `m = -s-1`, and `h = c+s+1`, the q-exponent is
`T_{h+z} - (c+1)z`, and the branch sign included with the theta signs is
`(-1)^(h+z)`.
-/
def thetaMulPFNegativeCoeffPF (N : ℕ) (z : ℤ) : ℤ :=
  ∑ h ∈ Finset.range (thetaMulPFWindowPF N z),
    ∑ c ∈ Finset.range h,
      if triIntPF ((h : ℤ) + z) - ((c : ℤ) + 1) * z = (N : ℤ) then
        negOnePowIntPF ℤ ((h : ℤ) + z)
      else
        0

/-- Full finite coefficient model for `j(u;q) * PF(u)` at `q^N u^z`. -/
def thetaMulPFCoeffPF (N : ℕ) (z : ℤ) : ℤ :=
  thetaMulPFPositiveCoeffPF N z + thetaMulPFNegativeCoeffPF N z

/-! ### Raw branch-window bridge

The following definitions keep the one-denominator inverse coefficient
`branchInvCoeffAtPF` visible.  They are the raw form needed by the HM-side
finite Appell numerator before the positive/negative branch sums are
compressed by the `h = k + m` and `k = -c - 1, m = c - h` reindexings.
-/

/-- One raw summand of `j(u;q) * PF(u;q)` at `q^N u^z`. -/
def thetaMulPFRawBranchTermPF (N : ℕ) (z k r : ℤ) : ℤ :=
  negOnePowIntPF ℤ r * negOnePowIntPF ℤ k *
    branchInvCoeffAtPF k
      ((N : ℤ) - jExpIntPF r - pfNumExpIntPF k)
      (z - r)

/--
Raw positive branch window, keeping the `branchInvCoeffAtPF` coefficient.
Here `k ≥ 0`, `m = h - k ≥ 0`, and the theta exponent is
`r = k + z - h`.
-/
def thetaMulPFRawPositiveCoeffPF (N : ℕ) (z : ℤ) : ℤ :=
  ∑ h ∈ Finset.range (thetaMulPFWindowPF N z),
    ∑ k ∈ Finset.range (h + 1),
      thetaMulPFRawBranchTermPF N z (k : ℤ) ((k : ℤ) + z - (h : ℤ))

/--
Raw negative branch window, keeping the `branchInvCoeffAtPF` coefficient.
Here the denominator index is `-c-1`, the branch `u`-power is `c-h < 0`,
and the theta exponent is `r = h + z - c`.
-/
def thetaMulPFRawNegativeCoeffPF (N : ℕ) (z : ℤ) : ℤ :=
  ∑ h ∈ Finset.range (thetaMulPFWindowPF N z),
    ∑ c ∈ Finset.range h,
      thetaMulPFRawBranchTermPF N z (-((c : ℤ) + 1))
        ((h : ℤ) + z - (c : ℤ))

/-- Full raw branch-window coefficient before compression. -/
def thetaMulPFRawCoeffPF (N : ℕ) (z : ℤ) : ℤ :=
  thetaMulPFRawPositiveCoeffPF N z + thetaMulPFRawNegativeCoeffPF N z

theorem thetaMulPFRawPositive_exponentPF (h k : ℕ) (z : ℤ) :
    jExpIntPF ((k : ℤ) + z - (h : ℤ)) + pfNumExpIntPF (k : ℤ) +
        (k : ℤ) * ((h : ℤ) - (k : ℤ)) =
      triIntPF ((h : ℤ) - z) + (k : ℤ) * z := by
  unfold jExpIntPF pfNumExpIntPF
  have h1 := two_mul_triIntPF (((k : ℤ) + z - (h : ℤ)) - 1)
  have h2 := two_mul_triIntPF (k : ℤ)
  have h3 := two_mul_triIntPF ((h : ℤ) - z)
  nlinarith

theorem thetaMulPFRawPositive_signPF (h k : ℕ) (z : ℤ) :
    negOnePowIntPF ℤ ((k : ℤ) + z - (h : ℤ)) *
        negOnePowIntPF ℤ (k : ℤ) =
      negOnePowIntPF ℤ ((h : ℤ) - z) := by
  rw [← negOnePowIntPF_add]
  apply negOnePowIntPF_eq_of_even_sub
  refine ⟨(k : ℤ) + z - (h : ℤ), ?_⟩
  ring

theorem thetaMulPFRawPositiveBranchTerm_eq_compressedPF
    (N h k : ℕ) (z : ℤ) (hk : k < h + 1) :
    thetaMulPFRawBranchTermPF N z (k : ℤ) ((k : ℤ) + z - (h : ℤ)) =
      if triIntPF ((h : ℤ) - z) + (k : ℤ) * z = (N : ℤ) then
        negOnePowIntPF ℤ ((h : ℤ) - z)
      else
        0 := by
  have hb_le : (k : ℤ) + z ≤ z + (h : ℤ) := by omega
  have hb_eq : z - ((k : ℤ) + z - (h : ℤ)) = (h : ℤ) - (k : ℤ) := by ring
  have hk_nonneg : 0 ≤ (k : ℤ) := Int.natCast_nonneg k
  have hiff :
      ((N : ℤ) - jExpIntPF ((k : ℤ) + z - (h : ℤ)) -
          pfNumExpIntPF (k : ℤ) =
        (k : ℤ) * (z - ((k : ℤ) + z - (h : ℤ)))) ↔
        triIntPF ((h : ℤ) - z) + (k : ℤ) * z = (N : ℤ) := by
    rw [hb_eq]
    have hexp := thetaMulPFRawPositive_exponentPF h k z
    omega
  by_cases hcond : triIntPF ((h : ℤ) - z) + (k : ℤ) * z = (N : ℤ)
  · have hbranch :
        branchInvCoeffAtPF (k : ℤ)
          ((N : ℤ) - jExpIntPF ((k : ℤ) + z - (h : ℤ)) -
            pfNumExpIntPF (k : ℤ))
          (z - ((k : ℤ) + z - (h : ℤ))) = 1 := by
      simp [branchInvCoeffAtPF, hk_nonneg, hb_le, hiff.mpr hcond]
    simp [thetaMulPFRawBranchTermPF, hcond, hbranch,
      thetaMulPFRawPositive_signPF]
  · have hbranch :
        branchInvCoeffAtPF (k : ℤ)
          ((N : ℤ) - jExpIntPF ((k : ℤ) + z - (h : ℤ)) -
            pfNumExpIntPF (k : ℤ))
          (z - ((k : ℤ) + z - (h : ℤ))) = 0 := by
      have hrawne :
          ¬ (N : ℤ) - jExpIntPF ((k : ℤ) + z - (h : ℤ)) -
              pfNumExpIntPF (k : ℤ) =
            (k : ℤ) * (z - ((k : ℤ) + z - (h : ℤ))) := by
        intro hraw
        exact hcond (hiff.mp hraw)
      simp [branchInvCoeffAtPF, hk_nonneg, hb_le, hrawne]
    simp [thetaMulPFRawBranchTermPF, hcond, hbranch]

theorem thetaMulPFRawNegative_exponentPF (h c : ℕ) (z : ℤ) :
    jExpIntPF ((h : ℤ) + z - (c : ℤ)) +
        pfNumExpIntPF (-((c : ℤ) + 1)) +
        (-((c : ℤ) + 1)) * ((c : ℤ) - (h : ℤ)) =
      triIntPF ((h : ℤ) + z) - ((c : ℤ) + 1) * z := by
  unfold jExpIntPF pfNumExpIntPF
  have h1 := two_mul_triIntPF (((h : ℤ) + z - (c : ℤ)) - 1)
  have h2 := two_mul_triIntPF (-((c : ℤ) + 1))
  have h3 := two_mul_triIntPF ((h : ℤ) + z)
  nlinarith

theorem thetaMulPFRawNegative_signPF (h c : ℕ) (z : ℤ) :
    negOnePowIntPF ℤ ((h : ℤ) + z - (c : ℤ)) *
        negOnePowIntPF ℤ (-((c : ℤ) + 1)) * (-1 : ℤ) =
      negOnePowIntPF ℤ ((h : ℤ) + z) := by
  have hmul :
      negOnePowIntPF ℤ ((h : ℤ) + z - (c : ℤ)) *
          negOnePowIntPF ℤ (-((c : ℤ) + 1)) =
        negOnePowIntPF ℤ
          (((h : ℤ) + z - (c : ℤ)) + (-((c : ℤ) + 1))) := by
    rw [negOnePowIntPF_add]
  rw [hmul]
  have hneg_one : (-1 : ℤ) = negOnePowIntPF ℤ (1 : ℤ) := by
    simp [negOnePowIntPF]
  rw [hneg_one, ← negOnePowIntPF_add]
  apply negOnePowIntPF_eq_of_even_sub
  refine ⟨-((c : ℤ)), ?_⟩
  ring

theorem thetaMulPFRawNegativeBranchTerm_eq_compressedPF
    (N h c : ℕ) (z : ℤ) (hc : c < h) :
    thetaMulPFRawBranchTermPF N z (-((c : ℤ) + 1))
        ((h : ℤ) + z - (c : ℤ)) =
      if triIntPF ((h : ℤ) + z) - ((c : ℤ) + 1) * z = (N : ℤ) then
        negOnePowIntPF ℤ ((h : ℤ) + z)
      else
        0 := by
  have hnot_nonneg_norm : ¬ (c : ℤ) ≤ -1 := by omega
  have hb_neg : z - ((h : ℤ) + z - (c : ℤ)) < 0 := by omega
  have hb_eq : z - ((h : ℤ) + z - (c : ℤ)) = (c : ℤ) - (h : ℤ) := by ring
  have hneg_norm : (-((c : ℤ) + 1)) = -1 + -(c : ℤ) := by ring
  have hiff :
      ((N : ℤ) - jExpIntPF ((h : ℤ) + z - (c : ℤ)) -
          pfNumExpIntPF (-((c : ℤ) + 1)) =
        (-((c : ℤ) + 1)) * (z - ((h : ℤ) + z - (c : ℤ)))) ↔
        triIntPF ((h : ℤ) + z) - ((c : ℤ) + 1) * z = (N : ℤ) := by
    rw [hb_eq]
    have hexp := thetaMulPFRawNegative_exponentPF h c z
    omega
  by_cases hcond : triIntPF ((h : ℤ) + z) - ((c : ℤ) + 1) * z = (N : ℤ)
  · have hraw := hiff.mpr hcond
    have hraw_norm :
        (N : ℤ) - jExpIntPF ((h : ℤ) + z - (c : ℤ)) -
            pfNumExpIntPF (-1 + -(c : ℤ)) =
          (-1 + -(c : ℤ)) * (z - ((h : ℤ) + z - (c : ℤ))) := by
      simpa [hneg_norm] using hraw
    have hbranch_norm :
        branchInvCoeffAtPF (-1 + -(c : ℤ))
          ((N : ℤ) - jExpIntPF ((h : ℤ) + z - (c : ℤ)) -
            pfNumExpIntPF (-1 + -(c : ℤ)))
          (z - ((h : ℤ) + z - (c : ℤ))) = -1 := by
      simp [branchInvCoeffAtPF, hnot_nonneg_norm, hb_neg, hraw_norm]
    calc
      thetaMulPFRawBranchTermPF N z (-((c : ℤ) + 1))
          ((h : ℤ) + z - (c : ℤ))
          = negOnePowIntPF ℤ ((h : ℤ) + z - (c : ℤ)) *
              negOnePowIntPF ℤ (-((c : ℤ) + 1)) * (-1 : ℤ) := by
                simp [thetaMulPFRawBranchTermPF, hbranch_norm, hneg_norm]
      _ = negOnePowIntPF ℤ ((h : ℤ) + z) :=
            thetaMulPFRawNegative_signPF h c z
      _ = (if triIntPF ((h : ℤ) + z) - ((c : ℤ) + 1) * z = (N : ℤ) then
            negOnePowIntPF ℤ ((h : ℤ) + z) else 0) := by
            simp [hcond]
  · have hrawne :
        ¬ (N : ℤ) - jExpIntPF ((h : ℤ) + z - (c : ℤ)) -
            pfNumExpIntPF (-((c : ℤ) + 1)) =
          (-((c : ℤ) + 1)) * (z - ((h : ℤ) + z - (c : ℤ))) := by
      intro hraw
      exact hcond (hiff.mp hraw)
    have hrawne_norm :
        ¬ (N : ℤ) - jExpIntPF ((h : ℤ) + z - (c : ℤ)) -
            pfNumExpIntPF (-1 + -(c : ℤ)) =
          (-1 + -(c : ℤ)) * (z - ((h : ℤ) + z - (c : ℤ))) := by
      intro hraw
      apply hrawne
      simpa [hneg_norm] using hraw
    have hbranch_norm :
        branchInvCoeffAtPF (-1 + -(c : ℤ))
          ((N : ℤ) - jExpIntPF ((h : ℤ) + z - (c : ℤ)) -
            pfNumExpIntPF (-1 + -(c : ℤ)))
          (z - ((h : ℤ) + z - (c : ℤ))) = 0 := by
      simp [branchInvCoeffAtPF, hnot_nonneg_norm, hb_neg, hrawne_norm]
    simp [thetaMulPFRawBranchTermPF, hcond, hbranch_norm, hneg_norm]

theorem thetaMulPFRawPositiveCoeffPF_eq_thetaMulPFPositiveCoeffPF
    (N : ℕ) (z : ℤ) :
    thetaMulPFRawPositiveCoeffPF N z = thetaMulPFPositiveCoeffPF N z := by
  unfold thetaMulPFRawPositiveCoeffPF thetaMulPFPositiveCoeffPF
  refine Finset.sum_congr rfl ?_
  intro h _hh
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hklt : k < h + 1 := by simpa using hk
  exact thetaMulPFRawPositiveBranchTerm_eq_compressedPF N h k z hklt

theorem thetaMulPFRawNegativeCoeffPF_eq_thetaMulPFNegativeCoeffPF
    (N : ℕ) (z : ℤ) :
    thetaMulPFRawNegativeCoeffPF N z = thetaMulPFNegativeCoeffPF N z := by
  unfold thetaMulPFRawNegativeCoeffPF thetaMulPFNegativeCoeffPF
  refine Finset.sum_congr rfl ?_
  intro h _hh
  refine Finset.sum_congr rfl ?_
  intro c hc
  have hclt : c < h := by simpa using hc
  exact thetaMulPFRawNegativeBranchTerm_eq_compressedPF N h c z hclt

theorem thetaMulPFRawCoeffPF_eq_thetaMulPFCoeffPF (N : ℕ) (z : ℤ) :
    thetaMulPFRawCoeffPF N z = thetaMulPFCoeffPF N z := by
  unfold thetaMulPFRawCoeffPF thetaMulPFCoeffPF
  rw [thetaMulPFRawPositiveCoeffPF_eq_thetaMulPFPositiveCoeffPF,
    thetaMulPFRawNegativeCoeffPF_eq_thetaMulPFNegativeCoeffPF]

theorem thetaMulPFCoeffPF_eq_thetaMulPFRawCoeffPF (N : ℕ) (z : ℤ) :
    thetaMulPFCoeffPF N z = thetaMulPFRawCoeffPF N z :=
  (thetaMulPFRawCoeffPF_eq_thetaMulPFCoeffPF N z).symm

/--
The same coefficient after merging the two valuation branches: the negative
branch supplies the upper half `h + 1 ≤ k ≤ 2h`.
-/
def thetaMulPFUnifiedCoeffPF (N : ℕ) (z : ℤ) : ℤ :=
  ∑ h ∈ Finset.range (thetaMulPFWindowPF N z),
    ∑ k ∈ Finset.range (2 * h + 1),
      if triIntPF ((h : ℤ) - z) + (k : ℤ) * z = (N : ℤ) then
        negOnePowIntPF ℤ ((h : ℤ) - z)
      else
        0

theorem thetaMulPFCoeffPF_eq_unified (N : ℕ) (z : ℤ) :
    thetaMulPFCoeffPF N z = thetaMulPFUnifiedCoeffPF N z := by
  unfold thetaMulPFCoeffPF thetaMulPFPositiveCoeffPF thetaMulPFNegativeCoeffPF
    thetaMulPFUnifiedCoeffPF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro h _hh
  conv_rhs =>
    rw [show 2 * h + 1 = (h + 1) + h by omega]
    rw [Finset.sum_range_add]
  rw [add_left_cancel_iff]
  let upper : ℕ → ℤ := fun i =>
    if triIntPF ((h : ℤ) - z) + ((h + 1 + i : ℕ) : ℤ) * z = (N : ℤ) then
      negOnePowIntPF ℤ ((h : ℤ) - z)
    else
      0
  have hreflect :
      (∑ i ∈ Finset.range h, upper i) =
        ∑ c ∈ Finset.range h, upper (h - 1 - c) := by
    rw [Finset.sum_range_reflect upper h]
  rw [hreflect]
  refine Finset.sum_congr rfl ?_
  intro c hc
  have hc_lt : c < h := by simpa using hc
  have hidx : (h : ℤ) + 1 + ((h - 1 - c : ℕ) : ℤ) =
      2 * (h : ℤ) - (c : ℤ) := by
    omega
  have hexp :
      triIntPF ((h : ℤ) + z) - ((c : ℤ) + 1) * z =
        triIntPF ((h : ℤ) - z) + (2 * (h : ℤ) - (c : ℤ)) * z := by
    rw [triIntPF_add_eq_sub_add]
    ring
  have hsign := negOnePowIntPF_add_eq_sub h z
  by_cases hcond :
      triIntPF ((h : ℤ) - z) + (2 * (h : ℤ) - (c : ℤ)) * z = (N : ℤ)
  · have hcond_neg :
      triIntPF ((h : ℤ) + z) - ((c : ℤ) + 1) * z = (N : ℤ) := by
        rw [hexp, hcond]
    have hcond_reflect :
        triIntPF ((h : ℤ) - z) +
            ((h : ℤ) + 1 + ((h - 1 - c : ℕ) : ℤ)) * z =
          (N : ℤ) := by
      rw [hidx]
      exact hcond
    simp [upper, hcond_neg, hcond_reflect, hsign]
  · have hcond_neg :
      triIntPF ((h : ℤ) + z) - ((c : ℤ) + 1) * z ≠ (N : ℤ) := by
        intro hbad
        apply hcond
        rwa [← hexp]
    have hcond_reflect :
        triIntPF ((h : ℤ) - z) +
            ((h : ℤ) + 1 + ((h - 1 - c : ℕ) : ℤ)) * z ≠
          (N : ℤ) := by
      intro hbad
      apply hcond
      rwa [hidx] at hbad
    simp [upper, hcond_neg, hcond_reflect]

theorem thetaMulPFPositiveCoeffPF_zero (N : ℕ) :
    thetaMulPFPositiveCoeffPF N 0 =
      ∑ h ∈ Finset.range (N + 1),
        ((h + 1 : ℕ) : ℤ) *
          if triPF h = N then (-1 : ℤ) ^ h else 0 := by
  unfold thetaMulPFPositiveCoeffPF thetaMulPFWindowPF
  simp only [sub_zero, Int.natAbs_zero]
  refine Finset.sum_congr rfl ?_
  intro h _hh
  by_cases ht : triPF h = N
  · have ht_int : triIntPF (h : ℤ) = (N : ℤ) := by
      rw [triIntPF_natCast, ht]
    simp [ht, ht_int, negOnePowIntPF]
  · simp [ht]

theorem thetaMulPFNegativeCoeffPF_zero (N : ℕ) :
    thetaMulPFNegativeCoeffPF N 0 =
      ∑ h ∈ Finset.range (N + 1),
        (h : ℤ) * if triPF h = N then (-1 : ℤ) ^ h else 0 := by
  unfold thetaMulPFNegativeCoeffPF thetaMulPFWindowPF
  simp only [add_zero, Int.natAbs_zero, mul_zero, sub_zero]
  refine Finset.sum_congr rfl ?_
  intro h _hh
  by_cases ht : triPF h = N
  · have ht_int : triIntPF (h : ℤ) = (N : ℤ) := by
      rw [triIntPF_natCast, ht]
    simp [ht, ht_int, negOnePowIntPF]
  · simp [ht]

theorem thetaMulPFCoeffPF_zero_eq_constCoeffPF (N : ℕ) :
    thetaMulPFCoeffPF N 0 = thetaMulPFConstCoeffPF N := by
  unfold thetaMulPFCoeffPF thetaMulPFConstCoeffPF
  rw [thetaMulPFPositiveCoeffPF_zero, thetaMulPFNegativeCoeffPF_zero]

theorem thetaMulPFCoeffPF_zero_eq_jacobiCubeCoeffPF (N : ℕ) :
    thetaMulPFCoeffPF N 0 = jacobiCubeCoeffPF N := by
  rw [thetaMulPFCoeffPF_zero_eq_constCoeffPF,
    thetaMulPFConstCoeffPF_eq_jacobiCubeCoeffPF]

/-! ## Nonconstant `u`-coefficients and PF assembly -/

noncomputable def thetaMulPFTailHitPF (N : ℕ) (z r : ℤ) : ℤ := by
  classical
  exact if ∃ t : ℕ, triIntPF r + (t : ℤ) * z = (N : ℤ) then 1 else 0

theorem triIntPF_reflect (r : ℤ) :
    triIntPF (-r - 1) = triIntPF r := by
  unfold triIntPF
  ring_nf

theorem negOnePowIntPF_reflect (r : ℤ) :
    negOnePowIntPF ℤ (-r - 1) = -negOnePowIntPF ℤ r := by
  rw [negOnePowIntPF_eq_negOnePow, negOnePowIntPF_eq_negOnePow]
  have h := Int.negOnePow_succ (-r - 1)
  have harg : -r - 1 + 1 = -r := by ring
  rw [harg, Int.negOnePow_neg] at h
  have hv := congrArg (fun u : ℤˣ => (u : ℤ)) h
  simp at hv
  linarith

theorem thetaMulPFTailHitPF_reflect (N : ℕ) (z r : ℤ) :
    thetaMulPFTailHitPF N z (-r - 1) = thetaMulPFTailHitPF N z r := by
  classical
  simp [thetaMulPFTailHitPF, triIntPF_reflect]

theorem triIntPF_nonneg (r : ℤ) :
    0 ≤ triIntPF r := by
  have htwo := two_mul_triIntPF r
  by_cases hr : 0 ≤ r
  · have hr1 : 0 ≤ r + 1 := by omega
    nlinarith [mul_nonneg hr hr1]
  · have hr0 : r ≤ 0 := by omega
    have hr1 : r + 1 ≤ 0 := by omega
    have hprod : 0 ≤ r * (r + 1) := mul_nonneg_of_nonpos_of_nonpos hr0 hr1
    nlinarith

theorem triIntPF_gt_of_nat_add_two_le (N : ℕ) {r : ℤ}
    (hr : (N : ℤ) + 2 ≤ r) :
    (N : ℤ) < triIntPF r := by
  have htwo := two_mul_triIntPF r
  nlinarith [sq_nonneg (r - ((N : ℤ) + 2)), htwo]

theorem thetaMulPFTailHitPF_eq_zero_of_tri_gt
    (N : ℕ) {z r : ℤ} (hz : 0 ≤ z) (hr : (N : ℤ) < triIntPF r) :
    thetaMulPFTailHitPF N z r = 0 := by
  classical
  unfold thetaMulPFTailHitPF
  simp only [ite_eq_right_iff, one_ne_zero, imp_false]
  rintro ⟨t, ht⟩
  have ht_nonneg : 0 ≤ (t : ℤ) * z :=
    mul_nonneg (Int.natCast_nonneg t) hz
  omega

private theorem sum_range_sub_shift_by (L M : ℕ) (f : ℕ → ℤ) (hML : M ≤ L) :
    (∑ h ∈ Finset.range L, (f h - f (h + M))) =
      (∑ h ∈ Finset.range M, f h) - (∑ h ∈ Finset.range M, f (L + h)) := by
  have hL : L = M + (L - M) := by omega
  have hL' : L = (L - M) + M := by omega
  have hfirst :
      (∑ h ∈ Finset.range L, f h) =
        (∑ h ∈ Finset.range M, f h) +
          ∑ h ∈ Finset.range (L - M), f (M + h) := by
    conv_lhs => rw [hL, Finset.sum_range_add]
  have hsecond :
      (∑ h ∈ Finset.range L, f (h + M)) =
        (∑ h ∈ Finset.range (L - M), f (M + h)) +
          ∑ h ∈ Finset.range M, f (L + h) := by
    conv_lhs => rw [hL', Finset.sum_range_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro h _hh
      congr 1
      omega
    · apply Finset.sum_congr rfl
      intro h _hh
      congr 1
      omega
  rw [Finset.sum_sub_distrib, hfirst, hsecond]
  ring

private theorem thetaMulPFUnifiedInner_eq_tailHit_sub_of_pos
    (N h : ℕ) {z : ℤ} (hz : 0 < z) :
    (∑ k ∈ Finset.range (2 * h + 1),
      if triIntPF ((h : ℤ) - z) + (k : ℤ) * z = (N : ℤ) then
        negOnePowIntPF ℤ ((h : ℤ) - z)
      else
        0) =
      negOnePowIntPF ℤ ((h : ℤ) - z) *
        (thetaMulPFTailHitPF N z ((h : ℤ) - z) -
          thetaMulPFTailHitPF N z ((h : ℤ) + z)) := by
  classical
  let r : ℤ := (h : ℤ) - z
  let c : ℤ := negOnePowIntPF ℤ r
  change (∑ k ∈ Finset.range (2 * h + 1),
      if triIntPF r + (k : ℤ) * z = (N : ℤ) then c else 0) =
    c * (thetaMulPFTailHitPF N z r - thetaMulPFTailHitPF N z ((h : ℤ) + z))
  have hz_ne : z ≠ 0 := by omega
  have htri :
      triIntPF ((h : ℤ) + z) =
        triIntPF r + ((2 * h + 1 : ℕ) : ℤ) * z := by
    dsimp [r]
    rw [triIntPF_add_eq_sub_add]
    norm_num
    ring
  by_cases hhit : ∃ t : ℕ, triIntPF r + (t : ℤ) * z = (N : ℤ)
  · rcases hhit with ⟨t, ht⟩
    have hcond : ∀ k : ℕ,
        (triIntPF r + (k : ℤ) * z = (N : ℤ)) ↔ k = t := by
      intro k
      constructor
      · intro hk
        have : (k : ℤ) * z = (t : ℤ) * z := by omega
        have hcast : (k : ℤ) = (t : ℤ) := mul_right_cancel₀ hz_ne this
        exact_mod_cast hcast
      · intro hkt
        subst k
        exact ht
    by_cases htlt : t < 2 * h + 1
    · have hno_shift :
          ¬ ∃ t' : ℕ, triIntPF ((h : ℤ) + z) + (t' : ℤ) * z = (N : ℤ) := by
        rintro ⟨t', ht'⟩
        have hmain :
            triIntPF r + ((2 * h + 1 + t' : ℕ) : ℤ) * z = (N : ℤ) := by
          calc
            triIntPF r + ((2 * h + 1 + t' : ℕ) : ℤ) * z
                = triIntPF ((h : ℤ) + z) + (t' : ℤ) * z := by
                    rw [Nat.cast_add, htri]
                    ring
            _ = (N : ℤ) := ht'
        have hk : 2 * h + 1 + t' = t := (hcond (2 * h + 1 + t')).mp hmain
        omega
      simp [thetaMulPFTailHitPF, hno_shift, hcond, htlt]
    · have htge : 2 * h + 1 ≤ t := by omega
      have hshift :
          ∃ t' : ℕ, triIntPF ((h : ℤ) + z) + (t' : ℤ) * z = (N : ℤ) := by
        refine ⟨t - (2 * h + 1), ?_⟩
        have hsplit :
            (t : ℤ) =
              ((2 * h + 1 : ℕ) : ℤ) + ((t - (2 * h + 1) : ℕ) : ℤ) := by
          omega
        calc
          triIntPF ((h : ℤ) + z) + ((t - (2 * h + 1) : ℕ) : ℤ) * z
              = triIntPF r + (t : ℤ) * z := by
                  rw [htri, hsplit]
                  ring
          _ = (N : ℤ) := ht
      simp [thetaMulPFTailHitPF, hshift, hcond, htlt]
  · have hno_shift :
        ¬ ∃ t' : ℕ, triIntPF ((h : ℤ) + z) + (t' : ℤ) * z = (N : ℤ) := by
      rintro ⟨t', ht'⟩
      apply hhit
      refine ⟨2 * h + 1 + t', ?_⟩
      calc
        triIntPF r + ((2 * h + 1 + t' : ℕ) : ℤ) * z
            = triIntPF ((h : ℤ) + z) + (t' : ℤ) * z := by
                rw [Nat.cast_add, htri]
                ring
        _ = (N : ℤ) := ht'
    have hzero : ∀ k : ℕ, triIntPF r + (k : ℤ) * z ≠ (N : ℤ) := by
      intro k hk
      exact hhit ⟨k, hk⟩
    simp [thetaMulPFTailHitPF, hno_shift, hzero]

theorem thetaMulPFUnifiedCoeffPF_zero_of_pos
    (N : ℕ) {z : ℤ} (hz : 0 < z) :
    thetaMulPFUnifiedCoeffPF N z = 0 := by
  classical
  let d : ℕ := z.natAbs
  have hz_ne : z ≠ 0 := by omega
  have hz_nonneg : 0 ≤ z := by omega
  have hz_cast : (d : ℤ) = z := by
    dsimp [d]
    exact Int.natAbs_of_nonneg hz_nonneg
  have hd_pos : 0 < d := by
    dsimp [d]
    exact Int.natAbs_pos.mpr hz_ne
  let W : ℕ := N + d + 2
  let M : ℕ := 2 * d
  let L : ℕ := max W M
  let inner : ℕ → ℤ := fun h =>
    ∑ k ∈ Finset.range (2 * h + 1),
      if triIntPF ((h : ℤ) - z) + (k : ℤ) * z = (N : ℤ) then
        negOnePowIntPF ℤ ((h : ℤ) - z)
      else
        0
  let term : ℕ → ℤ := fun h =>
    negOnePowIntPF ℤ ((h : ℤ) - z) *
      thetaMulPFTailHitPF N z ((h : ℤ) - z)
  have hwindow : thetaMulPFWindowPF N z = W := by
    dsimp [W, d]
    simp [thetaMulPFWindowPF, hz_ne]
  change (∑ h ∈ Finset.range (thetaMulPFWindowPF N z), inner h) = 0
  rw [hwindow]
  have hWL : W ≤ L := by
    dsimp [L]
    exact le_max_left W M
  have hML : M ≤ L := by
    dsimp [L]
    exact le_max_right W M
  have h_extend :
      (∑ h ∈ Finset.range W, inner h) =
        ∑ h ∈ Finset.range L, inner h := by
    have hL : L = W + (L - W) := by omega
    conv_rhs => rw [hL, Finset.sum_range_add]
    have htail :
        (∑ h ∈ Finset.range (L - W), inner (W + h)) = 0 := by
      apply Finset.sum_eq_zero
      intro h _hh
      dsimp [inner]
      apply Finset.sum_eq_zero
      intro k _hk
      have hr_ge :
          (N : ℤ) + 2 ≤ (W : ℤ) + (h : ℤ) - z := by
        dsimp [W, d]
        omega
      have htri_gt := triIntPF_gt_of_nat_add_two_le N hr_ge
      have hk_nonneg : 0 ≤ (k : ℤ) * z :=
        mul_nonneg (Int.natCast_nonneg k) hz_nonneg
      have hne :
          triIntPF ((W : ℤ) + (h : ℤ) - z) + (k : ℤ) * z ≠
            (N : ℤ) := by
        omega
      simp [hne]
    rw [htail]
    simp
  rw [h_extend]
  have h_inner_term : ∀ h : ℕ, inner h = term h - term (h + M) := by
    intro h
    have hM_arg : (h : ℤ) + (M : ℤ) - z = (h : ℤ) + z := by
      dsimp [M, d]
      omega
    have hsign := negOnePowIntPF_add_eq_sub h z
    calc
      inner h =
          negOnePowIntPF ℤ ((h : ℤ) - z) *
            (thetaMulPFTailHitPF N z ((h : ℤ) - z) -
              thetaMulPFTailHitPF N z ((h : ℤ) + z)) := by
            dsimp [inner]
            exact thetaMulPFUnifiedInner_eq_tailHit_sub_of_pos N h hz
      _ = term h - term (h + M) := by
            dsimp [term]
            rw [hM_arg, hsign]
            ring
  have hsum_term :
      (∑ h ∈ Finset.range L, inner h) =
        ∑ h ∈ Finset.range L, (term h - term (h + M)) := by
    apply Finset.sum_congr rfl
    intro h _hh
    exact h_inner_term h
  rw [hsum_term, sum_range_sub_shift_by L M term hML]
  have hboundary : (∑ h ∈ Finset.range M, term h) = 0 := by
    have hpair : ∀ h ∈ Finset.range M, term (M - 1 - h) = -term h := by
      intro h hh
      have hlt : h < M := by simpa using hh
      have hr :
          (((M - 1 - h : ℕ) : ℤ) - z) =
            -(((h : ℤ) - z)) - 1 := by
        dsimp [M, d]
        omega
      dsimp [term]
      rw [hr, thetaMulPFTailHitPF_reflect, negOnePowIntPF_reflect]
      ring
    have hreflect := (Finset.sum_range_reflect term M).symm
    have hsum_reflect :
        (∑ h ∈ Finset.range M, term (M - 1 - h)) =
          ∑ h ∈ Finset.range M, -term h := by
      apply Finset.sum_congr rfl
      intro h hh
      exact hpair h hh
    have hS :
        (∑ h ∈ Finset.range M, term h) =
          -(∑ h ∈ Finset.range M, term h) := by
      calc
        (∑ h ∈ Finset.range M, term h)
            = ∑ h ∈ Finset.range M, term (M - 1 - h) := hreflect
        _ = ∑ h ∈ Finset.range M, -term h := hsum_reflect
        _ = -(∑ h ∈ Finset.range M, term h) := by simp
    omega
  have hfar : (∑ h ∈ Finset.range M, term (L + h)) = 0 := by
    apply Finset.sum_eq_zero
    intro h _hh
    dsimp [term]
    have hr_ge :
        (N : ℤ) + 2 ≤ (L : ℤ) + (h : ℤ) - z := by
      have hLW : W ≤ L := hWL
      dsimp [W, d] at hLW ⊢
      omega
    have htri_gt := triIntPF_gt_of_nat_add_two_le N hr_ge
    have hhit_zero :=
      thetaMulPFTailHitPF_eq_zero_of_tri_gt N hz_nonneg htri_gt
    rw [hhit_zero, mul_zero]
  rw [hboundary, hfar]
  ring

private theorem thetaMulPFUnifiedInner_neg_eq_pos
    (N h : ℕ) {z : ℤ} (hz : z < 0) (hNd : z.natAbs ≤ N) :
    (∑ k ∈ Finset.range (2 * h + 1),
      if triIntPF ((h : ℤ) - z) + (k : ℤ) * z = (N : ℤ) then
        negOnePowIntPF ℤ ((h : ℤ) - z)
      else
        0) =
      ∑ k ∈ Finset.range (2 * h + 1),
        if triIntPF ((h : ℤ) - (-z)) + (k : ℤ) * (-z) =
            ((N - z.natAbs : ℕ) : ℤ) then
          negOnePowIntPF ℤ ((h : ℤ) - (-z))
        else
          0 := by
  let d : ℕ := z.natAbs
  have hd_cast : (d : ℤ) = -z := by
    dsimp [d]
    rw [← Int.natAbs_neg z]
    exact Int.natAbs_of_nonneg (by omega : 0 ≤ -z)
  have hz_eq : z = -(d : ℤ) := by omega
  have hNcast : ((N - d : ℕ) : ℤ) = (N : ℤ) - (d : ℤ) := by omega
  have hsign :
      negOnePowIntPF ℤ ((h : ℤ) - z) =
        negOnePowIntPF ℤ ((h : ℤ) - (-z)) := by
    have h0 := negOnePowIntPF_add_eq_sub h (d : ℤ)
    have hleft : (h : ℤ) - z = (h : ℤ) + (d : ℤ) := by omega
    have hright : (h : ℤ) - (-z) = (h : ℤ) - (d : ℤ) := by omega
    rw [hleft, hright]
    exact h0
  let f : ℕ → ℤ := fun k =>
    if triIntPF ((h : ℤ) - z) + (k : ℤ) * z = (N : ℤ) then
      negOnePowIntPF ℤ ((h : ℤ) - z)
    else
      0
  calc
    (∑ k ∈ Finset.range (2 * h + 1),
      if triIntPF ((h : ℤ) - z) + (k : ℤ) * z = (N : ℤ) then
        negOnePowIntPF ℤ ((h : ℤ) - z)
      else
        0) = ∑ k ∈ Finset.range (2 * h + 1), f k := rfl
    _ = ∑ k ∈ Finset.range (2 * h + 1), f (2 * h + 1 - 1 - k) := by
          exact (Finset.sum_range_reflect f (2 * h + 1)).symm
    _ = ∑ k ∈ Finset.range (2 * h + 1),
        if triIntPF ((h : ℤ) - (-z)) + (k : ℤ) * (-z) =
            ((N - z.natAbs : ℕ) : ℤ) then
          negOnePowIntPF ℤ ((h : ℤ) - (-z))
        else
          0 := by
          apply Finset.sum_congr rfl
          intro k hk
          have hklt : k < 2 * h + 1 := by simpa using hk
          have hsub :
              ((2 * h - k : ℕ) : ℤ) =
                2 * (h : ℤ) - (k : ℤ) := by
            omega
          have hcalc :
              triIntPF ((h : ℤ) - z) +
                  ((2 * h - k : ℕ) : ℤ) * z =
                triIntPF ((h : ℤ) - (-z)) + (k : ℤ) * (-z) + (d : ℤ) := by
            have htri := triIntPF_add_eq_sub_add (h : ℤ) (d : ℤ)
            rw [hz_eq]
            simp only [neg_neg]
            have harg : (h : ℤ) - -(d : ℤ) = (h : ℤ) + (d : ℤ) := by ring
            rw [harg, htri, hsub]
            ring
          have hiff :
              (triIntPF ((h : ℤ) - z) +
                    ((2 * h - k : ℕ) : ℤ) * z = (N : ℤ)) ↔
                (triIntPF ((h : ℤ) - (-z)) + (k : ℤ) * (-z) =
                  ((N - z.natAbs : ℕ) : ℤ)) := by
            dsimp [d] at hNcast
            rw [hcalc, hNcast]
            omega
          by_cases hpos :
              triIntPF ((h : ℤ) - (-z)) + (k : ℤ) * (-z) =
                ((N - z.natAbs : ℕ) : ℤ)
          · have hneg :
                triIntPF ((h : ℤ) - z) + ((2 * h - k : ℕ) : ℤ) * z =
                  (N : ℤ) := hiff.mpr hpos
            have hpos_norm :
                triIntPF ((h : ℤ) + z) + -((k : ℤ) * z) =
                  ((N - z.natAbs : ℕ) : ℤ) := by
              have harg : (h : ℤ) + z = (h : ℤ) - (-z) := by ring
              have hmul : -((k : ℤ) * z) = (k : ℤ) * (-z) := by ring
              rw [harg, hmul]
              exact hpos
            simp [f, hneg, hpos_norm, hsign]
          · have hneg :
                triIntPF ((h : ℤ) - z) + ((2 * h - k : ℕ) : ℤ) * z ≠
                  (N : ℤ) := by
              intro hn
              exact hpos (hiff.mp hn)
            have hpos_norm :
                ¬ triIntPF ((h : ℤ) + z) + -((k : ℤ) * z) =
                  ((N - z.natAbs : ℕ) : ℤ) := by
              intro hp
              apply hpos
              have harg : (h : ℤ) - (-z) = (h : ℤ) + z := by ring
              have hmul : (k : ℤ) * (-z) = -((k : ℤ) * z) := by ring
              rw [harg, hmul]
              exact hp
            simp [f, hneg, hpos_norm]

theorem thetaMulPFUnifiedCoeffPF_zero_of_neg
    (N : ℕ) {z : ℤ} (hz : z < 0) :
    thetaMulPFUnifiedCoeffPF N z = 0 := by
  classical
  let d : ℕ := z.natAbs
  have hz_ne : z ≠ 0 := by omega
  have hd_cast : (d : ℤ) = -z := by
    dsimp [d]
    rw [← Int.natAbs_neg z]
    exact Int.natAbs_of_nonneg (by omega : 0 ≤ -z)
  have hz_eq : z = -(d : ℤ) := by omega
  have hd_pos : 0 < d := by
    dsimp [d]
    exact Int.natAbs_pos.mpr hz_ne
  let Wneg : ℕ := N + d + 2
  let negInner : ℕ → ℤ := fun h =>
    ∑ k ∈ Finset.range (2 * h + 1),
      if triIntPF ((h : ℤ) - z) + (k : ℤ) * z = (N : ℤ) then
        negOnePowIntPF ℤ ((h : ℤ) - z)
      else
        0
  have hwindow_neg : thetaMulPFWindowPF N z = Wneg := by
    dsimp [Wneg, d]
    simp [thetaMulPFWindowPF, hz_ne]
  change (∑ h ∈ Finset.range (thetaMulPFWindowPF N z), negInner h) = 0
  rw [hwindow_neg]
  by_cases hNd : d ≤ N
  · let Wpos : ℕ := N + 2
    let posInner : ℕ → ℤ := fun h =>
      ∑ k ∈ Finset.range (2 * h + 1),
        if triIntPF ((h : ℤ) - (-z)) + (k : ℤ) * (-z) =
            ((N - d : ℕ) : ℤ) then
          negOnePowIntPF ℤ ((h : ℤ) - (-z))
        else
          0
    have hneg_to_pos :
        (∑ h ∈ Finset.range Wneg, negInner h) =
          ∑ h ∈ Finset.range Wneg, posInner h := by
      apply Finset.sum_congr rfl
      intro h _hh
      dsimp [negInner, posInner, d]
      exact thetaMulPFUnifiedInner_neg_eq_pos N h hz hNd
    rw [hneg_to_pos]
    have hwindow_pos :
        thetaMulPFWindowPF (N - d) (-z) = Wpos := by
      have hneg_ne : -z ≠ 0 := by omega
      dsimp [Wpos, d]
      simp [thetaMulPFWindowPF, hneg_ne, Int.natAbs_neg]
      omega
    have hpos_zero := thetaMulPFUnifiedCoeffPF_zero_of_pos (N - d) (z := -z) (by omega)
    unfold thetaMulPFUnifiedCoeffPF at hpos_zero
    rw [hwindow_pos] at hpos_zero
    change (∑ h ∈ Finset.range Wpos, posInner h) = 0 at hpos_zero
    have hWpos_le : Wpos ≤ Wneg := by
      dsimp [Wpos, Wneg]
      omega
    have h_extend_pos :
        (∑ h ∈ Finset.range Wpos, posInner h) =
          ∑ h ∈ Finset.range Wneg, posInner h := by
      have hW : Wneg = Wpos + (Wneg - Wpos) := by omega
      conv_rhs => rw [hW, Finset.sum_range_add]
      have htail :
          (∑ h ∈ Finset.range (Wneg - Wpos), posInner (Wpos + h)) = 0 := by
        apply Finset.sum_eq_zero
        intro h _hh
        dsimp [posInner]
        apply Finset.sum_eq_zero
        intro k _hk
        have hdeg_cast : ((N - d : ℕ) : ℤ) = (N : ℤ) - (d : ℤ) := by omega
        have hr_ge :
            ((N - d : ℕ) : ℤ) + 2 ≤
              (Wpos : ℤ) + (h : ℤ) - (-z) := by
          dsimp [Wpos, d] at hdeg_cast ⊢
          omega
        have htri_gt := triIntPF_gt_of_nat_add_two_le (N - d) hr_ge
        have hk_nonneg : 0 ≤ (k : ℤ) * (-z) :=
          mul_nonneg (Int.natCast_nonneg k) (by omega : 0 ≤ -z)
        have hne :
            triIntPF ((Wpos : ℤ) + (h : ℤ) - (-z)) + (k : ℤ) * (-z) ≠
              ((N - d : ℕ) : ℤ) := by
          omega
        have hne_norm :
            triIntPF ((Wpos : ℤ) + (h : ℤ) + z) + -((k : ℤ) * z) ≠
              ((N - d : ℕ) : ℤ) := by
          intro hbad
          apply hne
          have harg :
              (Wpos : ℤ) + (h : ℤ) - (-z) =
                (Wpos : ℤ) + (h : ℤ) + z := by ring
          have hmul : (k : ℤ) * (-z) = -((k : ℤ) * z) := by ring
          rw [harg, hmul]
          exact hbad
        simp [hne_norm]
      rw [htail]
      simp
    rwa [← h_extend_pos]
  · have hN_lt_d : N < d := by omega
    apply Finset.sum_eq_zero
    intro h _hh
    dsimp [negInner]
    apply Finset.sum_eq_zero
    intro k hk
    have hklt : k < 2 * h + 1 := by simpa using hk
    have hk_le : k ≤ 2 * h := by omega
    have hsub : ((2 * h + 1 - k : ℕ) : ℤ) =
        2 * (h : ℤ) + 1 - (k : ℤ) := by
      omega
    have htri := triIntPF_add_eq_sub_add (h : ℤ) (d : ℤ)
    have hexp :
        triIntPF ((h : ℤ) - z) + (k : ℤ) * z =
          triIntPF ((h : ℤ) - (d : ℤ)) +
            ((2 * h + 1 - k : ℕ) : ℤ) * (d : ℤ) := by
      rw [hz_eq]
      simp only [sub_neg_eq_add]
      rw [htri, hsub]
      ring
    have hcoef_pos : 1 ≤ ((2 * h + 1 - k : ℕ) : ℤ) := by
      omega
    have hd_pos_int : 0 < (d : ℤ) := by exact_mod_cast hd_pos
    have hprod_ge : (d : ℤ) ≤ ((2 * h + 1 - k : ℕ) : ℤ) * (d : ℤ) := by
      nlinarith [mul_le_mul_of_nonneg_right hcoef_pos (le_of_lt hd_pos_int)]
    have htri_nonneg := triIntPF_nonneg ((h : ℤ) - (d : ℤ))
    have hge :
        (d : ℤ) ≤
          triIntPF ((h : ℤ) - (d : ℤ)) +
            ((2 * h + 1 - k : ℕ) : ℤ) * (d : ℤ) := by
      nlinarith
    have hne :
        triIntPF ((h : ℤ) - z) + (k : ℤ) * z ≠ (N : ℤ) := by
      rw [hexp]
      omega
    simp [hne]

theorem thetaMulPFUnifiedCoeffPF_nonconstant_vanish
    (N : ℕ) {z : ℤ} (hz : z ≠ 0) :
    thetaMulPFUnifiedCoeffPF N z = 0 := by
  rcases lt_trichotomy z 0 with hz_neg | hz_zero | hz_pos
  · exact thetaMulPFUnifiedCoeffPF_zero_of_neg N hz_neg
  · exact (hz hz_zero).elim
  · exact thetaMulPFUnifiedCoeffPF_zero_of_pos N hz_pos

theorem thetaMulPFCoeffPF_nonconstant_vanish
    (N : ℕ) {z : ℤ} (hz : z ≠ 0) :
    thetaMulPFCoeffPF N z = 0 := by
  rw [thetaMulPFCoeffPF_eq_unified]
  exact thetaMulPFUnifiedCoeffPF_nonconstant_vanish N hz

theorem thetaMulPFCoeffPF_eq_jacobiCubeCoeffPF_ite (N : ℕ) (z : ℤ) :
    thetaMulPFCoeffPF N z = if z = 0 then jacobiCubeCoeffPF N else 0 := by
  by_cases hz : z = 0
  · subst z
    simp [thetaMulPFCoeffPF_zero_eq_jacobiCubeCoeffPF]
  · simp [hz, thetaMulPFCoeffPF_nonconstant_vanish N hz]

/--
The `q`-series coefficient of the cleared product `j(u;q) * PF(u)` at the
fixed Laurent power `u^z`.
-/
noncomputable def thetaMulPFSeriesCoeffPF (z : ℤ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun N => thetaMulPFCoeffPF N z

/-- The Jacobi-cube `q`-series `∑_N jacobiCubeCoeffPF N q^N`. -/
noncomputable def jacobiCubeSeriesPF : ℤ⟦X⟧ :=
  PowerSeries.mk jacobiCubeCoeffPF

theorem triPF_strictMono : StrictMono triPF := by
  simpa [triPF] using QseriesFormalization.PartIV.Ch19.triangular_strictMono

theorem jacobiCubeCoeffPF_eq_jacobiTripleSign (N : ℕ) :
    jacobiCubeCoeffPF N = QseriesFormalization.PartIV.Ch19.jacobiTripleSign N := by
  classical
  by_cases htri : ∃ h ≤ N, triPF h = N
  · rcases htri with ⟨h, hle, hh⟩
    have hmem : h ∈ Finset.range (N + 1) := by
      simp [hle]
    have hterm :
        (if triPF h = N then (-1 : ℤ) ^ h * (2 * (h : ℤ) + 1) else 0) =
          QseriesFormalization.PartIV.Ch19.jacobiTripleSign N := by
      have hN : N = h * (h + 1) / 2 := by
        simpa [triPF] using hh.symm
      rw [if_pos hh, hN,
        QseriesFormalization.PartIV.Ch19.jacobiTripleSign_triangular]
    unfold jacobiCubeCoeffPF
    rw [Finset.sum_eq_single h]
    · exact hterm
    · intro b hb hbne
      have hb_ne_tri : triPF b ≠ N := by
        intro hbN
        apply hbne
        apply triPF_strictMono.injective
        rw [hbN, hh]
      simp [hb_ne_tri]
    · intro hnot
      exact (hnot hmem).elim
  · have hno : ∀ k ≤ N, N ≠ k * (k + 1) / 2 := by
      intro k hk hkN
      apply htri
      refine ⟨k, hk, ?_⟩
      simpa [triPF] using hkN.symm
    have hcoeff_zero : jacobiCubeCoeffPF N = 0 := by
      unfold jacobiCubeCoeffPF
      apply Finset.sum_eq_zero
      intro h hh
      have hle : h ≤ N := by
        simpa [Nat.lt_succ_iff] using hh
      have hne : triPF h ≠ N := by
        intro ht
        exact htri ⟨h, hle, ht⟩
      simp [hne]
    rw [hcoeff_zero,
      QseriesFormalization.PartIV.Ch19.jacobiTripleSign_of_not_triangular N hno]

theorem jacobiCubeSeriesPF_eq_jacobiThetaPS :
    jacobiCubeSeriesPF = QseriesFormalization.PartIV.Ch19.jacobiThetaPS ℤ := by
  ext N
  simp [jacobiCubeSeriesPF, jacobiCubeCoeffPF_eq_jacobiTripleSign]

theorem jacobiCubeSeriesPF_eq_qPochInfPS_pow_three :
    jacobiCubeSeriesPF = (QseriesFormalization.PartIV.Ch19.qPochInfPS ℤ) ^ 3 := by
  rw [jacobiCubeSeriesPF_eq_jacobiThetaPS]
  exact (QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS ℤ).symm

/-- The right-hand side `J^3`, viewed as a Laurent-in-`u` coefficient family. -/
noncomputable def jacobiCubeUPowerCoeffPF (z : ℤ) : ℤ⟦X⟧ :=
  if z = 0 then jacobiCubeSeriesPF else 0

/-- The actual `(q;q)_∞^3` right-hand side as a Laurent-in-`u` coefficient family. -/
noncomputable def qPochInfPSCubeUPowerCoeffPF (z : ℤ) : ℤ⟦X⟧ :=
  if z = 0 then (QseriesFormalization.PartIV.Ch19.qPochInfPS ℤ) ^ 3 else 0

theorem jacobiCubeUPowerCoeffPF_eq_qPochInfPSCubeUPowerCoeffPF :
    jacobiCubeUPowerCoeffPF = qPochInfPSCubeUPowerCoeffPF := by
  funext z
  by_cases hz : z = 0
  · simp [jacobiCubeUPowerCoeffPF, qPochInfPSCubeUPowerCoeffPF, hz,
      jacobiCubeSeriesPF_eq_qPochInfPS_pow_three]
  · simp [jacobiCubeUPowerCoeffPF, qPochInfPSCubeUPowerCoeffPF, hz]

theorem thetaMulPFSeriesCoeffPF_eq_jacobiCubeUPowerCoeffPF (z : ℤ) :
    thetaMulPFSeriesCoeffPF z = jacobiCubeUPowerCoeffPF z := by
  apply PowerSeries.ext
  intro N
  by_cases hz : z = 0
  · subst z
    simp [thetaMulPFSeriesCoeffPF, jacobiCubeUPowerCoeffPF, jacobiCubeSeriesPF,
      thetaMulPFCoeffPF_zero_eq_jacobiCubeCoeffPF]
  · simp [thetaMulPFSeriesCoeffPF, jacobiCubeUPowerCoeffPF, hz,
      thetaMulPFCoeffPF_nonconstant_vanish N hz]

/--
Cleared partial-fraction expansion, HM (1.3), in the coefficient model of this
file: every Laurent `u`-coefficient of `j(u;q) * PF(u)` agrees with `J^3`.
The `u^0` coefficient is the Jacobi cube series; all other `u`-coefficients
vanish.
-/
theorem thetaMul_PF_eq_jacobiCube :
    thetaMulPFSeriesCoeffPF = jacobiCubeUPowerCoeffPF := by
  funext z
  exact thetaMulPFSeriesCoeffPF_eq_jacobiCubeUPowerCoeffPF z

/--
Cleared partial-fraction expansion for the actual formal series:
the coefficient family of `j(u;q) * PF(u;q)` is `(qPochInfPS ℤ)^3` in
`u^0` and vanishes in every nonzero Laurent power of `u`.
-/
theorem thetaMul_PF_eq_qPochInfPS_pow_three :
    thetaMulPFSeriesCoeffPF = qPochInfPSCubeUPowerCoeffPF := by
  rw [thetaMul_PF_eq_jacobiCube, jacobiCubeUPowerCoeffPF_eq_qPochInfPSCubeUPowerCoeffPF]

end Chapter10PF
end Pending
end QseriesFormalization
