import QseriesFormalization.Basic
import QseriesFormalization.Chapter02
import QseriesFormalization.Chapter03

/-!
# Chapter 4 — Part I: Some applications of Jacobi's triple product

(Hei-Chi Chan, *An Invitation to q-Series*, Ch 4, pp. 21–30.)

This chapter spins off four named identities from the Jacobi triple
product (Theorem 4.1, Euler's pentagonal theorem, Theorem 4.3, the
quintuple product identity).  The Jacobi triple product is now available;
the remaining infinite applications need the specialization and rewriting
layers connecting those products and bilateral sums to Chan's displayed forms.
-/

namespace QseriesFormalization
namespace PartI
namespace Ch04

open QseriesFormalization.PartI.Ch02 (jacobiInfiniteProduct jacobiInfiniteSeries jacobiTripleProduct)
open QseriesFormalization.PartI.Ch03 (finiteJTPRHS finite_jacobi_triple_product)
open Filter

open scoped Topology

section Field

variable {R : Type*} [Field R]

/-- Finite Euler product `(q; q)_n` (alias of `qPochhammer`). -/
def eulerProductTrunc (q : R) (n : Nat) : R :=
  qPochhammer q n

@[simp] theorem eulerProductTrunc_succ (q : R) (n : Nat) :
    eulerProductTrunc q (Nat.succ n) =
      eulerProductTrunc q n * (1 - q ^ (Nat.succ n)) := by
  rfl

/-- Theorem 4.1: left side. -/
noncomputable def theorem41LHS (q : ℂ) (a : Nat) : ℂ :=
  jacobiInfiniteProduct (q ^ 2) (-(q ^ a))

/-- Exponent `5n - 2 - 2a` from the first product in Chan Theorem 4.1. -/
def theorem41SecondExponent (a n : Nat) : Nat :=
  Int.toNat (5 * (n : Int) - 2 - 2 * (a : Int))

/-- Exponent `5n - 3 + 2a` from the first product in Chan Theorem 4.1. -/
def theorem41ThirdExponent (a n : Nat) : Nat :=
  Int.toNat (5 * (n : Int) - 3 + 2 * (a : Int))

/-- Exponent `j(5j+1)/2 - 2aj` from the bilateral sum in Chan Theorem 4.1. -/
def theorem41Index (a : Nat) (j : Int) : Nat :=
  Int.toNat ((j * (5 * j + 1)) / 2 - 2 * (a : Int) * j)

/--
Theorem 4.1 LHS truncated:
`∏_{n=1}^{N} (1 - q^{5n})(1 - q^{5n-2-2a})(1 - q^{5n-3+2a})`.
-/
noncomputable def theorem41LHSTrunc (q : R) (a : Nat) : Nat → R
  | 0 => 1
  | Nat.succ n =>
      theorem41LHSTrunc q a n *
        (1 - q ^ (5 * Nat.succ n)) *
        (1 - q ^ theorem41SecondExponent a (Nat.succ n)) *
        (1 - q ^ theorem41ThirdExponent a (Nat.succ n))

/-- Recursion for `theorem41LHSTrunc`: pulls the multiplicative step out
of the case-by-case `_one`, `_two`, ... closed-form theorems. -/
theorem theorem41LHSTrunc_succ (q : R) (a : Nat) (n : Nat) :
    theorem41LHSTrunc q a (n + 1) =
      theorem41LHSTrunc q a n *
        (1 - q ^ (5 * (n + 1))) *
        (1 - q ^ theorem41SecondExponent a (n + 1)) *
        (1 - q ^ theorem41ThirdExponent a (n + 1)) := rfl

/-- Theorem 4.1 RHS truncated: `∑_{j=-N}^{N} (-1)^j q^{j(5j+1)/2 - 2aj}`. -/
noncomputable def theorem41RHSTrunc (q : R) (a N : Nat) : R :=
  bilateralSum (fun j : Int => (-1 : R) ^ j.toNat * q ^ theorem41Index a j) N

/-- Sanity: at `N = 0` both sides equal 1. -/
theorem theorem41_truncated_zero (q : R) (a : Nat) :
    theorem41LHSTrunc q a 0 = 1 ∧ theorem41RHSTrunc q a 0 = 1 := by
  constructor
  · rfl
  · simp [theorem41RHSTrunc, theorem41Index]

/- The infinite Theorem 4.1 equality is now reduced to specializing JTP and
rewriting the resulting product and bilateral series into Chan's displayed form. -/

/-- Euler's pentagonal theorem (Theorem 4.2): product side. -/
noncomputable def eulerPentagonalProduct (q : ℂ) : ℂ :=
  jacobiInfiniteProduct q (-1)

/-- Nat-indexed product factor for the `z = -1` JTP specialization. -/
noncomputable def eulerPentagonalJacobiProductFactor (q : ℂ) (n : ℕ) : ℂ :=
  (1 - q ^ (2 * (n + 1))) *
    (1 - q ^ (2 * (n + 1) - 1)) *
    (1 - q ^ (2 * (n + 1) - 1))

/-- The `z = -1` product side as a Nat-indexed infinite product. -/
theorem eulerPentagonalProduct_eq_tprod_natFactor (q : ℂ) :
    eulerPentagonalProduct q = ∏' n : ℕ, eulerPentagonalJacobiProductFactor q n := by
  rw [eulerPentagonalProduct, Ch02.jacobiInfiniteProduct_eq_tprod_natFactor]
  exact tprod_congr fun n => by
    simp [eulerPentagonalJacobiProductFactor, Ch02.jacobiProductNatFactor,
      Ch02.jacobiProductEvenFactor, Ch02.jacobiProductOddFactor, sub_eq_add_neg]

/-- The Jacobi-series side obtained from the `z = -1` specialization. -/
noncomputable def eulerPentagonalJacobiSeries (q : ℂ) : ℂ :=
  jacobiInfiniteSeries q (-1)

/-- The `z = -1` Jacobi triple product specialization used in Chapter 4. -/
theorem eulerPentagonalProduct_eq_jacobiSeries (q : ℂ) (hq : ‖q‖ < 1) :
    eulerPentagonalProduct q = eulerPentagonalJacobiSeries q := by
  exact jacobiTripleProduct q (-1) hq (by norm_num)

/-- The `z = -1` JTP specialization as an explicit bilateral theta series. -/
theorem eulerPentagonalProduct_eq_jacobi_tsum (q : ℂ) (hq : ‖q‖ < 1) :
    eulerPentagonalProduct q = ∑' n : ℤ, (-1 : ℂ) ^ n * q ^ (n ^ 2) := by
  simpa [eulerPentagonalJacobiSeries, jacobiInfiniteSeries]
    using eulerPentagonalProduct_eq_jacobiSeries q hq

/-- The named `z = -1` Jacobi-series side is the corresponding `tsum`. -/
theorem eulerPentagonalJacobiSeries_eq_tsum (q : ℂ) :
    eulerPentagonalJacobiSeries q = ∑' n : ℤ, (-1 : ℂ) ^ n * q ^ (n ^ 2) := by
  rfl

/-- The bilateral theta terms in the `z = -1` specialization are summable. -/
theorem summable_eulerPentagonal_jacobi_terms (q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℤ => (-1 : ℂ) ^ n * q ^ (n ^ 2) :=
  Ch02.summable_jacobiInfiniteSeries_terms q (-1) hq

/-- HasSum form of the `z = -1` JTP specialization. -/
theorem hasSum_eulerPentagonal_jacobi_terms (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℤ => (-1 : ℂ) ^ n * q ^ (n ^ 2)) (eulerPentagonalProduct q) := by
  rw [eulerPentagonalProduct_eq_jacobi_tsum q hq]
  exact (summable_eulerPentagonal_jacobi_terms q hq).hasSum

/-- HasProd form of the `z = -1` product-side specialization. -/
theorem hasProd_eulerPentagonal_jacobi_factors (q : ℂ) (hq : ‖q‖ < 1) :
    HasProd (fun n : ℕ => eulerPentagonalJacobiProductFactor q n)
      (eulerPentagonalProduct q) := by
  simpa [eulerPentagonalProduct] using
    (Ch02.hasProd_jacobiProductNatFactor q (-1) hq).congr_fun (fun n => by
      simp [eulerPentagonalJacobiProductFactor, Ch02.jacobiProductNatFactor,
        Ch02.jacobiProductEvenFactor, Ch02.jacobiProductOddFactor, sub_eq_add_neg])

/--
The three residue-class product factor obtained in Euler's pentagonal theorem
from the JTP substitution `Q^2 = q^3`, `z = -Q/q^2`.
-/
noncomputable def eulerPentagonalCubicProductFactor (q : ℂ) (n : ℕ) : ℂ :=
  (1 - q ^ (3 * (n + 1))) *
    (1 - q ^ (3 * (n + 1) - 2)) *
    (1 - q ^ (3 * (n + 1) - 1))

/-- The even JTP product factor under the Euler pentagonal substitution. -/
theorem jacobiProductEvenFactor_eulerPentagonal_substitution
    (q Q : ℂ) (hQ : Q ^ 2 = q ^ 3) (n : ℕ) :
    Ch02.jacobiProductEvenFactor Q n = 1 - q ^ (3 * (n + 1)) := by
  simp [Ch02.jacobiProductEvenFactor]
  rw [show Q ^ (2 * (n + 1)) = (Q ^ 2) ^ (n + 1) by rw [pow_mul]]
  rw [hQ]
  rw [pow_mul]

/-- The `z` odd JTP product factor under the Euler pentagonal substitution. -/
theorem jacobiProductOddFactor_eulerPentagonal_substitution_left
    (q Q : ℂ) (hq : q ≠ 0) (hQ : Q ^ 2 = q ^ 3) (n : ℕ) :
    Ch02.jacobiProductOddFactor Q (-(Q / q ^ 2)) n =
      1 - q ^ (3 * (n + 1) - 2) := by
  have hpow : Q ^ (2 * (n + 1) - 1) = Q * (Q ^ 2) ^ n := by
    rw [show 2 * (n + 1) - 1 = 1 + 2 * n by omega]
    rw [pow_add, pow_mul]
    simp
  have hterm :
      (-(Q / q ^ 2)) * Q ^ (2 * (n + 1) - 1) =
        -q ^ (3 * (n + 1) - 2) := by
    rw [hpow, hQ]
    rw [← pow_mul]
    rw [show 3 * (n + 1) - 2 = 1 + 3 * n by omega]
    rw [pow_add]
    field_simp [hq]
    rw [hQ]
  rw [Ch02.jacobiProductOddFactor, hterm]
  ring

/-- The `z⁻¹` odd JTP product factor under the Euler pentagonal substitution. -/
theorem jacobiProductOddFactor_eulerPentagonal_substitution_right
    (q Q : ℂ) (hq : q ≠ 0) (hQ : Q ^ 2 = q ^ 3) (n : ℕ) :
    Ch02.jacobiProductOddFactor Q (-(Q / q ^ 2))⁻¹ n =
      1 - q ^ (3 * (n + 1) - 1) := by
  have hQnz : Q ≠ 0 := by
    intro hzero
    have hq3 : q ^ 3 ≠ 0 := pow_ne_zero 3 hq
    apply hq3
    rw [← hQ, hzero]
    norm_num
  have hpow : Q ^ (2 * (n + 1) - 1) = Q * (Q ^ 2) ^ n := by
    rw [show 2 * (n + 1) - 1 = 1 + 2 * n by omega]
    rw [pow_add, pow_mul]
    simp
  have hterm :
      (-(Q / q ^ 2))⁻¹ * Q ^ (2 * (n + 1) - 1) =
        -q ^ (3 * (n + 1) - 1) := by
    rw [hpow, hQ]
    rw [← pow_mul]
    rw [show 3 * (n + 1) - 1 = 2 + 3 * n by omega]
    rw [pow_add]
    field_simp [hq, hQnz]
  rw [Ch02.jacobiProductOddFactor, hterm]
  ring

/-- The full Nat-indexed JTP product factor under the Euler pentagonal substitution. -/
theorem jacobiProductNatFactor_eulerPentagonal_substitution
    (q Q : ℂ) (hq : q ≠ 0) (hQ : Q ^ 2 = q ^ 3) (n : ℕ) :
    Ch02.jacobiProductNatFactor Q (-(Q / q ^ 2)) n =
      eulerPentagonalCubicProductFactor q n := by
  rw [Ch02.jacobiProductNatFactor, eulerPentagonalCubicProductFactor,
    jacobiProductEvenFactor_eulerPentagonal_substitution q Q hQ n,
    jacobiProductOddFactor_eulerPentagonal_substitution_left q Q hq hQ n,
    jacobiProductOddFactor_eulerPentagonal_substitution_right q Q hq hQ n]

/-- Product-side JTP under the Euler pentagonal substitution as a Nat-indexed product. -/
theorem jacobiInfiniteProduct_eulerPentagonal_substitution_eq_tprod
    (q Q : ℂ) (hq : q ≠ 0) (hQ : Q ^ 2 = q ^ 3) :
    jacobiInfiniteProduct Q (-(Q / q ^ 2)) =
      ∏' n : ℕ, eulerPentagonalCubicProductFactor q n := by
  rw [Ch02.jacobiInfiniteProduct_eq_tprod_natFactor]
  exact tprod_congr fun n =>
    jacobiProductNatFactor_eulerPentagonal_substitution q Q hq hQ n

/-- HasProd form of the product-side Euler pentagonal JTP substitution. -/
theorem hasProd_eulerPentagonal_cubic_factors
    (q Q : ℂ) (hQnorm : ‖Q‖ < 1) (hq : q ≠ 0) (hQ : Q ^ 2 = q ^ 3) :
    HasProd (fun n : ℕ => eulerPentagonalCubicProductFactor q n)
      (jacobiInfiniteProduct Q (-(Q / q ^ 2))) := by
  simpa using
    (Ch02.hasProd_jacobiProductNatFactor Q (-(Q / q ^ 2)) hQnorm).congr_fun
      (fun n =>
        (jacobiProductNatFactor_eulerPentagonal_substitution q Q hq hQ n).symm)

/-- Finite residue-class product skeleton for Euler's pentagonal theorem. -/
theorem eulerPentagonalCubicProduct_partial_eq_qPochhammer (q : ℂ) (N : ℕ) :
    (∏ n ∈ Finset.range N, eulerPentagonalCubicProductFactor q n) =
      qPochhammer q (3 * N) := by
  induction N with
  | zero =>
      simp [eulerPentagonalCubicProductFactor]
  | succ N ih =>
      rw [Finset.prod_range_succ, ih]
      have hpoch :
          qPochhammer q (3 * (N + 1)) =
            qPochhammer q (3 * N) *
              (1 - q ^ (3 * N + 1)) *
              (1 - q ^ (3 * N + 2)) *
              (1 - q ^ (3 * N + 3)) := by
        rw [show 3 * (N + 1) = Nat.succ (Nat.succ (Nat.succ (3 * N))) by omega]
        simp only [qPochhammer_succ]
      rw [hpoch]
      simp [eulerPentagonalCubicProductFactor,
        show 3 * (N + 1) = 3 * N + 3 by omega]
      ring

/-- Finite Ch02 JTP product partial under the Euler pentagonal substitution. -/
theorem jacobiProductPartial_eulerPentagonal_substitution
    (q Q : ℂ) (hq : q ≠ 0) (hQ : Q ^ 2 = q ^ 3) (N : ℕ) :
    Ch02.jacobiProductPartial Q (-(Q / q ^ 2)) N = qPochhammer q (3 * N) := by
  rw [Ch02.jacobiProductPartial]
  calc
    (∏ n ∈ Finset.range N, Ch02.jacobiProductNatFactor Q (-(Q / q ^ 2)) n)
        = ∏ n ∈ Finset.range N, eulerPentagonalCubicProductFactor q n := by
          exact Finset.prod_congr rfl fun n _ =>
            jacobiProductNatFactor_eulerPentagonal_substitution q Q hq hQ n
    _ = qPochhammer q (3 * N) :=
          eulerPentagonalCubicProduct_partial_eq_qPochhammer q N

private lemma int_two_dvd_mul_succ (l : Int) : (2 : Int) ∣ l * (l + 1) := by
  rcases Int.even_or_odd l with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨m * (l + 1), by rw [hm]; ring⟩
  · exact ⟨l * (m + 1), by rw [hm]; ring⟩

private lemma int_two_dvd_mul_three_sub_one (l : Int) : (2 : Int) ∣ l * (3 * l - 1) := by
  rcases Int.even_or_odd l with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨m * (3 * l - 1), by rw [hm]; ring⟩
  · exact ⟨l * (3 * m + 1), by rw [hm]; ring⟩

private lemma int_three_mul_tri_sub_two_eq (j : Int) :
    3 * (j * (j + 1) / 2) - 2 * j = j * (3 * j - 1) / 2 := by
  have h1 : (2 : Int) ∣ j * (j + 1) := int_two_dvd_mul_succ j
  have h2 : (2 : Int) ∣ j * (3 * j - 1) := int_two_dvd_mul_three_sub_one j
  apply (mul_right_injective₀ (show (2 : Int) ≠ 0 by norm_num))
  calc
    2 * (3 * (j * (j + 1) / 2) - 2 * j) = 3 * (j * (j + 1)) - 4 * j := by
      rw [mul_sub]
      rw [show 2 * (3 * (j * (j + 1) / 2)) =
          3 * ((j * (j + 1) / 2) * 2) by ring]
      rw [Int.ediv_mul_cancel h1]
      ring
    _ = j * (3 * j - 1) := by ring
    _ = 2 * (j * (3 * j - 1) / 2) := by
      rw [show 2 * (j * (3 * j - 1) / 2) =
          (j * (3 * j - 1) / 2) * 2 by ring]
      rw [Int.ediv_mul_cancel h2]

private lemma zpow_Q_sq_eulerPentagonal_substitution
    (q Q : ℂ) (hQ : Q ^ 2 = q ^ 3) (j : Int) :
    Q ^ (j * (j + 1)) = q ^ (3 * (j * (j + 1) / 2)) := by
  have hdiv : (2 : Int) ∣ j * (j + 1) := int_two_dvd_mul_succ j
  have hmul : 2 * (j * (j + 1) / 2) = j * (j + 1) := by
    rw [show 2 * (j * (j + 1) / 2) = (j * (j + 1) / 2) * 2 by ring]
    exact Int.ediv_mul_cancel hdiv
  calc
    Q ^ (j * (j + 1)) = Q ^ (2 * (j * (j + 1) / 2)) := by rw [hmul]
    _ = (Q ^ (2 : Int)) ^ (j * (j + 1) / 2) := by rw [zpow_mul]
    _ = (Q ^ 2) ^ (j * (j + 1) / 2) := by rfl
    _ = (q ^ 3) ^ (j * (j + 1) / 2) := by rw [hQ]
    _ = q ^ (3 * (j * (j + 1) / 2)) := by
      simpa using (zpow_mul q (3 : ℤ) (j * (j + 1) / 2)).symm

/-- Term-level series-side algebra for the Euler pentagonal JTP substitution. -/
theorem jacobiSeriesTerm_eulerPentagonal_substitution
    (q Q : ℂ) (hq : q ≠ 0) (hQ : Q ^ 2 = q ^ 3) (j : Int) :
    (-(Q / q ^ 2)) ^ j * Q ^ (j ^ 2) =
      (-1 : ℂ) ^ j * q ^ (j * (3 * j - 1) / 2) := by
  rw [show j ^ 2 = j * j by ring]
  have hQnz : Q ≠ 0 := by
    intro hzero
    have hq3 : q ^ 3 ≠ 0 := pow_ne_zero 3 hq
    apply hq3
    rw [← hQ, hzero]
    norm_num
  have hbase : (-(Q / q ^ 2) : ℂ) = (-1 : ℂ) * Q * q ^ (-2 : ℤ) := by
    field_simp [hq]
  have hqneg : ((q ^ (-2 : ℤ)) ^ j) = q ^ ((-2 : ℤ) * j) := by
    simpa using (zpow_mul q (-2 : ℤ) j).symm
  rw [hbase]
  rw [mul_zpow, mul_zpow]
  rw [show ((-1 : ℂ) ^ j * Q ^ j * ((q ^ (-2 : ℤ)) ^ j)) * Q ^ (j * j) =
      (-1 : ℂ) ^ j * (Q ^ j * Q ^ (j * j)) * ((q ^ (-2 : ℤ)) ^ j) by ring]
  rw [← zpow_add₀ hQnz]
  rw [show j + j * j = j * (j + 1) by ring]
  rw [zpow_Q_sq_eulerPentagonal_substitution q Q hQ j]
  rw [hqneg]
  rw [show (-1 : ℂ) ^ j * q ^ (3 * (j * (j + 1) / 2)) * q ^ ((-2 : ℤ) * j) =
      (-1 : ℂ) ^ j * (q ^ (3 * (j * (j + 1) / 2)) * q ^ ((-2 : ℤ) * j)) by ring]
  rw [← zpow_add₀ hq]
  rw [show 3 * (j * (j + 1) / 2) + (-2 : ℤ) * j =
      3 * (j * (j + 1) / 2) - 2 * j by ring]
  rw [int_three_mul_tri_sub_two_eq j]

/-- Series-side JTP under the Euler pentagonal substitution, before `j ↦ -j`. -/
theorem jacobiInfiniteSeries_eulerPentagonal_substitution_eq_tsum_minus
    (q Q : ℂ) (hq : q ≠ 0) (hQ : Q ^ 2 = q ^ 3) :
    jacobiInfiniteSeries Q (-(Q / q ^ 2)) =
      ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (3 * j - 1) / 2) := by
  rw [jacobiInfiniteSeries]
  exact tsum_congr fun j =>
    jacobiSeriesTerm_eulerPentagonal_substitution q Q hq hQ j

/-- Reindex the minus-pentagonal bilateral series by `j ↦ -j`. -/
theorem eulerPentagonal_tsum_minus_eq_plus (q : ℂ) :
    (∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (3 * j - 1) / 2)) =
      ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (3 * j + 1) / 2) := by
  rw [← (Equiv.neg ℤ).tsum_eq
    (fun j : ℤ => (-1 : ℂ) ^ j * q ^ (j * (3 * j - 1) / 2))]
  exact tsum_congr fun j => by
    simp only [Equiv.neg_apply]
    have hsign : (-1 : ℂ) ^ (-j) = (-1 : ℂ) ^ j := by
      by_cases h : Even j <;> simp [neg_one_zpow_eq_ite, h]
    rw [hsign]
    congr 1
    ring_nf

/-- Series-side JTP under the Euler pentagonal substitution in Chan's exponent form. -/
theorem jacobiInfiniteSeries_eulerPentagonal_substitution_eq_tsum_plus
    (q Q : ℂ) (hq : q ≠ 0) (hQ : Q ^ 2 = q ^ 3) :
    jacobiInfiniteSeries Q (-(Q / q ^ 2)) =
      ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (3 * j + 1) / 2) := by
  rw [jacobiInfiniteSeries_eulerPentagonal_substitution_eq_tsum_minus q Q hq hQ]
  exact eulerPentagonal_tsum_minus_eq_plus q

/-- The Euler pentagonal JTP substitution, with product side grouped by residues mod `3`. -/
theorem eulerPentagonal_cubicProduct_eq_tsum
    (q Q : ℂ) (hQnorm : ‖Q‖ < 1) (hq : q ≠ 0) (hQ : Q ^ 2 = q ^ 3) :
    (∏' n : ℕ, eulerPentagonalCubicProductFactor q n) =
      ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (3 * j + 1) / 2) := by
  have hQnz : Q ≠ 0 := by
    intro hzero
    have hq3 : q ^ 3 ≠ 0 := pow_ne_zero 3 hq
    apply hq3
    rw [← hQ, hzero]
    norm_num
  have hz : (-(Q / q ^ 2) : ℂ) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero hQnz (pow_ne_zero 2 hq))
  calc
    (∏' n : ℕ, eulerPentagonalCubicProductFactor q n)
        = jacobiInfiniteProduct Q (-(Q / q ^ 2)) := by
          exact (jacobiInfiniteProduct_eulerPentagonal_substitution_eq_tprod q Q hq hQ).symm
    _ = jacobiInfiniteSeries Q (-(Q / q ^ 2)) :=
          jacobiTripleProduct Q (-(Q / q ^ 2)) hQnorm hz
    _ = ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (3 * j + 1) / 2) :=
          jacobiInfiniteSeries_eulerPentagonal_substitution_eq_tsum_plus q Q hq hQ

/-! ## Mod-5 residue factors for Rogers-Ramanujan (Ch7 dependency)

The classical R-R proof needs:
`(q;q)_∞ = ∏_{k=1..5} (q^k;q^5)_∞`.

Each factor `(q^k;q^5)_∞` = `∏'_n (1 - q^(k + 5n))` for `n ≥ 0`. -/

/-- `(q^k; q^5)_∞` truncated factor: `1 - q^k · q^(5n) = 1 - q^(k + 5n)`. -/
def rrMod5Factor (q : ℂ) (k : ℕ) (n : ℕ) : ℂ :=
  1 - q ^ (k + 5 * n)

@[simp] theorem rrMod5Factor_def (q : ℂ) (k n : ℕ) :
    rrMod5Factor q k n = 1 - q ^ (k + 5 * n) := rfl

/-- For ‖q‖ < 1 and k ≥ 1: `Summable fun n => ‖-q^k · (q^5)^n‖`. -/
private theorem summable_norm_rrMod5_tail (q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) :
    Summable fun n : ℕ => ‖-q ^ k * (q ^ 5) ^ n‖ := by
  have hq5 : ‖q ^ 5‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  exact Ch02.summable_norm_mul_geometric_complex (-(q ^ k)) (q ^ 5) hq5

/-- The k-th mod-5 residue factor family is multipliable for ‖q‖ < 1. -/
theorem multipliable_rrMod5Factor (q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) :
    Multipliable fun n : ℕ => rrMod5Factor q k n := by
  have h := multipliable_one_add_of_summable (summable_norm_rrMod5_tail q hq k)
  refine h.congr fun n => ?_
  simp only [rrMod5Factor]
  rw [show q ^ (k + 5 * n) = q ^ k * (q ^ 5) ^ n by
    rw [pow_add, pow_mul]]
  ring

/-- Each rrMod5Factor is nonzero for `‖q‖ < 1` and `k ≥ 1`. -/
theorem rrMod5Factor_ne_zero (q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    rrMod5Factor q k n ≠ 0 := by
  intro hzero
  have h_eq : q ^ (k + 5 * n) = 1 := by
    have : 1 - q ^ (k + 5 * n) = 0 := by simpa [rrMod5Factor] using hzero
    linear_combination -this
  have h_norm_one : ‖q ^ (k + 5 * n)‖ = 1 := by rw [h_eq, norm_one]
  rw [norm_pow] at h_norm_one
  have hq_nn : 0 ≤ ‖q‖ := norm_nonneg _
  have hexp_pos : 0 < k + 5 * n := by omega
  have h_lt : ‖q‖ ^ (k + 5 * n) < 1 :=
    pow_lt_one₀ hq_nn hq hexp_pos.ne'
  linarith

/-! ### Rogers-Ramanujan theta series via JTP at q^5

S₁(q) := ∑'_{j : ℤ} (-1)^j · q^(j(5j+1)/2) — JTP series at Q := Y^5, z := -Y (Y² = q).
S₂(q) := ∑'_{j : ℤ} (-1)^j · q^(j(5j+3)/2) — JTP series at Q := Y^5, z := -Y^3 (Y² = q).
-/

/-- Identity needed for series-side: `2 · (j(5j+1)/2) = j(5j+1)`. -/
private lemma int_two_dvd_j_mul_five_j_add_one (j : Int) : (2 : Int) ∣ j * (5 * j + 1) := by
  rcases Int.even_or_odd j with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨m * (5 * j + 1), by rw [hm]; ring⟩
  · exact ⟨j * (5 * m + 3), by rw [hm]; ring⟩

/-- Identity needed for series-side: `2 · (j(5j+3)/2) = j(5j+3)`. -/
private lemma int_two_dvd_j_mul_five_j_add_three (j : Int) : (2 : Int) ∣ j * (5 * j + 3) := by
  rcases Int.even_or_odd j with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨m * (5 * j + 3), by rw [hm]; ring⟩
  · exact ⟨j * (5 * m + 4), by rw [hm]; ring⟩

/-- For Y² = q and Y ≠ 0: `Y^(j(5j+1)) = q^(j(5j+1)/2)` for all j : ℤ.
This is the key algebraic identity for the JTP series-to-theta translation. -/
private lemma rr_zpow_Y_five_j_plus_one (Y q : ℂ) (hYq : Y ^ 2 = q) (j : Int) :
    Y ^ (j * (5 * j + 1)) = q ^ (j * (5 * j + 1) / 2) := by
  have hdiv : (2 : Int) ∣ j * (5 * j + 1) := int_two_dvd_j_mul_five_j_add_one j
  have hmul : 2 * (j * (5 * j + 1) / 2) = j * (5 * j + 1) := by
    rw [show 2 * (j * (5 * j + 1) / 2) = (j * (5 * j + 1) / 2) * 2 by ring]
    exact Int.ediv_mul_cancel hdiv
  calc
    Y ^ (j * (5 * j + 1)) = Y ^ (2 * (j * (5 * j + 1) / 2)) := by rw [hmul]
    _ = (Y ^ (2 : Int)) ^ (j * (5 * j + 1) / 2) := by rw [zpow_mul]
    _ = (Y ^ 2) ^ (j * (5 * j + 1) / 2) := by rfl
    _ = q ^ (j * (5 * j + 1) / 2) := by rw [hYq]

/-- Analogous identity for `5j + 3`. -/
private lemma rr_zpow_Y_five_j_plus_three (Y q : ℂ) (hYq : Y ^ 2 = q) (j : Int) :
    Y ^ (j * (5 * j + 3)) = q ^ (j * (5 * j + 3) / 2) := by
  have hdiv : (2 : Int) ∣ j * (5 * j + 3) := int_two_dvd_j_mul_five_j_add_three j
  have hmul : 2 * (j * (5 * j + 3) / 2) = j * (5 * j + 3) := by
    rw [show 2 * (j * (5 * j + 3) / 2) = (j * (5 * j + 3) / 2) * 2 by ring]
    exact Int.ediv_mul_cancel hdiv
  calc
    Y ^ (j * (5 * j + 3)) = Y ^ (2 * (j * (5 * j + 3) / 2)) := by rw [hmul]
    _ = (Y ^ (2 : Int)) ^ (j * (5 * j + 3) / 2) := by rw [zpow_mul]
    _ = (Y ^ 2) ^ (j * (5 * j + 3) / 2) := by rfl
    _ = q ^ (j * (5 * j + 3) / 2) := by rw [hYq]

/-- The first theta series equals jacobiInfiniteSeries at (Y^5, -Y). -/
theorem theta_sum_1_eq_jacobiSeries (q Y : ℂ) (hYne : Y ≠ 0) (hYq : Y ^ 2 = q) :
    (Ch02.jacobiInfiniteSeries (Y ^ 5) (-Y) : ℂ) =
      ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (5 * j + 1) / 2) := by
  rw [Ch02.jacobiInfiniteSeries]
  refine tsum_congr fun j => ?_
  -- Term: (-Y)^j · (Y^5)^(j²) = (-1)^j · Y^j · Y^(5j²) = (-1)^j · Y^(j + 5j²) = (-1)^j · q^(j(5j+1)/2).
  have h1 : (-Y : ℂ) ^ j = (-1) ^ j * Y ^ j := by
    rw [show (-Y : ℂ) = (-1 : ℂ) * Y from by ring]
    rw [mul_zpow]
  have h2 : ((Y : ℂ) ^ 5) ^ (j ^ 2) = Y ^ (5 * (j * j)) := by
    rw [show j ^ 2 = j * j from by ring]
    rw [show ((Y : ℂ) ^ 5) ^ (j * j) = (Y ^ (5 : ℤ)) ^ (j * j) from rfl]
    rw [← zpow_mul]
  rw [h1, h2]
  have h_mul : Y ^ j * Y ^ (5 * (j * j)) = Y ^ (j + 5 * (j * j)) := by
    rw [← zpow_add₀ hYne]
  have h_exp : (j + 5 * (j * j) : ℤ) = j * (5 * j + 1) := by ring
  rw [show ((-1 : ℂ) ^ j * Y ^ j) * Y ^ (5 * (j * j)) =
          (-1) ^ j * (Y ^ j * Y ^ (5 * (j * j))) from by ring]
  rw [h_mul, h_exp]
  rw [rr_zpow_Y_five_j_plus_one Y q hYq j]

/-- The second theta series equals jacobiInfiniteSeries at (Y^5, -Y^3). -/
theorem theta_sum_2_eq_jacobiSeries (q Y : ℂ) (hYne : Y ≠ 0) (hYq : Y ^ 2 = q) :
    (Ch02.jacobiInfiniteSeries (Y ^ 5) (-Y ^ 3) : ℂ) =
      ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (5 * j + 3) / 2) := by
  rw [Ch02.jacobiInfiniteSeries]
  refine tsum_congr fun j => ?_
  have h1 : (-(Y ^ 3) : ℂ) ^ j = (-1) ^ j * (Y ^ 3) ^ j := by
    rw [show (-(Y ^ 3) : ℂ) = (-1 : ℂ) * Y ^ 3 from by ring]
    rw [mul_zpow]
  have h_Y3 : ((Y : ℂ) ^ 3) ^ j = Y ^ (3 * j) := by
    rw [show ((Y : ℂ) ^ 3 : ℂ) = Y ^ (3 : ℤ) from rfl]
    rw [← zpow_mul]
  have h2 : ((Y : ℂ) ^ 5) ^ (j ^ 2) = Y ^ (5 * (j * j)) := by
    rw [show j ^ 2 = j * j from by ring]
    rw [show ((Y : ℂ) ^ 5) ^ (j * j) = (Y ^ (5 : ℤ)) ^ (j * j) from rfl]
    rw [← zpow_mul]
  rw [h1, h_Y3, h2]
  rw [show ((-1 : ℂ) ^ j * Y ^ (3 * j)) * Y ^ (5 * (j * j)) =
          (-1) ^ j * (Y ^ (3 * j) * Y ^ (5 * (j * j))) from by ring]
  rw [← zpow_add₀ hYne]
  have h_exp : (3 * j + 5 * (j * j) : ℤ) = j * (5 * j + 3) := by ring
  rw [h_exp, rr_zpow_Y_five_j_plus_three Y q hYq j]

/-- For Y² = q: `(Y^5)^(2m) = q^(5m)`. -/
private lemma Y_pow_five_even (Y q : ℂ) (hYq : Y ^ 2 = q) (m : ℕ) :
    (Y ^ 5) ^ (2 * m) = q ^ (5 * m) := by
  rw [← pow_mul, show 5 * (2 * m) = 2 * (5 * m) from by ring, pow_mul, hYq]

/-- jacobiProductNatFactor at (Y^5, -Y) equals the mod-5 triple (k=5,3,2). -/
private theorem jacobiProductNatFactor_S1_substitution
    (q Y : ℂ) (hYne : Y ≠ 0) (hYq : Y ^ 2 = q) (n : ℕ) :
    Ch02.jacobiProductNatFactor (Y ^ 5) (-Y) n =
      rrMod5Factor q 5 n * rrMod5Factor q 3 n * rrMod5Factor q 2 n := by
  have hEven : (Y ^ 5) ^ (2 * (n + 1)) = q ^ (5 + 5 * n) := by
    rw [show 2 * (n + 1) = 2 * (n + 1) from rfl, Y_pow_five_even Y q hYq (n + 1)]
    congr 1; ring
  have hOddBase : (Y ^ 5) ^ (2 * (n + 1) - 1) = Y * q ^ (5 * n + 2) := by
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 from by omega]
    rw [pow_succ, Y_pow_five_even Y q hYq n]
    have hY5 : (Y : ℂ) ^ 5 = Y * (Y ^ 2) ^ 2 := by ring
    rw [hY5, hYq]
    rw [show q ^ (5 * n + 2) = q ^ (5 * n) * q ^ 2 from by rw [← pow_add]]
    ring
  simp only [Ch02.jacobiProductNatFactor, Ch02.jacobiProductEvenFactor,
    Ch02.jacobiProductOddFactor, rrMod5Factor]
  rw [hEven, hOddBase]
  have h_inv : (-Y : ℂ)⁻¹ = -Y⁻¹ := by rw [neg_inv]
  rw [h_inv]
  have h_term2 : -Y * (Y * q ^ (5 * n + 2)) = -q ^ (5 * n + 3) := by
    have hYY : Y * Y = q := by rw [← sq, hYq]
    have h_succ : q ^ (5 * n + 3) = q * q ^ (5 * n + 2) := by
      rw [show 5 * n + 3 = 1 + (5 * n + 2) from by omega, pow_add, pow_one]
    rw [show -Y * (Y * q ^ (5 * n + 2)) = -(Y * Y) * q ^ (5 * n + 2) from by ring]
    rw [hYY, h_succ]; ring
  have h_term3 : -Y⁻¹ * (Y * q ^ (5 * n + 2)) = -q ^ (5 * n + 2) := by
    field_simp
  rw [h_term2, h_term3]
  -- Goal: (1 - q^(5+5n)) * (1 + -q^(5n+3)) * (1 + -q^(5n+2))
  --       = (1 - q^(5+5n)) * (1 - q^(3+5n)) * (1 - q^(2+5n))
  rw [show (5 * n + 3 : ℕ) = 3 + 5 * n from by omega,
      show (5 * n + 2 : ℕ) = 2 + 5 * n from by omega]
  ring

/-- For Y² = q with ‖q‖ < 1: ‖Y^5‖ < 1. -/
private lemma norm_Y_pow_5_lt_one (Y q : ℂ) (hYq : Y ^ 2 = q) (hq : ‖q‖ < 1) :
    ‖Y ^ 5‖ < 1 := by
  have hY_sq : ‖Y‖ ^ 2 = ‖q‖ := by
    rw [← norm_pow, hYq]
  have hY_nn : 0 ≤ ‖Y‖ := norm_nonneg _
  have hY_lt : ‖Y‖ < 1 := by
    have h := hq
    rw [← hY_sq] at h
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by simpa using h)
  rw [norm_pow]
  exact pow_lt_one₀ hY_nn hY_lt (by norm_num)

/-- The JTP product at (Y^5, -Y) decomposes into the mod-5 triple. -/
theorem jacobiInfiniteProduct_S1_eq_mod5_triple
    (q Y : ℂ) (hYne : Y ≠ 0) (hYq : Y ^ 2 = q) (hq : ‖q‖ < 1) :
    Ch02.jacobiInfiniteProduct (Y ^ 5) (-Y) =
      (∏' n : ℕ, rrMod5Factor q 5 n) * (∏' n : ℕ, rrMod5Factor q 3 n) *
      (∏' n : ℕ, rrMod5Factor q 2 n) := by
  have hY5norm : ‖Y ^ 5‖ < 1 := norm_Y_pow_5_lt_one Y q hYq hq
  -- HasProd for each factor.
  have hP5 := (multipliable_rrMod5Factor q hq 5).hasProd
  have hP3 := (multipliable_rrMod5Factor q hq 3).hasProd
  have hP2 := (multipliable_rrMod5Factor q hq 2).hasProd
  -- Triple HasProd via .mul.
  have hP_triple : HasProd
      (fun n : ℕ => rrMod5Factor q 5 n * rrMod5Factor q 3 n * rrMod5Factor q 2 n)
      ((∏' n, rrMod5Factor q 5 n) * (∏' n, rrMod5Factor q 3 n) *
       (∏' n, rrMod5Factor q 2 n)) :=
    (hP5.mul hP3).mul hP2
  -- Connect to jacobiProductNatFactor via the term-level identification.
  have hP_eq : HasProd (fun n : ℕ => Ch02.jacobiProductNatFactor (Y ^ 5) (-Y) n)
      ((∏' n, rrMod5Factor q 5 n) * (∏' n, rrMod5Factor q 3 n) *
       (∏' n, rrMod5Factor q 2 n)) := by
    refine hP_triple.congr_fun fun n => ?_
    exact jacobiProductNatFactor_S1_substitution q Y hYne hYq n
  rw [Ch02.jacobiInfiniteProduct_eq_tprod_natFactor]
  exact hP_eq.tprod_eq

/-- Term-level identification for S₂: jacobiProductNatFactor (Y^5) (-Y^3) =
mod-5 triple-factor for residues k=5,4,1. -/
private theorem jacobiProductNatFactor_S2_substitution
    (q Y : ℂ) (hYne : Y ≠ 0) (hYq : Y ^ 2 = q) (n : ℕ) :
    Ch02.jacobiProductNatFactor (Y ^ 5) (-Y ^ 3) n =
      rrMod5Factor q 5 n * rrMod5Factor q 4 n * rrMod5Factor q 1 n := by
  have hEven : (Y ^ 5) ^ (2 * (n + 1)) = q ^ (5 + 5 * n) := by
    rw [Y_pow_five_even Y q hYq (n + 1)]
    congr 1; ring
  have hOddBase : (Y ^ 5) ^ (2 * (n + 1) - 1) = Y * q ^ (5 * n + 2) := by
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 from by omega]
    rw [pow_succ, Y_pow_five_even Y q hYq n]
    have hY5 : (Y : ℂ) ^ 5 = Y * (Y ^ 2) ^ 2 := by ring
    rw [hY5, hYq]
    rw [show q ^ (5 * n + 2) = q ^ (5 * n) * q ^ 2 from by rw [← pow_add]]
    ring
  simp only [Ch02.jacobiProductNatFactor, Ch02.jacobiProductEvenFactor,
    Ch02.jacobiProductOddFactor, rrMod5Factor]
  rw [hEven, hOddBase]
  -- 2nd factor: 1 + -Y³ · (Y · q^(5n+2)) = 1 - Y^4 · q^(5n+2) = 1 - q^(5n+4)
  have hY4 : (Y : ℂ) ^ 4 = q ^ 2 := by
    rw [show (Y : ℂ) ^ 4 = (Y ^ 2) ^ 2 from by ring, hYq]
  have h_term2 : -Y ^ 3 * (Y * q ^ (5 * n + 2)) = -q ^ (5 * n + 4) := by
    have : -Y ^ 3 * (Y * q ^ (5 * n + 2)) = -(Y ^ 4) * q ^ (5 * n + 2) := by ring
    rw [this, hY4]
    rw [show q ^ (5 * n + 4) = q ^ 2 * q ^ (5 * n + 2) from by
      rw [← pow_add]; congr 1; omega]
    ring
  -- 3rd factor: 1 + (-Y^3)⁻¹ · (Y · q^(5n+2)) = 1 - Y^(-2) · q^(5n+2) = 1 - q^(-1) · q^(5n+2) = 1 - q^(5n+1)
  have h_term3 : (-(Y ^ 3) : ℂ)⁻¹ * (Y * q ^ (5 * n + 2)) = -q ^ (5 * n + 1) := by
    have hY_ne : (Y : ℂ) ≠ 0 := hYne
    have h_inv_Y3 : (-(Y ^ 3) : ℂ)⁻¹ = -(Y ^ 3)⁻¹ := by rw [neg_inv]
    rw [h_inv_Y3]
    have hq_ne_zero : q ≠ 0 := by
      intro hq_eq
      apply hYne
      have : Y ^ 2 = 0 := hq_eq ▸ hYq
      exact pow_eq_zero_iff (n := 2) (by norm_num : (2 : ℕ) ≠ 0) |>.mp this
    have h_step : -(Y ^ 3)⁻¹ * (Y * q ^ (5 * n + 2)) = -((Y ^ 2)⁻¹ * q ^ (5 * n + 2)) := by
      field_simp
    rw [h_step, hYq]
    rw [show q ^ (5 * n + 2) = q * q ^ (5 * n + 1) from by
      rw [show 5 * n + 2 = (5 * n + 1) + 1 from by omega, pow_succ]; ring]
    field_simp
  rw [h_term2, h_term3]
  rw [show (5 * n + 4 : ℕ) = 4 + 5 * n from by omega,
      show (5 * n + 1 : ℕ) = 1 + 5 * n from by omega]
  ring

/-- The JTP product at (Y^5, -Y^3) decomposes into the S₂ mod-5 triple. -/
theorem jacobiInfiniteProduct_S2_eq_mod5_triple
    (q Y : ℂ) (hYne : Y ≠ 0) (hYq : Y ^ 2 = q) (hq : ‖q‖ < 1) :
    Ch02.jacobiInfiniteProduct (Y ^ 5) (-Y ^ 3) =
      (∏' n : ℕ, rrMod5Factor q 5 n) * (∏' n : ℕ, rrMod5Factor q 4 n) *
      (∏' n : ℕ, rrMod5Factor q 1 n) := by
  have hP5 := (multipliable_rrMod5Factor q hq 5).hasProd
  have hP4 := (multipliable_rrMod5Factor q hq 4).hasProd
  have hP1 := (multipliable_rrMod5Factor q hq 1).hasProd
  have hP_triple : HasProd
      (fun n : ℕ => rrMod5Factor q 5 n * rrMod5Factor q 4 n * rrMod5Factor q 1 n)
      ((∏' n, rrMod5Factor q 5 n) * (∏' n, rrMod5Factor q 4 n) *
       (∏' n, rrMod5Factor q 1 n)) :=
    (hP5.mul hP4).mul hP1
  have hP_eq : HasProd (fun n : ℕ => Ch02.jacobiProductNatFactor (Y ^ 5) (-Y ^ 3) n)
      ((∏' n, rrMod5Factor q 5 n) * (∏' n, rrMod5Factor q 4 n) *
       (∏' n, rrMod5Factor q 1 n)) := by
    refine hP_triple.congr_fun fun n => ?_
    exact jacobiProductNatFactor_S2_substitution q Y hYne hYq n
  rw [Ch02.jacobiInfiniteProduct_eq_tprod_natFactor]
  exact hP_eq.tprod_eq

/-- **Theorem**: theta sum S₂ via mod-5 product. -/
theorem theta_sum_2_eq_mod5_product (q : ℂ) (hq : ‖q‖ < 1) (hq_ne : q ≠ 0) :
    (∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (5 * j + 3) / 2)) =
      (∏' n : ℕ, rrMod5Factor q 5 n) * (∏' n : ℕ, rrMod5Factor q 4 n) *
      (∏' n : ℕ, rrMod5Factor q 1 n) := by
  obtain ⟨Y, hYq⟩ := IsAlgClosed.exists_pow_nat_eq q (n := 2) (by norm_num)
  have hYne : Y ≠ 0 := by
    intro hY_zero
    apply hq_ne
    rw [← hYq, hY_zero]; ring
  have hY5_norm : ‖Y ^ 5‖ < 1 := norm_Y_pow_5_lt_one Y q hYq hq
  have hnegY3_ne : (-(Y ^ 3) : ℂ) ≠ 0 := by
    refine neg_ne_zero.mpr ?_
    exact pow_ne_zero 3 hYne
  rw [← theta_sum_2_eq_jacobiSeries q Y hYne hYq]
  rw [← Ch02.jacobiTripleProduct (Y ^ 5) (-Y ^ 3) hY5_norm hnegY3_ne]
  exact jacobiInfiniteProduct_S2_eq_mod5_triple q Y hYne hYq hq

/-- **Theorem**: theta sum S₁ via mod-5 product (the key Step 2 result for R-R).
For `‖q‖ < 1, q ≠ 0`:
`∑'_j (-1)^j · q^(j(5j+1)/2) = ∏' (q^5;q^5)·(q^3;q^5)·(q^2;q^5) factors`. -/
theorem theta_sum_1_eq_mod5_product (q : ℂ) (hq : ‖q‖ < 1) (hq_ne : q ≠ 0) :
    (∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (5 * j + 1) / 2)) =
      (∏' n : ℕ, rrMod5Factor q 5 n) * (∏' n : ℕ, rrMod5Factor q 3 n) *
      (∏' n : ℕ, rrMod5Factor q 2 n) := by
  obtain ⟨Y, hYq⟩ := IsAlgClosed.exists_pow_nat_eq q (n := 2) (by norm_num)
  have hYne : Y ≠ 0 := by
    intro hY_zero
    apply hq_ne
    rw [← hYq, hY_zero]; ring
  have hY5_norm : ‖Y ^ 5‖ < 1 := norm_Y_pow_5_lt_one Y q hYq hq
  have hnegY_ne : (-Y : ℂ) ≠ 0 := neg_ne_zero.mpr hYne
  -- Combine: theta sum = jacobiInfiniteSeries = jacobiInfiniteProduct = mod-5 triple.
  rw [← theta_sum_1_eq_jacobiSeries q Y hYne hYq]
  rw [← Ch02.jacobiTripleProduct (Y ^ 5) (-Y) hY5_norm hnegY_ne]
  exact jacobiInfiniteProduct_S1_eq_mod5_triple q Y hYne hYq hq

/-- The infinite product of the k-th mod-5 residue factor is nonzero for `‖q‖ < 1`, `k ≥ 1`. -/
theorem tprod_rrMod5Factor_ne_zero (q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) (hk : 1 ≤ k) :
    (∏' n : ℕ, rrMod5Factor q k n) ≠ 0 := by
  have h_eq_form : (∏' n : ℕ, rrMod5Factor q k n) =
      ∏' n : ℕ, (1 + -(q ^ k * (q ^ 5) ^ n)) := by
    refine tprod_congr fun n => ?_
    simp only [rrMod5Factor]
    rw [show q ^ (k + 5 * n) = q ^ k * (q ^ 5) ^ n by rw [pow_add, pow_mul]]
    ring
  rw [h_eq_form]
  refine tprod_one_add_ne_zero_of_summable (f := fun n : ℕ => -(q ^ k * (q ^ 5) ^ n)) ?_ ?_
  · intro n
    have h_ne := rrMod5Factor_ne_zero q hq k hk n
    have h_eq : (1 + -(q ^ k * (q ^ 5) ^ n) : ℂ) = rrMod5Factor q k n := by
      simp only [rrMod5Factor]
      rw [show q ^ (k + 5 * n) = q ^ k * (q ^ 5) ^ n by rw [pow_add, pow_mul]]
      ring
    rw [h_eq]
    exact h_ne
  · have h := summable_norm_rrMod5_tail q hq k
    refine h.congr fun n => ?_
    simp [norm_neg, norm_mul]

/-- Finite identity: `(q;q)_{5N} = ∏_{n<N} (1-q^(5n+1))(1-q^(5n+2))(1-q^(5n+3))(1-q^(5n+4))(1-q^(5n+5))`. -/
private theorem mod5_product_partial_eq (q : ℂ) (N : ℕ) :
    qPochhammer q (5 * N) =
      ∏ n ∈ Finset.range N,
        ((1 - q ^ (5 * n + 1)) * (1 - q ^ (5 * n + 2)) *
         (1 - q ^ (5 * n + 3)) * (1 - q ^ (5 * n + 4)) *
         (1 - q ^ (5 * n + 5))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ, ← ih]
    have h5 : 5 * (N + 1) = 5 * N + 5 := by ring
    rw [h5]
    -- Decompose qPochhammer q (5*N + 5) = qPochhammer q (5*N) * 5 factors.
    have h_unfold :
        qPochhammer q (5 * N + 5) =
          qPochhammer q (5 * N) *
          (1 - q ^ (5 * N + 1)) * (1 - q ^ (5 * N + 2)) *
          (1 - q ^ (5 * N + 3)) * (1 - q ^ (5 * N + 4)) *
          (1 - q ^ (5 * N + 5)) := by
      have e1 : 5 * N + 1 = (5 * N) + 1 := rfl
      have e2 : 5 * N + 2 = ((5 * N) + 1) + 1 := by omega
      have e3 : 5 * N + 3 = (((5 * N) + 1) + 1) + 1 := by omega
      have e4 : 5 * N + 4 = ((((5 * N) + 1) + 1) + 1) + 1 := by omega
      have e5 : 5 * N + 5 = (((((5 * N) + 1) + 1) + 1) + 1) + 1 := by omega
      rw [e5, qPochhammer_succ, ← e4]
      rw [show (5 * N + 4 : ℕ) = ((5 * N + 3) + 1 : ℕ) from by omega, qPochhammer_succ]
      rw [show (5 * N + 3 : ℕ) = ((5 * N + 2) + 1 : ℕ) from by omega, qPochhammer_succ]
      rw [show (5 * N + 2 : ℕ) = ((5 * N + 1) + 1 : ℕ) from by omega, qPochhammer_succ]
      rw [show (5 * N + 1 : ℕ) = ((5 * N) + 1 : ℕ) from rfl, qPochhammer_succ]
    rw [h_unfold]
    ring

/-- Nat-indexed Euler product factor `1 - q^(n+1)`. -/
def eulerPentagonalProductFactor (q : ℂ) (n : ℕ) : ℂ :=
  1 - q ^ (n + 1)

/-- Euler's infinite product side, Nat-indexed from exponent `1`. -/
noncomputable def eulerPentagonalInfiniteProduct (q : ℂ) : ℂ :=
  ∏' n : ℕ, eulerPentagonalProductFactor q n

private theorem summable_norm_eulerPentagonalProduct_tail (q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-q ^ (n + 1)‖ := by
  have h := Ch02.summable_norm_mul_geometric_complex (-q) q hq
  refine h.congr fun n => ?_
  congr 1
  rw [show -q * q ^ n = -q ^ (n + 1) by
    rw [pow_succ']
    ring]

/-- The Nat-indexed Euler product is multipliable for `‖q‖ < 1`. -/
theorem multipliable_eulerPentagonalProductFactor (q : ℂ) (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ => eulerPentagonalProductFactor q n := by
  have h := multipliable_one_add_of_summable (summable_norm_eulerPentagonalProduct_tail q hq)
  simpa [eulerPentagonalProductFactor, sub_eq_add_neg] using h

/-- HasProd form of Euler's infinite product side. -/
theorem hasProd_eulerPentagonalProductFactor (q : ℂ) (hq : ‖q‖ < 1) :
    HasProd (fun n : ℕ => eulerPentagonalProductFactor q n)
      (eulerPentagonalInfiniteProduct q) :=
  (multipliable_eulerPentagonalProductFactor q hq).hasProd

/-- Finite partial products of the Nat-indexed Euler product are q-Pochhammer symbols. -/
theorem eulerPentagonalProductFactor_partial_eq_qPochhammer (q : ℂ) (N : ℕ) :
    (∏ n ∈ Finset.range N, eulerPentagonalProductFactor q n) = qPochhammer q N := by
  induction N with
  | zero =>
      simp [eulerPentagonalProductFactor]
  | succ N ih =>
      rw [Finset.prod_range_succ, ih, qPochhammer_succ]
      simp [eulerPentagonalProductFactor]

/-- The finite q-Pochhammer products tend to Euler's infinite product. -/
theorem tendsto_eulerPentagonalProductTrunc (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => qPochhammer q N) atTop
      (𝓝 (eulerPentagonalInfiniteProduct q)) := by
  have h := (multipliable_eulerPentagonalProductFactor q hq).tendsto_prod_tprod_nat
  simpa [eulerPentagonalInfiniteProduct,
    eulerPentagonalProductFactor_partial_eq_qPochhammer] using h

/-- The partial qPochhammer at `5N` converges to `(q;q)_∞`. -/
theorem tendsto_qPochhammer_5N (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => qPochhammer q (5 * N)) atTop
      (𝓝 (eulerPentagonalInfiniteProduct q)) := by
  have h_main := tendsto_eulerPentagonalProductTrunc q hq
  have h_5N : Tendsto (fun N : ℕ => 5 * N) atTop atTop := by
    refine tendsto_atTop_mono (fun N => ?_) tendsto_id
    show N ≤ 5 * N
    omega
  exact h_main.comp h_5N

/-- Tendsto for each mod-5 residue strided product. -/
theorem tendsto_rrMod5Factor_partial (q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) :
    Tendsto (fun N : ℕ => ∏ n ∈ Finset.range N, rrMod5Factor q k n) atTop
      (𝓝 (∏' n : ℕ, rrMod5Factor q k n)) :=
  (multipliable_rrMod5Factor q hq k).tendsto_prod_tprod_nat

/-- Euler's infinite product equals the mod-5 regrouped product. -/
theorem eulerPentagonalInfiniteProduct_eq_mod5_regroup (q : ℂ) (hq : ‖q‖ < 1) :
    eulerPentagonalInfiniteProduct q =
      (∏' n : ℕ, rrMod5Factor q 1 n) * (∏' n : ℕ, rrMod5Factor q 2 n) *
      (∏' n : ℕ, rrMod5Factor q 3 n) * (∏' n : ℕ, rrMod5Factor q 4 n) *
      (∏' n : ℕ, rrMod5Factor q 5 n) := by
  have hLHS_tendsto := tendsto_qPochhammer_5N q hq
  have hRHS_tendsto :
      Tendsto (fun N : ℕ =>
        (∏ n ∈ Finset.range N, rrMod5Factor q 1 n) *
        (∏ n ∈ Finset.range N, rrMod5Factor q 2 n) *
        (∏ n ∈ Finset.range N, rrMod5Factor q 3 n) *
        (∏ n ∈ Finset.range N, rrMod5Factor q 4 n) *
        (∏ n ∈ Finset.range N, rrMod5Factor q 5 n))
        atTop
        (𝓝 ((∏' n, rrMod5Factor q 1 n) * (∏' n, rrMod5Factor q 2 n) *
            (∏' n, rrMod5Factor q 3 n) * (∏' n, rrMod5Factor q 4 n) *
            (∏' n, rrMod5Factor q 5 n))) :=
    (((((multipliable_rrMod5Factor q hq 1).tendsto_prod_tprod_nat.mul
        (multipliable_rrMod5Factor q hq 2).tendsto_prod_tprod_nat).mul
        (multipliable_rrMod5Factor q hq 3).tendsto_prod_tprod_nat).mul
        (multipliable_rrMod5Factor q hq 4).tendsto_prod_tprod_nat).mul
        (multipliable_rrMod5Factor q hq 5).tendsto_prod_tprod_nat)
  -- Bridge the two Tendsto's: the partial qPochhammer equals the 5-separate prods.
  have h_partial_eq : ∀ N : ℕ,
      qPochhammer q (5 * N) =
        (∏ n ∈ Finset.range N, rrMod5Factor q 1 n) *
        (∏ n ∈ Finset.range N, rrMod5Factor q 2 n) *
        (∏ n ∈ Finset.range N, rrMod5Factor q 3 n) *
        (∏ n ∈ Finset.range N, rrMod5Factor q 4 n) *
        (∏ n ∈ Finset.range N, rrMod5Factor q 5 n) := by
    intro N
    rw [mod5_product_partial_eq q N]
    -- Now goal: ∏ n, (5-factor product) = ∏ ... rrMod5 1 · ∏ ... rrMod5 2 · ... · ∏ ... rrMod5 5
    have h_factor_eq : ∀ n : ℕ,
        (1 - q ^ (5 * n + 1)) * (1 - q ^ (5 * n + 2)) *
        (1 - q ^ (5 * n + 3)) * (1 - q ^ (5 * n + 4)) *
        (1 - q ^ (5 * n + 5)) =
        rrMod5Factor q 1 n * rrMod5Factor q 2 n *
        rrMod5Factor q 3 n * rrMod5Factor q 4 n *
        rrMod5Factor q 5 n := by
      intro n
      simp only [rrMod5Factor]
      ring
    rw [Finset.prod_congr rfl (fun n _ => h_factor_eq n)]
    simp only [Finset.prod_mul_distrib]
  have hRHS_alt :
      Tendsto (fun N : ℕ => qPochhammer q (5 * N)) atTop
        (𝓝 ((∏' n, rrMod5Factor q 1 n) * (∏' n, rrMod5Factor q 2 n) *
            (∏' n, rrMod5Factor q 3 n) * (∏' n, rrMod5Factor q 4 n) *
            (∏' n, rrMod5Factor q 5 n))) := by
    refine hRHS_tendsto.congr' ?_
    refine Filter.Eventually.of_forall fun N => ?_
    exact (h_partial_eq N).symm
  exact tendsto_nhds_unique hLHS_tendsto hRHS_alt

/-- `(q;q)_∞ ≠ 0` for `‖q‖ < 1` (via the mod-5 regrouping, each factor nonzero). -/
theorem eulerPentagonalInfiniteProduct_ne_zero (q : ℂ) (hq : ‖q‖ < 1) :
    eulerPentagonalInfiniteProduct q ≠ 0 := by
  rw [eulerPentagonalInfiniteProduct_eq_mod5_regroup q hq]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_
  · exact tprod_rrMod5Factor_ne_zero q hq 1 (by norm_num)
  · exact tprod_rrMod5Factor_ne_zero q hq 2 (by norm_num)
  · exact tprod_rrMod5Factor_ne_zero q hq 3 (by norm_num)
  · exact tprod_rrMod5Factor_ne_zero q hq 4 (by norm_num)
  · exact tprod_rrMod5Factor_ne_zero q hq 5 (by norm_num)

private theorem summable_norm_eulerPentagonalCubicProduct_tail0 (q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-q ^ (3 * (n + 1))‖ := by
  have hq3 : ‖q ^ 3‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have h := Ch02.summable_norm_mul_geometric_complex (-(q ^ 3)) (q ^ 3) hq3
  refine h.congr fun n => ?_
  congr 1
  rw [show -(q ^ 3) * (q ^ 3) ^ n = -q ^ (3 * (n + 1)) by
    rw [← pow_mul]
    rw [show 3 * (n + 1) = 3 + 3 * n by omega]
    rw [pow_add]
    ring]

private theorem summable_norm_eulerPentagonalCubicProduct_tail1 (q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-q ^ (3 * (n + 1) - 2)‖ := by
  have hq3 : ‖q ^ 3‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have h := Ch02.summable_norm_mul_geometric_complex (-q) (q ^ 3) hq3
  refine h.congr fun n => ?_
  congr 1
  rw [show -q * (q ^ 3) ^ n = -q ^ (3 * (n + 1) - 2) by
    rw [← pow_mul]
    rw [show 3 * (n + 1) - 2 = 1 + 3 * n by omega]
    rw [pow_add]
    ring]

private theorem summable_norm_eulerPentagonalCubicProduct_tail2 (q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-q ^ (3 * (n + 1) - 1)‖ := by
  have hq3 : ‖q ^ 3‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have h := Ch02.summable_norm_mul_geometric_complex (-(q ^ 2)) (q ^ 3) hq3
  refine h.congr fun n => ?_
  congr 1
  rw [show -(q ^ 2) * (q ^ 3) ^ n = -q ^ (3 * (n + 1) - 1) by
    rw [← pow_mul]
    rw [show 3 * (n + 1) - 1 = 2 + 3 * n by omega]
    rw [pow_add]
    ring]

/-- The cubic residue product factors are multipliable for `‖q‖ < 1`. -/
theorem multipliable_eulerPentagonalCubicProductFactor (q : ℂ) (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ => eulerPentagonalCubicProductFactor q n := by
  have h0 : Multipliable fun n : ℕ => 1 - q ^ (3 * (n + 1)) := by
    have h := multipliable_one_add_of_summable
      (summable_norm_eulerPentagonalCubicProduct_tail0 q hq)
    simpa [sub_eq_add_neg] using h
  have h1 : Multipliable fun n : ℕ => 1 - q ^ (3 * (n + 1) - 2) := by
    have h := multipliable_one_add_of_summable
      (summable_norm_eulerPentagonalCubicProduct_tail1 q hq)
    simpa [sub_eq_add_neg] using h
  have h2 : Multipliable fun n : ℕ => 1 - q ^ (3 * (n + 1) - 1) := by
    have h := multipliable_one_add_of_summable
      (summable_norm_eulerPentagonalCubicProduct_tail2 q hq)
    simpa [sub_eq_add_neg] using h
  exact ((h0.mul h1).mul h2).congr fun n => by
    simp [eulerPentagonalCubicProductFactor, mul_assoc]

/-- HasProd form of the cubic residue product, independent of a chosen square root. -/
theorem hasProd_eulerPentagonalCubicProductFactor (q : ℂ) (hq : ‖q‖ < 1) :
    HasProd (fun n : ℕ => eulerPentagonalCubicProductFactor q n)
      (∏' n : ℕ, eulerPentagonalCubicProductFactor q n) :=
  (multipliable_eulerPentagonalCubicProductFactor q hq).hasProd

/--
The ordinary Euler product equals the product obtained by grouping factors
according to their residues modulo `3`.
-/
theorem eulerPentagonalInfiniteProduct_eq_tprod_cubicProductFactor
    (q : ℂ) (hq : ‖q‖ < 1) :
    eulerPentagonalInfiniteProduct q =
      ∏' n : ℕ, eulerPentagonalCubicProductFactor q n := by
  have h3 : Tendsto (fun N : ℕ => 3 * N) atTop atTop := by
    exact tendsto_atTop_mono (f := fun N : ℕ => N) (g := fun N => 3 * N)
      (fun N => Nat.le_mul_of_pos_left N (by norm_num : 0 < 3)) tendsto_id
  have heuler : Tendsto (fun N : ℕ => qPochhammer q (3 * N)) atTop
      (𝓝 (eulerPentagonalInfiniteProduct q)) := by
    exact (tendsto_eulerPentagonalProductTrunc q hq).comp h3
  have hcubic : Tendsto (fun N : ℕ => qPochhammer q (3 * N)) atTop
      (𝓝 (∏' n : ℕ, eulerPentagonalCubicProductFactor q n)) := by
    have h := (multipliable_eulerPentagonalCubicProductFactor q hq).tendsto_prod_tprod_nat
    simpa [eulerPentagonalCubicProduct_partial_eq_qPochhammer] using h
  exact tendsto_nhds_unique heuler hcubic

/-- Euler pentagonal theorem after choosing `Q` with `Q^2 = q^3`. -/
theorem eulerPentagonalInfiniteProduct_eq_tsum_of_sq
    (q Q : ℂ) (hqnorm : ‖q‖ < 1) (hQnorm : ‖Q‖ < 1) (hq : q ≠ 0)
    (hQ : Q ^ 2 = q ^ 3) :
    eulerPentagonalInfiniteProduct q =
      ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (3 * j + 1) / 2) := by
  rw [eulerPentagonalInfiniteProduct_eq_tprod_cubicProductFactor q hqnorm]
  exact eulerPentagonal_cubicProduct_eq_tsum q Q hQnorm hq hQ

/-- A square root `Q` of `q^3` still lies in the open unit disc. -/
theorem exists_eulerPentagonal_substitution_sqrt
    (q : ℂ) (hqnorm : ‖q‖ < 1) :
    ∃ Q : ℂ, ‖Q‖ < 1 ∧ Q ^ 2 = q ^ 3 := by
  rcases IsAlgClosed.exists_pow_nat_eq (q ^ 3) (n := 2) (by norm_num) with ⟨Q, hQ⟩
  refine ⟨Q, ?_, hQ⟩
  have hnorm : ‖Q‖ ^ 2 = ‖q‖ ^ 3 := by
    have := congrArg norm hQ
    simpa [norm_pow] using this
  have hq3lt : ‖q‖ ^ 3 < 1 :=
    pow_lt_one₀ (norm_nonneg q) hqnorm (by norm_num)
  have hQsq_lt : ‖Q‖ ^ 2 < 1 := by
    simpa [hnorm] using hq3lt
  have hQabs : |‖Q‖| < 1 := (sq_lt_one_iff_abs_lt_one ‖Q‖).mp hQsq_lt
  simpa [abs_of_nonneg (norm_nonneg Q)] using hQabs

/-- Euler's pentagonal theorem, Chan Theorem 4.2 in infinite-product form. -/
theorem eulerPentagonalInfiniteProduct_eq_tsum
    (q : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) :
    eulerPentagonalInfiniteProduct q =
      ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (3 * j + 1) / 2) := by
  rcases exists_eulerPentagonal_substitution_sqrt q hqnorm with ⟨Q, hQnorm, hQ⟩
  exact eulerPentagonalInfiniteProduct_eq_tsum_of_sq q Q hqnorm hQnorm hq hQ

/-- Euler's pentagonal theorem (Chan 4.2), free of `q ≠ 0` hypothesis (q=0 case trivial). -/
theorem eulerPentagonalInfiniteProduct_eq_tsum' (q : ℂ) (hqnorm : ‖q‖ < 1) :
    eulerPentagonalInfiniteProduct q =
      ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (3 * j + 1) / 2) := by
  by_cases hq : q = 0
  · subst hq
    -- LHS: ∏'(1 - 0^(n+1)) = ∏' 1 = 1.
    have hL : eulerPentagonalInfiniteProduct (0 : ℂ) = 1 := by
      unfold eulerPentagonalInfiniteProduct
      rw [show (fun n : ℕ => eulerPentagonalProductFactor (0 : ℂ) n) = (fun _ : ℕ => 1) by
        funext n
        simp [eulerPentagonalProductFactor, zero_pow (Nat.succ_ne_zero n)]]
      exact tprod_one
    rw [hL]
    -- RHS: ∑' j : ℤ, (-1)^j · 0^(j*(3j+1)/2). For j ≠ 0, j(3j+1)/2 ≠ 0 hence 0^· = 0.
    rw [tsum_eq_single 0]
    · simp
    · intro j hj
      -- j ≠ 0 ⇒ j*(3j+1)/2 ≠ 0.
      have h_idx_ne : j * (3 * j + 1) / 2 ≠ 0 := by
        have h_even : (2 : Int) ∣ j * (3 * j + 1) := by
          have hsucc : (2 : Int) ∣ j * (j + 1) := int_two_dvd_mul_succ j
          have : j * (3 * j + 1) = j * (j + 1) + 2 * j * j := by ring
          rw [this]
          exact dvd_add hsucc ⟨j * j, by ring⟩
        have h_mul_ne : j * (3 * j + 1) ≠ 0 := by
          intro h_mul_zero
          have h_factor : j = 0 ∨ 3 * j + 1 = 0 := mul_eq_zero.mp h_mul_zero
          rcases h_factor with h_j | h_3j
          · exact hj h_j
          · omega
        intro h_div_zero
        have : (2 : Int) * (j * (3 * j + 1) / 2) = j * (3 * j + 1) := by
          have h_mul_eq : (j * (3 * j + 1) / 2) * 2 = j * (3 * j + 1) :=
            Int.ediv_mul_cancel h_even
          linarith
        rw [h_div_zero, mul_zero] at this
        exact h_mul_ne this.symm
      rw [zero_zpow _ h_idx_ne]
      ring
  · exact eulerPentagonalInfiniteProduct_eq_tsum q hqnorm hq

/-- Truncated product side `∏_{n=1}^{N} (1 - q^n)` (Chan Theorem 4.2 LHS). -/
def eulerPentagonalProductTrunc (q : R) (N : Nat) : R :=
  qPochhammer q N

/-- Pentagonal-number index `j ↦ j(3j+1)/2` (Int → Nat for use as exponent). -/
def pentagonalIndex (j : Int) : Nat :=
  Int.toNat (j * (3 * j + 1) / 2)

/-- Truncated bilateral sum `∑_{j=-N}^{N} (-1)^j q^{j(3j+1)/2}` (Chan Theorem 4.2 RHS). -/
noncomputable def eulerPentagonalSeriesTrunc (q : R) (N : Nat) : R :=
  bilateralSum (fun j : Int => (-1 : R) ^ j.toNat * q ^ pentagonalIndex j) N

/-- Sanity: at `N = 0` both sides equal 1. -/
theorem euler_pentagonal_truncated_zero (q : R) :
    eulerPentagonalProductTrunc q 0 = 1 ∧ eulerPentagonalSeriesTrunc q 0 = 1 := by
  constructor
  · rfl
  · simp [eulerPentagonalSeriesTrunc, pentagonalIndex]

/-- The first nontrivial Euler product truncation is `1 - q`. -/
theorem eulerPentagonalProductTrunc_one (q : R) :
    eulerPentagonalProductTrunc q 1 = 1 - q := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

/-- At `N = 1`, the truncated Euler pentagonal series has terms `j = 0, 1, -1`. -/
theorem eulerPentagonalSeriesTrunc_one (q : R) :
    eulerPentagonalSeriesTrunc q 1 = 1 + q - q ^ 2 := by
  have hneg : (-1 : Int).toNat = 0 := by norm_num
  have htwo : Int.toNat 2 = 2 := rfl
  norm_num [eulerPentagonalSeriesTrunc, bilateralSum, pentagonalIndex]
  rw [hneg, htwo]
  ring

/-- The second Euler product truncation is `(1 - q)(1 - q^2)`. -/
theorem eulerPentagonalProductTrunc_two (q : R) :
    eulerPentagonalProductTrunc q 2 = (1 - q) * (1 - q ^ 2) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

/-- The third Euler product truncation is `(1 - q)(1 - q^2)(1 - q^3)`. -/
theorem eulerPentagonalProductTrunc_three (q : R) :
    eulerPentagonalProductTrunc q 3 = (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_four (q : R) :
    eulerPentagonalProductTrunc q 4 = (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_five (q : R) :
    eulerPentagonalProductTrunc q 5 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_six (q : R) :
    eulerPentagonalProductTrunc q 6 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_seven (q : R) :
    eulerPentagonalProductTrunc q 7 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_eight (q : R) :
    eulerPentagonalProductTrunc q 8 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_nine (q : R) :
    eulerPentagonalProductTrunc q 9 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_ten (q : R) :
    eulerPentagonalProductTrunc q 10 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_eleven (q : R) :
    eulerPentagonalProductTrunc q 11 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_twelve (q : R) :
    eulerPentagonalProductTrunc q 12 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_thirteen (q : R) :
    eulerPentagonalProductTrunc q 13 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_fourteen (q : R) :
    eulerPentagonalProductTrunc q 14 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_fifteen (q : R) :
    eulerPentagonalProductTrunc q 15 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_sixteen (q : R) :
    eulerPentagonalProductTrunc q 16 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_seventeen (q : R) :
    eulerPentagonalProductTrunc q 17 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_eighteen (q : R) :
    eulerPentagonalProductTrunc q 18 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_nineteen (q : R) :
    eulerPentagonalProductTrunc q 19 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_twenty (q : R) :
    eulerPentagonalProductTrunc q 20 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_twentyone (q : R) :
    eulerPentagonalProductTrunc q 21 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_twentytwo (q : R) :
    eulerPentagonalProductTrunc q 22 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_twentythree (q : R) :
    eulerPentagonalProductTrunc q 23 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_twentyfour (q : R) :
    eulerPentagonalProductTrunc q 24 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) * (1 - q ^ 24) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_twentyfive (q : R) :
    eulerPentagonalProductTrunc q 25 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) * (1 - q ^ 24) * (1 - q ^ 25) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_twentysix (q : R) :
    eulerPentagonalProductTrunc q 26 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) * (1 - q ^ 24) * (1 - q ^ 25) *
      (1 - q ^ 26) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_twentyseven (q : R) :
    eulerPentagonalProductTrunc q 27 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) * (1 - q ^ 24) * (1 - q ^ 25) *
      (1 - q ^ 26) * (1 - q ^ 27) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_twentyeight (q : R) :
    eulerPentagonalProductTrunc q 28 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) * (1 - q ^ 24) * (1 - q ^ 25) *
      (1 - q ^ 26) * (1 - q ^ 27) * (1 - q ^ 28) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_twentynine (q : R) :
    eulerPentagonalProductTrunc q 29 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) * (1 - q ^ 24) * (1 - q ^ 25) *
      (1 - q ^ 26) * (1 - q ^ 27) * (1 - q ^ 28) * (1 - q ^ 29) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_thirty (q : R) :
    eulerPentagonalProductTrunc q 30 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) * (1 - q ^ 24) * (1 - q ^ 25) *
      (1 - q ^ 26) * (1 - q ^ 27) * (1 - q ^ 28) * (1 - q ^ 29) * (1 - q ^ 30) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_thirtyone (q : R) :
    eulerPentagonalProductTrunc q 31 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) * (1 - q ^ 24) * (1 - q ^ 25) *
      (1 - q ^ 26) * (1 - q ^ 27) * (1 - q ^ 28) * (1 - q ^ 29) * (1 - q ^ 30) *
      (1 - q ^ 31) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_thirtytwo (q : R) :
    eulerPentagonalProductTrunc q 32 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) * (1 - q ^ 24) * (1 - q ^ 25) *
      (1 - q ^ 26) * (1 - q ^ 27) * (1 - q ^ 28) * (1 - q ^ 29) * (1 - q ^ 30) *
      (1 - q ^ 31) * (1 - q ^ 32) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_thirtythree (q : R) :
    eulerPentagonalProductTrunc q 33 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) * (1 - q ^ 24) * (1 - q ^ 25) *
      (1 - q ^ 26) * (1 - q ^ 27) * (1 - q ^ 28) * (1 - q ^ 29) * (1 - q ^ 30) *
      (1 - q ^ 31) * (1 - q ^ 32) * (1 - q ^ 33) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_thirtyfour (q : R) :
    eulerPentagonalProductTrunc q 34 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) * (1 - q ^ 24) * (1 - q ^ 25) *
      (1 - q ^ 26) * (1 - q ^ 27) * (1 - q ^ 28) * (1 - q ^ 29) * (1 - q ^ 30) *
      (1 - q ^ 31) * (1 - q ^ 32) * (1 - q ^ 33) * (1 - q ^ 34) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_thirtyfive (q : R) :
    eulerPentagonalProductTrunc q 35 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) * (1 - q ^ 24) * (1 - q ^ 25) *
      (1 - q ^ 26) * (1 - q ^ 27) * (1 - q ^ 28) * (1 - q ^ 29) * (1 - q ^ 30) *
      (1 - q ^ 31) * (1 - q ^ 32) * (1 - q ^ 33) * (1 - q ^ 34) * (1 - q ^ 35) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_thirtysix (q : R) :
    eulerPentagonalProductTrunc q 36 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) * (1 - q ^ 24) * (1 - q ^ 25) *
      (1 - q ^ 26) * (1 - q ^ 27) * (1 - q ^ 28) * (1 - q ^ 29) * (1 - q ^ 30) *
      (1 - q ^ 31) * (1 - q ^ 32) * (1 - q ^ 33) * (1 - q ^ 34) * (1 - q ^ 35) *
      (1 - q ^ 36) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_thirtyseven (q : R) :
    eulerPentagonalProductTrunc q 37 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) * (1 - q ^ 24) * (1 - q ^ 25) *
      (1 - q ^ 26) * (1 - q ^ 27) * (1 - q ^ 28) * (1 - q ^ 29) * (1 - q ^ 30) *
      (1 - q ^ 31) * (1 - q ^ 32) * (1 - q ^ 33) * (1 - q ^ 34) * (1 - q ^ 35) *
      (1 - q ^ 36) * (1 - q ^ 37) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_thirtyeight (q : R) :
    eulerPentagonalProductTrunc q 38 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) * (1 - q ^ 24) * (1 - q ^ 25) *
      (1 - q ^ 26) * (1 - q ^ 27) * (1 - q ^ 28) * (1 - q ^ 29) * (1 - q ^ 30) *
      (1 - q ^ 31) * (1 - q ^ 32) * (1 - q ^ 33) * (1 - q ^ 34) * (1 - q ^ 35) *
      (1 - q ^ 36) * (1 - q ^ 37) * (1 - q ^ 38) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_thirtynine (q : R) :
    eulerPentagonalProductTrunc q 39 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) * (1 - q ^ 24) * (1 - q ^ 25) *
      (1 - q ^ 26) * (1 - q ^ 27) * (1 - q ^ 28) * (1 - q ^ 29) * (1 - q ^ 30) *
      (1 - q ^ 31) * (1 - q ^ 32) * (1 - q ^ 33) * (1 - q ^ 34) * (1 - q ^ 35) *
      (1 - q ^ 36) * (1 - q ^ 37) * (1 - q ^ 38) * (1 - q ^ 39) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]

theorem eulerPentagonalProductTrunc_forty (q : R) :
    eulerPentagonalProductTrunc q 40 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) * (1 - q ^ 24) * (1 - q ^ 25) *
      (1 - q ^ 26) * (1 - q ^ 27) * (1 - q ^ 28) * (1 - q ^ 29) * (1 - q ^ 30) *
      (1 - q ^ 31) * (1 - q ^ 32) * (1 - q ^ 33) * (1 - q ^ 34) * (1 - q ^ 35) *
      (1 - q ^ 36) * (1 - q ^ 37) * (1 - q ^ 38) * (1 - q ^ 39) * (1 - q ^ 40) := by
  simp [eulerPentagonalProductTrunc, qPochhammer]


/--
At `N = 2`, Lean's truncated Euler pentagonal series uses
`(-1 : R) ^ j.toNat`, so the negative-index terms have positive sign.
-/
theorem eulerPentagonalSeriesTrunc_two (q : R) :
    eulerPentagonalSeriesTrunc q 2 = 1 + q - q ^ 2 + q ^ 5 + q ^ 7 := by
  have hneg_one : (-1 : Int).toNat = 0 := by norm_num
  have hneg_two : (-2 : Int).toNat = 0 := by norm_num
  have htwo : Int.toNat 2 = 2 := rfl
  have hfive : Int.toNat 5 = 5 := rfl
  have hseven : Int.toNat 7 = 7 := rfl
  norm_num [eulerPentagonalSeriesTrunc, bilateralSum, pentagonalIndex]
  rw [hneg_one, hneg_two, htwo, hfive, hseven]
  ring

/-- The truncated Euler pentagonal identity does NOT hold at N=1. -/
theorem eulerPentagonal_N1_difference (q : R) :
    eulerPentagonalSeriesTrunc q 1 - eulerPentagonalProductTrunc q 1 =
      2 * q - q ^ 2 := by
  rw [eulerPentagonalProductTrunc_one, eulerPentagonalSeriesTrunc_one]
  ring

/- The infinite Euler pentagonal theorem is proved above as
`eulerPentagonalInfiniteProduct_eq_tsum`. -/

/-- Theorem 4.3 LHS truncated: `(q; q)_N^3`. -/
noncomputable def theorem43LHSTrunc (q : R) (N : Nat) : R :=
  eulerPentagonalProductTrunc q N ^ 3

/-- Theorem 4.3 RHS truncated: `∑_{n=0}^{N} (-1)^n (2n+1) q^{n(n+1)/2}`. -/
noncomputable def theorem43RHSTrunc (q : R) (N : Nat) : R :=
  natSum (fun n : Nat => (-1 : R) ^ n * (2 * n + 1 : R) * q ^ triangular n) N

/-- Sanity: at `N = 0` both sides equal 1. -/
theorem theorem43_truncated_zero (q : R) :
    theorem43LHSTrunc q 0 = 1 ∧ theorem43RHSTrunc q 0 = 1 := by
  constructor
  · simp [theorem43LHSTrunc, eulerPentagonalProductTrunc]
  · simp [theorem43RHSTrunc, triangular]

/- The infinite Theorem 4.3 identity is deferred until its JTP specialization
and rewriting layer is formalized. -/

/-- Integer powers, interpreted in the ambient field. -/
noncomputable def intPow (x : R) (k : Int) : R :=
  if 0 ≤ k then x ^ k.toNat else (Inv.inv x) ^ (-k).toNat

/-- Exponent `3n^2 + n` in the Eq. (2.12) form of the quintuple product identity. -/
def quintupleQuadraticIndex (n : Int) : Nat :=
  Int.toNat (3 * n * n + n)

/--
Quintuple product LHS truncated in Chan's Eq. (2.12) form, with factors
for `n = 0, ..., N - 1`.
-/
noncomputable def quintupleProductLHSTrunc (q z : R) : Nat → R
  | 0 => 1
  | Nat.succ n =>
      quintupleProductLHSTrunc q z n *
        (1 - q ^ (2 * n + 2)) *
        (1 - z * q ^ (2 * n + 1)) *
        (1 - (Inv.inv z) * q ^ (2 * n + 1)) *
        (1 - z ^ 2 * q ^ (4 * n)) *
        (1 - (Inv.inv z) ^ 2 * q ^ (4 * n + 4))

/-- Nat-indexed quintuple product factor in Chan's Eq. (2.12) form. -/
noncomputable def quintupleProductFactor (q z : ℂ) (n : ℕ) : ℂ :=
  (1 - q ^ (2 * n + 2)) *
    (1 - z * q ^ (2 * n + 1)) *
    (1 - z⁻¹ * q ^ (2 * n + 1)) *
    (1 - z ^ 2 * q ^ (4 * n)) *
    (1 - z⁻¹ ^ 2 * q ^ (4 * n + 4))

/-- Infinite product side of the quintuple product identity. -/
noncomputable def quintupleProductLHS (q z : ℂ) : ℂ :=
  ∏' n : ℕ, quintupleProductFactor q z n

/-- Finite products of the Nat-indexed quintuple factors match the recursive truncation. -/
theorem quintupleProductFactor_partial_eq_trunc (q z : ℂ) (N : ℕ) :
    (∏ n ∈ Finset.range N, quintupleProductFactor q z n) =
      quintupleProductLHSTrunc q z N := by
  induction N with
  | zero =>
      simp [quintupleProductFactor, quintupleProductLHSTrunc]
  | succ N ih =>
      rw [Finset.prod_range_succ, ih]
      simp [quintupleProductFactor, quintupleProductLHSTrunc]
      ring

private theorem summable_norm_quintupleProduct_tail0 (q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-q ^ (2 * n + 2)‖ := by
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have h := Ch02.summable_norm_mul_geometric_complex (-(q ^ 2)) (q ^ 2) hq2
  refine h.congr fun n => ?_
  congr 1
  rw [show -(q ^ 2) * (q ^ 2) ^ n = -q ^ (2 * n + 2) by
    rw [← pow_mul]
    rw [show 2 * n + 2 = 2 + 2 * n by omega]
    rw [pow_add]
    ring]

private theorem summable_norm_quintupleProduct_tail1 (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-(z * q ^ (2 * n + 1))‖ := by
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have h := Ch02.summable_norm_mul_geometric_complex (-(z * q)) (q ^ 2) hq2
  refine h.congr fun n => ?_
  congr 1
  rw [show -(z * q) * (q ^ 2) ^ n = -(z * q ^ (2 * n + 1)) by
    rw [← pow_mul]
    rw [show 2 * n + 1 = 1 + 2 * n by omega]
    rw [pow_add]
    ring]

private theorem summable_norm_quintupleProduct_tail2 (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-(z⁻¹ * q ^ (2 * n + 1))‖ := by
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have h := Ch02.summable_norm_mul_geometric_complex (-(z⁻¹ * q)) (q ^ 2) hq2
  refine h.congr fun n => ?_
  congr 1
  rw [show -(z⁻¹ * q) * (q ^ 2) ^ n = -(z⁻¹ * q ^ (2 * n + 1)) by
    rw [← pow_mul]
    rw [show 2 * n + 1 = 1 + 2 * n by omega]
    rw [pow_add]
    ring]

private theorem summable_norm_quintupleProduct_tail3 (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-(z ^ 2 * q ^ (4 * n))‖ := by
  have hq4 : ‖q ^ 4‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have h := Ch02.summable_norm_mul_geometric_complex (-(z ^ 2)) (q ^ 4) hq4
  refine h.congr fun n => ?_
  congr 1
  rw [show -(z ^ 2) * (q ^ 4) ^ n = -(z ^ 2 * q ^ (4 * n)) by
    rw [← pow_mul]
    ring]

private theorem summable_norm_quintupleProduct_tail4 (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-(z⁻¹ ^ 2 * q ^ (4 * n + 4))‖ := by
  have hq4 : ‖q ^ 4‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have h := Ch02.summable_norm_mul_geometric_complex (-(z⁻¹ ^ 2 * q ^ 4)) (q ^ 4) hq4
  refine h.congr fun n => ?_
  congr 1
  rw [show -(z⁻¹ ^ 2 * q ^ 4) * (q ^ 4) ^ n =
      -(z⁻¹ ^ 2 * q ^ (4 * n + 4)) by
    rw [← pow_mul]
    rw [show 4 * n + 4 = 4 + 4 * n by omega]
    rw [pow_add]
    ring]

/-- The quintuple product side is multipliable for `‖q‖ < 1`. -/
theorem multipliable_quintupleProductFactor (q z : ℂ) (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ => quintupleProductFactor q z n := by
  have h0 : Multipliable fun n : ℕ => 1 - q ^ (2 * n + 2) := by
    have h := multipliable_one_add_of_summable (summable_norm_quintupleProduct_tail0 q hq)
    simpa [sub_eq_add_neg] using h
  have h1 : Multipliable fun n : ℕ => 1 - z * q ^ (2 * n + 1) := by
    have h := multipliable_one_add_of_summable (summable_norm_quintupleProduct_tail1 q z hq)
    simpa [sub_eq_add_neg] using h
  have h2 : Multipliable fun n : ℕ => 1 - z⁻¹ * q ^ (2 * n + 1) := by
    have h := multipliable_one_add_of_summable (summable_norm_quintupleProduct_tail2 q z hq)
    simpa [sub_eq_add_neg] using h
  have h3 : Multipliable fun n : ℕ => 1 - z ^ 2 * q ^ (4 * n) := by
    have h := multipliable_one_add_of_summable (summable_norm_quintupleProduct_tail3 q z hq)
    simpa [sub_eq_add_neg] using h
  have h4 : Multipliable fun n : ℕ => 1 - z⁻¹ ^ 2 * q ^ (4 * n + 4) := by
    have h := multipliable_one_add_of_summable (summable_norm_quintupleProduct_tail4 q z hq)
    simpa [sub_eq_add_neg] using h
  exact ((((h0.mul h1).mul h2).mul h3).mul h4).congr fun n => by
    simp [quintupleProductFactor, mul_assoc]

/-- HasProd form of the quintuple product side. -/
theorem hasProd_quintupleProductFactor (q z : ℂ) (hq : ‖q‖ < 1) :
    HasProd (fun n : ℕ => quintupleProductFactor q z n) (quintupleProductLHS q z) :=
  (multipliable_quintupleProductFactor q z hq).hasProd

/-- The recursive quintuple product truncations tend to the infinite product side. -/
theorem tendsto_quintupleProductLHSTrunc (q z : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => quintupleProductLHSTrunc q z N) atTop
      (𝓝 (quintupleProductLHS q z)) := by
  have h := (multipliable_quintupleProductFactor q z hq).tendsto_prod_tprod_nat
  simpa [quintupleProductLHS, quintupleProductFactor_partial_eq_trunc] using h

/--
Nat-indexed factor for Chan Theorem 4.4, written with zero-based index:
`(1 - q^(n+1))(1 - z q^(n+1))(1 - z⁻¹ q^n)
 (1 - z^2 q^(2n+1))(1 - z⁻¹^2 q^(2n+1))`.
-/
noncomputable def theorem44ProductFactor (q z : ℂ) (n : ℕ) : ℂ :=
  (1 - q ^ (n + 1)) *
    (1 - z * q ^ (n + 1)) *
    (1 - z⁻¹ * q ^ n) *
    (1 - z ^ 2 * q ^ (2 * n + 1)) *
    (1 - z⁻¹ ^ 2 * q ^ (2 * n + 1))

/-- Product side of Chan Theorem 4.4. -/
noncomputable def theorem44ProductLHS (q z : ℂ) : ℂ :=
  ∏' n : ℕ, theorem44ProductFactor q z n

/-- Zero-based finite partial product for Chan Theorem 4.4's product side. -/
noncomputable def theorem44ProductPartial (q z : ℂ) (N : ℕ) : ℂ :=
  ∏ n ∈ Finset.range N, theorem44ProductFactor q z n

/-- The finite Theorem 4.4 product partial as five finite q-Pochhammer factors. -/
theorem theorem44ProductPartial_eq_qPoch (q z : ℂ) (N : ℕ) :
    theorem44ProductPartial q z N =
      qPoch q q N * qPoch (z * q) q N * qPoch z⁻¹ q N *
        qPoch (z ^ 2 * q) (q ^ 2) N * qPoch (z⁻¹ ^ 2 * q) (q ^ 2) N := by
  induction N with
  | zero =>
      simp [theorem44ProductPartial]
  | succ N ih =>
      rw [theorem44ProductPartial, Finset.prod_range_succ]
      change theorem44ProductPartial q z N * theorem44ProductFactor q z N =
        qPoch q q (N + 1) * qPoch (z * q) q (N + 1) * qPoch z⁻¹ q (N + 1) *
          qPoch (z ^ 2 * q) (q ^ 2) (N + 1) * qPoch (z⁻¹ ^ 2 * q) (q ^ 2) (N + 1)
      rw [ih]
      have h1 : z * q * q ^ N = z * q ^ (N + 1) := by
        rw [pow_succ]
        ring
      have h3 : z ^ 2 * q * (q ^ 2) ^ N = z ^ 2 * q ^ (2 * N + 1) := by
        rw [← pow_mul]
        rw [show 2 * N + 1 = 1 + 2 * N by omega]
        rw [pow_add]
        ring
      simp [qPoch_succ, theorem44ProductFactor, h1, h3]
      ring

/-- The `z`-exponent appearing when the two Theorem 4.4 Jacobi sums are multiplied. -/
def theorem44DoubleSumZIndex (m n : Int) : Int :=
  2 * n - m

/-- The `(-1)`-exponent appearing when the two Theorem 4.4 Jacobi sums are multiplied. -/
def theorem44DoubleSumSignIndex (m n : Int) : Int :=
  m + n

/--
Six times the `q`-exponent in the product of the two Theorem 4.4 Jacobi
summands. This avoids integer-division bookkeeping in the regrouping layer.
-/
def theorem44DoubleSumSixExponent (m n : Int) : Int :=
  3 * m * (m - 1) + 6 * n ^ 2

/-- Six times the coefficient-side `q`-exponent in Chan Eq. (4.21). -/
def theorem44CoeffSixExponent (k l : Int) : Int :=
  k * (k + 1) + 2 * l * (l - 1)

/-- The coefficient-side sixfold exponent is always nonnegative. -/
theorem theorem44CoeffSixExponent_nonneg (k l : Int) :
    0 ≤ theorem44CoeffSixExponent k l := by
  have hk : 0 ≤ k * (k + 1) := by
    by_cases h : 0 ≤ k
    · exact mul_nonneg h (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  have hl : 0 ≤ l * (l - 1) := by
    by_cases h : 1 ≤ l
    · exact mul_nonneg (by omega) (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  unfold theorem44CoeffSixExponent
  nlinarith

/-- The coefficient-side sixfold exponent is always even. -/
theorem two_dvd_theorem44CoeffSixExponent (k l : Int) :
    (2 : Int) ∣ theorem44CoeffSixExponent k l := by
  rcases int_two_dvd_mul_succ k with ⟨a, ha⟩
  refine ⟨a + l * (l - 1), ?_⟩
  unfold theorem44CoeffSixExponent
  rw [ha]
  ring

/--
Under Chan's residue condition `3 ∣ l+k`, the coefficient-side sixfold
exponent is divisible by `6`, so it represents an honest integer exponent.
-/
theorem six_dvd_theorem44CoeffSixExponent_of_residue
    (k l : Int) (h : (3 : Int) ∣ l + k) :
    (6 : Int) ∣ theorem44CoeffSixExponent k l := by
  rcases h with ⟨a, ha⟩
  have hl : l = 3 * a - k := by omega
  rcases int_two_dvd_mul_succ k with ⟨b, hb⟩
  refine ⟨b + 3 * a ^ 2 - 2 * a * k - a, ?_⟩
  calc
    theorem44CoeffSixExponent k l =
        3 * (k * (k + 1)) + 18 * a ^ 2 - 12 * a * k - 6 * a := by
      unfold theorem44CoeffSixExponent
      rw [hl]
      ring
    _ = 6 * (b + 3 * a ^ 2 - 2 * a * k - a) := by
      rw [hb]
      ring

/-- Actual natural-number `q`-exponent attached to Chan's coefficient term. -/
def theorem44CoeffExponentIndex (k l : Int) : Nat :=
  Int.toNat (theorem44CoeffSixExponent k l / 6)

/-- The natural coefficient exponent recovers the sixfold exponent under the residue condition. -/
theorem theorem44CoeffExponentIndex_spec
    (k l : Int) (h : (3 : Int) ∣ l + k) :
    6 * ((theorem44CoeffExponentIndex k l : Nat) : Int) =
      theorem44CoeffSixExponent k l := by
  have hnonneg : 0 ≤ theorem44CoeffSixExponent k l :=
    theorem44CoeffSixExponent_nonneg k l
  have hdiv : (6 : Int) ∣ theorem44CoeffSixExponent k l :=
    six_dvd_theorem44CoeffSixExponent_of_residue k l h
  have hquot_nonneg : 0 ≤ theorem44CoeffSixExponent k l / 6 :=
    Int.ediv_nonneg hnonneg (by norm_num)
  unfold theorem44CoeffExponentIndex
  rw [Int.toNat_of_nonneg hquot_nonneg]
  rw [show 6 * (theorem44CoeffSixExponent k l / 6) =
      (theorem44CoeffSixExponent k l / 6) * 6 by ring]
  exact Int.ediv_mul_cancel hdiv

/-- Substituting `m = 2n - k` makes the product term contribute to `z^k`. -/
theorem theorem44DoubleSumZIndex_reindex (k n : Int) :
    theorem44DoubleSumZIndex (2 * n - k) n = k := by
  unfold theorem44DoubleSumZIndex
  ring

/-- Under `m = 2n-k`, the sign exponent is `l = 3n-k`. -/
theorem theorem44DoubleSumSignIndex_reindex (k n : Int) :
    theorem44DoubleSumSignIndex (2 * n - k) n = 3 * n - k := by
  unfold theorem44DoubleSumSignIndex
  ring

/-- The sixfold `q`-exponents match under Chan's reindexing `m = 2n-k`, `l = 3n-k`. -/
theorem theorem44DoubleSumSixExponent_reindex (k n : Int) :
    theorem44DoubleSumSixExponent (2 * n - k) n =
      theorem44CoeffSixExponent k (3 * n - k) := by
  unfold theorem44DoubleSumSixExponent theorem44CoeffSixExponent
  ring

/-- The reindexed coefficient variable `l = 3n-k` satisfies Chan's residue constraint. -/
theorem theorem44CoeffResidueCondition_reindex (k n : Int) :
    (3 : Int) ∣ (3 * n - k) + k := by
  use n
  ring

/-- The `z`-powers combine to `z^k` under Chan's reindexing. -/
theorem theorem44_zpow_reindex (z : ℂ) (hz : z ≠ 0) (k n : Int) :
    z ^ (-(2 * n - k)) * z ^ (2 * n) = z ^ k := by
  rw [← zpow_add₀ hz]
  congr 1
  ring

/-- The signs combine to the coefficient-side sign under Chan's reindexing. -/
theorem theorem44_sign_reindex (k n : Int) :
    (-1 : ℂ) ^ (2 * n - k) * (-1 : ℂ) ^ n = (-1 : ℂ) ^ (3 * n - k) := by
  rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  congr 1
  ring

/-- Coefficient sixfold exponent in the `k = 3r`, `l = 3j` residue class. -/
theorem theorem44CoeffSixExponent_residue_zero (r j : Int) :
    theorem44CoeffSixExponent (3 * r) (3 * j) =
      3 * r * (3 * r + 1) + 6 * j * (3 * j - 1) := by
  unfold theorem44CoeffSixExponent
  ring

/-- Coefficient sixfold exponent in the `k = -3r-1`, `l = 3j+1` residue class. -/
theorem theorem44CoeffSixExponent_residue_one (r j : Int) :
    theorem44CoeffSixExponent (-(3 * r) - 1) (3 * j + 1) =
      3 * r * (3 * r + 1) + 6 * j * (3 * j + 1) := by
  unfold theorem44CoeffSixExponent
  ring

/-- Coefficient sixfold exponent in the `k = 3r-2`, `l = 3j+2` residue class. -/
theorem theorem44CoeffSixExponent_residue_two (r j : Int) :
    theorem44CoeffSixExponent (3 * r - 2) (3 * j + 2) =
      (3 * r - 2) * (3 * r - 1) + 2 * (3 * j + 2) * (3 * j + 1) := by
  unfold theorem44CoeffSixExponent
  ring

/-- The `k = 3r`, `l = 3j` class satisfies the coefficient residue constraint. -/
theorem theorem44CoeffResidueCondition_zero (r j : Int) :
    (3 : Int) ∣ (3 * j) + (3 * r) := by
  use j + r
  ring

/-- The `k = -3r-1`, `l = 3j+1` class satisfies the coefficient residue constraint. -/
theorem theorem44CoeffResidueCondition_one (r j : Int) :
    (3 : Int) ∣ (3 * j + 1) + (-(3 * r) - 1) := by
  use j - r
  ring

/-- The `k = 3r-2`, `l = 3j+2` class satisfies the coefficient residue constraint. -/
theorem theorem44CoeffResidueCondition_two (r j : Int) :
    (3 : Int) ∣ (3 * j + 2) + (3 * r - 2) := by
  use j + r
  ring

/-- For `k = 3r`, Chan's residue constraint forces `l = 3j`. -/
theorem theorem44CoeffResidueCondition_zero_iff (r l : Int) :
    ((3 : Int) ∣ l + 3 * r) ↔ ∃ j : Int, l = 3 * j := by
  constructor
  · intro h
    rcases h with ⟨a, ha⟩
    refine ⟨a - r, ?_⟩
    omega
  · rintro ⟨j, rfl⟩
    use j + r
    ring

/-- For `k = -3r-1`, Chan's residue constraint forces `l = 3j+1`. -/
theorem theorem44CoeffResidueCondition_one_iff (r l : Int) :
    ((3 : Int) ∣ l + (-(3 * r) - 1)) ↔ ∃ j : Int, l = 3 * j + 1 := by
  constructor
  · intro h
    rcases h with ⟨a, ha⟩
    refine ⟨a + r, ?_⟩
    omega
  · rintro ⟨j, rfl⟩
    use j - r
    ring

/-- For `k = 3r-2`, Chan's residue constraint forces `l = 3j+2`. -/
theorem theorem44CoeffResidueCondition_two_iff (r l : Int) :
    ((3 : Int) ∣ l + (3 * r - 2)) ↔ ∃ j : Int, l = 3 * j + 2 := by
  constructor
  · intro h
    rcases h with ⟨a, ha⟩
    refine ⟨a - r, ?_⟩
    omega
  · rintro ⟨j, rfl⟩
    use j + r
    ring

/-- Natural coefficient exponent in the `k = 3r`, `l = 3j` residue class. -/
theorem theorem44CoeffExponentIndex_residue_zero_spec (r j : Int) :
    6 * ((theorem44CoeffExponentIndex (3 * r) (3 * j) : Nat) : Int) =
      3 * r * (3 * r + 1) + 6 * j * (3 * j - 1) := by
  rw [theorem44CoeffExponentIndex_spec (3 * r) (3 * j)
    (theorem44CoeffResidueCondition_zero r j)]
  exact theorem44CoeffSixExponent_residue_zero r j

/-- Natural coefficient exponent in the `k = -3r-1`, `l = 3j+1` residue class. -/
theorem theorem44CoeffExponentIndex_residue_one_spec (r j : Int) :
    6 * ((theorem44CoeffExponentIndex (-(3 * r) - 1) (3 * j + 1) : Nat) : Int) =
      3 * r * (3 * r + 1) + 6 * j * (3 * j + 1) := by
  rw [theorem44CoeffExponentIndex_spec (-(3 * r) - 1) (3 * j + 1)
    (theorem44CoeffResidueCondition_one r j)]
  exact theorem44CoeffSixExponent_residue_one r j

/-- Natural coefficient exponent in the `k = 3r-2`, `l = 3j+2` residue class. -/
theorem theorem44CoeffExponentIndex_residue_two_spec (r j : Int) :
    6 * ((theorem44CoeffExponentIndex (3 * r - 2) (3 * j + 2) : Nat) : Int) =
      (3 * r - 2) * (3 * r - 1) + 2 * (3 * j + 2) * (3 * j + 1) := by
  rw [theorem44CoeffExponentIndex_spec (3 * r - 2) (3 * j + 2)
    (theorem44CoeffResidueCondition_two r j)]
  exact theorem44CoeffSixExponent_residue_two r j

private theorem int_two_dvd_mul_three_add_one (r : Int) :
    (2 : Int) ∣ r * (3 * r + 1) := by
  rcases int_two_dvd_mul_succ r with ⟨a, ha⟩
  refine ⟨a + r ^ 2, ?_⟩
  calc
    r * (3 * r + 1) = r * (r + 1) + 2 * r ^ 2 := by ring
    _ = 2 * a + 2 * r ^ 2 := by rw [show r * (r + 1) = 2 * a by simpa [mul_comm] using ha]
    _ = 2 * (a + r ^ 2) := by ring

/-- The `k = 3r`, `l = 3j` natural exponent in Chan's divided form. -/
theorem theorem44CoeffExponentIndex_residue_zero_eq (r j : Int) :
    ((theorem44CoeffExponentIndex (3 * r) (3 * j) : Nat) : Int) =
      r * (3 * r + 1) / 2 + j * (3 * j - 1) := by
  apply (mul_right_injective₀ (show (6 : Int) ≠ 0 by norm_num))
  have hr : (2 : Int) ∣ r * (3 * r + 1) :=
    int_two_dvd_mul_three_add_one r
  have hhalf : 6 * (r * (3 * r + 1) / 2) = 3 * (r * (3 * r + 1)) := by
    rw [show 6 * (r * (3 * r + 1) / 2) =
        3 * ((r * (3 * r + 1) / 2) * 2) by ring]
    rw [Int.ediv_mul_cancel hr]
  calc
    6 * ((theorem44CoeffExponentIndex (3 * r) (3 * j) : Nat) : Int) =
        3 * r * (3 * r + 1) + 6 * j * (3 * j - 1) :=
          theorem44CoeffExponentIndex_residue_zero_spec r j
    _ = 6 * (r * (3 * r + 1) / 2 + j * (3 * j - 1)) := by
      rw [show 6 * (r * (3 * r + 1) / 2 + j * (3 * j - 1)) =
          6 * (r * (3 * r + 1) / 2) + 6 * (j * (3 * j - 1)) by ring]
      rw [hhalf]
      ring

/-- The `k = -3r-1`, `l = 3j+1` natural exponent in Chan's divided form. -/
theorem theorem44CoeffExponentIndex_residue_one_eq (r j : Int) :
    ((theorem44CoeffExponentIndex (-(3 * r) - 1) (3 * j + 1) : Nat) : Int) =
      r * (3 * r + 1) / 2 + j * (3 * j + 1) := by
  apply (mul_right_injective₀ (show (6 : Int) ≠ 0 by norm_num))
  have hr : (2 : Int) ∣ r * (3 * r + 1) :=
    int_two_dvd_mul_three_add_one r
  have hhalf : 6 * (r * (3 * r + 1) / 2) = 3 * (r * (3 * r + 1)) := by
    rw [show 6 * (r * (3 * r + 1) / 2) =
        3 * ((r * (3 * r + 1) / 2) * 2) by ring]
    rw [Int.ediv_mul_cancel hr]
  calc
    6 * ((theorem44CoeffExponentIndex (-(3 * r) - 1) (3 * j + 1) : Nat) : Int) =
        3 * r * (3 * r + 1) + 6 * j * (3 * j + 1) :=
          theorem44CoeffExponentIndex_residue_one_spec r j
    _ = 6 * (r * (3 * r + 1) / 2 + j * (3 * j + 1)) := by
      rw [show 6 * (r * (3 * r + 1) / 2 + j * (3 * j + 1)) =
          6 * (r * (3 * r + 1) / 2) + 6 * (j * (3 * j + 1)) by ring]
      rw [hhalf]
      ring

private theorem theorem44_three_mul_add_one_half_nonneg (r : Int) :
    0 ≤ r * (3 * r + 1) / 2 := by
  have hnum : 0 ≤ r * (3 * r + 1) := by
    by_cases h : 0 ≤ r
    · exact mul_nonneg h (by omega)
    · have hr : r ≤ 0 := by omega
      have hlin : 3 * r + 1 ≤ 0 := by omega
      exact mul_nonneg_of_nonpos_of_nonpos hr hlin
  exact Int.ediv_nonneg hnum (by norm_num)

private theorem theorem44_mul_three_sub_one_nonneg (j : Int) :
    0 ≤ j * (3 * j - 1) := by
  by_cases hzero : j = 0
  · simp [hzero]
  · by_cases hpos : 0 < j
    · have hj : 0 ≤ j := le_of_lt hpos
      have hlin : 0 ≤ 3 * j - 1 := by omega
      exact mul_nonneg hj hlin
    · have hj : j ≤ 0 := by omega
      have hlin : 3 * j - 1 ≤ 0 := by omega
      exact mul_nonneg_of_nonpos_of_nonpos hj hlin

private theorem theorem44_mul_three_add_one_nonneg (j : Int) :
    0 ≤ j * (3 * j + 1) := by
  by_cases h : 0 ≤ j
  · have hlin : 0 ≤ 3 * j + 1 := by omega
    exact mul_nonneg h hlin
  · have hj : j ≤ 0 := by omega
    have hlin : 3 * j + 1 ≤ 0 := by omega
    exact mul_nonneg_of_nonpos_of_nonpos hj hlin

/-- In the `k = 3r`, `l = 3j` residue class, the coefficient `q`-power splits. -/
theorem theorem44Coeff_qpow_residue_zero (q : ℂ) (r j : Int) :
    q ^ theorem44CoeffExponentIndex (3 * r) (3 * j) =
      q ^ Int.toNat (r * (3 * r + 1) / 2) *
        q ^ Int.toNat (j * (3 * j - 1)) := by
  let a : Int := r * (3 * r + 1) / 2
  let b : Int := j * (3 * j - 1)
  have ha : 0 ≤ a := theorem44_three_mul_add_one_half_nonneg r
  have hb : 0 ≤ b := theorem44_mul_three_sub_one_nonneg j
  have hidx_int :
      ((theorem44CoeffExponentIndex (3 * r) (3 * j) : Nat) : Int) = a + b := by
    simpa [a, b] using theorem44CoeffExponentIndex_residue_zero_eq r j
  have hidx_nat :
      theorem44CoeffExponentIndex (3 * r) (3 * j) =
        Int.toNat a + Int.toNat b := by
    have h := congrArg Int.toNat hidx_int
    simpa [Int.toNat_add ha hb] using h
  rw [hidx_nat, pow_add]

/-- In the `k = -3r-1`, `l = 3j+1` residue class, the coefficient `q`-power splits. -/
theorem theorem44Coeff_qpow_residue_one (q : ℂ) (r j : Int) :
    q ^ theorem44CoeffExponentIndex (-(3 * r) - 1) (3 * j + 1) =
      q ^ Int.toNat (r * (3 * r + 1) / 2) *
        q ^ Int.toNat (j * (3 * j + 1)) := by
  let a : Int := r * (3 * r + 1) / 2
  let b : Int := j * (3 * j + 1)
  have ha : 0 ≤ a := theorem44_three_mul_add_one_half_nonneg r
  have hb : 0 ≤ b := theorem44_mul_three_add_one_nonneg j
  have hidx_int :
      ((theorem44CoeffExponentIndex (-(3 * r) - 1) (3 * j + 1) : Nat) : Int) =
        a + b := by
    simpa [a, b] using theorem44CoeffExponentIndex_residue_one_eq r j
  have hidx_nat :
      theorem44CoeffExponentIndex (-(3 * r) - 1) (3 * j + 1) =
        Int.toNat a + Int.toNat b := by
    have h := congrArg Int.toNat hidx_int
    simpa [Int.toNat_add ha hb] using h
  rw [hidx_nat, pow_add]

/-- In the `l = 3j` residue class, the sign is unchanged. -/
theorem theorem44_sign_residue_zero (j : Int) :
    (-1 : ℂ) ^ (3 * j) = (-1 : ℂ) ^ j := by
  rw [show (3 : Int) * j = j + 2 * j by ring]
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  have hsq : (-1 : ℂ) ^ ((2 : Int) * j) = 1 := by
    rw [zpow_mul]
    norm_num
  rw [hsq]
  ring

/-- In the `l = 3j+1` residue class, the sign picks up a minus sign. -/
theorem theorem44_sign_residue_one (j : Int) :
    (-1 : ℂ) ^ (3 * j + 1) = -((-1 : ℂ) ^ j) := by
  rw [show (3 : Int) * j + 1 = j + 2 * j + 1 by ring]
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  have hsq : (-1 : ℂ) ^ ((2 : Int) * j) = 1 := by
    rw [zpow_mul]
    norm_num
  rw [hsq]
  norm_num

/-- In the `l = 3j+2` residue class, the sign is unchanged. -/
theorem theorem44_sign_residue_two (j : Int) :
    (-1 : ℂ) ^ (3 * j + 2) = (-1 : ℂ) ^ j := by
  rw [show (3 : Int) * j + 2 = j + 2 * j + 2 by ring]
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  have hsq : (-1 : ℂ) ^ ((2 : Int) * j) = 1 := by
    rw [zpow_mul]
    norm_num
  rw [hsq]
  norm_num

/-- Signed coefficient `q`-power in the `k = 3r`, `l = 3j` residue class. -/
theorem theorem44Coeff_signed_qpow_residue_zero (q : ℂ) (r j : Int) :
    (-1 : ℂ) ^ (3 * j) * q ^ theorem44CoeffExponentIndex (3 * r) (3 * j) =
      q ^ Int.toNat (r * (3 * r + 1) / 2) *
        ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j - 1))) := by
  rw [theorem44_sign_residue_zero j, theorem44Coeff_qpow_residue_zero q r j]
  ring

/-- Signed coefficient `q`-power in the `k = -3r-1`, `l = 3j+1` residue class. -/
theorem theorem44Coeff_signed_qpow_residue_one (q : ℂ) (r j : Int) :
    (-1 : ℂ) ^ (3 * j + 1) *
        q ^ theorem44CoeffExponentIndex (-(3 * r) - 1) (3 * j + 1) =
      -(q ^ Int.toNat (r * (3 * r + 1) / 2) *
          ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j + 1)))) := by
  rw [theorem44_sign_residue_one j, theorem44Coeff_qpow_residue_one q r j]
  ring

/-- Full coefficient monomial in the `k = 3r`, `l = 3j` residue class. -/
theorem theorem44Coeff_monomial_residue_zero (q z : ℂ) (r j : Int) :
    z ^ (3 * r) *
        ((-1 : ℂ) ^ (3 * j) * q ^ theorem44CoeffExponentIndex (3 * r) (3 * j)) =
      (z ^ (3 * r) * q ^ Int.toNat (r * (3 * r + 1) / 2)) *
        ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j - 1))) := by
  rw [theorem44Coeff_signed_qpow_residue_zero q r j]
  ring

/-- Full coefficient monomial in the `k = -3r-1`, `l = 3j+1` residue class. -/
theorem theorem44Coeff_monomial_residue_one (q z : ℂ) (r j : Int) :
    z ^ (-(3 * r) - 1) *
        ((-1 : ℂ) ^ (3 * j + 1) *
          q ^ theorem44CoeffExponentIndex (-(3 * r) - 1) (3 * j + 1)) =
      -((z ^ (-(3 * r) - 1) * q ^ Int.toNat (r * (3 * r + 1) / 2)) *
          ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j + 1)))) := by
  rw [theorem44Coeff_signed_qpow_residue_one q r j]
  ring

/-- Common outer factor in the two nonzero residue branches for fixed `r`. -/
noncomputable def theorem44CoeffPairedBranchOuter (q : ℂ) (r : Int) : ℂ :=
  q ^ Int.toNat (r * (3 * r + 1) / 2)

/-- Inner bracket in the paired nonzero residue branches for fixed `r,j`. -/
noncomputable def theorem44CoeffPairedBranchInner (q z : ℂ) (r j : Int) : ℂ :=
  z ^ (3 * r) * ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j - 1))) -
    z ^ (-(3 * r) - 1) * ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j + 1)))

/-- Factorized paired nonzero residue contribution for fixed `r,j`. -/
noncomputable def theorem44CoeffPairedBranchTerm (q z : ℂ) (r j : Int) : ℂ :=
  theorem44CoeffPairedBranchOuter q r * theorem44CoeffPairedBranchInner q z r j

/-- Symmetric finite partial sum of the paired-branch inner terms over `-N ≤ j ≤ N`. -/
noncomputable def theorem44CoeffPairedBranchInnerPartial
    (q z : ℂ) (r : Int) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), theorem44CoeffPairedBranchInner q z r j

/-- Left theta-like finite partial in the paired-branch inner term. -/
noncomputable def theorem44CoeffPairedBranchInnerLeftPartial
    (q z : ℂ) (r : Int) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    z ^ (3 * r) * ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j - 1)))

/-- Right theta-like finite partial in the paired-branch inner term. -/
noncomputable def theorem44CoeffPairedBranchInnerRightPartial
    (q z : ℂ) (r : Int) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    z ^ (-(3 * r) - 1) * ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j + 1)))

/-- Base left theta-like finite partial, before multiplying by the fixed `z`-factor. -/
noncomputable def theorem44CoeffPairedBranchLeftThetaPartial
    (q : ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    (-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j - 1))

/-- Base right theta-like finite partial, before multiplying by the fixed `z`-factor. -/
noncomputable def theorem44CoeffPairedBranchRightThetaPartial
    (q : ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    (-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j + 1))

/-- The base theta term left after the paired nonzero residue branches are combined. -/
noncomputable def theorem44CoeffPairedBranchThetaTerm (q : ℂ) (j : Int) : ℂ :=
  (-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j - 1))

/-- The infinite base theta series attached to the paired nonzero residue branches. -/
noncomputable def theorem44CoeffPairedBranchThetaSeries (q : ℂ) : ℂ :=
  ∑' j : ℤ, theorem44CoeffPairedBranchThetaTerm q j

/-- The base theta finite partial is the symmetric partial sum of the named theta term. -/
theorem theorem44CoeffPairedBranchLeftThetaPartial_eq_sum_thetaTerm
    (q : ℂ) (N : ℕ) :
    theorem44CoeffPairedBranchLeftThetaPartial q N =
      ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        theorem44CoeffPairedBranchThetaTerm q j := by
  rfl

/-- On symmetric finite intervals, the right theta-like partial reindexes to the left one. -/
theorem theorem44CoeffPairedBranchRightThetaPartial_eq_leftThetaPartial
    (q : ℂ) (N : ℕ) :
    theorem44CoeffPairedBranchRightThetaPartial q N =
      theorem44CoeffPairedBranchLeftThetaPartial q N := by
  rw [theorem44CoeffPairedBranchRightThetaPartial,
    theorem44CoeffPairedBranchLeftThetaPartial]
  refine Finset.sum_bij (fun j _ => -j) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_Icc] at hj
    simpa [Finset.mem_Icc] using
      (show -(N : ℤ) ≤ -j ∧ -j ≤ (N : ℤ) by constructor <;> omega)
  · intro a _ b _ h
    simpa using congrArg Neg.neg h
  · intro b hb
    refine ⟨-b, ?_, by simp⟩
    rw [Finset.mem_Icc] at hb
    simpa [Finset.mem_Icc] using
      (show -(N : ℤ) ≤ -b ∧ -b ≤ (N : ℤ) by constructor <;> omega)
  · intro j _
    have hsign : (-1 : ℂ) ^ (-j) = (-1 : ℂ) ^ j := by
      by_cases h : Even j <;> simp [neg_one_zpow_eq_ite, h]
    have hexp : (-j) * (3 * (-j) - 1) = j * (3 * j + 1) := by ring
    rw [hsign, hexp]

/-- The paired-branch theta term is a Jacobi-series term with base `q^3` and `z=-q⁻¹`. -/
theorem theorem44CoeffPairedBranchThetaTerm_eq_jacobiSeriesTerm
    (q : ℂ) (hq : q ≠ 0) (j : Int) :
    theorem44CoeffPairedBranchThetaTerm q j =
      (-q⁻¹) ^ j * (q ^ 3) ^ (j ^ 2) := by
  have hnonneg : 0 ≤ j * (3 * j - 1) :=
    theorem44_mul_three_sub_one_nonneg j
  have hnat :
      q ^ Int.toNat (j * (3 * j - 1)) = q ^ (j * (3 * j - 1)) := by
    rw [← zpow_natCast]
    congr 1
    exact Int.toNat_of_nonneg hnonneg
  unfold theorem44CoeffPairedBranchThetaTerm
  rw [hnat]
  have hbase : (-q⁻¹ : ℂ) = (-1 : ℂ) * q ^ (-1 : ℤ) := by
    field_simp [hq]
  rw [hbase, mul_zpow]
  have hqneg : (q ^ (-1 : ℤ)) ^ j = q ^ ((-1 : ℤ) * j) := by
    exact (zpow_mul q (-1 : ℤ) j).symm
  have hqcube : (q ^ 3) ^ (j ^ 2) = q ^ (3 * (j ^ 2)) := by
    simpa using (zpow_mul q (3 : ℤ) (j ^ 2)).symm
  rw [hqneg, hqcube]
  rw [show (-1 : ℂ) ^ j * q ^ ((-1 : ℤ) * j) * q ^ (3 * (j ^ 2)) =
      (-1 : ℂ) ^ j * (q ^ ((-1 : ℤ) * j) * q ^ (3 * (j ^ 2))) by ring]
  rw [← zpow_add₀ hq]
  congr 2
  ring

/-- The paired-branch theta series is a Jacobi bilateral series. -/
theorem theorem44CoeffPairedBranchThetaSeries_eq_jacobiInfiniteSeries
    (q : ℂ) (hq : q ≠ 0) :
    theorem44CoeffPairedBranchThetaSeries q =
      jacobiInfiniteSeries (q ^ 3) (-q⁻¹) := by
  rw [theorem44CoeffPairedBranchThetaSeries, jacobiInfiniteSeries]
  exact tsum_congr fun j =>
    theorem44CoeffPairedBranchThetaTerm_eq_jacobiSeriesTerm q hq j

/-- The paired-branch theta terms are summable for `‖q‖ < 1`. -/
theorem summable_theorem44CoeffPairedBranchThetaTerm
    (q : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) :
    Summable fun j : ℤ => theorem44CoeffPairedBranchThetaTerm q j := by
  have hq3 : ‖q ^ 3‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hqnorm (by norm_num)
  exact (Ch02.summable_jacobiInfiniteSeries_terms (q ^ 3) (-q⁻¹) hq3).congr
    fun j => (theorem44CoeffPairedBranchThetaTerm_eq_jacobiSeriesTerm q hq j).symm

/-- HasSum form of the paired-branch theta series. -/
theorem hasSum_theorem44CoeffPairedBranchThetaTerm
    (q : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) :
    HasSum (fun j : ℤ => theorem44CoeffPairedBranchThetaTerm q j)
      (theorem44CoeffPairedBranchThetaSeries q) :=
  (summable_theorem44CoeffPairedBranchThetaTerm q hqnorm hq).hasSum

/-- The finite paired-branch base theta partial is a Jacobi symmetric partial. -/
theorem theorem44CoeffPairedBranchLeftThetaPartial_eq_jacobiSeriesSymmetricPartial
    (q : ℂ) (hq : q ≠ 0) (N : ℕ) :
    theorem44CoeffPairedBranchLeftThetaPartial q N =
      Ch02.jacobiSeriesSymmetricPartial (q ^ 3) (-q⁻¹) N := by
  rw [theorem44CoeffPairedBranchLeftThetaPartial_eq_sum_thetaTerm,
    Ch02.jacobiSeriesSymmetricPartial]
  exact Finset.sum_congr rfl fun j _ =>
    theorem44CoeffPairedBranchThetaTerm_eq_jacobiSeriesTerm q hq j

/-- The paired-branch base theta symmetric partials tend to the named theta series. -/
theorem tendsto_theorem44CoeffPairedBranchLeftThetaPartial
    (q : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) :
    Tendsto (fun N : ℕ => theorem44CoeffPairedBranchLeftThetaPartial q N) atTop
      (𝓝 (theorem44CoeffPairedBranchThetaSeries q)) := by
  have hq3 : ‖q ^ 3‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hqnorm (by norm_num)
  have hcongr :
      (fun N : ℕ => theorem44CoeffPairedBranchLeftThetaPartial q N) =
        fun N : ℕ => Ch02.jacobiSeriesSymmetricPartial (q ^ 3) (-q⁻¹) N := by
    funext N
    exact theorem44CoeffPairedBranchLeftThetaPartial_eq_jacobiSeriesSymmetricPartial q hq N
  rw [hcongr, theorem44CoeffPairedBranchThetaSeries_eq_jacobiInfiniteSeries q hq]
  exact Ch02.tendsto_jacobiSeriesSymmetricPartial (q ^ 3) (-q⁻¹) hq3

/-- Symmetric finite partial sum of the paired-branch terms over `-N ≤ j ≤ N`. -/
noncomputable def theorem44CoeffPairedBranchTermPartial
    (q z : ℂ) (r : Int) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), theorem44CoeffPairedBranchTerm q z r j

/--
Symmetric finite partial sum of the two raw nonzero residue monomials over
`-N ≤ j ≤ N`, before packaging them as the named paired branch.
-/
noncomputable def theorem44CoeffMonomialPairPartial
    (q z : ℂ) (r : Int) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    (z ^ (3 * r) *
        ((-1 : ℂ) ^ (3 * j) * q ^ theorem44CoeffExponentIndex (3 * r) (3 * j)) +
      z ^ (-(3 * r) - 1) *
        ((-1 : ℂ) ^ (3 * j + 1) *
          q ^ theorem44CoeffExponentIndex (-(3 * r) - 1) (3 * j + 1)))

/-- The named paired-branch outer factor unfolds to Chan's `r`-exponent. -/
theorem theorem44CoeffPairedBranchOuter_eq (q : ℂ) (r : Int) :
    theorem44CoeffPairedBranchOuter q r =
      q ^ Int.toNat (r * (3 * r + 1) / 2) := by
  rfl

/-- The named paired-branch inner factor unfolds to the `j`-indexed difference. -/
theorem theorem44CoeffPairedBranchInner_eq (q z : ℂ) (r j : Int) :
    theorem44CoeffPairedBranchInner q z r j =
      z ^ (3 * r) * ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j - 1))) -
        z ^ (-(3 * r) - 1) *
          ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j + 1))) := by
  rfl

/-- The named paired-branch term unfolds to its outer-times-inner product. -/
theorem theorem44CoeffPairedBranchTerm_eq (q z : ℂ) (r j : Int) :
    theorem44CoeffPairedBranchTerm q z r j =
      theorem44CoeffPairedBranchOuter q r * theorem44CoeffPairedBranchInner q z r j := by
  rfl

/-- Fully explicit form of the named paired nonzero residue contribution. -/
theorem theorem44CoeffPairedBranchTerm_eq_explicit (q z : ℂ) (r j : Int) :
    theorem44CoeffPairedBranchTerm q z r j =
      q ^ Int.toNat (r * (3 * r + 1) / 2) *
        (z ^ (3 * r) * ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j - 1))) -
          z ^ (-(3 * r) - 1) *
            ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j + 1)))) := by
  rfl

/-- The paired-branch inner finite partial splits into its left and right theta-like parts. -/
theorem theorem44CoeffPairedBranchInnerPartial_eq_left_sub_right
    (q z : ℂ) (r : Int) (N : ℕ) :
    theorem44CoeffPairedBranchInnerPartial q z r N =
      theorem44CoeffPairedBranchInnerLeftPartial q z r N -
        theorem44CoeffPairedBranchInnerRightPartial q z r N := by
  simp [theorem44CoeffPairedBranchInnerPartial, theorem44CoeffPairedBranchInnerLeftPartial,
    theorem44CoeffPairedBranchInnerRightPartial, theorem44CoeffPairedBranchInner,
    Finset.sum_sub_distrib]

/-- The left inner finite partial factors out its fixed `z`-power. -/
theorem theorem44CoeffPairedBranchInnerLeftPartial_eq_zpow_mul_theta
    (q z : ℂ) (r : Int) (N : ℕ) :
    theorem44CoeffPairedBranchInnerLeftPartial q z r N =
      z ^ (3 * r) * theorem44CoeffPairedBranchLeftThetaPartial q N := by
  simp [theorem44CoeffPairedBranchInnerLeftPartial,
    theorem44CoeffPairedBranchLeftThetaPartial, Finset.mul_sum]

/-- The right inner finite partial factors out its fixed `z`-power. -/
theorem theorem44CoeffPairedBranchInnerRightPartial_eq_zpow_mul_theta
    (q z : ℂ) (r : Int) (N : ℕ) :
    theorem44CoeffPairedBranchInnerRightPartial q z r N =
      z ^ (-(3 * r) - 1) * theorem44CoeffPairedBranchRightThetaPartial q N := by
  simp [theorem44CoeffPairedBranchInnerRightPartial,
    theorem44CoeffPairedBranchRightThetaPartial, Finset.mul_sum]

/-- The paired-branch inner finite partial in terms of the base theta-like finite partials. -/
theorem theorem44CoeffPairedBranchInnerPartial_eq_zpow_mul_theta_sub_zpow_mul_theta
    (q z : ℂ) (r : Int) (N : ℕ) :
    theorem44CoeffPairedBranchInnerPartial q z r N =
      z ^ (3 * r) * theorem44CoeffPairedBranchLeftThetaPartial q N -
        z ^ (-(3 * r) - 1) * theorem44CoeffPairedBranchRightThetaPartial q N := by
  rw [theorem44CoeffPairedBranchInnerPartial_eq_left_sub_right,
    theorem44CoeffPairedBranchInnerLeftPartial_eq_zpow_mul_theta,
    theorem44CoeffPairedBranchInnerRightPartial_eq_zpow_mul_theta]

/-- The paired-branch inner finite partial as one theta partial times the `z`-power difference. -/
theorem theorem44CoeffPairedBranchInnerPartial_eq_zpow_sub_zpow_mul_theta
    (q z : ℂ) (r : Int) (N : ℕ) :
    theorem44CoeffPairedBranchInnerPartial q z r N =
      (z ^ (3 * r) - z ^ (-(3 * r) - 1)) *
        theorem44CoeffPairedBranchLeftThetaPartial q N := by
  rw [theorem44CoeffPairedBranchInnerPartial_eq_zpow_mul_theta_sub_zpow_mul_theta,
    theorem44CoeffPairedBranchRightThetaPartial_eq_leftThetaPartial]
  ring

/-- The paired-branch inner finite partials converge to the theta-series factorization. -/
theorem tendsto_theorem44CoeffPairedBranchInnerPartial
    (q z : ℂ) (r : Int) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) :
    Tendsto (fun N : ℕ => theorem44CoeffPairedBranchInnerPartial q z r N) atTop
      (𝓝 ((z ^ (3 * r) - z ^ (-(3 * r) - 1)) *
        theorem44CoeffPairedBranchThetaSeries q)) := by
  have htheta := tendsto_theorem44CoeffPairedBranchLeftThetaPartial q hqnorm hq
  have hscaled :
      Tendsto
        (fun N : ℕ =>
          (z ^ (3 * r) - z ^ (-(3 * r) - 1)) *
            theorem44CoeffPairedBranchLeftThetaPartial q N) atTop
        (𝓝 ((z ^ (3 * r) - z ^ (-(3 * r) - 1)) *
          theorem44CoeffPairedBranchThetaSeries q)) :=
    tendsto_const_nhds.mul htheta
  refine hscaled.congr' ?_
  exact Eventually.of_forall fun N =>
    (theorem44CoeffPairedBranchInnerPartial_eq_zpow_sub_zpow_mul_theta q z r N).symm

/-- The paired-branch finite partial factors with the inner left-minus-right split exposed. -/
theorem theorem44CoeffPairedBranchTermPartial_eq_outer_mul_left_sub_right
    (q z : ℂ) (r : Int) (N : ℕ) :
    theorem44CoeffPairedBranchTermPartial q z r N =
      theorem44CoeffPairedBranchOuter q r *
        (theorem44CoeffPairedBranchInnerLeftPartial q z r N -
          theorem44CoeffPairedBranchInnerRightPartial q z r N) := by
  simp [theorem44CoeffPairedBranchTermPartial, theorem44CoeffPairedBranchInnerLeftPartial,
    theorem44CoeffPairedBranchInnerRightPartial, theorem44CoeffPairedBranchTerm,
    theorem44CoeffPairedBranchInner, Finset.mul_sum, Finset.sum_sub_distrib, mul_sub]

/-- The paired-branch finite partial with all fixed `r,z` factors pulled outside theta sums. -/
theorem theorem44CoeffPairedBranchTermPartial_eq_outer_mul_zpow_theta_sub_zpow_theta
    (q z : ℂ) (r : Int) (N : ℕ) :
    theorem44CoeffPairedBranchTermPartial q z r N =
      theorem44CoeffPairedBranchOuter q r *
        (z ^ (3 * r) * theorem44CoeffPairedBranchLeftThetaPartial q N -
          z ^ (-(3 * r) - 1) * theorem44CoeffPairedBranchRightThetaPartial q N) := by
  simp [theorem44CoeffPairedBranchTermPartial, theorem44CoeffPairedBranchTerm,
    theorem44CoeffPairedBranchInner, theorem44CoeffPairedBranchLeftThetaPartial,
    theorem44CoeffPairedBranchRightThetaPartial, Finset.mul_sum, Finset.sum_sub_distrib,
    mul_sub]

/-- The paired-branch finite partial as the outer factor times one theta partial. -/
theorem theorem44CoeffPairedBranchTermPartial_eq_outer_mul_zpow_sub_zpow_mul_theta
    (q z : ℂ) (r : Int) (N : ℕ) :
    theorem44CoeffPairedBranchTermPartial q z r N =
      theorem44CoeffPairedBranchOuter q r *
        ((z ^ (3 * r) - z ^ (-(3 * r) - 1)) *
          theorem44CoeffPairedBranchLeftThetaPartial q N) := by
  rw [theorem44CoeffPairedBranchTermPartial_eq_outer_mul_zpow_theta_sub_zpow_theta,
    theorem44CoeffPairedBranchRightThetaPartial_eq_leftThetaPartial]
  ring

/-- The paired-branch term finite partials converge to the outer times theta-series factor. -/
theorem tendsto_theorem44CoeffPairedBranchTermPartial
    (q z : ℂ) (r : Int) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) :
    Tendsto (fun N : ℕ => theorem44CoeffPairedBranchTermPartial q z r N) atTop
      (𝓝 (theorem44CoeffPairedBranchOuter q r *
        ((z ^ (3 * r) - z ^ (-(3 * r) - 1)) *
          theorem44CoeffPairedBranchThetaSeries q))) := by
  have htheta := tendsto_theorem44CoeffPairedBranchLeftThetaPartial q hqnorm hq
  have hscaled :
      Tendsto
        (fun N : ℕ =>
          theorem44CoeffPairedBranchOuter q r *
            ((z ^ (3 * r) - z ^ (-(3 * r) - 1)) *
              theorem44CoeffPairedBranchLeftThetaPartial q N)) atTop
        (𝓝 (theorem44CoeffPairedBranchOuter q r *
          ((z ^ (3 * r) - z ^ (-(3 * r) - 1)) *
            theorem44CoeffPairedBranchThetaSeries q))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.mul htheta)
  refine hscaled.congr' ?_
  exact Eventually.of_forall fun N =>
    (theorem44CoeffPairedBranchTermPartial_eq_outer_mul_zpow_sub_zpow_mul_theta q z r N).symm

/-- The paired-branch finite partial sum factors out the fixed `r` outer term. -/
theorem theorem44CoeffPairedBranchTermPartial_eq_outer_mul_innerPartial
    (q z : ℂ) (r : Int) (N : ℕ) :
    theorem44CoeffPairedBranchTermPartial q z r N =
      theorem44CoeffPairedBranchOuter q r *
        theorem44CoeffPairedBranchInnerPartial q z r N := by
  simp [theorem44CoeffPairedBranchTermPartial, theorem44CoeffPairedBranchInnerPartial,
    theorem44CoeffPairedBranchTerm, Finset.mul_sum]

/--
The two nonzero residue branches with the same `r,j` combine into the
factorized difference used in Chan's coefficient extraction.
-/
theorem theorem44Coeff_monomial_residue_zero_add_one (q z : ℂ) (r j : Int) :
    z ^ (3 * r) *
        ((-1 : ℂ) ^ (3 * j) * q ^ theorem44CoeffExponentIndex (3 * r) (3 * j)) +
      z ^ (-(3 * r) - 1) *
        ((-1 : ℂ) ^ (3 * j + 1) *
          q ^ theorem44CoeffExponentIndex (-(3 * r) - 1) (3 * j + 1)) =
      q ^ Int.toNat (r * (3 * r + 1) / 2) *
        (z ^ (3 * r) * ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j - 1))) -
          z ^ (-(3 * r) - 1) *
            ((-1 : ℂ) ^ j * q ^ Int.toNat (j * (3 * j + 1)))) := by
  rw [theorem44Coeff_monomial_residue_zero q z r j,
    theorem44Coeff_monomial_residue_one q z r j]
  ring

/-- Named paired-branch form of `theorem44Coeff_monomial_residue_zero_add_one`. -/
theorem theorem44Coeff_monomial_residue_zero_add_one_eq_pairedTerm
    (q z : ℂ) (r j : Int) :
    z ^ (3 * r) *
        ((-1 : ℂ) ^ (3 * j) * q ^ theorem44CoeffExponentIndex (3 * r) (3 * j)) +
      z ^ (-(3 * r) - 1) *
        ((-1 : ℂ) ^ (3 * j + 1) *
          q ^ theorem44CoeffExponentIndex (-(3 * r) - 1) (3 * j + 1)) =
      theorem44CoeffPairedBranchTerm q z r j := by
  rw [theorem44Coeff_monomial_residue_zero_add_one q z r j]
  rfl

/--
The symmetric finite sum of the two raw nonzero residue branches is exactly
the named paired-branch finite partial sum.
-/
theorem theorem44CoeffMonomialPairPartial_eq_pairedBranchTermPartial
    (q z : ℂ) (r : Int) (N : ℕ) :
    theorem44CoeffMonomialPairPartial q z r N =
      theorem44CoeffPairedBranchTermPartial q z r N := by
  simp [theorem44CoeffMonomialPairPartial, theorem44CoeffPairedBranchTermPartial,
    theorem44Coeff_monomial_residue_zero_add_one_eq_pairedTerm]

/--
The raw two-branch finite partial sum factors into Chan's fixed outer
`r`-factor times the paired inner finite partial.
-/
theorem theorem44CoeffMonomialPairPartial_eq_outer_mul_innerPartial
    (q z : ℂ) (r : Int) (N : ℕ) :
    theorem44CoeffMonomialPairPartial q z r N =
      theorem44CoeffPairedBranchOuter q r *
        theorem44CoeffPairedBranchInnerPartial q z r N := by
  rw [theorem44CoeffMonomialPairPartial_eq_pairedBranchTermPartial,
    theorem44CoeffPairedBranchTermPartial_eq_outer_mul_innerPartial]

/-- Raw two-branch finite partial compressed to one base theta partial. -/
theorem theorem44CoeffMonomialPairPartial_eq_outer_mul_zpow_sub_zpow_mul_theta
    (q z : ℂ) (r : Int) (N : ℕ) :
    theorem44CoeffMonomialPairPartial q z r N =
      theorem44CoeffPairedBranchOuter q r *
        ((z ^ (3 * r) - z ^ (-(3 * r) - 1)) *
          theorem44CoeffPairedBranchLeftThetaPartial q N) := by
  rw [theorem44CoeffMonomialPairPartial_eq_pairedBranchTermPartial,
    theorem44CoeffPairedBranchTermPartial_eq_outer_mul_zpow_sub_zpow_mul_theta]

/-- The raw paired nonzero residue finite partials converge to the compressed theta-series form. -/
theorem tendsto_theorem44CoeffMonomialPairPartial
    (q z : ℂ) (r : Int) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) :
    Tendsto (fun N : ℕ => theorem44CoeffMonomialPairPartial q z r N) atTop
      (𝓝 (theorem44CoeffPairedBranchOuter q r *
        ((z ^ (3 * r) - z ^ (-(3 * r) - 1)) *
          theorem44CoeffPairedBranchThetaSeries q))) := by
  have hterm := tendsto_theorem44CoeffPairedBranchTermPartial q z r hqnorm hq
  refine hterm.congr' ?_
  exact Eventually.of_forall fun N =>
    (theorem44CoeffMonomialPairPartial_eq_pairedBranchTermPartial q z r N).symm

/-- Chan Eq. (2.12) is Theorem 4.4 after `q ↦ q^2` and `z ↦ z/q`, on factors. -/
theorem theorem44ProductFactor_substitution_eq_quintuple
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (n : ℕ) :
    theorem44ProductFactor (q ^ 2) (z / q) n = quintupleProductFactor q z n := by
  rw [theorem44ProductFactor, quintupleProductFactor]
  have h0 : (q ^ 2) ^ (n + 1) = q ^ (2 * n + 2) := by
    rw [← pow_mul]
    congr 1
  have h1 : z / q * q ^ (2 * n + 2) = z * q ^ (2 * n + 1) := by
    field_simp [hq]
    rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega]
    rw [pow_add]
    ring
  have h2 : (z / q)⁻¹ * (q ^ 2) ^ n = z⁻¹ * q ^ (2 * n + 1) := by
    rw [← pow_mul]
    field_simp [hq, hz]
    rw [show 2 * n + 1 = 1 + 2 * n by omega]
    rw [pow_add]
    ring
  have h3 : (z / q) ^ 2 * (q ^ 2) ^ (2 * n + 1) = z ^ 2 * q ^ (4 * n) := by
    rw [← pow_mul]
    field_simp [hq]
    rw [show 2 * (2 * n + 1) = 4 * n + 2 by omega]
    rw [show 4 * n + 2 = 4 * n + 2 by rfl]
    rw [pow_add]
    ring
  have h4 : (z / q)⁻¹ ^ 2 * (q ^ 2) ^ (2 * n + 1) =
      z⁻¹ ^ 2 * q ^ (4 * n + 4) := by
    rw [← pow_mul]
    field_simp [hq, hz]
    rw [show 2 * (2 * n + 1) = 4 * n + 2 by omega]
    rw [show 4 * n + 4 = 2 + (4 * n + 2) by omega]
    rw [pow_add]
    ring
  rw [h0, h1, h2, h3, h4]

/-- Theorem 4.4's finite product partial specializes to the Eq. (2.12) truncation. -/
theorem theorem44ProductPartial_substitution_eq_quintuple
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : ℕ) :
    theorem44ProductPartial (q ^ 2) (z / q) N = quintupleProductLHSTrunc q z N := by
  rw [theorem44ProductPartial]
  calc
    (∏ n ∈ Finset.range N, theorem44ProductFactor (q ^ 2) (z / q) n)
        = ∏ n ∈ Finset.range N, quintupleProductFactor q z n := by
          exact Finset.prod_congr rfl fun n _ =>
            theorem44ProductFactor_substitution_eq_quintuple q z hq hz n
    _ = quintupleProductLHSTrunc q z N :=
          quintupleProductFactor_partial_eq_trunc q z N

/-- Eq. (2.12)'s finite product truncation as five finite q-Pochhammer factors. -/
theorem quintupleProductLHSTrunc_eq_qPoch
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : ℕ) :
    quintupleProductLHSTrunc q z N =
      qPoch (q ^ 2) (q ^ 2) N * qPoch (z * q) (q ^ 2) N *
        qPoch (q / z) (q ^ 2) N * qPoch (z ^ 2) (q ^ 4) N *
          qPoch (q ^ 4 / z ^ 2) (q ^ 4) N := by
  rw [← theorem44ProductPartial_substitution_eq_quintuple q z hq hz N]
  rw [theorem44ProductPartial_eq_qPoch]
  have hbase : (q ^ 2) ^ 2 = q ^ 4 := by ring
  have h1 : (z / q) * q ^ 2 = z * q := by
    field_simp [hq]
  have h2 : (z / q)⁻¹ = q / z := by
    field_simp [hq, hz]
  have h3 : (z / q) ^ 2 * q ^ 2 = z ^ 2 := by
    field_simp [hq]
  have h4 : (q / z) ^ 2 * q ^ 2 = q ^ 4 / z ^ 2 := by
    field_simp [hz]
  rw [hbase, h1, h2, h3, h4]

/-- Theorem 4.4's product side specializes to the Eq. (2.12) product side. -/
theorem theorem44ProductLHS_substitution_eq_quintuple
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) :
    theorem44ProductLHS (q ^ 2) (z / q) = quintupleProductLHS q z := by
  rw [theorem44ProductLHS, quintupleProductLHS]
  exact tprod_congr fun n => theorem44ProductFactor_substitution_eq_quintuple q z hq hz n

private theorem summable_norm_theorem44Product_tail0 (q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-q ^ (n + 1)‖ := by
  have h := Ch02.summable_norm_mul_geometric_complex (-q) q hq
  refine h.congr fun n => ?_
  congr 1
  rw [show -q * q ^ n = -q ^ (n + 1) by
    rw [pow_succ]
    ring]

private theorem summable_norm_theorem44Product_tail1 (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-(z * q ^ (n + 1))‖ := by
  have h := Ch02.summable_norm_mul_geometric_complex (-(z * q)) q hq
  refine h.congr fun n => ?_
  congr 1
  rw [show -(z * q) * q ^ n = -(z * q ^ (n + 1)) by
    rw [pow_succ]
    ring]

private theorem summable_norm_theorem44Product_tail2 (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-(z⁻¹ * q ^ n)‖ := by
  have h := Ch02.summable_norm_mul_geometric_complex (-z⁻¹) q hq
  refine h.congr fun n => ?_
  congr 1
  ring

private theorem summable_norm_theorem44Product_tail3 (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-(z ^ 2 * q ^ (2 * n + 1))‖ := by
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have h := Ch02.summable_norm_mul_geometric_complex (-(z ^ 2 * q)) (q ^ 2) hq2
  refine h.congr fun n => ?_
  congr 1
  rw [show -(z ^ 2 * q) * (q ^ 2) ^ n = -(z ^ 2 * q ^ (2 * n + 1)) by
    rw [← pow_mul]
    rw [show 2 * n + 1 = 1 + 2 * n by omega]
    rw [pow_add]
    ring]

private theorem summable_norm_theorem44Product_tail4 (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-(z⁻¹ ^ 2 * q ^ (2 * n + 1))‖ := by
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have h := Ch02.summable_norm_mul_geometric_complex (-(z⁻¹ ^ 2 * q)) (q ^ 2) hq2
  refine h.congr fun n => ?_
  congr 1
  rw [show -(z⁻¹ ^ 2 * q) * (q ^ 2) ^ n =
      -(z⁻¹ ^ 2 * q ^ (2 * n + 1)) by
    rw [← pow_mul]
    rw [show 2 * n + 1 = 1 + 2 * n by omega]
    rw [pow_add]
    ring]

/-- Chan Theorem 4.4's product side is multipliable for `‖q‖ < 1`. -/
theorem multipliable_theorem44ProductFactor (q z : ℂ) (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ => theorem44ProductFactor q z n := by
  have h0 : Multipliable fun n : ℕ => 1 - q ^ (n + 1) := by
    have h := multipliable_one_add_of_summable (summable_norm_theorem44Product_tail0 q hq)
    simpa [sub_eq_add_neg] using h
  have h1 : Multipliable fun n : ℕ => 1 - z * q ^ (n + 1) := by
    have h := multipliable_one_add_of_summable (summable_norm_theorem44Product_tail1 q z hq)
    simpa [sub_eq_add_neg] using h
  have h2 : Multipliable fun n : ℕ => 1 - z⁻¹ * q ^ n := by
    have h := multipliable_one_add_of_summable (summable_norm_theorem44Product_tail2 q z hq)
    simpa [sub_eq_add_neg] using h
  have h3 : Multipliable fun n : ℕ => 1 - z ^ 2 * q ^ (2 * n + 1) := by
    have h := multipliable_one_add_of_summable (summable_norm_theorem44Product_tail3 q z hq)
    simpa [sub_eq_add_neg] using h
  have h4 : Multipliable fun n : ℕ => 1 - z⁻¹ ^ 2 * q ^ (2 * n + 1) := by
    have h := multipliable_one_add_of_summable (summable_norm_theorem44Product_tail4 q z hq)
    simpa [sub_eq_add_neg] using h
  exact ((((h0.mul h1).mul h2).mul h3).mul h4).congr fun n => by
    simp [theorem44ProductFactor, mul_assoc]

/-- HasProd form of Chan Theorem 4.4's product side. -/
theorem hasProd_theorem44ProductFactor (q z : ℂ) (hq : ‖q‖ < 1) :
    HasProd (fun n : ℕ => theorem44ProductFactor q z n) (theorem44ProductLHS q z) :=
  (multipliable_theorem44ProductFactor q z hq).hasProd

/-- The finite Theorem 4.4 product partials tend to the infinite product side. -/
theorem tendsto_theorem44ProductPartial (q z : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => theorem44ProductPartial q z N) atTop
      (𝓝 (theorem44ProductLHS q z)) := by
  have h := (multipliable_theorem44ProductFactor q z hq).tendsto_prod_tprod_nat
  simpa [theorem44ProductLHS, theorem44ProductPartial] using h

/-- Exponent `n(3n+1)/2` in Chan Theorem 4.4's series side. -/
def theorem44SeriesExponentIndex (n : Int) : Nat :=
  Int.toNat (n * (3 * n + 1) / 2)

private lemma theorem44SeriesExponentIndex_nonneg (n : Int) :
    0 ≤ n * (3 * n + 1) / 2 :=
  Int.ediv_nonneg (theorem44_mul_three_add_one_nonneg n) (by norm_num)

/-- Chan Theorem 4.4's displayed series term. -/
noncomputable def theorem44SeriesTerm (q z : ℂ) (n : ℤ) : ℂ :=
  q ^ theorem44SeriesExponentIndex n * (z ^ (3 * n) - z ^ (-(3 * n) - 1))

/-- Chan Theorem 4.4's displayed series side. -/
noncomputable def theorem44SeriesRHS (q z : ℂ) : ℂ :=
  ∑' n : ℤ, theorem44SeriesTerm q z n

/-- Exponent `n(3n+1)` in Theorem 4.4 after the substitution `q ↦ q^2`. -/
def theorem44SubstitutedQuadraticIndex (n : Int) : Nat :=
  Int.toNat (n * (3 * n + 1))

private lemma theorem44SubstitutedQuadraticIndex_nonneg (n : Int) :
    0 ≤ n * (3 * n + 1) := by
  nlinarith [sq_nonneg (3 * n + 1), sq_nonneg n]

/-- Theorem 4.4 series term after the substitution `q ↦ q^2`, `z ↦ z/q`. -/
noncomputable def theorem44SubstitutedSeriesTerm (q z : ℂ) (n : ℤ) : ℂ :=
  q ^ theorem44SubstitutedQuadraticIndex n *
    ((z / q) ^ (3 * n) - (z / q) ^ (-(3 * n + 1)))

/-- Theorem 4.4 series side after the substitution `q ↦ q^2`, `z ↦ z/q`. -/
noncomputable def theorem44SubstitutedSeriesRHS (q z : ℂ) : ℂ :=
  ∑' n : ℤ, theorem44SubstitutedSeriesTerm q z n

/-- The original Theorem 4.4 term becomes the substituted term under `q ↦ q^2`, `z ↦ z/q`. -/
theorem theorem44SeriesTerm_substitution_eq_substituted
    (q z : ℂ) (n : ℤ) :
    theorem44SeriesTerm (q ^ 2) (z / q) n =
      theorem44SubstitutedSeriesTerm q z n := by
  have hnum_nonneg : 0 ≤ n * (3 * n + 1) :=
    theorem44_mul_three_add_one_nonneg n
  have hhalf_nonneg : 0 ≤ n * (3 * n + 1) / 2 :=
    theorem44SeriesExponentIndex_nonneg n
  have hleft :
      (q ^ 2) ^ theorem44SeriesExponentIndex n =
        (q ^ 2) ^ (n * (3 * n + 1) / 2) := by
    rw [← zpow_natCast]
    congr 1
    exact Int.toNat_of_nonneg hhalf_nonneg
  have hright :
      q ^ theorem44SubstitutedQuadraticIndex n =
        q ^ (n * (3 * n + 1)) := by
    rw [← zpow_natCast]
    congr 1
    exact Int.toNat_of_nonneg hnum_nonneg
  have hpow :
      (q ^ 2) ^ theorem44SeriesExponentIndex n =
        q ^ theorem44SubstitutedQuadraticIndex n := by
    have hpow_natbase :
        (q ^ 2) ^ (n * (3 * n + 1) / 2) =
          q ^ ((2 : Int) * (n * (3 * n + 1) / 2)) := by
      simpa using (zpow_mul q (2 : ℤ) (n * (3 * n + 1) / 2)).symm
    rw [hleft, hright]
    rw [hpow_natbase]
    congr 1
    rw [show (2 : Int) * (n * (3 * n + 1) / 2) =
        (n * (3 * n + 1) / 2) * 2 by ring]
    exact Int.ediv_mul_cancel (int_two_dvd_mul_three_add_one n)
  rw [theorem44SeriesTerm, theorem44SubstitutedSeriesTerm, hpow]
  ring_nf

/-- The original Theorem 4.4 series side becomes the substituted series side. -/
theorem theorem44SeriesRHS_substitution_eq_substituted (q z : ℂ) :
    theorem44SeriesRHS (q ^ 2) (z / q) =
      theorem44SubstitutedSeriesRHS q z := by
  rw [theorem44SeriesRHS, theorem44SubstitutedSeriesRHS]
  exact tsum_congr fun n => theorem44SeriesTerm_substitution_eq_substituted q z n

private theorem theorem44SubstitutedSeriesTerm_first_eq
    (q z : ℂ) (hq : q ≠ 0) (n : ℤ) :
    q ^ theorem44SubstitutedQuadraticIndex n * ((z / q) ^ (3 * n)) =
      (z ^ 3 / q ^ 2) ^ n * (q ^ 3) ^ (n ^ 2) := by
  have hidx : ((theorem44SubstitutedQuadraticIndex n : ℕ) : ℤ) =
      n * (3 * n + 1) := by
    exact Int.toNat_of_nonneg (theorem44SubstitutedQuadraticIndex_nonneg n)
  have hq2n : (q ^ 2) ^ n = q ^ (2 * n) := by
    rw [← zpow_natCast q 2, ← zpow_mul]
    norm_num
  have hq3n2 : (q ^ 3) ^ (n ^ 2) = q ^ (3 * n ^ 2) := by
    rw [← zpow_natCast q 3, ← zpow_mul]
    norm_num
  have hz3n : (z ^ 3) ^ n = z ^ (3 * n) := by
    rw [← zpow_natCast z 3, ← zpow_mul]
    norm_num
  rw [← zpow_natCast, hidx]
  rw [div_zpow, div_zpow]
  rw [hz3n, hq2n, hq3n2]
  field_simp [hq]
  rw [show q ^ (n * (3 * n + 1)) * z ^ (3 * n) * q ^ (2 * n) =
      z ^ (3 * n) * (q ^ (n * (3 * n + 1)) * q ^ (2 * n)) by ring]
  rw [show z ^ (3 * n) * q ^ (3 * n) * q ^ (3 * n ^ 2) =
      z ^ (3 * n) * (q ^ (3 * n) * q ^ (3 * n ^ 2)) by ring]
  rw [← zpow_add₀ hq, ← zpow_add₀ hq]
  congr 1
  ring_nf

private theorem theorem44SubstitutedSeriesTerm_second_eq
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (n : ℤ) :
    q ^ theorem44SubstitutedQuadraticIndex n * ((z / q) ^ (-(3 * n + 1))) =
      (q / z) * ((q ^ 4 / z ^ 3) ^ n * (q ^ 3) ^ (n ^ 2)) := by
  have hidx : ((theorem44SubstitutedQuadraticIndex n : ℕ) : ℤ) =
      n * (3 * n + 1) := by
    exact Int.toNat_of_nonneg (theorem44SubstitutedQuadraticIndex_nonneg n)
  have hq4n : (q ^ 4) ^ n = q ^ (4 * n) := by
    rw [← zpow_natCast q 4, ← zpow_mul]
    norm_num
  have hz3n : (z ^ 3) ^ n = z ^ (3 * n) := by
    rw [← zpow_natCast z 3, ← zpow_mul]
    norm_num
  have hq3n2 : (q ^ 3) ^ (n ^ 2) = q ^ (3 * n ^ 2) := by
    rw [← zpow_natCast q 3, ← zpow_mul]
    norm_num
  have hzpart : z ^ (-(3 * n + 1)) * z * z ^ (3 * n) = 1 := by
    nth_rewrite 2 [show z = z ^ (1 : ℤ) by simp]
    rw [← zpow_add₀ hz, ← zpow_add₀ hz]
    rw [show -(3 * n + 1) + 1 + 3 * n = 0 by ring]
    simp
  have hqpart : q ^ (-(3 * n + 1)) * q * q ^ (4 * n) * q ^ (3 * n ^ 2) =
      q ^ (n * (3 * n + 1)) := by
    nth_rewrite 2 [show q = q ^ (1 : ℤ) by simp]
    rw [← zpow_add₀ hq, ← zpow_add₀ hq, ← zpow_add₀ hq]
    congr 1
    ring
  rw [← zpow_natCast, hidx]
  rw [div_zpow, div_zpow]
  rw [hq4n, hz3n, hq3n2]
  field_simp [hq, hz]
  rw [show q ^ (n * (3 * n + 1)) * z ^ (-(3 * n + 1)) * z * z ^ (3 * n) =
      q ^ (n * (3 * n + 1)) * (z ^ (-(3 * n + 1)) * z * z ^ (3 * n)) by
    ring]
  rw [hzpart]
  rw [hqpart]
  ring

/-- One summand on the RHS of the Eq. (2.12) quintuple product identity. -/
noncomputable def quintupleProductTerm (q z : R) (n : Int) : R :=
  q ^ quintupleQuadraticIndex n *
    (intPow (z / q) (3 * n) - intPow (q / z) (3 * n + 1))

/--
Complex RHS summand in Jacobi-series form:
`(z^3/q^2)^n (q^3)^{n^2} - (q/z) (q^4/z^3)^n (q^3)^{n^2}`.
-/
noncomputable def quintupleProductSeriesTerm (q z : ℂ) (n : ℤ) : ℂ :=
  (z ^ 3 / q ^ 2) ^ n * (q ^ 3) ^ (n ^ 2) -
    (q / z) * ((q ^ 4 / z ^ 3) ^ n * (q ^ 3) ^ (n ^ 2))

/-- Infinite bilateral series side of the quintuple product identity. -/
noncomputable def quintupleProductRHS (q z : ℂ) : ℂ :=
  ∑' n : ℤ, quintupleProductSeriesTerm q z n

/-- The displayed Theorem 4.4-substituted series term is the existing Eq. (2.12) term. -/
theorem theorem44SubstitutedSeriesTerm_eq_quintupleProductSeriesTerm
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (n : ℤ) :
    theorem44SubstitutedSeriesTerm q z n = quintupleProductSeriesTerm q z n := by
  rw [theorem44SubstitutedSeriesTerm, quintupleProductSeriesTerm, mul_sub]
  rw [theorem44SubstitutedSeriesTerm_first_eq q z hq n,
    theorem44SubstitutedSeriesTerm_second_eq q z hq hz n]

/-- The displayed Theorem 4.4-substituted series side is the existing Eq. (2.12) RHS. -/
theorem theorem44SubstitutedSeriesRHS_eq_quintupleProductRHS
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) :
    theorem44SubstitutedSeriesRHS q z = quintupleProductRHS q z := by
  rw [theorem44SubstitutedSeriesRHS, quintupleProductRHS]
  exact tsum_congr fun n =>
    theorem44SubstitutedSeriesTerm_eq_quintupleProductSeriesTerm q z hq hz n

/-- The quintuple product RHS bilateral series is summable for `‖q‖ < 1`. -/
theorem summable_quintupleProductSeriesTerm (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℤ => quintupleProductSeriesTerm q z n := by
  have hq3 : ‖q ^ 3‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have h1 := Ch02.summable_jacobiInfiniteSeries_terms (q ^ 3) (z ^ 3 / q ^ 2) hq3
  have h2 := Ch02.summable_jacobiInfiniteSeries_terms (q ^ 3) (q ^ 4 / z ^ 3) hq3
  simpa [quintupleProductSeriesTerm] using h1.sub (h2.mul_left (q / z))

/-- HasSum form of the quintuple product RHS bilateral series. -/
theorem hasSum_quintupleProductSeriesTerm (q z : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℤ => quintupleProductSeriesTerm q z n) (quintupleProductRHS q z) :=
  (summable_quintupleProductSeriesTerm q z hq).hasSum

/-- The substituted Theorem 4.4 bilateral series is summable via the Eq. (2.12) bridge. -/
theorem summable_theorem44SubstitutedSeriesTerm
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    Summable fun n : ℤ => theorem44SubstitutedSeriesTerm q z n :=
  (summable_quintupleProductSeriesTerm q z hqnorm).congr fun n =>
    (theorem44SubstitutedSeriesTerm_eq_quintupleProductSeriesTerm q z hq hz n).symm

/-- HasSum form of the substituted Theorem 4.4 bilateral series. -/
theorem hasSum_theorem44SubstitutedSeriesTerm
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    HasSum (fun n : ℤ => theorem44SubstitutedSeriesTerm q z n)
      (theorem44SubstitutedSeriesRHS q z) :=
  (summable_theorem44SubstitutedSeriesTerm q z hqnorm hq hz).hasSum

/-- The original Theorem 4.4 terms are summable after the Eq. (2.12) substitution. -/
theorem summable_theorem44SeriesTerm_substitution
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    Summable fun n : ℤ => theorem44SeriesTerm (q ^ 2) (z / q) n :=
  (summable_theorem44SubstitutedSeriesTerm q z hqnorm hq hz).congr fun n =>
    (theorem44SeriesTerm_substitution_eq_substituted q z n).symm

/-- HasSum form of the original Theorem 4.4 series after the Eq. (2.12) substitution. -/
theorem hasSum_theorem44SeriesTerm_substitution
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    HasSum (fun n : ℤ => theorem44SeriesTerm (q ^ 2) (z / q) n)
      (theorem44SeriesRHS (q ^ 2) (z / q)) :=
  (summable_theorem44SeriesTerm_substitution q z hqnorm hq hz).hasSum

/--
The Theorem 4.4 identity after `q ↦ q^2`, `z ↦ z/q` is exactly the
Eq. (2.12) quintuple product identity.
-/
theorem theorem44_substitution_identity_iff_quintupleProduct
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) :
    theorem44ProductLHS (q ^ 2) (z / q) =
        theorem44SeriesRHS (q ^ 2) (z / q) ↔
      quintupleProductLHS q z = quintupleProductRHS q z := by
  rw [theorem44ProductLHS_substitution_eq_quintuple q z hq hz,
    theorem44SeriesRHS_substitution_eq_substituted q z,
    theorem44SubstitutedSeriesRHS_eq_quintupleProductRHS q z hq hz]

/-- Forward transport from Eq. (2.12) to Theorem 4.4 after the standard substitution. -/
theorem theorem44_substitution_identity_of_quintupleProduct
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0)
    (h : quintupleProductLHS q z = quintupleProductRHS q z) :
    theorem44ProductLHS (q ^ 2) (z / q) =
      theorem44SeriesRHS (q ^ 2) (z / q) :=
  (theorem44_substitution_identity_iff_quintupleProduct q z hq hz).mpr h

/-- Reverse transport from the substituted Theorem 4.4 identity to Eq. (2.12). -/
theorem quintupleProduct_of_theorem44_substitution_identity
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0)
    (h : theorem44ProductLHS (q ^ 2) (z / q) =
      theorem44SeriesRHS (q ^ 2) (z / q)) :
    quintupleProductLHS q z = quintupleProductRHS q z :=
  (theorem44_substitution_identity_iff_quintupleProduct q z hq hz).mp h

/-- The quintuple RHS is the difference of two Jacobi bilateral series. -/
theorem quintupleProductRHS_eq_jacobiSeries_sub (q z : ℂ) (hq : ‖q‖ < 1) :
    quintupleProductRHS q z =
      Ch02.jacobiInfiniteSeries (q ^ 3) (z ^ 3 / q ^ 2) -
        (q / z) * Ch02.jacobiInfiniteSeries (q ^ 3) (q ^ 4 / z ^ 3) := by
  have hq3 : ‖q ^ 3‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have h1 := Ch02.summable_jacobiInfiniteSeries_terms (q ^ 3) (z ^ 3 / q ^ 2) hq3
  have h2 := Ch02.summable_jacobiInfiniteSeries_terms (q ^ 3) (q ^ 4 / z ^ 3) hq3
  rw [quintupleProductRHS, Ch02.jacobiInfiniteSeries, Ch02.jacobiInfiniteSeries]
  rw [← h2.tsum_mul_left (q / z)]
  rw [← h1.tsum_sub (h2.mul_left (q / z))]
  exact tsum_congr fun n => by simp [quintupleProductSeriesTerm]

/-- The quintuple RHS after applying Jacobi's triple product to both Jacobi series. -/
theorem quintupleProductRHS_eq_jacobiProduct_sub
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    quintupleProductRHS q z =
      Ch02.jacobiInfiniteProduct (q ^ 3) (z ^ 3 / q ^ 2) -
        (q / z) * Ch02.jacobiInfiniteProduct (q ^ 3) (q ^ 4 / z ^ 3) := by
  have hq3norm : ‖q ^ 3‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hqnorm (by norm_num)
  have hz1 : z ^ 3 / q ^ 2 ≠ 0 :=
    div_ne_zero (pow_ne_zero 3 hz) (pow_ne_zero 2 hq)
  have hz2 : q ^ 4 / z ^ 3 ≠ 0 :=
    div_ne_zero (pow_ne_zero 4 hq) (pow_ne_zero 3 hz)
  rw [quintupleProductRHS_eq_jacobiSeries_sub q z hqnorm]
  rw [← Ch02.jacobiTripleProduct (q ^ 3) (z ^ 3 / q ^ 2) hq3norm hz1]
  rw [← Ch02.jacobiTripleProduct (q ^ 3) (q ^ 4 / z ^ 3) hq3norm hz2]

/-- First Nat-indexed JTP product factor occurring in the quintuple product proof. -/
noncomputable def quintupleJacobiLeftFactor (q z : ℂ) (n : ℕ) : ℂ :=
  (1 - q ^ (6 * n + 6)) *
    (1 + z ^ 3 * q ^ (6 * n + 1)) *
    (1 + (z ^ 3)⁻¹ * q ^ (6 * n + 5))

/-- Second Nat-indexed JTP product factor occurring in the quintuple product proof. -/
noncomputable def quintupleJacobiRightFactor (q z : ℂ) (n : ℕ) : ℂ :=
  (1 - q ^ (6 * n + 6)) *
    (1 + q ^ (6 * n + 7) / z ^ 3) *
    (1 + z ^ 3 * q ^ (6 * n + 3) / q ^ 4)

/-- First product-side JTP factor after the quintuple substitution. -/
theorem jacobiProductNatFactor_quintuple_left_substitution
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (n : ℕ) :
    Ch02.jacobiProductNatFactor (q ^ 3) (z ^ 3 / q ^ 2) n =
      quintupleJacobiLeftFactor q z n := by
  simp [quintupleJacobiLeftFactor, Ch02.jacobiProductNatFactor,
    Ch02.jacobiProductEvenFactor, Ch02.jacobiProductOddFactor]
  have heven : (q ^ 3) ^ (2 * (n + 1)) = q ^ (6 * n + 6) := by
    rw [← pow_mul]
    congr 1
    omega
  have hodd1 : z ^ 3 / q ^ 2 * (q ^ 3) ^ (2 * (n + 1) - 1) =
      z ^ 3 * q ^ (6 * n + 1) := by
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
    rw [← pow_mul]
    rw [show 3 * (2 * n + 1) = 6 * n + 3 by omega]
    field_simp [hq]
    rw [show 6 * n + 3 = (6 * n + 1) + 2 by omega]
    rw [pow_add]
    ring
  have hodd2 : q ^ 2 / z ^ 3 * (q ^ 3) ^ (2 * (n + 1) - 1) =
      (z ^ 3)⁻¹ * q ^ (6 * n + 5) := by
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
    rw [← pow_mul]
    rw [show 3 * (2 * n + 1) = 6 * n + 3 by omega]
    field_simp [hz]
    rw [show 6 * n + 5 = 2 + (6 * n + 3) by omega]
    rw [pow_add]
    ring
  rw [heven, hodd1, hodd2]

/-- Second product-side JTP factor after the quintuple substitution. -/
theorem jacobiProductNatFactor_quintuple_right_substitution (q z : ℂ) (n : ℕ) :
    Ch02.jacobiProductNatFactor (q ^ 3) (q ^ 4 / z ^ 3) n =
      quintupleJacobiRightFactor q z n := by
  simp [quintupleJacobiRightFactor, Ch02.jacobiProductNatFactor,
    Ch02.jacobiProductEvenFactor, Ch02.jacobiProductOddFactor]
  have heven : (q ^ 3) ^ (2 * (n + 1)) = q ^ (6 * n + 6) := by
    rw [← pow_mul]
    congr 1
    omega
  have hodd1 : q ^ 4 / z ^ 3 * (q ^ 3) ^ (2 * (n + 1) - 1) =
      q ^ (6 * n + 7) / z ^ 3 := by
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
    rw [← pow_mul]
    rw [show 3 * (2 * n + 1) = 6 * n + 3 by omega]
    rw [show 6 * n + 7 = 4 + (6 * n + 3) by omega]
    rw [pow_add]
    ring
  have hodd2 : z ^ 3 / q ^ 4 * (q ^ 3) ^ (2 * (n + 1) - 1) =
      z ^ 3 * q ^ (6 * n + 3) / q ^ 4 := by
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
    rw [← pow_mul]
    rw [show 3 * (2 * n + 1) = 6 * n + 3 by omega]
    ring
  rw [heven, hodd1, hodd2]

/-- The explicit product-difference side obtained by applying JTP to the quintuple RHS. -/
noncomputable def quintupleProductExplicitRHS (q z : ℂ) : ℂ :=
  (∏' n : ℕ, quintupleJacobiLeftFactor q z n) -
    (q / z) * (∏' n : ℕ, quintupleJacobiRightFactor q z n)

/-- The quintuple RHS as a difference of two explicit Nat-indexed JTP products. -/
theorem quintupleProductRHS_eq_explicitProduct_sub
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    quintupleProductRHS q z =
      quintupleProductExplicitRHS q z := by
  rw [quintupleProductRHS_eq_jacobiProduct_sub q z hqnorm hq hz]
  rw [Ch02.jacobiInfiniteProduct_eq_tprod_natFactor]
  rw [Ch02.jacobiInfiniteProduct_eq_tprod_natFactor]
  rw [tprod_congr fun n =>
    jacobiProductNatFactor_quintuple_left_substitution q z hq hz n]
  rw [tprod_congr fun n =>
    jacobiProductNatFactor_quintuple_right_substitution q z n]
  rfl

/-- The remaining Eq. (2.12) product algebra is equivalent to the full quintuple identity. -/
theorem quintupleProduct_identity_iff_explicitProduct
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    quintupleProductLHS q z = quintupleProductRHS q z ↔
      quintupleProductLHS q z = quintupleProductExplicitRHS q z := by
  rw [quintupleProductRHS_eq_explicitProduct_sub q z hqnorm hq hz]

/-- Forward transport from the explicit product algebra to the full quintuple identity. -/
theorem quintupleProduct_identity_of_explicitProduct
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0)
    (h : quintupleProductLHS q z = quintupleProductExplicitRHS q z) :
    quintupleProductLHS q z = quintupleProductRHS q z :=
  (quintupleProduct_identity_iff_explicitProduct q z hqnorm hq hz).mpr h

/-- Reverse transport from the full quintuple identity to the explicit product algebra. -/
theorem quintupleProduct_explicitProduct_of_identity
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0)
    (h : quintupleProductLHS q z = quintupleProductRHS q z) :
    quintupleProductLHS q z = quintupleProductExplicitRHS q z :=
  (quintupleProduct_identity_iff_explicitProduct q z hqnorm hq hz).mp h

/-- Finite partial product of the first explicit JTP factor family. -/
noncomputable def quintupleJacobiLeftPartial (q z : ℂ) (N : ℕ) : ℂ :=
  ∏ n ∈ Finset.range N, quintupleJacobiLeftFactor q z n

/-- Finite partial product of the second explicit JTP factor family. -/
noncomputable def quintupleJacobiRightPartial (q z : ℂ) (N : ℕ) : ℂ :=
  ∏ n ∈ Finset.range N, quintupleJacobiRightFactor q z n

/-- Finite product-difference partials for the explicit product RHS bottleneck. -/
noncomputable def quintupleProductExplicitRHSPartial (q z : ℂ) (N : ℕ) : ℂ :=
  quintupleJacobiLeftPartial q z N - (q / z) * quintupleJacobiRightPartial q z N

/-- Finite product-side JTP partial after the first quintuple substitution. -/
theorem jacobiProductPartial_quintuple_left_substitution
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : ℕ) :
    Ch02.jacobiProductPartial (q ^ 3) (z ^ 3 / q ^ 2) N =
      quintupleJacobiLeftPartial q z N := by
  simp only [Ch02.jacobiProductPartial, quintupleJacobiLeftPartial]
  exact Finset.prod_congr rfl fun n _ =>
    jacobiProductNatFactor_quintuple_left_substitution q z hq hz n

/-- Finite product-side JTP partial after the second quintuple substitution. -/
theorem jacobiProductPartial_quintuple_right_substitution (q z : ℂ) (N : ℕ) :
    Ch02.jacobiProductPartial (q ^ 3) (q ^ 4 / z ^ 3) N =
      quintupleJacobiRightPartial q z N := by
  simp only [Ch02.jacobiProductPartial, quintupleJacobiRightPartial]
  exact Finset.prod_congr rfl fun n _ =>
    jacobiProductNatFactor_quintuple_right_substitution q z n

/-- The explicit RHS finite partial as a difference of two Ch02 JTP product partials. -/
theorem quintupleProductExplicitRHSPartial_eq_jacobiProductPartial_sub
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : ℕ) :
    quintupleProductExplicitRHSPartial q z N =
      Ch02.jacobiProductPartial (q ^ 3) (z ^ 3 / q ^ 2) N -
        (q / z) * Ch02.jacobiProductPartial (q ^ 3) (q ^ 4 / z ^ 3) N := by
  rw [quintupleProductExplicitRHSPartial,
    ← jacobiProductPartial_quintuple_left_substitution q z hq hz N,
    ← jacobiProductPartial_quintuple_right_substitution q z N]

/-- The remaining finite difference expressed in Ch02 JTP product partials. -/
theorem quintupleProduct_trunc_sub_explicitPartial_eq_jacobiProductPartial_sub
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : ℕ) :
    quintupleProductLHSTrunc q z N - quintupleProductExplicitRHSPartial q z N =
      quintupleProductLHSTrunc q z N -
        (Ch02.jacobiProductPartial (q ^ 3) (z ^ 3 / q ^ 2) N -
          (q / z) * Ch02.jacobiProductPartial (q ^ 3) (q ^ 4 / z ^ 3) N) := by
  rw [quintupleProductExplicitRHSPartial_eq_jacobiProductPartial_sub q z hq hz N]

/--
Weighted Laurent finite sum obtained by expanding the first finite JTP sum in
the explicit quintuple RHS partial.
-/
noncomputable def quintupleFiniteJTPLeftWeightedSummand (q z : ℂ) (N k : ℕ) : ℂ :=
  gaussianBinom (q ^ 6) (2 * N) k *
    (z ^ 3 / q ^ 2) ^ ((k : Int) - (N : Int)) *
      (q ^ 3) ^ (((k : Int) - (N : Int)) ^ 2)

/--
Weighted Laurent finite sum obtained by expanding the second finite JTP sum in
the explicit quintuple RHS partial.
-/
noncomputable def quintupleFiniteJTPRightWeightedSummand (q z : ℂ) (N k : ℕ) : ℂ :=
  gaussianBinom (q ^ 6) (2 * N) k *
    (q ^ 4 / z ^ 3) ^ ((k : Int) - (N : Int)) *
      (q ^ 3) ^ (((k : Int) - (N : Int)) ^ 2)

/-- Combined summand for the weighted Laurent difference in the explicit RHS partial. -/
noncomputable def quintupleFiniteJTPCombinedWeightedSummand (q z : ℂ) (N k : ℕ) : ℂ :=
  quintupleFiniteJTPLeftWeightedSummand q z N k -
    (q / z) * quintupleFiniteJTPRightWeightedSummand q z N k

/-- First weighted Laurent finite sum in the explicit quintuple RHS partial. -/
noncomputable def quintupleFiniteJTPLeftWeightedSum (q z : ℂ) (N : ℕ) : ℂ :=
  natSum (quintupleFiniteJTPLeftWeightedSummand q z N) (2 * N)

/-- Second weighted Laurent finite sum in the explicit quintuple RHS partial. -/
noncomputable def quintupleFiniteJTPRightWeightedSum (q z : ℂ) (N : ℕ) : ℂ :=
  natSum (quintupleFiniteJTPRightWeightedSummand q z N) (2 * N)

/-- Combined weighted Laurent finite sum in the explicit quintuple RHS partial. -/
noncomputable def quintupleFiniteJTPCombinedWeightedSum (q z : ℂ) (N : ℕ) : ℂ :=
  natSum (quintupleFiniteJTPCombinedWeightedSummand q z N) (2 * N)

/-- Combined weighted summand after splitting the Laurent monomials into `z` and `q` powers. -/
noncomputable def quintupleFiniteJTPCombinedMonomialSummand (q z : ℂ) (N k : ℕ) : ℂ :=
  let l : Int := (k : Int) - (N : Int)
  gaussianBinom (q ^ 6) (2 * N) k *
    (z ^ (3 * l) * q ^ (3 * l ^ 2 - 2 * l) -
      z ^ (-(3 * l) - 1) * q ^ (3 * l ^ 2 + 4 * l + 1))

/-- Combined weighted Laurent finite sum in monomial-split form. -/
noncomputable def quintupleFiniteJTPCombinedMonomialSum (q z : ℂ) (N : ℕ) : ℂ :=
  natSum (quintupleFiniteJTPCombinedMonomialSummand q z N) (2 * N)

/-- The first weighted Laurent monomial split into separate `z` and `q` powers. -/
theorem quintupleFiniteJTPLeftMonomial_eq_zpow_qpow
    (q z : ℂ) (hq : q ≠ 0) (l : Int) :
    (z ^ 3 / q ^ 2) ^ l * (q ^ 3) ^ (l ^ 2) =
      z ^ (3 * l) * q ^ (3 * l ^ 2 - 2 * l) := by
  rw [div_zpow]
  change (z ^ (3 : ℤ)) ^ l / (q ^ (2 : ℤ)) ^ l * (q ^ (3 : ℤ)) ^ (l ^ 2) =
      z ^ (3 * l) * q ^ (3 * l ^ 2 - 2 * l)
  rw [← zpow_mul, ← zpow_mul, ← zpow_mul]
  rw [div_eq_mul_inv]
  rw [← zpow_neg]
  rw [show z ^ (3 * l) * q ^ (-(2 * l)) * q ^ (3 * l ^ 2) =
      z ^ (3 * l) * (q ^ (-(2 * l)) * q ^ (3 * l ^ 2)) by ring_nf]
  rw [← (zpow_add₀ hq (-(2 * l)) (3 * l ^ 2))]
  congr 1
  ring_nf

/-- The scaled second weighted Laurent monomial split into separate `z` and `q` powers. -/
theorem quintupleFiniteJTPRightScaledMonomial_eq_zpow_qpow
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (l : Int) :
    (q / z) * ((q ^ 4 / z ^ 3) ^ l * (q ^ 3) ^ (l ^ 2)) =
      z ^ (-(3 * l) - 1) * q ^ (3 * l ^ 2 + 4 * l + 1) := by
  rw [div_zpow]
  change q / z * ((q ^ (4 : ℤ)) ^ l / (z ^ (3 : ℤ)) ^ l *
      (q ^ (3 : ℤ)) ^ (l ^ 2)) =
      z ^ (-(3 * l) - 1) * q ^ (3 * l ^ 2 + 4 * l + 1)
  rw [← zpow_mul, ← zpow_mul, ← zpow_mul]
  rw [div_eq_mul_inv]
  rw [div_eq_mul_inv]
  rw [← zpow_neg]
  rw [← zpow_neg_one z]
  rw [show q * z ^ (-1 : ℤ) * (q ^ (4 * l) * z ^ (-(3 * l)) * q ^ (3 * l ^ 2)) =
      (z ^ (-(3 * l)) * z ^ (-1 : ℤ)) *
        ((q ^ (4 * l) * q ^ (3 * l ^ 2)) * q) by ring_nf]
  rw [← (zpow_add₀ hz (-(3 * l)) (-1))]
  rw [← (zpow_add₀ hq (4 * l) (3 * l ^ 2))]
  rw [show q ^ (4 * l + 3 * l ^ 2) * q =
      q ^ (4 * l + 3 * l ^ 2) * q ^ (1 : Int) by simp]
  rw [← (zpow_add₀ hq (4 * l + 3 * l ^ 2) 1)]
  congr 1
  all_goals ring_nf

/-- The quintuple RHS series term in monomial-split form. -/
theorem quintupleProductSeriesTerm_eq_combinedMonomialBracket
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (l : Int) :
    quintupleProductSeriesTerm q z l =
      z ^ (3 * l) * q ^ (3 * l ^ 2 - 2 * l) -
        z ^ (-(3 * l) - 1) * q ^ (3 * l ^ 2 + 4 * l + 1) := by
  rw [quintupleProductSeriesTerm]
  rw [quintupleFiniteJTPLeftMonomial_eq_zpow_qpow q z hq l,
    quintupleFiniteJTPRightScaledMonomial_eq_zpow_qpow q z hq hz l]

/-- The monomial-split combined finite summand is a Gaussian coefficient times the RHS term. -/
theorem quintupleFiniteJTPCombinedMonomialSummand_eq_gaussian_mul_seriesTerm
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N k : ℕ) :
    quintupleFiniteJTPCombinedMonomialSummand q z N k =
      gaussianBinom (q ^ 6) (2 * N) k *
        quintupleProductSeriesTerm q z ((k : Int) - (N : Int)) := by
  unfold quintupleFiniteJTPCombinedMonomialSummand
  rw [quintupleProductSeriesTerm_eq_combinedMonomialBracket q z hq hz]

/--
For fixed nonnegative offset `r`, the centered positive monomial-split summand
has the expected bilateral-series limit after multiplying by `(q^6;q^6)_N`.
-/
theorem tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialSummand_center_add
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) (r : ℕ) :
    Tendsto
      (fun N : ℕ =>
        qPoch (q ^ 6) (q ^ 6) N *
          quintupleFiniteJTPCombinedMonomialSummand q z N (N + r))
      atTop (𝓝 (quintupleProductSeriesTerm q z (r : Int))) := by
  have hq3norm : ‖q ^ 3‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hqnorm (by norm_num)
  have hbase : (q ^ 3) ^ 2 = q ^ 6 := by ring
  have hcoef :
      Tendsto
        (fun N : ℕ =>
          qPoch (q ^ 6) (q ^ 6) N * gaussianBinom (q ^ 6) (2 * N) (N + r))
        atTop (𝓝 1) := by
    simpa [hbase] using Ch03.tendsto_qPoch_mul_gaussian_center_add (q ^ 3) hq3norm r
  have hterm := hcoef.mul_const (quintupleProductSeriesTerm q z (r : Int))
  have heq :
      (fun N : ℕ =>
        qPoch (q ^ 6) (q ^ 6) N * gaussianBinom (q ^ 6) (2 * N) (N + r) *
          quintupleProductSeriesTerm q z (r : Int)) =ᶠ[atTop]
        (fun N : ℕ =>
          qPoch (q ^ 6) (q ^ 6) N *
            quintupleFiniteJTPCombinedMonomialSummand q z N (N + r)) := by
    exact Eventually.of_forall fun N => by
      change
        qPoch (q ^ 6) (q ^ 6) N * gaussianBinom (q ^ 6) (2 * N) (N + r) *
            quintupleProductSeriesTerm q z (r : Int) =
          qPoch (q ^ 6) (q ^ 6) N *
            quintupleFiniteJTPCombinedMonomialSummand q z N (N + r)
      rw [quintupleFiniteJTPCombinedMonomialSummand_eq_gaussian_mul_seriesTerm q z hq hz]
      have hoff : ((N + r : ℕ) : Int) - (N : Int) = (r : Int) := by omega
      rw [hoff]
      ring
  simpa using hterm.congr' heq

/--
For fixed nonnegative offset `r`, the centered negative monomial-split summand
has the expected bilateral-series limit after multiplying by `(q^6;q^6)_N`.
-/
theorem tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialSummand_center_sub
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) (r : ℕ) :
    Tendsto
      (fun N : ℕ =>
        qPoch (q ^ 6) (q ^ 6) N *
          quintupleFiniteJTPCombinedMonomialSummand q z N (N - r))
      atTop (𝓝 (quintupleProductSeriesTerm q z (-(r : Int)))) := by
  have hq3norm : ‖q ^ 3‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hqnorm (by norm_num)
  have hbase : (q ^ 3) ^ 2 = q ^ 6 := by ring
  have hcoef :
      Tendsto
        (fun N : ℕ =>
          qPoch (q ^ 6) (q ^ 6) N * gaussianBinom (q ^ 6) (2 * N) (N - r))
        atTop (𝓝 1) := by
    simpa [hbase] using Ch03.tendsto_qPoch_mul_gaussian_center_sub (q ^ 3) hq3norm r
  have hterm := hcoef.mul_const (quintupleProductSeriesTerm q z (-(r : Int)))
  have heq :
      (fun N : ℕ =>
        qPoch (q ^ 6) (q ^ 6) N * gaussianBinom (q ^ 6) (2 * N) (N - r) *
          quintupleProductSeriesTerm q z (-(r : Int))) =ᶠ[atTop]
        (fun N : ℕ =>
          qPoch (q ^ 6) (q ^ 6) N *
            quintupleFiniteJTPCombinedMonomialSummand q z N (N - r)) := by
    filter_upwards [eventually_ge_atTop r] with N hN
    rw [quintupleFiniteJTPCombinedMonomialSummand_eq_gaussian_mul_seriesTerm q z hq hz]
    have hoff : ((N - r : ℕ) : Int) - (N : Int) = -(r : Int) := by omega
    rw [hoff]
    ring
  simpa using hterm.congr' heq

/-- Symmetric nonzero pair term in the quintuple RHS bilateral series. -/
noncomputable def quintupleProductSeriesSymmetricPairTerm (q z : ℂ) (r : ℕ) : ℂ :=
  quintupleProductSeriesTerm q z (-(((r + 1 : ℕ) : Int))) +
    quintupleProductSeriesTerm q z (((r + 1 : ℕ) : Int))

/-- Fixed symmetric nonzero pair partial in the quintuple RHS bilateral series. -/
noncomputable def quintupleProductSeriesSymmetricPairPartial
    (q z : ℂ) (M : ℕ) : ℂ :=
  ∑ r ∈ Finset.range M, quintupleProductSeriesSymmetricPairTerm q z r

/-- Fixed symmetric partial in the quintuple RHS bilateral series. -/
noncomputable def quintupleProductSeriesSymmetricPartial (q z : ℂ) (M : ℕ) : ℂ :=
  quintupleProductSeriesTerm q z 0 + quintupleProductSeriesSymmetricPairPartial q z M

/-- Finite Gaussian-weighted symmetric nonzero pair in the monomial-split combined sum. -/
noncomputable def quintupleFiniteJTPCombinedMonomialPairTerm
    (q z : ℂ) (N r : ℕ) : ℂ :=
  quintupleFiniteJTPCombinedMonomialSummand q z N (N - (r + 1)) +
    quintupleFiniteJTPCombinedMonomialSummand q z N (N + (r + 1))

/-- Fixed finite Gaussian-weighted symmetric nonzero pair partial. -/
noncomputable def quintupleFiniteJTPCombinedMonomialPairPartial
    (q z : ℂ) (N M : ℕ) : ℂ :=
  ∑ r ∈ Finset.range M, quintupleFiniteJTPCombinedMonomialPairTerm q z N r

/-- Fixed finite Gaussian-weighted symmetric partial including the center term. -/
noncomputable def quintupleFiniteJTPCombinedMonomialSymmetricPartial
    (q z : ℂ) (N M : ℕ) : ℂ :=
  quintupleFiniteJTPCombinedMonomialSummand q z N N +
    quintupleFiniteJTPCombinedMonomialPairPartial q z N M

/-- A fixed finite monomial pair tends to the corresponding bilateral RHS pair. -/
theorem tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialPairTerm
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) (r : ℕ) :
    Tendsto
      (fun N : ℕ =>
        qPoch (q ^ 6) (q ^ 6) N *
          quintupleFiniteJTPCombinedMonomialPairTerm q z N r)
      atTop (𝓝 (quintupleProductSeriesSymmetricPairTerm q z r)) := by
  have hneg :=
    tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialSummand_center_sub
      q z hqnorm hq hz (r + 1)
  have hpos :=
    tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialSummand_center_add
      q z hqnorm hq hz (r + 1)
  convert hneg.add hpos using 1
  · ext N
    rw [quintupleFiniteJTPCombinedMonomialPairTerm]
    ring

/-- Fixed monomial pair partials converge to the corresponding bilateral RHS pair partial. -/
theorem tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialPairPartial
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) (M : ℕ) :
    Tendsto
      (fun N : ℕ =>
        qPoch (q ^ 6) (q ^ 6) N *
          quintupleFiniteJTPCombinedMonomialPairPartial q z N M)
      atTop (𝓝 (quintupleProductSeriesSymmetricPairPartial q z M)) := by
  simpa [quintupleFiniteJTPCombinedMonomialPairPartial,
    quintupleProductSeriesSymmetricPairPartial, Finset.mul_sum]
    using tendsto_finset_sum (Finset.range M)
      (fun r _ =>
        tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialPairTerm q z hqnorm hq hz r)

/--
Fixed monomial symmetric partials converge to the corresponding bilateral RHS
symmetric partial.
-/
theorem tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialSymmetricPartial
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) (M : ℕ) :
    Tendsto
      (fun N : ℕ =>
        qPoch (q ^ 6) (q ^ 6) N *
          quintupleFiniteJTPCombinedMonomialSymmetricPartial q z N M)
      atTop (𝓝 (quintupleProductSeriesSymmetricPartial q z M)) := by
  have hcenter :=
    tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialSummand_center_add
      q z hqnorm hq hz 0
  have hpairs :=
    tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialPairPartial
      q z hqnorm hq hz M
  convert hcenter.add hpairs using 1
  · ext N
    rw [quintupleFiniteJTPCombinedMonomialSymmetricPartial]
    ring_nf

/-- The weighted Laurent difference combines into a single inclusive `natSum`. -/
theorem quintupleFiniteJTPWeightedSum_sub_eq_combined
    (q z : ℂ) (N : ℕ) :
    quintupleFiniteJTPLeftWeightedSum q z N -
        (q / z) * quintupleFiniteJTPRightWeightedSum q z N =
      quintupleFiniteJTPCombinedWeightedSum q z N := by
  rw [quintupleFiniteJTPLeftWeightedSum, quintupleFiniteJTPRightWeightedSum,
    quintupleFiniteJTPCombinedWeightedSum]
  induction 2 * N with
  | zero =>
      simp [quintupleFiniteJTPCombinedWeightedSummand]
  | succ M ih =>
      rw [natSum_succ, natSum_succ, natSum_succ, ← ih]
      simp [quintupleFiniteJTPCombinedWeightedSummand]
      ring_nf

/-- The combined weighted Laurent summand equals the monomial-split summand. -/
theorem quintupleFiniteJTPCombinedWeightedSummand_eq_monomialSummand
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N k : ℕ) :
    quintupleFiniteJTPCombinedWeightedSummand q z N k =
      quintupleFiniteJTPCombinedMonomialSummand q z N k := by
  unfold quintupleFiniteJTPCombinedWeightedSummand
    quintupleFiniteJTPLeftWeightedSummand quintupleFiniteJTPRightWeightedSummand
    quintupleFiniteJTPCombinedMonomialSummand
  set l : Int := (k : Int) - (N : Int)
  have hleft := quintupleFiniteJTPLeftMonomial_eq_zpow_qpow q z hq l
  have hright := quintupleFiniteJTPRightScaledMonomial_eq_zpow_qpow q z hq hz l
  calc
    gaussianBinom (q ^ 6) (2 * N) k * (z ^ 3 / q ^ 2) ^ l * (q ^ 3) ^ l ^ 2 -
        q / z * (gaussianBinom (q ^ 6) (2 * N) k * (q ^ 4 / z ^ 3) ^ l *
          (q ^ 3) ^ l ^ 2) =
      gaussianBinom (q ^ 6) (2 * N) k * ((z ^ 3 / q ^ 2) ^ l * (q ^ 3) ^ l ^ 2) -
        gaussianBinom (q ^ 6) (2 * N) k *
          ((q / z) * ((q ^ 4 / z ^ 3) ^ l * (q ^ 3) ^ l ^ 2)) := by ring
    _ = gaussianBinom (q ^ 6) (2 * N) k *
        (z ^ (3 * l) * q ^ (3 * l ^ 2 - 2 * l)) -
        gaussianBinom (q ^ 6) (2 * N) k *
          (z ^ (-(3 * l) - 1) * q ^ (3 * l ^ 2 + 4 * l + 1)) := by
      rw [hleft, hright]
    _ = gaussianBinom (q ^ 6) (2 * N) k *
        (z ^ (3 * l) * q ^ (3 * l ^ 2 - 2 * l) -
          z ^ (-(3 * l) - 1) * q ^ (3 * l ^ 2 + 4 * l + 1)) := by ring

/-- The combined weighted Laurent sum equals its monomial-split form. -/
theorem quintupleFiniteJTPCombinedWeightedSum_eq_monomialSum
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : ℕ) :
    quintupleFiniteJTPCombinedWeightedSum q z N =
      quintupleFiniteJTPCombinedMonomialSum q z N := by
  unfold quintupleFiniteJTPCombinedWeightedSum quintupleFiniteJTPCombinedMonomialSum
  exact Ch03.natSum_congr_le (2 * N) fun k _ =>
    quintupleFiniteJTPCombinedWeightedSummand_eq_monomialSummand q z hq hz N k

/-- First finite-JTP sum expanded as a weighted Laurent finite sum. -/
theorem finiteJTPRHS_quintuple_left_eq_weightedSum
    (q z : ℂ) (hq : q ≠ 0) (N : ℕ) :
    finiteJTPRHS (q ^ 6) (-(z ^ 3 * q)) N =
      quintupleFiniteJTPLeftWeightedSum q z N := by
  have hq3 : q ^ 3 ≠ 0 := pow_ne_zero 3 hq
  have hbase : (q ^ 3) ^ 2 = q ^ 6 := by ring
  have harg : -((z ^ 3 / q ^ 2) * q ^ 3) = -(z ^ 3 * q) := by
    field_simp [hq]
  have h := Ch03.finiteJTPRHS_qsq_neg_zq (q ^ 3) (z ^ 3 / q ^ 2) hq3 N
  rw [hbase] at h
  rw [harg] at h
  exact h

/-- Second finite-JTP sum expanded as a weighted Laurent finite sum. -/
theorem finiteJTPRHS_quintuple_right_eq_weightedSum
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : ℕ) :
    finiteJTPRHS (q ^ 6) (-(q ^ 7 / z ^ 3)) N =
      quintupleFiniteJTPRightWeightedSum q z N := by
  have hq3 : q ^ 3 ≠ 0 := pow_ne_zero 3 hq
  have hbase : (q ^ 3) ^ 2 = q ^ 6 := by ring
  have harg : -((q ^ 4 / z ^ 3) * q ^ 3) = -(q ^ 7 / z ^ 3) := by
    field_simp [hz]
  have h := Ch03.finiteJTPRHS_qsq_neg_zq (q ^ 3) (q ^ 4 / z ^ 3) hq3 N
  rw [hbase] at h
  rw [harg] at h
  exact h

/--
The explicit RHS finite partial expanded by finite JTP into a common
`(q^6;q^6)_N` factor times two finite-JTP sums.
-/
theorem quintupleProductExplicitRHSPartial_eq_qPoch_mul_finiteJTPRHS_sub
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : ℕ) :
    quintupleProductExplicitRHSPartial q z N =
      qPoch (q ^ 6) (q ^ 6) N * finiteJTPRHS (q ^ 6) (-(z ^ 3 * q)) N -
        (q / z) * (qPoch (q ^ 6) (q ^ 6) N *
          finiteJTPRHS (q ^ 6) (-(q ^ 7 / z ^ 3)) N) := by
  have hq3 : q ^ 3 ≠ 0 := pow_ne_zero 3 hq
  have hzleft : z ^ 3 / q ^ 2 ≠ 0 :=
    div_ne_zero (pow_ne_zero 3 hz) (pow_ne_zero 2 hq)
  have hzright : q ^ 4 / z ^ 3 ≠ 0 :=
    div_ne_zero (pow_ne_zero 4 hq) (pow_ne_zero 3 hz)
  rw [quintupleProductExplicitRHSPartial_eq_jacobiProductPartial_sub q z hq hz N]
  rw [Ch03.jacobiProductPartial_eq_qPoch_mul_finiteJTPRHS (q ^ 3) (z ^ 3 / q ^ 2)
    hq3 hzleft N]
  rw [Ch03.jacobiProductPartial_eq_qPoch_mul_finiteJTPRHS (q ^ 3) (q ^ 4 / z ^ 3)
    hq3 hzright N]
  have hq6 : (q ^ 3) ^ 2 = q ^ 6 := by ring
  have hleftArg : -((z ^ 3 / q ^ 2) * q ^ 3) = -(z ^ 3 * q) := by
    field_simp [hq]
  have hrightArg : -((q ^ 4 / z ^ 3) * q ^ 3) = -(q ^ 7 / z ^ 3) := by
    field_simp [hz]
  rw [hq6, hleftArg, hrightArg]

/-- The explicit RHS finite partial expanded into two weighted Laurent finite sums. -/
theorem quintupleProductExplicitRHSPartial_eq_qPoch_mul_weightedSums_sub
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : ℕ) :
    quintupleProductExplicitRHSPartial q z N =
      qPoch (q ^ 6) (q ^ 6) N * quintupleFiniteJTPLeftWeightedSum q z N -
        (q / z) * (qPoch (q ^ 6) (q ^ 6) N *
          quintupleFiniteJTPRightWeightedSum q z N) := by
  rw [quintupleProductExplicitRHSPartial_eq_qPoch_mul_finiteJTPRHS_sub q z hq hz N]
  rw [finiteJTPRHS_quintuple_left_eq_weightedSum q z hq N,
    finiteJTPRHS_quintuple_right_eq_weightedSum q z hq hz N]

/-- The explicit RHS finite partial as one q-Pochhammer factor times one weighted sum. -/
theorem quintupleProductExplicitRHSPartial_eq_qPoch_mul_combinedWeightedSum
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : ℕ) :
    quintupleProductExplicitRHSPartial q z N =
      qPoch (q ^ 6) (q ^ 6) N *
        quintupleFiniteJTPCombinedWeightedSum q z N := by
  rw [quintupleProductExplicitRHSPartial_eq_qPoch_mul_weightedSums_sub q z hq hz N]
  rw [← quintupleFiniteJTPWeightedSum_sub_eq_combined q z N]
  ring

/-- The explicit RHS finite partial in monomial-split combined-sum form. -/
theorem quintupleProductExplicitRHSPartial_eq_qPoch_mul_combinedMonomialSum
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : ℕ) :
    quintupleProductExplicitRHSPartial q z N =
      qPoch (q ^ 6) (q ^ 6) N *
        quintupleFiniteJTPCombinedMonomialSum q z N := by
  rw [quintupleProductExplicitRHSPartial_eq_qPoch_mul_combinedWeightedSum q z hq hz N]
  rw [quintupleFiniteJTPCombinedWeightedSum_eq_monomialSum q z hq hz N]

/--
The finite difference bottleneck written entirely in finite q-Pochhammer
factors and finite-JTP sums.
-/
theorem quintupleProduct_trunc_sub_explicitPartial_eq_qPoch_finiteJTPRHS
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : ℕ) :
    quintupleProductLHSTrunc q z N - quintupleProductExplicitRHSPartial q z N =
      (qPoch (q ^ 2) (q ^ 2) N * qPoch (z * q) (q ^ 2) N *
          qPoch (q / z) (q ^ 2) N * qPoch (z ^ 2) (q ^ 4) N *
            qPoch (q ^ 4 / z ^ 2) (q ^ 4) N) -
        (qPoch (q ^ 6) (q ^ 6) N * finiteJTPRHS (q ^ 6) (-(z ^ 3 * q)) N -
          (q / z) * (qPoch (q ^ 6) (q ^ 6) N *
            finiteJTPRHS (q ^ 6) (-(q ^ 7 / z ^ 3)) N)) := by
  rw [quintupleProductLHSTrunc_eq_qPoch q z hq hz N]
  rw [quintupleProductExplicitRHSPartial_eq_qPoch_mul_finiteJTPRHS_sub q z hq hz N]

/--
The finite difference bottleneck after expanding the two finite-JTP sums into
weighted Laurent finite sums.
-/
theorem quintupleProduct_trunc_sub_explicitPartial_eq_qPoch_weightedSums
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : ℕ) :
    quintupleProductLHSTrunc q z N - quintupleProductExplicitRHSPartial q z N =
      (qPoch (q ^ 2) (q ^ 2) N * qPoch (z * q) (q ^ 2) N *
          qPoch (q / z) (q ^ 2) N * qPoch (z ^ 2) (q ^ 4) N *
            qPoch (q ^ 4 / z ^ 2) (q ^ 4) N) -
        (qPoch (q ^ 6) (q ^ 6) N * quintupleFiniteJTPLeftWeightedSum q z N -
          (q / z) * (qPoch (q ^ 6) (q ^ 6) N *
            quintupleFiniteJTPRightWeightedSum q z N)) := by
  rw [quintupleProductLHSTrunc_eq_qPoch q z hq hz N]
  rw [quintupleProductExplicitRHSPartial_eq_qPoch_mul_weightedSums_sub q z hq hz N]

/--
The finite difference bottleneck with the RHS as one finite q-Pochhammer
factor times one combined weighted Laurent sum.
-/
theorem quintupleProduct_trunc_sub_explicitPartial_eq_qPoch_combinedWeightedSum
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : ℕ) :
    quintupleProductLHSTrunc q z N - quintupleProductExplicitRHSPartial q z N =
      (qPoch (q ^ 2) (q ^ 2) N * qPoch (z * q) (q ^ 2) N *
          qPoch (q / z) (q ^ 2) N * qPoch (z ^ 2) (q ^ 4) N *
            qPoch (q ^ 4 / z ^ 2) (q ^ 4) N) -
        qPoch (q ^ 6) (q ^ 6) N *
          quintupleFiniteJTPCombinedWeightedSum q z N := by
  rw [quintupleProductLHSTrunc_eq_qPoch q z hq hz N]
  rw [quintupleProductExplicitRHSPartial_eq_qPoch_mul_combinedWeightedSum q z hq hz N]

/--
The finite difference bottleneck with the RHS in monomial-split combined-sum
form.
-/
theorem quintupleProduct_trunc_sub_explicitPartial_eq_qPoch_combinedMonomialSum
    (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (N : ℕ) :
    quintupleProductLHSTrunc q z N - quintupleProductExplicitRHSPartial q z N =
      (qPoch (q ^ 2) (q ^ 2) N * qPoch (z * q) (q ^ 2) N *
          qPoch (q / z) (q ^ 2) N * qPoch (z ^ 2) (q ^ 4) N *
            qPoch (q ^ 4 / z ^ 2) (q ^ 4) N) -
        qPoch (q ^ 6) (q ^ 6) N *
          quintupleFiniteJTPCombinedMonomialSum q z N := by
  rw [quintupleProductLHSTrunc_eq_qPoch q z hq hz N]
  rw [quintupleProductExplicitRHSPartial_eq_qPoch_mul_combinedMonomialSum q z hq hz N]

/-- The first explicit JTP factor family is multipliable. -/
theorem multipliable_quintupleJacobiLeftFactor
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    Multipliable fun n : ℕ => quintupleJacobiLeftFactor q z n := by
  have hq3norm : ‖q ^ 3‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hqnorm (by norm_num)
  exact (Ch02.multipliable_jacobiProductNatFactor (q ^ 3) (z ^ 3 / q ^ 2) hq3norm).congr
    fun n => jacobiProductNatFactor_quintuple_left_substitution q z hq hz n

/-- The second explicit JTP factor family is multipliable. -/
theorem multipliable_quintupleJacobiRightFactor (q z : ℂ) (hqnorm : ‖q‖ < 1) :
    Multipliable fun n : ℕ => quintupleJacobiRightFactor q z n := by
  have hq3norm : ‖q ^ 3‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hqnorm (by norm_num)
  exact (Ch02.multipliable_jacobiProductNatFactor (q ^ 3) (q ^ 4 / z ^ 3) hq3norm).congr
    fun n => jacobiProductNatFactor_quintuple_right_substitution q z n

/-- The first explicit JTP partial products tend to their infinite product. -/
theorem tendsto_quintupleJacobiLeftPartial
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    Tendsto (fun N : ℕ => quintupleJacobiLeftPartial q z N) atTop
      (𝓝 (∏' n : ℕ, quintupleJacobiLeftFactor q z n)) := by
  have h := (multipliable_quintupleJacobiLeftFactor q z hqnorm hq hz).tendsto_prod_tprod_nat
  simpa [quintupleJacobiLeftPartial] using h

/-- The second explicit JTP partial products tend to their infinite product. -/
theorem tendsto_quintupleJacobiRightPartial (q z : ℂ) (hqnorm : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => quintupleJacobiRightPartial q z N) atTop
      (𝓝 (∏' n : ℕ, quintupleJacobiRightFactor q z n)) := by
  have h := (multipliable_quintupleJacobiRightFactor q z hqnorm).tendsto_prod_tprod_nat
  simpa [quintupleJacobiRightPartial] using h

/-- The explicit RHS finite product-difference partials tend to the explicit RHS. -/
theorem tendsto_quintupleProductExplicitRHSPartial
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    Tendsto (fun N : ℕ => quintupleProductExplicitRHSPartial q z N) atTop
      (𝓝 (quintupleProductExplicitRHS q z)) := by
  have hleft := tendsto_quintupleJacobiLeftPartial q z hqnorm hq hz
  have hright := tendsto_quintupleJacobiRightPartial q z hqnorm
  have hscaled :
      Tendsto (fun N : ℕ => (q / z) * quintupleJacobiRightPartial q z N) atTop
        (𝓝 ((q / z) * (∏' n : ℕ, quintupleJacobiRightFactor q z n))) :=
    tendsto_const_nhds.mul hright
  simpa [quintupleProductExplicitRHSPartial, quintupleProductExplicitRHS] using
    hleft.sub hscaled

/--
If the finite difference between the quintuple LHS truncation and the explicit
product RHS partial tends to zero, then the explicit product identity follows.
-/
theorem quintupleProduct_explicitProduct_of_tendsto_trunc_sub_explicit
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0)
    (h :
      Tendsto
        (fun N : ℕ =>
          quintupleProductLHSTrunc q z N - quintupleProductExplicitRHSPartial q z N)
        atTop (𝓝 0)) :
    quintupleProductLHS q z = quintupleProductExplicitRHS q z := by
  have hlim :
      Tendsto
        (fun N : ℕ =>
          quintupleProductLHSTrunc q z N - quintupleProductExplicitRHSPartial q z N)
        atTop (𝓝 (quintupleProductLHS q z - quintupleProductExplicitRHS q z)) :=
    (tendsto_quintupleProductLHSTrunc q z hqnorm).sub
      (tendsto_quintupleProductExplicitRHSPartial q z hqnorm hq hz)
  have hzero : quintupleProductLHS q z - quintupleProductExplicitRHS q z = 0 :=
    (tendsto_nhds_unique h hlim).symm
  exact sub_eq_zero.mp hzero

/--
Ch02-product-partial version of the finite-difference reduction for the
explicit product identity.
-/
theorem quintupleProduct_explicitProduct_of_tendsto_trunc_sub_jacobiPartials
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0)
    (h :
      Tendsto
        (fun N : ℕ =>
          quintupleProductLHSTrunc q z N -
            (Ch02.jacobiProductPartial (q ^ 3) (z ^ 3 / q ^ 2) N -
              (q / z) * Ch02.jacobiProductPartial (q ^ 3) (q ^ 4 / z ^ 3) N))
        atTop (𝓝 0)) :
    quintupleProductLHS q z = quintupleProductExplicitRHS q z := by
  refine quintupleProduct_explicitProduct_of_tendsto_trunc_sub_explicit q z hqnorm hq hz ?_
  refine h.congr' ?_
  exact Eventually.of_forall fun N =>
    (quintupleProduct_trunc_sub_explicitPartial_eq_jacobiProductPartial_sub q z hq hz N).symm

/--
Finite-JTP/q-Pochhammer version of the finite-difference reduction for the
explicit product identity.
-/
theorem quintupleProduct_explicitProduct_of_tendsto_trunc_sub_qPoch_finiteJTPRHS
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0)
    (h :
      Tendsto
        (fun N : ℕ =>
          (qPoch (q ^ 2) (q ^ 2) N * qPoch (z * q) (q ^ 2) N *
              qPoch (q / z) (q ^ 2) N * qPoch (z ^ 2) (q ^ 4) N *
                qPoch (q ^ 4 / z ^ 2) (q ^ 4) N) -
            (qPoch (q ^ 6) (q ^ 6) N * finiteJTPRHS (q ^ 6) (-(z ^ 3 * q)) N -
              (q / z) * (qPoch (q ^ 6) (q ^ 6) N *
                finiteJTPRHS (q ^ 6) (-(q ^ 7 / z ^ 3)) N)))
        atTop (𝓝 0)) :
    quintupleProductLHS q z = quintupleProductExplicitRHS q z := by
  refine quintupleProduct_explicitProduct_of_tendsto_trunc_sub_explicit q z hqnorm hq hz ?_
  refine h.congr' ?_
  exact Eventually.of_forall fun N =>
    (quintupleProduct_trunc_sub_explicitPartial_eq_qPoch_finiteJTPRHS q z hq hz N).symm

/--
Weighted-Laurent-sum version of the finite-difference reduction for the
explicit product identity.
-/
theorem quintupleProduct_explicitProduct_of_tendsto_trunc_sub_qPoch_weightedSums
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0)
    (h :
      Tendsto
        (fun N : ℕ =>
          (qPoch (q ^ 2) (q ^ 2) N * qPoch (z * q) (q ^ 2) N *
              qPoch (q / z) (q ^ 2) N * qPoch (z ^ 2) (q ^ 4) N *
                qPoch (q ^ 4 / z ^ 2) (q ^ 4) N) -
            (qPoch (q ^ 6) (q ^ 6) N * quintupleFiniteJTPLeftWeightedSum q z N -
              (q / z) * (qPoch (q ^ 6) (q ^ 6) N *
                quintupleFiniteJTPRightWeightedSum q z N)))
        atTop (𝓝 0)) :
    quintupleProductLHS q z = quintupleProductExplicitRHS q z := by
  refine quintupleProduct_explicitProduct_of_tendsto_trunc_sub_explicit q z hqnorm hq hz ?_
  refine h.congr' ?_
  exact Eventually.of_forall fun N =>
    (quintupleProduct_trunc_sub_explicitPartial_eq_qPoch_weightedSums q z hq hz N).symm

/--
Combined-weighted-sum version of the finite-difference reduction for the
explicit product identity.
-/
theorem quintupleProduct_explicitProduct_of_tendsto_trunc_sub_qPoch_combinedWeightedSum
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0)
    (h :
      Tendsto
        (fun N : ℕ =>
          (qPoch (q ^ 2) (q ^ 2) N * qPoch (z * q) (q ^ 2) N *
              qPoch (q / z) (q ^ 2) N * qPoch (z ^ 2) (q ^ 4) N *
                qPoch (q ^ 4 / z ^ 2) (q ^ 4) N) -
            qPoch (q ^ 6) (q ^ 6) N *
              quintupleFiniteJTPCombinedWeightedSum q z N)
        atTop (𝓝 0)) :
    quintupleProductLHS q z = quintupleProductExplicitRHS q z := by
  refine quintupleProduct_explicitProduct_of_tendsto_trunc_sub_explicit q z hqnorm hq hz ?_
  refine h.congr' ?_
  exact Eventually.of_forall fun N =>
    (quintupleProduct_trunc_sub_explicitPartial_eq_qPoch_combinedWeightedSum q z hq hz N).symm

/--
Monomial-split combined-sum version of the finite-difference reduction for the
explicit product identity.
-/
theorem quintupleProduct_explicitProduct_of_tendsto_trunc_sub_qPoch_combinedMonomialSum
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0)
    (h :
      Tendsto
        (fun N : ℕ =>
          (qPoch (q ^ 2) (q ^ 2) N * qPoch (z * q) (q ^ 2) N *
              qPoch (q / z) (q ^ 2) N * qPoch (z ^ 2) (q ^ 4) N *
                qPoch (q ^ 4 / z ^ 2) (q ^ 4) N) -
            qPoch (q ^ 6) (q ^ 6) N *
              quintupleFiniteJTPCombinedMonomialSum q z N)
        atTop (𝓝 0)) :
    quintupleProductLHS q z = quintupleProductExplicitRHS q z := by
  refine quintupleProduct_explicitProduct_of_tendsto_trunc_sub_explicit q z hqnorm hq hz ?_
  refine h.congr' ?_
  exact Eventually.of_forall fun N =>
    (quintupleProduct_trunc_sub_explicitPartial_eq_qPoch_combinedMonomialSum q z hq hz N).symm

/-- Quintuple product RHS truncated: the bilateral sum over `-N ≤ n ≤ N`. -/
noncomputable def quintupleProductRHSTrunc (q z : R) (N : Nat) : R :=
  bilateralSum (quintupleProductTerm q z) N

/-- Sanity: the zero truncations unfold to the expected first terms. -/
theorem quintupleProduct_truncated_zero (q z : R) :
    quintupleProductLHSTrunc q z 0 = 1 ∧
      quintupleProductRHSTrunc q z 0 = 1 - q / z := by
  constructor
  · rfl
  · simp [quintupleProductRHSTrunc, quintupleProductTerm, quintupleQuadraticIndex,
      intPow]

/-- Quintuple product LHS at N=1: one triple of factors. -/
theorem quintupleProductLHSTrunc_one (q z : R) :
    quintupleProductLHSTrunc q z 1 =
      (1 - q ^ 2) * (1 - z * q) * (1 - z⁻¹ * q) * (1 - z ^ 2) * (1 - z⁻¹ ^ 2 * q ^ 4) := by
  simp [quintupleProductLHSTrunc]

/-- Quintuple product LHS at N=2. -/
theorem quintupleProductLHSTrunc_two (q z : R) :
    quintupleProductLHSTrunc q z 2 =
      (1 - q ^ 2) * (1 - z * q) * (1 - z⁻¹ * q) * (1 - z ^ 2) * (1 - z⁻¹ ^ 2 * q ^ 4) *
      (1 - q ^ 4) * (1 - z * q ^ 3) * (1 - z⁻¹ * q ^ 3) * (1 - z ^ 2 * q ^ 4) * (1 - z⁻¹ ^ 2 * q ^ 8) := by
  simp [quintupleProductLHSTrunc]

/-- Quintuple product LHS at N=3. -/
theorem quintupleProductLHSTrunc_three (q z : R) :
    quintupleProductLHSTrunc q z 3 =
      (1 - q ^ 2) * (1 - z * q) * (1 - z⁻¹ * q) * (1 - z ^ 2) * (1 - z⁻¹ ^ 2 * q ^ 4) *
      (1 - q ^ 4) * (1 - z * q ^ 3) * (1 - z⁻¹ * q ^ 3) * (1 - z ^ 2 * q ^ 4) * (1 - z⁻¹ ^ 2 * q ^ 8) *
      (1 - q ^ 6) * (1 - z * q ^ 5) * (1 - z⁻¹ * q ^ 5) * (1 - z ^ 2 * q ^ 8) * (1 - z⁻¹ ^ 2 * q ^ 12) := by
  simp [quintupleProductLHSTrunc]

theorem quintupleProductLHSTrunc_four (q z : R) :
    quintupleProductLHSTrunc q z 4 =
      quintupleProductLHSTrunc q z 3 *
      (1 - q ^ 8) * (1 - z * q ^ 7) * (1 - z⁻¹ * q ^ 7) * (1 - z ^ 2 * q ^ 12) * (1 - z⁻¹ ^ 2 * q ^ 16) := by
  simp [quintupleProductLHSTrunc]

theorem quintupleProductLHSTrunc_five (q z : R) :
    quintupleProductLHSTrunc q z 5 =
      quintupleProductLHSTrunc q z 4 *
      (1 - q ^ 10) * (1 - z * q ^ 9) * (1 - z⁻¹ * q ^ 9) * (1 - z ^ 2 * q ^ 16) * (1 - z⁻¹ ^ 2 * q ^ 20) := by
  simp [quintupleProductLHSTrunc]

theorem quintupleProductLHSTrunc_six (q z : R) :
    quintupleProductLHSTrunc q z 6 =
      quintupleProductLHSTrunc q z 5 *
      (1 - q ^ 12) * (1 - z * q ^ 11) * (1 - z⁻¹ * q ^ 11) * (1 - z ^ 2 * q ^ 20) * (1 - z⁻¹ ^ 2 * q ^ 24) := by
  simp [quintupleProductLHSTrunc]

theorem quintupleProductLHSTrunc_seven (q z : R) :
    quintupleProductLHSTrunc q z 7 =
      quintupleProductLHSTrunc q z 6 *
      (1 - q ^ 14) * (1 - z * q ^ 13) * (1 - z⁻¹ * q ^ 13) * (1 - z ^ 2 * q ^ 24) * (1 - z⁻¹ ^ 2 * q ^ 28) := by
  simp [quintupleProductLHSTrunc]

theorem quintupleProductLHSTrunc_eight (q z : R) :
    quintupleProductLHSTrunc q z 8 =
      quintupleProductLHSTrunc q z 7 *
      (1 - q ^ 16) * (1 - z * q ^ 15) * (1 - z⁻¹ * q ^ 15) * (1 - z ^ 2 * q ^ 28) * (1 - z⁻¹ ^ 2 * q ^ 32) := by
  simp [quintupleProductLHSTrunc]

theorem quintupleProductLHSTrunc_nine (q z : R) :
    quintupleProductLHSTrunc q z 9 =
      quintupleProductLHSTrunc q z 8 *
      (1 - q ^ 18) * (1 - z * q ^ 17) * (1 - z⁻¹ * q ^ 17) * (1 - z ^ 2 * q ^ 32) * (1 - z⁻¹ ^ 2 * q ^ 36) := by
  simp [quintupleProductLHSTrunc]

theorem quintupleProductLHSTrunc_ten (q z : R) :
    quintupleProductLHSTrunc q z 10 =
      quintupleProductLHSTrunc q z 9 *
      (1 - q ^ 20) * (1 - z * q ^ 19) * (1 - z⁻¹ * q ^ 19) * (1 - z ^ 2 * q ^ 36) * (1 - z⁻¹ ^ 2 * q ^ 40) := by
  simp [quintupleProductLHSTrunc]

theorem quintupleProductLHSTrunc_eleven (q z : R) :
    quintupleProductLHSTrunc q z 11 =
      quintupleProductLHSTrunc q z 10 *
      (1 - q ^ 22) * (1 - z * q ^ 21) * (1 - z⁻¹ * q ^ 21) * (1 - z ^ 2 * q ^ 40) * (1 - z⁻¹ ^ 2 * q ^ 44) := by
  simp [quintupleProductLHSTrunc]

theorem quintupleProductLHSTrunc_twelve (q z : R) :
    quintupleProductLHSTrunc q z 12 =
      quintupleProductLHSTrunc q z 11 *
      (1 - q ^ 24) * (1 - z * q ^ 23) * (1 - z⁻¹ * q ^ 23) * (1 - z ^ 2 * q ^ 44) * (1 - z⁻¹ ^ 2 * q ^ 48) := by
  simp [quintupleProductLHSTrunc]

theorem quintupleProductLHSTrunc_thirteen (q z : R) :
    quintupleProductLHSTrunc q z 13 =
      quintupleProductLHSTrunc q z 12 *
      (1 - q ^ 26) * (1 - z * q ^ 25) * (1 - z⁻¹ * q ^ 25) * (1 - z ^ 2 * q ^ 48) * (1 - z⁻¹ ^ 2 * q ^ 52) := by
  simp [quintupleProductLHSTrunc]

theorem quintupleProductLHSTrunc_fourteen (q z : R) :
    quintupleProductLHSTrunc q z 14 =
      quintupleProductLHSTrunc q z 13 *
      (1 - q ^ 28) * (1 - z * q ^ 27) * (1 - z⁻¹ * q ^ 27) * (1 - z ^ 2 * q ^ 52) * (1 - z⁻¹ ^ 2 * q ^ 56) := by
  simp [quintupleProductLHSTrunc]

theorem quintupleProductLHSTrunc_fifteen (q z : R) :
    quintupleProductLHSTrunc q z 15 =
      quintupleProductLHSTrunc q z 14 *
      (1 - q ^ 30) * (1 - z * q ^ 29) * (1 - z⁻¹ * q ^ 29) * (1 - z ^ 2 * q ^ 56) * (1 - z⁻¹ ^ 2 * q ^ 60) := by
  simp [quintupleProductLHSTrunc]

/- The infinite quintuple product identity is deferred to the JTP specialization
and rewriting layer used in Chan's proof. -/

/-! ### Finite JTP specialized at z = 1: Euler pentagonal general identity -/

/--
Specializing the finite Jacobi triple product at `z = 1`:
`(1; q)_n * (q; q)_n = finiteJTPRHS q 1 n`.

When `z = 1`, the factor `z⁻¹ * q = q`, so the LHS becomes
`qPoch 1 q n * qPoch q q n`.
-/
theorem finite_jtp_at_z_one (q : R) (hq : q ≠ 0) (n : Nat) :
    qPoch 1 q n * qPoch q q n = finiteJTPRHS q 1 n := by
  have h := finite_jacobi_triple_product q 1 one_ne_zero hq n
  rwa [inv_one, one_mul] at h

/--
`qPoch 1 q n = 0` for any `n ≥ 1`: the first factor `(1 - 1 * q^0) = 0`
kills the entire product.
-/
theorem qPoch_one_eq_zero (q : R) (n : Nat) (hn : 1 ≤ n) :
    qPoch (1 : R) q n = 0 := by
  cases n with
  | zero => omega
  | succ m =>
    induction m with
    | zero => simp [qPoch]
    | succ k ih =>
      rw [qPoch_succ]
      have : qPoch (1 : R) q (k + 1) = 0 := ih (by omega)
      rw [this]
      simp

/-- Succ-indexed form of `qPoch_one_eq_zero`, convenient for finite truncations. -/
theorem qPoch_one_succ_eq_zero (q : R) (n : Nat) :
    qPoch (1 : R) q (n + 1) = 0 :=
  qPoch_one_eq_zero q (n + 1) (by omega)

/-- The finite `(1; q^6)` factor that appears in Theorem 4.4's third residue class is zero. -/
theorem theorem44ResidueTwo_qPoch_one_qsix_zero (q : ℂ) (n : Nat) :
    qPoch (1 : ℂ) (q ^ 6) (n + 1) = 0 :=
  qPoch_one_succ_eq_zero (q ^ 6) n

/-- Any finite coefficient expression containing the Theorem 4.4 third-residue zero factor vanishes. -/
theorem theorem44ResidueTwo_qPoch_zero_factor (q A B : ℂ) (n : Nat) :
    A * qPoch (1 : ℂ) (q ^ 6) (n + 1) * B = 0 := by
  rw [theorem44ResidueTwo_qPoch_one_qsix_zero q n]
  ring

/--
The finite JTP RHS vanishes at `z = 1` for all `n ≥ 1`.  This is the
general truncated pentagonal vanishing identity: the bilateral sum
`∑_{k=0}^{2n} [2n choose k]_q · q^{(k-n)(k-n-1)/2} · (-1)^{k-n}`
equals zero for every `n ≥ 1`.
-/
theorem finiteJTPRHS_at_z_one_eq_zero (q : R) (hq : q ≠ 0) (n : Nat) (hn : 1 ≤ n) :
    finiteJTPRHS q 1 n = 0 := by
  have h := finite_jtp_at_z_one q hq n
  rw [qPoch_one_eq_zero q n hn, zero_mul] at h
  exact h.symm

/--
`qPoch q q n = qPochhammer q n` restated in Chapter 4 context
(already in Basic as `qPoch_q_eq_qPochhammer`).
-/
theorem qPoch_q_eq_eulerProduct (q : R) (n : Nat) :
    qPoch q q n = eulerPentagonalProductTrunc q n := by
  simp [eulerPentagonalProductTrunc, qPoch_q_eq_qPochhammer]

/--
Restatement using the Chapter 4 Euler product notation:
`finiteJTPRHS q 1 n = 0` for `n ≥ 1`, connecting to `eulerPentagonalProductTrunc`.
-/
theorem euler_pentagonal_jtp_connection (q : R) (hq : q ≠ 0) (n : Nat) (hn : 1 ≤ n) :
    finiteJTPRHS q 1 n = 0 :=
  finiteJTPRHS_at_z_one_eq_zero q hq n hn

end Field

/-! ### Quintuple product identity: final assembly via Tannery-style convergence

The strategy: prove both the LHS product truncation and the qPoch⁶×combinedMonomialSum
converge to `quintupleProductLHS`, then their difference → 0, closing the identity.

Key bridge: a generic "fixed-core + uniform-tail" convergence lemma. -/

section QuintupleAssembly

open scoped Topology
open Filter

/-- Generic diagonal-convergence lemma: if `C N M → P M` for fixed M,
`P M → L`, and the tail `S N - C N M` is uniformly small for large M,
then `S N → L`. -/
theorem tendsto_of_fixed_core_and_uniform_tail
    {S : ℕ → ℂ} {C : ℕ → ℕ → ℂ} {P : ℕ → ℂ} {L : ℂ}
    (hfixed : ∀ M : ℕ, Tendsto (fun N : ℕ => C N M) atTop (𝓝 (P M)))
    (hP : Tendsto P atTop (𝓝 L))
    (htail : ∀ ε > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ᶠ N in atTop, ‖S N - C N M‖ < ε) :
    Tendsto S atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨K₁, hK₁⟩ := Metric.tendsto_atTop.mp hP (ε / 3) hε3
  obtain ⟨K₂, hK₂⟩ := htail (ε / 3) hε3
  set M := max K₁ K₂
  have hM1 : M ≥ K₁ := le_max_left _ _
  have hM2 : M ≥ K₂ := le_max_right _ _
  have h_PM : dist (P M) L < ε / 3 := hK₁ M hM1
  have h_tail_ev := hK₂ M hM2
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp (hfixed M) (ε / 3) hε3
  rw [Filter.eventually_atTop] at h_tail_ev
  obtain ⟨N₂, hN₂⟩ := h_tail_ev
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  have h_core : dist (C N M) (P M) < ε / 3 := hN₁ N (by omega)
  have h_tail : ‖S N - C N M‖ < ε / 3 := hN₂ N (by omega)
  have h_dist_tail : dist (S N) (C N M) < ε / 3 := by
    rwa [Complex.dist_eq]
  linarith [dist_triangle (S N) (C N M) L,
            dist_triangle (C N M) (P M) L]

/-- The symmetric partials converge to the quintuple RHS. -/
theorem tendsto_quintupleProductSeriesSymmetricPartial_to_RHS
    (q z : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (quintupleProductSeriesSymmetricPartial q z) atTop
      (𝓝 (quintupleProductRHS q z)) := by
  set f := quintupleProductSeriesTerm q z
  have hsumm := summable_quintupleProductSeriesTerm q z hq
  set g := quintupleProductSeriesSymmetricPairTerm q z
  have hneg : Summable (fun r : ℕ => f (-(↑r + 1))) :=
    hsumm.comp_injective (fun a b (h : -(↑a + 1 : ℤ) = -(↑b + 1)) => by omega)
  have hpos : Summable (fun r : ℕ => f ((r : ℤ) + 1)) :=
    hsumm.comp_injective (fun a b (h : (↑a : ℤ) + 1 = ↑b + 1) => by omega)
  set a := ∑' r : ℕ, f (-(↑r + 1 : ℤ))
  set b := ∑' r : ℕ, f ((↑r : ℤ) + 1)
  have hg : HasSum g (a + b) := by
    show HasSum (fun r : ℕ => f (-(↑r + 1 : ℤ)) + f ((↑r : ℤ) + 1)) (a + b)
    exact hneg.hasSum.add hpos.hasSum
  have hnat : Summable (fun n : ℕ => f ↑n) :=
    hsumm.comp_injective Nat.cast_injective
  have hRHS : quintupleProductRHS q z = f 0 + (a + b) := by
    have h1 : (∑' n : ℤ, f n) = (∑' n : ℕ, f ↑n) + a :=
      tsum_of_nat_of_neg_add_one hnat hneg
    have h2 : (∑' n : ℕ, f ↑n) = f 0 + b := by
      rw [hnat.tsum_eq_zero_add]
      simp only [b]
      congr 1
    rw [quintupleProductRHS, h1, h2]; ring
  have hpartial : quintupleProductSeriesSymmetricPartial q z =
      (fun M => f 0 + ∑ r ∈ Finset.range M, g r) := by
    ext M
    rfl
  rw [hRHS, hpartial]
  exact tendsto_const_nhds.add hg.tendsto_sum_nat

/-! ### Quintuple product: uniform tail estimate for the combined monomial sum -/

/-- The normalized full combined-monomial sum used in the finite JTP
factorization of the quintuple product. -/
noncomputable def qPoch_qsix_mul_quintupleCombinedMonomialSum (q z : ℂ) (N : ℕ) : ℂ :=
  qPoch (q ^ 6) (q ^ 6) N * quintupleFiniteJTPCombinedMonomialSum q z N

/-- The normalized fixed symmetric core of the combined-monomial sum. -/
noncomputable def qPoch_qsix_mul_quintupleCombinedMonomialCore (q z : ℂ) (N M : ℕ) : ℂ :=
  qPoch (q ^ 6) (q ^ 6) N * quintupleFiniteJTPCombinedMonomialSymmetricPartial q z N M

/-- The normalized combined-monomial tail. -/
noncomputable def qPoch_qsix_mul_quintupleCombinedMonomialTail (q z : ℂ) (N M : ℕ) : ℂ :=
  qPoch_qsix_mul_quintupleCombinedMonomialSum q z N -
    qPoch_qsix_mul_quintupleCombinedMonomialCore q z N M

/-- Split-norm majorant: ∑' (‖f(-(M+r+1))‖ + ‖f(M+r+1)‖). Easier to bound than ‖pair‖. -/
noncomputable def quintupleSplitNormMajorantTail (q z : ℂ) (M : ℕ) : ℝ :=
  ∑' r : ℕ, (‖quintupleProductSeriesTerm q z (-(↑(M + r) + 1 : ℤ))‖ +
    ‖quintupleProductSeriesTerm q z ((↑(M + r) : ℤ) + 1)‖)

/-- The split-norm majorant components are summable. -/
theorem summable_split_norm_majorant_terms (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun r : ℕ =>
      ‖quintupleProductSeriesTerm q z (-(↑r + 1 : ℤ))‖ +
        ‖quintupleProductSeriesTerm q z ((↑r : ℤ) + 1)‖) := by
  have hf := summable_quintupleProductSeriesTerm q z hq
  have hinj_neg : Function.Injective (fun r : ℕ => (-(↑r + 1 : ℤ))) :=
    fun a b h => by push_cast at h; omega
  have hinj_pos : Function.Injective (fun r : ℕ => ((↑r : ℤ) + 1)) :=
    fun a b h => by push_cast at h; omega
  exact ((hf.comp_injective hinj_neg).norm).add ((hf.comp_injective hinj_pos).norm)

/-- Split-norm majorant tails tend to zero. -/
theorem tendsto_quintupleSplitNormMajorantTail_zero (q z : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (quintupleSplitNormMajorantTail q z) atTop (𝓝 0) := by
  set g := fun r : ℕ =>
    ‖quintupleProductSeriesTerm q z (-(↑r + 1 : ℤ))‖ +
      ‖quintupleProductSeriesTerm q z ((↑r : ℤ) + 1)‖
  have : quintupleSplitNormMajorantTail q z = fun i => ∑' k, g (k + i) := by
    ext i
    simp only [quintupleSplitNormMajorantTail, g]
    congr 1; ext k
    congr 2 <;> push_cast <;> ring
  rw [this]
  exact tendsto_sum_nat_add g

/-! Dead Route B end-cap removed: the bridge to `quintupleProductRHS` is now
done entirely via Route A (JTP product decomposition) below. The upstream
`qPoch_qsix_mul_quintupleCombinedMonomial*` and `tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomial*`
infrastructure is retained in case it's useful for future routes. -/

/-! #### Route A: Product decomposition via JTP

The quintuple product factors decompose as:
  quintupleProductFactor(n) = JacobiNatFactor(q, -z, n) × JacobiNatFactor(q², -z²/q², n) / (1-q^{4n+4})

At the infinite product level:
  quintupleProductLHS = jacobiInfiniteProduct(q, -z) × jacobiInfiniteProduct(q², -z²/q²) / (q⁴;q⁴)_∞

Then JTP converts each infinite product to a bilateral series, and the product
of two series (after mod-3 regrouping) gives ExplicitRHS. -/

/-- Factor-level identity: `quintupleProductFactor q z n` equals the product of two
JTP Nat-factors divided by `(1 - q^{4n+4})`. -/
theorem quintupleProductFactor_eq_jacobi_div (q z : ℂ) (hq : q ≠ 0) (hz : z ≠ 0) (n : ℕ) :
    quintupleProductFactor q z n * (1 - q ^ (4 * n + 4)) =
      Ch02.jacobiProductNatFactor q (-z) n *
        Ch02.jacobiProductNatFactor (q ^ 2) (-(z ^ 2 / q ^ 2)) n := by
  simp only [quintupleProductFactor, Ch02.jacobiProductNatFactor,
    Ch02.jacobiProductEvenFactor, Ch02.jacobiProductOddFactor]
  have hpow1 : (q ^ 2) ^ (2 * (n + 1)) = q ^ (4 * n + 4) := by ring
  have hpow2 : (q ^ 2) ^ (2 * (n + 1) - 1) = q ^ (4 * n + 2) := by
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 from by omega, ← pow_mul]; congr 1; ring
  rw [hpow1, hpow2]
  have hzsq : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have hqsq : q ^ 2 ≠ 0 := pow_ne_zero 2 hq
  set a := q ^ (2 * n + 2)
  set b := z * q ^ (2 * n + 1)
  set c := z⁻¹ * q ^ (2 * n + 1)
  set d := z ^ 2 * q ^ (4 * n)
  set e := z⁻¹ ^ 2 * q ^ (4 * n + 4)
  set f := q ^ (4 * n + 4)
  show (1 - a) * (1 - b) * (1 - c) * (1 - d) * (1 - e) * (1 - f) =
    (1 - a) * (1 + -z * q ^ (2 * n + 1)) * (1 + (-z)⁻¹ * q ^ (2 * n + 1)) *
      ((1 - q ^ (4 * n + 4)) * (1 + -(z ^ 2 / q ^ 2) * q ^ (4 * n + 2)) *
        (1 + (-(z ^ 2 / q ^ 2))⁻¹ * q ^ (4 * n + 2)))
  have hb' : 1 + -z * q ^ (2 * n + 1) = 1 - b := by simp [b]; ring
  have hc' : 1 + (-z)⁻¹ * q ^ (2 * n + 1) = 1 - c := by
    simp only [c, neg_inv]; ring
  have hd' : 1 + -(z ^ 2 / q ^ 2) * q ^ (4 * n + 2) = 1 - d := by
    simp only [d]; field_simp; ring
  have he' : 1 + (-(z ^ 2 / q ^ 2))⁻¹ * q ^ (4 * n + 2) = 1 - e := by
    simp only [e]
    have : (-(z ^ 2 / q ^ 2))⁻¹ = -(q ^ 2 / z ^ 2) := by
      simp [neg_inv, inv_div]
    rw [this]; field_simp; ring
  rw [hb', hc', hd', he']
  ring

/-- Infinite product decomposition:
`quintupleProductLHS * (q⁴;q⁴)_∞ = JTP(q,-z) × JTP(q²,-z²/q²)`. -/
theorem quintupleProductLHS_mul_qPoch_eq_jacobi_mul
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    quintupleProductLHS q z * (∏' n : ℕ, (1 - q ^ (4 * n + 4))) =
      Ch02.jacobiInfiniteProduct q (-z) *
        Ch02.jacobiInfiniteProduct (q ^ 2) (-(z ^ 2 / q ^ 2)) := by
  have hq2 : ‖q ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hqnorm (by norm_num)
  have hmult_qpf := multipliable_quintupleProductFactor q z hqnorm
  have hmult_even : Multipliable (fun n : ℕ => (1 : ℂ) - q ^ (4 * n + 4)) := by
    have h := Ch02.multipliable_jacobiProductEvenFactor (q ^ 2) hq2
    simp only [Ch02.jacobiProductEvenFactor] at h
    exact h.congr fun n => by congr 1; ring
  have hmult_left := Ch02.multipliable_jacobiProductNatFactor q (-z) hqnorm
  have hmult_right := Ch02.multipliable_jacobiProductNatFactor (q ^ 2) (-(z ^ 2 / q ^ 2)) hq2
  rw [quintupleProductLHS]
  rw [← hmult_qpf.tprod_mul hmult_even]
  rw [show (fun n => quintupleProductFactor q z n * (1 - q ^ (4 * n + 4))) =
    (fun n => Ch02.jacobiProductNatFactor q (-z) n *
      Ch02.jacobiProductNatFactor (q ^ 2) (-(z ^ 2 / q ^ 2)) n) from by
    ext n; exact quintupleProductFactor_eq_jacobi_div q z hq hz n]
  rw [hmult_left.tprod_mul hmult_right]
  congr 1 <;> exact (Ch02.jacobiInfiniteProduct_eq_tprod_natFactor _ _).symm

/-- Convert the product decomposition to series using JTP. -/
theorem quintupleProductLHS_mul_qPoch_eq_series_mul
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    quintupleProductLHS q z * (∏' n : ℕ, (1 - q ^ (4 * n + 4))) =
      Ch02.jacobiInfiniteSeries q (-z) *
        Ch02.jacobiInfiniteSeries (q ^ 2) (-(z ^ 2 / q ^ 2)) := by
  rw [quintupleProductLHS_mul_qPoch_eq_jacobi_mul q z hqnorm hq hz]
  have hq2 : ‖q ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hqnorm (by norm_num)
  rw [Ch02.jacobiTripleProduct q (-z) hqnorm (neg_ne_zero.mpr hz)]
  rw [Ch02.jacobiTripleProduct (q ^ 2) (-(z ^ 2 / q ^ 2)) hq2
    (neg_ne_zero.mpr (div_ne_zero (pow_ne_zero 2 hz) (pow_ne_zero 2 hq)))]

/-- Sub-lemma 1: Cauchy product + shear reindex + Fubini. -/
def quintupleShearEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.1 + 2 * p.2, p.2)
  invFun p := (p.1 - 2 * p.2, p.2)
  left_inv := fun p => by ext <;> simp <;> ring
  right_inv := fun p => by ext <;> simp <;> ring

theorem quintuple_double_sum_shear
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    (∑' r : ℤ, (-z) ^ r * q ^ (r ^ 2)) *
      (∑' s : ℤ, (-(z ^ 2 / q ^ 2)) ^ s * (q ^ 2) ^ (s ^ 2)) =
      ∑' k : ℤ, (-1 : ℂ) ^ k * z ^ k * q ^ (k ^ 2) *
        (∑' s : ℤ, (-1 : ℂ) ^ s * q ^ (6 * s ^ 2 - (4 * k + 2) * s)) := by
  classical
  let f : ℤ → ℂ := fun r => (-z) ^ r * q ^ (r ^ 2)
  let g : ℤ → ℂ := fun s => (-(z ^ 2 / q ^ 2)) ^ s * (q ^ 2) ^ (s ^ 2)
  have hq2norm : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hqnorm (by norm_num)
  have hf : Summable f := by
    simpa [f] using Ch02.summable_jacobiInfiniteSeries_terms q (-z) hqnorm
  have hg : Summable g := by
    simpa [g] using Ch02.summable_jacobiInfiniteSeries_terms (q ^ 2) (-(z ^ 2 / q ^ 2)) hq2norm
  let shear : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (p.1 + 2 * p.2, p.2)
      invFun := fun p => (p.1 - 2 * p.2, p.2)
      left_inv := by intro p; rcases p with ⟨r, s⟩; ext <;> simp <;> ring
      right_inv := by intro p; rcases p with ⟨k, s⟩; ext <;> simp <;> ring }
  have hterm : ∀ k s : ℤ,
      f (k - 2 * s) * g s =
        (-1 : ℂ) ^ k * z ^ k * q ^ (k ^ 2) *
          ((-1 : ℂ) ^ s * q ^ (6 * s ^ 2 - (4 * k + 2) * s)) := by
    intro k s; dsimp [f, g]
    have hmone : (-1 : ℂ) ≠ 0 := by norm_num
    have h1 : (-z) ^ (k - 2 * s) = (-1) ^ (k - 2 * s) * z ^ (k - 2 * s) := by
      rw [neg_eq_neg_one_mul, mul_zpow]
    have h2 : (-(z ^ 2 / q ^ 2)) ^ s = (-1) ^ s * z ^ (2 * s) / q ^ (2 * s) := by
      rw [neg_eq_neg_one_mul, mul_zpow, div_zpow,
          ← zpow_natCast z 2, ← zpow_mul, ← zpow_natCast q 2, ← zpow_mul]
      push_cast; ring
    have h3 : (q ^ 2) ^ (s ^ 2) = q ^ (2 * s ^ 2) := by
      rw [← zpow_natCast q 2, ← zpow_mul]; push_cast; rfl
    have hsign : (-1 : ℂ) ^ (k - 2 * s) * (-1) ^ s = (-1) ^ k * (-1) ^ s := by
      rw [← zpow_add₀ hmone, show k - 2 * s + s = k - s from by ring,
          show k - s = k + s + (-2 * s) from by ring, zpow_add₀ hmone]
      have : (-1 : ℂ) ^ (-2 * s) = 1 := by
        rw [show (-2 : ℤ) * s = -(2 * s) from by ring, zpow_neg, zpow_mul,
            show (-1 : ℂ) ^ (2 : ℤ) = 1 from by norm_num, one_zpow, inv_one]
      rw [this, mul_one, zpow_add₀ hmone]
    have hzpow : z ^ (k - 2 * s) * z ^ (2 * s) = z ^ k := by
      rw [← zpow_add₀ hz]; congr 1; ring
    have hqpow : q ^ ((k - 2 * s) ^ 2) / q ^ (2 * s) * q ^ (2 * s ^ 2) =
        q ^ (k ^ 2) * q ^ (6 * s ^ 2 - (4 * k + 2) * s) := by
      rw [div_eq_mul_inv, ← zpow_neg, ← zpow_add₀ hq, ← zpow_add₀ hq, ← zpow_add₀ hq]
      congr 1; ring
    rw [h1, h2, h3]
    calc (-1) ^ (k - 2 * s) * z ^ (k - 2 * s) * q ^ ((k - 2 * s) ^ 2) *
          ((-1) ^ s * z ^ (2 * s) / q ^ (2 * s) * q ^ (2 * s ^ 2))
        = ((-1) ^ (k - 2 * s) * (-1) ^ s) * (z ^ (k - 2 * s) * z ^ (2 * s)) *
            (q ^ ((k - 2 * s) ^ 2) / q ^ (2 * s) * q ^ (2 * s ^ 2)) := by ring
      _ = ((-1) ^ k * (-1) ^ s) * z ^ k * (q ^ (k ^ 2) * q ^ (6 * s ^ 2 - (4 * k + 2) * s)) := by
          rw [hsign, hzpow, hqpow]
      _ = (-1) ^ k * z ^ k * q ^ (k ^ 2) * ((-1) ^ s * q ^ (6 * s ^ 2 - (4 * k + 2) * s)) := by
          ring
  calc (∑' r : ℤ, (-z) ^ r * q ^ (r ^ 2)) *
        (∑' s : ℤ, (-(z ^ 2 / q ^ 2)) ^ s * (q ^ 2) ^ (s ^ 2))
      = (∑' r : ℤ, f r) * (∑' s : ℤ, g s) := by simp [f, g]
    _ = ∑' p : ℤ × ℤ, f p.1 * g p.2 := by
        exact hf.tsum_mul_tsum hg (summable_mul_of_summable_norm hf.norm hg.norm)
    _ = ∑' p : ℤ × ℤ, f (p.1 - 2 * p.2) * g p.2 := by
        simpa [shear] using ((shear.symm).tsum_eq (fun p : ℤ × ℤ => f p.1 * g p.2)).symm
    _ = ∑' p : ℤ × ℤ, (-1 : ℂ) ^ p.1 * z ^ p.1 * q ^ (p.1 ^ 2) *
          ((-1 : ℂ) ^ p.2 * q ^ (6 * p.2 ^ 2 - (4 * p.1 + 2) * p.2)) := by
        apply tsum_congr; intro p; exact hterm p.1 p.2
    _ = ∑' k : ℤ, ∑' s : ℤ, (-1 : ℂ) ^ k * z ^ k * q ^ (k ^ 2) *
          ((-1 : ℂ) ^ s * q ^ (6 * s ^ 2 - (4 * k + 2) * s)) := by
        have hsumm_fg := summable_mul_of_summable_norm hf.norm hg.norm
        -- The function after tsum_congr is summable via the Cauchy product + shear equiv
        have hsumm_shear : Summable (fun p : ℤ × ℤ =>
            (-1 : ℂ) ^ p.1 * z ^ p.1 * q ^ (p.1 ^ 2) *
              ((-1 : ℂ) ^ p.2 * q ^ (6 * p.2 ^ 2 - (4 * p.1 + 2) * p.2))) := by
          rw [show (fun p : ℤ × ℤ => (-1 : ℂ) ^ p.1 * z ^ p.1 * q ^ (p.1 ^ 2) *
              ((-1 : ℂ) ^ p.2 * q ^ (6 * p.2 ^ 2 - (4 * p.1 + 2) * p.2))) =
            (fun p : ℤ × ℤ => f p.1 * g p.2) ∘ quintupleShearEquiv.symm from by
            ext p; simp [quintupleShearEquiv]
            exact (hterm p.1 p.2).symm]
          exact (quintupleShearEquiv.symm.summable_iff.mpr hsumm_fg)
        exact hsumm_shear.tsum_prod
    _ = ∑' k : ℤ, (-1 : ℂ) ^ k * z ^ k * q ^ (k ^ 2) *
          (∑' s : ℤ, (-1 : ℂ) ^ s * q ^ (6 * s ^ 2 - (4 * k + 2) * s)) := by
        apply tsum_congr; intro k; rw [tsum_mul_left]

/-- Helper: multipliability of `1 - q^(a*n + b)` for `‖q‖ < 1` and `a > 0`. -/
private theorem multipliable_one_sub_qpow_aff (q : ℂ) (hqnorm : ‖q‖ < 1) (a b : ℕ) (ha : 0 < a) :
    Multipliable (fun n : ℕ => (1 : ℂ) - q ^ (a * n + b)) := by
  refine (multipliable_one_add_of_summable (f := fun n : ℕ => -(q ^ (a * n + b))) ?_).congr
    (fun n => by ring)
  simp_rw [norm_neg, norm_pow]
  have ha1 : ‖q‖ ^ a < 1 := pow_lt_one₀ (norm_nonneg q) hqnorm (Nat.pos_iff_ne_zero.mp ha)
  have hgeom : Summable (fun n : ℕ => (‖q‖ ^ a) ^ n) :=
    summable_geometric_of_lt_one (by positivity) ha1
  refine (hgeom.mul_left (‖q‖ ^ b)).congr fun n => ?_
  rw [show a * n + b = b + a * n from by ring, pow_add, pow_mul]

/-- For `m : ℕ`, the product over `Fin 3` of `1 - q^(12m + 4r.val + 4)` is the triple
factor `(1 - q^(12m+4))(1 - q^(12m+8))(1 - q^(12m+12))`. -/
private theorem fin3_qpoch_factor_eval (q : ℂ) (m : ℕ) :
    (∏ r : Fin 3, ((1 : ℂ) - q ^ (12 * m + 4 * r.val + 4))) =
      ((1 : ℂ) - q ^ (12 * m + 4)) * ((1 : ℂ) - q ^ (12 * m + 8)) *
        ((1 : ℂ) - q ^ (12 * m + 12)) := by
  have e0 : 12 * m + 4 * (0 : Fin 3).val + 4 = 12 * m + 4 := by
    show 12 * m + 4 * 0 + 4 = 12 * m + 4; omega
  have e1 : 12 * m + 4 * (1 : Fin 3).val + 4 = 12 * m + 8 := by
    show 12 * m + 4 * 1 + 4 = 12 * m + 8; omega
  have e2 : 12 * m + 4 * (2 : Fin 3).val + 4 = 12 * m + 12 := by
    show 12 * m + 4 * 2 + 4 = 12 * m + 12; omega
  rw [Fin.prod_univ_three, e0, e1, e2]

/-- Mod-3 residue split of `(q^4; q^4)_∞` via finite partial products and uniqueness of limits.
This avoids the `Nat.divModEquiv 3` bijection, which times out in `tprod_prod`. -/
private theorem qpoch_q4_residue_split (q : ℂ) (hqnorm : ‖q‖ < 1) :
    (∏' m : ℕ, ((1 : ℂ) - q ^ (12 * m + 4))) *
        (∏' m : ℕ, ((1 : ℂ) - q ^ (12 * m + 8))) *
        (∏' m : ℕ, ((1 : ℂ) - q ^ (12 * m + 12))) =
      ∏' m : ℕ, ((1 : ℂ) - q ^ (4 * m + 4)) := by
  classical
  set f4 : ℕ → ℂ := fun m => (1 : ℂ) - q ^ (12 * m + 4) with hf4def
  set f8 : ℕ → ℂ := fun m => (1 : ℂ) - q ^ (12 * m + 8) with hf8def
  set f12 : ℕ → ℂ := fun m => (1 : ℂ) - q ^ (12 * m + 12) with hf12def
  set ffull : ℕ → ℂ := fun m => (1 : ℂ) - q ^ (4 * m + 4) with hffulldef
  have hM4 : Multipliable f4 := multipliable_one_sub_qpow_aff q hqnorm 12 4 (by norm_num)
  have hM8 : Multipliable f8 := multipliable_one_sub_qpow_aff q hqnorm 12 8 (by norm_num)
  have hM12 : Multipliable f12 := multipliable_one_sub_qpow_aff q hqnorm 12 12 (by norm_num)
  have hMfull : Multipliable ffull := multipliable_one_sub_qpow_aff q hqnorm 4 4 (by norm_num)
  -- Key finite identity: (∏ range N f4)(∏ range N f8)(∏ range N f12) = ∏ range (3N) ffull
  have hfinite : ∀ N : ℕ,
      ((∏ m ∈ Finset.range N, f4 m) *
          (∏ m ∈ Finset.range N, f8 m) *
          (∏ m ∈ Finset.range N, f12 m)) =
        ∏ m ∈ Finset.range (3 * N), ffull m := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        have h0 : 4 * (3 * N) + 4 = 12 * N + 4 := by ring
        have h1 : 4 * (3 * N + 1) + 4 = 12 * N + 8 := by ring
        have h2 : 4 * (3 * N + 2) + 4 = 12 * N + 12 := by ring
        have hN : 3 * (N + 1) = (3 * N + 2) + 1 := by ring
        rw [Finset.prod_range_succ (f := f4),
            Finset.prod_range_succ (f := f8),
            Finset.prod_range_succ (f := f12),
            hN,
            Finset.prod_range_succ (f := ffull),
            show (3 * N + 2 : ℕ) = (3 * N + 1) + 1 from rfl,
            Finset.prod_range_succ (f := ffull),
            show (3 * N + 1 : ℕ) = 3 * N + 1 from rfl,
            Finset.prod_range_succ (f := ffull)]
        simp only [hf4def, hf8def, hf12def, hffulldef, h0, h1, h2]
        have : (∏ m ∈ Finset.range N, f4 m) *
                  (∏ m ∈ Finset.range N, f8 m) *
                  (∏ m ∈ Finset.range N, f12 m) =
                ∏ m ∈ Finset.range (3 * N), ffull m := ih
        linear_combination
          ((1 : ℂ) - q ^ (12 * N + 4)) * ((1 : ℂ) - q ^ (12 * N + 8)) *
            ((1 : ℂ) - q ^ (12 * N + 12)) * this
  -- Both LHS-shape and RHS-shape converge to the same product
  have hlimL :
      Tendsto
        (fun N : ℕ =>
          (∏ m ∈ Finset.range N, f4 m) *
            (∏ m ∈ Finset.range N, f8 m) *
            (∏ m ∈ Finset.range N, f12 m))
        atTop
        (𝓝 ((∏' m : ℕ, f4 m) *
            (∏' m : ℕ, f8 m) *
            (∏' m : ℕ, f12 m))) :=
    ((hM4.hasProd.tendsto_prod_nat.mul hM8.hasProd.tendsto_prod_nat).mul
      hM12.hasProd.tendsto_prod_nat)
  have hmul_atTop : Tendsto (fun N : ℕ => 3 * N) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    refine Filter.eventually_atTop.2 ⟨b, fun N hN => ?_⟩
    omega
  have hlimFull3 :
      Tendsto (fun N : ℕ => ∏ m ∈ Finset.range (3 * N), ffull m) atTop
        (𝓝 (∏' m : ℕ, ffull m)) :=
    hMfull.hasProd.tendsto_prod_nat.comp hmul_atTop
  have hlimR :
      Tendsto
        (fun N : ℕ =>
          (∏ m ∈ Finset.range N, f4 m) *
            (∏ m ∈ Finset.range N, f8 m) *
            (∏ m ∈ Finset.range N, f12 m))
        atTop (𝓝 (∏' m : ℕ, ffull m)) := by
    have hfun : (fun N : ℕ =>
          (∏ m ∈ Finset.range N, f4 m) *
            (∏ m ∈ Finset.range N, f8 m) *
            (∏ m ∈ Finset.range N, f12 m)) =
        (fun N : ℕ => ∏ m ∈ Finset.range (3 * N), ffull m) := funext hfinite
    rw [hfun]; exact hlimFull3
  exact tendsto_nhds_unique hlimL hlimR

/-- Iterated Jacobi functional equation: shifting the second argument by `q^(2n)` for `n : ℤ`. -/
private theorem jacobiInfiniteSeries_qsq_iterate_int
    (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (z : ℂ) (hz : z ≠ 0) (n : ℤ) :
    Ch02.jacobiInfiniteSeries q (q ^ (2 * n : ℤ) * z) =
      q ^ (-(n * n) : ℤ) * z ^ (-n : ℤ) * Ch02.jacobiInfiniteSeries q z := by
  classical
  rw [Ch02.jacobiInfiniteSeries, Ch02.jacobiInfiniteSeries]
  rw [← (Equiv.addRight n).tsum_eq
    (fun r : ℤ => z ^ r * q ^ (r ^ 2))]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro r
  show (q ^ (2 * n : ℤ) * z) ^ r * q ^ (r ^ 2) =
    q ^ (-(n * n) : ℤ) * z ^ (-n : ℤ) * (z ^ (r + n) * q ^ ((r + n) ^ 2))
  -- Goal: (q^(2n) z)^r * q^(r²) = q^(-n²) z^(-n) * (z^(r+n) * q^((r+n)²))
  have hq2n : (q ^ (2 * n : ℤ) * z : ℂ) ^ r =
      q ^ ((2 * n) * r) * z ^ r := by
    rw [mul_zpow]
    congr 1
    rw [← zpow_mul]
  have hzsplit : z ^ (r + n) = z ^ r * z ^ n := by
    rw [zpow_add₀ hz]
  have hqsplit :
      q ^ ((2 * n) * r) * q ^ (r ^ 2) =
        q ^ (-(n * n) : ℤ) * q ^ ((r + n) ^ 2) := by
    rw [← zpow_add₀ hq0, ← zpow_add₀ hq0]
    congr 1; ring
  calc
    (q ^ (2 * n : ℤ) * z) ^ r * q ^ (r ^ 2)
        = (q ^ ((2 * n) * r) * z ^ r) * q ^ (r ^ 2) := by rw [hq2n]
      _ = (q ^ ((2 * n) * r) * q ^ (r ^ 2)) * z ^ r := by ring
      _ = (q ^ (-(n * n) : ℤ) * q ^ ((r + n) ^ 2)) * z ^ r := by rw [hqsplit]
      _ = q ^ (-(n * n) : ℤ) * z ^ (-n : ℤ) * (z ^ (r + n) * q ^ ((r + n) ^ 2)) := by
          have hzcancel : z ^ (-n : ℤ) * z ^ (r + n) = z ^ r := by
            rw [← zpow_add₀ hz]; congr 1; ring
          calc
            (q ^ (-(n * n) : ℤ) * q ^ ((r + n) ^ 2)) * z ^ r
                = q ^ (-(n * n) : ℤ) * q ^ ((r + n) ^ 2) *
                    (z ^ (-n : ℤ) * z ^ (r + n)) := by rw [hzcancel]
              _ = q ^ (-(n * n) : ℤ) * z ^ (-n : ℤ) *
                    (z ^ (r + n) * q ^ ((r + n) ^ 2)) := by ring

/-- Sub-lemma 2: Inner JTP + mod-3 residue evaluation. -/
theorem quintuple_theta_kernel_eval
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    (∑' k : ℤ, (-1 : ℂ) ^ k * z ^ k * q ^ (k ^ 2) *
      (∑' s : ℤ, (-1 : ℂ) ^ s * q ^ (6 * s ^ 2 - (4 * k + 2) * s))) =
      (∏' n : ℕ, (1 - q ^ (4 * n + 4))) * quintupleProductRHS q z := by
  classical
  -- Helper: match inner sum to JTP series
  have hI_eq_jtp : ∀ k : ℤ, (∑' s : ℤ, (-1 : ℂ) ^ s * q ^ (6 * s ^ 2 - (4 * k + 2) * s)) =
      Ch02.jacobiInfiniteSeries (q ^ 6) (-(q ^ (-(4 * k + 2) : ℤ))) := by
    intro k
    simp only [Ch02.jacobiInfiniteSeries]
    apply tsum_congr; intro s
    rw [show (-(q ^ (-(4 * k + 2) : ℤ)) : ℂ) = (-1) * q ^ (-(4 * k + 2) : ℤ) from by ring,
        mul_zpow, ← zpow_mul, ← zpow_natCast q 6, ← zpow_mul]
    push_cast
    rw [show (-1 : ℂ) ^ s * q ^ (-(4 * k + 2) * s) * q ^ (6 * s ^ 2) =
        (-1 : ℂ) ^ s * (q ^ (-(4 * k + 2) * s) * q ^ (6 * s ^ 2)) from by ring]
    rw [← zpow_add₀ hq]; congr 1; ring
  set P : ℂ := ∏' n : ℕ, (1 - q ^ (4 * n + 4))
  set I : ℤ → ℂ := fun k => ∑' s : ℤ, (-1 : ℂ) ^ s * q ^ (6 * s ^ 2 - (4 * k + 2) * s)
  -- Helper: factor identity for JTP at (q⁶, -q⁻²)
  have hfactor : ∀ m : ℕ, Ch02.jacobiProductNatFactor (q^6) (-(q^((-2 : ℤ)))) m =
      (1 - q^((12*(m:ℤ)+4))) * (1 - q^((12*(m:ℤ)+8))) * (1 - q^((12*(m:ℤ)+12))) := by
    intro m
    unfold Ch02.jacobiProductNatFactor Ch02.jacobiProductEvenFactor Ch02.jacobiProductOddFactor
    rw [show 2 * (m + 1) - 1 = 2 * m + 1 from by omega,
        show (q ^ 6) ^ (2 * (m + 1)) = q ^ (12 * m + 12) from by rw [← pow_mul]; congr 1; ring,
        show (q ^ 6) ^ (2 * m + 1) = q ^ (12 * m + 6) from by rw [← pow_mul]; congr 1; ring,
        ← zpow_natCast q (12 * m + 12), ← zpow_natCast q (12 * m + 6)]
    push_cast
    have h1 : -(q ^ ((-2 : ℤ))) * q ^ ((12 : ℤ) * ↑m + 6) = -(q ^ ((12 : ℤ) * ↑m + 4)) := by
      have : q ^ ((-2 : ℤ)) * q ^ ((12 : ℤ) * ↑m + 6) = q ^ ((12 : ℤ) * ↑m + 4) := by
        rw [← zpow_add₀ hq]; congr 1; ring
      linear_combination -this
    have h2 : (-(q ^ ((-2 : ℤ))))⁻¹ * q ^ ((12 : ℤ) * ↑m + 6) = -(q ^ ((12 : ℤ) * ↑m + 8)) := by
      rw [inv_neg, zpow_neg, inv_inv]
      have : q ^ (2 : ℤ) * q ^ ((12 : ℤ) * ↑m + 6) = q ^ ((12 : ℤ) * ↑m + 8) := by
        rw [← zpow_add₀ hq]; congr 1; ring
      linear_combination -this
    rw [h1, h2]; ring
  have hq6 : (q^6 : ℂ) ≠ 0 := pow_ne_zero _ hq
  have hq6norm : ‖q^6‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hqnorm (by norm_num)
  have hzneg2_ne : (-(q^((-2 : ℤ))) : ℂ) ≠ 0 := neg_ne_zero.mpr (zpow_ne_zero _ hq)
  -- hfactor stated with Nat exponents
  have hfactor_nat : ∀ m : ℕ, Ch02.jacobiProductNatFactor (q^6) (-(q^((-2 : ℤ)))) m =
      ((1 : ℂ) - q^(12*m+4)) * ((1 : ℂ) - q^(12*m+8)) * ((1 : ℂ) - q^(12*m+12)) := by
    intro m
    rw [hfactor m]
    have h4 : (q : ℂ)^((12 * (m : ℤ) + 4)) = q^(12*m+4 : ℕ) := by
      rw [show (12 * (m : ℤ) + 4) = ((12 * m + 4 : ℕ) : ℤ) from by push_cast; ring]
      exact zpow_natCast q _
    have h8 : (q : ℂ)^((12 * (m : ℤ) + 8)) = q^(12*m+8 : ℕ) := by
      rw [show (12 * (m : ℤ) + 8) = ((12 * m + 8 : ℕ) : ℤ) from by push_cast; ring]
      exact zpow_natCast q _
    have h12 : (q : ℂ)^((12 * (m : ℤ) + 12)) = q^(12*m+12 : ℕ) := by
      rw [show (12 * (m : ℤ) + 12) = ((12 * m + 12 : ℕ) : ℤ) from by push_cast; ring]
      exact zpow_natCast q _
    rw [h4, h8, h12]
  -- I(0) = P
  have hI0_eq_P : Ch02.jacobiInfiniteSeries (q^6) (-(q^((-2 : ℤ)))) = P := by
    rw [← Ch02.jacobiTripleProduct (q^6) _ hq6norm hzneg2_ne,
        Ch02.jacobiInfiniteProduct_eq_tprod_natFactor,
        tprod_congr hfactor_nat]
    have hM4 := multipliable_one_sub_qpow_aff q hqnorm 12 4 (by norm_num)
    have hM8 := multipliable_one_sub_qpow_aff q hqnorm 12 8 (by norm_num)
    have hM12 := multipliable_one_sub_qpow_aff q hqnorm 12 12 (by norm_num)
    rw [(hM4.mul hM8).tprod_mul hM12, hM4.tprod_mul hM8]
    exact qpoch_q4_residue_split q hqnorm
  have hI0 : ∀ n : ℤ, I (3 * n) = (-1 : ℂ) ^ n * q ^ (-(6 * n ^ 2 + 2 * n)) * P := by
    intro n
    show (∑' s : ℤ, (-1 : ℂ) ^ s * q ^ (6 * s^2 - (4 * (3 * n) + 2) * s)) = _
    rw [hI_eq_jtp (3 * n)]
    -- Identify the argument: -q^(-(12n+2):ℤ) = (q^6)^(2*(-n):ℤ) * (-q^(-2:ℤ))
    have harg : (-(q^(-(4 * (3 * n) + 2) : ℤ)) : ℂ) =
        (q^6 : ℂ)^(2 * (-n) : ℤ) * (-(q^((-2 : ℤ)))) := by
      rw [show ((q : ℂ)^6) = q^((6 : ℤ)) from (zpow_natCast q 6).symm, ← zpow_mul,
          show -((q : ℂ)^((-2 : ℤ))) = -1 * q^((-2 : ℤ)) from by ring,
          show -((q : ℂ)^(-(4 * (3 * n) + 2) : ℤ)) =
              -1 * q^(-(4 * (3 * n) + 2) : ℤ) from by ring,
          show ((q : ℂ)^((6 : ℤ) * (2 * -n))) * (-1 * (q : ℂ)^((-2 : ℤ))) =
              -1 * ((q : ℂ)^((6 : ℤ) * (2 * -n)) * q^((-2 : ℤ))) from by ring,
          ← zpow_add₀ hq]
      congr 1; congr 1; ring
    rw [harg, jacobiInfiniteSeries_qsq_iterate_int (q^6) hq6norm hq6
        (-(q^((-2:ℤ)))) hzneg2_ne (-n), hI0_eq_P]
    -- Goal: (q^6)^(-((-n)*(-n))) * (-q^(-2:ℤ))^(-(-n)) * P = (-1)^n * q^(-(6*n²+2*n)) * P
    have h1 : ((q^6 : ℂ))^(-((-n) * (-n)) : ℤ) = q^(-(6 * n^2) : ℤ) := by
      rw [show ((q : ℂ)^6) = q^((6 : ℤ)) from (zpow_natCast q 6).symm,
          ← zpow_mul,
          show ((6 : ℤ) * (-((-n) * (-n)))) = -(6 * n^2) from by ring]
    have h2 : ((-(q^((-2 : ℤ))) : ℂ))^(-(-n) : ℤ) =
        (-1 : ℂ)^n * q^(-(2 * n) : ℤ) := by
      rw [show (-(-n) : ℤ) = n from neg_neg n,
          show ((-(q : ℂ)^((-2 : ℤ))) : ℂ) = (-1 : ℂ) * q^((-2 : ℤ)) from by ring,
          mul_zpow,
          ← zpow_mul,
          show ((-2 : ℤ) * n) = -(2 * n) from by ring]
    rw [h1, h2,
        show (q : ℂ)^(-(6 * n^2) : ℤ) * ((-1 : ℂ)^n * q^(-(2 * n) : ℤ)) =
            (-1 : ℂ)^n * (q^(-(6 * n^2) : ℤ) * q^(-(2 * n) : ℤ)) from by ring,
        ← zpow_add₀ hq,
        show (-(6 * n^2) + -(2 * n) : ℤ) = -(6 * n^2 + 2 * n) from by ring]
  have hI1 : ∀ n : ℤ, I (3 * n + 1) = 0 := by
    intro n
    show ∑' s : ℤ, (-1 : ℂ) ^ s * q ^ (6 * s ^ 2 - (4 * (3 * n + 1) + 2) * s) = 0
    rw [show (4 * (3 * n + 1) + 2 : ℤ) = 12 * n + 6 from by ring]
    set c := 2 * n + 1
    set f₁ := fun s : ℤ => (-1 : ℂ) ^ s * q ^ (6 * s ^ 2 - (12 * n + 6) * s)
    have hmone : (-1 : ℂ) ≠ 0 := by norm_num
    have hflip : ∀ s, f₁ (c - s) = -f₁ s := by
      intro s; dsimp [f₁, c]
      have hexp : 6 * ((2*n+1) - s) ^ 2 - (12 * n + 6) * ((2*n+1) - s) =
          6 * s ^ 2 - (12 * n + 6) * s := by ring
      rw [hexp, show (2*n+1 : ℤ) - s = (2*n+1) + (-s) from by ring, zpow_add₀ hmone, zpow_neg]
      have hcodd : (-1 : ℂ) ^ (2*n+1) = -1 := by
        rw [zpow_add₀ hmone, zpow_mul, show (-1 : ℂ) ^ (2 : ℤ) = 1 from by norm_num, one_zpow]; simp
      have hinv : ((-1 : ℂ) ^ s)⁻¹ = (-1) ^ s :=
        inv_eq_of_mul_eq_one_left (by
          rw [← zpow_add₀ hmone, show s + s = 2 * s from by ring, zpow_mul,
              show (-1 : ℂ) ^ (2 : ℤ) = 1 from by norm_num, one_zpow])
      rw [hcodd, hinv]; ring
    have h : (∑' s, f₁ s) = -(∑' s, f₁ s) := by
      conv_lhs => rw [← (Equiv.subLeft c).tsum_eq f₁]
      simp only [Equiv.subLeft_apply, hflip, tsum_neg]
    have h2 : 2 * (∑' s, f₁ s) = 0 := by linear_combination (∑' s, f₁ s) + h
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num : (2 : ℂ) ≠ 0)
  have hI2 : ∀ n : ℤ, I (3 * n + 2) =
      (-1 : ℂ) ^ (n + 1) * q ^ (-(6 * n ^ 2 + 10 * n + 4)) * P := by
    have hzpos2_ne : (-(q^((2 : ℤ))) : ℂ) ≠ 0 := neg_ne_zero.mpr (zpow_ne_zero _ hq)
    -- hfactor analog for (q^6, -q²): same factorization as hfactor_nat but with positive z exponent
    have hfactor_pos_nat : ∀ m : ℕ,
        Ch02.jacobiProductNatFactor (q^6) (-(q^((2 : ℤ)))) m =
          ((1 : ℂ) - q^(12*m+4)) * ((1 : ℂ) - q^(12*m+8)) * ((1 : ℂ) - q^(12*m+12)) := by
      intro m
      unfold Ch02.jacobiProductNatFactor Ch02.jacobiProductEvenFactor
        Ch02.jacobiProductOddFactor
      rw [show 2 * (m + 1) - 1 = 2 * m + 1 from by omega,
          show (q^6 : ℂ)^(2*(m+1)) = q^(12*m+12) from by rw [← pow_mul]; congr 1; ring,
          show (q^6 : ℂ)^(2*m+1) = q^(12*m+6) from by rw [← pow_mul]; congr 1; ring,
          ← zpow_natCast q (12*m+12), ← zpow_natCast q (12*m+6)]
      push_cast
      have h1 : -((q : ℂ)^((2 : ℤ))) * (q : ℂ)^((12 : ℤ)*↑m + 6) =
          -((q : ℂ)^((12 : ℤ)*↑m + 8)) := by
        have : (q : ℂ)^((2 : ℤ)) * (q : ℂ)^((12 : ℤ)*↑m + 6) =
            (q : ℂ)^((12 : ℤ)*↑m + 8) := by
          rw [← zpow_add₀ hq]; congr 1; ring
        linear_combination -this
      have h2 : (-((q : ℂ)^((2 : ℤ))))⁻¹ * (q : ℂ)^((12 : ℤ)*↑m + 6) =
          -((q : ℂ)^((12 : ℤ)*↑m + 4)) := by
        rw [inv_neg, ← zpow_neg]
        have : (q : ℂ)^(-(2 : ℤ)) * (q : ℂ)^((12 : ℤ)*↑m + 6) =
            (q : ℂ)^((12 : ℤ)*↑m + 4) := by
          rw [← zpow_add₀ hq]; congr 1; ring
        linear_combination -this
      rw [h1, h2]
      have h4 : (q : ℂ)^((12 * (m : ℤ) + 4)) = q^(12*m+4 : ℕ) := by
        rw [show (12 * (m : ℤ) + 4) = ((12 * m + 4 : ℕ) : ℤ) from by push_cast; ring]
        exact zpow_natCast q _
      have h8 : (q : ℂ)^((12 * (m : ℤ) + 8)) = q^(12*m+8 : ℕ) := by
        rw [show (12 * (m : ℤ) + 8) = ((12 * m + 8 : ℕ) : ℤ) from by push_cast; ring]
        exact zpow_natCast q _
      have h12 : (q : ℂ)^((12 * (m : ℤ) + 12)) = q^(12*m+12 : ℕ) := by
        rw [show (12 * (m : ℤ) + 12) = ((12 * m + 12 : ℕ) : ℤ) from by push_cast; ring]
        exact zpow_natCast q _
      rw [h4, h8, h12]
      ring
    -- JTP(q^6, -q²) = P (analog of hI0_eq_P at the negative shift origin)
    have hI_neg1_eq_P : Ch02.jacobiInfiniteSeries (q^6) (-(q^((2 : ℤ)))) = P := by
      rw [← Ch02.jacobiTripleProduct (q^6) _ hq6norm hzpos2_ne,
          Ch02.jacobiInfiniteProduct_eq_tprod_natFactor,
          tprod_congr hfactor_pos_nat]
      have hM4 := multipliable_one_sub_qpow_aff q hqnorm 12 4 (by norm_num)
      have hM8 := multipliable_one_sub_qpow_aff q hqnorm 12 8 (by norm_num)
      have hM12 := multipliable_one_sub_qpow_aff q hqnorm 12 12 (by norm_num)
      rw [(hM4.mul hM8).tprod_mul hM12, hM4.tprod_mul hM8]
      exact qpoch_q4_residue_split q hqnorm
    -- Now the main hI2 body.
    intro n
    show (∑' s : ℤ, (-1 : ℂ) ^ s * q ^ (6 * s^2 - (4 * (3 * n + 2) + 2) * s)) = _
    rw [hI_eq_jtp (3 * n + 2)]
    have harg : (-(q^(-(4 * (3 * n + 2) + 2) : ℤ)) : ℂ) =
        (q^6 : ℂ)^(2 * (-(n+1)) : ℤ) * (-(q^((2 : ℤ)))) := by
      rw [show ((q : ℂ)^6) = q^((6 : ℤ)) from (zpow_natCast q 6).symm, ← zpow_mul,
          show -((q : ℂ)^((2 : ℤ))) = -1 * q^((2 : ℤ)) from by ring,
          show -((q : ℂ)^(-(4 * (3 * n + 2) + 2) : ℤ)) =
              -1 * q^(-(4 * (3 * n + 2) + 2) : ℤ) from by ring,
          show ((q : ℂ)^((6 : ℤ) * (2 * -(n+1)))) * (-1 * (q : ℂ)^((2 : ℤ))) =
              -1 * ((q : ℂ)^((6 : ℤ) * (2 * -(n+1))) * q^((2 : ℤ))) from by ring,
          ← zpow_add₀ hq]
      congr 1; congr 1; ring
    rw [harg, jacobiInfiniteSeries_qsq_iterate_int (q^6) hq6norm hq6
        (-(q^((2:ℤ)))) hzpos2_ne (-(n+1)), hI_neg1_eq_P]
    have h1 : ((q^6 : ℂ))^(-((-(n+1)) * (-(n+1))) : ℤ) =
        q^(-(6 * (n+1)^2) : ℤ) := by
      rw [show ((q : ℂ)^6) = q^((6 : ℤ)) from (zpow_natCast q 6).symm, ← zpow_mul,
          show ((6 : ℤ) * (-((-(n+1)) * (-(n+1))))) = -(6 * (n+1)^2) from by ring]
    have h2 : ((-(q^((2 : ℤ))) : ℂ))^(-(-(n+1)) : ℤ) =
        (-1 : ℂ)^(n+1) * q^(2 * (n+1) : ℤ) := by
      rw [show (-(-(n+1)) : ℤ) = (n+1) from neg_neg _,
          show ((-(q : ℂ)^((2 : ℤ))) : ℂ) = (-1 : ℂ) * q^((2 : ℤ)) from by ring,
          mul_zpow,
          ← zpow_mul]
    rw [h1, h2,
        show (q : ℂ)^(-(6 * (n+1)^2) : ℤ) * ((-1 : ℂ)^(n+1) * q^(2 * (n+1) : ℤ)) =
            (-1 : ℂ)^(n+1) * (q^(-(6 * (n+1)^2) : ℤ) * q^(2 * (n+1) : ℤ)) from by ring,
        ← zpow_add₀ hq,
        show (-(6 * (n+1)^2) + 2 * (n+1) : ℤ) = -(6 * n^2 + 10 * n + 4) from by ring]
  have hsplit : (∑' k : ℤ, (-1 : ℂ) ^ k * z ^ k * q ^ (k ^ 2) * I k) =
      P * (∑' n : ℤ, quintupleProductSeriesTerm q z n) := by
    classical
    set F : ℤ → ℂ := fun k => (-1 : ℂ) ^ k * z ^ k * q ^ (k ^ 2) * I k with hFdef
    set A : ℤ → ℂ := fun n => (z ^ 3 / q ^ 2) ^ n * (q ^ 3) ^ (n ^ 2) with hAdef
    set B : ℤ → ℂ := fun n => (q / z) * ((q ^ 4 / z ^ 3) ^ n * (q ^ 3) ^ (n ^ 2)) with hBdef
    have hq3norm : ‖q ^ 3‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg q) hqnorm (by norm_num)
    have hA_summ : Summable A :=
      Ch02.summable_jacobiInfiniteSeries_terms (q ^ 3) (z ^ 3 / q ^ 2) hq3norm
    have hB_summ : Summable B :=
      (Ch02.summable_jacobiInfiniteSeries_terms (q ^ 3) (q ^ 4 / z ^ 3) hq3norm).mul_left (q / z)
    -- Algebraic identities
    have hA_alg : ∀ n : ℤ, A n = z ^ (3 * n) * q ^ (3 * n ^ 2 - 2 * n) := by
      intro n
      show (z ^ 3 / q ^ 2) ^ n * (q ^ 3) ^ (n ^ 2) = _
      have hz3 : (z ^ 3 : ℂ) ^ n = z ^ (3 * n) := by
        simpa using (zpow_mul z (3 : ℤ) n).symm
      have hq2 : (q ^ 2 : ℂ) ^ n = q ^ (2 * n) := by
        simpa using (zpow_mul q (2 : ℤ) n).symm
      have hq3 : (q ^ 3 : ℂ) ^ (n ^ 2) = q ^ (3 * n ^ 2) := by
        simpa using (zpow_mul q (3 : ℤ) (n ^ 2)).symm
      rw [div_zpow, hz3, hq2, hq3]
      rw [show z ^ (3 * n) / q ^ (2 * n) * q ^ (3 * n ^ 2)
          = z ^ (3 * n) * (q ^ (3 * n ^ 2) / q ^ (2 * n)) by ring]
      rw [← zpow_sub₀ hq]
    have hB_alg_shift : ∀ n : ℤ,
        B (-n - 1) = z ^ (3 * n + 2) * q ^ (3 * n ^ 2 + 2 * n) := by
      intro n
      show (q / z) * ((q ^ 4 / z ^ 3) ^ (-n - 1) * (q ^ 3) ^ ((-n - 1) ^ 2)) = _
      have hq4 : (q ^ 4 : ℂ) ^ (-n - 1) = q ^ (4 * (-n - 1)) := by
        simpa using (zpow_mul q (4 : ℤ) (-n - 1)).symm
      have hz3 : (z ^ 3 : ℂ) ^ (-n - 1) = z ^ (3 * (-n - 1)) := by
        simpa using (zpow_mul z (3 : ℤ) (-n - 1)).symm
      have hq3 : (q ^ 3 : ℂ) ^ ((-n - 1) ^ 2) = q ^ (3 * ((-n - 1) ^ 2)) := by
        simpa using (zpow_mul q (3 : ℤ) ((-n - 1) ^ 2)).symm
      rw [div_zpow, hq4, hz3, hq3]
      have hqz : (q / z : ℂ) = q ^ (1 : ℤ) * z ^ (-1 : ℤ) := by
        rw [zpow_one, zpow_neg_one]; rfl
      rw [hqz]
      rw [show
          q ^ (1 : ℤ) * z ^ (-1 : ℤ) *
              ((q ^ (4 * (-n - 1)) / z ^ (3 * (-n - 1))) *
                q ^ (3 * ((-n - 1) ^ 2))) =
            (q ^ (1 : ℤ) * q ^ (4 * (-n - 1)) * q ^ (3 * ((-n - 1) ^ 2))) *
              (z ^ (-1 : ℤ) * (z ^ (3 * (-n - 1)))⁻¹) by ring]
      rw [← zpow_neg, ← zpow_add₀ hq, ← zpow_add₀ hq, ← zpow_add₀ hz]
      rw [show ((1 : ℤ) + 4 * (-n - 1) + 3 * (-n - 1) ^ 2 : ℤ) = 3 * n ^ 2 + 2 * n from by ring,
          show ((-1 : ℤ) + -(3 * (-n - 1)) : ℤ) = 3 * n + 2 from by ring]
      ring
    -- F values per residue class.
    have hF0 : ∀ n : ℤ, F (3 * n) = P * A n := by
      intro n
      show (-1 : ℂ) ^ (3 * n) * z ^ (3 * n) * q ^ ((3 * n) ^ 2) * I (3 * n) = P * A n
      rw [hI0 n, hA_alg n]
      have hm : (-1 : ℂ) ≠ 0 := by norm_num
      have hsgn : (-1 : ℂ) ^ (3 * n) * (-1 : ℂ) ^ n = 1 := by
        rw [← zpow_add₀ hm]
        have he : Even (3 * n + n) := ⟨2 * n, by ring⟩
        simpa [neg_one_zpow_eq_ite, he]
      have hqpow :
          q ^ ((3 * n) ^ 2) * q ^ (-(6 * n ^ 2 + 2 * n)) = q ^ (3 * n ^ 2 - 2 * n) := by
        rw [← zpow_add₀ hq]; congr 1; ring
      calc
        (-1 : ℂ) ^ (3 * n) * z ^ (3 * n) * q ^ ((3 * n) ^ 2) *
            ((-1 : ℂ) ^ n * q ^ (-(6 * n ^ 2 + 2 * n)) * P)
            = ((-1 : ℂ) ^ (3 * n) * (-1 : ℂ) ^ n) * z ^ (3 * n) *
                (q ^ ((3 * n) ^ 2) * q ^ (-(6 * n ^ 2 + 2 * n))) * P := by ring
          _ = z ^ (3 * n) * q ^ (3 * n ^ 2 - 2 * n) * P := by rw [hsgn, hqpow]; ring
          _ = P * (z ^ (3 * n) * q ^ (3 * n ^ 2 - 2 * n)) := by ring
    have hF1 : ∀ n : ℤ, F (3 * n + 1) = 0 := by
      intro n
      show (-1 : ℂ) ^ (3 * n + 1) * z ^ (3 * n + 1) * q ^ ((3 * n + 1) ^ 2) * I (3 * n + 1) = 0
      rw [hI1 n]; ring
    have hF2 : ∀ n : ℤ, F (3 * n + 2) = P * (-B (-n - 1)) := by
      intro n
      show (-1 : ℂ) ^ (3 * n + 2) * z ^ (3 * n + 2) * q ^ ((3 * n + 2) ^ 2) *
          I (3 * n + 2) = _
      rw [hI2 n, hB_alg_shift n]
      have hm : (-1 : ℂ) ≠ 0 := by norm_num
      have hsgn : (-1 : ℂ) ^ (3 * n + 2) * (-1 : ℂ) ^ (n + 1) = -1 := by
        rw [← zpow_add₀ hm]
        have hodd : ¬ Even (3 * n + 2 + (n + 1)) := by
          rintro ⟨a, ha⟩; omega
        simpa [neg_one_zpow_eq_ite, hodd]
      have hqpow :
          q ^ ((3 * n + 2) ^ 2) * q ^ (-(6 * n ^ 2 + 10 * n + 4)) = q ^ (3 * n ^ 2 + 2 * n) := by
        rw [← zpow_add₀ hq]; congr 1; ring
      calc
        (-1 : ℂ) ^ (3 * n + 2) * z ^ (3 * n + 2) * q ^ ((3 * n + 2) ^ 2) *
            ((-1 : ℂ) ^ (n + 1) * q ^ (-(6 * n ^ 2 + 10 * n + 4)) * P)
            = ((-1 : ℂ) ^ (3 * n + 2) * (-1 : ℂ) ^ (n + 1)) * z ^ (3 * n + 2) *
                (q ^ ((3 * n + 2) ^ 2) * q ^ (-(6 * n ^ 2 + 10 * n + 4))) * P := by ring
          _ = -(z ^ (3 * n + 2) * q ^ (3 * n ^ 2 + 2 * n)) * P := by rw [hsgn, hqpow]; ring
          _ = P * -(z ^ (3 * n + 2) * q ^ (3 * n ^ 2 + 2 * n)) := by ring
    -- HasSum on each coset.
    have hSum0 : HasSum (fun n : ℤ => F (3 * n)) (P * ∑' n, A n) :=
      (hA_summ.hasSum.mul_left P).congr_fun fun n => hF0 n
    have hSum1 : HasSum (fun n : ℤ => F (3 * n + 1)) 0 :=
      (hasSum_zero : HasSum (fun _ : ℤ => (0 : ℂ)) 0).congr_fun fun n => hF1 n
    -- Shift equiv for the -B(-n-1) sum.
    let eShift : ℤ ≃ ℤ :=
      { toFun := fun n => -n - 1
        invFun := fun n => -n - 1
        left_inv := by intro n; ring
        right_inv := by intro n; ring }
    have hShiftSum : HasSum (fun n : ℤ => -B (-n - 1)) (∑' n, -B n) := by
      have hBneg : HasSum (fun n : ℤ => -B n) (∑' n, -B n) := hB_summ.neg.hasSum
      exact (eShift.hasSum_iff (f := fun n : ℤ => -B n)).mpr hBneg
    have hSum2 : HasSum (fun n : ℤ => F (3 * n + 2)) (P * ∑' n, -B n) :=
      (hShiftSum.mul_left P).congr_fun fun n => hF2 n
    -- Equiv ℤ × Fin 3 ≃ ℤ ⊕ (ℤ ⊕ ℤ) and combination with Int.divModEquiv 3.
    let prodFin3ToSum : ℤ × Fin 3 ≃ ℤ ⊕ (ℤ ⊕ ℤ) :=
      { toFun := fun p => match p.2 with
          | 0 => Sum.inl p.1
          | 1 => Sum.inr (Sum.inl p.1)
          | 2 => Sum.inr (Sum.inr p.1)
        invFun := fun
          | Sum.inl n => (n, 0)
          | Sum.inr (Sum.inl n) => (n, 1)
          | Sum.inr (Sum.inr n) => (n, 2)
        left_inv := fun ⟨n, r⟩ => by fin_cases r <;> rfl
        right_inv := fun x => by rcases x with n | (n | n) <;> rfl }
    let cosetEquiv : ℤ ≃ ℤ ⊕ (ℤ ⊕ ℤ) := (Int.divModEquiv 3).trans prodFin3ToSum
    -- The Sum.elim function expressing F on cosets.
    set Fsum : ℤ ⊕ (ℤ ⊕ ℤ) → ℂ :=
      Sum.elim (fun n => F (3 * n))
        (Sum.elim (fun n => F (3 * n + 1)) (fun n => F (3 * n + 2))) with hFsumDef
    -- HasSum Fsum via two HasSum.sum:
    have hSumInner : HasSum
        (Sum.elim (fun n : ℤ => F (3 * n + 1)) (fun n : ℤ => F (3 * n + 2)))
        (0 + P * ∑' n, -B n) :=
      HasSum.sum (f := Sum.elim _ _) hSum1 hSum2
    have hSumFsum : HasSum Fsum
        ((P * ∑' n, A n) + (0 + P * ∑' n, -B n)) :=
      HasSum.sum (f := Sum.elim _ _) hSum0 hSumInner
    -- Identify Fsum with F ∘ cosetEquiv.
    have hFcompEq : ∀ x : ℤ ⊕ (ℤ ⊕ ℤ), F (cosetEquiv.symm x) = Fsum x := by
      intro x
      rcases x with n | (n | n)
      · show F (cosetEquiv.symm (Sum.inl n)) = F (3 * n)
        show F ((Int.divModEquiv 3).symm (n, 0)) = F (3 * n)
        congr 1
        show n * 3 + ((0 : Fin 3) : ℤ) = 3 * n
        simp; ring
      · show F (cosetEquiv.symm (Sum.inr (Sum.inl n))) = F (3 * n + 1)
        show F ((Int.divModEquiv 3).symm (n, 1)) = F (3 * n + 1)
        congr 1
        show n * 3 + ((1 : Fin 3) : ℤ) = 3 * n + 1
        simp; ring
      · show F (cosetEquiv.symm (Sum.inr (Sum.inr n))) = F (3 * n + 2)
        show F ((Int.divModEquiv 3).symm (n, 2)) = F (3 * n + 2)
        congr 1
        show n * 3 + ((2 : Fin 3) : ℤ) = 3 * n + 2
        simp; ring
    -- Transfer HasSum to F.
    have hSumF : HasSum F ((P * ∑' n, A n) + (0 + P * ∑' n, -B n)) := by
      have hcomp : HasSum (fun x => F (cosetEquiv.symm x))
          ((P * ∑' n, A n) + (0 + P * ∑' n, -B n)) :=
        hSumFsum.congr_fun hFcompEq
      exact (cosetEquiv.symm.hasSum_iff (f := F)).mp hcomp
    have hLHS : (∑' k : ℤ, F k) = (P * ∑' n, A n) + (0 + P * ∑' n, -B n) := hSumF.tsum_eq
    have hterm : (∑' n : ℤ, quintupleProductSeriesTerm q z n) =
        (∑' n, A n) + (∑' n, -B n) := by
      have hsum : HasSum (fun n : ℤ => A n + (-B n)) ((∑' n, A n) + (∑' n, -B n)) :=
        hA_summ.hasSum.add hB_summ.neg.hasSum
      have hcongr : ∀ n : ℤ, quintupleProductSeriesTerm q z n = A n + (-B n) := by
        intro n
        show (z ^ 3 / q ^ 2) ^ n * (q ^ 3) ^ (n ^ 2) -
            (q / z) * ((q ^ 4 / z ^ 3) ^ n * (q ^ 3) ^ (n ^ 2)) = _
        ring
      exact (hsum.congr_fun hcongr).tsum_eq
    calc
      (∑' k : ℤ, (-1 : ℂ) ^ k * z ^ k * q ^ (k ^ 2) * I k)
          = ∑' k : ℤ, F k := by simp [F]
        _ = (P * ∑' n, A n) + (0 + P * ∑' n, -B n) := hLHS
        _ = P * ((∑' n, A n) + (∑' n, -B n)) := by ring
        _ = P * (∑' n : ℤ, quintupleProductSeriesTerm q z n) := by rw [hterm]
  calc (∑' k : ℤ, (-1 : ℂ) ^ k * z ^ k * q ^ (k ^ 2) *
      (∑' s : ℤ, (-1 : ℂ) ^ s * q ^ (6 * s ^ 2 - (4 * k + 2) * s)))
      = ∑' k : ℤ, (-1 : ℂ) ^ k * z ^ k * q ^ (k ^ 2) * I k := by simp [I]
    _ = P * (∑' n : ℤ, quintupleProductSeriesTerm q z n) := hsplit
    _ = (∏' n : ℕ, (1 - q ^ (4 * n + 4))) * quintupleProductRHS q z := by
        simp [P, quintupleProductRHS]

/-- The double bilateral product equals `(q⁴;q⁴)_∞` times the quintuple RHS.
This is the core identity: the product of two JTP series, after Cauchy product
+ reindexing + mod-3 regrouping, gives `(q⁴;q⁴)_∞ * quintupleRHS`. -/
theorem jacobiSeries_mul_eq_qPoch_mul_quintupleRHS
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    Ch02.jacobiInfiniteSeries q (-z) *
      Ch02.jacobiInfiniteSeries (q ^ 2) (-(z ^ 2 / q ^ 2)) =
      (∏' n : ℕ, (1 - q ^ (4 * n + 4))) * quintupleProductRHS q z := by
  simp only [Ch02.jacobiInfiniteSeries]
  exact (quintuple_double_sum_shear q z hqnorm hq hz).trans
    (quintuple_theta_kernel_eval q z hqnorm hq hz)

/-- **Theorem 4.4 (Quintuple Product Identity)**. -/
theorem quintupleProduct_identity (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    quintupleProductLHS q z = quintupleProductRHS q z := by
  have hprod := quintupleProductLHS_mul_qPoch_eq_series_mul q z hqnorm hq hz
  have hdouble := jacobiSeries_mul_eq_qPoch_mul_quintupleRHS q z hqnorm hq hz
  have hqPoch_ne : (∏' n : ℕ, (1 - q ^ (4 * n + 4))) ≠ 0 := by
    rw [show (fun n : ℕ => (1 : ℂ) - q ^ (4 * n + 4)) = (fun n => 1 + (-(q ^ (4 * n + 4)))) from
      funext fun n => by ring]
    apply tprod_one_add_ne_zero_of_summable
    · intro n
      rw [show (1 : ℂ) + -(q ^ (4 * n + 4)) = 1 - q ^ (4 * n + 4) from by ring]
      apply sub_ne_zero.mpr; intro heq
      have h1 : ‖q‖ ^ (4 * n + 4) = 1 := by
        have := congr_arg (‖·‖) heq.symm; simp [norm_pow] at this; exact this
      linarith [pow_lt_one₀ (norm_nonneg q) hqnorm (show 4 * n + 4 ≠ 0 by omega)]
    · simp only [norm_neg, norm_pow]
      have hq4 : ‖q‖ ^ 4 < 1 := pow_lt_one₀ (norm_nonneg q) hqnorm (by norm_num)
      refine ((summable_geometric_of_lt_one (by positivity) hq4).mul_left
        (‖q‖ ^ 4)).congr fun n => ?_
      rw [show ‖q‖ ^ (4 * n + 4) = ‖q‖ ^ 4 * (‖q‖ ^ 4) ^ n from by
        rw [show 4 * n + 4 = 4 + 4 * n from by ring, pow_add, pow_mul]]
  have hkey : quintupleProductLHS q z * (∏' n : ℕ, (1 - q ^ (4 * n + 4))) =
      (∏' n : ℕ, (1 - q ^ (4 * n + 4))) * quintupleProductRHS q z :=
    hprod.trans hdouble
  rw [mul_comm (quintupleProductLHS q z)] at hkey
  exact mul_left_cancel₀ hqPoch_ne hkey

-- Remove old final assembly that needed hqPoch_ne
-- (no longer needed since we use the finite identity route)

end QuintupleAssembly

/- Theorem 4.3 (Jacobi's identity) lives in `Chapter04_T43.lean`. -/

end Ch04
end PartI
end QseriesFormalization
