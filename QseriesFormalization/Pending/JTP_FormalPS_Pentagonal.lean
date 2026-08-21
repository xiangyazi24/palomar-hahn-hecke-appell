import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import QseriesFormalization.Chapter04

/-!
# Formal power-series shells for the mod-5 JTP pentagonal specialisations

This pending file isolates the formal objects for Hirschhorn's two
mod-5 Jacobi-triple-product specialisations.  The full analytic-to-formal
coefficient bridge is not asserted here; all declarations below are fully
proved.
-/

namespace QseriesFormalization
namespace Pending
namespace JTPFormalPSPentagonal

open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology

/-! ## Formal AP products -/

/-- The formal factor `1 - X^(r + m n)`. -/
noncomputable def apFactorPS (R : Type*) [CommRing R] (r m n : ℕ) : R⟦X⟧ :=
  (1 : R⟦X⟧) - PowerSeries.X ^ (r + m * n)

@[simp] theorem apFactorPS_def (R : Type*) [CommRing R] (r m n : ℕ) :
    apFactorPS R r m n = (1 : R⟦X⟧) - PowerSeries.X ^ (r + m * n) := rfl

/-- The formal AP product `(q^r;q^m)_∞ = ∏_{n≥0} (1 - X^(r+mn))`. -/
noncomputable def qPochAPPS (R : Type*) [CommRing R] [TopologicalSpace R]
    (r m : ℕ) : R⟦X⟧ :=
  ∏' n : ℕ, apFactorPS R r m n

/-- The AP product is multipliable when the step is positive. -/
theorem multipliable_apFactorPS (R : Type*) [CommRing R] [TopologicalSpace R]
    (r m : ℕ) (hm : 0 < m) :
    Multipliable fun n : ℕ => apFactorPS R r m n := by
  nontriviality R
  simp_rw [apFactorPS, sub_eq_add_neg]
  apply PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun k =>
    Filter.eventually_atTop.mpr ⟨k + 1, ?_⟩
  intro n hn
  rw [PowerSeries.order_neg, PowerSeries.order_X_pow]
  norm_cast
  have hm1 : 1 ≤ m := Nat.succ_le_iff.mpr hm
  calc
    k < n := by omega
    _ ≤ m * n := Nat.le_mul_of_pos_left n hm1
    _ ≤ r + m * n := Nat.le_add_left _ _

/-- HasProd form of `qPochAPPS`. -/
theorem hasProd_qPochAPPS (R : Type*) [CommRing R] [TopologicalSpace R]
    (r m : ℕ) (hm : 0 < m) :
    HasProd (fun n : ℕ => apFactorPS R r m n) (qPochAPPS R r m) :=
  (multipliable_apFactorPS R r m hm).hasProd

/-- Finite partial products converge to `qPochAPPS`. -/
theorem tendsto_qPochAPPS_partial (R : Type*) [CommRing R] [TopologicalSpace R]
    (r m : ℕ) (hm : 0 < m) :
    Tendsto (fun N : ℕ => ∏ n ∈ Finset.range N, apFactorPS R r m n) atTop
      (𝓝 (qPochAPPS R r m)) :=
  (multipliable_apFactorPS R r m hm).tendsto_prod_tprod_nat

/-- `(q,q^4,q^5;q^5)_∞` as a formal power series. -/
noncomputable def pentagonalProduct014PS
    (R : Type*) [CommRing R] [TopologicalSpace R] : R⟦X⟧ :=
  qPochAPPS R 1 5 * qPochAPPS R 4 5 * qPochAPPS R 5 5

/-- `(q^2,q^3,q^5;q^5)_∞` as a formal power series. -/
noncomputable def pentagonalProduct023PS
    (R : Type*) [CommRing R] [TopologicalSpace R] : R⟦X⟧ :=
  qPochAPPS R 2 5 * qPochAPPS R 3 5 * qPochAPPS R 5 5

/-- The per-`n` triple factor for `(q,q^4,q^5;q^5)_∞`. -/
noncomputable def pentagonalTripleFactor014PS (R : Type*) [CommRing R] (n : ℕ) : R⟦X⟧ :=
  apFactorPS R 1 5 n * apFactorPS R 4 5 n * apFactorPS R 5 5 n

/-- The per-`n` triple factor for `(q^2,q^3,q^5;q^5)_∞`. -/
noncomputable def pentagonalTripleFactor023PS (R : Type*) [CommRing R] (n : ℕ) : R⟦X⟧ :=
  apFactorPS R 2 5 n * apFactorPS R 3 5 n * apFactorPS R 5 5 n

/-- HasProd form of the first mod-5 triple product. -/
theorem hasProd_pentagonalTripleFactor014PS
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    HasProd (fun n : ℕ => pentagonalTripleFactor014PS R n)
      (pentagonalProduct014PS R) := by
  unfold pentagonalProduct014PS pentagonalTripleFactor014PS
  exact ((hasProd_qPochAPPS R 1 5 (by norm_num)).mul
    (hasProd_qPochAPPS R 4 5 (by norm_num))).mul
    (hasProd_qPochAPPS R 5 5 (by norm_num))

/-- HasProd form of the second mod-5 triple product. -/
theorem hasProd_pentagonalTripleFactor023PS
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    HasProd (fun n : ℕ => pentagonalTripleFactor023PS R n)
      (pentagonalProduct023PS R) := by
  unfold pentagonalProduct023PS pentagonalTripleFactor023PS
  exact ((hasProd_qPochAPPS R 2 5 (by norm_num)).mul
    (hasProd_qPochAPPS R 3 5 (by norm_num))).mul
    (hasProd_qPochAPPS R 5 5 (by norm_num))

/-- Tprod form of the first mod-5 triple product. -/
theorem pentagonalProduct014PS_eq_tprod
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    pentagonalProduct014PS R = ∏' n : ℕ, pentagonalTripleFactor014PS R n :=
  (hasProd_pentagonalTripleFactor014PS R).tprod_eq.symm

/-- Tprod form of the second mod-5 triple product. -/
theorem pentagonalProduct023PS_eq_tprod
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    pentagonalProduct023PS R = ∏' n : ℕ, pentagonalTripleFactor023PS R n :=
  (hasProd_pentagonalTripleFactor023PS R).tprod_eq.symm

/-! ## Formal bilateral series coefficients -/

/-- The integer exponent `(5k² - 3k)/2`, coerced to `Nat`. -/
def pentagonal014Exp (k : ℤ) : ℕ :=
  (k * (5 * k - 3) / 2).toNat

/-- The integer exponent `(5k² - k)/2`, coerced to `Nat`. -/
def pentagonal023Exp (k : ℤ) : ℕ :=
  (k * (5 * k - 1) / 2).toNat

/-- The sign `(-1)^k`, represented over an arbitrary commutative ring. -/
def negOnePowInt (R : Type*) [CommRing R] (k : ℤ) : R :=
  (-1 : R) ^ k.natAbs

/-- Coefficient of `X^n` in the first bilateral pentagonal AP series. -/
noncomputable def pentagonal014Coeff (R : Type*) [CommRing R] (n : ℕ) : R :=
  ∑ k ∈ Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ),
    if pentagonal014Exp k = n then negOnePowInt R k else 0

/-- Coefficient of `X^n` in the second bilateral pentagonal AP series. -/
noncomputable def pentagonal023Coeff (R : Type*) [CommRing R] (n : ℕ) : R :=
  ∑ k ∈ Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ),
    if pentagonal023Exp k = n then negOnePowInt R k else 0

/-- Formal series `∑_{k∈ℤ} (-1)^k X^((5k²-3k)/2)`. -/
noncomputable def pentagonal014SeriesPS (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.mk (pentagonal014Coeff R)

/-- Formal series `∑_{k∈ℤ} (-1)^k X^((5k²-k)/2)`. -/
noncomputable def pentagonal023SeriesPS (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.mk (pentagonal023Coeff R)

@[simp] theorem coeff_pentagonal014SeriesPS
    (R : Type*) [CommRing R] (n : ℕ) :
    (pentagonal014SeriesPS R).coeff n = pentagonal014Coeff R n := by
  unfold pentagonal014SeriesPS
  rw [PowerSeries.coeff_mk]

@[simp] theorem coeff_pentagonal023SeriesPS
    (R : Type*) [CommRing R] (n : ℕ) :
    (pentagonal023SeriesPS R).coeff n = pentagonal023Coeff R n := by
  unfold pentagonal023SeriesPS
  rw [PowerSeries.coeff_mk]

/-! ## Bilateral theta analytic-to-formal bridge -/

lemma pentagonal014Exp_nonneg_int (k : ℤ) :
    0 ≤ k * (5 * k - 3) / 2 := by
  have hnum : 0 ≤ k * (5 * k - 3) := by
    by_cases hk : 0 ≤ k
    · by_cases hk0 : k = 0
      · simp [hk0]
      · have hkpos : 1 ≤ k := by omega
        have hfac : 0 ≤ 5 * k - 3 := by nlinarith
        exact mul_nonneg hk hfac
    · have hk_nonpos : k ≤ 0 := by omega
      have hfac : 5 * k - 3 ≤ 0 := by nlinarith
      exact mul_nonneg_of_nonpos_of_nonpos hk_nonpos hfac
  exact Int.ediv_nonneg hnum (by norm_num)

lemma pentagonal023Exp_nonneg_int (k : ℤ) :
    0 ≤ k * (5 * k - 1) / 2 := by
  have hnum : 0 ≤ k * (5 * k - 1) := by
    by_cases hk : 0 ≤ k
    · by_cases hk0 : k = 0
      · simp [hk0]
      · have hkpos : 1 ≤ k := by omega
        have hfac : 0 ≤ 5 * k - 1 := by nlinarith
        exact mul_nonneg hk hfac
    · have hk_nonpos : k ≤ 0 := by omega
      have hfac : 5 * k - 1 ≤ 0 := by nlinarith
      exact mul_nonneg_of_nonpos_of_nonpos hk_nonpos hfac
  exact Int.ediv_nonneg hnum (by norm_num)

lemma int_coe_pentagonal014Exp (k : ℤ) :
    (pentagonal014Exp k : ℤ) = k * (5 * k - 3) / 2 := by
  unfold pentagonal014Exp
  exact Int.toNat_of_nonneg (pentagonal014Exp_nonneg_int k)

lemma int_coe_pentagonal023Exp (k : ℤ) :
    (pentagonal023Exp k : ℤ) = k * (5 * k - 1) / 2 := by
  unfold pentagonal023Exp
  exact Int.toNat_of_nonneg (pentagonal023Exp_nonneg_int k)

lemma pentagonal014Exp_bound_pos (k : ℤ) (hk : 0 ≤ k) :
    k ≤ k * (5 * k - 3) / 2 := by
  rw [Int.le_ediv_iff_mul_le (by norm_num : (0 : ℤ) < 2)]
  by_cases hk0 : k = 0
  · simp [hk0]
  · have hkpos : 1 ≤ k := by omega
    nlinarith

lemma pentagonal014Exp_bound_neg (k : ℤ) (hk : k ≤ 0) :
    -k ≤ k * (5 * k - 3) / 2 := by
  rw [Int.le_ediv_iff_mul_le (by norm_num : (0 : ℤ) < 2)]
  nlinarith

lemma pentagonal023Exp_bound_pos (k : ℤ) (hk : 0 ≤ k) :
    k ≤ k * (5 * k - 1) / 2 := by
  rw [Int.le_ediv_iff_mul_le (by norm_num : (0 : ℤ) < 2)]
  by_cases hk0 : k = 0
  · simp [hk0]
  · have hkpos : 1 ≤ k := by omega
    nlinarith

lemma pentagonal023Exp_bound_neg (k : ℤ) (hk : k ≤ 0) :
    -k ≤ k * (5 * k - 1) / 2 := by
  rw [Int.le_ediv_iff_mul_le (by norm_num : (0 : ℤ) < 2)]
  by_cases hk0 : k = 0
  · simp [hk0]
  · have hkneg : k ≤ -1 := by omega
    nlinarith

lemma pentagonal014Exp_mem_Icc_of_eq {k : ℤ} {n : ℕ} (h : pentagonal014Exp k = n) :
    k ∈ Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ) := by
  rw [Finset.mem_Icc]
  have hn : (n : ℤ) = k * (5 * k - 3) / 2 := by
    rw [← h]
    exact int_coe_pentagonal014Exp k
  constructor
  · by_cases hk : 0 ≤ k
    · have hn_nonneg : (0 : ℤ) ≤ n := by exact_mod_cast Nat.zero_le n
      omega
    · have hk_nonpos : k ≤ 0 := by omega
      have hneg : -k ≤ (n : ℤ) := by
        rw [hn]
        exact pentagonal014Exp_bound_neg k hk_nonpos
      omega
  · by_cases hk : 0 ≤ k
    · have hle : k ≤ (n : ℤ) := by
        rw [hn]
        exact pentagonal014Exp_bound_pos k hk
      omega
    · have hk_nonpos : k ≤ 0 := by omega
      have hn_nonneg : (0 : ℤ) ≤ n := by exact_mod_cast Nat.zero_le n
      omega

lemma pentagonal023Exp_mem_Icc_of_eq {k : ℤ} {n : ℕ} (h : pentagonal023Exp k = n) :
    k ∈ Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ) := by
  rw [Finset.mem_Icc]
  have hn : (n : ℤ) = k * (5 * k - 1) / 2 := by
    rw [← h]
    exact int_coe_pentagonal023Exp k
  constructor
  · by_cases hk : 0 ≤ k
    · have hn_nonneg : (0 : ℤ) ≤ n := by exact_mod_cast Nat.zero_le n
      omega
    · have hk_nonpos : k ≤ 0 := by omega
      have hneg : -k ≤ (n : ℤ) := by
        rw [hn]
        exact pentagonal023Exp_bound_neg k hk_nonpos
      omega
  · by_cases hk : 0 ≤ k
    · have hle : k ≤ (n : ℤ) := by
        rw [hn]
        exact pentagonal023Exp_bound_pos k hk
      omega
    · have hk_nonpos : k ≤ 0 := by omega
      have hn_nonneg : (0 : ℤ) ≤ n := by exact_mod_cast Nat.zero_le n
      omega

lemma negOnePowInt_complex_eq_zpow (k : ℤ) :
    negOnePowInt ℂ k = (-1 : ℂ) ^ k := by
  cases k with
  | ofNat n =>
      simp [negOnePowInt]
  | negSucc n =>
      simp [negOnePowInt]
      have hsq : ((-1 : ℂ) ^ (n + 1)) * ((-1 : ℂ) ^ (n + 1)) = 1 := by
        rw [← pow_add]
        rw [show (n + 1 + (n + 1)) = 2 * (n + 1) by ring]
        rw [pow_mul]
        norm_num
      exact eq_inv_of_mul_eq_one_right hsq

lemma norm_negOnePowInt_complex (k : ℤ) :
    ‖negOnePowInt ℂ k‖ = 1 := by
  simp [negOnePowInt, norm_pow]

noncomputable def pentagonal014ThetaTerm (q : ℂ) (k : ℤ) : ℂ :=
  negOnePowInt ℂ k * q ^ pentagonal014Exp k

noncomputable def pentagonal023ThetaTerm (q : ℂ) (k : ℤ) : ℂ :=
  negOnePowInt ℂ k * q ^ pentagonal023Exp k

noncomputable def pentagonal014ThetaNat (q : ℂ) : ℂ :=
  ∑' k : ℤ, pentagonal014ThetaTerm q k

noncomputable def pentagonal023ThetaNat (q : ℂ) : ℂ :=
  ∑' k : ℤ, pentagonal023ThetaTerm q k

noncomputable def pentagonal014Analytic (q : ℂ) : ℂ :=
  ∑' k : ℤ, (-1 : ℂ) ^ k * q ^ (k * (5 * k - 3) / 2)

noncomputable def pentagonal023Analytic (q : ℂ) : ℂ :=
  ∑' k : ℤ, (-1 : ℂ) ^ k * q ^ (k * (5 * k - 1) / 2)

lemma pentagonal014_zpow_term_eq_thetaTerm (q : ℂ) (k : ℤ) :
    (-1 : ℂ) ^ k * q ^ (k * (5 * k - 3) / 2) =
      pentagonal014ThetaTerm q k := by
  rw [pentagonal014ThetaTerm]
  rw [← negOnePowInt_complex_eq_zpow k]
  rw [← int_coe_pentagonal014Exp k]
  rw [zpow_natCast]

lemma pentagonal023_zpow_term_eq_thetaTerm (q : ℂ) (k : ℤ) :
    (-1 : ℂ) ^ k * q ^ (k * (5 * k - 1) / 2) =
      pentagonal023ThetaTerm q k := by
  rw [pentagonal023ThetaTerm]
  rw [← negOnePowInt_complex_eq_zpow k]
  rw [← int_coe_pentagonal023Exp k]
  rw [zpow_natCast]

theorem pentagonal014Analytic_eq_thetaNat (q : ℂ) :
    pentagonal014Analytic q = pentagonal014ThetaNat q := by
  unfold pentagonal014Analytic pentagonal014ThetaNat
  exact tsum_congr fun k => pentagonal014_zpow_term_eq_thetaTerm q k

theorem pentagonal023Analytic_eq_thetaNat (q : ℂ) :
    pentagonal023Analytic q = pentagonal023ThetaNat q := by
  unfold pentagonal023Analytic pentagonal023ThetaNat
  exact tsum_congr fun k => pentagonal023_zpow_term_eq_thetaTerm q k

theorem summable_pentagonal014ThetaTerm (q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun k : ℤ => pentagonal014ThetaTerm q k := by
  rw [summable_int_iff_summable_nat_and_neg]
  have hgeom : Summable fun n : ℕ => ‖q‖ ^ n := by
    have hnorm : ‖(‖q‖ : ℝ)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg q)]
      exact hq
    simpa using summable_geometric_of_norm_lt_one hnorm
  constructor
  · refine Summable.of_norm_bounded hgeom ?_
    intro n
    have hle_int : (n : ℤ) ≤ (pentagonal014Exp (n : ℤ) : ℤ) := by
      rw [int_coe_pentagonal014Exp]
      exact pentagonal014Exp_bound_pos (n : ℤ) (by exact_mod_cast Nat.zero_le n)
    have hle_nat : n ≤ pentagonal014Exp (n : ℤ) := by exact_mod_cast hle_int
    calc
      ‖pentagonal014ThetaTerm q (n : ℤ)‖ = ‖q‖ ^ pentagonal014Exp (n : ℤ) := by
        rw [pentagonal014ThetaTerm, norm_mul, norm_negOnePowInt_complex, one_mul, norm_pow]
      _ ≤ ‖q‖ ^ n := pow_le_pow_of_le_one (norm_nonneg q) (le_of_lt hq) hle_nat
  · refine Summable.of_norm_bounded hgeom ?_
    intro n
    have hle_int : (n : ℤ) ≤ (pentagonal014Exp (-(n : ℤ)) : ℤ) := by
      have h := pentagonal014Exp_bound_neg (-(n : ℤ)) (by omega)
      rw [← int_coe_pentagonal014Exp (-(n : ℤ))] at h
      simpa using h
    have hle_nat : n ≤ pentagonal014Exp (-(n : ℤ)) := by exact_mod_cast hle_int
    calc
      ‖pentagonal014ThetaTerm q (-(n : ℤ))‖ =
          ‖q‖ ^ pentagonal014Exp (-(n : ℤ)) := by
        rw [pentagonal014ThetaTerm, norm_mul, norm_negOnePowInt_complex, one_mul, norm_pow]
      _ ≤ ‖q‖ ^ n := pow_le_pow_of_le_one (norm_nonneg q) (le_of_lt hq) hle_nat

theorem summable_pentagonal023ThetaTerm (q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun k : ℤ => pentagonal023ThetaTerm q k := by
  rw [summable_int_iff_summable_nat_and_neg]
  have hgeom : Summable fun n : ℕ => ‖q‖ ^ n := by
    have hnorm : ‖(‖q‖ : ℝ)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg q)]
      exact hq
    simpa using summable_geometric_of_norm_lt_one hnorm
  constructor
  · refine Summable.of_norm_bounded hgeom ?_
    intro n
    have hle_int : (n : ℤ) ≤ (pentagonal023Exp (n : ℤ) : ℤ) := by
      rw [int_coe_pentagonal023Exp]
      exact pentagonal023Exp_bound_pos (n : ℤ) (by exact_mod_cast Nat.zero_le n)
    have hle_nat : n ≤ pentagonal023Exp (n : ℤ) := by exact_mod_cast hle_int
    calc
      ‖pentagonal023ThetaTerm q (n : ℤ)‖ = ‖q‖ ^ pentagonal023Exp (n : ℤ) := by
        rw [pentagonal023ThetaTerm, norm_mul, norm_negOnePowInt_complex, one_mul, norm_pow]
      _ ≤ ‖q‖ ^ n := pow_le_pow_of_le_one (norm_nonneg q) (le_of_lt hq) hle_nat
  · refine Summable.of_norm_bounded hgeom ?_
    intro n
    have hle_int : (n : ℤ) ≤ (pentagonal023Exp (-(n : ℤ)) : ℤ) := by
      have h := pentagonal023Exp_bound_neg (-(n : ℤ)) (by omega)
      rw [← int_coe_pentagonal023Exp (-(n : ℤ))] at h
      simpa using h
    have hle_nat : n ≤ pentagonal023Exp (-(n : ℤ)) := by exact_mod_cast hle_int
    calc
      ‖pentagonal023ThetaTerm q (-(n : ℤ))‖ =
          ‖q‖ ^ pentagonal023Exp (-(n : ℤ)) := by
        rw [pentagonal023ThetaTerm, norm_mul, norm_negOnePowInt_complex, one_mul, norm_pow]
      _ ≤ ‖q‖ ^ n := pow_le_pow_of_le_one (norm_nonneg q) (le_of_lt hq) hle_nat

theorem pentagonal014_fiber_tsum_eq_coeff_mul_pow (q : ℂ) (n : ℕ) :
    (∑' k : ↑(pentagonal014Exp ⁻¹' ({n} : Set ℕ)), pentagonal014ThetaTerm q k) =
      pentagonal014Coeff ℂ n * q ^ n := by
  rw [tsum_subtype]
  rw [tsum_eq_sum (s := Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ))]
  · rw [pentagonal014Coeff, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _hk
    by_cases h : pentagonal014Exp k = n
    · rw [Set.indicator_of_mem]
      · simp [h, pentagonal014ThetaTerm]
      · simpa using h
    · have hnot : k ∉ pentagonal014Exp ⁻¹' ({n} : Set ℕ) := by
        simpa using h
      rw [Set.indicator_of_notMem hnot]
      simp [h]
  · intro k hk
    rw [Set.indicator_of_notMem]
    intro hmem
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hmem
    exact hk (pentagonal014Exp_mem_Icc_of_eq hmem)

theorem pentagonal023_fiber_tsum_eq_coeff_mul_pow (q : ℂ) (n : ℕ) :
    (∑' k : ↑(pentagonal023Exp ⁻¹' ({n} : Set ℕ)), pentagonal023ThetaTerm q k) =
      pentagonal023Coeff ℂ n * q ^ n := by
  rw [tsum_subtype]
  rw [tsum_eq_sum (s := Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ))]
  · rw [pentagonal023Coeff, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _hk
    by_cases h : pentagonal023Exp k = n
    · rw [Set.indicator_of_mem]
      · simp [h, pentagonal023ThetaTerm]
      · simpa using h
    · have hnot : k ∉ pentagonal023Exp ⁻¹' ({n} : Set ℕ) := by
        simpa using h
      rw [Set.indicator_of_notMem hnot]
      simp [h]
  · intro k hk
    rw [Set.indicator_of_notMem]
    intro hmem
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hmem
    exact hk (pentagonal023Exp_mem_Icc_of_eq hmem)

theorem hasSum_pentagonal014Coeff_mul_pow (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => pentagonal014Coeff ℂ n * q ^ n)
      (pentagonal014ThetaNat q) := by
  unfold pentagonal014ThetaNat
  have h := (summable_pentagonal014ThetaTerm q hq).hasSum
  convert h.tsum_fiberwise pentagonal014Exp using 1
  ext n
  exact (pentagonal014_fiber_tsum_eq_coeff_mul_pow q n).symm

theorem hasSum_pentagonal023Coeff_mul_pow (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => pentagonal023Coeff ℂ n * q ^ n)
      (pentagonal023ThetaNat q) := by
  unfold pentagonal023ThetaNat
  have h := (summable_pentagonal023ThetaTerm q hq).hasSum
  convert h.tsum_fiberwise pentagonal023Exp using 1
  ext n
  exact (pentagonal023_fiber_tsum_eq_coeff_mul_pow q n).symm

noncomputable def pentagonal014SeriesFMLS : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (pentagonal014Coeff ℂ)

noncomputable def pentagonal023SeriesFMLS : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (pentagonal023Coeff ℂ)

theorem one_le_pentagonal014SeriesFMLS_radius :
    (1 : ENNReal) ≤ pentagonal014SeriesFMLS.radius := by
  rw [show (1 : ENNReal) = ((1 : NNReal) : ENNReal) by simp]
  apply ENNReal.le_of_forall_nnreal_lt
  intro s hs
  rw [ENNReal.coe_lt_coe] at hs
  have hq_norm : ‖((s : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.coe_nonneg]
    exact_mod_cast hs
  have h_sum := (hasSum_pentagonal014Coeff_mul_pow ((s : ℝ) : ℂ) hq_norm).summable
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  have h_sum_norm := h_sum.norm
  have h_eq :
      (fun n : ℕ => ‖pentagonal014SeriesFMLS n‖ * (s : ℝ) ^ n) =
        (fun n : ℕ => ‖pentagonal014Coeff ℂ n * (((s : ℝ) : ℂ)) ^ n‖) := by
    funext n
    rw [pentagonal014SeriesFMLS, FormalMultilinearSeries.ofScalars_norm]
    rw [norm_mul, norm_pow]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.coe_nonneg]
  rw [h_eq]
  exact h_sum_norm

theorem one_le_pentagonal023SeriesFMLS_radius :
    (1 : ENNReal) ≤ pentagonal023SeriesFMLS.radius := by
  rw [show (1 : ENNReal) = ((1 : NNReal) : ENNReal) by simp]
  apply ENNReal.le_of_forall_nnreal_lt
  intro s hs
  rw [ENNReal.coe_lt_coe] at hs
  have hq_norm : ‖((s : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.coe_nonneg]
    exact_mod_cast hs
  have h_sum := (hasSum_pentagonal023Coeff_mul_pow ((s : ℝ) : ℂ) hq_norm).summable
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  have h_sum_norm := h_sum.norm
  have h_eq :
      (fun n : ℕ => ‖pentagonal023SeriesFMLS n‖ * (s : ℝ) ^ n) =
        (fun n : ℕ => ‖pentagonal023Coeff ℂ n * (((s : ℝ) : ℂ)) ^ n‖) := by
    funext n
    rw [pentagonal023SeriesFMLS, FormalMultilinearSeries.ofScalars_norm]
    rw [norm_mul, norm_pow]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.coe_nonneg]
  rw [h_eq]
  exact h_sum_norm

theorem hasFPowerSeriesOnBall_pentagonal014ThetaNat :
    HasFPowerSeriesOnBall pentagonal014ThetaNat pentagonal014SeriesFMLS 0 1 := by
  refine ⟨one_le_pentagonal014SeriesFMLS_radius, by positivity, ?_⟩
  intro y hy
  rw [zero_add]
  have hy_norm : ‖y‖ < 1 := by
    have h1 : (1 : ENNReal) = ENNReal.ofReal 1 := by simp
    have h_ball : y ∈ Metric.ball (0 : ℂ) 1 := by
      rw [h1, Metric.emetric_ball] at hy
      exact hy
    have h2 : dist y (0 : ℂ) < 1 := Metric.mem_ball.mp h_ball
    rwa [dist_zero_right] at h2
  have h := hasSum_pentagonal014Coeff_mul_pow y hy_norm
  convert h using 1
  funext n
  rw [pentagonal014SeriesFMLS, FormalMultilinearSeries.ofScalars_apply_eq]
  rw [smul_eq_mul]

theorem hasFPowerSeriesOnBall_pentagonal023ThetaNat :
    HasFPowerSeriesOnBall pentagonal023ThetaNat pentagonal023SeriesFMLS 0 1 := by
  refine ⟨one_le_pentagonal023SeriesFMLS_radius, by positivity, ?_⟩
  intro y hy
  rw [zero_add]
  have hy_norm : ‖y‖ < 1 := by
    have h1 : (1 : ENNReal) = ENNReal.ofReal 1 := by simp
    have h_ball : y ∈ Metric.ball (0 : ℂ) 1 := by
      rw [h1, Metric.emetric_ball] at hy
      exact hy
    have h2 : dist y (0 : ℂ) < 1 := Metric.mem_ball.mp h_ball
    rwa [dist_zero_right] at h2
  have h := hasSum_pentagonal023Coeff_mul_pow y hy_norm
  convert h using 1
  funext n
  rw [pentagonal023SeriesFMLS, FormalMultilinearSeries.ofScalars_apply_eq]
  rw [smul_eq_mul]

theorem hasFPowerSeriesOnBall_pentagonal014Analytic :
    HasFPowerSeriesOnBall pentagonal014Analytic pentagonal014SeriesFMLS 0 1 := by
  exact hasFPowerSeriesOnBall_pentagonal014ThetaNat.congr fun q _ =>
    (pentagonal014Analytic_eq_thetaNat q).symm

theorem hasFPowerSeriesOnBall_pentagonal023Analytic :
    HasFPowerSeriesOnBall pentagonal023Analytic pentagonal023SeriesFMLS 0 1 := by
  exact hasFPowerSeriesOnBall_pentagonal023ThetaNat.congr fun q _ =>
    (pentagonal023Analytic_eq_thetaNat q).symm

/-! ## Analytic identities already closed in Chapter 4, in target exponent orientation -/

/-- Reindex `j ↦ -j` for the first target exponent. -/
theorem tsum_pentagonal014_eq_theta_sum_2 (q : ℂ) :
    (∑' k : ℤ, (-1 : ℂ) ^ k * q ^ (k * (5 * k - 3) / 2)) =
      ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (5 * j + 3) / 2) := by
  rw [← (Equiv.neg ℤ).tsum_eq
    (fun j : ℤ => (-1 : ℂ) ^ j * q ^ (j * (5 * j - 3) / 2))]
  exact tsum_congr fun j => by
    simp only [Equiv.neg_apply]
    have hsign : (-1 : ℂ) ^ (-j) = (-1 : ℂ) ^ j := by
      by_cases h : Even j <;> simp [neg_one_zpow_eq_ite, h]
    rw [hsign]
    congr 1
    ring_nf

/-- Reindex `j ↦ -j` for the second target exponent. -/
theorem tsum_pentagonal023_eq_theta_sum_1 (q : ℂ) :
    (∑' k : ℤ, (-1 : ℂ) ^ k * q ^ (k * (5 * k - 1) / 2)) =
      ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (5 * j + 1) / 2) := by
  rw [← (Equiv.neg ℤ).tsum_eq
    (fun j : ℤ => (-1 : ℂ) ^ j * q ^ (j * (5 * j - 1) / 2))]
  exact tsum_congr fun j => by
    simp only [Equiv.neg_apply]
    have hsign : (-1 : ℂ) ^ (-j) = (-1 : ℂ) ^ j := by
      by_cases h : Even j <;> simp [neg_one_zpow_eq_ite, h]
    rw [hsign]
    congr 1
    ring_nf

/-- Analytic JTP specialisation for `(q,q^4,q^5;q^5)_∞`, target orientation. -/
theorem analytic_pentagonal014_eq_mod5_product
    (q : ℂ) (hq : ‖q‖ < 1) (hq_ne : q ≠ 0) :
    (∑' k : ℤ, (-1 : ℂ) ^ k * q ^ (k * (5 * k - 3) / 2)) =
      (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 5 n) *
        (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 4 n) *
        (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 1 n) := by
  rw [tsum_pentagonal014_eq_theta_sum_2]
  exact PartI.Ch04.theta_sum_2_eq_mod5_product q hq hq_ne

/-- Analytic JTP specialisation for `(q^2,q^3,q^5;q^5)_∞`, target orientation. -/
theorem analytic_pentagonal023_eq_mod5_product
    (q : ℂ) (hq : ‖q‖ < 1) (hq_ne : q ≠ 0) :
    (∑' k : ℤ, (-1 : ℂ) ^ k * q ^ (k * (5 * k - 1) / 2)) =
      (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 5 n) *
        (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 3 n) *
        (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 2 n) := by
  rw [tsum_pentagonal023_eq_theta_sum_1]
  exact PartI.Ch04.theta_sum_1_eq_mod5_product q hq hq_ne

/-! ## Product-side analytic functions, with the puncture at `q = 0` filled -/

/-- The analytic product `(q,q^4,q^5;q^5)_∞`. -/
noncomputable def pentagonal014ProductAnalytic (q : ℂ) : ℂ :=
  (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 5 n) *
    (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 4 n) *
    (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 1 n)

/-- The analytic product `(q^2,q^3,q^5;q^5)_∞`. -/
noncomputable def pentagonal023ProductAnalytic (q : ℂ) : ℂ :=
  (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 5 n) *
    (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 3 n) *
    (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 2 n)

theorem tprod_rrMod5Factor_zero (k : ℕ) (hk : 1 ≤ k) :
    (∏' n : ℕ, PartI.Ch04.rrMod5Factor (0 : ℂ) k n) = 1 := by
  have hfac :
      (fun n : ℕ => PartI.Ch04.rrMod5Factor (0 : ℂ) k n) =
        fun _ : ℕ => (1 : ℂ) := by
    funext n
    have hne : k + 5 * n ≠ 0 := by omega
    have hpow : (0 : ℂ) ^ (k + 5 * n) = 0 := zero_pow hne
    simp [PartI.Ch04.rrMod5Factor, hpow]
  rw [hfac]
  simp

lemma pentagonal014Exp_pos_of_ne_zero {k : ℤ} (hk : k ≠ 0) :
    0 < pentagonal014Exp k := by
  by_cases hk_nonneg : 0 ≤ k
  · have hk_one : (1 : ℤ) ≤ k := by omega
    have hle_int : (1 : ℤ) ≤ (pentagonal014Exp k : ℤ) := by
      rw [int_coe_pentagonal014Exp]
      exact le_trans hk_one (pentagonal014Exp_bound_pos k hk_nonneg)
    have hle_nat : 1 ≤ pentagonal014Exp k := by exact_mod_cast hle_int
    omega
  · have hk_nonpos : k ≤ 0 := by omega
    have hk_one : (1 : ℤ) ≤ -k := by omega
    have hle_int : (1 : ℤ) ≤ (pentagonal014Exp k : ℤ) := by
      rw [int_coe_pentagonal014Exp]
      exact le_trans hk_one (pentagonal014Exp_bound_neg k hk_nonpos)
    have hle_nat : 1 ≤ pentagonal014Exp k := by exact_mod_cast hle_int
    omega

lemma pentagonal023Exp_pos_of_ne_zero {k : ℤ} (hk : k ≠ 0) :
    0 < pentagonal023Exp k := by
  by_cases hk_nonneg : 0 ≤ k
  · have hk_one : (1 : ℤ) ≤ k := by omega
    have hle_int : (1 : ℤ) ≤ (pentagonal023Exp k : ℤ) := by
      rw [int_coe_pentagonal023Exp]
      exact le_trans hk_one (pentagonal023Exp_bound_pos k hk_nonneg)
    have hle_nat : 1 ≤ pentagonal023Exp k := by exact_mod_cast hle_int
    omega
  · have hk_nonpos : k ≤ 0 := by omega
    have hk_one : (1 : ℤ) ≤ -k := by omega
    have hle_int : (1 : ℤ) ≤ (pentagonal023Exp k : ℤ) := by
      rw [int_coe_pentagonal023Exp]
      exact le_trans hk_one (pentagonal023Exp_bound_neg k hk_nonpos)
    have hle_nat : 1 ≤ pentagonal023Exp k := by exact_mod_cast hle_int
    omega

theorem pentagonal014ThetaNat_zero : pentagonal014ThetaNat 0 = 1 := by
  unfold pentagonal014ThetaNat
  rw [tsum_eq_single (0 : ℤ)]
  · simp [pentagonal014ThetaTerm, pentagonal014Exp, negOnePowInt]
  · intro k hk
    rw [pentagonal014ThetaTerm]
    rw [zero_pow (pentagonal014Exp_pos_of_ne_zero hk).ne', mul_zero]

theorem pentagonal023ThetaNat_zero : pentagonal023ThetaNat 0 = 1 := by
  unfold pentagonal023ThetaNat
  rw [tsum_eq_single (0 : ℤ)]
  · simp [pentagonal023ThetaTerm, pentagonal023Exp, negOnePowInt]
  · intro k hk
    rw [pentagonal023ThetaTerm]
    rw [zero_pow (pentagonal023Exp_pos_of_ne_zero hk).ne', mul_zero]

theorem pentagonal014Analytic_zero : pentagonal014Analytic 0 = 1 := by
  rw [pentagonal014Analytic_eq_thetaNat, pentagonal014ThetaNat_zero]

theorem pentagonal023Analytic_zero : pentagonal023Analytic 0 = 1 := by
  rw [pentagonal023Analytic_eq_thetaNat, pentagonal023ThetaNat_zero]

theorem pentagonal014ProductAnalytic_eq_pentagonal014Analytic
    (q : ℂ) (hq : ‖q‖ < 1) :
    pentagonal014ProductAnalytic q = pentagonal014Analytic q := by
  by_cases hq_zero : q = 0
  · subst q
    unfold pentagonal014ProductAnalytic
    rw [tprod_rrMod5Factor_zero 5 (by norm_num),
      tprod_rrMod5Factor_zero 4 (by norm_num),
      tprod_rrMod5Factor_zero 1 (by norm_num),
      pentagonal014Analytic_zero]
    ring
  · exact (analytic_pentagonal014_eq_mod5_product q hq hq_zero).symm

theorem pentagonal023ProductAnalytic_eq_pentagonal023Analytic
    (q : ℂ) (hq : ‖q‖ < 1) :
    pentagonal023ProductAnalytic q = pentagonal023Analytic q := by
  by_cases hq_zero : q = 0
  · subst q
    unfold pentagonal023ProductAnalytic
    rw [tprod_rrMod5Factor_zero 5 (by norm_num),
      tprod_rrMod5Factor_zero 3 (by norm_num),
      tprod_rrMod5Factor_zero 2 (by norm_num),
      pentagonal023Analytic_zero]
    ring
  · exact (analytic_pentagonal023_eq_mod5_product q hq hq_zero).symm

lemma norm_lt_one_of_mem_emetric_unit_ball {q : ℂ}
    (hq : q ∈ EMetric.ball (0 : ℂ) (1 : ENNReal)) :
    ‖q‖ < 1 := by
  have h : edist q 0 < 1 := EMetric.mem_ball.mp hq
  rw [edist_dist, dist_zero_right] at h
  exact_mod_cast ENNReal.ofReal_lt_one.mp (lt_of_lt_of_le h (le_refl _))

/-- The product-side analytic function has the theta Taylor expansion on `‖q‖ < 1`. -/
theorem hasFPowerSeriesOnBall_pentagonal014ProductAnalytic_series :
    HasFPowerSeriesOnBall pentagonal014ProductAnalytic pentagonal014SeriesFMLS 0 1 := by
  refine hasFPowerSeriesOnBall_pentagonal014Analytic.congr ?_
  intro q hq
  exact (pentagonal014ProductAnalytic_eq_pentagonal014Analytic q
    (norm_lt_one_of_mem_emetric_unit_ball hq)).symm

/-- The product-side analytic function has the theta Taylor expansion on `‖q‖ < 1`. -/
theorem hasFPowerSeriesOnBall_pentagonal023ProductAnalytic_series :
    HasFPowerSeriesOnBall pentagonal023ProductAnalytic pentagonal023SeriesFMLS 0 1 := by
  refine hasFPowerSeriesOnBall_pentagonal023Analytic.congr ?_
  intro q hq
  exact (pentagonal023ProductAnalytic_eq_pentagonal023Analytic q
    (norm_lt_one_of_mem_emetric_unit_ball hq)).symm

/-! ## Final uniqueness step, conditional on the product-coefficient Taylor bridge -/

noncomputable def pentagonal014ProductCoeffFMLS : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (pentagonalProduct014PS ℂ).coeff n)

noncomputable def pentagonal023ProductCoeffFMLS : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (pentagonalProduct023PS ℂ).coeff n)

/-! ### Product-coefficient finite partial bridges -/

lemma coeff_mul_apFactorPS_eq_of_lt
    (R : Type*) [CommRing R] (P : R⟦X⟧) (k r m N : ℕ)
    (hk : k < r + m * N) :
    (P * apFactorPS R r m N).coeff k = P.coeff k := by
  rw [apFactorPS, mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow']
  simp [Nat.not_le_of_gt hk]

theorem partial_prod_pentagonalTripleFactor014PS_coeff_stable
    (R : Type*) [CommRing R] (k N : ℕ) (hN : k ≤ N) :
    PowerSeries.coeff k
        (∏ n ∈ Finset.range (N + 1), pentagonalTripleFactor014PS R n) =
      PowerSeries.coeff k
        (∏ n ∈ Finset.range N, pentagonalTripleFactor014PS R n) := by
  rw [Finset.prod_range_succ]
  change PowerSeries.coeff k
      ((∏ n ∈ Finset.range N, pentagonalTripleFactor014PS R n) *
        (apFactorPS R 1 5 N * apFactorPS R 4 5 N * apFactorPS R 5 5 N)) =
    PowerSeries.coeff k (∏ n ∈ Finset.range N, pentagonalTripleFactor014PS R n)
  let P : R⟦X⟧ := ∏ n ∈ Finset.range N, pentagonalTripleFactor014PS R n
  calc
    PowerSeries.coeff k
        (P * (apFactorPS R 1 5 N * apFactorPS R 4 5 N * apFactorPS R 5 5 N))
        = PowerSeries.coeff k
          (((P * apFactorPS R 1 5 N) * apFactorPS R 4 5 N) *
            apFactorPS R 5 5 N) := by
          ring_nf
    _ = PowerSeries.coeff k ((P * apFactorPS R 1 5 N) * apFactorPS R 4 5 N) :=
          coeff_mul_apFactorPS_eq_of_lt R
            ((P * apFactorPS R 1 5 N) * apFactorPS R 4 5 N) k 5 5 N (by omega)
    _ = PowerSeries.coeff k (P * apFactorPS R 1 5 N) :=
          coeff_mul_apFactorPS_eq_of_lt R (P * apFactorPS R 1 5 N) k 4 5 N
            (by omega)
    _ = PowerSeries.coeff k P :=
          coeff_mul_apFactorPS_eq_of_lt R P k 1 5 N (by omega)

theorem partial_prod_pentagonalTripleFactor023PS_coeff_stable
    (R : Type*) [CommRing R] (k N : ℕ) (hN : k ≤ N) :
    PowerSeries.coeff k
        (∏ n ∈ Finset.range (N + 1), pentagonalTripleFactor023PS R n) =
      PowerSeries.coeff k
        (∏ n ∈ Finset.range N, pentagonalTripleFactor023PS R n) := by
  rw [Finset.prod_range_succ]
  change PowerSeries.coeff k
      ((∏ n ∈ Finset.range N, pentagonalTripleFactor023PS R n) *
        (apFactorPS R 2 5 N * apFactorPS R 3 5 N * apFactorPS R 5 5 N)) =
    PowerSeries.coeff k (∏ n ∈ Finset.range N, pentagonalTripleFactor023PS R n)
  let P : R⟦X⟧ := ∏ n ∈ Finset.range N, pentagonalTripleFactor023PS R n
  calc
    PowerSeries.coeff k
        (P * (apFactorPS R 2 5 N * apFactorPS R 3 5 N * apFactorPS R 5 5 N))
        = PowerSeries.coeff k
          (((P * apFactorPS R 2 5 N) * apFactorPS R 3 5 N) *
            apFactorPS R 5 5 N) := by
          ring_nf
    _ = PowerSeries.coeff k ((P * apFactorPS R 2 5 N) * apFactorPS R 3 5 N) :=
          coeff_mul_apFactorPS_eq_of_lt R
            ((P * apFactorPS R 2 5 N) * apFactorPS R 3 5 N) k 5 5 N (by omega)
    _ = PowerSeries.coeff k (P * apFactorPS R 2 5 N) :=
          coeff_mul_apFactorPS_eq_of_lt R (P * apFactorPS R 2 5 N) k 3 5 N
            (by omega)
    _ = PowerSeries.coeff k P :=
          coeff_mul_apFactorPS_eq_of_lt R P k 2 5 N (by omega)

theorem partial_prod_pentagonalTripleFactor014PS_coeff_eq
    (R : Type*) [CommRing R] (k N M : ℕ) (hkN : k ≤ N) (hNM : N ≤ M) :
    PowerSeries.coeff k
        (∏ n ∈ Finset.range M, pentagonalTripleFactor014PS R n) =
      PowerSeries.coeff k
        (∏ n ∈ Finset.range N, pentagonalTripleFactor014PS R n) := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M _ ih =>
      rw [partial_prod_pentagonalTripleFactor014PS_coeff_stable R k M (by omega), ih]

theorem partial_prod_pentagonalTripleFactor023PS_coeff_eq
    (R : Type*) [CommRing R] (k N M : ℕ) (hkN : k ≤ N) (hNM : N ≤ M) :
    PowerSeries.coeff k
        (∏ n ∈ Finset.range M, pentagonalTripleFactor023PS R n) =
      PowerSeries.coeff k
        (∏ n ∈ Finset.range N, pentagonalTripleFactor023PS R n) := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M _ ih =>
      rw [partial_prod_pentagonalTripleFactor023PS_coeff_stable R k M (by omega), ih]

theorem coeff_pentagonalProduct014PS_eq_coeff_partial
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (k : ℕ) :
    (pentagonalProduct014PS R).coeff k =
      (∏ n ∈ Finset.range (k + 1), pentagonalTripleFactor014PS R n).coeff k := by
  have h_tendsto : Tendsto
      (fun N : ℕ => ∏ n ∈ Finset.range N, pentagonalTripleFactor014PS R n) atTop
      (𝓝 (pentagonalProduct014PS R)) :=
    (hasProd_pentagonalTripleFactor014PS R).tendsto_prod_nat
  have h_coeff_tendsto : Tendsto
      (fun N : ℕ => PowerSeries.coeff k
        (∏ n ∈ Finset.range N, pentagonalTripleFactor014PS R n)) atTop
      (𝓝 (PowerSeries.coeff k (pentagonalProduct014PS R))) :=
    ((PowerSeries.WithPiTopology.continuous_coeff R k).tendsto _).comp h_tendsto
  have h_const_tendsto : Tendsto
      (fun N : ℕ => PowerSeries.coeff k
        (∏ n ∈ Finset.range N, pentagonalTripleFactor014PS R n)) atTop
      (𝓝 (PowerSeries.coeff k
        (∏ n ∈ Finset.range (k + 1), pentagonalTripleFactor014PS R n))) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    exact ⟨k + 1, fun N hN =>
      (partial_prod_pentagonalTripleFactor014PS_coeff_eq R k (k + 1) N (by omega) hN).symm⟩
  exact tendsto_nhds_unique h_coeff_tendsto h_const_tendsto

theorem coeff_pentagonalProduct023PS_eq_coeff_partial
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (k : ℕ) :
    (pentagonalProduct023PS R).coeff k =
      (∏ n ∈ Finset.range (k + 1), pentagonalTripleFactor023PS R n).coeff k := by
  have h_tendsto : Tendsto
      (fun N : ℕ => ∏ n ∈ Finset.range N, pentagonalTripleFactor023PS R n) atTop
      (𝓝 (pentagonalProduct023PS R)) :=
    (hasProd_pentagonalTripleFactor023PS R).tendsto_prod_nat
  have h_coeff_tendsto : Tendsto
      (fun N : ℕ => PowerSeries.coeff k
        (∏ n ∈ Finset.range N, pentagonalTripleFactor023PS R n)) atTop
      (𝓝 (PowerSeries.coeff k (pentagonalProduct023PS R))) :=
    ((PowerSeries.WithPiTopology.continuous_coeff R k).tendsto _).comp h_tendsto
  have h_const_tendsto : Tendsto
      (fun N : ℕ => PowerSeries.coeff k
        (∏ n ∈ Finset.range N, pentagonalTripleFactor023PS R n)) atTop
      (𝓝 (PowerSeries.coeff k
        (∏ n ∈ Finset.range (k + 1), pentagonalTripleFactor023PS R n))) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    exact ⟨k + 1, fun N hN =>
      (partial_prod_pentagonalTripleFactor023PS_coeff_eq R k (k + 1) N (by omega) hN).symm⟩
  exact tendsto_nhds_unique h_coeff_tendsto h_const_tendsto

theorem tendsto_pentagonal014ProductAnalytic_partial
    (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto
      (fun N : ℕ => ∏ n ∈ Finset.range N,
        PartI.Ch04.rrMod5Factor q 5 n * PartI.Ch04.rrMod5Factor q 4 n *
          PartI.Ch04.rrMod5Factor q 1 n)
      atTop (𝓝 (pentagonal014ProductAnalytic q)) := by
  have h5 := (PartI.Ch04.multipliable_rrMod5Factor q hq 5).tendsto_prod_tprod_nat
  have h4 := (PartI.Ch04.multipliable_rrMod5Factor q hq 4).tendsto_prod_tprod_nat
  have h1 := (PartI.Ch04.multipliable_rrMod5Factor q hq 1).tendsto_prod_tprod_nat
  simpa [pentagonal014ProductAnalytic, Finset.prod_mul_distrib, mul_assoc]
    using ((h5.mul h4).mul h1)

theorem tendsto_pentagonal023ProductAnalytic_partial
    (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto
      (fun N : ℕ => ∏ n ∈ Finset.range N,
        PartI.Ch04.rrMod5Factor q 5 n * PartI.Ch04.rrMod5Factor q 3 n *
          PartI.Ch04.rrMod5Factor q 2 n)
      atTop (𝓝 (pentagonal023ProductAnalytic q)) := by
  have h5 := (PartI.Ch04.multipliable_rrMod5Factor q hq 5).tendsto_prod_tprod_nat
  have h3 := (PartI.Ch04.multipliable_rrMod5Factor q hq 3).tendsto_prod_tprod_nat
  have h2 := (PartI.Ch04.multipliable_rrMod5Factor q hq 2).tendsto_prod_tprod_nat
  simpa [pentagonal023ProductAnalytic, Finset.prod_mul_distrib, mul_assoc]
    using ((h5.mul h3).mul h2)

lemma norm_coeff_mul_apFactorPS_complex_le
    (P : ℂ⟦X⟧) (B : ℝ) (hB : 0 ≤ B)
    (hP : ∀ k : ℕ, ‖P.coeff k‖ ≤ B) (k r m N : ℕ) :
    ‖(P * apFactorPS ℂ r m N).coeff k‖ ≤ 2 * B := by
  rw [apFactorPS, mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow']
  by_cases hle : r + m * N ≤ k
  · rw [if_pos hle]
    calc
      ‖P.coeff k - P.coeff (k - (r + m * N))‖
          ≤ ‖P.coeff k‖ + ‖P.coeff (k - (r + m * N))‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add (hP k) (hP (k - (r + m * N)))
      _ = 2 * B := by ring
  · rw [if_neg hle, sub_zero]
    linarith [hP k]

lemma norm_coeff_mul_pentagonalTripleFactor014PS_complex_le
    (P : ℂ⟦X⟧) (B : ℝ) (hB : 0 ≤ B)
    (hP : ∀ k : ℕ, ‖P.coeff k‖ ≤ B) (k N : ℕ) :
    ‖(P * pentagonalTripleFactor014PS ℂ N).coeff k‖ ≤ 8 * B := by
  have hP1 : ∀ k : ℕ, ‖(P * apFactorPS ℂ 1 5 N).coeff k‖ ≤ 2 * B :=
    fun k => norm_coeff_mul_apFactorPS_complex_le P B hB hP k 1 5 N
  have hP2 : ∀ k : ℕ,
      ‖((P * apFactorPS ℂ 1 5 N) * apFactorPS ℂ 4 5 N).coeff k‖ ≤
        2 * (2 * B) :=
    fun k => norm_coeff_mul_apFactorPS_complex_le
      (P * apFactorPS ℂ 1 5 N) (2 * B) (by nlinarith) hP1 k 4 5 N
  calc
    ‖(P * pentagonalTripleFactor014PS ℂ N).coeff k‖ =
        ‖(((P * apFactorPS ℂ 1 5 N) * apFactorPS ℂ 4 5 N) *
          apFactorPS ℂ 5 5 N).coeff k‖ := by
        congr 1
        rw [pentagonalTripleFactor014PS]
        ring_nf
    _ ≤ 2 * (2 * (2 * B)) :=
        norm_coeff_mul_apFactorPS_complex_le
          ((P * apFactorPS ℂ 1 5 N) * apFactorPS ℂ 4 5 N)
          (2 * (2 * B)) (by nlinarith) hP2 k 5 5 N
    _ = 8 * B := by ring

lemma norm_coeff_mul_pentagonalTripleFactor023PS_complex_le
    (P : ℂ⟦X⟧) (B : ℝ) (hB : 0 ≤ B)
    (hP : ∀ k : ℕ, ‖P.coeff k‖ ≤ B) (k N : ℕ) :
    ‖(P * pentagonalTripleFactor023PS ℂ N).coeff k‖ ≤ 8 * B := by
  have hP1 : ∀ k : ℕ, ‖(P * apFactorPS ℂ 2 5 N).coeff k‖ ≤ 2 * B :=
    fun k => norm_coeff_mul_apFactorPS_complex_le P B hB hP k 2 5 N
  have hP2 : ∀ k : ℕ,
      ‖((P * apFactorPS ℂ 2 5 N) * apFactorPS ℂ 3 5 N).coeff k‖ ≤
        2 * (2 * B) :=
    fun k => norm_coeff_mul_apFactorPS_complex_le
      (P * apFactorPS ℂ 2 5 N) (2 * B) (by nlinarith) hP1 k 3 5 N
  calc
    ‖(P * pentagonalTripleFactor023PS ℂ N).coeff k‖ =
        ‖(((P * apFactorPS ℂ 2 5 N) * apFactorPS ℂ 3 5 N) *
          apFactorPS ℂ 5 5 N).coeff k‖ := by
        congr 1
        rw [pentagonalTripleFactor023PS]
        ring_nf
    _ ≤ 2 * (2 * (2 * B)) :=
        norm_coeff_mul_apFactorPS_complex_le
          ((P * apFactorPS ℂ 2 5 N) * apFactorPS ℂ 3 5 N)
          (2 * (2 * B)) (by nlinarith) hP2 k 5 5 N
    _ = 8 * B := by ring

lemma norm_coeff_partial_pentagonalTripleFactor014PS_complex_le
    (N k : ℕ) :
    ‖(∏ n ∈ Finset.range N, pentagonalTripleFactor014PS ℂ n).coeff k‖ ≤
      (8 : ℝ) ^ N := by
  revert k
  induction N with
  | zero =>
      intro k
      by_cases hk : k = 0 <;> simp [hk]
  | succ N ih =>
      intro k
      rw [Finset.prod_range_succ]
      calc
        ‖((∏ n ∈ Finset.range N, pentagonalTripleFactor014PS ℂ n) *
            pentagonalTripleFactor014PS ℂ N).coeff k‖
            ≤ 8 * (8 : ℝ) ^ N :=
          norm_coeff_mul_pentagonalTripleFactor014PS_complex_le
            (∏ n ∈ Finset.range N, pentagonalTripleFactor014PS ℂ n)
            ((8 : ℝ) ^ N) (by positivity) (fun j => ih j) k N
        _ = (8 : ℝ) ^ (N + 1) := by
          rw [pow_succ]
          ring

lemma norm_coeff_partial_pentagonalTripleFactor023PS_complex_le
    (N k : ℕ) :
    ‖(∏ n ∈ Finset.range N, pentagonalTripleFactor023PS ℂ n).coeff k‖ ≤
      (8 : ℝ) ^ N := by
  revert k
  induction N with
  | zero =>
      intro k
      by_cases hk : k = 0 <;> simp [hk]
  | succ N ih =>
      intro k
      rw [Finset.prod_range_succ]
      calc
        ‖((∏ n ∈ Finset.range N, pentagonalTripleFactor023PS ℂ n) *
            pentagonalTripleFactor023PS ℂ N).coeff k‖
            ≤ 8 * (8 : ℝ) ^ N :=
          norm_coeff_mul_pentagonalTripleFactor023PS_complex_le
            (∏ n ∈ Finset.range N, pentagonalTripleFactor023PS ℂ n)
            ((8 : ℝ) ^ N) (by positivity) (fun j => ih j) k N
        _ = (8 : ℝ) ^ (N + 1) := by
          rw [pow_succ]
          ring

lemma norm_coeff_pentagonalProduct014PS_complex_le (k : ℕ) :
    ‖(pentagonalProduct014PS ℂ).coeff k‖ ≤ (8 : ℝ) ^ (k + 1) := by
  rw [coeff_pentagonalProduct014PS_eq_coeff_partial ℂ k]
  exact norm_coeff_partial_pentagonalTripleFactor014PS_complex_le (k + 1) k

lemma norm_coeff_pentagonalProduct023PS_complex_le (k : ℕ) :
    ‖(pentagonalProduct023PS ℂ).coeff k‖ ≤ (8 : ℝ) ^ (k + 1) := by
  rw [coeff_pentagonalProduct023PS_eq_coeff_partial ℂ k]
  exact norm_coeff_partial_pentagonalTripleFactor023PS_complex_le (k + 1) k

lemma norm_coeff_partial_pentagonalTripleFactor014PS_complex_le_uniform
    (N k : ℕ) :
    ‖(∏ n ∈ Finset.range N, pentagonalTripleFactor014PS ℂ n).coeff k‖ ≤
      (8 : ℝ) ^ (k + 1) := by
  by_cases hN : N ≤ k + 1
  · exact le_trans (norm_coeff_partial_pentagonalTripleFactor014PS_complex_le N k)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 8) hN)
  · have hle : k + 1 ≤ N := Nat.le_of_not_ge hN
    rw [partial_prod_pentagonalTripleFactor014PS_coeff_eq ℂ k (k + 1) N
      (by omega) hle]
    exact norm_coeff_partial_pentagonalTripleFactor014PS_complex_le (k + 1) k

lemma norm_coeff_partial_pentagonalTripleFactor023PS_complex_le_uniform
    (N k : ℕ) :
    ‖(∏ n ∈ Finset.range N, pentagonalTripleFactor023PS ℂ n).coeff k‖ ≤
      (8 : ℝ) ^ (k + 1) := by
  by_cases hN : N ≤ k + 1
  · exact le_trans (norm_coeff_partial_pentagonalTripleFactor023PS_complex_le N k)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 8) hN)
  · have hle : k + 1 ≤ N := Nat.le_of_not_ge hN
    rw [partial_prod_pentagonalTripleFactor023PS_coeff_eq ℂ k (k + 1) N
      (by omega) hle]
    exact norm_coeff_partial_pentagonalTripleFactor023PS_complex_le (k + 1) k

lemma hasSum_coeff_mul_apFactorPS_complex
    (P : ℂ⟦X⟧) (q p : ℂ) (r m N : ℕ)
    (hP : HasSum (fun k : ℕ => P.coeff k * q ^ k) p) :
    HasSum (fun k : ℕ => (P * apFactorPS ℂ r m N).coeff k * q ^ k)
      (p * (1 - q ^ (r + m * N))) := by
  let d : ℕ := r + m * N
  let shift : ℕ → ℂ := fun k => (if d ≤ k then P.coeff (k - d) else 0) * q ^ k
  have htail : HasSum (fun n : ℕ => shift (n + d)) (p * q ^ d) := by
    have hmul : HasSum (fun n : ℕ => (P.coeff n * q ^ n) * q ^ d)
        (p * q ^ d) :=
      hP.mul_right (q ^ d)
    refine hmul.congr_fun ?_
    intro n
    dsimp [shift]
    rw [if_pos (by omega), show n + d - d = n by omega, pow_add]
    ring
  have hshift_full : HasSum shift (p * q ^ d) := by
    have hfull := (hasSum_nat_add_iff d).mp htail
    have hzero : (∑ i ∈ Finset.range d, shift i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      dsimp [shift]
      rw [if_neg (Nat.not_le_of_gt (Finset.mem_range.mp hi))]
      simp
    simpa [hzero] using hfull
  have hdiff : HasSum
      (fun k : ℕ => P.coeff k * q ^ k - shift k) (p - p * q ^ d) :=
    hP.sub hshift_full
  have hsum : HasSum
      (fun k : ℕ => (P * apFactorPS ℂ r m N).coeff k * q ^ k)
      (p - p * q ^ d) := by
    refine hdiff.congr_fun ?_
    intro k
    dsimp [shift, d]
    rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow']
    by_cases hle : r + m * N ≤ k
    · ring
    · ring
  have hval : p - p * q ^ d = p * (1 - q ^ (r + m * N)) := by
    dsimp [d]
    ring
  simpa [hval] using hsum

lemma hasSum_coeff_mul_pentagonalTripleFactor014PS_complex
    (P : ℂ⟦X⟧) (q p : ℂ) (N : ℕ)
    (hP : HasSum (fun k : ℕ => P.coeff k * q ^ k) p) :
    HasSum (fun k : ℕ => (P * pentagonalTripleFactor014PS ℂ N).coeff k * q ^ k)
      (p * (PartI.Ch04.rrMod5Factor q 5 N * PartI.Ch04.rrMod5Factor q 4 N *
        PartI.Ch04.rrMod5Factor q 1 N)) := by
  have h1 := hasSum_coeff_mul_apFactorPS_complex P q p 1 5 N hP
  have h2 := hasSum_coeff_mul_apFactorPS_complex (P * apFactorPS ℂ 1 5 N) q
    (p * (1 - q ^ (1 + 5 * N))) 4 5 N h1
  have h3 := hasSum_coeff_mul_apFactorPS_complex
    ((P * apFactorPS ℂ 1 5 N) * apFactorPS ℂ 4 5 N) q
    ((p * (1 - q ^ (1 + 5 * N))) * (1 - q ^ (4 + 5 * N))) 5 5 N h2
  convert h3 using 1
  · ext k
    rw [pentagonalTripleFactor014PS]
    ring_nf
  · rw [PartI.Ch04.rrMod5Factor, PartI.Ch04.rrMod5Factor, PartI.Ch04.rrMod5Factor]
    ring

lemma hasSum_coeff_mul_pentagonalTripleFactor023PS_complex
    (P : ℂ⟦X⟧) (q p : ℂ) (N : ℕ)
    (hP : HasSum (fun k : ℕ => P.coeff k * q ^ k) p) :
    HasSum (fun k : ℕ => (P * pentagonalTripleFactor023PS ℂ N).coeff k * q ^ k)
      (p * (PartI.Ch04.rrMod5Factor q 5 N * PartI.Ch04.rrMod5Factor q 3 N *
        PartI.Ch04.rrMod5Factor q 2 N)) := by
  have h1 := hasSum_coeff_mul_apFactorPS_complex P q p 2 5 N hP
  have h2 := hasSum_coeff_mul_apFactorPS_complex (P * apFactorPS ℂ 2 5 N) q
    (p * (1 - q ^ (2 + 5 * N))) 3 5 N h1
  have h3 := hasSum_coeff_mul_apFactorPS_complex
    ((P * apFactorPS ℂ 2 5 N) * apFactorPS ℂ 3 5 N) q
    ((p * (1 - q ^ (2 + 5 * N))) * (1 - q ^ (3 + 5 * N))) 5 5 N h2
  convert h3 using 1
  · ext k
    rw [pentagonalTripleFactor023PS]
    ring_nf
  · rw [PartI.Ch04.rrMod5Factor, PartI.Ch04.rrMod5Factor, PartI.Ch04.rrMod5Factor]
    ring

lemma hasSum_coeff_partial_pentagonalTripleFactor014PS_complex
    (q : ℂ) (N : ℕ) :
    HasSum (fun k : ℕ =>
        (∏ n ∈ Finset.range N, pentagonalTripleFactor014PS ℂ n).coeff k * q ^ k)
      (∏ n ∈ Finset.range N,
        PartI.Ch04.rrMod5Factor q 5 n * PartI.Ch04.rrMod5Factor q 4 n *
          PartI.Ch04.rrMod5Factor q 1 n) := by
  induction N with
  | zero =>
      simpa using (hasSum_single (0 : ℕ)
        (f := fun k : ℕ => ((1 : ℂ⟦X⟧).coeff k) * q ^ k)
        (by
          intro b hb
          simp [PowerSeries.coeff_one, hb]))
  | succ N ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      exact hasSum_coeff_mul_pentagonalTripleFactor014PS_complex
        (∏ n ∈ Finset.range N, pentagonalTripleFactor014PS ℂ n) q
        (∏ n ∈ Finset.range N,
          PartI.Ch04.rrMod5Factor q 5 n * PartI.Ch04.rrMod5Factor q 4 n *
            PartI.Ch04.rrMod5Factor q 1 n) N ih

lemma hasSum_coeff_partial_pentagonalTripleFactor023PS_complex
    (q : ℂ) (N : ℕ) :
    HasSum (fun k : ℕ =>
        (∏ n ∈ Finset.range N, pentagonalTripleFactor023PS ℂ n).coeff k * q ^ k)
      (∏ n ∈ Finset.range N,
        PartI.Ch04.rrMod5Factor q 5 n * PartI.Ch04.rrMod5Factor q 3 n *
          PartI.Ch04.rrMod5Factor q 2 n) := by
  induction N with
  | zero =>
      simpa using (hasSum_single (0 : ℕ)
        (f := fun k : ℕ => ((1 : ℂ⟦X⟧).coeff k) * q ^ k)
        (by
          intro b hb
          simp [PowerSeries.coeff_one, hb]))
  | succ N ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      exact hasSum_coeff_mul_pentagonalTripleFactor023PS_complex
        (∏ n ∈ Finset.range N, pentagonalTripleFactor023PS ℂ n) q
        (∏ n ∈ Finset.range N,
          PartI.Ch04.rrMod5Factor q 5 n * PartI.Ch04.rrMod5Factor q 3 n *
            PartI.Ch04.rrMod5Factor q 2 n) N ih

lemma summable_pentagonalProduct_bound_of_norm_lt_one_sixteenth
    {q : ℂ} (hq : ‖q‖ < (1 / 16 : ℝ)) :
    Summable fun k : ℕ => (8 : ℝ) ^ (k + 1) * ‖q‖ ^ k := by
  have hgeom : Summable fun k : ℕ => ((8 : ℝ) * ‖q‖) ^ k := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (8 : ℝ) * ‖q‖)]
    nlinarith [hq, norm_nonneg q]
  convert hgeom.mul_left (8 : ℝ) using 1
  ext k
  rw [pow_succ, mul_pow]
  ring

theorem hasSum_pentagonalProduct014PS_coeff_mul_pow_of_norm_lt_one_sixteenth
    (q : ℂ) (hq : ‖q‖ < (1 / 16 : ℝ)) :
    HasSum (fun k : ℕ => (pentagonalProduct014PS ℂ).coeff k * q ^ k)
      (pentagonal014ProductAnalytic q) := by
  let f : ℕ → ℕ → ℂ := fun N k =>
    (∏ n ∈ Finset.range N, pentagonalTripleFactor014PS ℂ n).coeff k * q ^ k
  let g : ℕ → ℂ := fun k => (pentagonalProduct014PS ℂ).coeff k * q ^ k
  let bound : ℕ → ℝ := fun k => (8 : ℝ) ^ (k + 1) * ‖q‖ ^ k
  have hbound_sum : Summable bound :=
    summable_pentagonalProduct_bound_of_norm_lt_one_sixteenth hq
  have hab : ∀ k : ℕ, Tendsto (fun N : ℕ => f N k) atTop (𝓝 (g k)) := by
    intro k
    apply tendsto_nhds_of_eventually_eq
    refine Filter.eventually_atTop.mpr ⟨k + 1, ?_⟩
    intro N hN
    dsimp [f, g]
    rw [partial_prod_pentagonalTripleFactor014PS_coeff_eq ℂ k (k + 1) N
      (by omega) hN]
    rw [← coeff_pentagonalProduct014PS_eq_coeff_partial ℂ k]
  have h_bound : ∀ᶠ N in atTop, ∀ k : ℕ, ‖f N k‖ ≤ bound k :=
    Filter.Eventually.of_forall fun N => by
      intro k
      dsimp [f, bound]
      rw [norm_mul, norm_pow]
      gcongr
      exact norm_coeff_partial_pentagonalTripleFactor014PS_complex_le_uniform N k
  have h_tsum : Tendsto (fun N : ℕ => ∑' k : ℕ, f N k) atTop
      (𝓝 (∑' k : ℕ, g k)) :=
    tendsto_tsum_of_dominated_convergence hbound_sum hab h_bound
  have h_finite : ∀ N : ℕ, (∑' k : ℕ, f N k) =
      ∏ n ∈ Finset.range N,
        PartI.Ch04.rrMod5Factor q 5 n * PartI.Ch04.rrMod5Factor q 4 n *
          PartI.Ch04.rrMod5Factor q 1 n := by
    intro N
    exact (hasSum_coeff_partial_pentagonalTripleFactor014PS_complex q N).tsum_eq
  have hq_unit : ‖q‖ < 1 := by nlinarith [hq]
  have h_partial :=
    tendsto_pentagonal014ProductAnalytic_partial q hq_unit
  have h_tsum_analytic : Tendsto (fun N : ℕ => ∑' k : ℕ, f N k) atTop
      (𝓝 (pentagonal014ProductAnalytic q)) :=
    Filter.Tendsto.congr (fun N => (h_finite N).symm) h_partial
  have h_eq : (∑' k : ℕ, g k) = pentagonal014ProductAnalytic q :=
    tendsto_nhds_unique h_tsum h_tsum_analytic
  have hg_summable : Summable g := by
    refine hbound_sum.of_norm_bounded ?_
    intro k
    dsimp [g, bound]
    rw [norm_mul, norm_pow]
    gcongr
    exact norm_coeff_pentagonalProduct014PS_complex_le k
  simpa [g, h_eq] using hg_summable.hasSum

theorem hasSum_pentagonalProduct023PS_coeff_mul_pow_of_norm_lt_one_sixteenth
    (q : ℂ) (hq : ‖q‖ < (1 / 16 : ℝ)) :
    HasSum (fun k : ℕ => (pentagonalProduct023PS ℂ).coeff k * q ^ k)
      (pentagonal023ProductAnalytic q) := by
  let f : ℕ → ℕ → ℂ := fun N k =>
    (∏ n ∈ Finset.range N, pentagonalTripleFactor023PS ℂ n).coeff k * q ^ k
  let g : ℕ → ℂ := fun k => (pentagonalProduct023PS ℂ).coeff k * q ^ k
  let bound : ℕ → ℝ := fun k => (8 : ℝ) ^ (k + 1) * ‖q‖ ^ k
  have hbound_sum : Summable bound :=
    summable_pentagonalProduct_bound_of_norm_lt_one_sixteenth hq
  have hab : ∀ k : ℕ, Tendsto (fun N : ℕ => f N k) atTop (𝓝 (g k)) := by
    intro k
    apply tendsto_nhds_of_eventually_eq
    refine Filter.eventually_atTop.mpr ⟨k + 1, ?_⟩
    intro N hN
    dsimp [f, g]
    rw [partial_prod_pentagonalTripleFactor023PS_coeff_eq ℂ k (k + 1) N
      (by omega) hN]
    rw [← coeff_pentagonalProduct023PS_eq_coeff_partial ℂ k]
  have h_bound : ∀ᶠ N in atTop, ∀ k : ℕ, ‖f N k‖ ≤ bound k :=
    Filter.Eventually.of_forall fun N => by
      intro k
      dsimp [f, bound]
      rw [norm_mul, norm_pow]
      gcongr
      exact norm_coeff_partial_pentagonalTripleFactor023PS_complex_le_uniform N k
  have h_tsum : Tendsto (fun N : ℕ => ∑' k : ℕ, f N k) atTop
      (𝓝 (∑' k : ℕ, g k)) :=
    tendsto_tsum_of_dominated_convergence hbound_sum hab h_bound
  have h_finite : ∀ N : ℕ, (∑' k : ℕ, f N k) =
      ∏ n ∈ Finset.range N,
        PartI.Ch04.rrMod5Factor q 5 n * PartI.Ch04.rrMod5Factor q 3 n *
          PartI.Ch04.rrMod5Factor q 2 n := by
    intro N
    exact (hasSum_coeff_partial_pentagonalTripleFactor023PS_complex q N).tsum_eq
  have hq_unit : ‖q‖ < 1 := by nlinarith [hq]
  have h_partial :=
    tendsto_pentagonal023ProductAnalytic_partial q hq_unit
  have h_tsum_analytic : Tendsto (fun N : ℕ => ∑' k : ℕ, f N k) atTop
      (𝓝 (pentagonal023ProductAnalytic q)) :=
    Filter.Tendsto.congr (fun N => (h_finite N).symm) h_partial
  have h_eq : (∑' k : ℕ, g k) = pentagonal023ProductAnalytic q :=
    tendsto_nhds_unique h_tsum h_tsum_analytic
  have hg_summable : Summable g := by
    refine hbound_sum.of_norm_bounded ?_
    intro k
    dsimp [g, bound]
    rw [norm_mul, norm_pow]
    gcongr
    exact norm_coeff_pentagonalProduct023PS_complex_le k
  simpa [g, h_eq] using hg_summable.hasSum

theorem one_sixteenth_le_pentagonal014ProductCoeffFMLS_radius :
    ((1 / 16 : NNReal) : ENNReal) ≤ pentagonal014ProductCoeffFMLS.radius := by
  refine FormalMultilinearSeries.le_radius_of_bound
    pentagonal014ProductCoeffFMLS 8 (r := (1 / 16 : NNReal)) ?_
  intro n
  rw [pentagonal014ProductCoeffFMLS, FormalMultilinearSeries.ofScalars_norm]
  calc
    ‖(pentagonalProduct014PS ℂ).coeff n‖ * ((1 / 16 : NNReal) : ℝ) ^ n
        ≤ (8 : ℝ) ^ (n + 1) * ((1 / 16 : NNReal) : ℝ) ^ n := by
        gcongr
        exact norm_coeff_pentagonalProduct014PS_complex_le n
    _ = 8 * ((1 / 2 : ℝ) ^ n) := by
        rw [pow_succ]
        rw [show (8 : ℝ) ^ n * 8 * ((1 / 16 : NNReal) : ℝ) ^ n =
          8 * (((8 : ℝ) * ((1 / 16 : NNReal) : ℝ)) ^ n) by
            rw [mul_pow]
            ring]
        norm_num
    _ ≤ 8 := by
        have hpow : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        nlinarith

theorem one_sixteenth_le_pentagonal023ProductCoeffFMLS_radius :
    ((1 / 16 : NNReal) : ENNReal) ≤ pentagonal023ProductCoeffFMLS.radius := by
  refine FormalMultilinearSeries.le_radius_of_bound
    pentagonal023ProductCoeffFMLS 8 (r := (1 / 16 : NNReal)) ?_
  intro n
  rw [pentagonal023ProductCoeffFMLS, FormalMultilinearSeries.ofScalars_norm]
  calc
    ‖(pentagonalProduct023PS ℂ).coeff n‖ * ((1 / 16 : NNReal) : ℝ) ^ n
        ≤ (8 : ℝ) ^ (n + 1) * ((1 / 16 : NNReal) : ℝ) ^ n := by
        gcongr
        exact norm_coeff_pentagonalProduct023PS_complex_le n
    _ = 8 * ((1 / 2 : ℝ) ^ n) := by
        rw [pow_succ]
        rw [show (8 : ℝ) ^ n * 8 * ((1 / 16 : NNReal) : ℝ) ^ n =
          8 * (((8 : ℝ) * ((1 / 16 : NNReal) : ℝ)) ^ n) by
            rw [mul_pow]
            ring]
        norm_num
    _ ≤ 8 := by
        have hpow : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        nlinarith

theorem hasFPowerSeriesOnBall_pentagonal014ProductAnalytic_productCoeff_small :
    HasFPowerSeriesOnBall pentagonal014ProductAnalytic pentagonal014ProductCoeffFMLS 0
      ((1 / 16 : NNReal) : ENNReal) := by
  refine ⟨one_sixteenth_le_pentagonal014ProductCoeffFMLS_radius, by norm_num, ?_⟩
  intro y hy
  rw [zero_add]
  have hy_norm : ‖y‖ < (1 / 16 : ℝ) := by
    have h_radius : (((1 / 16 : NNReal) : ENNReal) =
        ENNReal.ofReal (1 / 16 : ℝ)) := by
      rw [ENNReal.coe_nnreal_eq]
      congr
    have h_ball : y ∈ Metric.ball (0 : ℂ) (1 / 16 : ℝ) := by
      rw [h_radius, Metric.emetric_ball] at hy
      exact hy
    have hdist : dist y (0 : ℂ) < (1 / 16 : ℝ) := Metric.mem_ball.mp h_ball
    rwa [dist_zero_right] at hdist
  have h := hasSum_pentagonalProduct014PS_coeff_mul_pow_of_norm_lt_one_sixteenth y hy_norm
  convert h using 1
  funext n
  rw [pentagonal014ProductCoeffFMLS, FormalMultilinearSeries.ofScalars_apply_eq]
  rw [smul_eq_mul]

theorem hasFPowerSeriesOnBall_pentagonal023ProductAnalytic_productCoeff_small :
    HasFPowerSeriesOnBall pentagonal023ProductAnalytic pentagonal023ProductCoeffFMLS 0
      ((1 / 16 : NNReal) : ENNReal) := by
  refine ⟨one_sixteenth_le_pentagonal023ProductCoeffFMLS_radius, by norm_num, ?_⟩
  intro y hy
  rw [zero_add]
  have hy_norm : ‖y‖ < (1 / 16 : ℝ) := by
    have h_radius : (((1 / 16 : NNReal) : ENNReal) =
        ENNReal.ofReal (1 / 16 : ℝ)) := by
      rw [ENNReal.coe_nnreal_eq]
      congr
    have h_ball : y ∈ Metric.ball (0 : ℂ) (1 / 16 : ℝ) := by
      rw [h_radius, Metric.emetric_ball] at hy
      exact hy
    have hdist : dist y (0 : ℂ) < (1 / 16 : ℝ) := Metric.mem_ball.mp h_ball
    rwa [dist_zero_right] at hdist
  have h := hasSum_pentagonalProduct023PS_coeff_mul_pow_of_norm_lt_one_sixteenth y hy_norm
  convert h using 1
  funext n
  rw [pentagonal023ProductCoeffFMLS, FormalMultilinearSeries.ofScalars_apply_eq]
  rw [smul_eq_mul]

theorem pentagonal014ProductCoeffFMLS_eq_pentagonal014SeriesFMLS :
    pentagonal014ProductCoeffFMLS = pentagonal014SeriesFMLS := by
  have h_prod : HasFPowerSeriesAt pentagonal014ProductAnalytic
      pentagonal014ProductCoeffFMLS 0 :=
    ⟨((1 / 16 : NNReal) : ENNReal),
      hasFPowerSeriesOnBall_pentagonal014ProductAnalytic_productCoeff_small⟩
  have h_series : HasFPowerSeriesAt pentagonal014ProductAnalytic
      pentagonal014SeriesFMLS 0 :=
    ⟨1, hasFPowerSeriesOnBall_pentagonal014ProductAnalytic_series⟩
  exact h_prod.eq_formalMultilinearSeries h_series

theorem pentagonal023ProductCoeffFMLS_eq_pentagonal023SeriesFMLS :
    pentagonal023ProductCoeffFMLS = pentagonal023SeriesFMLS := by
  have h_prod : HasFPowerSeriesAt pentagonal023ProductAnalytic
      pentagonal023ProductCoeffFMLS 0 :=
    ⟨((1 / 16 : NNReal) : ENNReal),
      hasFPowerSeriesOnBall_pentagonal023ProductAnalytic_productCoeff_small⟩
  have h_series : HasFPowerSeriesAt pentagonal023ProductAnalytic
      pentagonal023SeriesFMLS 0 :=
    ⟨1, hasFPowerSeriesOnBall_pentagonal023ProductAnalytic_series⟩
  exact h_prod.eq_formalMultilinearSeries h_series

theorem hasFPowerSeriesOnBall_pentagonal014ProductAnalytic_productCoeff :
    HasFPowerSeriesOnBall pentagonal014ProductAnalytic pentagonal014ProductCoeffFMLS 0 1 := by
  rw [pentagonal014ProductCoeffFMLS_eq_pentagonal014SeriesFMLS]
  exact hasFPowerSeriesOnBall_pentagonal014ProductAnalytic_series

theorem hasFPowerSeriesOnBall_pentagonal023ProductAnalytic_productCoeff :
    HasFPowerSeriesOnBall pentagonal023ProductAnalytic pentagonal023ProductCoeffFMLS 0 1 := by
  rw [pentagonal023ProductCoeffFMLS_eq_pentagonal023SeriesFMLS]
  exact hasFPowerSeriesOnBall_pentagonal023ProductAnalytic_series

theorem pentagonalProduct014PS_eq_pentagonal014SeriesPS_complex_of_productCoeff_taylor
    (hprod :
      HasFPowerSeriesOnBall pentagonal014ProductAnalytic pentagonal014ProductCoeffFMLS 0 1) :
    pentagonalProduct014PS ℂ = pentagonal014SeriesPS ℂ := by
  have h_fps_prod : HasFPowerSeriesAt pentagonal014ProductAnalytic
      pentagonal014ProductCoeffFMLS 0 :=
    ⟨1, hprod⟩
  have h_fps_series : HasFPowerSeriesAt pentagonal014ProductAnalytic
      pentagonal014SeriesFMLS 0 :=
    ⟨1, hasFPowerSeriesOnBall_pentagonal014ProductAnalytic_series⟩
  have h_unique : pentagonal014ProductCoeffFMLS = pentagonal014SeriesFMLS :=
    h_fps_prod.eq_formalMultilinearSeries h_fps_series
  ext n
  have h_coeff : (pentagonalProduct014PS ℂ).coeff n = pentagonal014Coeff ℂ n := by
    have h_prod_coeff : pentagonal014ProductCoeffFMLS.coeff n =
        (pentagonalProduct014PS ℂ).coeff n := by
      simp [pentagonal014ProductCoeffFMLS]
    have h_series_coeff : pentagonal014SeriesFMLS.coeff n = pentagonal014Coeff ℂ n := by
      simp [pentagonal014SeriesFMLS]
    rw [← h_prod_coeff, ← h_series_coeff, h_unique]
  rw [h_coeff, coeff_pentagonal014SeriesPS]

theorem pentagonalProduct023PS_eq_pentagonal023SeriesPS_complex_of_productCoeff_taylor
    (hprod :
      HasFPowerSeriesOnBall pentagonal023ProductAnalytic pentagonal023ProductCoeffFMLS 0 1) :
    pentagonalProduct023PS ℂ = pentagonal023SeriesPS ℂ := by
  have h_fps_prod : HasFPowerSeriesAt pentagonal023ProductAnalytic
      pentagonal023ProductCoeffFMLS 0 :=
    ⟨1, hprod⟩
  have h_fps_series : HasFPowerSeriesAt pentagonal023ProductAnalytic
      pentagonal023SeriesFMLS 0 :=
    ⟨1, hasFPowerSeriesOnBall_pentagonal023ProductAnalytic_series⟩
  have h_unique : pentagonal023ProductCoeffFMLS = pentagonal023SeriesFMLS :=
    h_fps_prod.eq_formalMultilinearSeries h_fps_series
  ext n
  have h_coeff : (pentagonalProduct023PS ℂ).coeff n = pentagonal023Coeff ℂ n := by
    have h_prod_coeff : pentagonal023ProductCoeffFMLS.coeff n =
        (pentagonalProduct023PS ℂ).coeff n := by
      simp [pentagonal023ProductCoeffFMLS]
    have h_series_coeff : pentagonal023SeriesFMLS.coeff n = pentagonal023Coeff ℂ n := by
      simp [pentagonal023SeriesFMLS]
    rw [← h_prod_coeff, ← h_series_coeff, h_unique]
  rw [h_coeff, coeff_pentagonal023SeriesPS]

theorem pentagonalProduct014PS_eq_pentagonal014SeriesPS_complex :
    pentagonalProduct014PS ℂ = pentagonal014SeriesPS ℂ :=
  pentagonalProduct014PS_eq_pentagonal014SeriesPS_complex_of_productCoeff_taylor
    hasFPowerSeriesOnBall_pentagonal014ProductAnalytic_productCoeff

theorem pentagonalProduct023PS_eq_pentagonal023SeriesPS_complex :
    pentagonalProduct023PS ℂ = pentagonal023SeriesPS ℂ :=
  pentagonalProduct023PS_eq_pentagonal023SeriesPS_complex_of_productCoeff_taylor
    hasFPowerSeriesOnBall_pentagonal023ProductAnalytic_productCoeff

end JTPFormalPSPentagonal
end Pending
end QseriesFormalization
