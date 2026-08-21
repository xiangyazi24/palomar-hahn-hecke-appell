import QseriesFormalization.Chapter04

/-!
# Chapter 4 — Theorem 4.3 (Jacobi's identity)

**Goal**: `(q;q)_∞^3 = ∑_{n≥0} (-1)^n (2n+1) q^{n(n+1)/2}` for `‖q‖ < 1`.

**Strategy** (see `docs/T43_strategy.md`). Parameterise by `Q : ℂ` with
`Q² = q`. JTP at base `Q`:
```
J(Q, z) = ∑_{n∈ℤ} z^n · Q^(n²) = ∏_{n≥1}(1 - Q^(2n))(1 + zQ^(2n-1))(1 + z⁻¹Q^(2n-1)).
```
At `z = -Q` both sides vanish (the `n=1` factor `(1 + z⁻¹Q)|_{z=-Q} = 0`).
Differentiate in `z`, evaluate at `z = -Q`:

* Series:  `dS/dz|_{z=-Q} = -Q⁻¹ · ∑_{n≥0}(2n+1)(-1)^n q^(n(n+1)/2)`.
* Product: `dP/dz|_{z=-Q} = -Q⁻¹ · (q;q)_∞^3`.

JTP gives equality of functions, hence of derivatives. Cancel `-Q⁻¹`.
Lift via `Complex.exists_sq` for the final wrapper.

This module sets up Phase 1: series-side termwise derivative.
-/

namespace QseriesFormalization
namespace PartI
namespace Ch04

section Theorem43

open scoped Topology
open Filter

/-- The `n`-th term of the bilateral JTP series: `z ↦ z^n · Q^{n²}`. -/
noncomputable def jacobiSeriesT (Q : ℂ) (n : ℤ) : ℂ → ℂ :=
  fun z => z ^ n * Q ^ (n ^ 2)

/-- The termwise derivative: `(n : ℂ) · z^(n-1) · Q^{n²}`. -/
noncomputable def jacobiSeriesT' (Q : ℂ) (n : ℤ) : ℂ → ℂ :=
  fun z => (n : ℂ) * z ^ (n - 1) * Q ^ (n ^ 2)

/-- HasDerivAt for the n-th JTP series term in z (for z ≠ 0). -/
theorem hasDerivAt_jacobiSeriesT (Q : ℂ) (n : ℤ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (jacobiSeriesT Q n) (jacobiSeriesT' Q n z) z := by
  simp only [jacobiSeriesT']
  have h := (hasDerivAt_zpow n z (Or.inl hz)).mul_const (Q ^ (n ^ 2))
  convert h using 1

/-! ## Summability of the derivative-bound series

We need summability of the uniform bound
`u(n) := (n.natAbs : ℝ) * R^(n.natAbs+1) * ‖Q‖^(n.natAbs * n.natAbs)`
over `n : ℤ` (and equivalently over `n : ℕ` via the `int_iff_nat_and_neg`
split). The key fact: `‖Q‖^(n*n)` provides Gaussian-style super-exponential
decay that dominates any polynomial-times-geometric bound on the rest.
-/

/-- For `‖Q‖ < 1` and any real `R`, the bound
`(n : ℝ) * R^(n+1) * ‖Q‖^(n*n)` is summable over `n : ℕ`. -/
theorem summable_jacobiSeriesT'_boundNat (Q : ℂ) (hQ : ‖Q‖ < 1) (R : ℝ) :
    Summable (fun n : ℕ => (n : ℝ) * R ^ (n + 1) * ‖Q‖ ^ (n * n)) := by
  have hQnn : 0 ≤ ‖Q‖ := norm_nonneg _
  by_cases hRzero : R = 0
  · refine summable_zero.congr ?_
    intro n
    simp [hRzero, pow_succ, mul_zero, zero_mul]
  -- R ≠ 0; pick N with |R| * ‖Q‖^N ≤ 1/2.
  have habsR : 0 < |R| := abs_pos.mpr hRzero
  have hQ_pow_tendsto : Tendsto (fun n : ℕ => ‖Q‖ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hQnn hQ
  have hε_pos : 0 < 1 / (2 * |R|) := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hQ_pow_tendsto (1 / (2 * |R|)) hε_pos
  have hN' : ∀ n ≥ N, ‖Q‖ ^ n ≤ 1 / (2 * |R|) := by
    intro n hn
    have hball := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg hQnn n)] at hball
    exact hball.le
  -- Comparison bound `g n := n * |R| * (1/2)^n` (Summable via `pow_mul_geometric`).
  set g : ℕ → ℝ := fun n => (n : ℝ) * |R| * (1 / 2 : ℝ) ^ n
  have hg_summable : Summable g := by
    have base : Summable (fun n : ℕ => (n : ℝ) ^ 1 * (1 / 2 : ℝ) ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (r := (1 / 2 : ℝ)) (by rw [Real.norm_eq_abs]; norm_num)
    have base' : Summable (fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n) := by
      simpa using base
    have := base'.mul_right |R|
    refine this.congr fun n => ?_
    simp [g]; ring
  refine hg_summable.of_norm_bounded_eventually ?_
  rw [Nat.cofinite_eq_atTop]
  refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  -- Bound chain for n ≥ N.
  rw [Real.norm_eq_abs]
  have habs_n : |((n : ℝ))| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
  have habs_pow : |R ^ (n + 1)| = |R| ^ (n + 1) := abs_pow R (n + 1)
  have habs_Q : |‖Q‖ ^ (n * n)| = ‖Q‖ ^ (n * n) :=
    abs_of_nonneg (pow_nonneg hQnn (n * n))
  have habs_f : |(n : ℝ) * R ^ (n + 1) * ‖Q‖ ^ (n * n)| =
      (n : ℝ) * |R| ^ (n + 1) * ‖Q‖ ^ (n * n) := by
    rw [abs_mul, abs_mul, habs_n, habs_pow, habs_Q]
  rw [habs_f]
  -- `‖Q‖^(n*n) ≤ (‖Q‖^N)^n` since `N*n ≤ n*n` for n ≥ N (and ‖Q‖ ≤ 1).
  have hQ_pow_le : ‖Q‖ ^ (n * n) ≤ (‖Q‖ ^ N) ^ n := by
    rw [← pow_mul]
    exact pow_le_pow_of_le_one hQnn hQ.le (Nat.mul_le_mul_right n hn)
  -- |R| * ‖Q‖^N ≤ 1/2.
  have hRQ_le_half : |R| * ‖Q‖ ^ N ≤ 1 / 2 := by
    calc |R| * ‖Q‖ ^ N
        ≤ |R| * (1 / (2 * |R|)) := by
          exact mul_le_mul_of_nonneg_left (hN' N le_rfl) habsR.le
      _ = 1 / 2 := by field_simp
  -- (|R| * ‖Q‖^N)^n ≤ (1/2)^n.
  have hpow_RQ_le : (|R| * ‖Q‖ ^ N) ^ n ≤ (1 / 2 : ℝ) ^ n := by
    apply pow_le_pow_left₀ (by positivity) hRQ_le_half n
  -- Chain.
  calc (n : ℝ) * |R| ^ (n + 1) * ‖Q‖ ^ (n * n)
      ≤ (n : ℝ) * |R| ^ (n + 1) * (‖Q‖ ^ N) ^ n := by
        apply mul_le_mul_of_nonneg_left hQ_pow_le
        exact mul_nonneg (Nat.cast_nonneg n) (pow_nonneg habsR.le _)
    _ = (n : ℝ) * |R| * (|R| * ‖Q‖ ^ N) ^ n := by
        rw [pow_succ, mul_pow]; ring
    _ ≤ (n : ℝ) * |R| * (1 / 2 : ℝ) ^ n := by
        apply mul_le_mul_of_nonneg_left hpow_RQ_le
        exact mul_nonneg (Nat.cast_nonneg n) habsR.le
    _ = g n := by simp [g]

/-- ℤ version: `Summable (fun n : ℤ => n.natAbs * R^(n.natAbs+1) * ‖Q‖^(n.natAbs*n.natAbs))`. -/
theorem summable_jacobiSeriesT'_boundInt (Q : ℂ) (hQ : ‖Q‖ < 1) (R : ℝ) :
    Summable (fun n : ℤ =>
      (n.natAbs : ℝ) * R ^ (n.natAbs + 1) * ‖Q‖ ^ (n.natAbs * n.natAbs)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨?_, ?_⟩
  · refine (summable_jacobiSeriesT'_boundNat Q hQ R).congr fun n => ?_
    simp
  · refine (summable_jacobiSeriesT'_boundNat Q hQ R).congr fun n => ?_
    simp [Int.natAbs_neg]

/-- Helper: `‖y‖^k ≤ R^k.natAbs` for any `k : ℤ`, when `y ≠ 0`,
`‖y‖ ≤ R`, and `‖y‖⁻¹ ≤ R`. -/
private lemma norm_zpow_le_pow_natAbs {y : ℂ} (hy : y ≠ 0) {R : ℝ}
    (hR1 : ‖y‖ ≤ R) (hR2 : ‖y‖⁻¹ ≤ R) (k : ℤ) :
    ‖y‖ ^ k ≤ R ^ k.natAbs := by
  have hy_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  by_cases hk : 0 ≤ k
  · have hcast : ((k.natAbs : ℕ) : ℤ) = k := Int.natAbs_of_nonneg hk
    have hrw : ‖y‖ ^ k = ‖y‖ ^ k.natAbs := by
      conv_lhs => rw [← hcast]
      rw [zpow_natCast]
    rw [hrw]
    exact pow_le_pow_left₀ (norm_nonneg _) hR1 k.natAbs
  · push_neg at hk
    have hnk_nonneg : 0 ≤ -k := by linarith
    have h_natAbs_eq : (-k).natAbs = k.natAbs := Int.natAbs_neg k
    have hcast : (((-k).natAbs : ℕ) : ℤ) = -k := Int.natAbs_of_nonneg hnk_nonneg
    have hk_eq : k = -((k.natAbs : ℕ) : ℤ) := by
      rw [← h_natAbs_eq, hcast]; ring
    have hrw : ‖y‖ ^ k = (‖y‖⁻¹) ^ k.natAbs := by
      conv_lhs => rw [hk_eq]
      rw [zpow_neg, zpow_natCast, ← inv_pow]
    rw [hrw]
    exact pow_le_pow_left₀ (by positivity) hR2 k.natAbs

/-- Uniform pointwise bound on the derivative term `jacobiSeriesT' Q n y`. -/
theorem norm_jacobiSeriesT'_le (Q : ℂ) (n : ℤ) {y : ℂ} {R : ℝ}
    (hy_ne : y ≠ 0) (hyR : ‖y‖ ≤ R) (hyR' : ‖y‖⁻¹ ≤ R) :
    ‖jacobiSeriesT' Q n y‖ ≤
      (n.natAbs : ℝ) * R ^ (n.natAbs + 1) * ‖Q‖ ^ (n.natAbs * n.natAbs) := by
  have hy_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy_ne
  have hR_pos : 0 < R := lt_of_lt_of_le hy_pos hyR
  -- ‖y‖ * ‖y‖⁻¹ = 1 ≤ R * R, so 1 ≤ R² hence R ≥ 1 (R > 0).
  have hR_ge_one : 1 ≤ R := by
    have hprod : ‖y‖ * ‖y‖⁻¹ ≤ R * R := mul_le_mul hyR hyR' (by positivity) hR_pos.le
    rw [mul_inv_cancel₀ hy_pos.ne'] at hprod
    nlinarith [hR_pos]
  -- Decompose norm.
  simp only [jacobiSeriesT', norm_mul]
  -- ‖(n : ℂ)‖ = (n.natAbs : ℝ).
  have hn_norm : ‖(n : ℂ)‖ = (n.natAbs : ℝ) := by
    rw [Complex.norm_intCast, ← Int.cast_abs, ← Nat.cast_natAbs]
  rw [hn_norm]
  -- Bound for ‖y^(n-1)‖.
  have h_y : ‖y ^ (n - 1)‖ ≤ R ^ (n.natAbs + 1) := by
    rw [norm_zpow]
    have hb := norm_zpow_le_pow_natAbs hy_ne hyR hyR' (n - 1)
    -- (n - 1).natAbs ≤ n.natAbs + 1.
    have hle : (n - 1).natAbs ≤ n.natAbs + 1 := by omega
    calc ‖y‖ ^ (n - 1) ≤ R ^ (n - 1).natAbs := hb
      _ ≤ R ^ (n.natAbs + 1) :=
        pow_le_pow_right₀ hR_ge_one hle
  -- Compute ‖Q^(n²)‖.
  have h_Q : ‖Q ^ (n ^ 2)‖ = ‖Q‖ ^ (n.natAbs * n.natAbs) := by
    have hsq_nonneg : (0 : ℤ) ≤ n ^ 2 := sq_nonneg n
    have hnatAbs_eq : (n ^ 2).natAbs = n.natAbs * n.natAbs := by
      rw [sq, Int.natAbs_mul]
    have hsq_eq : ((n.natAbs * n.natAbs : ℕ) : ℤ) = n ^ 2 := by
      rw [← hnatAbs_eq, Int.natAbs_of_nonneg hsq_nonneg]
    rw [show (n^2 : ℤ) = ((n.natAbs * n.natAbs : ℕ) : ℤ) from hsq_eq.symm,
        zpow_natCast, norm_pow]
  rw [h_Q]
  -- Combine.
  have h_nonneg : 0 ≤ (n.natAbs : ℝ) * ‖Q‖ ^ (n.natAbs * n.natAbs) :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (norm_nonneg _) _)
  have h_yQ_bound :
      (n.natAbs : ℝ) * ‖y ^ (n - 1)‖ * ‖Q‖ ^ (n.natAbs * n.natAbs) ≤
      (n.natAbs : ℝ) * R ^ (n.natAbs + 1) * ‖Q‖ ^ (n.natAbs * n.natAbs) := by
    have hn_nonneg : 0 ≤ (n.natAbs : ℝ) := Nat.cast_nonneg _
    have hQ_nonneg : 0 ≤ ‖Q‖ ^ (n.natAbs * n.natAbs) := pow_nonneg (norm_nonneg _) _
    nlinarith [h_y, norm_nonneg (y ^ (n - 1))]
  -- We need to rewrite ‖Q^(n²)‖ to ‖Q‖^(n.natAbs * n.natAbs) on the LHS too.
  -- After `rw [h_Q]`, the LHS already has the right form.
  convert h_yQ_bound using 1

/-! ## The series derivative theorem

The series side `J(Q, z) = ∑_{n∈ℤ} z^n · Q^{n²}` is differentiable in `z`
on the punctured plane, with derivative given by termwise differentiation.
-/

/-- The bilateral JTP series is differentiable in `z` for `z ≠ 0`, with
derivative the termwise-differentiated bilateral series. -/
theorem hasDerivAt_jacobiInfiniteSeries (Q : ℂ) (hQ : ‖Q‖ < 1) {y : ℂ} (hy : y ≠ 0) :
    HasDerivAt (fun z => Ch02.jacobiInfiniteSeries Q z)
      (∑' n : ℤ, jacobiSeriesT' Q n y) y := by
  have hy_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  -- Choose radius `r = ‖y‖/2` for the ball around `y`.
  set r : ℝ := ‖y‖ / 2 with hr_def
  have hr_pos : 0 < r := half_pos hy_pos
  -- Uniform bound `R = max(3‖y‖/2, 2/‖y‖)` covering `‖z‖` and `‖z‖⁻¹`.
  set R : ℝ := max (3 * ‖y‖ / 2) (2 / ‖y‖) with hR_def
  have hR_le_norm : 3 * ‖y‖ / 2 ≤ R := le_max_left _ _
  have hR_le_inv : 2 / ‖y‖ ≤ R := le_max_right _ _
  have hR_pos : 0 < R := lt_of_lt_of_le (by positivity : (0 : ℝ) < 3 * ‖y‖ / 2) hR_le_norm
  -- The open ball.
  let t : Set ℂ := Metric.ball y r
  have ht_open : IsOpen t := Metric.isOpen_ball
  have ht_y : y ∈ t := Metric.mem_ball_self hr_pos
  have ht_preconn : IsPreconnected t := (convex_ball y r).isPreconnected
  -- For `z ∈ t`: `‖y‖/2 ≤ ‖z‖ ≤ 3‖y‖/2`.
  have h_ball_norm : ∀ z ∈ t, ‖z‖ ≤ 3 * ‖y‖ / 2 ∧ ‖y‖ / 2 ≤ ‖z‖ := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h_upper : ‖z‖ ≤ ‖y‖ + r := by
      have := norm_le_norm_add_norm_sub' y z
      have h' : ‖z - y‖ = ‖y - z‖ := norm_sub_rev z y
      have h1 : ‖z‖ ≤ ‖y‖ + ‖z - y‖ := by
        have := norm_sub_norm_le z y
        linarith
      linarith [hz.le]
    have h_lower : ‖y‖ - r ≤ ‖z‖ := by
      have h1 : ‖y‖ - ‖z‖ ≤ ‖y - z‖ := norm_sub_norm_le y z
      have h' : ‖y - z‖ = ‖z - y‖ := norm_sub_rev y z
      rw [h'] at h1
      linarith [hz.le]
    refine ⟨?_, ?_⟩
    · simp only [hr_def] at h_upper; linarith
    · simp only [hr_def] at h_lower; linarith
  -- For `z ∈ t`: `z ≠ 0` and `‖z‖⁻¹ ≤ R`.
  have h_ball_ne : ∀ z ∈ t, z ≠ 0 := by
    intro z hz hz_zero
    have hzn := (h_ball_norm z hz).2
    rw [hz_zero, norm_zero] at hzn
    linarith
  have h_ball_inv : ∀ z ∈ t, ‖z‖⁻¹ ≤ R := by
    intro z hz
    have h_lower := (h_ball_norm z hz).2
    have h_z_pos : 0 < ‖z‖ := lt_of_lt_of_le (half_pos hy_pos) h_lower
    have : ‖z‖⁻¹ ≤ (‖y‖ / 2)⁻¹ := by
      exact inv_anti₀ (half_pos hy_pos) h_lower
    have heq : (‖y‖ / 2)⁻¹ = 2 / ‖y‖ := by
      rw [inv_div]
    rw [heq] at this
    linarith [hR_le_inv]
  have h_ball_le_R : ∀ z ∈ t, ‖z‖ ≤ R := by
    intro z hz
    have h_upper := (h_ball_norm z hz).1
    linarith [hR_le_norm]
  -- Apply `hasDerivAt_tsum_of_isPreconnected`.
  refine hasDerivAt_tsum_of_isPreconnected
    (u := fun n : ℤ =>
      (n.natAbs : ℝ) * R ^ (n.natAbs + 1) * ‖Q‖ ^ (n.natAbs * n.natAbs))
    (g := fun n => jacobiSeriesT Q n)
    (g' := fun n => jacobiSeriesT' Q n)
    (summable_jacobiSeriesT'_boundInt Q hQ R)
    ht_open ht_preconn ?_ ?_ ht_y ?_ ht_y
  · -- HasDerivAt
    intro n z hz
    exact hasDerivAt_jacobiSeriesT Q n (h_ball_ne z hz)
  · -- Uniform bound
    intro n z hz
    exact norm_jacobiSeriesT'_le Q n (h_ball_ne z hz)
      (h_ball_le_R z hz) (h_ball_inv z hz)
  · -- Pointwise summability at `y`
    have := Ch02.summable_jacobiInfiniteSeries_terms Q y hQ
    exact this.congr (fun n => rfl)

/-! ## Phase 2: the product-side derivative at `z = -Q`

We factor the JTP infinite product as

  `jacobiInfiniteProduct Q z = (1 + z⁻¹ Q) · P_mod(z)`

where `P_mod` collects the other factors. At `z = -Q` the first factor
vanishes, so `(jacobiInfiniteProduct Q)' (-Q) = ((1 + z⁻¹ Q))' (-Q) · P_mod (-Q)`.

* `(1 + z⁻¹ Q)' (-Q) = -Q⁻¹` (computed below).
* `P_mod (-Q) = (q;q)_∞ ^ 3`  (uses partial-product limit + Ch02 multipliability).
-/

/-- Derivative of the vanishing factor `z ↦ 1 + z⁻¹ Q` at `z = -Q` is `-Q⁻¹`. -/
theorem hasDerivAt_oneAddInvMul_negQ {Q : ℂ} (hQ_ne : Q ≠ 0) :
    HasDerivAt (fun z : ℂ => 1 + z⁻¹ * Q) (-Q⁻¹) (-Q) := by
  have hnegQ_ne : (-Q : ℂ) ≠ 0 := neg_ne_zero.mpr hQ_ne
  -- d/dz(z⁻¹) = -(z²)⁻¹ at z = -Q ≠ 0
  have h1 : HasDerivAt (fun z : ℂ => z⁻¹) (-((-Q : ℂ) ^ 2)⁻¹) (-Q) := hasDerivAt_inv hnegQ_ne
  -- d/dz(z⁻¹ * Q) = -(z²)⁻¹ * Q
  have h2 : HasDerivAt (fun z : ℂ => z⁻¹ * Q) (-((-Q : ℂ) ^ 2)⁻¹ * Q) (-Q) := h1.mul_const Q
  -- d/dz(1 + z⁻¹ * Q) is the same derivative
  have h3 : HasDerivAt (fun z : ℂ => 1 + z⁻¹ * Q) (-((-Q : ℂ) ^ 2)⁻¹ * Q) (-Q) :=
    h2.const_add 1
  -- Simplify: -((-Q)²)⁻¹ * Q = -Q⁻¹
  have hval : -((-Q : ℂ) ^ 2)⁻¹ * Q = -Q⁻¹ := by
    have hsq : (-Q : ℂ) ^ 2 = Q ^ 2 := by ring
    rw [hsq]; field_simp
  rw [← hval]
  exact h3

/-- Product rule shortcut: if `g x = 0` then `(g · R)'(x) = g'(x) · R(x)`,
provided only that `R` is continuous at `x` (no derivative needed for `R`).

Proof via the slope characterization of `HasDerivAt`:
`(g(y)·R(y) - 0) / (y - x) = (g(y) - g(x))/(y-x) · R(y) → g'(x) · R(x)`. -/
theorem hasDerivAt_mul_of_left_vanish {g R : ℂ → ℂ} {g' x : ℂ}
    (hg : HasDerivAt g g' x) (hg0 : g x = 0) (hR : ContinuousAt R x) :
    HasDerivAt (fun z => g z * R z) (g' * R x) x := by
  rw [hasDerivAt_iff_tendsto_slope]
  have h_slope_g : Tendsto (fun y => (y - x)⁻¹ • (g y - g x)) (𝓝[≠] x) (𝓝 g') := by
    rw [hasDerivAt_iff_tendsto_slope] at hg
    exact hg
  have h_slope_g' : Tendsto (fun y => (y - x)⁻¹ • g y) (𝓝[≠] x) (𝓝 g') := by
    refine h_slope_g.congr' ?_
    filter_upwards with y
    rw [hg0]; simp
  have hR_lim : Tendsto R (𝓝[≠] x) (𝓝 (R x)) :=
    (hR.tendsto).mono_left nhdsWithin_le_nhds
  -- Slope of (g·R) at x: (y-x)⁻¹ · (g(y)R(y) - 0) = ((y-x)⁻¹ · g(y)) · R(y)
  have h_mul : Tendsto (fun y => (y - x)⁻¹ • (g y * R y - g x * R x))
      (𝓝[≠] x) (𝓝 (g' * R x)) := by
    refine (h_slope_g'.mul hR_lim).congr' ?_
    filter_upwards with y
    rw [hg0]; simp; ring
  exact h_mul

/-! ### Local summability for shifted odd-factor family

`ℂ` is a CommMonoid (not CommGroup) under multiplication, so we cannot use
`Multipliable.tprod_eq_zero_mul` (which needs CommGroup). Instead we use
`tprod_eq_zero_mul'`, which requires multipliability of the shifted family.
We build that from `multipliable_one_add_of_summable` and a local geometric bound. -/

/-- Summability of `‖c * Q^(2*(n+2) - 1)‖` over `n : ℕ` for `‖Q‖ < 1`.
This is the shifted analogue of `Ch02.summable_norm_jacobiProduct_odd_tail`. -/
private theorem summable_norm_jacobiProduct_odd_tail_shifted
    (Q c : ℂ) (hQ : ‖Q‖ < 1) :
    Summable fun n : ℕ => ‖c * Q ^ (2 * (n + 2) - 1)‖ := by
  -- Bound by ‖c‖ * ‖Q‖^(2n+3) ≤ ‖c‖ * ‖Q‖^(2n+3); use geometric summability.
  have h_geom : Summable fun n : ℕ => ‖c‖ * ‖Q‖ ^ (2 * n + 3) := by
    have hQnn : 0 ≤ ‖Q‖ := norm_nonneg _
    have h_base : Summable fun n : ℕ => ‖Q‖ ^ n :=
      summable_geometric_of_lt_one hQnn hQ
    -- ‖Q‖^(2n+3) = ‖Q‖^3 * (‖Q‖^2)^n
    have h_sq : Summable fun n : ℕ => (‖Q‖ ^ 2) ^ n := by
      refine summable_geometric_of_lt_one (by positivity) ?_
      calc ‖Q‖ ^ 2 = ‖Q‖ * ‖Q‖ := by ring
        _ < 1 * 1 := mul_lt_mul' hQ.le hQ hQnn one_pos
        _ = 1 := one_mul 1
    have h_scaled : Summable fun n : ℕ => ‖Q‖ ^ 3 * (‖Q‖ ^ 2) ^ n :=
      h_sq.mul_left _
    have h_pow_eq : ∀ n : ℕ, ‖Q‖ ^ (2 * n + 3) = ‖Q‖ ^ 3 * (‖Q‖ ^ 2) ^ n := by
      intro n
      rw [show 2 * n + 3 = 3 + 2 * n from by ring, pow_add, pow_mul]
    refine (h_scaled.mul_left ‖c‖).congr fun n => ?_
    rw [h_pow_eq n]
  refine h_geom.congr fun n => ?_
  rw [norm_mul, norm_pow]
  have h_exp : 2 * (n + 2) - 1 = 2 * n + 3 := by omega
  rw [h_exp]

/-- Multipliability of the shifted odd-factor family. -/
theorem multipliable_jacobiProductOddFactor_shifted
    (Q c : ℂ) (hQ : ‖Q‖ < 1) :
    Multipliable fun n : ℕ => 1 + c * Q ^ (2 * (n + 2) - 1) :=
  multipliable_one_add_of_summable
    (summable_norm_jacobiProduct_odd_tail_shifted Q c hQ)

/-- The `k=0` value of the odd-inv factor for parameter `z⁻¹`. -/
private theorem jacobiProductOddFactor_zinv_zero (Q z : ℂ) :
    Ch02.jacobiProductOddFactor Q z⁻¹ 0 = 1 + z⁻¹ * Q := by
  simp [Ch02.jacobiProductOddFactor]

/-- The `k+1` form of the odd-inv factor matches the shifted family. -/
private theorem jacobiProductOddFactor_zinv_succ (Q z : ℂ) (k : ℕ) :
    Ch02.jacobiProductOddFactor Q z⁻¹ (k + 1) = 1 + z⁻¹ * Q ^ (2 * (k + 2) - 1) := by
  simp [Ch02.jacobiProductOddFactor]

/-- Multipliability of `jacobiProductOddFactor Q z⁻¹ (·+1)` via the shifted form. -/
theorem multipliable_jacobiProductOddFactor_zinv_shifted
    (Q z : ℂ) (hQ : ‖Q‖ < 1) :
    Multipliable fun k : ℕ => Ch02.jacobiProductOddFactor Q z⁻¹ (k + 1) := by
  have h := multipliable_jacobiProductOddFactor_shifted Q z⁻¹ hQ
  refine h.congr fun k => ?_
  exact (jacobiProductOddFactor_zinv_succ Q z k).symm

/-- Split off the `k=0` factor from the odd-inv tprod. -/
theorem tprod_jacobiProductOddFactor_zinv_split (Q z : ℂ) (hQ : ‖Q‖ < 1) :
    (∏' k : ℕ, Ch02.jacobiProductOddFactor Q z⁻¹ k) =
      (1 + z⁻¹ * Q) *
        (∏' k : ℕ, Ch02.jacobiProductOddFactor Q z⁻¹ (k + 1)) := by
  have h := tprod_eq_zero_mul'
    (multipliable_jacobiProductOddFactor_zinv_shifted Q z hQ)
  rw [jacobiProductOddFactor_zinv_zero] at h
  exact h

/-- The product-side tprod decomposes as a product of three sub-tprods. -/
theorem jacobiInfiniteProduct_eq_triple_tprod (Q z : ℂ) (hQ : ‖Q‖ < 1) :
    Ch02.jacobiInfiniteProduct Q z =
      (∏' k : ℕ, Ch02.jacobiProductEvenFactor Q k) *
      (∏' k : ℕ, Ch02.jacobiProductOddFactor Q z k) *
      (∏' k : ℕ, Ch02.jacobiProductOddFactor Q z⁻¹ k) := by
  have h_even := Ch02.multipliable_jacobiProductEvenFactor Q hQ
  have h_z := Ch02.multipliable_jacobiProductOddFactor Q z hQ
  have h_zinv := Ch02.multipliable_jacobiProductOddFactor Q z⁻¹ hQ
  have hP_triple : HasProd
      (fun k : ℕ => Ch02.jacobiProductEvenFactor Q k *
                    Ch02.jacobiProductOddFactor Q z k *
                    Ch02.jacobiProductOddFactor Q z⁻¹ k)
      ((∏' k : ℕ, Ch02.jacobiProductEvenFactor Q k) *
       (∏' k : ℕ, Ch02.jacobiProductOddFactor Q z k) *
       (∏' k : ℕ, Ch02.jacobiProductOddFactor Q z⁻¹ k)) :=
    (h_even.hasProd.mul h_z.hasProd).mul h_zinv.hasProd
  rw [Ch02.jacobiInfiniteProduct_eq_tprod_natFactor]
  exact hP_triple.tprod_eq

/-- The product side factorises with the vanishing factor `(1 + z⁻¹·Q)` extracted. -/
theorem jacobiInfiniteProduct_factor_at_zeroOdd (Q z : ℂ) (hQ : ‖Q‖ < 1) :
    Ch02.jacobiInfiniteProduct Q z = (1 + z⁻¹ * Q) *
      ((∏' k : ℕ, Ch02.jacobiProductEvenFactor Q k) *
       (∏' k : ℕ, Ch02.jacobiProductOddFactor Q z k) *
       (∏' k : ℕ, Ch02.jacobiProductOddFactor Q z⁻¹ (k + 1))) := by
  rw [jacobiInfiniteProduct_eq_triple_tprod Q z hQ,
      tprod_jacobiProductOddFactor_zinv_split Q z hQ]
  ring

/-! ### Evaluation of `P_mod(-Q) = (q;q)_∞^3` -/

/-- At `z = -Q`, the `z`-odd factor collapses to the even factor. -/
private theorem jacobiProductOddFactor_negQ_eq_even (Q : ℂ) (k : ℕ) :
    Ch02.jacobiProductOddFactor Q (-Q) k = Ch02.jacobiProductEvenFactor Q k := by
  show 1 + -Q * Q ^ (2 * (k + 1) - 1) = 1 - Q ^ (2 * (k + 1))
  have hexp : 2 * (k + 1) = (2 * (k + 1) - 1) + 1 := by omega
  rw [show Q ^ (2 * (k + 1)) = Q ^ (2 * (k + 1) - 1) * Q by rw [← pow_succ, ← hexp]]
  ring

/-- At `z⁻¹ = -Q⁻¹`, the shifted `z⁻¹`-odd factor collapses to the even factor. -/
private theorem jacobiProductOddFactor_invNegQ_succ_eq_even
    (Q : ℂ) (hQ : Q ≠ 0) (k : ℕ) :
    Ch02.jacobiProductOddFactor Q (-Q)⁻¹ (k + 1) = Ch02.jacobiProductEvenFactor Q k := by
  simp only [Ch02.jacobiProductOddFactor, Ch02.jacobiProductEvenFactor]
  -- (-Q)⁻¹ = -Q⁻¹ for Q ≠ 0
  have hinv : (-Q : ℂ)⁻¹ = -Q⁻¹ := by
    rw [neg_inv]
  rw [hinv]
  -- 1 + (-Q⁻¹) * Q^(2*((k+1)+1) - 1) = 1 - Q⁻¹ * Q^(2k+3) = 1 - Q^(2k+2) = 1 - Q^(2*(k+1))
  have hexp : 2 * (k + 1 + 1) - 1 = 2 * (k + 1) + 1 := by omega
  rw [hexp, pow_add, pow_one]
  have hQ_pow : Q⁻¹ * (Q ^ (2 * (k + 1)) * Q) = Q ^ (2 * (k + 1)) := by
    field_simp
  linear_combination -hQ_pow

/-- The `z`-odd tprod at `z = -Q` equals the even tprod. -/
theorem tprod_jacobiProductOddFactor_negQ
    (Q : ℂ) :
    (∏' k : ℕ, Ch02.jacobiProductOddFactor Q (-Q) k) =
      ∏' k : ℕ, Ch02.jacobiProductEvenFactor Q k := by
  refine tprod_congr fun k => ?_
  exact jacobiProductOddFactor_negQ_eq_even Q k

/-- The shifted `z⁻¹`-odd tprod at `z = -Q` equals the even tprod. -/
theorem tprod_jacobiProductOddFactor_invNegQ_shifted
    (Q : ℂ) (hQ : Q ≠ 0) :
    (∏' k : ℕ, Ch02.jacobiProductOddFactor Q (-Q)⁻¹ (k + 1)) =
      ∏' k : ℕ, Ch02.jacobiProductEvenFactor Q k := by
  refine tprod_congr fun k => ?_
  exact jacobiProductOddFactor_invNegQ_succ_eq_even Q hQ k

/-- `P_mod` evaluated at `-Q` equals `((q;q)_∞)^3` where `q = Q^2`. -/
theorem jacobiProductMod_at_negQ (Q : ℂ) (hQ : Q ≠ 0) :
    ((∏' k : ℕ, Ch02.jacobiProductEvenFactor Q k) *
     (∏' k : ℕ, Ch02.jacobiProductOddFactor Q (-Q) k) *
     (∏' k : ℕ, Ch02.jacobiProductOddFactor Q (-Q)⁻¹ (k + 1))) =
      (∏' k : ℕ, Ch02.jacobiProductEvenFactor Q k) ^ 3 := by
  rw [tprod_jacobiProductOddFactor_negQ Q,
      tprod_jacobiProductOddFactor_invNegQ_shifted Q hQ]
  ring

/-! ### Phase 3: series-side reindex

The bilateral series derivative at `z = -Q` reindexes via pairing `n ↔ -1 - n`
to a one-sided sum:
`∑' n : ℤ, jacobiSeriesT' Q n (-Q) = -Q⁻¹ · ∑' n : ℕ, (-1)^n · (2n+1) · Q^(n(n+1))`. -/

/-- Closed-form for the term at `y = -Q`, for any `n : ℤ` with `Q ≠ 0`. -/
theorem jacobiSeriesT'_at_negQ (Q : ℂ) (hQ : Q ≠ 0) (n : ℤ) :
    jacobiSeriesT' Q n (-Q) =
      (n : ℂ) * (-1) ^ (n - 1) * Q ^ (n ^ 2 + n - 1) := by
  simp only [jacobiSeriesT']
  have h1 : (-Q : ℂ) ^ (n - 1) = (-1) ^ (n - 1) * Q ^ (n - 1) := by
    rw [show (-Q : ℂ) = (-1 : ℂ) * Q from by ring]
    rw [mul_zpow]
  have hQ_mul : Q ^ (n - 1) * Q ^ (n ^ 2) = Q ^ (n ^ 2 + n - 1) := by
    rw [← zpow_add₀ hQ]
    congr 1; ring
  rw [h1]
  rw [show (n : ℂ) * ((-1) ^ (n - 1) * Q ^ (n - 1)) * Q ^ (n ^ 2) =
          (n : ℂ) * (-1) ^ (n - 1) * (Q ^ (n - 1) * Q ^ (n ^ 2)) from by ring]
  rw [hQ_mul]

/-- Sum of paired terms (`n` and `-1 - n`) at `y = -Q`. -/
theorem jacobiSeriesT'_pair_at_negQ (Q : ℂ) (hQ : Q ≠ 0) (n : ℕ) :
    jacobiSeriesT' Q n (-Q) + jacobiSeriesT' Q (-(1 + (n : ℤ))) (-Q) =
      -Q⁻¹ * ((-1) ^ n * (2 * (n : ℂ) + 1) * Q ^ ((n : ℕ) * (n + 1))) := by
  -- term at n (ℕ): (n : ℂ) · (-1)^(n-1) · Q^(n²+n-1).
  -- term at -1 - n: (-(1+n)) · (-1)^(-(1+n)-1) · Q^((-(1+n))² + (-(1+n)) - 1)
  --              = -(1+n) · (-1)^(-(n+2)) · Q^((n+1)² - (n+1) - 1)
  --              = -(1+n) · (-1)^n · Q^(n²+n-1)
  -- Note: (-1)^(-(n+2)) = (-1)^(n+2) = (-1)^n in ℂ.
  rw [jacobiSeriesT'_at_negQ Q hQ n,
      jacobiSeriesT'_at_negQ Q hQ (-(1 + n))]
  -- First simplify the n-term: (n : ℂ) * (-1)^((n : ℤ) - 1) * Q^((n : ℤ)^2 + n - 1)
  have h_n_exp : ((n : ℤ) ^ 2 + (n : ℤ) - 1 : ℤ) = ((n * (n + 1) : ℕ) : ℤ) - 1 := by
    push_cast; ring
  have h_neg1n : (-1 : ℂ) ^ ((n : ℤ) - 1) = -((-1) ^ n : ℂ) := by
    have : ((n : ℤ) - 1 : ℤ) = (n : ℤ) + (-1 : ℤ) := by ring
    rw [this, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_neg, zpow_one]
    have hn_nat : ((-1 : ℂ)) ^ ((n : ℤ)) = (-1 : ℂ) ^ n := by
      rw [zpow_natCast]
    rw [hn_nat]; ring
  -- For the second term: index is -(1+n), so:
  -- exponent: (-(1+n))^2 + (-(1+n)) - 1 = (1+n)^2 - (1+n) - 1 = n² + n - 1
  have h_neg_n_exp : ((-(1 + (n : ℤ))) ^ 2 + (-(1 + (n : ℤ))) - 1 : ℤ) =
      ((n * (n + 1) : ℕ) : ℤ) - 1 := by
    push_cast; ring
  -- coefficient at -(1+n): -1 power: (-1)^(-(1+n)-1) = (-1)^(-(n+2)) = (-1)^(n+2) = (-1)^n in ℂ
  have h_neg1_paired : (-1 : ℂ) ^ (-(1 + (n : ℤ)) - 1) = ((-1) ^ n : ℂ) := by
    have : (-(1 + (n : ℤ)) - 1 : ℤ) = -((n : ℤ) + 2) := by ring
    rw [this, zpow_neg]
    have heq : (-1 : ℂ) ^ ((n : ℤ) + 2) = (-1 : ℂ) ^ n := by
      have : ((n : ℤ) + 2 : ℤ) = ((n + 2 : ℕ) : ℤ) := by push_cast; ring
      rw [this, zpow_natCast]
      rw [show (n + 2 : ℕ) = n + 1 + 1 from rfl, pow_succ, pow_succ]
      ring
    rw [heq]
    rcases Nat.even_or_odd n with he | ho
    · rw [he.neg_one_pow]; simp
    · rw [ho.neg_one_pow]; simp
  -- Cast the index `-(1 + n)` to ℂ.
  have h_neg_n_cast : ((-(1 + (n : ℤ)) : ℤ) : ℂ) = -(1 + (n : ℂ)) := by push_cast; ring
  rw [h_n_exp, h_neg_n_exp, h_neg1n, h_neg1_paired, h_neg_n_cast]
  -- Q^((n*(n+1) : ℕ) - 1 : ℤ) = Q^(n*(n+1)) * Q⁻¹
  have h_Q_split : Q ^ (((n * (n + 1) : ℕ) : ℤ) - 1) = Q ^ ((n * (n + 1) : ℕ)) * Q⁻¹ := by
    rw [zpow_sub₀ hQ, zpow_one, zpow_natCast, div_eq_mul_inv]
  rw [h_Q_split]
  push_cast
  ring

/-- Summability of the bilateral derivative series at any `y ≠ 0`. -/
theorem summable_jacobiSeriesT'_at (Q : ℂ) (hQ : ‖Q‖ < 1) {y : ℂ} (hy : y ≠ 0) :
    Summable fun n : ℤ => jacobiSeriesT' Q n y := by
  have hy_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  set R : ℝ := max ‖y‖ ‖y‖⁻¹ + 1 with hR_def
  have hR_pos : 0 < R := by
    have h1 : 0 ≤ max ‖y‖ ‖y‖⁻¹ := le_max_iff.mpr (Or.inl hy_pos.le)
    linarith
  have hyR : ‖y‖ ≤ R := by
    have h1 : ‖y‖ ≤ max ‖y‖ ‖y‖⁻¹ := le_max_left _ _
    linarith
  have hyR' : ‖y‖⁻¹ ≤ R := by
    have h1 : ‖y‖⁻¹ ≤ max ‖y‖ ‖y‖⁻¹ := le_max_right _ _
    linarith
  refine (summable_jacobiSeriesT'_boundInt Q hQ R).of_norm_bounded ?_
  intro n
  exact norm_jacobiSeriesT'_le Q n hy hyR hyR'

/-- Summability of the half-series at `y = -Q` (the `n : ℕ` part). -/
theorem summable_jacobiSeriesT'_negQ_nat (Q : ℂ) (hQ : ‖Q‖ < 1) (hQ_ne : Q ≠ 0) :
    Summable fun n : ℕ => jacobiSeriesT' Q n (-Q) := by
  have hnegQ_ne : (-Q : ℂ) ≠ 0 := neg_ne_zero.mpr hQ_ne
  have h := summable_jacobiSeriesT'_at Q hQ hnegQ_ne
  rw [summable_int_iff_summable_nat_and_neg] at h
  exact h.1

/-- Summability of the half-series at `y = -Q` (the negative-integer part). -/
theorem summable_jacobiSeriesT'_negQ_neg (Q : ℂ) (hQ : ‖Q‖ < 1) (hQ_ne : Q ≠ 0) :
    Summable fun n : ℕ => jacobiSeriesT' Q (-((n : ℤ) + 1)) (-Q) := by
  have hnegQ_ne : (-Q : ℂ) ≠ 0 := neg_ne_zero.mpr hQ_ne
  have h := summable_jacobiSeriesT'_at Q hQ hnegQ_ne
  -- ∑'_{n : ℤ} f n = ∑'_{n : ℕ} f n + ∑'_{n : ℕ} f (-(n+1))
  -- via multipliable_int_iff_multipliable_nat_and_neg_add_one's additive form
  have h_comp : Summable fun n : ℕ => jacobiSeriesT' Q (Int.negSucc n) (-Q) :=
    h.comp_injective (i := Int.negSucc) (@Int.negSucc.inj)
  refine h_comp.congr fun n => ?_
  rfl

/-- The bilateral sum at `y = -Q` reindexes to one-sided form via `n ↔ -(1+n)`. -/
theorem tsum_jacobiSeriesT'_negQ_paired (Q : ℂ) (hQ : ‖Q‖ < 1) (hQ_ne : Q ≠ 0) :
    (∑' n : ℤ, jacobiSeriesT' Q n (-Q)) =
      ∑' n : ℕ, (jacobiSeriesT' Q n (-Q) + jacobiSeriesT' Q (-((n : ℤ) + 1)) (-Q)) := by
  have h_nat := summable_jacobiSeriesT'_negQ_nat Q hQ hQ_ne
  have h_neg := summable_jacobiSeriesT'_negQ_neg Q hQ hQ_ne
  have hs_nat : HasSum (fun n : ℕ => jacobiSeriesT' Q n (-Q))
      (∑' n : ℕ, jacobiSeriesT' Q n (-Q)) := h_nat.hasSum
  have hs_neg : HasSum (fun n : ℕ => jacobiSeriesT' Q (-((n : ℤ) + 1)) (-Q))
      (∑' n : ℕ, jacobiSeriesT' Q (-((n : ℤ) + 1)) (-Q)) := h_neg.hasSum
  have hs_int : HasSum (fun n : ℤ => jacobiSeriesT' Q n (-Q))
      ((∑' n : ℕ, jacobiSeriesT' Q n (-Q)) +
       ∑' n : ℕ, jacobiSeriesT' Q (-((n : ℤ) + 1)) (-Q)) :=
    HasSum.of_nat_of_neg_add_one hs_nat hs_neg
  rw [hs_int.tsum_eq, ← h_nat.tsum_add h_neg]

/-- The bilateral derivative-at-`-Q` sum in closed form. -/
theorem tsum_jacobiSeriesT'_negQ_closed (Q : ℂ) (hQ : ‖Q‖ < 1) (hQ_ne : Q ≠ 0) :
    (∑' n : ℤ, jacobiSeriesT' Q n (-Q)) =
      -Q⁻¹ * ∑' n : ℕ,
        ((-1) ^ n * (2 * (n : ℂ) + 1) * Q ^ (n * (n + 1))) := by
  rw [tsum_jacobiSeriesT'_negQ_paired Q hQ hQ_ne]
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have h := jacobiSeriesT'_pair_at_negQ Q hQ_ne n
  rw [show (-((n : ℤ) + 1) : ℤ) = -(1 + (n : ℤ)) from by ring]
  exact h

/-! ### Phase 3 → 2 bridge: transfer derivative via JTP S = P -/

/-- Series and product agree on the punctured plane via JTP. -/
theorem jacobiInfiniteSeries_eqOn_jacobiInfiniteProduct (Q : ℂ) (hQ : ‖Q‖ < 1) :
    ∀ z ∈ ({0} : Set ℂ)ᶜ,
      Ch02.jacobiInfiniteSeries Q z = Ch02.jacobiInfiniteProduct Q z := by
  intro z hz
  have hz_ne : z ≠ 0 := hz
  exact (Ch02.jacobiTripleProduct Q z hQ hz_ne).symm

/-- The product has the same derivative as the series at any `y ≠ 0`. -/
theorem hasDerivAt_jacobiInfiniteProduct (Q : ℂ) (hQ : ‖Q‖ < 1) {y : ℂ} (hy : y ≠ 0) :
    HasDerivAt (fun z => Ch02.jacobiInfiniteProduct Q z)
      (∑' n : ℤ, jacobiSeriesT' Q n y) y := by
  have h_series := hasDerivAt_jacobiInfiniteSeries Q hQ hy
  refine h_series.congr_of_eventuallyEq ?_
  have h_mem : y ∈ ({0} : Set ℂ)ᶜ := hy
  have h_open : IsOpen (({0} : Set ℂ)ᶜ) := isOpen_compl_singleton
  filter_upwards [h_open.mem_nhds h_mem] with z hz
  have hz_ne : z ≠ 0 := hz
  exact Ch02.jacobiTripleProduct Q z hQ hz_ne

/-! ### Phase 2 finish: continuity of `P_mod` at `-Q`

Uses `hasProdUniformlyOn_nat_one_add` (from Mathlib) on a closed ball around `-Q`. -/

/-- Continuity at `-Q` of the second factor `∏' k, (1 + z · Q^(2(k+1)-1))`. -/
theorem continuousAt_jacobiProductOddFactor_z_tprod (Q : ℂ) (hQ : ‖Q‖ < 1) :
    ContinuousAt (fun z : ℂ => ∏' k : ℕ, Ch02.jacobiProductOddFactor Q z k) (-Q) := by
  -- Use closed ball K = closedBall (-Q) 1 (compact in ℂ).
  set K : Set ℂ := Metric.closedBall (-Q) 1
  have hK_compact : IsCompact K := isCompact_closedBall _ _
  have hK_mem : (-Q : ℂ) ∈ K := Metric.mem_closedBall_self zero_le_one
  -- Bound function: u k = (‖Q‖ + 2) * ‖Q‖^(2k+1).
  set u : ℕ → ℝ := fun k => (‖Q‖ + 2) * ‖Q‖ ^ (2 * k + 1)
  have hQnn : 0 ≤ ‖Q‖ := norm_nonneg _
  have hu_summable : Summable u := by
    have h_sq : Summable fun k : ℕ => (‖Q‖ ^ 2) ^ k := by
      refine summable_geometric_of_lt_one (by positivity) ?_
      calc ‖Q‖ ^ 2 = ‖Q‖ * ‖Q‖ := by ring
        _ < 1 * 1 := mul_lt_mul' hQ.le hQ hQnn one_pos
        _ = 1 := one_mul 1
    have h_scaled : Summable fun k : ℕ => ‖Q‖ * (‖Q‖ ^ 2) ^ k := h_sq.mul_left _
    have h_pow_eq : ∀ k : ℕ, ‖Q‖ ^ (2 * k + 1) = ‖Q‖ * (‖Q‖ ^ 2) ^ k := by
      intro k; rw [show 2 * k + 1 = 1 + 2 * k from by ring, pow_add, pow_one, pow_mul]
    refine ((h_scaled.mul_left (‖Q‖ + 2)).congr fun k => ?_)
    simp only [u]
    rw [h_pow_eq k]
  -- Pointwise bound: ‖z · Q^(2(k+1)-1)‖ ≤ u k for z ∈ K.
  have h_bound : ∀ᶠ k in atTop, ∀ z ∈ K, ‖z * Q ^ (2 * (k + 1) - 1)‖ ≤ u k := by
    refine Filter.eventually_atTop.mpr ⟨0, fun k _ z hz => ?_⟩
    have hz_norm : ‖z‖ ≤ ‖Q‖ + 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have h := norm_sub_norm_le z (-Q)
      have : ‖-Q‖ = ‖Q‖ := norm_neg Q
      linarith
    have h_exp : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    rw [norm_mul, norm_pow, h_exp]
    have hQ_pow : ‖Q‖ ^ (2 * k + 1) = ‖Q‖ ^ (2 * k + 1) := rfl
    calc ‖z‖ * ‖Q‖ ^ (2 * k + 1)
        ≤ (‖Q‖ + 1) * ‖Q‖ ^ (2 * k + 1) :=
          mul_le_mul_of_nonneg_right hz_norm (pow_nonneg hQnn _)
      _ ≤ (‖Q‖ + 2) * ‖Q‖ ^ (2 * k + 1) := by
          apply mul_le_mul_of_nonneg_right
          · linarith
          · exact pow_nonneg hQnn _
  -- Continuity of each term.
  have h_cts : ∀ k : ℕ, ContinuousOn (fun z : ℂ => z * Q ^ (2 * (k + 1) - 1)) K := by
    intro k
    fun_prop
  -- Apply Summable.hasProdUniformlyOn_nat_one_add.
  have h_uniform := Summable.hasProdUniformlyOn_nat_one_add (R := ℂ) hK_compact
    hu_summable h_bound h_cts
  -- The tprod is continuous on K.
  have h_continuousOn : ContinuousOn
      (fun z => ∏' k : ℕ, (1 + z * Q ^ (2 * (k + 1) - 1))) K := by
    have h_uniformly := h_uniform.tendstoUniformlyOn
    refine h_uniformly.continuousOn (Filter.Frequently.of_forall fun s => ?_)
    exact continuousOn_finset_prod _ fun i _ => by fun_prop
  -- K ∈ 𝓝 (-Q) since the closed ball of radius 1 around -Q is a nbhd of -Q.
  have hK_nhds : K ∈ 𝓝 (-Q : ℂ) := by
    apply Metric.closedBall_mem_nhds
    exact one_pos
  -- Continuity at -Q follows.
  have h_continuousAt : ContinuousAt
      (fun z => ∏' k : ℕ, (1 + z * Q ^ (2 * (k + 1) - 1))) (-Q) :=
    h_continuousOn.continuousAt hK_nhds
  -- Translate back to jacobiProductOddFactor form.
  have h_eq : (fun z : ℂ => ∏' k : ℕ, Ch02.jacobiProductOddFactor Q z k) =
      fun z => ∏' k : ℕ, (1 + z * Q ^ (2 * (k + 1) - 1)) := by
    funext z
    refine tprod_congr fun k => ?_
    simp [Ch02.jacobiProductOddFactor]
  rw [h_eq]
  exact h_continuousAt

/-- Continuity at `-Q` of the shifted `z⁻¹`-odd factor. -/
theorem continuousAt_jacobiProductOddFactor_zinv_shifted_tprod
    (Q : ℂ) (hQ : ‖Q‖ < 1) (hQ_ne : Q ≠ 0) :
    ContinuousAt
      (fun z : ℂ => ∏' k : ℕ, Ch02.jacobiProductOddFactor Q z⁻¹ (k + 1)) (-Q) := by
  have hQnn : 0 ≤ ‖Q‖ := norm_nonneg _
  have hQ_pos : 0 < ‖Q‖ := norm_pos_iff.mpr hQ_ne
  -- K = closedBall(-Q, ‖Q‖/2). Compact, avoids 0.
  set r : ℝ := ‖Q‖ / 2 with hr_def
  have hr_pos : 0 < r := half_pos hQ_pos
  set K : Set ℂ := Metric.closedBall (-Q) r
  have hK_compact : IsCompact K := isCompact_closedBall _ _
  -- Bound function: u k = 2 * ‖Q‖^(2k+2).
  set u : ℕ → ℝ := fun k => 2 * ‖Q‖ ^ (2 * k + 2)
  have hu_summable : Summable u := by
    have h_sq : Summable fun k : ℕ => (‖Q‖ ^ 2) ^ k := by
      refine summable_geometric_of_lt_one (by positivity) ?_
      calc ‖Q‖ ^ 2 = ‖Q‖ * ‖Q‖ := by ring
        _ < 1 * 1 := mul_lt_mul' hQ.le hQ hQnn one_pos
        _ = 1 := one_mul 1
    have h_scaled : Summable fun k : ℕ => ‖Q‖ ^ 2 * (‖Q‖ ^ 2) ^ k := h_sq.mul_left _
    have h_pow_eq : ∀ k : ℕ, ‖Q‖ ^ (2 * k + 2) = ‖Q‖ ^ 2 * (‖Q‖ ^ 2) ^ k := by
      intro k; rw [show 2 * k + 2 = 2 + 2 * k from by ring, pow_add, pow_mul]
    refine ((h_scaled.mul_left 2).congr fun k => ?_)
    simp only [u]
    rw [h_pow_eq k]
  -- On K, z ≠ 0 and ‖z⁻¹‖ ≤ 2/‖Q‖.
  have hK_ne_zero : ∀ z ∈ K, z ≠ 0 := by
    intro z hz hz_zero
    rw [Metric.mem_closedBall, dist_eq_norm, hz_zero, zero_sub, neg_neg] at hz
    linarith
  have hK_inv_bound : ∀ z ∈ K, ‖z⁻¹‖ ≤ 2 / ‖Q‖ := by
    intro z hz
    have hz_ne := hK_ne_zero z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have h_lower : ‖Q‖ / 2 ≤ ‖z‖ := by
      have h := norm_sub_norm_le (-Q) z
      have h' : ‖-Q‖ = ‖Q‖ := norm_neg Q
      have hsub : ‖-Q - z‖ = ‖z - (-Q)‖ := norm_sub_rev (-Q) z
      rw [hsub] at h
      rw [h'] at h
      linarith
    have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le (half_pos hQ_pos) h_lower
    rw [norm_inv]
    rw [show (2 : ℝ) / ‖Q‖ = (‖Q‖ / 2)⁻¹ from by rw [inv_div]]
    exact inv_anti₀ (half_pos hQ_pos) h_lower
  -- Pointwise bound: ‖z⁻¹ · Q^(2(k+2)-1)‖ ≤ u k for z ∈ K.
  have h_bound : ∀ᶠ k in atTop, ∀ z ∈ K,
      ‖z⁻¹ * Q ^ (2 * (k + 2) - 1)‖ ≤ u k := by
    refine Filter.eventually_atTop.mpr ⟨0, fun k _ z hz => ?_⟩
    have hz_inv_bound : ‖z⁻¹‖ ≤ 2 / ‖Q‖ := hK_inv_bound z hz
    have h_exp : 2 * (k + 2) - 1 = 2 * k + 3 := by omega
    rw [norm_mul, norm_pow, h_exp]
    calc ‖z⁻¹‖ * ‖Q‖ ^ (2 * k + 3)
        ≤ (2 / ‖Q‖) * ‖Q‖ ^ (2 * k + 3) :=
          mul_le_mul_of_nonneg_right hz_inv_bound (pow_nonneg hQnn _)
      _ = 2 * (‖Q‖ ^ (2 * k + 3) / ‖Q‖) := by ring
      _ = 2 * ‖Q‖ ^ (2 * k + 2) := by
          congr 1
          rw [show 2 * k + 3 = (2 * k + 2) + 1 from rfl, pow_succ]
          field_simp
  -- Continuity of each term on K (z⁻¹ continuous since K avoids 0).
  have h_cts : ∀ k : ℕ, ContinuousOn (fun z : ℂ => z⁻¹ * Q ^ (2 * (k + 2) - 1)) K := by
    intro k
    refine ContinuousOn.mul ?_ continuousOn_const
    exact continuousOn_inv₀.mono (fun z hz => hK_ne_zero z hz)
  -- Apply hasProdUniformlyOn_nat_one_add.
  have h_uniform := Summable.hasProdUniformlyOn_nat_one_add (R := ℂ) hK_compact
    hu_summable h_bound h_cts
  have h_continuousOn : ContinuousOn
      (fun z => ∏' k : ℕ, (1 + z⁻¹ * Q ^ (2 * (k + 2) - 1))) K := by
    refine h_uniform.tendstoUniformlyOn.continuousOn (Filter.Frequently.of_forall fun s => ?_)
    refine continuousOn_finset_prod _ fun i _ => ?_
    refine ContinuousOn.add continuousOn_const ?_
    exact h_cts i
  have hK_nhds : K ∈ 𝓝 (-Q : ℂ) := Metric.closedBall_mem_nhds _ hr_pos
  have h_continuousAt : ContinuousAt
      (fun z => ∏' k : ℕ, (1 + z⁻¹ * Q ^ (2 * (k + 2) - 1))) (-Q) :=
    h_continuousOn.continuousAt hK_nhds
  -- Translate back to jacobiProductOddFactor form.
  have h_eq : (fun z : ℂ => ∏' k : ℕ, Ch02.jacobiProductOddFactor Q z⁻¹ (k + 1)) =
      fun z => ∏' k : ℕ, (1 + z⁻¹ * Q ^ (2 * (k + 2) - 1)) := by
    funext z
    refine tprod_congr fun k => ?_
    simp [Ch02.jacobiProductOddFactor]
  rw [h_eq]
  exact h_continuousAt

/-- Continuity at `-Q` of the modified product `P_mod`. -/
theorem continuousAt_jacobiProductMod (Q : ℂ) (hQ : ‖Q‖ < 1) (hQ_ne : Q ≠ 0) :
    ContinuousAt (fun z : ℂ =>
      (∏' k : ℕ, Ch02.jacobiProductEvenFactor Q k) *
      (∏' k : ℕ, Ch02.jacobiProductOddFactor Q z k) *
      (∏' k : ℕ, Ch02.jacobiProductOddFactor Q z⁻¹ (k + 1))) (-Q) := by
  have h1 : ContinuousAt (fun _ : ℂ => ∏' k : ℕ, Ch02.jacobiProductEvenFactor Q k) (-Q) :=
    continuousAt_const
  have h2 := continuousAt_jacobiProductOddFactor_z_tprod Q hQ
  have h3 := continuousAt_jacobiProductOddFactor_zinv_shifted_tprod Q hQ hQ_ne
  exact (h1.mul h2).mul h3

/-! ### Phase 2 finish: derivative of `jacobiInfiniteProduct` at `-Q` -/

/-- The infinite product has derivative `-Q⁻¹·(∏'even)^3` at `z = -Q`. -/
theorem hasDerivAt_jacobiInfiniteProduct_at_negQ_product
    (Q : ℂ) (hQ : ‖Q‖ < 1) (hQ_ne : Q ≠ 0) :
    HasDerivAt (fun z : ℂ => Ch02.jacobiInfiniteProduct Q z)
      (-Q⁻¹ * (∏' k : ℕ, Ch02.jacobiProductEvenFactor Q k) ^ 3) (-Q) := by
  -- Step 1: apply hasDerivAt_mul_of_left_vanish to the factored form.
  set R : ℂ → ℂ := fun z =>
    (∏' k : ℕ, Ch02.jacobiProductEvenFactor Q k) *
    (∏' k : ℕ, Ch02.jacobiProductOddFactor Q z k) *
    (∏' k : ℕ, Ch02.jacobiProductOddFactor Q z⁻¹ (k + 1)) with hR_def
  have h_R_at : R (-Q) = (∏' k : ℕ, Ch02.jacobiProductEvenFactor Q k) ^ 3 := by
    simp only [R]
    exact jacobiProductMod_at_negQ Q hQ_ne
  have h_R_cont : ContinuousAt R (-Q) :=
    continuousAt_jacobiProductMod Q hQ hQ_ne
  have h_g_deriv : HasDerivAt (fun z : ℂ => 1 + z⁻¹ * Q) (-Q⁻¹) (-Q) :=
    hasDerivAt_oneAddInvMul_negQ hQ_ne
  have h_g_zero : (fun z : ℂ => 1 + z⁻¹ * Q) (-Q) = 0 := by
    show 1 + (-Q : ℂ)⁻¹ * Q = 0
    field_simp
    ring
  have h_factored_deriv :
      HasDerivAt (fun z => (1 + z⁻¹ * Q) * R z) (-Q⁻¹ * R (-Q)) (-Q) :=
    hasDerivAt_mul_of_left_vanish h_g_deriv h_g_zero h_R_cont
  rw [h_R_at] at h_factored_deriv
  -- Step 2: jacobiInfiniteProduct = (1 + z⁻¹Q) · R on z ≠ 0 (factorization).
  have h_eq_on : (fun z : ℂ => Ch02.jacobiInfiniteProduct Q z) =ᶠ[𝓝 (-Q)]
      (fun z => (1 + z⁻¹ * Q) * R z) := by
    have h_open : IsOpen (({0} : Set ℂ)ᶜ) := isOpen_compl_singleton
    have h_mem : (-Q : ℂ) ∈ ({0} : Set ℂ)ᶜ := neg_ne_zero.mpr hQ_ne
    filter_upwards [h_open.mem_nhds h_mem] with z hz
    have hz_ne : z ≠ 0 := hz
    simp only [R]
    rw [jacobiInfiniteProduct_factor_at_zeroOdd Q z hQ]
  -- Transfer the derivative via eventuallyEq.
  exact h_factored_deriv.congr_of_eventuallyEq h_eq_on

/-! ### Phase 4: Jacobi's identity in Q-parameterised form -/

/-- Jacobi's identity in Q-parameter form: for `‖Q‖ < 1, Q ≠ 0`,
`(∏' k, 1 - Q^(2(k+1)))^3 = ∑' n : ℕ, (-1)^n · (2n+1) · Q^(n(n+1))`. -/
theorem jacobiIdentity_Q (Q : ℂ) (hQ : ‖Q‖ < 1) (hQ_ne : Q ≠ 0) :
    (∏' k : ℕ, Ch02.jacobiProductEvenFactor Q k) ^ 3 =
      ∑' n : ℕ, ((-1) ^ n * (2 * (n : ℂ) + 1) * Q ^ (n * (n + 1))) := by
  have hnegQ_ne : (-Q : ℂ) ≠ 0 := neg_ne_zero.mpr hQ_ne
  -- Derivative formula via JTP transfer (series side).
  have h_deriv_series :
      HasDerivAt (fun z => Ch02.jacobiInfiniteProduct Q z)
        (∑' n : ℤ, jacobiSeriesT' Q n (-Q)) (-Q) :=
    hasDerivAt_jacobiInfiniteProduct Q hQ hnegQ_ne
  -- Derivative formula via product rule.
  have h_deriv_product :
      HasDerivAt (fun z => Ch02.jacobiInfiniteProduct Q z)
        (-Q⁻¹ * (∏' k : ℕ, Ch02.jacobiProductEvenFactor Q k) ^ 3) (-Q) :=
    hasDerivAt_jacobiInfiniteProduct_at_negQ_product Q hQ hQ_ne
  -- Uniqueness of derivative.
  have h_eq := h_deriv_series.unique h_deriv_product
  -- Replace series with closed form.
  rw [tsum_jacobiSeriesT'_negQ_closed Q hQ hQ_ne] at h_eq
  -- h_eq : -Q⁻¹ * series_sum = -Q⁻¹ * (∏' even)^3.
  -- Cancel -Q⁻¹.
  have hnegQ_inv_ne : (-Q⁻¹ : ℂ) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hQ_ne)
  have h := mul_left_cancel₀ hnegQ_inv_ne h_eq
  exact h.symm

/-! ### Phase 4: q-parameterised Jacobi's identity -/

/-- For `Q² = q` and `n : ℕ`: `Q^(n(n+1)) = q^(n(n+1)/2)`. -/
private theorem Q_pow_eq_q_pow_halved (Q q : ℂ) (hQ_sq : Q ^ 2 = q) (n : ℕ) :
    Q ^ (n * (n + 1)) = q ^ (n * (n + 1) / 2) := by
  have h_even : Even (n * (n + 1)) := Nat.even_mul_succ_self n
  obtain ⟨m, hm⟩ := h_even
  have hm_eq : n * (n + 1) = 2 * m := by linarith
  have h_div : n * (n + 1) / 2 = m := by omega
  rw [h_div, hm_eq, pow_mul, hQ_sq]

/-- Jacobi's identity (Theorem 4.3, q-parameterised form).
For `‖q‖ < 1`: `(∏' k, 1 - q^(k+1))^3 = ∑' n, (-1)^n · (2n+1) · q^(n(n+1)/2)`. -/
theorem jacobiIdentity (q : ℂ) (hq : ‖q‖ < 1) :
    (∏' k : ℕ, (1 - q ^ (k + 1))) ^ 3 =
      ∑' n : ℕ, ((-1) ^ n * (2 * (n : ℂ) + 1) * q ^ (n * (n + 1) / 2)) := by
  by_cases hq_ne : q = 0
  · -- Trivial case q = 0.
    subst hq_ne
    -- LHS: (∏' k, 1 - 0^(k+1))^3 = 1^3 = 1.
    have hL : (∏' k : ℕ, (1 - (0 : ℂ) ^ (k + 1))) ^ 3 = 1 := by
      have h_each : ∀ k : ℕ, (1 - (0 : ℂ) ^ (k + 1)) = 1 := by
        intro k; rw [zero_pow (Nat.succ_ne_zero k)]; ring
      rw [tprod_congr h_each, tprod_one]
      ring
    rw [hL]
    -- RHS: ∑' n, (-1)^n * (2n+1) * 0^(n*(n+1)/2) = at n=0: 1 * 1 * 1 = 1, rest = 0.
    have h_sum : (∑' n : ℕ, ((-1) ^ n * (2 * (n : ℂ) + 1) * (0 : ℂ) ^ (n * (n + 1) / 2))) = 1 := by
      rw [tsum_eq_single 0]
      · simp
      · intro n hn
        have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
        have h_div_pos : 0 < n * (n + 1) / 2 := by
          have : 1 * 2 ≤ n * (n + 1) := by
            apply Nat.mul_le_mul
            · exact hn_pos
            · omega
          omega
        rw [zero_pow (Nat.pos_iff_ne_zero.mp h_div_pos)]
        ring
    rw [h_sum]
  · -- Non-trivial: pick Q with Q² = q via algebraic closure of ℂ.
    obtain ⟨Q, hQ_sq⟩ := IsAlgClosed.exists_pow_nat_eq q (n := 2) (by norm_num)
    have hQ_ne : Q ≠ 0 := by
      intro hQ_zero
      apply hq_ne
      rw [← hQ_sq, hQ_zero]; ring
    have hQ_norm : ‖Q‖ < 1 := by
      have : ‖Q‖ ^ 2 = ‖q‖ := by
        rw [← norm_pow, hQ_sq]
      nlinarith [norm_nonneg Q, sq_nonneg ‖Q‖]
    -- Apply jacobiIdentity_Q.
    have h_Q := jacobiIdentity_Q Q hQ_norm hQ_ne
    -- Translate left side: ∏' k, jacobiProductEvenFactor Q k = ∏' k, (1 - q^(k+1)).
    have h_LHS_eq : ∏' k : ℕ, Ch02.jacobiProductEvenFactor Q k =
        ∏' k : ℕ, (1 - q ^ (k + 1)) := by
      refine tprod_congr fun k => ?_
      simp only [Ch02.jacobiProductEvenFactor]
      have hpow : Q ^ (2 * (k + 1)) = q ^ (k + 1) := by
        rw [pow_mul, hQ_sq]
      rw [hpow]
    -- Translate right side via Q^(n(n+1)) = q^(n(n+1)/2).
    have h_RHS_eq :
        (∑' n : ℕ, ((-1) ^ n * (2 * (n : ℂ) + 1) * Q ^ (n * (n + 1)))) =
        ∑' n : ℕ, ((-1) ^ n * (2 * (n : ℂ) + 1) * q ^ (n * (n + 1) / 2)) := by
      refine tsum_congr fun n => ?_
      rw [Q_pow_eq_q_pow_halved Q q hQ_sq n]
    rw [← h_LHS_eq, ← h_RHS_eq]
    exact h_Q

/-- Jacobi's identity stated using `eulerPentagonalInfiniteProduct` ((q;q)_∞).
For `‖q‖ < 1`: `(q;q)_∞^3 = ∑' n, (-1)^n · (2n+1) · q^(n(n+1)/2)`. -/
theorem jacobiIdentity_pochhammer (q : ℂ) (hq : ‖q‖ < 1) :
    (eulerPentagonalInfiniteProduct q) ^ 3 =
      ∑' n : ℕ, ((-1) ^ n * (2 * (n : ℂ) + 1) * q ^ (n * (n + 1) / 2)) := by
  rw [show eulerPentagonalInfiniteProduct q = ∏' k : ℕ, (1 - q ^ (k + 1)) from rfl]
  exact jacobiIdentity q hq

/-- Jacobi's identity in qPochhammer-limit form: the cube of the partition product equals the
sum over triangular-exponent terms. The finite qPochhammer products tend to the infinite product. -/
theorem tendsto_qPochhammer_cubed_to_jacobiSeries (q : ℂ) (hq : ‖q‖ < 1) :
    Filter.Tendsto (fun N : ℕ => (qPochhammer q N) ^ 3) Filter.atTop
      (nhds (∑' n : ℕ, ((-1) ^ n * (2 * (n : ℂ) + 1) * q ^ (n * (n + 1) / 2)))) := by
  rw [← jacobiIdentity_pochhammer q hq]
  exact (tendsto_eulerPentagonalProductTrunc q hq).pow 3

end Theorem43

end Ch04
end PartI
end QseriesFormalization
