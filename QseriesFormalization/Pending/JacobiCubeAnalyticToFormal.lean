import QseriesFormalization.Chapter04_T43
import QseriesFormalization.Chapter19
import QseriesFormalization.Chapter19_JacobiTripleSignChar

/-!
# Pending: B2 via analytic → formal Taylor bridge

Independent attack route on the cube convolution identity. Avoids
Sylvester's combinatorial bijection by leveraging the already-proved
**analytic** Jacobi cube identity from Chapter 4:

  `jacobiIdentity_pochhammer (q : ℂ) (hq : ‖q‖ < 1) :
       (eulerPentagonalInfiniteProduct q)^3
         = ∑' n : ℕ, ((-1)^n · (2n+1) · q^(n(n+1)/2))`

The plan: extract coefficient `n` from both sides via analytic Taylor
uniqueness, and identify both with the corresponding formal-PS coefficient.

## Roadmap

Let `f q := (eulerPentagonalInfiniteProduct q)^3` and
    `g q := ∑' n, (-1)^n (2n+1) q^{n(n+1)/2}`.
Both are analytic on `Metric.ball 0 1`, and equal there by
`jacobiIdentity_pochhammer`.

1. **Polynomial truncation agreement (analytic side).**  For `N > n`,
   `f q ≡ ((∏_{k=1}^N (1 - q^k))^3 : polynomial)  (mod q^{N+1})` near 0.
   *Reason*: the tail factors `∏_{k>N}(1 - q^k)` have constant coefficient
   1 and start at order > N, so they don't affect coefficients of degree
   ≤ N.

2. **Polynomial coefficient = formal-PS coefficient.**  For
   `P : ℂ[X]` and `n < deg(P)+1`, `P.coeff n` (polynomial) =
   `(P : ℂ⟦X⟧).coeff n` (formal PS) = analytic Taylor coefficient of
   `P.eval q` at `0`.

3. **Truncation = formal qPochInfPS truncation.**  Already proved as
   `coeff_qPochInfPS_pow_eq_coeff_finite_product_pow`.

4. **RHS Taylor extraction.**  The Taylor coefficient at `0` of `g`
   of order `n` equals `((jacobiTripleSign n : ℤ) : ℂ)` — by index
   unpacking and dominated convergence on the geometric tail.

5. **Combine via analytic uniqueness.**  `HasFPowerSeriesAt.eq_formal-
   MultilinearSeries_of_eventually` (Mathlib) gives that the formal
   multilinear series at 0 of `f` and `g` coincide, hence their
   coefficient functions agree.

Substantial Mathlib infrastructure (`HasFPowerSeriesAt`,
`AnalyticAt.taylor`, `Polynomial.hasFPowerSeries`) is involved. The
steps below isolate the analytic interfaces used by the final bridge.

Once all five are closed, the headline goal in
`Pending/Chapter19_B2_FromCubeConvolution.lean` follows in two lines
(rewrite + ext, matched against this file's bridge theorems).
-/

namespace QseriesFormalization
namespace Pending
namespace JacobiCubeAnalyticToFormal

open QseriesFormalization.PartI.Ch04 (eulerPentagonalInfiniteProduct
  jacobiIdentity_pochhammer)
open QseriesFormalization.PartIV.Ch19 (qPochInfPS jacobiThetaPS jacobiTripleSign
  coeff_jacobiThetaPS coeff_qPochInfPS_pow_eq_coeff_finite_product_pow
  map_qPochInfPS)

/-- **The analytic LHS function**: cube of the Euler pentagonal product. -/
noncomputable def fAnalytic (q : ℂ) : ℂ :=
  (eulerPentagonalInfiniteProduct q) ^ 3

/-- **The analytic RHS function**: triangular-exponent sum. -/
noncomputable def gAnalytic (q : ℂ) : ℂ :=
  ∑' n : ℕ, ((-1) ^ n * (2 * (n : ℂ) + 1) * q ^ (n * (n + 1) / 2))

/-- **Analytic Jacobi cube identity** — restatement of
`Ch04.jacobiIdentity_pochhammer` in this file's notation. -/
theorem fAnalytic_eq_gAnalytic (q : ℂ) (hq : ‖q‖ < 1) :
    fAnalytic q = gAnalytic q := by
  unfold fAnalytic gAnalytic
  exact jacobiIdentity_pochhammer q hq

/-! ### Step 1: polynomial truncation agreement

For each `n`, there exists `N` such that
  `fAnalytic q = ((∏_{k=0}^{N-1} (1 - q^(k+1)))^3) + (higher order tail)`
where the tail contributes 0 to the coefficient of `q^n` for `n < N`.

The right Lean machinery: `HasFPowerSeriesOnBall` + tail estimates.
-/

/- **Step 1.** The analytic Taylor coefficient at `0` of `fAnalytic` of
order `n` equals the polynomial coefficient at order `n` of the finite
truncation `(∏_{k=0}^{n}(1 - X^(k+1)))^3 ∈ ℂ[X]`.

Statement deferred until the Mathlib idiom is fixed (one of
`iteratedFDeriv`, `HasFPowerSeriesAt`, `Analytic.taylorCoeff`).  A
placeholder `True` here would violate the playbook (trivially-true
RHS), so we leave the precise statement out of the file and document
it here as the next concrete dependency. -/

/-! ### Step 2: polynomial coefficient = formal PS coefficient.

This direction is essentially `Polynomial.coe_powerSeries` plus
`Polynomial.coeff_coe` or `PowerSeries.coeff_polynomial`. Mathlib has
the natural ring hom `ℂ[X] →+* ℂ⟦X⟧` (`Polynomial.toPowerSeries`) and
it preserves coefficients.
-/

/-! ### Step 3: truncation = formal qPochInfPS truncation.

Already proved in `Chapter19.coeff_qPochInfPS_pow_eq_coeff_finite_product_pow`.
-/

/-! ### Step 4: RHS Taylor extraction. **CLOSED.**

The reindex `∑' k, jacobiTripleSign k · q^k = ∑' n, (-1)^n (2n+1) q^{T_n}`
is now proved unconditionally in `Chapter19_JacobiTripleSignChar` as
`tsum_jacobiTripleSign_eq_jacobi_series`. -/

/-- **`gAnalytic` in Taylor form.** -/
theorem gAnalytic_eq_tsum_jacobiTripleSign (q : ℂ) :
    gAnalytic q = ∑' k : ℕ, ((jacobiTripleSign k : ℤ) : ℂ) * q ^ k := by
  unfold gAnalytic
  rw [QseriesFormalization.PartIV.Ch19.tsum_jacobiTripleSign_eq_jacobi_series]

/-- **`fAnalytic` in Taylor form** (on the unit disc).  This is the
combined consequence of Ch04's analytic Jacobi identity and Step 4. -/
theorem fAnalytic_eq_tsum_jacobiTripleSign (q : ℂ) (hq : ‖q‖ < 1) :
    fAnalytic q = ∑' k : ℕ, ((jacobiTripleSign k : ℤ) : ℂ) * q ^ k := by
  rw [fAnalytic_eq_gAnalytic q hq, gAnalytic_eq_tsum_jacobiTripleSign]

/-- **HasSum form on the unit disc.**  The sequence
`(fun k => jacobiTripleSign k · q^k)` `HasSum` to `fAnalytic q` for
`‖q‖ < 1`.  Combines summability (from `summable_jacobiTripleSign_mul_pow`)
with the value identity. -/
theorem hasSum_jacobiTripleSign_fAnalytic (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun k : ℕ => ((jacobiTripleSign k : ℤ) : ℂ) * q ^ k)
      (fAnalytic q) := by
  have hsum := QseriesFormalization.PartIV.Ch19.summable_jacobiTripleSign_mul_pow q hq
  have hval := fAnalytic_eq_tsum_jacobiTripleSign q hq
  rw [hval]
  exact hsum.hasSum

/-! ### Step 5: combine via analytic uniqueness.

`Mathlib.Analysis.Analytic.Uniqueness.HasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually`
gives: if `f` and `g` are analytic at `0` with formal multilinear series
`p` and `q` respectively, and `f = g` eventually near `0`, then `p = q`.

Applied here: `fAnalytic` has formal series `ofScalars ℂ (jts ·)` on
`ball 0 1` (the `hasFPowerSeriesOnBall_fAnalytic` below); the formal-PS
`(qPochInfPS ℂ) ^ 3` is also an analytic-PS at 0 (via its coefficients
matching a polynomial truncation up to high order).  By the uniqueness
of formal multilinear series for an analytic function, the coefficient
sequences coincide. -/

/-- **The candidate formal multilinear series** for `fAnalytic` /
`jacobiThetaPS ℂ`: built from the scalar coefficient sequence
`fun n => (jacobiTripleSign n : ℂ)` using Mathlib's `.ofScalars`. -/
noncomputable def jacobiThetaSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => ((jacobiTripleSign n : ℤ) : ℂ))

/-- **Radius bound for `jacobiThetaSeries`** is at least 1, from the
absolute summability of `(jts n : ℂ) · q^n` for any `‖q‖ < 1`. -/
theorem one_le_jacobiThetaSeries_radius :
    (1 : ENNReal) ≤ jacobiThetaSeries.radius := by
  rw [show (1 : ENNReal) = ((1 : NNReal) : ENNReal) by simp]
  apply ENNReal.le_of_forall_nnreal_lt
  intro s hs
  rw [ENNReal.coe_lt_coe] at hs
  have hq_norm : ‖((s : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.coe_nonneg]
    exact_mod_cast hs
  have h_sum := QseriesFormalization.PartIV.Ch19.summable_jacobiTripleSign_mul_pow
    ((s : ℝ) : ℂ) hq_norm
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  have h_sum_norm := h_sum.norm
  have h_eq : (fun n : ℕ => ‖jacobiThetaSeries n‖ * (s : ℝ)^n) =
      (fun n : ℕ => ‖((jacobiTripleSign n : ℤ) : ℂ) * (((s : ℝ) : ℂ))^n‖) := by
    funext n
    rw [jacobiThetaSeries, FormalMultilinearSeries.ofScalars_norm]
    rw [norm_mul, norm_pow]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.coe_nonneg]
  rw [h_eq]
  exact h_sum_norm

/-- **`fAnalytic` has formal power series `jacobiThetaSeries` on the unit
ball at 0.**

Combines the radius bound `one_le_jacobiThetaSeries_radius` with the
pointwise `HasSum` from `hasSum_jacobiTripleSign_fAnalytic`.  Fully
proven — no sorries.  This is the LHS-side analytic-formal bridge that
feeds Step 5 (analytic uniqueness). -/
theorem hasFPowerSeriesOnBall_fAnalytic :
    HasFPowerSeriesOnBall fAnalytic jacobiThetaSeries 0 1 := by
  refine ⟨one_le_jacobiThetaSeries_radius, by positivity, ?_⟩
  intro y hy
  rw [zero_add]
  have hy_norm : ‖y‖ < 1 := by
    have h1 : (1 : ENNReal) = ENNReal.ofReal 1 := by simp
    have h_ball : y ∈ Metric.ball (0 : ℂ) 1 := by
      rw [h1, Metric.emetric_ball] at hy
      exact hy
    have h2 : dist y (0 : ℂ) < 1 := Metric.mem_ball.mp h_ball
    rwa [dist_zero_right] at h2
  have h := hasSum_jacobiTripleSign_fAnalytic y hy_norm
  convert h using 1
  funext n
  rw [jacobiThetaSeries, FormalMultilinearSeries.ofScalars_apply_eq]
  rw [smul_eq_mul]

/-- **`fAnalytic` is analytic at `0` with formal series `jacobiThetaSeries`.** -/
theorem hasFPowerSeriesAt_fAnalytic :
    HasFPowerSeriesAt fAnalytic jacobiThetaSeries 0 :=
  ⟨1, hasFPowerSeriesOnBall_fAnalytic⟩

/-- **The candidate formal series via `cubeConvolution`**: built using
`ofScalars` on `n ↦ (cubeConvolution n : ℂ)`. -/
noncomputable def cubeConvolutionSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun n => ((QseriesFormalization.PartIV.Ch19.cubeConvolution n : ℤ) : ℂ))

/-- Radius bound for `cubeConvolutionSeries`. -/
theorem one_le_cubeConvolutionSeries_radius :
    (1 : ENNReal) ≤ cubeConvolutionSeries.radius := by
  rw [show (1 : ENNReal) = ((1 : NNReal) : ENNReal) by simp]
  apply ENNReal.le_of_forall_nnreal_lt
  intro s hs
  rw [ENNReal.coe_lt_coe] at hs
  have hq_norm : ‖((s : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.coe_nonneg]
    exact_mod_cast hs
  have h_sum := QseriesFormalization.PartIV.Ch19.summable_norm_qpow_cubeConvolution
    ((s : ℝ) : ℂ) hq_norm
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  have h_eq : (fun n : ℕ => ‖cubeConvolutionSeries n‖ * (s : ℝ)^n) =
      (fun n : ℕ =>
        ‖((s : ℝ) : ℂ)^n *
          ((QseriesFormalization.PartIV.Ch19.cubeConvolution n : ℤ) : ℂ)‖) := by
    funext n
    rw [cubeConvolutionSeries, FormalMultilinearSeries.ofScalars_norm]
    rw [norm_mul, norm_pow]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.coe_nonneg]
    ring
  rw [h_eq]
  exact h_sum

/-- `fAnalytic` has the cubeConvolution formal series on the unit ball. -/
theorem hasFPowerSeriesOnBall_fAnalytic_cubeConvolution :
    HasFPowerSeriesOnBall fAnalytic cubeConvolutionSeries 0 1 := by
  refine ⟨one_le_cubeConvolutionSeries_radius, by positivity, ?_⟩
  intro y hy
  rw [zero_add]
  have hy_norm : ‖y‖ < 1 := by
    have h1 : (1 : ENNReal) = ENNReal.ofReal 1 := by simp
    have h_ball : y ∈ Metric.ball (0 : ℂ) 1 := by
      rw [h1, Metric.emetric_ball] at hy
      exact hy
    have h2 : dist y (0 : ℂ) < 1 := Metric.mem_ball.mp h_ball
    rwa [dist_zero_right] at h2
  -- HasSum of cubeConvolutionSeries · y^n to fAnalytic y.
  have h_summable :=
    QseriesFormalization.PartIV.Ch19.summable_qpow_cubeConvolution y hy_norm
  have h_tsum :=
    QseriesFormalization.PartIV.Ch19.eulerPentagonalInfiniteProduct_cube_eq_tsum_qpow_cubeConvolution
      y hy_norm
  have h_fAnalytic_eq : fAnalytic y = ∑' n : ℕ, y^n *
      ((QseriesFormalization.PartIV.Ch19.cubeConvolution n : ℤ) : ℂ) := by
    show (eulerPentagonalInfiniteProduct y)^3 = _
    exact h_tsum
  rw [h_fAnalytic_eq]
  have h_hassum := h_summable.hasSum
  convert h_hassum using 1
  funext n
  rw [cubeConvolutionSeries, FormalMultilinearSeries.ofScalars_apply_eq]
  rw [smul_eq_mul]
  ring

/-- **HEADLINE: `(qPochInfPS ℂ)^3 = jacobiThetaPS ℂ`** in formal power series.

Proof: BOTH `cubeConvolutionSeries` (via `cubeConvolution`) and
`jacobiThetaSeries` (via `jacobiTripleSign`) are HasFPowerSeriesOnBall
of `fAnalytic` at 0 (radius ≥ 1).  By
`HasFPowerSeriesAt.eq_formalMultilinearSeries`, the formal multilinear
series coincide.  By `ofScalars_series_eq_iff` (with `Nontrivial ℂ`),
their scalar sequences coincide pointwise: `cubeConvolution n = jts n` ∀n.
Bridge via `coeff_qPochInfPS_pow_three_int_eq_cubeConvolution` then gives
the formal-PS identity. -/
theorem qPochInfPS_pow_three_eq_jacobiThetaPS_complex :
    (qPochInfPS ℂ) ^ 3 = jacobiThetaPS ℂ := by
  -- Step 1: cubeConvolutionSeries = jacobiThetaSeries by uniqueness.
  have h_fps_cube : HasFPowerSeriesAt fAnalytic cubeConvolutionSeries 0 :=
    ⟨1, hasFPowerSeriesOnBall_fAnalytic_cubeConvolution⟩
  have h_fps_jts : HasFPowerSeriesAt fAnalytic jacobiThetaSeries 0 :=
    hasFPowerSeriesAt_fAnalytic
  have h_unique : cubeConvolutionSeries = jacobiThetaSeries :=
    h_fps_cube.eq_formalMultilinearSeries h_fps_jts
  -- Step 2: extract coefficient equality.
  have h_coeff : ∀ n : ℕ,
      ((QseriesFormalization.PartIV.Ch19.cubeConvolution n : ℤ) : ℂ) =
      ((jacobiTripleSign n : ℤ) : ℂ) := by
    intro n
    have h_cube_coeff : cubeConvolutionSeries.coeff n =
        ((QseriesFormalization.PartIV.Ch19.cubeConvolution n : ℤ) : ℂ) := by
      simp [cubeConvolutionSeries]
    have h_jts_coeff : jacobiThetaSeries.coeff n =
        ((jacobiTripleSign n : ℤ) : ℂ) := by
      simp [jacobiThetaSeries]
    rw [← h_cube_coeff, ← h_jts_coeff, h_unique]
  -- Step 3: lift to integer level.
  have h_int : ∀ n : ℕ,
      QseriesFormalization.PartIV.Ch19.cubeConvolution n = jacobiTripleSign n := by
    intro n
    have := h_coeff n
    exact_mod_cast this
  -- Step 4: extract coefficient identity for (qPochInfPS ℂ)^3 = jacobiThetaPS ℂ.
  ext n
  rw [QseriesFormalization.PartIV.Ch19.coeff_jacobiThetaPS]
  -- Use coeff_qPochInfPS_pow_three_int_eq_cubeConvolution + lift to ℂ.
  have h_int_eq : ((QseriesFormalization.PartIV.Ch19.qPochInfPS ℤ)^3).coeff n =
      QseriesFormalization.PartIV.Ch19.cubeConvolution n := by
    have := QseriesFormalization.PartIV.Ch19.coeff_qPochInfPS_pow_three_int_eq_cubeConvolution n
    unfold QseriesFormalization.PartIV.Ch19.cubeConvolution
    exact this
  -- Bridge ℤ → ℂ via map.
  have h_map : PowerSeries.map (Int.castRingHom ℂ) ((qPochInfPS ℤ)^3) =
      (qPochInfPS ℂ)^3 := by
    rw [map_pow, map_qPochInfPS]
  have h_cast : ((qPochInfPS ℂ)^3).coeff n =
      (((qPochInfPS ℤ)^3).coeff n : ℂ) := by
    rw [← h_map, PowerSeries.coeff_map]; rfl
  rw [h_cast, h_int_eq, h_int n]

/-- **Integer version**: from the complex version via injectivity of
`PowerSeries.map (Int.castRingHom ℂ)`.

This is the clean integer payoff: once the complex analytic identity
becomes a formal-PS identity (the deep `_complex` step), the ℤ version
drops out in 10 lines with no further math. -/
theorem qPochInfPS_pow_three_eq_jacobiThetaPS_int :
    (qPochInfPS ℤ) ^ 3 = jacobiThetaPS ℤ := by
  -- Apply `PowerSeries.map (Int.castRingHom ℂ)` to both sides and
  -- use injectivity to descend.
  apply PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective
  rw [map_pow, map_qPochInfPS]
  -- Goal: (qPochInfPS ℂ)^3 = PowerSeries.map (Int.castRingHom ℂ) (jacobiThetaPS ℤ)
  rw [qPochInfPS_pow_three_eq_jacobiThetaPS_complex]
  -- Goal: jacobiThetaPS ℂ = PowerSeries.map (Int.castRingHom ℂ) (jacobiThetaPS ℤ)
  ext n
  rw [PowerSeries.coeff_map, coeff_jacobiThetaPS, coeff_jacobiThetaPS]
  simp

/-- **General version**: for any commutative ring `R`,
`(qPochInfPS R)^3 = jacobiThetaPS R`.

Lift from the integer version via `PowerSeries.map (Int.castRingHom R)`
+ `map_qPochInfPS` naturality. -/
theorem qPochInfPS_pow_three_eq_jacobiThetaPS (R : Type*) [CommRing R] :
    (qPochInfPS R) ^ 3 = jacobiThetaPS R := by
  have h_int := qPochInfPS_pow_three_eq_jacobiThetaPS_int
  have h_map_lift := congrArg (PowerSeries.map (Int.castRingHom R)) h_int
  rw [map_pow] at h_map_lift
  rw [map_qPochInfPS] at h_map_lift
  have h_jacobi_map : PowerSeries.map (Int.castRingHom R) (jacobiThetaPS ℤ) =
      jacobiThetaPS R := by
    ext n
    rw [PowerSeries.coeff_map, coeff_jacobiThetaPS, coeff_jacobiThetaPS]
    simp
  rw [h_jacobi_map] at h_map_lift
  exact h_map_lift

/-- **Corollary**: `(qPochInfPS R)^6 = (jacobiThetaPS R)^2`. Building block for
the analogous proof of `∀ n, 7 ∣ p(7n + 5)` (Ramanujan's second congruence). -/
theorem qPochInfPS_pow_six_eq_jacobiThetaPS_pow_two (R : Type*) [CommRing R] :
    (qPochInfPS R) ^ 6 = (jacobiThetaPS R) ^ 2 := by
  have h_b2 := qPochInfPS_pow_three_eq_jacobiThetaPS R
  calc (qPochInfPS R) ^ 6
      = ((qPochInfPS R) ^ 3) ^ 2 := by ring
    _ = (jacobiThetaPS R) ^ 2 := by rw [h_b2]

end JacobiCubeAnalyticToFormal
end Pending
end QseriesFormalization
