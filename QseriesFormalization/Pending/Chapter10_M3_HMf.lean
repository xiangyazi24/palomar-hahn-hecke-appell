import QseriesFormalization.Pending.Chapter10_M3_Engine

/-!
# The M3 formal Hecke double sum `f_{2,3,2}(x,y,Q^9)`

This file packages the lifted Hickerson-Mortenson `f`-side as a formal
two-variable Hahn-series object.  The q-first exponent of the `(r,s)` term is

`9*r^2 + 27*r*s + 9*s^2 - 9*r - 9*s`,

with the usual Hecke double-cone sign.
-/

open scoped Classical
open Set

namespace QseriesFormalization
namespace Pending
namespace Ch10M3HMf

open QseriesFormalization.Ch10TwoVar
open QseriesFormalization.Pending.Ch10HM
open QseriesFormalization.Pending.Ch10M3Engine

noncomputable section

/-! ## Coefficients, exponents, and cone support -/

/-- Cone coefficient for the lifted `f_{2,3,2}` Hecke double sum. -/
def FhmCoeff (r s : ℤ) : ℚ :=
  if 0 ≤ r ∧ 0 ≤ s then
    negOnePowIntQ (r + s)
  else if r ≤ -1 ∧ s ≤ -1 then
    -negOnePowIntQ (r + s)
  else
    0

/-- Lifted exponent `9*r^2 + 27*r*s + 9*s^2 - 9*r - 9*s`. -/
def FhmExp (r s : ℤ) : ℤ :=
  9 * r * r + 27 * r * s + 9 * s * s - 9 * r - 9 * s

/-- The northeast part of the Hecke cone. -/
def FhmNE (r s : ℤ) : Prop := 0 ≤ r ∧ 0 ≤ s

/-- The southwest part of the Hecke cone. -/
def FhmSW (r s : ℤ) : Prop := r ≤ -1 ∧ s ≤ -1

/-- The support cone for `Fhm`. -/
def FhmCone (r s : ℤ) : Prop := FhmNE r s ∨ FhmSW r s

theorem negOnePowIntQ_add_one (n : ℤ) :
    negOnePowIntQ (n + 1) = -negOnePowIntQ n := by
  rw [negOnePowIntQ_add, show negOnePowIntQ (1 : ℤ) = (-1 : ℚ) by rfl]
  ring

@[simp] theorem negOnePowIntQ_sub_one (n : ℤ) :
    negOnePowIntQ (n - 1) = -negOnePowIntQ n := by
  rw [negOnePowIntQ_sub, show negOnePowIntQ (1 : ℤ) = (-1 : ℚ) by rfl]
  ring

@[simp] theorem negOnePowIntQ_sub_two (n : ℤ) :
    negOnePowIntQ (n - 2) = negOnePowIntQ n := by
  rw [negOnePowIntQ_sub, show negOnePowIntQ (2 : ℤ) = (1 : ℚ) by rfl]
  ring

@[simp] theorem negOnePowIntQ_sub_three (n : ℤ) :
    negOnePowIntQ (n - 3) = -negOnePowIntQ n := by
  rw [negOnePowIntQ_sub, show negOnePowIntQ (3 : ℤ) = (-1 : ℚ) by rfl]
  ring

theorem FhmCoeff_ne_zero_cone {r s : ℤ} (h : FhmCoeff r s ≠ 0) :
    FhmCone r s := by
  unfold FhmCoeff at h
  unfold FhmCone FhmNE FhmSW
  by_cases hne : 0 ≤ r ∧ 0 ≤ s
  · exact Or.inl hne
  · by_cases hsw : r ≤ -1 ∧ s ≤ -1
    · exact Or.inr hsw
    · simp [hne, hsw] at h

theorem FhmCoeff_of_not_cone {r s : ℤ} (h : ¬ FhmCone r s) :
    FhmCoeff r s = 0 := by
  unfold FhmCone FhmNE FhmSW at h
  unfold FhmCoeff
  have hne : ¬ (0 ≤ r ∧ 0 ≤ s) := by
    intro hne
    exact h (Or.inl hne)
  have hsw : ¬ (r ≤ -1 ∧ s ≤ -1) := by
    intro hsw
    exact h (Or.inr hsw)
  simp [hne, hsw]

theorem FhmCoeff_NE {r s : ℤ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    FhmCoeff r s = negOnePowIntQ (r + s) := by
  unfold FhmCoeff
  simp [hr, hs]

theorem FhmCoeff_SW {r s : ℤ} (hr : r ≤ -1) (hs : s ≤ -1) :
    FhmCoeff r s = -negOnePowIntQ (r + s) := by
  unfold FhmCoeff
  have hne : ¬ (0 ≤ r ∧ 0 ≤ s) := by omega
  simp [hne, hr, hs]

theorem FhmCoeff_step_x_bulk {r s : ℤ}
    (hleft : r ≠ 0) (hright : r ≠ 1)
    (hs₁ : s ≠ -1) (hs₂ : s ≠ -2) (hs₃ : s ≠ -3) :
    FhmCoeff r s = -FhmCoeff (r - 2) (s + 3) := by
  by_cases hs_nonneg : 0 ≤ s
  · by_cases hr_nonneg : 0 ≤ r
    · have hr2 : 2 ≤ r := by omega
      rw [FhmCoeff_NE (r := r) (s := s) hr_nonneg hs_nonneg,
        FhmCoeff_NE (r := r - 2) (s := s + 3) (by omega) (by omega)]
      rw [show r - 2 + (s + 3) = (r + s) + 1 by ring, negOnePowIntQ_add_one]
      ring
    · have hrle : r ≤ -1 := by omega
      have hnot0 : ¬ FhmCone r s := by
        unfold FhmCone FhmNE FhmSW
        omega
      have hnot1 : ¬ FhmCone (r - 2) (s + 3) := by
        unfold FhmCone FhmNE FhmSW
        omega
      rw [FhmCoeff_of_not_cone hnot0, FhmCoeff_of_not_cone hnot1]
      ring
  · have hsle : s ≤ -1 := by omega
    by_cases hr_nonneg : 0 ≤ r
    · have hnot0 : ¬ FhmCone r s := by
        unfold FhmCone FhmNE FhmSW
        omega
      by_cases hs3 : s ≤ -4
      · by_cases hr2 : 2 ≤ r
        · rw [FhmCoeff_of_not_cone hnot0,
            FhmCoeff_of_not_cone (r := r - 2) (s := s + 3) (by
              unfold FhmCone FhmNE FhmSW
              omega)]
          ring
        · have hr01 : r = 0 ∨ r = 1 := by omega
          rcases hr01 with rfl | rfl <;> contradiction
      · have hnot1 : ¬ FhmCone (r - 2) (s + 3) := by
          have : False := by omega
          exact False.elim this
        rw [FhmCoeff_of_not_cone hnot0, FhmCoeff_of_not_cone hnot1]
        ring
    · have hrle : r ≤ -1 := by omega
      by_cases hs3 : s ≤ -4
      · rw [FhmCoeff_SW (r := r) (s := s) hrle hsle,
          FhmCoeff_SW (r := r - 2) (s := s + 3) (by omega) (by omega)]
        rw [show r - 2 + (s + 3) = (r + s) + 1 by ring, negOnePowIntQ_add_one]
        ring
      · have hnot1 : ¬ FhmCone (r - 2) (s + 3) := by
          have : False := by omega
          exact False.elim this
        have hnot0 : ¬ FhmCone r s := by
          unfold FhmCone FhmNE FhmSW
          omega
        rw [FhmCoeff_of_not_cone hnot0, FhmCoeff_of_not_cone hnot1]
        ring

@[simp] theorem FhmExp_step_x_identity (r s : ℤ) :
    FhmExp (r - 2) (s + 3) + (54 - 45 * r) = FhmExp r s := by
  unfold FhmExp
  ring

theorem FhmExp_NE_nonneg {r s : ℤ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    0 ≤ FhmExp r s := by
  have hrm : 0 ≤ r * (r - 1) := by
    by_cases h0 : r = 0
    · subst r
      norm_num
    · have h1 : 1 ≤ r := by omega
      exact mul_nonneg hr (by omega)
  have hsm : 0 ≤ s * (s - 1) := by
    by_cases h0 : s = 0
    · subst s
      norm_num
    · have h1 : 1 ≤ s := by omega
      exact mul_nonneg hs (by omega)
  have hrs : 0 ≤ r * s := mul_nonneg hr hs
  unfold FhmExp
  nlinarith

theorem FhmExp_SW_nonneg {r s : ℤ} (hr : r ≤ -1) (hs : s ≤ -1) :
    0 ≤ FhmExp r s := by
  have hr2 : 0 ≤ r * r := by nlinarith [sq_nonneg r]
  have hs2 : 0 ≤ s * s := by nlinarith [sq_nonneg s]
  have hrs : 0 ≤ r * s := mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  unfold FhmExp
  nlinarith

theorem FhmExp_cone_nonneg {r s : ℤ} (h : FhmCone r s) :
    0 ≤ FhmExp r s := by
  rcases h with hne | hsw
  · exact FhmExp_NE_nonneg hne.1 hne.2
  · exact FhmExp_SW_nonneg hsw.1 hsw.2

theorem int_nonneg_sq_le_quadratic_minus_self_add_one {n : ℤ} (hn : 0 ≤ n) :
    n ^ 2 ≤ 9 * (n * n - n) + 1 := by
  by_cases h0 : n = 0
  · subst n
    norm_num
  · by_cases h1 : n = 1
    · subst n
      norm_num
    · have hn2 : 2 ≤ n := by omega
      nlinarith [sq_nonneg (n - 2)]

theorem FhmExp_NE_sq_le_left {r s N : ℤ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hN : FhmExp r s = N) :
    r ^ 2 ≤ N + 1 := by
  have hquad := int_nonneg_sq_le_quadratic_minus_self_add_one hr
  have hsquad : 0 ≤ 9 * (s * s - s) := by
    have hsm : 0 ≤ s * (s - 1) := by
      by_cases h0 : s = 0
      · subst s
        norm_num
      · have h1 : 1 ≤ s := by omega
        exact mul_nonneg hs (by omega)
    nlinarith
  have hrs : 0 ≤ 27 * r * s := by nlinarith [mul_nonneg hr hs]
  unfold FhmExp at hN
  nlinarith

theorem FhmExp_NE_sq_le_right {r s N : ℤ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hN : FhmExp r s = N) :
    s ^ 2 ≤ N + 1 := by
  have hquad := int_nonneg_sq_le_quadratic_minus_self_add_one hs
  have hrquad : 0 ≤ 9 * (r * r - r) := by
    have hrm : 0 ≤ r * (r - 1) := by
      by_cases h0 : r = 0
      · subst r
        norm_num
      · have h1 : 1 ≤ r := by omega
        exact mul_nonneg hr (by omega)
    nlinarith
  have hrs : 0 ≤ 27 * r * s := by nlinarith [mul_nonneg hr hs]
  unfold FhmExp at hN
  nlinarith

theorem FhmExp_SW_sq_le_left {r s N : ℤ}
    (hr : r ≤ -1) (hs : s ≤ -1) (hN : FhmExp r s = N) :
    r ^ 2 ≤ N := by
  have hrs : 0 ≤ r * s := mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  have hs2 : 0 ≤ s * s := by nlinarith [sq_nonneg s]
  have hlinr : 0 ≤ -9 * r := by omega
  have hlins : 0 ≤ -9 * s := by omega
  unfold FhmExp at hN
  nlinarith [sq_nonneg r]

theorem FhmExp_SW_sq_le_right {r s N : ℤ}
    (hr : r ≤ -1) (hs : s ≤ -1) (hN : FhmExp r s = N) :
    s ^ 2 ≤ N := by
  have hrs : 0 ≤ r * s := mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  have hr2 : 0 ≤ r * r := by nlinarith [sq_nonneg r]
  have hlinr : 0 ≤ -9 * r := by omega
  have hlins : 0 ≤ -9 * s := by omega
  unfold FhmExp at hN
  nlinarith [sq_nonneg s]

theorem FhmExp_sq_le_natAbs_add_one_left {r s N : ℤ}
    (hcone : FhmCone r s) (hN : FhmExp r s = N) :
    r ^ 2 ≤ (N.natAbs : ℤ) + 1 := by
  have hNabs : N ≤ (N.natAbs : ℤ) := Int.le_natAbs
  rcases hcone with hne | hsw
  · have hsq := FhmExp_NE_sq_le_left hne.1 hne.2 hN
    omega
  · have hsq := FhmExp_SW_sq_le_left hsw.1 hsw.2 hN
    omega

theorem FhmExp_sq_le_natAbs_add_one_right {r s N : ℤ}
    (hcone : FhmCone r s) (hN : FhmExp r s = N) :
    s ^ 2 ≤ (N.natAbs : ℤ) + 1 := by
  have hNabs : N ≤ (N.natAbs : ℤ) := Int.le_natAbs
  rcases hcone with hne | hsw
  · have hsq := FhmExp_NE_sq_le_right hne.1 hne.2 hN
    omega
  · have hsq := FhmExp_SW_sq_le_right hsw.1 hsw.2 hN
    omega

/-- The exponent envelope containing all nonzero terms of `FhmFamily`. -/
def FhmEnvelope : Set ExpQXY :=
  {g | ∃ r s : ℤ, FhmCoeff r s ≠ 0 ∧ g = expQXY (FhmExp r s) r s}

/-- For a fixed Q-degree, the cone points contributing to `Fhm` are finite. -/
theorem Fhm_finite_fiber (N : ℤ) :
    {p : ℤ × ℤ | FhmCoeff p.1 p.2 ≠ 0 ∧ FhmExp p.1 p.2 = N}.Finite := by
  apply Set.Finite.subset (Set.finite_Icc
    ((-((N.natAbs : ℤ) + 1), -((N.natAbs : ℤ) + 1)) : ℤ × ℤ)
    ((((N.natAbs : ℤ) + 1), ((N.natAbs : ℤ) + 1)) : ℤ × ℤ))
  rintro ⟨r, s⟩ hp
  simp only [Set.mem_setOf_eq] at hp
  obtain ⟨hcoeff, hN⟩ := hp
  have hcone : FhmCone r s := FhmCoeff_ne_zero_cone hcoeff
  have hr2 : r ^ 2 ≤ (N.natAbs : ℤ) + 1 :=
    FhmExp_sq_le_natAbs_add_one_left hcone hN
  have hs2 : s ^ 2 ≤ (N.natAbs : ℤ) + 1 :=
    FhmExp_sq_le_natAbs_add_one_right hcone hN
  rw [Set.mem_Icc, Prod.le_def, Prod.le_def]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    nlinarith [sq_nonneg r, sq_nonneg s, sq_nonneg (r - 1), sq_nonneg (r + 1),
      sq_nonneg (s - 1), sq_nonneg (s + 1), hr2, hs2]

theorem FhmEnvelope_isPWO : FhmEnvelope.IsPWO := by
  apply Set.PartiallyWellOrderedOn.subsetProdLex
  · have hsub : (fun (z : ℤ ×ₗ ExpXY) => (ofLex z).1) '' FhmEnvelope ⊆
        Set.Ici (0 : ℤ) := by
      rintro N ⟨z, hz, rfl⟩
      rcases hz with ⟨r, s, hcoeff, rfl⟩
      exact FhmExp_cone_nonneg (FhmCoeff_ne_zero_cone hcoeff)
    exact ((bddBelow_Ici (a := (0 : ℤ))).isWF.isPWO).mono hsub
  · intro N
    apply Set.Finite.isPWO
    apply Set.Finite.subset (Set.Finite.image
      (fun p : ℤ × ℤ => (toLex (p.1, p.2) : ExpXY)) (Fhm_finite_fiber N))
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    rcases hy with ⟨r, s, hcoeff, hy_eq⟩
    refine ⟨(r, s), ?_, ?_⟩
    · simp only [Set.mem_setOf_eq]
      constructor
      · exact hcoeff
      · have h1 : (ofLex (toLex (N, y) : ExpQXY)).1 =
            (ofLex (expQXY (FhmExp r s) r s)).1 := by
          rw [hy_eq]
        simpa [expQXY] using h1.symm
    · have h2 : (ofLex (toLex (N, y) : ExpQXY)).2 =
          (ofLex (expQXY (FhmExp r s) r s)).2 := by
        rw [hy_eq]
      simpa [expQXY] using h2.symm

/-! ## The formal `S` object and coefficient extraction -/

/-- Summable family whose hsum is the formal `f_{2,3,2}` object. -/
def FhmFamily : HahnSeries.SummableFamily ExpQXY ℚ (ℤ × ℤ) where
  toFun := fun p => monom (FhmExp p.1 p.2) p.1 p.2 (FhmCoeff p.1 p.2)
  isPWO_iUnion_support' := by
    refine FhmEnvelope_isPWO.mono (Set.iUnion_subset (fun p => ?_))
    intro g hg
    refine ⟨p.1, p.2, ?_, ?_⟩
    · by_contra hzero
      rw [HahnSeries.mem_support] at hg
      rw [hzero, monom_zero] at hg
      exact hg rfl
    · exact HahnSeries.support_single_subset hg
  finite_co_support' := by
    intro g
    apply Set.Finite.subset (Set.finite_singleton (((ofLex g).2 |> ofLex).1,
      ((ofLex g).2 |> ofLex).2))
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    rw [Set.mem_singleton_iff]
    unfold monom at hp
    rw [HahnSeries.coeff_single] at hp
    by_cases heq : g = expQXY (FhmExp p.1 p.2) p.1 p.2
    · rw [heq]
      rfl
    · simp [heq] at hp

/-- The formal lifted Hecke double sum. -/
def Fhm : S := FhmFamily.hsum

theorem coeffQXY_Fhm (e r s : ℤ) :
    coeffQXY Fhm e r s = if e = FhmExp r s then FhmCoeff r s else 0 := by
  unfold coeffQXY Fhm
  rw [HahnSeries.SummableFamily.coeff_hsum_eq_sum_of_subset
    (t := ({(r, s)} : Finset (ℤ × ℤ)))]
  · simp only [Finset.sum_singleton]
    change (monom (FhmExp r s) r s (FhmCoeff r s)).coeff (expQXY e r s) =
      if e = FhmExp r s then FhmCoeff r s else 0
    unfold monom
    rw [HahnSeries.coeff_single]
    by_cases h : e = FhmExp r s
    · simp [h]
    · have hne : expQXY e r s ≠ expQXY (FhmExp r s) r s := by
        intro hcon
        exact h (expQXY_inj hcon).1
      simp [h, hne]
  · intro p hp
    simp only [Set.mem_setOf_eq] at hp
    change (monom (FhmExp p.1 p.2) p.1 p.2 (FhmCoeff p.1 p.2)).coeff
      (expQXY e r s) ≠ 0 at hp
    unfold monom at hp
    rw [HahnSeries.coeff_single] at hp
    by_cases heq : expQXY e r s = expQXY (FhmExp p.1 p.2) p.1 p.2
    · have hp_eq : p = (r, s) :=
        Prod.ext (expQXY_inj heq).2.1.symm (expQXY_inj heq).2.2.symm
      simpa using hp_eq
    · simp [heq] at hp

/-- Coefficient extraction for `Fhm`: the `(x,y)` slice is one Q-monomial. -/
theorem coeffXY_Fhm (r s e : ℤ) :
    (coeffXY Fhm r s).coeff e = if e = FhmExp r s then FhmCoeff r s else 0 := by
  rw [coeffXY_coeff, coeffQXY_Fhm]

/-- The `(x,y)` slice of `Fhm` as a single Hahn monomial. -/
theorem coeffXY_Fhm_single (r s : ℤ) :
    coeffXY Fhm r s = HahnSeries.single (FhmExp r s) (FhmCoeff r s) := by
  apply HahnSeries.ext
  funext e
  rw [coeffXY_Fhm, HahnSeries.coeff_single]
  simp

/-! ## x-direction functional-equation defect -/

/-- The slice-level inhomogeneous term after dividing the FE by the LHS
`Q^(45*m)` factor.  Its coefficient is exactly the boundary defect left by the
reindex `(r,s) ↦ (r-2,s+3)`. -/
def FhmInhomSlice (m : ℤ) : QYSlice :=
  fun s => HahnSeries.single (FhmExp m s)
    (FhmCoeff m s + FhmCoeff (m - 2) (s + 3))

/-- The `I_Y` coefficient after taking the `x^m` slice and dividing by
`Q^(45*m)`: the two `x` boundary strips. -/
def FhmIYCoeff (m s : ℤ) : ℚ :=
  if m = 0 then
    negOnePowIntQ s
  else if m = 1 then
    -negOnePowIntQ s
  else
    0

/-- The `I_X` coefficient after taking the `x^m` slice and dividing by
`Q^(45*m)`: the three `y` boundary strips. -/
def FhmIXCoeff (m s : ℤ) : ℚ :=
  if s = -3 then
    negOnePowIntQ (m - 2)
  else if s = -2 then
    -negOnePowIntQ (m - 2)
  else if s = -1 then
    negOnePowIntQ (m - 2)
  else
    0

/-- Slice form of `Q^(-45m) * I_Y`. -/
def FhmIYSlice (m : ℤ) : QYSlice :=
  fun s => HahnSeries.single (FhmExp m s) (FhmIYCoeff m s)

/-- Slice form of `Q^(-45m) * I_X`. -/
def FhmIXSlice (m : ℤ) : QYSlice :=
  fun s => HahnSeries.single (FhmExp m s) (FhmIXCoeff m s)

theorem coeff_FhmInhomSlice (m s e : ℤ) :
    (FhmInhomSlice m s).coeff e =
      if e = FhmExp m s then FhmCoeff m s + FhmCoeff (m - 2) (s + 3) else 0 := by
  unfold FhmInhomSlice
  rw [HahnSeries.coeff_single]
  by_cases h : e = FhmExp m s <;> simp [h]

/-- Slice form of the `x -> Q^45 x` functional equation for the formal
`f`-side, with the boundary theta defect kept explicit as `FhmInhomSlice`. -/
theorem Fhm_homogeneous_x_FE (m : ℤ) :
    sliceX Fhm m =
      scaleQY (-1 : K) (shiftQY (54 - 45 * m) (-3) (sliceX Fhm (m - 2))) +
        FhmInhomSlice m := by
  funext s
  apply HahnSeries.ext
  funext e
  rw [Pi.add_apply]
  rw [sliceX, coeffXY_Fhm]
  unfold scaleQY shiftQY sliceX
  rw [HahnSeries.coeff_add]
  change (if e = FhmExp m s then FhmCoeff m s else 0) =
    ((-1 : K) * (QseriesFormalization.Ch10TwoVar.Qpow (54 - 45 * m) *
        coeffXY Fhm (m - 2) (s - -3))).coeff e +
      (FhmInhomSlice m s).coeff e
  rw [show s - -3 = s + 3 by ring]
  rw [show ((-1 : K) * (QseriesFormalization.Ch10TwoVar.Qpow (54 - 45 * m) *
        coeffXY Fhm (m - 2) (s + 3))).coeff e =
      -((QseriesFormalization.Ch10TwoVar.Qpow (54 - 45 * m) *
        coeffXY Fhm (m - 2) (s + 3)).coeff e) by
        rw [neg_mul, HahnSeries.coeff_neg]
        simp]
  unfold QseriesFormalization.Ch10TwoVar.Qpow
  rw [HahnSeries.coeff_single_mul, one_mul, coeffXY_Fhm, coeff_FhmInhomSlice]
  have hiff :
      e - (54 - 45 * m) = FhmExp (m - 2) (s + 3) ↔ e = FhmExp m s := by
    rw [← FhmExp_step_x_identity m s]
    omega
  by_cases h : e = FhmExp m s
  · rw [if_pos h, if_pos (hiff.mpr h), if_pos h]
    ring
  · rw [if_neg h, if_neg (by intro h'; exact h (hiff.mp h')), if_neg h]
    ring

/-!
The theorem above is the formal reindexing core.  The next layer is the
theta-normal spelling of `FhmInhomSlice`:

* `I_Y = j(y;Q^18) - Q^45*x*j(Q^27*y;Q^18)`;
* `I_X = Q^54*x^2*y^-3*
    (j(x;Q^18) - y*j(Q^27*x;Q^18) + Q^18*y^2*j(Q^54*x;Q^18))`.

After dividing the `x^m` slice by `Q^(45*m)`, those are precisely the five
boundary strips `m = 0`, `m = 1`, and `s = -3,-2,-1`.  The exact finite-window
`jCoeff` reassembly for this spelling is not yet mechanized here; the missing
step is a case split proving `FhmInhomSlice` equals those five unrestricted
bilateral theta slices coefficientwise, with the `m=0,1` and `s=-3,-2,-1`
overlaps cancelling.
-/

#print axioms Fhm_homogeneous_x_FE

end

end Ch10M3HMf
end Pending
end QseriesFormalization

open scoped Classical
open Set

namespace QseriesFormalization
namespace Pending
namespace Ch10M3HMf

open QseriesFormalization.Ch10TwoVar
open QseriesFormalization.Pending.Ch10HM
open QseriesFormalization.Pending.Ch10M3Engine

noncomputable section

/-! ## f-side theta reassembly -/

private theorem FhmCoeff_inhom_eq_theta_m_zero (s : ℤ) :
    FhmCoeff 0 s + FhmCoeff (0 - 2) (s + 3) =
      FhmIYCoeff 0 s + FhmIXCoeff 0 s := by
  by_cases hs_nonneg : 0 ≤ s
  · unfold FhmCoeff FhmIYCoeff FhmIXCoeff
    have hs3le : ¬ s + 3 ≤ -1 := by omega
    have hs3 : s ≠ -3 := by omega
    have hs2 : s ≠ -2 := by omega
    have hs1 : s ≠ -1 := by omega
    simp [hs_nonneg, hs3le, hs3, hs2, hs1]
  · by_cases hs4 : s ≤ -4
    · unfold FhmCoeff FhmIYCoeff FhmIXCoeff
      have hs3le : s + 3 ≤ -1 := by omega
      have hs3 : s ≠ -3 := by omega
      have hs2 : s ≠ -2 := by omega
      have hs1 : s ≠ -1 := by omega
      simp [hs_nonneg, hs3le, hs3, hs2, hs1]
      rw [show (-2 : ℤ) + (s + 3) = s + 1 by ring, negOnePowIntQ_add_one]
      ring
    · have hcases : s = -3 ∨ s = -2 ∨ s = -1 := by omega
      rcases hcases with rfl | rfl | rfl <;>
        norm_num [FhmCoeff, FhmIYCoeff, FhmIXCoeff, negOnePowIntQ]

private theorem FhmCoeff_inhom_eq_theta_m_one (s : ℤ) :
    FhmCoeff 1 s + FhmCoeff (1 - 2) (s + 3) =
      FhmIYCoeff 1 s + FhmIXCoeff 1 s := by
  by_cases hs_nonneg : 0 ≤ s
  · unfold FhmCoeff FhmIYCoeff FhmIXCoeff
    have hs3le : ¬ (s + 3 ≤ -1) := by omega
    have hs3 : s ≠ -3 := by omega
    have hs2 : s ≠ -2 := by omega
    have hs1 : s ≠ -1 := by omega
    simp [hs_nonneg, hs3, hs2, hs1]
    rw [if_neg hs3le]
    rw [show 1 + s = s + 1 by ring, negOnePowIntQ_add_one]
    ring
  · by_cases hs4 : s ≤ -4
    · unfold FhmCoeff FhmIYCoeff FhmIXCoeff
      have hs3le : s + 3 ≤ -1 := by omega
      have hs3 : s ≠ -3 := by omega
      have hs2 : s ≠ -2 := by omega
      have hs1 : s ≠ -1 := by omega
      simp [hs_nonneg, hs3le, hs3, hs2, hs1]
      have hpow : negOnePowIntQ (s + 2) = negOnePowIntQ s := by
        rw [← negOnePowIntQ_sub_two (s + 2)]
        congr 1
        ring
      rw [show (-1 : ℤ) + (s + 3) = s + 2 by ring, hpow]
    · have hcases : s = -3 ∨ s = -2 ∨ s = -1 := by omega
      rcases hcases with rfl | rfl | rfl <;>
        norm_num [FhmCoeff, FhmIYCoeff, FhmIXCoeff, negOnePowIntQ]

private theorem FhmCoeff_inhom_eq_theta_s_neg_three
    (m : ℤ) (hm0 : m ≠ 0) (hm1 : m ≠ 1) :
    FhmCoeff m (-3) + FhmCoeff (m - 2) (-3 + 3) =
      FhmIYCoeff m (-3) + FhmIXCoeff m (-3) := by
  by_cases hm2 : 2 ≤ m
  · unfold FhmCoeff FhmIYCoeff FhmIXCoeff
    have hm_nonneg : 0 ≤ m := by omega
    have hm_not_sw : ¬ m ≤ -1 := by omega
    simp [hm0, hm1, hm_nonneg, hm_not_sw, hm2]
  · have hmle : m ≤ -1 := by omega
    unfold FhmCoeff FhmIYCoeff FhmIXCoeff
    simp [hm0, hm1, hmle, hm2]
    rw [show m + (-3 : ℤ) = (m - 2) - 1 by ring, negOnePowIntQ_sub_one]
    rw [negOnePowIntQ_sub_two]
    ring

private theorem FhmCoeff_inhom_eq_theta_s_neg_two
    (m : ℤ) (hm0 : m ≠ 0) (hm1 : m ≠ 1) :
    FhmCoeff m (-2) + FhmCoeff (m - 2) (-2 + 3) =
      FhmIYCoeff m (-2) + FhmIXCoeff m (-2) := by
  by_cases hm2 : 2 ≤ m
  · unfold FhmCoeff FhmIYCoeff FhmIXCoeff
    have hm_nonneg : 0 ≤ m := by omega
    have hm_not_sw : ¬ m ≤ -1 := by omega
    simp [hm0, hm1, hm_nonneg, hm_not_sw, hm2]
    simp [show m - 2 + 1 = m - 1 by ring]
  · have hmle : m ≤ -1 := by omega
    unfold FhmCoeff FhmIYCoeff FhmIXCoeff
    simp [hm0, hm1, hmle, hm2]
    simp [show m + (-2 : ℤ) = m - 2 by ring]

private theorem FhmCoeff_inhom_eq_theta_s_neg_one
    (m : ℤ) (hm0 : m ≠ 0) (hm1 : m ≠ 1) :
    FhmCoeff m (-1) + FhmCoeff (m - 2) (-1 + 3) =
      FhmIYCoeff m (-1) + FhmIXCoeff m (-1) := by
  by_cases hm2 : 2 ≤ m
  · unfold FhmCoeff FhmIYCoeff FhmIXCoeff
    have hm_nonneg : 0 ≤ m := by omega
    have hm_not_sw : ¬ m ≤ -1 := by omega
    simp [hm0, hm1, hm_nonneg, hm_not_sw, hm2]
  · have hmle : m ≤ -1 := by omega
    unfold FhmCoeff FhmIYCoeff FhmIXCoeff
    simp [hm0, hm1, hmle, hm2]
    rw [show m + (-1 : ℤ) = (m - 2) + 1 by ring, negOnePowIntQ_add_one]
    rw [negOnePowIntQ_sub_two]
    ring

/-- Coefficientwise f-side boundary reassembly into the two `I_Y` strips and
the three `I_X` strips. -/
theorem FhmCoeff_inhom_eq_theta (m s : ℤ) :
    FhmCoeff m s + FhmCoeff (m - 2) (s + 3) =
      FhmIYCoeff m s + FhmIXCoeff m s := by
  by_cases hm0 : m = 0
  · subst m
    exact FhmCoeff_inhom_eq_theta_m_zero s
  · by_cases hm1 : m = 1
    · subst m
      exact FhmCoeff_inhom_eq_theta_m_one s
    · by_cases hs3 : s = -3
      · subst s
        exact FhmCoeff_inhom_eq_theta_s_neg_three m hm0 hm1
      · by_cases hs2 : s = -2
        · subst s
          exact FhmCoeff_inhom_eq_theta_s_neg_two m hm0 hm1
        · by_cases hs1 : s = -1
          · subst s
            exact FhmCoeff_inhom_eq_theta_s_neg_one m hm0 hm1
          · have hbulk := FhmCoeff_step_x_bulk (r := m) (s := s) hm0 hm1 hs1 hs2 hs3
            unfold FhmIYCoeff FhmIXCoeff
            simp [hm0, hm1, hs3, hs2, hs1]
            rw [hbulk]
            ring

/-- Slice-level theta reassembly of the f-side inhomogeneous residual. -/
theorem FhmInhom_eq_theta : ∀ m s, FhmInhomSlice m s = FhmIYSlice m s + FhmIXSlice m s := by
  intro m s
  apply HahnSeries.ext
  funext e
  unfold FhmInhomSlice FhmIYSlice FhmIXSlice
  rw [HahnSeries.coeff_add, HahnSeries.coeff_single, HahnSeries.coeff_single,
    HahnSeries.coeff_single]
  by_cases h : e = FhmExp m s
  · simp [h, FhmCoeff_inhom_eq_theta m s]
  · simp [h]

/-- Genuine f-side x-direction functional equation with the inhomogeneous term
spelled as the explicit theta boundary slices. -/
theorem Fhm_homogeneous_x_FE_theta (m : ℤ) :
    sliceX Fhm m =
      scaleQY (-1) (shiftQY (54 - 45 * m) (-3) (sliceX Fhm (m - 2))) +
        FhmIYSlice m + FhmIXSlice m := by
  rw [Fhm_homogeneous_x_FE m]
  have htheta : FhmInhomSlice m = FhmIYSlice m + FhmIXSlice m := by
    funext s
    exact FhmInhom_eq_theta m s
  rw [htheta]
  rw [add_assoc]

#print axioms FhmInhom_eq_theta
#print axioms Fhm_homogeneous_x_FE_theta

end

end Ch10M3HMf
end Pending
end QseriesFormalization
