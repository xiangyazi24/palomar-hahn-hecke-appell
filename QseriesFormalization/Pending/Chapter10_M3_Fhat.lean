import QseriesFormalization.Pending.Chapter10_TwoVar

/-!
# The M3 formal cone `Fhat`

This file packages the formal two-variable cone series needed by the M3
endgame.  The exponent is q-first lexicographic via `Ch10TwoVar.ExpQXY`.
-/

open scoped Classical
open Set

namespace QseriesFormalization
namespace Pending
namespace Ch10M3Fhat

open QseriesFormalization.Ch10TwoVar
open QseriesFormalization.Pending.Ch10HM

noncomputable section

/-- Cone coefficient for the formal `Fhat` series. -/
def FhatCoeff (a b : ℤ) : ℚ :=
  if 0 ≤ a ∧ 0 ≤ b then
    negOnePowIntQ (a + b)
  else if a ≤ -1 ∧ b ≤ -1 then
    -negOnePowIntQ (a + b)
  else
    0

/-- Cone exponent `9(a²+3ab+b²)`. -/
def FhatExp (a b : ℤ) : ℤ :=
  9 * (a * a + 3 * a * b + b * b)

/-- The northeast part of the cone. -/
def FhatNE (a b : ℤ) : Prop := 0 ≤ a ∧ 0 ≤ b

/-- The southwest part of the cone. -/
def FhatSW (a b : ℤ) : Prop := a ≤ -1 ∧ b ≤ -1

/-- The support cone for `Fhat`. -/
def FhatCone (a b : ℤ) : Prop := FhatNE a b ∨ FhatSW a b

theorem negOnePowIntQ_add_one (n : ℤ) :
    negOnePowIntQ (n + 1) = -negOnePowIntQ n := by
  rw [negOnePowIntQ_add, show negOnePowIntQ (1 : ℤ) = (-1 : ℚ) by rfl]
  ring

theorem FhatCoeff_ne_zero_cone {a b : ℤ} (h : FhatCoeff a b ≠ 0) :
    FhatCone a b := by
  unfold FhatCoeff at h
  unfold FhatCone FhatNE FhatSW
  by_cases hne : 0 ≤ a ∧ 0 ≤ b
  · exact Or.inl hne
  · by_cases hsw : a ≤ -1 ∧ b ≤ -1
    · exact Or.inr hsw
    · simp [hne, hsw] at h

theorem FhatCoeff_of_not_cone {a b : ℤ} (h : ¬ FhatCone a b) :
    FhatCoeff a b = 0 := by
  unfold FhatCone FhatNE FhatSW at h
  unfold FhatCoeff
  have hne : ¬ (0 ≤ a ∧ 0 ≤ b) := by
    intro hne
    exact h (Or.inl hne)
  have hsw : ¬ (a ≤ -1 ∧ b ≤ -1) := by
    intro hsw
    exact h (Or.inr hsw)
  simp [hne, hsw]

theorem FhatCoeff_NE {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    FhatCoeff a b = negOnePowIntQ (a + b) := by
  unfold FhatCoeff
  simp [ha, hb]

theorem FhatCoeff_SW {a b : ℤ} (ha : a ≤ -1) (hb : b ≤ -1) :
    FhatCoeff a b = -negOnePowIntQ (a + b) := by
  unfold FhatCoeff
  have hne : ¬ (0 ≤ a ∧ 0 ≤ b) := by omega
  simp [hne, ha, hb]

theorem FhatCoeff_step_a_of_ne_neg_one {a b : ℤ} (ha : a ≠ -1) :
    FhatCoeff (a + 1) b = -FhatCoeff a b := by
  by_cases hb0 : 0 ≤ b
  · by_cases ha0 : 0 ≤ a
    · rw [FhatCoeff_NE (a := a + 1) (b := b) (by omega) hb0,
        FhatCoeff_NE (a := a) (b := b) ha0 hb0]
      rw [show a + 1 + b = (a + b) + 1 by ring, negOnePowIntQ_add_one]
    · have ha1 : a ≤ -1 := by omega
      have ha2 : a ≤ -2 := by omega
      have hnot1 : ¬ FhatCone (a + 1) b := by
        unfold FhatCone FhatNE FhatSW
        omega
      have hnot0 : ¬ FhatCone a b := by
        unfold FhatCone FhatNE FhatSW
        omega
      rw [FhatCoeff_of_not_cone hnot1, FhatCoeff_of_not_cone hnot0]
      ring
  · have hb1 : b ≤ -1 := by omega
    by_cases ha0 : 0 ≤ a
    · have hnot1 : ¬ FhatCone (a + 1) b := by
        unfold FhatCone FhatNE FhatSW
        omega
      have hnot0 : ¬ FhatCone a b := by
        unfold FhatCone FhatNE FhatSW
        omega
      rw [FhatCoeff_of_not_cone hnot1, FhatCoeff_of_not_cone hnot0]
      ring
    · have ha1 : a ≤ -1 := by omega
      have ha2 : a ≤ -2 := by omega
      rw [FhatCoeff_SW (a := a + 1) (b := b) (by omega) hb1,
        FhatCoeff_SW (a := a) (b := b) ha1 hb1]
      rw [show a + 1 + b = (a + b) + 1 by ring, negOnePowIntQ_add_one]

@[simp] theorem FhatExp_step_a (a b : ℤ) :
    FhatExp (a + 1) b = FhatExp a b + (18 * a + 9 + 27 * b) := by
  unfold FhatExp
  ring

theorem FhatExp_NE_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ FhatExp a b := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  unfold FhatExp
  nlinarith [sq_nonneg a, sq_nonneg b, hab]

theorem FhatExp_SW_ge_45 {a b : ℤ} (ha : a ≤ -1) (hb : b ≤ -1) :
    45 ≤ FhatExp a b := by
  have ha2 : 1 ≤ a * a := by nlinarith [sq_nonneg (a + 1)]
  have hb2 : 1 ≤ b * b := by nlinarith [sq_nonneg (b + 1)]
  have hb0 : b ≤ 0 := by omega
  have hab1 : 1 ≤ a * b := by
    have hmul : (-1 : ℤ) * b ≤ a * b := mul_le_mul_of_nonpos_right ha hb0
    nlinarith
  unfold FhatExp
  nlinarith

theorem FhatExp_SW_nonneg {a b : ℤ} (ha : a ≤ -1) (hb : b ≤ -1) :
    0 ≤ FhatExp a b := by
  exact le_trans (by norm_num : (0 : ℤ) ≤ 45) (FhatExp_SW_ge_45 ha hb)

theorem FhatExp_cone_nonneg {a b : ℤ} (h : FhatCone a b) :
    0 ≤ FhatExp a b := by
  rcases h with hne | hsw
  · exact FhatExp_NE_nonneg hne.1 hne.2
  · exact FhatExp_SW_nonneg hsw.1 hsw.2

theorem FhatExp_NE_ge_nine_a_sq {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    9 * a ^ 2 ≤ FhatExp a b := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  unfold FhatExp
  nlinarith [sq_nonneg b, hab]

theorem FhatExp_NE_ge_nine_b_sq {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    9 * b ^ 2 ≤ FhatExp a b := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  unfold FhatExp
  nlinarith [sq_nonneg a, hab]

theorem FhatExp_SW_ge_nine_a_sq {a b : ℤ} (ha : a ≤ -1) (hb : b ≤ -1) :
    9 * a ^ 2 ≤ FhatExp a b := by
  have hab : 0 ≤ a * b := mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  unfold FhatExp
  nlinarith [sq_nonneg b, hab]

theorem FhatExp_SW_ge_nine_b_sq {a b : ℤ} (ha : a ≤ -1) (hb : b ≤ -1) :
    9 * b ^ 2 ≤ FhatExp a b := by
  have hab : 0 ≤ a * b := mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  unfold FhatExp
  nlinarith [sq_nonneg a, hab]

theorem FhatExp_sq_le_of_cone_left {a b N : ℤ}
    (hcone : FhatCone a b) (hN : FhatExp a b = N) :
    a ^ 2 ≤ N := by
  rcases hcone with hne | hsw
  · have h9 := FhatExp_NE_ge_nine_a_sq hne.1 hne.2
    nlinarith
  · have h9 := FhatExp_SW_ge_nine_a_sq hsw.1 hsw.2
    nlinarith

theorem FhatExp_sq_le_of_cone_right {a b N : ℤ}
    (hcone : FhatCone a b) (hN : FhatExp a b = N) :
    b ^ 2 ≤ N := by
  rcases hcone with hne | hsw
  · have h9 := FhatExp_NE_ge_nine_b_sq hne.1 hne.2
    nlinarith
  · have h9 := FhatExp_SW_ge_nine_b_sq hsw.1 hsw.2
    nlinarith

/-- The exponent envelope containing all nonzero terms of `FhatFamily`. -/
def FhatEnvelope : Set ExpQXY :=
  {g | ∃ a b : ℤ, FhatCoeff a b ≠ 0 ∧ g = expQXY (FhatExp a b) a b}

/-- For a fixed Q-degree, the cone points contributing to `Fhat` are finite. -/
theorem Fhat_finite_fiber (N : ℤ) :
    {p : ℤ × ℤ | FhatCoeff p.1 p.2 ≠ 0 ∧ FhatExp p.1 p.2 = N}.Finite := by
  apply Set.Finite.subset (Set.finite_Icc
    ((-(N.natAbs : ℤ), -(N.natAbs : ℤ)) : ℤ × ℤ)
    (((N.natAbs : ℤ), (N.natAbs : ℤ)) : ℤ × ℤ))
  rintro ⟨a, b⟩ hp
  simp only [Set.mem_setOf_eq] at hp
  obtain ⟨hcoeff, hN⟩ := hp
  have hcone : FhatCone a b := FhatCoeff_ne_zero_cone hcoeff
  have ha2 : a ^ 2 ≤ N := FhatExp_sq_le_of_cone_left hcone hN
  have hb2 : b ^ 2 ≤ N := FhatExp_sq_le_of_cone_right hcone hN
  have hNn : (N : ℤ) ≤ (N.natAbs : ℤ) := Int.le_natAbs
  rw [Set.mem_Icc, Prod.le_def, Prod.le_def]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - 1), sq_nonneg (a + 1),
      sq_nonneg (b - 1), sq_nonneg (b + 1), ha2, hb2, hNn]

theorem FhatEnvelope_isPWO : FhatEnvelope.IsPWO := by
  apply Set.PartiallyWellOrderedOn.subsetProdLex
  · have hsub : (fun (z : ℤ ×ₗ ExpXY) => (ofLex z).1) '' FhatEnvelope ⊆
        Set.Ici (0 : ℤ) := by
      rintro N ⟨z, hz, rfl⟩
      rcases hz with ⟨a, b, hcoeff, rfl⟩
      exact FhatExp_cone_nonneg (FhatCoeff_ne_zero_cone hcoeff)
    exact ((bddBelow_Ici (a := (0 : ℤ))).isWF.isPWO).mono hsub
  · intro N
    apply Set.Finite.isPWO
    apply Set.Finite.subset (Set.Finite.image
      (fun p : ℤ × ℤ => (toLex (p.1, p.2) : ExpXY)) (Fhat_finite_fiber N))
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    rcases hy with ⟨a, b, hcoeff, hy_eq⟩
    refine ⟨(a, b), ?_, ?_⟩
    · simp only [Set.mem_setOf_eq]
      constructor
      · exact hcoeff
      · have h1 : (ofLex (toLex (N, y) : ExpQXY)).1 =
            (ofLex (expQXY (FhatExp a b) a b)).1 := by
          rw [hy_eq]
        simpa [expQXY] using h1.symm
    · have h2 : (ofLex (toLex (N, y) : ExpQXY)).2 =
          (ofLex (expQXY (FhatExp a b) a b)).2 := by
        rw [hy_eq]
      simpa [expQXY] using h2.symm

/-- Summable family whose hsum is the cone object `Fhat`. -/
def FhatFamily : HahnSeries.SummableFamily ExpQXY ℚ (ℤ × ℤ) where
  toFun := fun p => monom (FhatExp p.1 p.2) p.1 p.2 (FhatCoeff p.1 p.2)
  isPWO_iUnion_support' := by
    refine FhatEnvelope_isPWO.mono (Set.iUnion_subset (fun p => ?_))
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
    by_cases heq : g = expQXY (FhatExp p.1 p.2) p.1 p.2
    · rw [heq]
      rfl
    · simp [heq] at hp

/-- The formal cone object. -/
def Fhat : S := FhatFamily.hsum

theorem coeffQXY_Fhat (e a b : ℤ) :
    coeffQXY Fhat e a b = if e = FhatExp a b then FhatCoeff a b else 0 := by
  unfold coeffQXY Fhat
  rw [HahnSeries.SummableFamily.coeff_hsum_eq_sum_of_subset
    (t := ({(a, b)} : Finset (ℤ × ℤ)))]
  · simp only [Finset.sum_singleton]
    change (monom (FhatExp a b) a b (FhatCoeff a b)).coeff (expQXY e a b) =
      if e = FhatExp a b then FhatCoeff a b else 0
    unfold monom
    rw [HahnSeries.coeff_single]
    by_cases h : e = FhatExp a b
    · simp [h]
    · have hne : expQXY e a b ≠ expQXY (FhatExp a b) a b := by
        intro hcon
        exact h (expQXY_inj hcon).1
      simp [h, hne]
  · intro p hp
    simp only [Set.mem_setOf_eq] at hp
    change (monom (FhatExp p.1 p.2) p.1 p.2 (FhatCoeff p.1 p.2)).coeff
      (expQXY e a b) ≠ 0 at hp
    unfold monom at hp
    rw [HahnSeries.coeff_single] at hp
    by_cases heq : expQXY e a b = expQXY (FhatExp p.1 p.2) p.1 p.2
    · have hp_eq : p = (a, b) :=
        Prod.ext (expQXY_inj heq).2.1.symm (expQXY_inj heq).2.2.symm
      simpa using hp_eq
    · simp [heq] at hp

/-- Coefficient extraction for `Fhat`: the `(x,y)` slice is one Q-monomial. -/
theorem coeffXY_Fhat (a b e : ℤ) :
    (coeffXY Fhat a b).coeff e = if e = FhatExp a b then FhatCoeff a b else 0 := by
  rw [coeffXY_coeff, coeffQXY_Fhat]

/-- The `(x,y)` slice of `Fhat` as a single Hahn monomial. -/
theorem coeffXY_Fhat_single (a b : ℤ) :
    coeffXY Fhat a b = HahnSeries.single (FhatExp a b) (FhatCoeff a b) := by
  apply HahnSeries.ext
  funext e
  rw [coeffXY_Fhat, HahnSeries.coeff_single]
  simp

/-- Bulk x-step functional equation for all columns except the boundary jump `a=-1 → 0`. -/
theorem coeffXY_Fhat_step_x {a b : ℤ} (ha : a ≠ -1) :
    coeffXY Fhat (a + 1) b =
      -QseriesFormalization.Ch10TwoVar.Qpow (18 * a + 9 + 27 * b) * coeffXY Fhat a b := by
  apply HahnSeries.ext
  funext e
  rw [coeffXY_Fhat]
  rw [show (-QseriesFormalization.Ch10TwoVar.Qpow (18 * a + 9 + 27 * b) *
        coeffXY Fhat a b).coeff e =
      -((QseriesFormalization.Ch10TwoVar.Qpow (18 * a + 9 + 27 * b) *
        coeffXY Fhat a b).coeff e) by
        rw [neg_mul, HahnSeries.coeff_neg]]
  unfold QseriesFormalization.Ch10TwoVar.Qpow
  rw [HahnSeries.coeff_single_mul, one_mul, coeffXY_Fhat]
  have hiff :
      e = FhatExp (a + 1) b ↔
        e - (18 * a + 9 + 27 * b) = FhatExp a b := by
    rw [FhatExp_step_a]
    omega
  by_cases h : e = FhatExp (a + 1) b
  · rw [if_pos h, if_pos (hiff.mp h), FhatCoeff_step_a_of_ne_neg_one ha]
  · rw [if_neg h, if_neg (by intro h'; exact h (hiff.mpr h'))]
    ring

/-- Northeast-column boundary at `a=0`. -/
theorem coeffXY_Fhat_a_zero_of_nonneg {b e : ℤ} (hb : 0 ≤ b) :
    (coeffXY Fhat 0 b).coeff e =
      if e = FhatExp 0 b then negOnePowIntQ b else 0 := by
  rw [coeffXY_Fhat, FhatCoeff_NE (a := 0) (b := b) (by norm_num) hb]
  simp

/-- Southwest-column boundary at `a=-1`. -/
theorem coeffXY_Fhat_a_neg_one_of_nonpos {b e : ℤ} (hb : b ≤ -1) :
    (coeffXY Fhat (-1) b).coeff e =
      if e = FhatExp (-1) b then negOnePowIntQ b else 0 := by
  rw [coeffXY_Fhat, FhatCoeff_SW (a := -1) (b := b) (by norm_num) hb]
  have hsign : -negOnePowIntQ ((-1 : ℤ) + b) = negOnePowIntQ b := by
    rw [show (-1 : ℤ) + b = b - 1 by ring, negOnePowIntQ_sub,
      show negOnePowIntQ (1 : ℤ) = (-1 : ℚ) by rfl]
    ring
  rw [hsign]

/-- The boundary transition `a=-1 → 0` is the only x-step not covered by
`coeffXY_Fhat_step_x`; this records the exact coefficient-level defect. -/
theorem coeffXY_Fhat_boundary_jump (b e : ℤ) :
    (coeffXY Fhat 0 b +
        QseriesFormalization.Ch10TwoVar.Qpow (-9 + 27 * b) * coeffXY Fhat (-1) b).coeff e =
      (if e = FhatExp 0 b then FhatCoeff 0 b else 0) +
        (if e - (-9 + 27 * b) = FhatExp (-1) b then FhatCoeff (-1) b else 0) := by
  rw [HahnSeries.coeff_add, coeffXY_Fhat]
  unfold QseriesFormalization.Ch10TwoVar.Qpow
  rw [HahnSeries.coeff_single_mul, one_mul, coeffXY_Fhat]

/-- Shape consumed by the later uniqueness engine: a candidate with this boundary jump and
the same bulk recurrence is expected to agree with `Fhat` coefficientwise. -/
def FhatUniquenessShape (G : S) : Prop :=
  (∀ a b : ℤ, a ≠ -1 →
    coeffXY G (a + 1) b =
      -QseriesFormalization.Ch10TwoVar.Qpow (18 * a + 9 + 27 * b) * coeffXY G a b) ∧
  (∀ b e : ℤ,
    (coeffXY G 0 b + QseriesFormalization.Ch10TwoVar.Qpow (-9 + 27 * b) *
        coeffXY G (-1) b).coeff e =
      (coeffXY Fhat 0 b + QseriesFormalization.Ch10TwoVar.Qpow (-9 + 27 * b) *
        coeffXY Fhat (-1) b).coeff e)

theorem Fhat_satisfies_uniqueness_shape : FhatUniquenessShape Fhat := by
  constructor
  · intro a b ha
    exact coeffXY_Fhat_step_x ha
  · intro b e
    rfl

end

end Ch10M3Fhat
end Pending
end QseriesFormalization
