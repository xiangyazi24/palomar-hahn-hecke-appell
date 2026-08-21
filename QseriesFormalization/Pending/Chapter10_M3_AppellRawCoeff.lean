import QseriesFormalization.Pending.Chapter10_M3_AppellMhat

/-!
# Appell-side raw coefficient helpers

This file contains the row-family-to-raw-term coefficient expansion used by
both `AppellCoeffNF` and `DiagClose`.  Keeping it separate avoids the import
cycle that would otherwise prevent `AppellCoeffNF` from using the qInv
cancellation lemmas in `DiagClose`.
-/

namespace QseriesFormalization.Pending.Ch10M3Ghat

open QseriesFormalization.Ch10TwoVar
open QseriesFormalization.Pending.Ch10HM
open QseriesFormalization.Pending.Ch10M3Mhat
open QseriesFormalization.Pending.Ch10M3MhatFE2
open scoped Classical

noncomputable section

/-- Per-row raw expansion: one row's `lead·jTheta·Appell·dTheta` coefficient = a finsum over the
`MhatRowFamilyOf` 4-index `((k,(r,t)),m)` (reverse of `MhatRowFamilyOf_hsum` + `coeff_hsum`). -/
theorem coeff_Mhat_row_raw (row : MhatRow) (e x y : ℤ) :
    (row.lead.toMonom *
      ((mhatJThetaFamily row).hsum *
        ((mhatAppellFamilyOf mhatAppellPWO 1 row).hsum *
          (mhatDThetaFamily 1 row).hsum))).coeff (expQXY e x y)
    = ∑ᶠ idx : (ℤ × (ℤ × ℤ)) × ℤ,
        ((MhatRowFamilyOf mhatAppellPWO 1 row) idx).coeff (expQXY e x y) := by
  rw [← MhatRowFamilyOf_hsum, HahnSeries.SummableFamily.coeff_hsum]

/-- The `MhatRowFamilyOf` term at `((k,(r,t)),m)` is the explicit 4-monom product
`lead · jTheta(k) · Appell(r,t) · dTheta(m)`. -/
theorem MhatRowFamily_term (row : MhatRow) (k r t m : ℤ) :
    (MhatRowFamilyOf mhatAppellPWO 1 row) (((k, (r, t)), m)) =
      row.lead.toMonom *
        ((mhatJThetaFamily row).toFun k *
          (mhatAppellFamilyOf mhatAppellPWO 1 row).toFun (r, t) *
            (mhatDThetaFamily 1 row).toFun m) := by
  rfl

/-- `thetaQDeg 18 e r = 9r(r-1)+er` (the A=18 analogue of `thetaQDeg_90`). -/
theorem thetaQDeg_18 (e r : ℤ) : thetaQDeg 18 e r = 9 * r * (r - 1) + e * r := by
  unfold thetaQDeg
  have h2 := two_mul_Tn r
  have hT : 18 * Tn r = 9 * r * (r - 1) := by nlinarith
  rw [hT]

/-- S-level identity: the 4-monom product `lead·jTheta(k)·strip(r,t)·dTheta(m)` collapses to the
single normal-form monomial `mhatRawTerm 1 row k r t m`. -/
theorem MhatRowFamily_term_eq_raw (row : MhatRow) (k r t m : ℤ) :
    row.lead.toMonom *
      ((mhatJThetaFamily row).toFun k *
        (mhatAppellFamilyOf mhatAppellPWO 1 row).toFun (r, t) *
          (mhatDThetaFamily 1 row).toFun m) = mhatRawTerm 1 row k r t m := by
  show AffineXY.toMonom row.lead *
      (monom (thetaQDeg 18 row.jArg.c0 k) (row.jArg.cX * k) (row.jArg.cY * k) (negOnePowIntQ k) *
        mhatAppellStripTerm 1 row r t *
        monom (thetaQDeg 90 (row.mZ 1).neg.c0 m) ((row.mZ 1).neg.cX * m) ((row.mZ 1).neg.cY * m)
          (negOnePowIntQ m)) = mhatRawTerm 1 row k r t m
  rw [thetaQDeg_18, thetaQDeg_90]
  unfold AffineXY.toMonom mhatAppellStripTerm mhatAppellStripExp mhatAppellStripCoeff
    mhatRawTerm mhatRawExp mhatRawCoeff mhatJThetaExp mhatDThetaExp mhatAppellNumeratorExp
    AffineXY.add
  rw [monom_mul, monom_mul, monom_mul]
  rw [negOnePowIntQ_add (k + r) m, negOnePowIntQ_add k r]
  congr 1 <;> ring

/-- The `MhatRowFamilyOf` term collapses directly to the normal-form monomial. -/
theorem MhatRowFamily_term_raw (row : MhatRow) (k r t m : ℤ) :
    (MhatRowFamilyOf mhatAppellPWO 1 row) (((k, (r, t)), m)) = mhatRawTerm 1 row k r t m := by
  rw [MhatRowFamily_term, MhatRowFamily_term_eq_raw]

/-- Per-row coefficient over the explicit normal-form monomial `mhatRawTerm`. -/
theorem coeff_Mhat_row_rawTerm (row : MhatRow) (e x y : ℤ) :
    (row.lead.toMonom *
      ((mhatJThetaFamily row).hsum *
        ((mhatAppellFamilyOf mhatAppellPWO 1 row).hsum *
          (mhatDThetaFamily 1 row).hsum))).coeff (expQXY e x y)
    = ∑ᶠ idx : (ℤ × (ℤ × ℤ)) × ℤ,
        (mhatRawTerm 1 row idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff (expQXY e x y) := by
  rw [coeff_Mhat_row_raw]
  apply finsum_congr
  intro idx
  obtain ⟨⟨k, r, t⟩, m⟩ := idx
  rw [MhatRowFamily_term_raw]

/-- The normal-form monomial coefficient as an explicit `(e,x,y)`-indicator. -/
theorem mhatRawTerm_coeff (row : MhatRow) (e x y k r t m : ℤ) :
    (mhatRawTerm 1 row k r t m).coeff (expQXY e x y) =
      if e = (mhatRawExp 1 row k r t m).c0 ∧ x = (mhatRawExp 1 row k r t m).cX ∧
          y = (mhatRawExp 1 row k r t m).cY then
        mhatRawCoeff 1 row k r t m else 0 := by
  simp only [mhatRawTerm, monom, HahnSeries.coeff_single, expQXY_eq_iff]

/-- The raw-term coefficient support is finite, inherited from the proved row summable family. -/
theorem mhatRawTerm_coeff_support_finite (row : MhatRow) (e x y : ℤ) :
    (Function.support (fun idx : (ℤ × (ℤ × ℤ)) × ℤ =>
      (mhatRawTerm 1 row idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
        (expQXY e x y))).Finite := by
  have hf : (Function.support (fun idx : (ℤ × (ℤ × ℤ)) × ℤ =>
      ((MhatRowFamilyOf mhatAppellPWO 1 row) idx).coeff (expQXY e x y))).Finite :=
    (MhatRowFamilyOf mhatAppellPWO 1 row).finite_co_support' (expQXY e x y)
  apply hf.subset
  intro idx hidx
  rcases idx with ⟨⟨k, r, t⟩, m⟩
  rw [Function.mem_support] at hidx ⊢
  rw [MhatRowFamily_term_raw]
  exact hidx

private theorem support_finsum_prod_left_finite {α β : Type*} {f : α × β → ℚ}
    (hf : (Function.support f).Finite) :
    (Function.support (fun a : α => ∑ᶠ b : β, f (a, b))).Finite := by
  classical
  refine Set.Finite.subset (hf.image (fun p : α × β => p.1)) ?_
  intro a ha
  simp only [Function.mem_support] at ha
  by_contra hmem
  have hzero : ∀ b : β, f (a, b) = 0 := by
    intro b
    by_contra hb
    apply hmem
    refine ⟨(a, b), ?_, rfl⟩
    simpa [Function.mem_support] using hb
  exact ha (finsum_eq_zero_of_forall_eq_zero hzero)

/-- Curry the concrete Mhat raw index `((k,(r,t)),m)` into four nested finsums. -/
theorem finsum_mhatRaw_curry
    {f : (ℤ × (ℤ × ℤ)) × ℤ → ℚ}
    (hf : (Function.support f).Finite) :
    (∑ᶠ idx : (ℤ × (ℤ × ℤ)) × ℤ, f idx) =
      ∑ᶠ k : ℤ, ∑ᶠ r : ℤ, ∑ᶠ t : ℤ, ∑ᶠ m : ℤ,
        f ((k, (r, t)), m) := by
  classical
  rw [finsum_curry _ hf]
  let g : ℤ × (ℤ × ℤ) → ℚ := fun x => ∑ᶠ m : ℤ, f (x, m)
  change (∑ᶠ x : ℤ × (ℤ × ℤ), g x) = _
  have hg : (Function.support g).Finite :=
    support_finsum_prod_left_finite (f := f) hf
  rw [finsum_curry _ hg]
  let h : ℤ → ℚ := fun k => ∑ᶠ rt : ℤ × ℤ, g (k, rt)
  change (∑ᶠ k : ℤ, h k) = _
  apply finsum_congr
  intro k
  change (∑ᶠ rt : ℤ × ℤ, g (k, rt)) =
    ∑ᶠ r : ℤ, ∑ᶠ t : ℤ, ∑ᶠ m : ℤ, f ((k, (r, t)), m)
  have hrt : (Function.support (fun rt : ℤ × ℤ => g (k, rt))).Finite :=
    (hg.preimage (by
      intro rt₁ _ rt₂ _ hrt
      exact Prod.ext_iff.mp hrt |>.2))
  rw [finsum_curry _ hrt]

end

end QseriesFormalization.Pending.Ch10M3Ghat
