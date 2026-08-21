import QseriesFormalization.Pending.Chapter10_M3_GhatFE
import QseriesFormalization.Pending.Chapter10_M3_Engine

/-!
# `Ghat` row-pair base definitions

This file contains only the row-pair definitions and elementary slice algebra
used by both the old FE route and the current cleared-identity route.  The
row-pair functional-equation proof lives in `Chapter10_M3_GhatPair.lean`.
-/

namespace QseriesFormalization.Pending.Ch10M3Ghat

open QseriesFormalization.Ch10TwoVar
open QseriesFormalization.Pending.Ch10HM
open QseriesFormalization.Pending.Ch10M3Mhat
open QseriesFormalization.Pending.Ch10M3Engine

noncomputable section

/-- Sum over the four `MhatRow` constructors. -/
theorem sum_MhatRow_four (f : MhatRow → S) :
    ∑ row : MhatRow, f row =
      f MhatRow.R0 + f MhatRow.R1 + f MhatRow.R2 + f MhatRow.R3 := by
  have huniv : (Finset.univ : Finset MhatRow) =
      {MhatRow.R0, MhatRow.R1, MhatRow.R2, MhatRow.R3} := by decide
  rw [show (∑ row : MhatRow, f row) = (Finset.univ : Finset MhatRow).sum f from rfl, huniv]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- Additive slice extraction (mirror of `sliceX_sub`). -/
theorem sliceX_add (F G : S) (n : ℤ) :
    sliceX (F + G) n = fun j => coeffXY F n j + coeffXY G n j := by
  funext j
  apply HahnSeries.ext
  funext a
  simp [sliceX, coeffXY_coeff, coeffQXY]

/-- Pointwise additive slice. -/
theorem sliceX_add_apply (F G : S) (n j : ℤ) :
    sliceX (F + G) n j = sliceX F n j + sliceX G n j := by
  apply HahnSeries.ext; funext a
  simp [sliceX, coeffXY_coeff, coeffQXY]

/-- Pointwise subtractive slice. -/
theorem sliceX_sub_apply (F G : S) (n j : ℤ) :
    sliceX (F - G) n j = sliceX F n j - sliceX G n j := by
  apply HahnSeries.ext; funext a
  simp [sliceX, coeffXY_coeff, coeffQXY]

/-- R0/R2 row-pair. -/
noncomputable def GhatPairY : S :=
  GRowS mhatAppellPWO 1 MhatRow.R0 + GRowS mhatAppellPWO 1 MhatRow.R2

/-- R1/R3 row-pair. -/
noncomputable def GhatPairX : S :=
  GRowS mhatAppellPWO 1 MhatRow.R1 + GRowS mhatAppellPWO 1 MhatRow.R3

/-- `Ghat 1` decomposes into the two row-pairs. -/
theorem Ghat_one_eq_pairs : Ghat 1 = GhatPairY + GhatPairX := by
  rw [Ghat, GhatOf, sum_MhatRow_four, GhatPairY, GhatPairX]
  ring

end

end QseriesFormalization.Pending.Ch10M3Ghat
