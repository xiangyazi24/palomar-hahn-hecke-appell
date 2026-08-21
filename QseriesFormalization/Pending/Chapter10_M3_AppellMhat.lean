import QseriesFormalization.Pending.Chapter10_M3_PairBoundary
import QseriesFormalization.Pending.Chapter10_M3_MhatRows

/-!
# Appell cleared-boundary factorization: `PpairY·B_X + PpairX·B_Y = Mhat 1`

The boundary thetas supply each row's missing dTheta factor (row `mZ` pairing:
`mZ R1 = (mZ R0).neg`, `mZ R3 = (mZ R2).neg`, `mZ R2 = mZ R0`, `mZ R3 = mZ R1`), so
`B_X = (dTheta R0).hsum = (dTheta R2).hsum` and `B_Y = (dTheta R1).hsum = (dTheta R3).hsum`.
Hence each cleared pair times its boundary reproduces the corresponding `Mhat` rows.
-/

namespace QseriesFormalization.Pending.Ch10M3Ghat

open QseriesFormalization.Ch10TwoVar
open QseriesFormalization.Pending.Ch10HM
open QseriesFormalization.Pending.Ch10M3Mhat
open QseriesFormalization.Pending.Ch10M3MhatFE2

noncomputable section

/-- `B_X` is the dTheta of row R0 (`mZ R1 = (mZ R0).neg`). -/
theorem dTheta_R0_eq_BX : (mhatDThetaFamily 1 MhatRow.R0).hsum = BX := rfl
/-- `B_X` is also the dTheta of row R2 (`mZ R2 = mZ R0`). -/
theorem dTheta_R2_eq_BX : (mhatDThetaFamily 1 MhatRow.R2).hsum = BX := rfl
/-- `B_Y` is the dTheta of row R1. -/
theorem dTheta_R1_eq_BY : (mhatDThetaFamily 1 MhatRow.R1).hsum = BY := rfl
/-- `B_Y` is also the dTheta of row R3. -/
theorem dTheta_R3_eq_BY : (mhatDThetaFamily 1 MhatRow.R3).hsum = BY := rfl

/-- The Appell cleared-boundary side reproduces `Mhat 1` (the boundaries supply the dThetas).
The four row factorizations are taken as UN-annotated `have`s so each picks up the exact
`MhatRowFamilyOf_hsum` output type (avoids the heterogeneous-index motive failure). -/
theorem Ppair_boundary_eq_Mhat_one :
    PpairY * BX + PpairX * BY = Mhat 1 := by
  have hR0 := MhatRowFamilyOf_hsum (h := mhatAppellPWO) (ell := (1 : ℤ)) (row := MhatRow.R0)
  have hR1 := MhatRowFamilyOf_hsum (h := mhatAppellPWO) (ell := (1 : ℤ)) (row := MhatRow.R1)
  have hR2 := MhatRowFamilyOf_hsum (h := mhatAppellPWO) (ell := (1 : ℤ)) (row := MhatRow.R2)
  have hR3 := MhatRowFamilyOf_hsum (h := mhatAppellPWO) (ell := (1 : ℤ)) (row := MhatRow.R3)
  conv_rhs =>
    rw [Mhat_eq_row_sum, sum_MhatRow_four (fun row : MhatRow => RowS (1 : ℤ) row)]
    unfold RowS
    rw [hR0, hR1, hR2, hR3, dTheta_R0_eq_BX, dTheta_R1_eq_BY, dTheta_R2_eq_BX, dTheta_R3_eq_BY]
  unfold PpairY PpairX
  ring

end

end QseriesFormalization.Pending.Ch10M3Ghat
