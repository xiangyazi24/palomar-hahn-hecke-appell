import QseriesFormalization.Pending.Chapter10_M3_GhatPairBase
import QseriesFormalization.Pending.Chapter10_M3_HMf

/-!
# Boundary-cleared row-pair numerators

This file isolates the definitions shared by the cleared-identity proof route.
It intentionally does not import the old row-pair FE proof file.
-/

namespace QseriesFormalization.Pending.Ch10M3Ghat

open QseriesFormalization.Ch10TwoVar
open QseriesFormalization.Pending.Ch10HM
open QseriesFormalization.Pending.Ch10M3Mhat
open QseriesFormalization.Pending.Ch10M3HMf

noncomputable section

/-- The `B_Y = j(Q^18 x^-2 y^2; Q^90)` boundary. -/
abbrev BY : S := ghatBoundary 1 MhatRow.R0

/-- The `B_X = j(Q^-18 x^2 y^-2; Q^90)` boundary. -/
abbrev BX : S := ghatBoundary 1 MhatRow.R1

/-- The boundary-cleared numerator combination for the R0/R2 pair. -/
noncomputable def PpairY : S :=
  MhatRow.R0.lead.toMonom * ((mhatJThetaFamily MhatRow.R0).hsum *
      (mhatAppellFamilyOf mhatAppellPWO 1 MhatRow.R0).hsum)
  + MhatRow.R2.lead.toMonom * ((mhatJThetaFamily MhatRow.R2).hsum *
      (mhatAppellFamilyOf mhatAppellPWO 1 MhatRow.R2).hsum)

/-- The boundary-cleared numerator combination for the R1/R3 pair. -/
noncomputable def PpairX : S :=
  MhatRow.R1.lead.toMonom * ((mhatJThetaFamily MhatRow.R1).hsum *
      (mhatAppellFamilyOf mhatAppellPWO 1 MhatRow.R1).hsum)
  + MhatRow.R3.lead.toMonom * ((mhatJThetaFamily MhatRow.R3).hsum *
      (mhatAppellFamilyOf mhatAppellPWO 1 MhatRow.R3).hsum)

/-- The cleared difference for the boundary-cleared identity. -/
def clearedD : S := Fhm * BY * BX - (PpairY * BX + PpairX * BY)

/-- The fixed `x^x y^y` `Q`-slice of the cleared difference. -/
def clearedSliceXY (x y : ℤ) : K := coeffXY clearedD x y

theorem clearedSliceXY_coeff (x y e : ℤ) :
    (clearedSliceXY x y).coeff e = coeffQXY clearedD e x y := rfl

end

end QseriesFormalization.Pending.Ch10M3Ghat
