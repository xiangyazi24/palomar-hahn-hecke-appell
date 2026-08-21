import QseriesFormalization.Pending.Chapter10_M3_Mhat
import QseriesFormalization.Pending.Chapter10_M3_HahnInv

/-!
# Faithful two-variable HM g-side `Ghat`

The current `Mhat` carries a spurious factor: its row is
`lead·jTheta·N(a,z)·j(-z,90) = lead·jTheta·j(z,90)·j(-z,90)·M(a,z)`, so
`Mhat = j_product·Fhm` (verified). The faithful object uses the Appell-Lerch
quotient `M(a,z) = N(a,z)/j(z,90)`, realized via the localized inverse `locInv`
(no global field instance needed), and NO dTheta.
-/

namespace QseriesFormalization.Pending.Ch10M3Ghat

open QseriesFormalization.Ch10TwoVar
open QseriesFormalization.Pending.Ch10M3Mhat
open QseriesFormalization.Pending.Ch10M3HahnInv

noncomputable section

/-- Lifted Appell boundary theta `j(Q^mZ; Q^90)` (the denominator of `M`). -/
noncomputable def ghatBoundary (ell : ℤ) (row : MhatRow) : S :=
  (mhatThetaFamily 90 (row.mZ ell).c0 (row.mZ ell).cX (row.mZ ell).cY
    (by norm_num)).hsum

/-- Faithful lifted Appell-Lerch factor `M(a,z) = N(a,z) / j(z,90)`,
realized as `locInv(boundary) * N`. -/
noncomputable def ghatAppellM (h : MhatAppellPWOResidual) (ell : ℤ) (row : MhatRow) : S :=
  locInv (ghatBoundary ell row) * (mhatAppellFamilyOf h ell row).hsum

/-- Faithful HM row: `Q^lead · j(Q^jArg;Q^18) · M(mArg,mZ)`. -/
noncomputable def GRowS (h : MhatAppellPWOResidual) (ell : ℤ) (row : MhatRow) : S :=
  row.lead.toMonom *
    ((mhatJThetaFamily row).hsum * ghatAppellM h ell row)

/-- Faithful two-variable HM g-side (conditional on the PWO residual). -/
noncomputable def GhatOf (h : MhatAppellPWOResidual) (ell : ℤ) : S :=
  ∑ row : MhatRow, GRowS h ell row

/-- The unconditional faithful HM g-side. -/
noncomputable def Ghat (ell : ℤ) : S :=
  GhatOf mhatAppellPWO ell

end

end QseriesFormalization.Pending.Ch10M3Ghat
