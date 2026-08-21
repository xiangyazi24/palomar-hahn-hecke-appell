import QseriesFormalization.Pending.Chapter10_M3_PairBoundary

namespace QseriesFormalization.Pending.Ch10M3Ghat
open QseriesFormalization.Ch10TwoVar
open QseriesFormalization.Pending.Ch10HM
open QseriesFormalization.Pending.Ch10M3Mhat
open QseriesFormalization.Pending.Ch10M3HahnInv

noncomputable section

/-- KEY factorization: R0/R2 share the boundary, so `locInv(B)` factors out. -/
theorem GhatPairY_eq_locInv_mul_PpairY :
    GhatPairY = locInv (ghatBoundary 1 MhatRow.R0) * PpairY := by
  unfold GhatPairY GRowS ghatAppellM PpairY
  rw [← ghatBoundary_R0_eq_R2]
  ring

/-- Clearing the boundary: `B · GhatPairY = P`. -/
theorem ghatBoundary_mul_GhatPairY :
    ghatBoundary 1 MhatRow.R0 * GhatPairY = PpairY := by
  rw [GhatPairY_eq_locInv_mul_PpairY, ← mul_assoc,
      mul_locInv _ (ghatBoundary_ne_zero 1 MhatRow.R0), one_mul]

end

end QseriesFormalization.Pending.Ch10M3Ghat
