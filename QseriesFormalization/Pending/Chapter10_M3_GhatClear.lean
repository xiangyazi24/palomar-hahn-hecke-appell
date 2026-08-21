import QseriesFormalization.Pending.Chapter10_M3_GhatPairCoeff

/-!
# Cleared-identity route to `Fhm = Ghat`

Numerically VERIFIED (inverse-free): `Fhm·B_Y·B_X = PpairY·B_X + PpairX·B_Y`.
From this single cleared identity, `Fhm = Ghat` follows by pure `mul_locInv`
algebra — no `locInv` transport, no `σₓ`, no per-pair functional equation.
The cleared identity is the genuine HM content, isolated inverse-free.
-/

namespace QseriesFormalization.Pending.Ch10M3Ghat

open QseriesFormalization.Ch10TwoVar
open QseriesFormalization.Pending.Ch10HM
open QseriesFormalization.Pending.Ch10M3Mhat
open QseriesFormalization.Pending.Ch10M3HMf
open QseriesFormalization.Pending.Ch10M3HahnInv

noncomputable section

/-- R1/R3 factorization: `locInv(B_X)` is the common factor. -/
theorem GhatPairX_eq_locInv_mul_PpairX :
    GhatPairX = locInv (ghatBoundary 1 MhatRow.R1) * PpairX := by
  unfold GhatPairX GRowS ghatAppellM PpairX
  rw [← ghatBoundary_R1_eq_R3]
  ring

/-- THE CLEARED-ROUTE BRIDGE: the inverse-free cleared identity implies `Fhm = Ghat`. -/
theorem Fhm_eq_Ghat_of_cleared
    (hcleared :
      Fhm * ghatBoundary 1 MhatRow.R0 * ghatBoundary 1 MhatRow.R1 =
        PpairY * ghatBoundary 1 MhatRow.R1 + PpairX * ghatBoundary 1 MhatRow.R0) :
    Fhm = Ghat 1 := by
  have e1 : ghatBoundary 1 MhatRow.R0 * locInv (ghatBoundary 1 MhatRow.R0) = 1 :=
    mul_locInv _ (ghatBoundary_ne_zero 1 MhatRow.R0)
  have e2 : ghatBoundary 1 MhatRow.R1 * locInv (ghatBoundary 1 MhatRow.R1) = 1 :=
    mul_locInv _ (ghatBoundary_ne_zero 1 MhatRow.R1)
  rw [Ghat_one_eq_pairs, GhatPairY_eq_locInv_mul_PpairY, GhatPairX_eq_locInv_mul_PpairX]
  calc Fhm
      = Fhm * (ghatBoundary 1 MhatRow.R0 * locInv (ghatBoundary 1 MhatRow.R0)) *
          (ghatBoundary 1 MhatRow.R1 * locInv (ghatBoundary 1 MhatRow.R1)) := by
        rw [e1, e2]; ring
    _ = (Fhm * ghatBoundary 1 MhatRow.R0 * ghatBoundary 1 MhatRow.R1) *
          (locInv (ghatBoundary 1 MhatRow.R0) * locInv (ghatBoundary 1 MhatRow.R1)) := by ring
    _ = (PpairY * ghatBoundary 1 MhatRow.R1 + PpairX * ghatBoundary 1 MhatRow.R0) *
          (locInv (ghatBoundary 1 MhatRow.R0) * locInv (ghatBoundary 1 MhatRow.R1)) := by
        rw [hcleared]
    _ = locInv (ghatBoundary 1 MhatRow.R0) * PpairY +
          locInv (ghatBoundary 1 MhatRow.R1) * PpairX := by
        have hexp :
            (PpairY * ghatBoundary 1 MhatRow.R1 + PpairX * ghatBoundary 1 MhatRow.R0) *
              (locInv (ghatBoundary 1 MhatRow.R0) * locInv (ghatBoundary 1 MhatRow.R1)) =
            PpairY * (ghatBoundary 1 MhatRow.R1 * locInv (ghatBoundary 1 MhatRow.R1)) *
                locInv (ghatBoundary 1 MhatRow.R0) +
            PpairX * (ghatBoundary 1 MhatRow.R0 * locInv (ghatBoundary 1 MhatRow.R0)) *
                locInv (ghatBoundary 1 MhatRow.R1) := by ring
        rw [hexp, e1, e2]; ring

end

end QseriesFormalization.Pending.Ch10M3Ghat
