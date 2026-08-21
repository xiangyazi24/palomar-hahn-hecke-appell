import QseriesFormalization.Pending.Chapter10_TwoVar
import Mathlib

/-!
# Localized inverse in the two-variable Hahn ring `S`

`S = HahnSeries ExpQXY ℚ` has no global `Field` instance (a Lex-of-Lex typeclass
diamond around `IsOrderedAddMonoid ExpQXY`). But Mathlib's HahnSeries inverse is an
explicit formula needing only `IsOrderedCancelAddMonoid` (which `S` has) plus the
ring structure. We extract it as a localized inverse `locInv`, giving genuine
two-sided inverses for any nonzero element — enough to build the faithful Appell-Lerch
quotient `M = N / j(z,90)` without the diamonded field instance.
-/

namespace QseriesFormalization.Pending.Ch10M3HahnInv

open QseriesFormalization.Ch10TwoVar
open HahnSeries

noncomputable section

/-- Localized inverse via the explicit Hahn formula (no global `Field` needed). -/
noncomputable def locInv (u : S) : S :=
  single (-u.order) (u.leadingCoeff)⁻¹ *
    (SummableFamily.powers
      (1 - single (-u.order) (u.leadingCoeff)⁻¹ * u)).hsum

/-- For any nonzero `u`, `locInv u` is a genuine right inverse. -/
theorem mul_locInv (u : S) (hu : u ≠ 0) : u * locInv u = 1 := by
  have hlc : u.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hu
  have h := SummableFamily.one_sub_self_mul_hsum_powers
    (unit_aux u (inv_mul_cancel₀ hlc) _ (neg_add_cancel u.order))
  rw [sub_sub_cancel] at h
  rw [locInv, ← mul_assoc, mul_comm u _]
  exact h

/-- `locInv u` is also a left inverse (`S` is commutative). -/
theorem locInv_mul (u : S) (hu : u ≠ 0) : locInv u * u = 1 := by
  rw [mul_comm]; exact mul_locInv u hu

/-- `locInv u ≠ 0` for nonzero `u`. -/
theorem locInv_ne_zero (u : S) (hu : u ≠ 0) : locInv u ≠ 0 := by
  intro h
  have := mul_locInv u hu
  rw [h, mul_zero] at this
  exact one_ne_zero this.symm

end

end QseriesFormalization.Pending.Ch10M3HahnInv
