import QseriesFormalization.Pending.Chapter10_M3_Mhat
import QseriesFormalization.Pending.Chapter10_M3_Engine

/-!
# `Mhat` row hsum and coefficient APIs

This file contains the completed row-factorization infrastructure that was
originally housed in `Chapter10_M3_MhatFE.lean`.  The functional-equation route
for `Mhat` is false/bypassed, but these row APIs are still used by the faithful
cleared-identity route.
-/

namespace QseriesFormalization.Pending.Ch10M3MhatFE2

open QseriesFormalization.Ch10TwoVar
open QseriesFormalization.Pending.Ch10HM
open QseriesFormalization.Pending.Ch10M3Mhat
open QseriesFormalization.Pending.Ch10M3Engine

noncomputable section

/-! ## Row hsum = lead * jTheta.hsum * Appell.hsum * dTheta.hsum -/

/-- The hsum of a row family factors as lead * (jTheta * Appell * dTheta). -/
theorem MhatRowFamilyOf_hsum (h : MhatAppellPWOResidual) (ell : ℤ) (row : MhatRow) :
    (MhatRowFamilyOf h ell row).hsum =
      row.lead.toMonom *
        ((mhatJThetaFamily row).hsum *
          ((mhatAppellFamilyOf h ell row).hsum *
            (mhatDThetaFamily ell row).hsum)) := by
  unfold MhatRowFamilyOf
  rw [HahnSeries.SummableFamily.hsum_smul]
  rw [HahnSeries.SummableFamily.hsum_mul]
  rw [HahnSeries.SummableFamily.hsum_mul]
  rw [mul_assoc]

/-- coeffXY decomposition for the conditional Mhat. -/
theorem coeffXY_Mhat_row_sum (ell a b e : ℤ) :
    (coeffXY (Mhat ell) a b).coeff e =
      ∑ row : MhatRow,
        (row.lead.toMonom *
          ((mhatJThetaFamily row).hsum *
            ((mhatAppellFamilyOf mhatAppellPWO ell row).hsum *
              (mhatDThetaFamily ell row).hsum))).coeff (expQXY e a b) := by
  rw [coeffXY_Mhat]
  congr 1
  ext row
  rw [← MhatRowFamilyOf_hsum]

/-! ## Row sum APIs -/

/-- The row-level S object: lead * jTheta * Appell * dTheta. -/
def RowS (ell : ℤ) (row : MhatRow) : S :=
  (MhatRowFamilyOf mhatAppellPWO ell row).hsum

/-- Mhat as a sum of row S objects. -/
theorem Mhat_eq_row_sum (ell : ℤ) :
    Mhat ell = ∑ row : MhatRow, RowS ell row := by
  unfold Mhat MhatOf RowS
  rfl

/-- coeffQXY distributes over Fintype sums. -/
theorem coeffQXY_fintype_sum {ι : Type*} [Fintype ι] (F : ι → S) (e a b : ℤ) :
    coeffQXY (∑ i, F i) e a b = ∑ i, coeffQXY (F i) e a b := by
  unfold coeffQXY
  rw [HahnSeries.coeff_sum]

/-- sliceX distributes over Fintype sums at HahnSeries coefficient level. -/
theorem sliceX_fintype_sum_coeff {ι : Type*} [Fintype ι] (F : ι → S)
    (m s e : ℤ) :
    (sliceX (∑ i, F i) m s).coeff e = ∑ i, (sliceX (F i) m s).coeff e := by
  simp only [sliceX, coeffXY_coeff, coeffQXY_fintype_sum]

/-- sliceX distributes over the 4-row sum of Mhat (HahnSeries level). -/
theorem sliceX_Mhat_eq_row_sum_coeff (ell m s e : ℤ) :
    (sliceX (Mhat ell) m s).coeff e =
      ∑ row : MhatRow, (sliceX (RowS ell row) m s).coeff e := by
  rw [Mhat_eq_row_sum]
  exact sliceX_fintype_sum_coeff (fun row => RowS ell row) m s e

end

end QseriesFormalization.Pending.Ch10M3MhatFE2
