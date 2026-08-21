import QseriesFormalization.Pending.Chapter10_M3_Ghat

/-!
# Faithful `Ghat` — foundational algebra for the x-FE

`ghatBoundary` is nonzero (each row's `mZ` has x-slope `±2`), so the localized
inverse is a genuine inverse, giving the workhorse `ghatBoundary · ghatAppellM = N`.
These feed the row-pair x-FE defect computation.
-/

namespace QseriesFormalization.Pending.Ch10M3Ghat

open QseriesFormalization.Ch10TwoVar
open QseriesFormalization.Pending.Ch10HM
open QseriesFormalization.Pending.Ch10M3Mhat
open QseriesFormalization.Pending.Ch10M3HahnInv
open HahnSeries

noncomputable section

/-- A lifted theta family with nonzero x-slope is a nonzero Hahn series:
its coefficient at `(thetaQDeg A e 0, 0, 0)` is the `n=0` term `= 1`, and no other
`n` reaches x-degree `0` since `i ≠ 0`. -/
theorem mhatThetaFamily_hsum_ne_zero (A e i j : ℤ) (hA : 0 < A) (hi : i ≠ 0) :
    (mhatThetaFamily A e i j hA).hsum ≠ 0 := by
  intro hzero
  have hkey : (mhatThetaFamily A e i j hA).hsum.coeff
      (expQXY (thetaQDeg A e 0) 0 0) = 1 := by
    rw [SummableFamily.coeff_hsum]
    rw [finsum_eq_single _ (0 : ℤ)]
    · show (monom (thetaQDeg A e 0) (i * 0) (j * 0) (negOnePowIntQ 0)).coeff
        (expQXY (thetaQDeg A e 0) 0 0) = 1
      rw [mul_zero, mul_zero, monom, HahnSeries.coeff_single_same]
      simp [negOnePowIntQ]
    · intro n hn
      show (monom (thetaQDeg A e n) (i * n) (j * n) (negOnePowIntQ n)).coeff
        (expQXY (thetaQDeg A e 0) 0 0) = 0
      rw [monom]
      apply HahnSeries.coeff_single_of_ne
      intro hcon
      have h2 := congrArg (fun g => (ofLex g).2) hcon
      simp [expQXY, ofLex_toLex] at h2
      rcases h2.1 with h | h
      · exact hi h
      · exact hn h
  rw [hzero, HahnSeries.coeff_zero] at hkey
  exact one_ne_zero hkey.symm

/-- Each row's boundary theta `j(Q^mZ;Q^90)` is nonzero (x-slope `±2`). -/
theorem ghatBoundary_ne_zero (ell : ℤ) (row : MhatRow) :
    ghatBoundary ell row ≠ 0 := by
  unfold ghatBoundary
  apply mhatThetaFamily_hsum_ne_zero
  cases row <;> norm_num [MhatRow.mZ]

/-- Workhorse: `boundary · M = N` (clears the localized inverse). -/
theorem ghatBoundary_mul_ghatAppellM (h : MhatAppellPWOResidual) (ell : ℤ)
    (row : MhatRow) :
    ghatBoundary ell row * ghatAppellM h ell row =
      (mhatAppellFamilyOf h ell row).hsum := by
  rw [ghatAppellM, ← mul_assoc, mul_locInv _ (ghatBoundary_ne_zero ell row), one_mul]

/-- Right-clearing form of `ghatBoundary_mul_ghatAppellM`.  This is the
orientation needed when a row is multiplied by its boundary on the right. -/
theorem ghatAppellM_mul_ghatBoundary (h : MhatAppellPWOResidual) (ell : ℤ)
    (row : MhatRow) :
    ghatAppellM h ell row * ghatBoundary ell row =
      (mhatAppellFamilyOf h ell row).hsum := by
  unfold ghatAppellM
  calc
    (locInv (ghatBoundary ell row) * (mhatAppellFamilyOf h ell row).hsum) *
        ghatBoundary ell row
        = (locInv (ghatBoundary ell row) * ghatBoundary ell row) *
            (mhatAppellFamilyOf h ell row).hsum := by
          ring
    _ = (mhatAppellFamilyOf h ell row).hsum := by
          rw [locInv_mul _ (ghatBoundary_ne_zero ell row), one_mul]

/-- The inverse-free numerator of one faithful `Ghat` row. -/
noncomputable def GRowSCleared (h : MhatAppellPWOResidual) (ell : ℤ)
    (row : MhatRow) : S :=
  row.lead.toMonom *
    ((mhatJThetaFamily row).hsum * (mhatAppellFamilyOf h ell row).hsum)

/-- Row-level boundary clearing.  The proof uses only
`locInv u * u = 1`, hidden in `ghatAppellM_mul_ghatBoundary`; no termwise
specialization of `locInv` is involved. -/
theorem GRowS_mul_ghatBoundary (h : MhatAppellPWOResidual) (ell : ℤ)
    (row : MhatRow) :
    GRowS h ell row * ghatBoundary ell row =
      GRowSCleared h ell row := by
  unfold GRowS GRowSCleared
  calc
    row.lead.toMonom * ((mhatJThetaFamily row).hsum * ghatAppellM h ell row) *
        ghatBoundary ell row
        = row.lead.toMonom *
            ((mhatJThetaFamily row).hsum *
              (ghatAppellM h ell row * ghatBoundary ell row)) := by
          ring
    _ = row.lead.toMonom *
        ((mhatJThetaFamily row).hsum * (mhatAppellFamilyOf h ell row).hsum) := by
          rw [ghatAppellM_mul_ghatBoundary h ell row]

/-- R0 and R2 share the boundary theta (same `mZ`). -/
theorem ghatBoundary_R0_eq_R2 (ell : ℤ) :
    ghatBoundary ell MhatRow.R0 = ghatBoundary ell MhatRow.R2 := rfl

/-- R1 and R3 share the boundary theta (same `mZ`). -/
theorem ghatBoundary_R1_eq_R3 (ell : ℤ) :
    ghatBoundary ell MhatRow.R1 = ghatBoundary ell MhatRow.R3 := rfl

end

end QseriesFormalization.Pending.Ch10M3Ghat
