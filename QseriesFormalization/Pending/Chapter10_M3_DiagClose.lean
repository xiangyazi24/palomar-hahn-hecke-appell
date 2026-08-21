import QseriesFormalization.Pending.Chapter10_M3_PairBoundary
import QseriesFormalization.Pending.Chapter10_M3_GhatClear
import QseriesFormalization.Pending.Chapter10_M3_HeckeCoeffNF
import QseriesFormalization.Pending.Chapter10_M3_AppellRawCoeff
import QseriesFormalization.Pending.Chapter10_M3_OmegaKernel
import QseriesFormalization.Pending.Chapter10_M3_J1Cube

/-!
# Diagonal closure: `clearedSliceXY t t = 0`

Both `Fhm * BY * BX` and `Mhat 1` reduce to the same diagonal `J₁³` normal form.
The mechanism:
- Hecke side: `uvOmega` normal form → diagonal omega kernel → `omega_sum(2i) = 2i+1`
- Appell side: 2-row diagonal collision → Jacobi derivative → `J₁³`
Both produce `(-1)^i(2i+1)Q^{diagQ(t,i)}`, hence their difference vanishes.

**Parity split**: even `t` → R0+R1 survive; odd `t` → R2+R3 survive.
-/

open scoped Classical

namespace QseriesFormalization.Pending.Ch10M3DiagClose

open QseriesFormalization.Ch10TwoVar
open QseriesFormalization.Pending.Ch10HM
open QseriesFormalization.Pending.Ch10M3Mhat
open QseriesFormalization.Pending.Ch10M3HMf
open QseriesFormalization.Pending.Ch10M3Ghat
open QseriesFormalization.Pending.Ch10M3OmegaKernel
open QseriesFormalization.Pending.Ch10M3J1Cube
open QseriesFormalization.Pending.Ch10M3HahnInv
open HahnSeries

noncomputable section

/-! ## Row-level diagonal xy constraints -/

/-- R0 diagonal constraint: `2(n-r) = t` and `k = l + 2t`. -/
theorem R0_diag_xy (t k r l n : ℤ)
    (hx : 0 + 0 * k + (-2) * r + 0 * l + 2 * n = t)
    (hy : 0 + 1 * k + 2 * r + (-1) * l + (-2) * n = t) :
    2 * (n - r) = t ∧ k = l + 2 * t := by
  constructor <;> omega

/-- R1 diagonal constraint. -/
theorem R1_diag_xy (t k r l n : ℤ)
    (hx : 0 + 1 * k + 2 * r + (-1) * l + (-2) * n = t)
    (hy : 0 + 0 * k + (-2) * r + 0 * l + 2 * n = t) :
    2 * (n - r) = t ∧ k = l + 2 * t := by
  constructor <;> omega

/-- R2 diagonal constraint: `2(n-r) = t - 1`. -/
theorem R2_diag_xy (t k r l n : ℤ)
    (hx : 1 + 0 * k + (-2) * r + 0 * l + 2 * n = t)
    (hy : (-1) + 1 * k + 2 * r + (-1) * l + (-2) * n = t) :
    2 * (n - r) = t - 1 ∧ k = l + 2 * t := by
  constructor <;> omega

/-- R3 diagonal constraint: `2(n-r) = t - 1`. -/
theorem R3_diag_xy (t k r l n : ℤ)
    (hx : (-1) + 1 * k + 2 * r + (-1) * l + (-2) * n = t)
    (hy : 1 + 0 * k + (-2) * r + 0 * l + 2 * n = t) :
    2 * (n - r) = t - 1 ∧ k = l + 2 * t := by
  constructor <;> omega

/-! ## Parity: which rows survive on the diagonal -/

/-- R0 needs even `t` (from `2(n-r) = t`). -/
theorem R0_diag_even {t r n : ℤ} (h : 2 * (n - r) = t) : ∃ h : ℤ, t = 2 * h :=
  ⟨n - r, by omega⟩

/-- R2 needs odd `t` (from `2(n-r) = t - 1`). -/
theorem R2_diag_odd {t r n : ℤ} (h : 2 * (n - r) = t - 1) : ∃ h : ℤ, t = 2 * h + 1 :=
  ⟨n - r, by omega⟩

/-! ## Off-diagonal: Hecke exponent-gap lemma

The key telescope coordinate is `c = 2*u + v`.
Shifting `u → u+1` at fixed `v` changes the Hecke q-degree by `90*c`.
This is the one-step boundary for the omega-line telescope. -/

/-- The Hecke q-degree polynomial `Phi(x,y,u,v)`. -/
def heckePhi (x y u v : ℤ) : ℤ :=
  FhmExp (x - 2 * v) (y + 2 * v) + BYExp u + BXExp (u + v)

/-- One u-step shifts Phi by `90*(2u+v)`. This is the fundamental exponent gap. -/
theorem heckePhi_u_succ (x y u v : ℤ) :
    heckePhi x y (u + 1) v = heckePhi x y u v + 90 * (2 * u + v) := by
  unfold heckePhi FhmExp BYExp BXExp
  ring

/-- The telescope coordinate `c = 2u+v`. -/
abbrev teleCoord (u v : ℤ) : ℤ := 2 * u + v

/-- Equivalent statement: `Phi(u+1,v) - Phi(u,v) = 90 * c`. -/
theorem heckePhi_gap_eq_tele (x y u v : ℤ) :
    heckePhi x y (u + 1) v - heckePhi x y u v = 90 * teleCoord u v := by
  rw [heckePhi_u_succ]; ring

/-- The full q-degree in normal form: `Phi = FhmExp(x,y) + 90u²+90uv+9v²-90u+(18(x-y)-63)v`. -/
theorem heckePhi_expand (x y u v : ℤ) :
    heckePhi x y u v =
      FhmExp x y + 90 * u * u + 90 * u * v + 9 * v * v - 90 * u + (18 * (x - y) - 63) * v := by
  unfold heckePhi FhmExp BYExp BXExp
  ring

/-! ## Even diagonal: R0+R1 q-degree difference -/

/-- R0 even-diagonal q-degree (from chan2 Q1906). -/
def qR0EvenDiag (h r l : ℤ) : ℤ :=
  189 * h * h + 72 * h * l + 90 * h * r - 99 * h +
  9 * l * l + 90 * l * r - 27 * l + 90 * r * r - 90 * r

/-- R1 even-diagonal q-degree. -/
def qR1EvenDiag (h r l : ℤ) : ℤ :=
  189 * h * h + 72 * h * l + 90 * h * r - 63 * h +
  9 * l * l + 90 * l * r - 63 * l + 90 * r * r - 90 * r

/-- The R0-R1 q-degree gap on the even diagonal: `36*(h-l)`. -/
theorem qR1_sub_qR0_even (h r l : ℤ) :
    qR1EvenDiag h r l - qR0EvenDiag h r l = 36 * (h - l) := by
  unfold qR0EvenDiag qR1EvenDiag; ring

/-! ## FhmExp on the diagonal -/

/-- `FhmExp(t,t) = 45*t^2 - 18*t`. -/
theorem FhmExp_diag (t : ℤ) : FhmExp t t = 45 * t * t - 18 * t := by
  unfold FhmExp; ring

/-- Hecke Phi on the diagonal: `Phi(t,t,u,v) = 45t²-18t + 90u²+90uv+9v²-90u-63v`. -/
theorem heckePhi_diag (t u v : ℤ) :
    heckePhi t t u v = 45 * t * t - 18 * t +
      90 * u * u + 90 * u * v + 9 * v * v - 90 * u - 63 * v := by
  unfold heckePhi FhmExp BYExp BXExp; ring

/-- R0 even-diagonal q at `l=0` (after branch telescope). -/
theorem qR0EvenDiag_l_zero (h r : ℤ) :
    qR0EvenDiag h r 0 = 189 * h * h + 90 * h * r - 99 * h + 90 * r * r - 90 * r := by
  unfold qR0EvenDiag; ring

/-- R0 even-diagonal q at `l=0` equals `90*r*(r-1) + 90*h*r + 189*h^2 - 99*h`. -/
theorem qR0EvenDiag_l_zero_alt (h r : ℤ) :
    qR0EvenDiag h r 0 = 90 * r * (r - 1) + 90 * h * r + 189 * h * h - 99 * h := by
  unfold qR0EvenDiag; ring

/-! ## The common diagonal normal form: diagJ1Cube

`diagQ(t, i) = FhmExp(t,t) + 90*i*(i+1) = 45*t² - 18*t + 90*i*(i+1)`.
The bilateral version: `diagQN(t, n) = FhmExp(t,t) + 90*n*(n-1)`.
Pairing n=-i and n=i+1 (both give n*(n-1) = i*(i+1)) yields the J₁³ multiplicity. -/

/-- The diagonal q-degree polynomial: `FhmExp(t,t) + 90*i*(i+1)`. -/
def diagQ (t i : ℤ) : ℤ := 45 * t * t - 18 * t + 90 * i * (i + 1)

/-- The bilateral version: `FhmExp(t,t) + 90*n*(n-1)`. -/
def diagQN (t n : ℤ) : ℤ := 45 * t * t - 18 * t + 90 * n * (n - 1)

/-- diagQ and diagQN agree under the pairing `n = -i`. -/
theorem diagQN_neg (t i : ℤ) : diagQN t (-i) = diagQ t i := by
  unfold diagQN diagQ; ring

/-- diagQ and diagQN agree under the pairing `n = i+1`. -/
theorem diagQN_succ (t i : ℤ) : diagQN t (i + 1) = diagQ t i := by
  unfold diagQN diagQ; ring

/-- diagQ at `i=0` is `FhmExp(t,t)`. -/
theorem diagQ_zero (t : ℤ) : diagQ t 0 = FhmExp t t := by
  unfold diagQ FhmExp; ring

/-- diagQN equals `heckePhi(t,t,n,0)` (the Hecke Phi at v=0 and u=n). -/
theorem diagQN_eq_heckePhi (t n : ℤ) : diagQN t n = heckePhi t t n 0 := by
  unfold diagQN heckePhi FhmExp BYExp BXExp; ring

/-! ## Per-row rawExp component formulas

For each row, the x and y components of mhatRawExp have specific affine shapes.
Key: the denominator branch cX (or cY) is 0 for the "free" coordinate,
so lexPositive doesn't affect it. -/

/-- The denominator exponent for R0 at `ell=1` has `cX = 0`. -/
theorem dExp_R0_cX (r : ℤ) : (mhatDenomExp 1 MhatRow.R0 r).cX = 0 := by
  unfold mhatDenomExp MhatRow.mArg MhatRow.mZ; ring

/-- The denominator exponent for R1 at `ell=1` has `cY = 0`. -/
theorem dExp_R1_cY (r : ℤ) : (mhatDenomExp 1 MhatRow.R1 r).cY = 0 := by
  unfold mhatDenomExp MhatRow.mArg MhatRow.mZ; ring

/-- The denominator exponent for R2 at `ell=1` has `cX = 0`. -/
theorem dExp_R2_cX (r : ℤ) : (mhatDenomExp 1 MhatRow.R2 r).cX = 0 := by
  unfold mhatDenomExp MhatRow.mArg MhatRow.mZ; ring

/-- The denominator exponent for R3 at `ell=1` has `cY = 0`. -/
theorem dExp_R3_cY (r : ℤ) : (mhatDenomExp 1 MhatRow.R3 r).cY = 0 := by
  unfold mhatDenomExp MhatRow.mArg MhatRow.mZ; ring

/-! ## Per-row rawExp x/y component formulas (the parity-determining constraints) -/

/-- R0 rawExp x-component: `x = -2r + 2m` (independent of k, t). -/
theorem rawExp_R0_cX (k r t m : ℤ) :
    (mhatRawExp 1 MhatRow.R0 k r t m).cX = -2 * r + 2 * m := by
  unfold mhatRawExp mhatJThetaExp mhatAppellNumeratorExp mhatDenomBranchExp
    mhatDenomExp mhatDThetaExp AffineXY.add AffineXY.smul AffineXY.neg
    MhatRow.lead MhatRow.jArg MhatRow.mArg MhatRow.mZ
  simp only [AffineXY.lexPositive]; split <;> ring

/-- R1 rawExp y-component: `y = -2r + 2m` (independent of k, t). -/
theorem rawExp_R1_cY (k r t m : ℤ) :
    (mhatRawExp 1 MhatRow.R1 k r t m).cY = -2 * r + 2 * m := by
  unfold mhatRawExp mhatJThetaExp mhatAppellNumeratorExp mhatDenomBranchExp
    mhatDenomExp mhatDThetaExp AffineXY.add AffineXY.smul AffineXY.neg
    MhatRow.lead MhatRow.jArg MhatRow.mArg MhatRow.mZ
  simp only [AffineXY.lexPositive]; split <;> ring

/-- R2 rawExp x-component: `x = 1 - 2r + 2m` (independent of k, t). -/
theorem rawExp_R2_cX (k r t m : ℤ) :
    (mhatRawExp 1 MhatRow.R2 k r t m).cX = 1 - 2 * r + 2 * m := by
  unfold mhatRawExp mhatJThetaExp mhatAppellNumeratorExp mhatDenomBranchExp
    mhatDenomExp mhatDThetaExp AffineXY.add AffineXY.smul AffineXY.neg
    MhatRow.lead MhatRow.jArg MhatRow.mArg MhatRow.mZ
  simp only [AffineXY.lexPositive]; split <;> ring

/-- R3 rawExp y-component: `y = 1 - 2r + 2m` (independent of k, t). -/
theorem rawExp_R3_cY (k r t m : ℤ) :
    (mhatRawExp 1 MhatRow.R3 k r t m).cY = 1 - 2 * r + 2 * m := by
  unfold mhatRawExp mhatJThetaExp mhatAppellNumeratorExp mhatDenomBranchExp
    mhatDenomExp mhatDThetaExp AffineXY.add AffineXY.smul AffineXY.neg
    MhatRow.lead MhatRow.jArg MhatRow.mArg MhatRow.mZ
  simp only [AffineXY.lexPositive]; split <;> ring

/-- R0 rawExp y-component: `y = k + 2r - 2m + (if lexPos then -t else t)`. -/
theorem rawExp_R0_cY (k r t m : ℤ) :
    (mhatRawExp 1 MhatRow.R0 k r t m).cY =
      k + 2 * r - 2 * m +
        (if (mhatDenomExp 1 MhatRow.R0 r).lexPositive then -t else t) := by
  unfold mhatRawExp mhatJThetaExp mhatAppellNumeratorExp mhatDenomBranchExp
    mhatDenomExp mhatDThetaExp AffineXY.add AffineXY.smul AffineXY.neg
    MhatRow.lead MhatRow.jArg MhatRow.mArg MhatRow.mZ
  simp only [AffineXY.lexPositive]; split <;> ring

/-- R1 rawExp x-component: `x = k + 2r - 2m + (if lexPos then -t else t)`. -/
theorem rawExp_R1_cX (k r t m : ℤ) :
    (mhatRawExp 1 MhatRow.R1 k r t m).cX =
      k + 2 * r - 2 * m +
        (if (mhatDenomExp 1 MhatRow.R1 r).lexPositive then -t else t) := by
  unfold mhatRawExp mhatJThetaExp mhatAppellNumeratorExp mhatDenomBranchExp
    mhatDenomExp mhatDThetaExp AffineXY.add AffineXY.smul AffineXY.neg
    MhatRow.lead MhatRow.jArg MhatRow.mArg MhatRow.mZ
  simp only [AffineXY.lexPositive]; split <;> ring

/-- R0 requires x even: if the rawTerm contributes at x, then x = -2r+2m is even. -/
theorem R0_x_even (k r t m : ℤ) : Even ((mhatRawExp 1 MhatRow.R0 k r t m).cX) := by
  rw [rawExp_R0_cX]; exact ⟨m - r, by ring⟩

/-- R2 requires x odd: the rawExp x-component is always odd. -/
theorem R2_x_odd (k r t m : ℤ) : ¬ Even ((mhatRawExp 1 MhatRow.R2 k r t m).cX) := by
  rw [rawExp_R2_cX]; intro ⟨c, hc⟩; omega

/-! ## Zero contribution: rows with wrong parity contribute 0 -/

/-- R2's raw term coefficient vanishes at any even x (its x-component is always odd). -/
theorem R2_rawTerm_coeff_zero_of_even_x (e x y : ℤ) (hx : Even x) (k r t m : ℤ) :
    (mhatRawTerm 1 MhatRow.R2 k r t m).coeff (expQXY e x y) = 0 := by
  rw [mhatRawTerm_coeff]
  simp only [ite_eq_right_iff]
  intro ⟨_, hxeq, _⟩
  exfalso; exact R2_x_odd k r t m (hxeq ▸ hx)

/-- R0's raw term coefficient vanishes at any odd x (its x-component is always even). -/
theorem R0_rawTerm_coeff_zero_of_odd_x (e x y : ℤ) (hx : ¬ Even x) (k r t m : ℤ) :
    (mhatRawTerm 1 MhatRow.R0 k r t m).coeff (expQXY e x y) = 0 := by
  rw [mhatRawTerm_coeff]
  simp only [ite_eq_right_iff]
  intro ⟨_, hxeq, _⟩
  exfalso; exact hx (hxeq ▸ R0_x_even k r t m)

/-- R1 requires y even. -/
theorem R1_y_even (k r t m : ℤ) : Even ((mhatRawExp 1 MhatRow.R1 k r t m).cY) := by
  rw [rawExp_R1_cY]; exact ⟨m - r, by ring⟩

/-- R3 requires y odd. -/
theorem R3_y_odd (k r t m : ℤ) : ¬ Even ((mhatRawExp 1 MhatRow.R3 k r t m).cY) := by
  rw [rawExp_R3_cY]; intro ⟨c, hc⟩; omega

/-- R3's raw term coefficient vanishes at any even y. -/
theorem R3_rawTerm_coeff_zero_of_even_y (e x y : ℤ) (hy : Even y) (k r t m : ℤ) :
    (mhatRawTerm 1 MhatRow.R3 k r t m).coeff (expQXY e x y) = 0 := by
  rw [mhatRawTerm_coeff]
  simp only [ite_eq_right_iff]
  intro ⟨_, _, hyeq⟩
  exfalso; exact R3_y_odd k r t m (hyeq ▸ hy)

/-- R1's raw term coefficient vanishes at any odd y. -/
theorem R1_rawTerm_coeff_zero_of_odd_y (e x y : ℤ) (hy : ¬ Even y) (k r t m : ℤ) :
    (mhatRawTerm 1 MhatRow.R1 k r t m).coeff (expQXY e x y) = 0 := by
  rw [mhatRawTerm_coeff]
  simp only [ite_eq_right_iff]
  intro ⟨_, _, hyeq⟩
  exfalso; exact hy (hyeq ▸ R1_y_even k r t m)

/-! ## Row-level finsum vanishing: wrong-parity rows contribute 0

These are the key lemmas for the parity split of the 4-row sum. -/

/-- R2's entire row finsum vanishes at even x. -/
theorem R2_row_finsum_zero_of_even_x (e x y : ℤ) (hx : Even x) :
    (∑ᶠ idx : (ℤ × (ℤ × ℤ)) × ℤ,
      (mhatRawTerm 1 MhatRow.R2 idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
        (expQXY e x y)) = 0 := by
  apply finsum_eq_zero_of_forall_eq_zero
  intro ⟨⟨k, r, t⟩, m⟩
  exact R2_rawTerm_coeff_zero_of_even_x e x y hx k r t m

/-- R0's entire row finsum vanishes at odd x. -/
theorem R0_row_finsum_zero_of_odd_x (e x y : ℤ) (hx : ¬ Even x) :
    (∑ᶠ idx : (ℤ × (ℤ × ℤ)) × ℤ,
      (mhatRawTerm 1 MhatRow.R0 idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
        (expQXY e x y)) = 0 := by
  apply finsum_eq_zero_of_forall_eq_zero
  intro ⟨⟨k, r, t⟩, m⟩
  exact R0_rawTerm_coeff_zero_of_odd_x e x y hx k r t m

/-- R3's entire row finsum vanishes at even y. -/
theorem R3_row_finsum_zero_of_even_y (e x y : ℤ) (hy : Even y) :
    (∑ᶠ idx : (ℤ × (ℤ × ℤ)) × ℤ,
      (mhatRawTerm 1 MhatRow.R3 idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
        (expQXY e x y)) = 0 := by
  apply finsum_eq_zero_of_forall_eq_zero
  intro ⟨⟨k, r, t⟩, m⟩
  exact R3_rawTerm_coeff_zero_of_even_y e x y hy k r t m

/-- R1's entire row finsum vanishes at odd y. -/
theorem R1_row_finsum_zero_of_odd_y (e x y : ℤ) (hy : ¬ Even y) :
    (∑ᶠ idx : (ℤ × (ℤ × ℤ)) × ℤ,
      (mhatRawTerm 1 MhatRow.R1 idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
        (expQXY e x y)) = 0 := by
  apply finsum_eq_zero_of_forall_eq_zero
  intro ⟨⟨k, r, t⟩, m⟩
  exact R1_rawTerm_coeff_zero_of_odd_y e x y hy k r t m

/-! ## Parity split of the 4-row Fintype sum -/

private theorem sum_MhatRow_four_rat (f : MhatRow → ℚ) :
    ∑ row : MhatRow, f row =
      f MhatRow.R0 + f MhatRow.R1 + f MhatRow.R2 + f MhatRow.R3 := by
  show Finset.univ.sum f = _
  have : (Finset.univ : Finset MhatRow) = {.R0, .R1, .R2, .R3} := by decide
  rw [this]; simp [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]; ring

/-- Even x, even y: the 4-row sum reduces to R0 + R1. -/
theorem Mhat_row_sum_even_even (e x y : ℤ) (hx : Even x) (hy : Even y) :
    ∑ row : MhatRow,
      (∑ᶠ idx : (ℤ × (ℤ × ℤ)) × ℤ,
        (mhatRawTerm 1 row idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
          (expQXY e x y)) =
    (∑ᶠ idx : (ℤ × (ℤ × ℤ)) × ℤ,
      (mhatRawTerm 1 MhatRow.R0 idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
        (expQXY e x y)) +
    (∑ᶠ idx : (ℤ × (ℤ × ℤ)) × ℤ,
      (mhatRawTerm 1 MhatRow.R1 idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
        (expQXY e x y)) := by
  rw [sum_MhatRow_four_rat,
      R2_row_finsum_zero_of_even_x e x y hx,
      R3_row_finsum_zero_of_even_y e x y hy]; ring

/-- Even x, odd y: the 4-row sum reduces to R0 + R3. -/
theorem Mhat_row_sum_even_odd (e x y : ℤ) (hx : Even x) (hy : ¬ Even y) :
    ∑ row : MhatRow,
      (∑ᶠ idx : (ℤ × (ℤ × ℤ)) × ℤ,
        (mhatRawTerm 1 row idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
          (expQXY e x y)) =
    (∑ᶠ idx : (ℤ × (ℤ × ℤ)) × ℤ,
      (mhatRawTerm 1 MhatRow.R0 idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
        (expQXY e x y)) +
    (∑ᶠ idx : (ℤ × (ℤ × ℤ)) × ℤ,
      (mhatRawTerm 1 MhatRow.R3 idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
        (expQXY e x y)) := by
  rw [sum_MhatRow_four_rat,
      R2_row_finsum_zero_of_even_x e x y hx,
      R1_row_finsum_zero_of_odd_y e x y hy]; ring

/-- Odd x, even y: the 4-row sum reduces to R2 + R1. -/
theorem Mhat_row_sum_odd_even (e x y : ℤ) (hx : ¬ Even x) (hy : Even y) :
    ∑ row : MhatRow,
      (∑ᶠ idx : (ℤ × (ℤ × ℤ)) × ℤ,
        (mhatRawTerm 1 row idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
          (expQXY e x y)) =
    (∑ᶠ idx : (ℤ × (ℤ × ℤ)) × ℤ,
      (mhatRawTerm 1 MhatRow.R2 idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
        (expQXY e x y)) +
    (∑ᶠ idx : (ℤ × (ℤ × ℤ)) × ℤ,
      (mhatRawTerm 1 MhatRow.R1 idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
        (expQXY e x y)) := by
  rw [sum_MhatRow_four_rat,
      R0_row_finsum_zero_of_odd_x e x y hx,
      R3_row_finsum_zero_of_even_y e x y hy]; ring

/-- Odd x, odd y: the 4-row sum reduces to R2 + R3. -/
theorem Mhat_row_sum_odd_odd (e x y : ℤ) (hx : ¬ Even x) (hy : ¬ Even y) :
    ∑ row : MhatRow,
      (∑ᶠ idx : (ℤ × (ℤ × ℤ)) × ℤ,
        (mhatRawTerm 1 row idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
          (expQXY e x y)) =
    (∑ᶠ idx : (ℤ × (ℤ × ℤ)) × ℤ,
      (mhatRawTerm 1 MhatRow.R2 idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
        (expQXY e x y)) +
    (∑ᶠ idx : (ℤ × (ℤ × ℤ)) × ℤ,
      (mhatRawTerm 1 MhatRow.R3 idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
        (expQXY e x y)) := by
  rw [sum_MhatRow_four_rat,
      R0_row_finsum_zero_of_odd_x e x y hx,
      R1_row_finsum_zero_of_odd_y e x y hy]; ring

/-! ## Branch coefficient = Hecke cone sign (key bridge identity)

The signed branch coefficient sgCone(r-1, u) is EXACTLY the Hecke sg function
shifted by 1. This connects the Appell geometric branch to the Hecke cone. -/

/-- R0 denominator exponent at `ell = 1`. -/
theorem R0_denomExp_one (r : ℤ) :
    mhatDenomExp 1 MhatRow.R0 r = ⟨90 * r - 18, 0, -1⟩ := by
  unfold mhatDenomExp MhatRow.mArg MhatRow.mZ
  show AffineXY.mk (90 * (r - 1) + 54 + 18) (2 + -2) (-3 + 2) = AffineXY.mk (90 * r - 18) 0 (-1)
  congr 1 <;> omega

/-- R1 denominator exponent at `ell = 1`. -/
theorem R1_denomExp_one (r : ℤ) :
    mhatDenomExp 1 MhatRow.R1 r = ⟨90 * r - 54, -1, 0⟩ := by
  unfold mhatDenomExp MhatRow.mArg MhatRow.mZ
  show AffineXY.mk (90 * (r - 1) + 54 + -18) (-3 + 2) (2 + -2) = AffineXY.mk (90 * r - 54) (-1) 0
  congr 1 <;> omega

/-- R0 is lex-positive exactly when `r ≥ 1`. -/
theorem R0_lexPositive_iff (r : ℤ) :
    (mhatDenomExp 1 MhatRow.R0 r).lexPositive ↔ 1 ≤ r := by
  rw [R0_denomExp_one]; unfold AffineXY.lexPositive; simp; omega

/-- R1 is lex-positive exactly when `r ≥ 1`. -/
theorem R1_lexPositive_iff (r : ℤ) :
    (mhatDenomExp 1 MhatRow.R1 r).lexPositive ↔ 1 ≤ r := by
  rw [R1_denomExp_one]; unfold AffineXY.lexPositive; simp; omega

/-- R2 denominator exponent at `ell = 1`. -/
theorem R2_denomExp_one (r : ℤ) :
    mhatDenomExp 1 MhatRow.R2 r = ⟨90 * r - 63, 0, -1⟩ := by
  unfold mhatDenomExp MhatRow.mArg MhatRow.mZ
  show AffineXY.mk (90 * (r - 1) + 9 + 18) (2 + -2) (-3 + 2) =
    AffineXY.mk (90 * r - 63) 0 (-1)
  congr 1 <;> omega

/-- R3 denominator exponent at `ell = 1`. -/
theorem R3_denomExp_one (r : ℤ) :
    mhatDenomExp 1 MhatRow.R3 r = ⟨90 * r - 99, -1, 0⟩ := by
  unfold mhatDenomExp MhatRow.mArg MhatRow.mZ
  show AffineXY.mk (90 * (r - 1) + 9 + -18) (-3 + 2) (2 + -2) =
    AffineXY.mk (90 * r - 99) (-1) 0
  congr 1 <;> omega

/-- R2 is lex-positive exactly when `r ≥ 1`. -/
theorem R2_lexPositive_iff (r : ℤ) :
    (mhatDenomExp 1 MhatRow.R2 r).lexPositive ↔ 1 ≤ r := by
  rw [R2_denomExp_one]; unfold AffineXY.lexPositive; simp; omega

/-- R3 is lex-positive exactly when `r ≥ 2`. -/
theorem R3_lexPositive_iff (r : ℤ) :
    (mhatDenomExp 1 MhatRow.R3 r).lexPositive ↔ 2 ≤ r := by
  rw [R3_denomExp_one]; unfold AffineXY.lexPositive; simp; omega

/-! ## Signed strip coordinates for row reindexing -/

/-- R0 raw exponent in signed strip coordinate `l`. -/
theorem R0_signed_rawExp (a y r l : ℤ) :
    mhatRawExp 1 MhatRow.R0 (2 * a + y + l) r (if 1 ≤ r then l else -l) (r + a) =
      ⟨heckePhi (2 * a) y (r + l) (a - l), 2 * a, y⟩ := by
  by_cases hr : 1 ≤ r
  · have hp : (mhatDenomExp 1 MhatRow.R0 r).lexPositive :=
      (R0_lexPositive_iff r).2 hr
    have hp' : (⟨90 * r - 18, 0, -1⟩ : AffineXY).lexPositive := by
      simpa [R0_denomExp_one] using hp
    simp [mhatRawExp, mhatJThetaExp, mhatAppellNumeratorExp, mhatDenomBranchExp,
      R0_denomExp_one, mhatDThetaExp, AffineXY.add, AffineXY.smul, AffineXY.neg,
      MhatRow.lead, MhatRow.jArg, MhatRow.mArg, MhatRow.mZ, hp', hr,
      heckePhi, FhmExp, BYExp, BXExp]
    constructor
    · ring
    constructor <;> ring
  · have hp : ¬ (mhatDenomExp 1 MhatRow.R0 r).lexPositive :=
      mt (R0_lexPositive_iff r).1 hr
    have hp' : ¬ (⟨90 * r - 18, 0, -1⟩ : AffineXY).lexPositive := by
      simpa [R0_denomExp_one] using hp
    simp [mhatRawExp, mhatJThetaExp, mhatAppellNumeratorExp, mhatDenomBranchExp,
      R0_denomExp_one, mhatDThetaExp, AffineXY.add, AffineXY.smul, AffineXY.neg,
      MhatRow.lead, MhatRow.jArg, MhatRow.mArg, MhatRow.mZ, hp', hr,
      heckePhi, FhmExp, BYExp, BXExp]
    constructor
    · ring
    constructor <;> ring

/-- R0 raw coefficient in signed strip coordinate `l`. -/
theorem R0_signed_rawCoeff (a y r l : ℤ) :
    mhatRawCoeff 1 MhatRow.R0 (2 * a + y + l) r (if 1 ≤ r then l else -l) (r + a) =
      negOnePowIntQ (2 * a + y + (a - l)) * (((sg (r - 1) l : ℤ) : ℚ)) := by
  have hsign :
      negOnePowIntQ ((2 * a + y + l) + r + (r + a)) =
        negOnePowIntQ (2 * a + y + (a - l)) := by
    apply negOnePowIntQ_eq_of_even_sub
    refine ⟨l + r, ?_⟩
    ring
  by_cases hr : 1 ≤ r
  · have hp : (mhatDenomExp 1 MhatRow.R0 r).lexPositive :=
      (R0_lexPositive_iff r).2 hr
    unfold mhatRawCoeff mhatDenomBranchCoeff sg
    rw [hsign]
    have hr0 : 0 ≤ r - 1 := by omega
    have hrn : ¬ r - 1 < 0 := by omega
    by_cases hl : 0 ≤ l
    · simp [hp, hr, hr0, hrn, hl]
    · have hll : l < 0 := by omega
      simp [hp, hr, hr0, hrn, hl, hll]
  · have hp : ¬ (mhatDenomExp 1 MhatRow.R0 r).lexPositive :=
      mt (R0_lexPositive_iff r).1 hr
    unfold mhatRawCoeff mhatDenomBranchCoeff sg
    rw [hsign]
    have hrlt : r - 1 < 0 := by omega
    have hrn : ¬ 0 ≤ r - 1 := by omega
    by_cases hl : l < 0
    · have ht : 1 ≤ -l := by omega
      have hln : ¬ 0 ≤ l := by omega
      simp [hp, hr, hrlt, hrn, hl, hln, ht]
    · have ht : ¬ 1 ≤ -l := by omega
      have hl0 : 0 ≤ l := by omega
      simp [hp, hr, hrlt, hrn, hl, hl0, ht]

/-- R1 raw exponent in signed strip coordinate `l`. -/
theorem R1_signed_rawExp (x b r l : ℤ) :
    mhatRawExp 1 MhatRow.R1 (x + 2 * b + l) r (if 1 ≤ r then l else -l) (r + b) =
      ⟨heckePhi x (2 * b) (r + b) (l - b), x, 2 * b⟩ := by
  by_cases hr : 1 ≤ r
  · have hp : (mhatDenomExp 1 MhatRow.R1 r).lexPositive :=
      (R1_lexPositive_iff r).2 hr
    have hp' : (⟨90 * r - 54, -1, 0⟩ : AffineXY).lexPositive := by
      simpa [R1_denomExp_one] using hp
    simp [mhatRawExp, mhatJThetaExp, mhatAppellNumeratorExp, mhatDenomBranchExp,
      R1_denomExp_one, mhatDThetaExp, AffineXY.add, AffineXY.smul, AffineXY.neg,
      MhatRow.lead, MhatRow.jArg, MhatRow.mZ, hp', hr,
      heckePhi, FhmExp, BYExp, BXExp]
    constructor
    · ring
    constructor <;> ring
  · have hp : ¬ (mhatDenomExp 1 MhatRow.R1 r).lexPositive :=
      mt (R1_lexPositive_iff r).1 hr
    have hp' : ¬ (⟨90 * r - 54, -1, 0⟩ : AffineXY).lexPositive := by
      simpa [R1_denomExp_one] using hp
    simp [mhatRawExp, mhatJThetaExp, mhatAppellNumeratorExp, mhatDenomBranchExp,
      R1_denomExp_one, mhatDThetaExp, AffineXY.add, AffineXY.smul, AffineXY.neg,
      MhatRow.lead, MhatRow.jArg, MhatRow.mZ, hp', hr,
      heckePhi, FhmExp, BYExp, BXExp]
    constructor
    · ring
    constructor <;> ring

/-- R1 raw coefficient in signed strip coordinate `l`. -/
theorem R1_signed_rawCoeff (x b r l : ℤ) :
    mhatRawCoeff 1 MhatRow.R1 (x + 2 * b + l) r (if 1 ≤ r then l else -l) (r + b) =
      negOnePowIntQ (x + 2 * b + (l - b)) * (((sg (r - 1) l : ℤ) : ℚ)) := by
  have hsign :
      negOnePowIntQ ((x + 2 * b + l) + r + (r + b)) =
        negOnePowIntQ (x + 2 * b + (l - b)) := by
    apply negOnePowIntQ_eq_of_even_sub
    refine ⟨b + r, ?_⟩
    ring
  by_cases hr : 1 ≤ r
  · have hp : (mhatDenomExp 1 MhatRow.R1 r).lexPositive :=
      (R1_lexPositive_iff r).2 hr
    unfold mhatRawCoeff mhatDenomBranchCoeff sg
    rw [hsign]
    have hr0 : 0 ≤ r - 1 := by omega
    have hrn : ¬ r - 1 < 0 := by omega
    by_cases hl : 0 ≤ l
    · simp [hp, hr, hr0, hrn, hl]
    · have hll : l < 0 := by omega
      simp [hp, hr, hr0, hrn, hl, hll]
  · have hp : ¬ (mhatDenomExp 1 MhatRow.R1 r).lexPositive :=
      mt (R1_lexPositive_iff r).1 hr
    unfold mhatRawCoeff mhatDenomBranchCoeff sg
    rw [hsign]
    have hrlt : r - 1 < 0 := by omega
    have hrn : ¬ 0 ≤ r - 1 := by omega
    by_cases hl : l < 0
    · have ht : 1 ≤ -l := by omega
      have hln : ¬ 0 ≤ l := by omega
      simp [hp, hr, hrlt, hrn, hl, hln, ht]
    · have ht : ¬ 1 ≤ -l := by omega
      have hl0 : 0 ≤ l := by omega
      simp [hp, hr, hrlt, hrn, hl, hl0, ht]

/-- R2 raw exponent in signed strip coordinate `l`. -/
theorem R2_signed_rawExp (a y r l : ℤ) :
    mhatRawExp 1 MhatRow.R2 (2 * a + 1 + y + l) r (if 1 ≤ r then l else -l) (r + a) =
      ⟨heckePhi (2 * a + 1) y (r + l) (a - l), 2 * a + 1, y⟩ := by
  by_cases hr : 1 ≤ r
  · have hp : (mhatDenomExp 1 MhatRow.R2 r).lexPositive :=
      (R2_lexPositive_iff r).2 hr
    have hp' : (⟨90 * r - 63, 0, -1⟩ : AffineXY).lexPositive := by
      simpa [R2_denomExp_one] using hp
    simp [mhatRawExp, mhatJThetaExp, mhatAppellNumeratorExp, mhatDenomBranchExp,
      R2_denomExp_one, mhatDThetaExp, AffineXY.add, AffineXY.smul, AffineXY.neg,
      MhatRow.lead, MhatRow.jArg, MhatRow.mZ, hp', hr,
      heckePhi, FhmExp, BYExp, BXExp]
    constructor
    · ring
    constructor <;> ring
  · have hp : ¬ (mhatDenomExp 1 MhatRow.R2 r).lexPositive :=
      mt (R2_lexPositive_iff r).1 hr
    have hp' : ¬ (⟨90 * r - 63, 0, -1⟩ : AffineXY).lexPositive := by
      simpa [R2_denomExp_one] using hp
    simp [mhatRawExp, mhatJThetaExp, mhatAppellNumeratorExp, mhatDenomBranchExp,
      R2_denomExp_one, mhatDThetaExp, AffineXY.add, AffineXY.smul, AffineXY.neg,
      MhatRow.lead, MhatRow.jArg, MhatRow.mZ, hp', hr,
      heckePhi, FhmExp, BYExp, BXExp]
    constructor
    · ring
    constructor <;> ring

/-- R2 raw coefficient in signed strip coordinate `l`. -/
theorem R2_signed_rawCoeff (a y r l : ℤ) :
    mhatRawCoeff 1 MhatRow.R2 (2 * a + 1 + y + l) r (if 1 ≤ r then l else -l) (r + a) =
      negOnePowIntQ (2 * a + 1 + y + (a - l)) * (((sg (r - 1) l : ℤ) : ℚ)) := by
  have hsign :
      negOnePowIntQ ((2 * a + 1 + y + l) + r + (r + a)) =
        negOnePowIntQ (2 * a + 1 + y + (a - l)) := by
    apply negOnePowIntQ_eq_of_even_sub
    refine ⟨l + r, ?_⟩
    ring
  by_cases hr : 1 ≤ r
  · have hp : (mhatDenomExp 1 MhatRow.R2 r).lexPositive :=
      (R2_lexPositive_iff r).2 hr
    unfold mhatRawCoeff mhatDenomBranchCoeff sg
    rw [hsign]
    have hr0 : 0 ≤ r - 1 := by omega
    have hrn : ¬ r - 1 < 0 := by omega
    by_cases hl : 0 ≤ l
    · simp [hp, hr, hr0, hrn, hl]
    · have hll : l < 0 := by omega
      simp [hp, hr, hr0, hrn, hl, hll]
  · have hp : ¬ (mhatDenomExp 1 MhatRow.R2 r).lexPositive :=
      mt (R2_lexPositive_iff r).1 hr
    unfold mhatRawCoeff mhatDenomBranchCoeff sg
    rw [hsign]
    have hrlt : r - 1 < 0 := by omega
    have hrn : ¬ 0 ≤ r - 1 := by omega
    by_cases hl : l < 0
    · have ht : 1 ≤ -l := by omega
      have hln : ¬ 0 ≤ l := by omega
      simp [hp, hr, hrlt, hrn, hl, hln, ht]
    · have ht : ¬ 1 ≤ -l := by omega
      have hl0 : 0 ≤ l := by omega
      simp [hp, hr, hrlt, hrn, hl, hl0, ht]

/-- R3 raw exponent in signed strip coordinate `l`. -/
theorem R3_signed_rawExp (x b r l : ℤ) :
    mhatRawExp 1 MhatRow.R3 (x + 2 * b + 1 + l) r (if 2 ≤ r then l else -l) (r + b) =
      ⟨heckePhi x (2 * b + 1) (r + b) (l - b), x, 2 * b + 1⟩ := by
  by_cases hr : 2 ≤ r
  · have hp : (mhatDenomExp 1 MhatRow.R3 r).lexPositive :=
      (R3_lexPositive_iff r).2 hr
    have hp' : (⟨90 * r - 99, -1, 0⟩ : AffineXY).lexPositive := by
      simpa [R3_denomExp_one] using hp
    simp [mhatRawExp, mhatJThetaExp, mhatAppellNumeratorExp, mhatDenomBranchExp,
      R3_denomExp_one, mhatDThetaExp, AffineXY.add, AffineXY.smul, AffineXY.neg,
      MhatRow.lead, MhatRow.jArg, MhatRow.mZ, hp', hr,
      heckePhi, FhmExp, BYExp, BXExp]
    constructor
    · ring
    constructor <;> ring
  · have hp : ¬ (mhatDenomExp 1 MhatRow.R3 r).lexPositive :=
      mt (R3_lexPositive_iff r).1 hr
    have hp' : ¬ (⟨90 * r - 99, -1, 0⟩ : AffineXY).lexPositive := by
      simpa [R3_denomExp_one] using hp
    simp [mhatRawExp, mhatJThetaExp, mhatAppellNumeratorExp, mhatDenomBranchExp,
      R3_denomExp_one, mhatDThetaExp, AffineXY.add, AffineXY.smul, AffineXY.neg,
      MhatRow.lead, MhatRow.jArg, MhatRow.mZ, hp', hr,
      heckePhi, FhmExp, BYExp, BXExp]
    constructor
    · ring
    constructor <;> ring

/-- R3 raw coefficient in signed strip coordinate `l`; note the shifted threshold `r-2`. -/
theorem R3_signed_rawCoeff (x b r l : ℤ) :
    mhatRawCoeff 1 MhatRow.R3 (x + 2 * b + 1 + l) r (if 2 ≤ r then l else -l) (r + b) =
      negOnePowIntQ (x + 2 * b + 1 + (l - b)) * (((sg (r - 2) l : ℤ) : ℚ)) := by
  have hsign :
      negOnePowIntQ ((x + 2 * b + 1 + l) + r + (r + b)) =
        negOnePowIntQ (x + 2 * b + 1 + (l - b)) := by
    apply negOnePowIntQ_eq_of_even_sub
    refine ⟨b + r, ?_⟩
    ring
  by_cases hr : 2 ≤ r
  · have hp : (mhatDenomExp 1 MhatRow.R3 r).lexPositive :=
      (R3_lexPositive_iff r).2 hr
    unfold mhatRawCoeff mhatDenomBranchCoeff sg
    rw [hsign]
    have hr0 : 0 ≤ r - 2 := by omega
    have hrn : ¬ r - 2 < 0 := by omega
    by_cases hl : 0 ≤ l
    · simp [hp, hr, hr0, hrn, hl]
    · have hll : l < 0 := by omega
      simp [hp, hr, hr0, hrn, hl, hll]
  · have hp : ¬ (mhatDenomExp 1 MhatRow.R3 r).lexPositive :=
      mt (R3_lexPositive_iff r).1 hr
    unfold mhatRawCoeff mhatDenomBranchCoeff sg
    rw [hsign]
    have hrlt : r - 2 < 0 := by omega
    have hrn : ¬ 0 ≤ r - 2 := by omega
    by_cases hl : l < 0
    · have ht : 1 ≤ -l := by omega
      have hln : ¬ 0 ≤ l := by omega
      simp [hp, hr, hrlt, hrn, hl, hln, ht]
    · have ht : ¬ 1 ≤ -l := by omega
      have hl0 : 0 ≤ l := by omega
      simp [hp, hr, hrlt, hrn, hl, hl0, ht]

/-! ## Appell-Hecke q-degree ring identities

The exact (r,l)→(u,v) maps at general x,y (verified numerically):
  R0 at x=2a: (u,v) = (r+l, a-l), so q_R0 = heckePhi(2a, y, r+l, a-l)
  R1 at y=2b: (u,v) = (s+l, l-b), so q_R1 = heckePhi(x, 2b, s+b, l-b)

NOTE: these are q-degree identities only. The SIGNS do NOT match pointwise —
the R0+R1 combined sign ≠ Hecke sg at individual (u,v). The identity holds
at the SUMMED level via the omega telescope mechanism. -/

/-- R0 q-degree ring identity: the R0 raw q-degree at x=2a equals heckePhi at (u,v)=(r+l, a-l). -/
theorem qR0_eq_heckePhi (a y r l : ℤ) :
    (9 * (2*a+y+l) * (2*a+y+l-1) + (45*r*(r-1)+18*r) + (90*r-18)*l +
      (45*(r+a)*(r+a-1)-18*(r+a)))
    = heckePhi (2*a) y (r+l) (a-l) := by
  unfold heckePhi FhmExp BYExp BXExp; ring

/-- R1 q-degree ring identity: the R1 raw q-degree at y=2b equals heckePhi at (u,v)=(s+b, l-b). -/
theorem qR1_eq_heckePhi (x b s l : ℤ) :
    (9 * (x+2*b+l) * (x+2*b+l-1) + (45*s*(s-1)-18*s) + (90*s-54)*l +
      (45*(s+b)*(s+b-1)+18*(s+b)))
    = heckePhi x (2*b) (s+b) (l-b) := by
  unfold heckePhi FhmExp BYExp BXExp; ring

/-- R2 q-degree ring identity: at x=2a+1, (u,v)=(r+l, a-l).
Note: R2 jArg c0=9, so jTheta_q = 9*k² (not 9*k*(k-1)). -/
theorem qR2_eq_heckePhi (a y r l : ℤ) :
    (-9 + 9*(2*a+1+y+l)*(2*a+1+y+l) + (45*r*(r-1)+18*r) + (90*r-63)*l +
      (45*(r+a)*(r+a-1)-18*(r+a)))
    = heckePhi (2*a+1) y (r+l) (a-l) := by
  unfold heckePhi FhmExp BYExp BXExp; ring

/-- R3 q-degree ring identity: at y=2b+1, (u,v)=(s+b, l-b).
Note: R3 jArg c0=9, so jTheta_q = 9*k² (not 9*k*(k-1)). -/
theorem qR3_eq_heckePhi (x b s l : ℤ) :
    (-9 + 9*(x+2*b+1+l)*(x+2*b+1+l) + (45*s*(s-1)-18*s) + (90*s-99)*l +
      (45*(s+b)*(s+b-1)+18*(s+b)))
    = heckePhi x (2*b+1) (s+b) (l-b) := by
  unfold heckePhi FhmExp BYExp BXExp; ring

/-! ## The Phi involution and sg pairing — the sum-level telescope mechanism

Phi(x,y,u,v) = Phi(x,y,1-u-v,v): an involution pairing U with 1-U-V at fixed V.
Under this involution, sg(A,B) + sg(-A-1,B) telescopes to a constant. -/

/-- The Phi involution: `Phi(u,v) = Phi(1-u-v, v)`. -/
theorem heckePhi_invol (x y u v : ℤ) :
    heckePhi x y u v = heckePhi x y (1 - u - v) v := by
  unfold heckePhi FhmExp BYExp BXExp; ring

/-- The sg pairing under `A → -A-1`: `sg(A,B) + sg(-A-1,B) = if B≥0 then 1 else -1`. -/
theorem sg_invol_pair (A B : ℤ) :
    (sg A B : ℤ) + sg (-A - 1) B = if 0 ≤ B then 1 else -1 := by
  unfold sg; by_cases hB : 0 ≤ B <;> simp [hB] <;> omega

/-! ## R01 bracket pairing under the involution (b = -a sector)

For `b = -a` (the anti-diagonal sector), the involution `U → 1-U-V`
gives exact pointwise pairing: `R01(U) + R01(τ(U)) = 2*uvOmega(U)`.

For general `(a,b)`, the pairing has a nonzero defect that cancels across
V values at shared q-degrees — a sum-level identity. -/

/-- The R0+R1 bracket (coefficient without `(-1)^V` factor). -/
def R01Bracket (a b U V : ℤ) : ℤ :=
  sg (U + V - a - 1) (a - V) + sg (U - b - 1) (V + b)

/-- The Hecke cone bracket. -/
def uvOmegaBracket (a b V : ℤ) : ℤ :=
  sg (a - V) (b + V)

/-- Anti-diagonal pairing: for `b = -a`, the involution gives exact 2*uvOmega. -/
theorem R01Bracket_pair_anti_diag (a U V : ℤ) :
    R01Bracket a (-a) U V + R01Bracket a (-a) (1 - U - V) V
      = 2 * uvOmegaBracket a (-a) V := by
  unfold R01Bracket uvOmegaBracket sg
  split_ifs <;> omega

/-! ## NoZeroDivisors cancellation: clearedD = 0 ↔ Fhm = Ghat

S = HahnSeries ExpQXY ℚ has NoZeroDivisors (Mathlib instance).
So Fhm*BY*BX = Ghat*BY*BX implies Fhm = Ghat by cancellation. -/

/-- Mhat = Ghat * BY * BX (algebraic, from locInv factoring). -/
theorem Mhat_eq_Ghat_mul_BYBX :
    PpairY * ghatBoundary 1 MhatRow.R1 + PpairX * ghatBoundary 1 MhatRow.R0 =
    Ghat 1 * ghatBoundary 1 MhatRow.R0 * ghatBoundary 1 MhatRow.R1 := by
  rw [Ghat_one_eq_pairs]
  have hPY : PpairY = ghatBoundary 1 MhatRow.R0 * GhatPairY := by
    rw [GhatPairY_eq_locInv_mul_PpairY]
    rw [← mul_assoc, mul_locInv _ (ghatBoundary_ne_zero 1 MhatRow.R0), one_mul]
  have hPX : PpairX = ghatBoundary 1 MhatRow.R1 * GhatPairX := by
    rw [GhatPairX_eq_locInv_mul_PpairX]
    rw [← mul_assoc, mul_locInv _ (ghatBoundary_ne_zero 1 MhatRow.R1), one_mul]
  rw [hPY, hPX]; ring

/-- BY * BX ≠ 0 (product of nonzero theta functions). -/
theorem BYBX_ne_zero : ghatBoundary 1 MhatRow.R0 * ghatBoundary 1 MhatRow.R1 ≠ 0 :=
  mul_ne_zero (ghatBoundary_ne_zero 1 MhatRow.R0) (ghatBoundary_ne_zero 1 MhatRow.R1)

/-- clearedD = 0 implies Fhm = Ghat 1 (forward direction uses Fhm_eq_Ghat_of_cleared). -/
theorem Fhm_eq_Ghat_of_clearedD_zero
    (h : Fhm * ghatBoundary 1 MhatRow.R0 * ghatBoundary 1 MhatRow.R1 -
      (PpairY * ghatBoundary 1 MhatRow.R1 + PpairX * ghatBoundary 1 MhatRow.R0) = 0) :
    Fhm = Ghat 1 :=
  Fhm_eq_Ghat_of_cleared (sub_eq_zero.mp h)

/-! ## Cross-V defect wall decomposition

The defect from the involution pairing decomposes as two "wall" step functions.
This is the key structural identity for the cross-V cancellation. -/

/-- Integer step function: 1 if c ≤ n, else 0 (as ℚ). -/
def stepGE (c n : ℤ) : ℚ := if c ≤ n then 1 else 0

/-- The wall function: a finite signed indicator. -/
def wall (p q n : ℤ) : ℚ := stepGE (q + 1) n - stepGE (1 - p) n

/-- Integer sign as ℚ. -/
def zsgn (n : ℤ) : ℚ := if 0 ≤ n then 1 else -1

/-- The same-sign indicator is the half-sum of the two one-variable signs. -/
theorem sg_eq_zsgn (A B : ℤ) :
    ((sg A B : ℤ) : ℚ) = (zsgn A + zsgn B) / 2 := by
  unfold sg zsgn
  split_ifs <;> norm_num <;> omega

/-- The cross-V defect from the involution pairing. -/
def crossDefect (a b U V : ℤ) : ℚ :=
  (zsgn (U + V - a - 1) + zsgn (-U - a) + zsgn (U - b - 1) + zsgn (-U - V - b)) / 2

set_option maxHeartbeats 800000 in
/-- The defect decomposes as two wall functions. -/
theorem crossDefect_eq_wall (a b U V : ℤ) :
    crossDefect a b U V = wall a b U + wall b a (U + V) := by
  simp only [crossDefect, wall, stepGE, zsgn]
  split_ifs <;> norm_num <;> omega

/-- The involution-pair defect of the R0/R1 bracket is exactly `crossDefect`. -/
theorem R01Bracket_pair_defect (a b U V : ℤ) :
    (((R01Bracket a b U V + R01Bracket a b (1 - U - V) V -
      2 * uvOmegaBracket a b V : ℤ) : ℚ) = crossDefect a b U V) := by
  unfold R01Bracket uvOmegaBracket crossDefect
  simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  rw [sg_eq_zsgn, sg_eq_zsgn, sg_eq_zsgn, sg_eq_zsgn, sg_eq_zsgn]
  ring

/-- In wall coordinates the two wall terms are the same one-variable function. -/
theorem wall_coord_eq (a b p : ℤ) :
    wall b a (p + a + 1) = wall a b (-a - p) := by
  unfold wall stepGE
  split_ifs <;> norm_num <;> omega

/-! ## Cross-V defect cancellation — the FINAL algebraic mechanism

Change variables: p = U+V-a-1, q = -U-a. Then Defect = g_K(p) + g_K(q)
and Phi becomes symmetric in (p,q) with L = 2a+4b+5 (always odd).

The root-pair involution q → 8p+L-q preserves Phi, has no integer fixed
point (L odd), and flips (-1)^{p+q}. This gives pairwise cancellation. -/

/-- The symmetric quadratic Psi in wall coordinates (p,q). -/
def Psi (a b p q : ℤ) : ℤ :=
  54*a*a + 36*a*b + 36*b*b - 72*a - 54*b - 54 +
  9 * (p*p + q*q - 8*p*q - (2*a+4*b+5)*(p+q))

/-- Psi is symmetric in (p,q). -/
theorem Psi_swap (a b p q : ℤ) : Psi a b p q = Psi a b q p := by
  unfold Psi; ring

/-- The root-pair involution for fixed p. -/
def qInv (a b p q : ℤ) : ℤ := 8*p + (2*a + 4*b + 5) - q

/-- qInv is an involution. -/
theorem qInv_invol (a b p q : ℤ) : qInv a b p (qInv a b p q) = q := by
  unfold qInv; ring

/-- qInv preserves Psi at fixed p. -/
theorem qInv_preserves_Psi (a b p q : ℤ) : Psi a b p (qInv a b p q) = Psi a b p q := by
  unfold Psi qInv; ring

/-- qInv has NO integer fixed point (L = 2a+4b+5 is always odd). -/
theorem qInv_no_fix (a b p q : ℤ) : qInv a b p q ≠ q := by
  unfold qInv; omega

/-- qInv flips the parity of p+q. -/
theorem qInv_flips_parity (a b p q : ℤ) : (p + qInv a b p q) % 2 ≠ (p + q) % 2 := by
  unfold qInv; omega

/-- The wall-coordinate change: p = U+V-a-1, q = -U-a. -/
def pCoord (a U V : ℤ) : ℤ := U + V - a - 1
def qCoord (a U : ℤ) : ℤ := -U - a

/-- Inverse: U = -a-q, V = p+q+2a+1. -/
def UOf (a q : ℤ) : ℤ := -a - q
def VOf (a p q : ℤ) : ℤ := p + q + 2*a + 1

/-- The coordinate change is invertible. -/
theorem coord_inverse_U (a p q : ℤ) : qCoord a (UOf a q) = q := by unfold qCoord UOf; ring
theorem coord_inverse_V (a p q : ℤ) : pCoord a (UOf a q) (VOf a p q) = p := by
  unfold pCoord UOf VOf; ring

/-! ## Parity-parametrised qInv core

The four `(x,y)` parity sectors have the same root-pair mechanism, but the
linear constant in the symmetric quadratic is
`L = 2a + 4b + 5 + 2η - 2ε`.  The original `qInv` above is the `L = 2a+4b+5`
special case.
-/

/-- The symmetric part of the wall-coordinate quadratic, with arbitrary odd linear constant. -/
def PsiCore (L p q : ℤ) : ℤ := p * p + q * q - 8 * p * q - L * (p + q)

/-- Root-pair involution for the quadratic `PsiCore L p q`, with `p` fixed. -/
def qInvL (L p q : ℤ) : ℤ := 8 * p + L - q

theorem PsiCore_swap (L p q : ℤ) : PsiCore L p q = PsiCore L q p := by
  unfold PsiCore
  ring

theorem qInvL_invol (L p q : ℤ) : qInvL L p (qInvL L p q) = q := by
  unfold qInvL
  ring

theorem qInvL_preserves_PsiCore (L p q : ℤ) :
    PsiCore L p (qInvL L p q) = PsiCore L p q := by
  unfold PsiCore qInvL
  ring

theorem qInvL_no_fix {L p q : ℤ} (hL : Odd L) : qInvL L p q ≠ q := by
  intro h
  rcases hL with ⟨n, hn⟩
  unfold qInvL at h
  omega

theorem qInvL_negOnePow {L p q : ℤ} (hL : Odd L) :
    negOnePowIntQ (p + qInvL L p q) = -negOnePowIntQ (p + q) := by
  have hodd : Odd ((p + qInvL L p q) - (p + q)) := by
    rcases hL with ⟨n, hn⟩
    refine ⟨4 * p + n - q, ?_⟩
    unfold qInvL
    omega
  simpa using
    (negOnePowIntQ_eq_neg_of_odd_sub (m := p + qInvL L p q) (n := p + q) hodd)

/-- At fixed `p`, the two `q`-roots of `PsiCore` cancel by the odd `qInvL` involution. -/
theorem qInvL_inner_const_sum_zero (L E p : ℤ) (C : ℚ) (hL : Odd L) :
    (∑ᶠ q : ℤ,
      C * negOnePowIntQ (p + q) *
        (if E = PsiCore L p q then (1 : ℚ) else 0)) = 0 := by
  classical
  let f : ℤ → ℚ := fun q =>
    C * negOnePowIntQ (p + q) *
      (if E = PsiCore L p q then (1 : ℚ) else 0)
  let e : ℤ ≃ ℤ :=
    { toFun := fun q => qInvL L p q
      invFun := fun q => qInvL L p q
      left_inv := by intro q; exact qInvL_invol L p q
      right_inv := by intro q; exact qInvL_invol L p q }
  have hanti : ∀ q, f (e q) = -f q := by
    intro q
    dsimp [f, e]
    rw [qInvL_negOnePow (p := p) (q := q) hL, qInvL_preserves_PsiCore]
    ring
  calc
    (∑ᶠ q : ℤ, C * negOnePowIntQ (p + q) *
        (if E = PsiCore L p q then (1 : ℚ) else 0))
        = ∑ᶠ q : ℤ, f q := rfl
    _ = ∑ᶠ q : ℤ, f (e q) := (finsum_comp_equiv e).symm
    _ = ∑ᶠ q : ℤ, -f q := by
          apply finsum_congr
          intro q
          exact hanti q
    _ = -(∑ᶠ q : ℤ, f q) := by rw [finsum_neg_distrib]
    _ = 0 := by
          have h : (∑ᶠ q : ℤ, f q) = -(∑ᶠ q : ℤ, f q) := by
            calc
              (∑ᶠ q : ℤ, f q)
                  = ∑ᶠ q : ℤ, f (e q) := (finsum_comp_equiv e).symm
              _ = ∑ᶠ q : ℤ, -f q := by
                    apply finsum_congr
                    intro q
                    exact hanti q
              _ = -(∑ᶠ q : ℤ, f q) := by rw [finsum_neg_distrib]
          linarith

/-- The fixed-`p` qInv cancellation after multiplying by any outer weight `G p`. -/
theorem qInvL_weighted_p_sum_zero (L E : ℤ) (G : ℤ → ℚ) (hL : Odd L) :
    (∑ᶠ p : ℤ, ∑ᶠ q : ℤ,
      G p * negOnePowIntQ (p + q) *
        (if E = PsiCore L p q then (1 : ℚ) else 0)) = 0 := by
  apply finsum_eq_zero_of_forall_eq_zero
  intro p
  exact qInvL_inner_const_sum_zero L E p (G p) hL

/-! ## Parity-shifted off-diagonal cancellation data -/

/-- The Appell two-row bracket in the sector `y = 2b + eta`.
For `eta = 0` this is `R0/R2 + R1`; for `eta = 1` it is `R0/R2 + R3`. -/
def AppellBracketEta (eta a b U V : ℤ) : ℤ :=
  sg (U + V - a - 1) (a - V) + sg (U - b - eta - 1) (V + b)

/-- The parity-shifted pair defect under `U ↦ 1-U-V`. -/
theorem AppellBracketEta_pair_defect (eta a b U V : ℤ) :
    ((AppellBracketEta eta a b U V +
      AppellBracketEta eta a b (1 - U - V) V -
      2 * uvOmegaBracket a b V : ℤ) : ℚ) =
      (zsgn (pCoord a U V) + zsgn (qCoord a U) +
        zsgn (-(a + b + eta + 1) - qCoord a U) +
        zsgn (-(a + b + eta + 1) - pCoord a U V)) / 2 := by
  unfold AppellBracketEta uvOmegaBracket pCoord qCoord
  simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  rw [sg_eq_zsgn, sg_eq_zsgn, sg_eq_zsgn, sg_eq_zsgn, sg_eq_zsgn]
  ring

/-- The constant term of `heckePhi` after the wall-coordinate change. -/
def PhiPQConst (a b eps eta : ℤ) : ℤ :=
  heckePhi (2 * a + eps) (2 * b + eta) (UOf a 0) (VOf a 0 0) -
    9 * PsiCore (2 * a + 4 * b + 5 + 2 * eta - 2 * eps) 0 0

/-- In wall coordinates, every parity sector has the same symmetric quadratic core. -/
theorem heckePhi_wall_coords (a b eps eta p q : ℤ) :
    heckePhi (2 * a + eps) (2 * b + eta) (UOf a q) (VOf a p q) =
      PhiPQConst a b eps eta +
        9 * PsiCore (2 * a + 4 * b + 5 + 2 * eta - 2 * eps) p q := by
  unfold PhiPQConst heckePhi UOf VOf PsiCore FhmExp BYExp BXExp
  ring

/-- `L = 2a+4b+5+2eta-2eps` is odd in all four parity sectors. -/
theorem parity_L_odd (a b eps eta : ℤ) :
    Odd (2 * a + 4 * b + 5 + 2 * eta - 2 * eps) := by
  refine ⟨a + 2 * b + eta - eps + 2, ?_⟩
  ring

/-- Fixed-`p` qInv cancellation on an affine `PsiCore` fiber. -/
theorem qInvL_inner_const_sum_zero_affine (L E C p : ℤ) (A : ℤ) (W : ℚ) (hL : Odd L) :
    (∑ᶠ q : ℤ,
      W * negOnePowIntQ (p + q) *
        (if E = C + A * PsiCore L p q then (1 : ℚ) else 0)) = 0 := by
  classical
  let f : ℤ → ℚ := fun q =>
    W * negOnePowIntQ (p + q) *
      (if E = C + A * PsiCore L p q then (1 : ℚ) else 0)
  let e : ℤ ≃ ℤ :=
    { toFun := fun q => qInvL L p q
      invFun := fun q => qInvL L p q
      left_inv := by intro q; exact qInvL_invol L p q
      right_inv := by intro q; exact qInvL_invol L p q }
  have hanti : ∀ q, f (e q) = -f q := by
    intro q
    dsimp [f, e]
    rw [qInvL_negOnePow (p := p) (q := q) hL, qInvL_preserves_PsiCore]
    ring
  calc
    (∑ᶠ q : ℤ,
      W * negOnePowIntQ (p + q) *
        (if E = C + A * PsiCore L p q then (1 : ℚ) else 0))
        = ∑ᶠ q : ℤ, f q := rfl
    _ = ∑ᶠ q : ℤ, f (e q) := (finsum_comp_equiv e).symm
    _ = ∑ᶠ q : ℤ, -f q := by
          apply finsum_congr
          intro q
          exact hanti q
    _ = -(∑ᶠ q : ℤ, f q) := by rw [finsum_neg_distrib]
    _ = 0 := by
          have h : (∑ᶠ q : ℤ, f q) = -(∑ᶠ q : ℤ, f q) := by
            calc
              (∑ᶠ q : ℤ, f q)
                  = ∑ᶠ q : ℤ, f (e q) := (finsum_comp_equiv e).symm
              _ = ∑ᶠ q : ℤ, -f q := by
                    apply finsum_congr
                    intro q
                    exact hanti q
              _ = -(∑ᶠ q : ℤ, f q) := by rw [finsum_neg_distrib]
          linarith

theorem qInvL_weighted_p_sum_zero_affine (L E C A : ℤ) (G : ℤ → ℚ) (hL : Odd L) :
    (∑ᶠ p : ℤ, ∑ᶠ q : ℤ,
      G p * negOnePowIntQ (p + q) *
        (if E = C + A * PsiCore L p q then (1 : ℚ) else 0)) = 0 := by
  apply finsum_eq_zero_of_forall_eq_zero
  intro p
  exact qInvL_inner_const_sum_zero_affine L E C p A (G p) hL

/-- If two fixed-`p` points lie on the same `PsiCore` fiber, they are the two qInv roots. -/
theorem PsiCore_fixed_left_eq_or_qInv (L p q q₀ : ℤ)
    (h : PsiCore L p q = PsiCore L p q₀) :
    q = q₀ ∨ q = qInvL L p q₀ := by
  have hmul : (q - q₀) * (q + q₀ - (8 * p + L)) = 0 := by
    have hdiff : PsiCore L p q - PsiCore L p q₀ =
        (q - q₀) * (q + q₀ - (8 * p + L)) := by
      unfold PsiCore
      ring
    rw [← hdiff, h]
    ring
  rcases mul_eq_zero.mp hmul with hq | hsum
  · left
    omega
  · right
    unfold qInvL
    omega

/-- If two fixed-`q` points lie on the same `PsiCore` fiber, they are the two qInv roots. -/
theorem PsiCore_fixed_right_eq_or_qInv (L p p₀ q : ℤ)
    (h : PsiCore L p q = PsiCore L p₀ q) :
    p = p₀ ∨ p = qInvL L q p₀ := by
  have h' : PsiCore L q p = PsiCore L q p₀ := by
    rw [← PsiCore_swap L p q, ← PsiCore_swap L p₀ q]
    exact h
  exact PsiCore_fixed_left_eq_or_qInv L q p p₀ h'

/-- A fixed-`p` affine `PsiCore` fiber has finite q-support. -/
theorem affine_PsiCore_fixed_left_finite (L E C A p : ℤ) (hA : A ≠ 0) :
    ({q : ℤ | E = C + A * PsiCore L p q}).Finite := by
  classical
  by_cases hroot : ∃ q₀ : ℤ, E = C + A * PsiCore L p q₀
  · rcases hroot with ⟨q₀, hq₀⟩
    refine Set.Finite.subset
      ((Set.finite_singleton q₀).union (Set.finite_singleton (qInvL L p q₀))) ?_
    intro q hq
    simp only [Set.mem_setOf_eq] at hq
    simp only [Set.mem_union, Set.mem_singleton_iff]
    have hsame : PsiCore L p q = PsiCore L p q₀ := by
      have hmul : A * PsiCore L p q = A * PsiCore L p q₀ := by
        have hsum : C + A * PsiCore L p q = C + A * PsiCore L p q₀ := by
          rw [← hq, ← hq₀]
        omega
      exact Int.eq_of_mul_eq_mul_left hA hmul
    exact PsiCore_fixed_left_eq_or_qInv L p q q₀ hsame
  · refine Set.Finite.subset (Set.finite_singleton (0 : ℤ)) ?_
    intro q hq
    simp only [Set.mem_setOf_eq] at hq
    exact False.elim (hroot ⟨q, hq⟩)

/-- A fixed-`q` affine `PsiCore` fiber has finite p-support. -/
theorem affine_PsiCore_fixed_right_finite (L E C A q : ℤ) (hA : A ≠ 0) :
    ({p : ℤ | E = C + A * PsiCore L p q}).Finite := by
  classical
  by_cases hroot : ∃ p₀ : ℤ, E = C + A * PsiCore L p₀ q
  · rcases hroot with ⟨p₀, hp₀⟩
    refine Set.Finite.subset
      ((Set.finite_singleton p₀).union (Set.finite_singleton (qInvL L q p₀))) ?_
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    simp only [Set.mem_union, Set.mem_singleton_iff]
    have hsame : PsiCore L p q = PsiCore L p₀ q := by
      have hmul : A * PsiCore L p q = A * PsiCore L p₀ q := by
        have hsum : C + A * PsiCore L p q = C + A * PsiCore L p₀ q := by
          rw [← hp, ← hp₀]
        omega
      exact Int.eq_of_mul_eq_mul_left hA hmul
    exact PsiCore_fixed_right_eq_or_qInv L p p₀ q hsame
  · refine Set.Finite.subset (Set.finite_singleton (0 : ℤ)) ?_
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    exact False.elim (hroot ⟨p, hp⟩)

/-- Product-form qInv cancellation with the second coordinate fixed. -/
theorem qInvL_weighted_second_prod_sum_zero_affine
    (L E C A : ℤ) (G : ℤ → ℚ) (hL : Odd L) :
    (∑ᶠ pq : ℤ × ℤ,
      G pq.2 * negOnePowIntQ (pq.1 + pq.2) *
        (if E = C + A * PsiCore L pq.1 pq.2 then (1 : ℚ) else 0)) = 0 := by
  classical
  let f : ℤ × ℤ → ℚ := fun pq =>
    G pq.2 * negOnePowIntQ (pq.1 + pq.2) *
      (if E = C + A * PsiCore L pq.1 pq.2 then (1 : ℚ) else 0)
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun pq => (qInvL L pq.2 pq.1, pq.2)
      invFun := fun pq => (qInvL L pq.2 pq.1, pq.2)
      left_inv := by
        intro pq
        rcases pq with ⟨p, q⟩
        simp [qInvL_invol]
      right_inv := by
        intro pq
        rcases pq with ⟨p, q⟩
        simp [qInvL_invol] }
  have hpres (p q : ℤ) :
      PsiCore L (qInvL L q p) q = PsiCore L p q := by
    calc
      PsiCore L (qInvL L q p) q = PsiCore L q (qInvL L q p) := PsiCore_swap L _ _
      _ = PsiCore L q p := qInvL_preserves_PsiCore L q p
      _ = PsiCore L p q := (PsiCore_swap L p q).symm
  have hanti : ∀ pq, f (e pq) = -f pq := by
    intro pq
    rcases pq with ⟨p, q⟩
    dsimp [f, e]
    have hsign : negOnePowIntQ (qInvL L q p + q) = -negOnePowIntQ (p + q) := by
      simpa [add_comm] using qInvL_negOnePow (L := L) (p := q) (q := p) hL
    rw [hsign, hpres]
    ring
  calc
    (∑ᶠ pq : ℤ × ℤ,
      G pq.2 * negOnePowIntQ (pq.1 + pq.2) *
        (if E = C + A * PsiCore L pq.1 pq.2 then (1 : ℚ) else 0))
        = ∑ᶠ pq : ℤ × ℤ, f pq := rfl
    _ = ∑ᶠ pq : ℤ × ℤ, f (e pq) := (finsum_comp_equiv e).symm
    _ = ∑ᶠ pq : ℤ × ℤ, -f pq := by
          apply finsum_congr
          intro pq
          exact hanti pq
    _ = -(∑ᶠ pq : ℤ × ℤ, f pq) := by rw [finsum_neg_distrib]
    _ = 0 := by
          have h : (∑ᶠ pq : ℤ × ℤ, f pq) = -(∑ᶠ pq : ℤ × ℤ, f pq) := by
            calc
              (∑ᶠ pq : ℤ × ℤ, f pq)
                  = ∑ᶠ pq : ℤ × ℤ, f (e pq) := (finsum_comp_equiv e).symm
              _ = ∑ᶠ pq : ℤ × ℤ, -f pq := by
                    apply finsum_congr
                    intro pq
                    exact hanti pq
              _ = -(∑ᶠ pq : ℤ × ℤ, f pq) := by rw [finsum_neg_distrib]
          linarith

/-! ## Final assembly: Fhm = Ghat 1

The proof chain:
  Mhat = Ghat * BY * BX (Mhat_eq_Ghat_mul_BYBX)
  → clearedD = (Fhm - Ghat) * BY * BX
  → clearedD = 0 iff Fhm = Ghat (by NoZeroDivisors + BYBX_ne_zero)
  → Fhm = Ghat via Fhm_eq_Ghat_of_clearedD_zero

The final coefficient identity is proved in `Chapter10_M3_AppellCoeffNF` by
finsum reindexing: parity split, signed strip coordinates, and qInv cancellation.
The theorem below records the reusable final implication. -/

/-- The main theorem, conditional on the coefficient identity.
Together with `coeffQXY_Ppair_boundary_uvOmega`, this gives
`Fhm = Ghat 1` immediately. -/
theorem Fhm_eq_Ghat_main
    (hcoeff :
      PpairY * ghatBoundary 1 MhatRow.R1 + PpairX * ghatBoundary 1 MhatRow.R0 =
      Fhm * ghatBoundary 1 MhatRow.R0 * ghatBoundary 1 MhatRow.R1) :
    Fhm = Ghat 1 := by
  apply Fhm_eq_Ghat_of_clearedD_zero
  rw [hcoeff]; ring

end

end QseriesFormalization.Pending.Ch10M3DiagClose
