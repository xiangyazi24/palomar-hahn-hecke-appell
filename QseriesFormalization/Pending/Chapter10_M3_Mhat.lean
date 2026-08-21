import QseriesFormalization.Pending.Chapter10_TwoVar
import QseriesFormalization.Pending.Chapter10_M3_Fhat

/-!
# The M3 formal m-table object `Mhat`

This file records the affine four-row data for the formal `(X,Y)` lift of the
HM m-table and starts the genuine four-index Hahn-family construction of the
cleared m-table side.
-/

open scoped Classical
open Set

namespace QseriesFormalization
namespace Pending
namespace Ch10M3Mhat

open QseriesFormalization.Ch10TwoVar
open QseriesFormalization.Pending.Ch10HM

noncomputable section

/-! ## Affine row data for the formal lift -/

/-- An affine exponent `c₀ + c₁ X + c₂ Y`, lifted as `Q^c₀ x^c₁ y^c₂`. -/
structure AffineXY where
  c0 : ℤ
  cX : ℤ
  cY : ℤ
deriving DecidableEq, Repr

namespace AffineXY

def eval (u : AffineXY) (X Y : ℤ) : ℤ :=
  u.c0 + u.cX * X + u.cY * Y

def add (u v : AffineXY) : AffineXY :=
  ⟨u.c0 + v.c0, u.cX + v.cX, u.cY + v.cY⟩

def neg (u : AffineXY) : AffineXY :=
  ⟨-u.c0, -u.cX, -u.cY⟩

def smul (n : ℤ) (u : AffineXY) : AffineXY :=
  ⟨n * u.c0, n * u.cX, n * u.cY⟩

def toMonom (u : AffineXY) : S :=
  monom u.c0 u.cX u.cY 1

@[simp] theorem eval_add (u v : AffineXY) (X Y : ℤ) :
    (u.add v).eval X Y = u.eval X Y + v.eval X Y := by
  unfold eval add
  ring

@[simp] theorem eval_neg (u : AffineXY) (X Y : ℤ) :
    u.neg.eval X Y = -u.eval X Y := by
  unfold eval neg
  ring

@[simp] theorem eval_smul (n : ℤ) (u : AffineXY) (X Y : ℤ) :
    (u.smul n).eval X Y = n * u.eval X Y := by
  unfold eval smul
  ring

end AffineXY

/-- The four generic rows of the HM m-table. -/
inductive MhatRow
  | R0
  | R1
  | R2
  | R3
deriving DecidableEq, Repr, Fintype

namespace MhatRow

def lead : MhatRow → AffineXY
  | R0 => ⟨0, 0, 0⟩
  | R1 => ⟨0, 0, 0⟩
  | R2 => ⟨-9, 1, -1⟩
  | R3 => ⟨-9, -1, 1⟩

def jArg : MhatRow → AffineXY
  | R0 => ⟨0, 0, 1⟩
  | R1 => ⟨0, 1, 0⟩
  | R2 => ⟨9, 0, 1⟩
  | R3 => ⟨9, 1, 0⟩

def mArg : MhatRow → AffineXY
  | R0 => ⟨54, 2, -3⟩
  | R1 => ⟨54, -3, 2⟩
  | R2 => ⟨9, 2, -3⟩
  | R3 => ⟨9, -3, 2⟩

def mZ (ell : ℤ) : MhatRow → AffineXY
  | R0 => ⟨18 * ell, -2, 2⟩
  | R1 => ⟨-18 * ell, 2, -2⟩
  | R2 => ⟨18 * ell, -2, 2⟩
  | R3 => ⟨-18 * ell, 2, -2⟩

end MhatRow

/-- Lexicographic positivity for lifted denominator exponents. -/
def AffineXY.lexPositive (u : AffineXY) : Prop :=
  0 < u.c0 ∨ u.c0 = 0 ∧ (0 < u.cX ∨ u.cX = 0 ∧ 0 < u.cY)

instance (u : AffineXY) : Decidable u.lexPositive := by
  unfold AffineXY.lexPositive
  infer_instance

/-- The lifted `j(Q^jArg; Q^18)` exponent for index `k`. -/
def mhatJThetaExp (row : MhatRow) (k : ℤ) : AffineXY :=
  let j := row.jArg
  ⟨9 * k * (k - 1) + j.c0 * k, j.cX * k, j.cY * k⟩

/-- The lifted Appell numerator exponent for index `r`. -/
def mhatAppellNumeratorExp (ell : ℤ) (row : MhatRow) (r : ℤ) : AffineXY :=
  let z := row.mZ ell
  ⟨45 * r * (r - 1) + z.c0 * r, z.cX * r, z.cY * r⟩

/-- The lifted denominator monomial `90(r-1)+mArg+mZ`. -/
def mhatDenomExp (ell : ℤ) (row : MhatRow) (r : ℤ) : AffineXY :=
  let a := row.mArg
  let z := row.mZ ell
  ⟨90 * (r - 1) + a.c0 + z.c0, a.cX + z.cX, a.cY + z.cY⟩

/-- The exponent contributed by the geometric branch at strip index `t`. -/
def mhatDenomBranchExp (ell : ℤ) (row : MhatRow) (r t : ℤ) : AffineXY :=
  let d := mhatDenomExp ell row r
  if d.lexPositive then d.smul t else d.smul (-t)

/-- The coefficient contributed by the geometric branch at strip index `t`. -/
def mhatDenomBranchCoeff (ell : ℤ) (row : MhatRow) (r t : ℤ) : ℚ :=
  let d := mhatDenomExp ell row r
  if d.lexPositive then
    if 0 ≤ t then 1 else 0
  else
    if 1 ≤ t then -1 else 0

/-- The lifted `j(Q^(-mZ); Q^90)` exponent for index `m`. -/
def mhatDThetaExp (ell : ℤ) (row : MhatRow) (m : ℤ) : AffineXY :=
  let z := (row.mZ ell).neg
  ⟨45 * m * (m - 1) + z.c0 * m, z.cX * m, z.cY * m⟩

/-- Raw four-index exponent for one row of the intended formal m-table lift. -/
def mhatRawExp (ell : ℤ) (row : MhatRow) (k r t m : ℤ) : AffineXY :=
  (((row.lead.add (mhatJThetaExp row k)).add
      (mhatAppellNumeratorExp ell row r)).add
        (mhatDenomBranchExp ell row r t)).add
          (mhatDThetaExp ell row m)

/-- Raw four-index coefficient for one row of the intended formal m-table lift. -/
def mhatRawCoeff (ell : ℤ) (row : MhatRow) (k r t m : ℤ) : ℚ :=
  QseriesFormalization.Pending.Ch10HM.negOnePowIntQ (k + r + m) *
    mhatDenomBranchCoeff ell row r t

/-- Raw four-index monomial for one row of the intended formal m-table lift. -/
def mhatRawTerm (ell : ℤ) (row : MhatRow) (k r t m : ℤ) : S :=
  let e := mhatRawExp ell row k r t m
  monom e.c0 e.cX e.cY (mhatRawCoeff ell row k r t m)

/-!
## Stage-0 numeric pin

The affine row data above was checked by a standalone Python integer script on
2026-06-11.  For the nine documented HM pieces
`(ell,X,Y) = (1,18,18), (1,27,24), (2,36,30), (2,24,27), (1,33,33),
(1,42,39), (1,30,36), (1,39,42), (1,48,48)`, evaluating
`lead/jArg/mArg/mZ` gives exactly `Ch10HM.hmF232Terms ell X Y` row-by-row.
The same script checked all sampled points
`k,r,m ∈ [-2,2]`, `t ∈ [0,3]` for the theta/numerator/D-theta affine
exponent formulas against the one-variable `jExp`/`appellNumeratorExp`
formulas.  The formal lexicographic geometric branch is intentionally kept as
the Hahn-series branch; proving its global PWO support is the remaining
load-bearing obligation below.
-/

/-! ## Genuine factor families -/

/-- A two-variable theta family with the HM parity sign `negOnePowIntQ`. -/
noncomputable def mhatThetaFamily (A e i j : ℤ) (hA : 0 < A) :
    HahnSeries.SummableFamily ExpQXY ℚ ℤ where
  toFun n := monom (thetaQDeg A e n) (i * n) (j * n) (negOnePowIntQ n)
  isPWO_iUnion_support' := by
    refine (thetaExp_range_isPWO A e i j hA).mono (Set.iUnion_subset (fun n => ?_))
    intro g hg
    refine ⟨n, ?_⟩
    have : g = expQXY (thetaQDeg A e n) (i * n) (j * n) :=
      HahnSeries.support_single_subset hg
    rw [this]
    rfl
  finite_co_support' := by
    intro g
    apply Set.Finite.subset (thetaExp_finite_fiber A e i j hA g)
    intro n hn
    simp only [Set.mem_setOf_eq] at hn ⊢
    by_contra hne
    apply hn
    unfold monom
    rw [HahnSeries.coeff_single_of_ne]
    intro hcon
    apply hne
    rw [hcon]
    rfl

/-- The lifted `j(Q^jArg;Q^18)` factor for one row. -/
noncomputable def mhatJThetaFamily (row : MhatRow) :
    HahnSeries.SummableFamily ExpQXY ℚ ℤ :=
  mhatThetaFamily 18 row.jArg.c0 row.jArg.cX row.jArg.cY (by norm_num)

/-- The lifted `j(Q^(-mZ);Q^90)` factor for one row. -/
noncomputable def mhatDThetaFamily (ell : ℤ) (row : MhatRow) :
    HahnSeries.SummableFamily ExpQXY ℚ ℤ :=
  let z := (row.mZ ell).neg
  mhatThetaFamily 90 z.c0 z.cX z.cY (by norm_num)

/-- The affine exponent of the Appell `(r,t)` strip factor. -/
def mhatAppellStripExp (ell : ℤ) (row : MhatRow) (r t : ℤ) : AffineXY :=
  (mhatAppellNumeratorExp ell row r).add (mhatDenomBranchExp ell row r t)

/-- The coefficient of the Appell `(r,t)` strip factor. -/
def mhatAppellStripCoeff (ell : ℤ) (row : MhatRow) (r t : ℤ) : ℚ :=
  negOnePowIntQ r * mhatDenomBranchCoeff ell row r t

/-- One Appell `(r,t)` strip monomial in the two-variable Hahn ring. -/
noncomputable def mhatAppellStripTerm (ell : ℤ) (row : MhatRow) (r t : ℤ) : S :=
  let e := mhatAppellStripExp ell row r t
  monom e.c0 e.cX e.cY (mhatAppellStripCoeff ell row r t)

theorem mhatDenomExp_ne_zero (ell : ℤ) (row : MhatRow) (r : ℤ) :
    mhatDenomExp ell row r ≠ ⟨0, 0, 0⟩ := by
  cases row <;>
    unfold mhatDenomExp MhatRow.mArg MhatRow.mZ <;>
    simp

theorem mhatDenomBranchCoeff_t_nonneg_of_ne_zero {ell : ℤ} {row : MhatRow}
    {r t : ℤ} (h : mhatDenomBranchCoeff ell row r t ≠ 0) :
    0 ≤ t := by
  unfold mhatDenomBranchCoeff at h
  by_cases hp : (mhatDenomExp ell row r).lexPositive
  · simp [hp] at h
    by_contra ht
    have htn : ¬ 0 ≤ t := by omega
    simp [htn] at h
  · simp [hp] at h
    by_contra ht
    have htn : ¬ 1 ≤ t := by omega
    simp [htn] at h

theorem mhatAppellStripCoeff_t_nonneg_of_ne_zero {ell : ℤ} {row : MhatRow}
    {r t : ℤ} (h : mhatAppellStripCoeff ell row r t ≠ 0) :
    0 ≤ t := by
  apply mhatDenomBranchCoeff_t_nonneg_of_ne_zero (ell := ell) (row := row) (r := r)
  intro hb
  unfold mhatAppellStripCoeff at h
  rw [hb, mul_zero] at h
  exact h rfl

theorem thetaQDeg_90 (e r : ℤ) :
    thetaQDeg 90 e r = 45 * r * (r - 1) + e * r := by
  unfold thetaQDeg
  have h2 := two_mul_Tn r
  have hT : 90 * Tn r = 45 * r * (r - 1) := by
    nlinarith
  rw [hT]

def thetaQDeg90LeBound (e N : ℤ) : ℤ :=
  (720 * N + (2 * e - 90) ^ 2) + (2 * e - 90) ^ 2 + 2

theorem thetaQDeg90_le_bound {e r N : ℤ} (hle : thetaQDeg 90 e r ≤ N) :
    -thetaQDeg90LeBound e N ≤ r ∧ r ≤ thetaQDeg90LeBound e N := by
  unfold thetaQDeg90LeBound
  have h2 := two_mul_Tn r
  have hid : 720 * (thetaQDeg 90 e r) =
      (180 * r + (2 * e - 90)) ^ 2 - (2 * e - 90) ^ 2 := by
    unfold thetaQDeg
    have : 2 * (90 * Tn r) = 90 * (r * (r - 1)) := by
      rw [← h2]
      ring
    nlinarith
  set M : ℤ := 720 * N + (2 * e - 90) ^ 2 with hM
  set c : ℤ := 2 * e - 90 with hc
  have hsq_le : (180 * r + c) ^ 2 ≤ M := by
    rw [hM, hc]
    nlinarith [hid, hle]
  have hMnonneg : 0 ≤ M := by
    nlinarith [hsq_le, sq_nonneg (180 * r + c)]
  have hub : 180 * r + c ≤ M + 1 := by
    nlinarith [hsq_le, sq_nonneg (180 * r + c - 1)]
  have hlb : -(M + 1) ≤ 180 * r + c := by
    nlinarith [hsq_le, sq_nonneg (180 * r + c + 1)]
  have hc_le : -c ≤ c ^ 2 + 1 ∧ c ≤ c ^ 2 + 1 := by
    constructor <;> nlinarith [sq_nonneg (c - 1), sq_nonneg (c + 1)]
  constructor
  · rcases le_or_gt 0 r with hr0 | hr0
    · nlinarith [hMnonneg, sq_nonneg c, hr0]
    · have hmul : 180 * r ≤ r := by nlinarith [hr0]
      nlinarith [hlb, hmul, hc_le.2, hMnonneg, sq_nonneg c]
  · rcases le_or_gt 0 r with hr0 | hr0
    · have hmul : r ≤ 180 * r := by nlinarith [hr0]
      nlinarith [hub, hmul, hc_le.1, hMnonneg, sq_nonneg c]
    · nlinarith [hMnonneg, sq_nonneg c, hr0]

theorem mhatAppellNumeratorExp_c0_eq_theta (ell : ℤ) (row : MhatRow) (r : ℤ) :
    (mhatAppellNumeratorExp ell row r).c0 = thetaQDeg 90 (row.mZ ell).c0 r := by
  rw [thetaQDeg_90]
  unfold mhatAppellNumeratorExp
  simp

theorem mhatDenomExp_lexPositive_c0_pos {ell : ℤ} {row : MhatRow} {r : ℤ}
    (hp : (mhatDenomExp ell row r).lexPositive) :
    0 < (mhatDenomExp ell row r).c0 := by
  cases row <;>
    simpa [mhatDenomExp, MhatRow.mArg, MhatRow.mZ, AffineXY.lexPositive] using hp

theorem mhatDenomBranchExp_c0_nonneg_of_branchCoeff_ne_zero {ell : ℤ} {row : MhatRow}
    {r t : ℤ} (h : mhatDenomBranchCoeff ell row r t ≠ 0) :
    0 ≤ (mhatDenomBranchExp ell row r t).c0 := by
  unfold mhatDenomBranchExp
  by_cases hp : (mhatDenomExp ell row r).lexPositive
  · have ht : 0 ≤ t := mhatDenomBranchCoeff_t_nonneg_of_ne_zero h
    have hd : 0 ≤ (mhatDenomExp ell row r).c0 :=
      le_of_lt (mhatDenomExp_lexPositive_c0_pos hp)
    simp [hp, AffineXY.smul]
    exact mul_nonneg ht hd
  · have ht : 0 ≤ t := mhatDenomBranchCoeff_t_nonneg_of_ne_zero h
    have hd : (mhatDenomExp ell row r).c0 ≤ 0 := by
      unfold AffineXY.lexPositive at hp
      by_contra hlt
      have hpos : 0 < (mhatDenomExp ell row r).c0 := by omega
      exact hp (Or.inl hpos)
    simp [hp, AffineXY.smul]
    have hprod : 0 ≤ (-t) * (mhatDenomExp ell row r).c0 :=
      mul_nonneg_of_nonpos_of_nonpos (by omega) hd
    nlinarith

theorem mhatAppellStripExp_c0_ge_num {ell : ℤ} {row : MhatRow} {r t : ℤ}
    (h : mhatAppellStripCoeff ell row r t ≠ 0) :
    (mhatAppellNumeratorExp ell row r).c0 ≤ (mhatAppellStripExp ell row r t).c0 := by
  have hb : mhatDenomBranchCoeff ell row r t ≠ 0 := by
    intro hz
    unfold mhatAppellStripCoeff at h
    rw [hz, mul_zero] at h
    exact h rfl
  have hnonneg := mhatDenomBranchExp_c0_nonneg_of_branchCoeff_ne_zero hb
  simpa [mhatAppellStripExp, AffineXY.add] using hnonneg

theorem mhatAppellStripExp_c0_ge_theta {ell : ℤ} {row : MhatRow} {r t : ℤ}
    (h : mhatAppellStripCoeff ell row r t ≠ 0) :
    thetaQDeg 90 (row.mZ ell).c0 r ≤ (mhatAppellStripExp ell row r t).c0 := by
  calc
    thetaQDeg 90 (row.mZ ell).c0 r = (mhatAppellNumeratorExp ell row r).c0 := by
      rw [mhatAppellNumeratorExp_c0_eq_theta]
    _ ≤ (mhatAppellStripExp ell row r t).c0 := mhatAppellStripExp_c0_ge_num h

theorem mhatAppellStripExp_c0_of_lexPositive {ell : ℤ} {row : MhatRow} {r t : ℤ}
    (hp : (mhatDenomExp ell row r).lexPositive) :
    (mhatAppellStripExp ell row r t).c0 =
      (mhatAppellNumeratorExp ell row r).c0 + t * (mhatDenomExp ell row r).c0 := by
  simp [mhatAppellStripExp, mhatDenomBranchExp, hp, AffineXY.add, AffineXY.smul]

theorem mhatAppell_t_le_of_lexPositive {ell : ℤ} {row : MhatRow} {r t N B : ℤ}
    (hN : N = (mhatAppellStripExp ell row r t).c0)
    (hcoeff : mhatAppellStripCoeff ell row r t ≠ 0)
    (hp : (mhatDenomExp ell row r).lexPositive)
    (hB : B ≤ thetaQDeg 90 (row.mZ ell).c0 r) :
    t ≤ N - B := by
  have ht : 0 ≤ t := mhatAppellStripCoeff_t_nonneg_of_ne_zero hcoeff
  have hdpos : 0 < (mhatDenomExp ell row r).c0 := mhatDenomExp_lexPositive_c0_pos hp
  have hdge : 1 ≤ (mhatDenomExp ell row r).c0 := hdpos
  have hnumB : B ≤ (mhatAppellNumeratorExp ell row r).c0 := by
    rwa [mhatAppellNumeratorExp_c0_eq_theta]
  have hN' : N = (mhatAppellNumeratorExp ell row r).c0 +
      t * (mhatDenomExp ell row r).c0 := by
    rw [hN, mhatAppellStripExp_c0_of_lexPositive hp]
  have ht_le_mul : t ≤ t * (mhatDenomExp ell row r).c0 := by
    nlinarith
  nlinarith

theorem expQXY_inj_toLex {N : ℤ} {y : ExpXY} {q x z : ℤ}
    (h : (toLex (N, y) : ExpQXY) = expQXY q x z) :
    N = q ∧ (ofLex y).1 = x ∧ (ofLex y).2 = z := by
  have h' : expQXY N (ofLex y).1 (ofLex y).2 = expQXY q x z := by
    rw [show expQXY N (ofLex y).1 (ofLex y).2 = (toLex (N, y) : ExpQXY) by rfl]
    exact h
  exact expQXY_inj h'

theorem mhatAppellStripExp_R0_cX (ell r t : ℤ) :
    (mhatAppellStripExp ell MhatRow.R0 r t).cX = -2 * r := by
  have hb : (mhatDenomBranchExp ell MhatRow.R0 r t).cX = 0 := by
    simp only [mhatDenomBranchExp]
    split <;> simp [mhatDenomExp, MhatRow.mArg, MhatRow.mZ, AffineXY.smul]
  simp [mhatAppellStripExp, AffineXY.add, mhatAppellNumeratorExp, MhatRow.mZ, hb]

theorem mhatAppellStripExp_R2_cX (ell r t : ℤ) :
    (mhatAppellStripExp ell MhatRow.R2 r t).cX = -2 * r := by
  have hb : (mhatDenomBranchExp ell MhatRow.R2 r t).cX = 0 := by
    simp only [mhatDenomBranchExp]
    split <;> simp [mhatDenomExp, MhatRow.mArg, MhatRow.mZ, AffineXY.smul]
  simp [mhatAppellStripExp, AffineXY.add, mhatAppellNumeratorExp, MhatRow.mZ, hb]

theorem mhatAppellStripExp_R1_cY (ell r t : ℤ) :
    (mhatAppellStripExp ell MhatRow.R1 r t).cY = -2 * r := by
  have hb : (mhatDenomBranchExp ell MhatRow.R1 r t).cY = 0 := by
    simp only [mhatDenomBranchExp]
    split <;> simp [mhatDenomExp, MhatRow.mArg, MhatRow.mZ, AffineXY.smul]
  simp [mhatAppellStripExp, AffineXY.add, mhatAppellNumeratorExp, MhatRow.mZ, hb]

theorem mhatAppellStripExp_R3_cY (ell r t : ℤ) :
    (mhatAppellStripExp ell MhatRow.R3 r t).cY = -2 * r := by
  have hb : (mhatDenomBranchExp ell MhatRow.R3 r t).cY = 0 := by
    simp only [mhatDenomBranchExp]
    split <;> simp [mhatDenomExp, MhatRow.mArg, MhatRow.mZ, AffineXY.smul]
  simp [mhatAppellStripExp, AffineXY.add, mhatAppellNumeratorExp, MhatRow.mZ, hb]

theorem mhatAppellStripExp_R0_cY_of_lexPositive {ell r t : ℤ}
    (hp : (mhatDenomExp ell MhatRow.R0 r).lexPositive) :
    (mhatAppellStripExp ell MhatRow.R0 r t).cY = 2 * r - t := by
  unfold mhatAppellStripExp mhatDenomBranchExp
  rw [if_pos hp]
  simp [AffineXY.add, AffineXY.smul, mhatAppellNumeratorExp, mhatDenomExp,
    MhatRow.mZ, MhatRow.mArg]
  ring

theorem mhatAppellStripExp_R0_cY_of_not_lexPositive {ell r t : ℤ}
    (hn : ¬(mhatDenomExp ell MhatRow.R0 r).lexPositive) :
    (mhatAppellStripExp ell MhatRow.R0 r t).cY = 2 * r + t := by
  unfold mhatAppellStripExp mhatDenomBranchExp
  rw [if_neg hn]
  simp [AffineXY.add, AffineXY.smul, mhatAppellNumeratorExp, mhatDenomExp,
    MhatRow.mZ, MhatRow.mArg]

theorem mhatAppellStripExp_R2_cY_of_lexPositive {ell r t : ℤ}
    (hp : (mhatDenomExp ell MhatRow.R2 r).lexPositive) :
    (mhatAppellStripExp ell MhatRow.R2 r t).cY = 2 * r - t := by
  unfold mhatAppellStripExp mhatDenomBranchExp
  rw [if_pos hp]
  simp [AffineXY.add, AffineXY.smul, mhatAppellNumeratorExp, mhatDenomExp,
    MhatRow.mZ, MhatRow.mArg]
  ring

theorem mhatAppellStripExp_R2_cY_of_not_lexPositive {ell r t : ℤ}
    (hn : ¬(mhatDenomExp ell MhatRow.R2 r).lexPositive) :
    (mhatAppellStripExp ell MhatRow.R2 r t).cY = 2 * r + t := by
  unfold mhatAppellStripExp mhatDenomBranchExp
  rw [if_neg hn]
  simp [AffineXY.add, AffineXY.smul, mhatAppellNumeratorExp, mhatDenomExp,
    MhatRow.mZ, MhatRow.mArg]

theorem mhatAppellStripExp_R1_cX_of_lexPositive {ell r t : ℤ}
    (hp : (mhatDenomExp ell MhatRow.R1 r).lexPositive) :
    (mhatAppellStripExp ell MhatRow.R1 r t).cX = 2 * r - t := by
  unfold mhatAppellStripExp mhatDenomBranchExp
  rw [if_pos hp]
  simp [AffineXY.add, AffineXY.smul, mhatAppellNumeratorExp, mhatDenomExp,
    MhatRow.mZ, MhatRow.mArg]
  ring

theorem mhatAppellStripExp_R1_cX_of_not_lexPositive {ell r t : ℤ}
    (hn : ¬(mhatDenomExp ell MhatRow.R1 r).lexPositive) :
    (mhatAppellStripExp ell MhatRow.R1 r t).cX = 2 * r + t := by
  unfold mhatAppellStripExp mhatDenomBranchExp
  rw [if_neg hn]
  simp [AffineXY.add, AffineXY.smul, mhatAppellNumeratorExp, mhatDenomExp,
    MhatRow.mZ, MhatRow.mArg]

theorem mhatAppellStripExp_R3_cX_of_lexPositive {ell r t : ℤ}
    (hp : (mhatDenomExp ell MhatRow.R3 r).lexPositive) :
    (mhatAppellStripExp ell MhatRow.R3 r t).cX = 2 * r - t := by
  unfold mhatAppellStripExp mhatDenomBranchExp
  rw [if_pos hp]
  simp [AffineXY.add, AffineXY.smul, mhatAppellNumeratorExp, mhatDenomExp,
    MhatRow.mZ, MhatRow.mArg]
  ring

theorem mhatAppellStripExp_R3_cX_of_not_lexPositive {ell r t : ℤ}
    (hn : ¬(mhatDenomExp ell MhatRow.R3 r).lexPositive) :
    (mhatAppellStripExp ell MhatRow.R3 r t).cX = 2 * r + t := by
  unfold mhatAppellStripExp mhatDenomBranchExp
  rw [if_neg hn]
  simp [AffineXY.add, AffineXY.smul, mhatAppellNumeratorExp, mhatDenomExp,
    MhatRow.mZ, MhatRow.mArg]

theorem mhatAppellStripTerm_coeff_ne_zero {ell : ℤ} {row : MhatRow} {r t : ℤ}
    {g : ExpQXY} (h : (mhatAppellStripTerm ell row r t).coeff g ≠ 0) :
    mhatAppellStripCoeff ell row r t ≠ 0 ∧
      g = expQXY (mhatAppellStripExp ell row r t).c0
        (mhatAppellStripExp ell row r t).cX
        (mhatAppellStripExp ell row r t).cY := by
  unfold mhatAppellStripTerm monom at h
  rw [HahnSeries.coeff_single] at h
  by_cases heq : g = expQXY (mhatAppellStripExp ell row r t).c0
      (mhatAppellStripExp ell row r t).cX
      (mhatAppellStripExp ell row r t).cY
  · simp [heq] at h
    exact ⟨h, heq⟩
  · simp [heq] at h

/-- Residual support predicate for the not-yet-banked affine Appell PWO proof. -/
def MhatAppellSupportPoint (ell : ℤ) (row : MhatRow) (g : ExpQXY) : Prop :=
  ∃ r t : ℤ,
    mhatAppellStripCoeff ell row r t ≠ 0 ∧
      g = expQXY (mhatAppellStripExp ell row r t).c0
        (mhatAppellStripExp ell row r t).cX
        (mhatAppellStripExp ell row r t).cY

theorem mhatAppellSupportPoint_fiber_isPWO_R0 (ell N : ℤ) :
    {y : ExpXY | MhatAppellSupportPoint ell MhatRow.R0 (toLex (N, y) : ExpQXY)}.IsPWO := by
  obtain ⟨B, hB⟩ := thetaQDeg_bddBelow 90 (MhatRow.R0.mZ ell).c0 (by norm_num)
  let C := thetaQDeg90LeBound (MhatRow.R0.mZ ell).c0 N
  apply Set.PartiallyWellOrderedOn.subsetProdLex
  · refine ((bddBelow_Ici (a := (-2 * C : ℤ))).isWF.isPWO).mono ?_
    rintro x ⟨y, hy, rfl⟩
    rw [Set.mem_Ici]
    rcases hy with ⟨r, t, hcoeff, heq⟩
    obtain ⟨hN, hx, _⟩ := expQXY_inj_toLex heq
    have htheta : thetaQDeg 90 (MhatRow.R0.mZ ell).c0 r ≤ N := by
      rw [hN]
      exact mhatAppellStripExp_c0_ge_theta hcoeff
    have hr := thetaQDeg90_le_bound htheta
    have hxval := mhatAppellStripExp_R0_cX ell r t
    rw [hxval] at hx
    change -2 * C ≤ (ofLex y).1
    rw [hx]
    nlinarith [hr.2]
  · intro x
    refine ((bddBelow_Ici (a := (-x - (N - B) : ℤ))).isWF.isPWO).mono ?_
    intro yy hyy
    rw [Set.mem_Ici]
    simp only [Set.mem_setOf_eq] at hyy
    rcases hyy with ⟨r, t, hcoeff, heq⟩
    obtain ⟨hN, hx, hyc⟩ := expQXY_inj_toLex heq
    simp only [ofLex_toLex] at hx hyc
    have htheta : thetaQDeg 90 (MhatRow.R0.mZ ell).c0 r ≤ N := by
      rw [hN]
      exact mhatAppellStripExp_c0_ge_theta hcoeff
    have hB_r : B ≤ thetaQDeg 90 (MhatRow.R0.mZ ell).c0 r := hB ⟨r, rfl⟩
    have hBN : B ≤ N := le_trans hB_r htheta
    have hxval := mhatAppellStripExp_R0_cX ell r t
    rw [hxval] at hx
    by_cases hp : (mhatDenomExp ell MhatRow.R0 r).lexPositive
    · have ht_le : t ≤ N - B := mhatAppell_t_le_of_lexPositive hN hcoeff hp hB_r
      have hyval :=
        mhatAppellStripExp_R0_cY_of_lexPositive (ell := ell) (r := r) (t := t) hp
      rw [hyval] at hyc
      rw [hyc, hx]
      nlinarith
    · have ht_nonneg := mhatAppellStripCoeff_t_nonneg_of_ne_zero hcoeff
      have hyval :=
        mhatAppellStripExp_R0_cY_of_not_lexPositive (ell := ell) (r := r) (t := t) hp
      rw [hyval] at hyc
      rw [hyc, hx]
      nlinarith

theorem mhatAppellSupportPoint_fiber_isPWO_R2 (ell N : ℤ) :
    {y : ExpXY | MhatAppellSupportPoint ell MhatRow.R2 (toLex (N, y) : ExpQXY)}.IsPWO := by
  obtain ⟨B, hB⟩ := thetaQDeg_bddBelow 90 (MhatRow.R2.mZ ell).c0 (by norm_num)
  let C := thetaQDeg90LeBound (MhatRow.R2.mZ ell).c0 N
  apply Set.PartiallyWellOrderedOn.subsetProdLex
  · refine ((bddBelow_Ici (a := (-2 * C : ℤ))).isWF.isPWO).mono ?_
    rintro x ⟨y, hy, rfl⟩
    rw [Set.mem_Ici]
    rcases hy with ⟨r, t, hcoeff, heq⟩
    obtain ⟨hN, hx, _⟩ := expQXY_inj_toLex heq
    have htheta : thetaQDeg 90 (MhatRow.R2.mZ ell).c0 r ≤ N := by
      rw [hN]
      exact mhatAppellStripExp_c0_ge_theta hcoeff
    have hr := thetaQDeg90_le_bound htheta
    have hxval := mhatAppellStripExp_R2_cX ell r t
    rw [hxval] at hx
    change -2 * C ≤ (ofLex y).1
    rw [hx]
    nlinarith [hr.2]
  · intro x
    refine ((bddBelow_Ici (a := (-x - (N - B) : ℤ))).isWF.isPWO).mono ?_
    intro yy hyy
    rw [Set.mem_Ici]
    simp only [Set.mem_setOf_eq] at hyy
    rcases hyy with ⟨r, t, hcoeff, heq⟩
    obtain ⟨hN, hx, hyc⟩ := expQXY_inj_toLex heq
    simp only [ofLex_toLex] at hx hyc
    have htheta : thetaQDeg 90 (MhatRow.R2.mZ ell).c0 r ≤ N := by
      rw [hN]
      exact mhatAppellStripExp_c0_ge_theta hcoeff
    have hB_r : B ≤ thetaQDeg 90 (MhatRow.R2.mZ ell).c0 r := hB ⟨r, rfl⟩
    have hBN : B ≤ N := le_trans hB_r htheta
    have hxval := mhatAppellStripExp_R2_cX ell r t
    rw [hxval] at hx
    by_cases hp : (mhatDenomExp ell MhatRow.R2 r).lexPositive
    · have ht_le : t ≤ N - B := mhatAppell_t_le_of_lexPositive hN hcoeff hp hB_r
      have hyval :=
        mhatAppellStripExp_R2_cY_of_lexPositive (ell := ell) (r := r) (t := t) hp
      rw [hyval] at hyc
      rw [hyc, hx]
      nlinarith
    · have ht_nonneg := mhatAppellStripCoeff_t_nonneg_of_ne_zero hcoeff
      have hyval :=
        mhatAppellStripExp_R2_cY_of_not_lexPositive (ell := ell) (r := r) (t := t) hp
      rw [hyval] at hyc
      rw [hyc, hx]
      nlinarith

theorem mhatAppellSupportPoint_fiber_isPWO_R1 (ell N : ℤ) :
    {y : ExpXY | MhatAppellSupportPoint ell MhatRow.R1 (toLex (N, y) : ExpQXY)}.IsPWO := by
  obtain ⟨B, hB⟩ := thetaQDeg_bddBelow 90 (MhatRow.R1.mZ ell).c0 (by norm_num)
  let C := thetaQDeg90LeBound (MhatRow.R1.mZ ell).c0 N
  apply Set.PartiallyWellOrderedOn.subsetProdLex
  · refine ((bddBelow_Ici (a := (-2 * C - (N - B) : ℤ))).isWF.isPWO).mono ?_
    rintro x ⟨y, hy, rfl⟩
    rw [Set.mem_Ici]
    rcases hy with ⟨r, t, hcoeff, heq⟩
    obtain ⟨hN, hx, _⟩ := expQXY_inj_toLex heq
    have htheta : thetaQDeg 90 (MhatRow.R1.mZ ell).c0 r ≤ N := by
      rw [hN]
      exact mhatAppellStripExp_c0_ge_theta hcoeff
    have hB_r : B ≤ thetaQDeg 90 (MhatRow.R1.mZ ell).c0 r := hB ⟨r, rfl⟩
    have hBN : B ≤ N := le_trans hB_r htheta
    have hr := thetaQDeg90_le_bound htheta
    change -2 * C - (N - B) ≤ (ofLex y).1
    by_cases hp : (mhatDenomExp ell MhatRow.R1 r).lexPositive
    · have ht_le : t ≤ N - B := mhatAppell_t_le_of_lexPositive hN hcoeff hp hB_r
      have hxval :=
        mhatAppellStripExp_R1_cX_of_lexPositive (ell := ell) (r := r) (t := t) hp
      rw [hxval] at hx
      rw [hx]
      nlinarith [hr.1]
    · have ht_nonneg := mhatAppellStripCoeff_t_nonneg_of_ne_zero hcoeff
      have hxval :=
        mhatAppellStripExp_R1_cX_of_not_lexPositive (ell := ell) (r := r) (t := t) hp
      rw [hxval] at hx
      rw [hx]
      nlinarith [hr.1, hBN]
  · intro x
    refine ((bddBelow_Ici (a := (-2 * C : ℤ))).isWF.isPWO).mono ?_
    intro yy hyy
    rw [Set.mem_Ici]
    simp only [Set.mem_setOf_eq] at hyy
    rcases hyy with ⟨r, t, hcoeff, heq⟩
    obtain ⟨hN, _, hyc⟩ := expQXY_inj_toLex heq
    simp only [ofLex_toLex] at hyc
    have htheta : thetaQDeg 90 (MhatRow.R1.mZ ell).c0 r ≤ N := by
      rw [hN]
      exact mhatAppellStripExp_c0_ge_theta hcoeff
    have hr := thetaQDeg90_le_bound htheta
    have hyval := mhatAppellStripExp_R1_cY ell r t
    rw [hyval] at hyc
    rw [hyc]
    nlinarith [hr.2]

theorem mhatAppellSupportPoint_fiber_isPWO_R3 (ell N : ℤ) :
    {y : ExpXY | MhatAppellSupportPoint ell MhatRow.R3 (toLex (N, y) : ExpQXY)}.IsPWO := by
  obtain ⟨B, hB⟩ := thetaQDeg_bddBelow 90 (MhatRow.R3.mZ ell).c0 (by norm_num)
  let C := thetaQDeg90LeBound (MhatRow.R3.mZ ell).c0 N
  apply Set.PartiallyWellOrderedOn.subsetProdLex
  · refine ((bddBelow_Ici (a := (-2 * C - (N - B) : ℤ))).isWF.isPWO).mono ?_
    rintro x ⟨y, hy, rfl⟩
    rw [Set.mem_Ici]
    rcases hy with ⟨r, t, hcoeff, heq⟩
    obtain ⟨hN, hx, _⟩ := expQXY_inj_toLex heq
    have htheta : thetaQDeg 90 (MhatRow.R3.mZ ell).c0 r ≤ N := by
      rw [hN]
      exact mhatAppellStripExp_c0_ge_theta hcoeff
    have hB_r : B ≤ thetaQDeg 90 (MhatRow.R3.mZ ell).c0 r := hB ⟨r, rfl⟩
    have hBN : B ≤ N := le_trans hB_r htheta
    have hr := thetaQDeg90_le_bound htheta
    change -2 * C - (N - B) ≤ (ofLex y).1
    by_cases hp : (mhatDenomExp ell MhatRow.R3 r).lexPositive
    · have ht_le : t ≤ N - B := mhatAppell_t_le_of_lexPositive hN hcoeff hp hB_r
      have hxval :=
        mhatAppellStripExp_R3_cX_of_lexPositive (ell := ell) (r := r) (t := t) hp
      rw [hxval] at hx
      rw [hx]
      nlinarith [hr.1]
    · have ht_nonneg := mhatAppellStripCoeff_t_nonneg_of_ne_zero hcoeff
      have hxval :=
        mhatAppellStripExp_R3_cX_of_not_lexPositive (ell := ell) (r := r) (t := t) hp
      rw [hxval] at hx
      rw [hx]
      nlinarith [hr.1, hBN]
  · intro x
    refine ((bddBelow_Ici (a := (-2 * C : ℤ))).isWF.isPWO).mono ?_
    intro yy hyy
    rw [Set.mem_Ici]
    simp only [Set.mem_setOf_eq] at hyy
    rcases hyy with ⟨r, t, hcoeff, heq⟩
    obtain ⟨hN, _, hyc⟩ := expQXY_inj_toLex heq
    simp only [ofLex_toLex] at hyc
    have htheta : thetaQDeg 90 (MhatRow.R3.mZ ell).c0 r ≤ N := by
      rw [hN]
      exact mhatAppellStripExp_c0_ge_theta hcoeff
    have hr := thetaQDeg90_le_bound htheta
    have hyval := mhatAppellStripExp_R3_cY ell r t
    rw [hyval] at hyc
    rw [hyc]
    nlinarith [hr.2]

theorem mhatAppellSupportPoint_isPWO (ell : ℤ) (row : MhatRow) :
    {g : ExpQXY | MhatAppellSupportPoint ell row g}.IsPWO := by
  apply Set.PartiallyWellOrderedOn.subsetProdLex
  · obtain ⟨B, hB⟩ := thetaQDeg_bddBelow 90 (row.mZ ell).c0 (by norm_num)
    refine ((bddBelow_Ici (a := B)).isWF.isPWO).mono ?_
    rintro N ⟨g, hg, rfl⟩
    rw [Set.mem_Ici]
    rcases hg with ⟨r, t, hcoeff, heq⟩
    have hq : (ofLex g).1 = (mhatAppellStripExp ell row r t).c0 := by
      have h1 : (ofLex g).1 = (ofLex (expQXY (mhatAppellStripExp ell row r t).c0
          (mhatAppellStripExp ell row r t).cX
          (mhatAppellStripExp ell row r t).cY)).1 := by
        rw [heq]
      simpa [expQXY] using h1
    change B ≤ (ofLex g).1
    rw [hq]
    exact le_trans (hB ⟨r, rfl⟩) (mhatAppellStripExp_c0_ge_theta hcoeff)
  · intro N
    cases row
    · exact mhatAppellSupportPoint_fiber_isPWO_R0 ell N
    · exact mhatAppellSupportPoint_fiber_isPWO_R1 ell N
    · exact mhatAppellSupportPoint_fiber_isPWO_R2 ell N
    · exact mhatAppellSupportPoint_fiber_isPWO_R3 ell N

theorem mhatAppell_finite_co_support (ell : ℤ) (row : MhatRow) (g : ExpQXY) :
    {p : ℤ × ℤ | (mhatAppellStripTerm ell row p.1 p.2).coeff g ≠ 0}.Finite := by
  cases row
  · let N := (ofLex g).1
    let y0 := (ofLex (ofLex g).2).2
    let C := thetaQDeg90LeBound (MhatRow.R0.mZ ell).c0 N
    let T := 2 * C + (y0.natAbs : ℤ) + 1
    apply Set.Finite.subset (Set.finite_Icc ((-C, 0) : ℤ × ℤ) ((C, T) : ℤ × ℤ))
    rintro ⟨r, t⟩ hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    obtain ⟨hcoeff, heq⟩ := mhatAppellStripTerm_coeff_ne_zero hp
    have hN : N = (mhatAppellStripExp ell MhatRow.R0 r t).c0 := by
      unfold N
      rw [heq]
      rfl
    have htheta : thetaQDeg 90 (MhatRow.R0.mZ ell).c0 r ≤ N := by
      rw [hN]
      exact mhatAppellStripExp_c0_ge_theta hcoeff
    have hr := thetaQDeg90_le_bound htheta
    have ht0 := mhatAppellStripCoeff_t_nonneg_of_ne_zero hcoeff
    have hy_eq : y0 = (mhatAppellStripExp ell MhatRow.R0 r t).cY := by
      unfold y0
      rw [heq]
      rfl
    have hy_le_abs : y0 ≤ (y0.natAbs : ℤ) := Int.le_natAbs
    have hneg_y_le_abs : -y0 ≤ (y0.natAbs : ℤ) := by
      have := Int.le_natAbs (a := -y0)
      simpa using this
    have ht_upper : t ≤ T := by
      by_cases hp : (mhatDenomExp ell MhatRow.R0 r).lexPositive
      · have hyval :=
          mhatAppellStripExp_R0_cY_of_lexPositive (ell := ell) (r := r) (t := t) hp
        rw [hyval] at hy_eq
        unfold T
        nlinarith [hr.1, hr.2, hy_le_abs, hneg_y_le_abs]
      · have hyval :=
          mhatAppellStripExp_R0_cY_of_not_lexPositive (ell := ell) (r := r) (t := t) hp
        rw [hyval] at hy_eq
        unfold T
        nlinarith [hr.1, hr.2, hy_le_abs, hneg_y_le_abs]
    rw [Set.mem_Icc, Prod.le_def, Prod.le_def]
    exact ⟨⟨hr.1, ht0⟩, ⟨hr.2, ht_upper⟩⟩
  · let N := (ofLex g).1
    let x0 := (ofLex (ofLex g).2).1
    let C := thetaQDeg90LeBound (MhatRow.R1.mZ ell).c0 N
    let T := 2 * C + (x0.natAbs : ℤ) + 1
    apply Set.Finite.subset (Set.finite_Icc ((-C, 0) : ℤ × ℤ) ((C, T) : ℤ × ℤ))
    rintro ⟨r, t⟩ hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    obtain ⟨hcoeff, heq⟩ := mhatAppellStripTerm_coeff_ne_zero hp
    have hN : N = (mhatAppellStripExp ell MhatRow.R1 r t).c0 := by
      unfold N
      rw [heq]
      rfl
    have htheta : thetaQDeg 90 (MhatRow.R1.mZ ell).c0 r ≤ N := by
      rw [hN]
      exact mhatAppellStripExp_c0_ge_theta hcoeff
    have hr := thetaQDeg90_le_bound htheta
    have ht0 := mhatAppellStripCoeff_t_nonneg_of_ne_zero hcoeff
    have hx_eq : x0 = (mhatAppellStripExp ell MhatRow.R1 r t).cX := by
      unfold x0
      rw [heq]
      rfl
    have hx_le_abs : x0 ≤ (x0.natAbs : ℤ) := Int.le_natAbs
    have hneg_x_le_abs : -x0 ≤ (x0.natAbs : ℤ) := by
      have := Int.le_natAbs (a := -x0)
      simpa using this
    have ht_upper : t ≤ T := by
      by_cases hp : (mhatDenomExp ell MhatRow.R1 r).lexPositive
      · have hxval :=
          mhatAppellStripExp_R1_cX_of_lexPositive (ell := ell) (r := r) (t := t) hp
        rw [hxval] at hx_eq
        unfold T
        nlinarith [hr.1, hr.2, hx_le_abs, hneg_x_le_abs]
      · have hxval :=
          mhatAppellStripExp_R1_cX_of_not_lexPositive (ell := ell) (r := r) (t := t) hp
        rw [hxval] at hx_eq
        unfold T
        nlinarith [hr.1, hr.2, hx_le_abs, hneg_x_le_abs]
    rw [Set.mem_Icc, Prod.le_def, Prod.le_def]
    exact ⟨⟨hr.1, ht0⟩, ⟨hr.2, ht_upper⟩⟩
  · let N := (ofLex g).1
    let y0 := (ofLex (ofLex g).2).2
    let C := thetaQDeg90LeBound (MhatRow.R2.mZ ell).c0 N
    let T := 2 * C + (y0.natAbs : ℤ) + 1
    apply Set.Finite.subset (Set.finite_Icc ((-C, 0) : ℤ × ℤ) ((C, T) : ℤ × ℤ))
    rintro ⟨r, t⟩ hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    obtain ⟨hcoeff, heq⟩ := mhatAppellStripTerm_coeff_ne_zero hp
    have hN : N = (mhatAppellStripExp ell MhatRow.R2 r t).c0 := by
      unfold N
      rw [heq]
      rfl
    have htheta : thetaQDeg 90 (MhatRow.R2.mZ ell).c0 r ≤ N := by
      rw [hN]
      exact mhatAppellStripExp_c0_ge_theta hcoeff
    have hr := thetaQDeg90_le_bound htheta
    have ht0 := mhatAppellStripCoeff_t_nonneg_of_ne_zero hcoeff
    have hy_eq : y0 = (mhatAppellStripExp ell MhatRow.R2 r t).cY := by
      unfold y0
      rw [heq]
      rfl
    have hy_le_abs : y0 ≤ (y0.natAbs : ℤ) := Int.le_natAbs
    have hneg_y_le_abs : -y0 ≤ (y0.natAbs : ℤ) := by
      have := Int.le_natAbs (a := -y0)
      simpa using this
    have ht_upper : t ≤ T := by
      by_cases hp : (mhatDenomExp ell MhatRow.R2 r).lexPositive
      · have hyval :=
          mhatAppellStripExp_R2_cY_of_lexPositive (ell := ell) (r := r) (t := t) hp
        rw [hyval] at hy_eq
        unfold T
        nlinarith [hr.1, hr.2, hy_le_abs, hneg_y_le_abs]
      · have hyval :=
          mhatAppellStripExp_R2_cY_of_not_lexPositive (ell := ell) (r := r) (t := t) hp
        rw [hyval] at hy_eq
        unfold T
        nlinarith [hr.1, hr.2, hy_le_abs, hneg_y_le_abs]
    rw [Set.mem_Icc, Prod.le_def, Prod.le_def]
    exact ⟨⟨hr.1, ht0⟩, ⟨hr.2, ht_upper⟩⟩
  · let N := (ofLex g).1
    let x0 := (ofLex (ofLex g).2).1
    let C := thetaQDeg90LeBound (MhatRow.R3.mZ ell).c0 N
    let T := 2 * C + (x0.natAbs : ℤ) + 1
    apply Set.Finite.subset (Set.finite_Icc ((-C, 0) : ℤ × ℤ) ((C, T) : ℤ × ℤ))
    rintro ⟨r, t⟩ hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    obtain ⟨hcoeff, heq⟩ := mhatAppellStripTerm_coeff_ne_zero hp
    have hN : N = (mhatAppellStripExp ell MhatRow.R3 r t).c0 := by
      unfold N
      rw [heq]
      rfl
    have htheta : thetaQDeg 90 (MhatRow.R3.mZ ell).c0 r ≤ N := by
      rw [hN]
      exact mhatAppellStripExp_c0_ge_theta hcoeff
    have hr := thetaQDeg90_le_bound htheta
    have ht0 := mhatAppellStripCoeff_t_nonneg_of_ne_zero hcoeff
    have hx_eq : x0 = (mhatAppellStripExp ell MhatRow.R3 r t).cX := by
      unfold x0
      rw [heq]
      rfl
    have hx_le_abs : x0 ≤ (x0.natAbs : ℤ) := Int.le_natAbs
    have hneg_x_le_abs : -x0 ≤ (x0.natAbs : ℤ) := by
      have := Int.le_natAbs (a := -x0)
      simpa using this
    have ht_upper : t ≤ T := by
      by_cases hp : (mhatDenomExp ell MhatRow.R3 r).lexPositive
      · have hxval :=
          mhatAppellStripExp_R3_cX_of_lexPositive (ell := ell) (r := r) (t := t) hp
        rw [hxval] at hx_eq
        unfold T
        nlinarith [hr.1, hr.2, hx_le_abs, hneg_x_le_abs]
      · have hxval :=
          mhatAppellStripExp_R3_cX_of_not_lexPositive (ell := ell) (r := r) (t := t) hp
        rw [hxval] at hx_eq
        unfold T
        nlinarith [hr.1, hr.2, hx_le_abs, hneg_x_le_abs]
    rw [Set.mem_Icc, Prod.le_def, Prod.le_def]
    exact ⟨⟨hr.1, ht0⟩, ⟨hr.2, ht_upper⟩⟩

/--
The affine Appell strip family is the remaining proof obligation for the full
four-index `MhatRowFamily`.  It is recorded as a theorem-shaped target rather
than replaced by a collapsed cone object.
-/
def MhatAppellPWOResidual : Prop :=
  ∀ ell row, (⋃ p : ℤ × ℤ, (mhatAppellStripTerm ell row p.1 p.2).support).IsPWO ∧
    ∀ g : ExpQXY,
      {p : ℤ × ℤ | (mhatAppellStripTerm ell row p.1 p.2).coeff g ≠ 0}.Finite

theorem mhatAppellPWO : MhatAppellPWOResidual := by
  intro ell row
  constructor
  · refine (mhatAppellSupportPoint_isPWO ell row).mono (Set.iUnion_subset (fun p => ?_))
    intro g hg
    rcases p with ⟨r, t⟩
    have hcoeff_g : (mhatAppellStripTerm ell row r t).coeff g ≠ 0 := by
      simpa [HahnSeries.mem_support] using hg
    obtain ⟨hstrip, heq⟩ := mhatAppellStripTerm_coeff_ne_zero hcoeff_g
    exact ⟨r, t, hstrip, heq⟩
  · intro g
    exact mhatAppell_finite_co_support ell row g

/-- The Appell strip as a `SummableFamily`, conditional on the residual PWO/fiber proof. -/
noncomputable def mhatAppellFamilyOf (h : MhatAppellPWOResidual)
    (ell : ℤ) (row : MhatRow) :
    HahnSeries.SummableFamily ExpQXY ℚ (ℤ × ℤ) where
  toFun p := mhatAppellStripTerm ell row p.1 p.2
  isPWO_iUnion_support' := (h ell row).1
  finite_co_support' := (h ell row).2

/--
The genuine four-index row family assembled from the row monomial, the
`jArg` theta, the affine Appell strip, and the `-mZ` theta.  This is conditional
only on `MhatAppellPWOResidual`; no cone-side object is used.
-/
noncomputable def MhatRowFamilyOf (h : MhatAppellPWOResidual)
    (ell : ℤ) (row : MhatRow) :
    HahnSeries.SummableFamily ExpQXY ℚ ((ℤ × (ℤ × ℤ)) × ℤ) :=
  row.lead.toMonom •
    (((mhatJThetaFamily row).mul (mhatAppellFamilyOf h ell row)).mul
      (mhatDThetaFamily ell row))

/-- The conditional four-row m-table object: the intended `Mhat` once the residual is proved. -/
noncomputable def MhatOf (h : MhatAppellPWOResidual) (ell : ℤ) : S :=
  ∑ row : MhatRow, (MhatRowFamilyOf h ell row).hsum

/-- The unconditional four-row m-table object. -/
noncomputable def Mhat (ell : ℤ) : S :=
  MhatOf mhatAppellPWO ell

/-- Coefficient extraction for the conditional construction as a finite row sum of row hsums. -/
theorem coeffQXY_MhatOf (h : MhatAppellPWOResidual) (ell e a b : ℤ) :
    coeffQXY (MhatOf h ell) e a b =
      ∑ row : MhatRow, ((MhatRowFamilyOf h ell row).hsum).coeff (expQXY e a b) := by
  unfold coeffQXY MhatOf
  rw [HahnSeries.coeff_sum]

/-- Slice coefficient extraction for the conditional construction. -/
theorem coeffXY_MhatOf (h : MhatAppellPWOResidual) (ell a b e : ℤ) :
    (coeffXY (MhatOf h ell) a b).coeff e =
      ∑ row : MhatRow, ((MhatRowFamilyOf h ell row).hsum).coeff (expQXY e a b) := by
  rw [coeffXY_coeff, coeffQXY_MhatOf]

/-- Coefficient extraction for the unconditional construction as a finite row sum of row hsums. -/
theorem coeffQXY_Mhat (ell e a b : ℤ) :
    coeffQXY (Mhat ell) e a b =
      ∑ row : MhatRow, ((MhatRowFamilyOf mhatAppellPWO ell row).hsum).coeff
        (expQXY e a b) := by
  simpa [Mhat] using coeffQXY_MhatOf mhatAppellPWO ell e a b

/-- Slice coefficient extraction for the unconditional construction. -/
theorem coeffXY_Mhat (ell a b e : ℤ) :
    (coeffXY (Mhat ell) a b).coeff e =
      ∑ row : MhatRow, ((MhatRowFamilyOf mhatAppellPWO ell row).hsum).coeff
        (expQXY e a b) := by
  simpa [Mhat] using coeffXY_MhatOf mhatAppellPWO ell a b e

end

end Ch10M3Mhat
end Pending
end QseriesFormalization
