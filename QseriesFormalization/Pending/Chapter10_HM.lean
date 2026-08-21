import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Order
import QseriesFormalization.Basic
import QseriesFormalization.Chapter03
import QseriesFormalization.Pending.JTP_FormalPS_Pentagonal
import QseriesFormalization.Pending.Chapter10_PF

/-!
# Chapter 10 HM/Appell-Lerch scaffold

This file starts the Hickerson-Mortenson route for Chan's Chapter 10
Appell-Lerch reduction.  It is intentionally isolated in `Pending/` and is
not imported by `QseriesFormalization.lean` or `Audit.lean`.

The numerical companion is `scripts/ch10_hm_verify.py`.  It checks the nine
shifted `T_ij` entries against the direct `f_{2,3,2}` cone sum through `Q^44`.

The raw `ell = 1` specialization has two singular `0 * infinity` products
after substituting Chan's monomials.  The verifier therefore uses the same HM
corollary with `ell = 2` for exactly `T02` and `T10`; all other entries use
`ell = 1`.  The choice is recorded below as `hmEll`.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch10HM

open scoped LaurentSeries
open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology
open QseriesFormalization.Pending.JTPFormalPSPentagonal

noncomputable section

/-! ## Exponent-level Laurent data -/

/-- The Laurent-series coefficient field used for the Ch10 HM table. -/
abbrev QLaurent := LaurentSeries ℚ

/-- Coefficient extraction for the Ch10 Laurent-series layer. -/
def lcoeff (s : QLaurent) (e : ℤ) : ℚ :=
  s.coeff e

/-- The Laurent monomial `Q^e`. -/
def Qpow (e : ℤ) : QLaurent :=
  HahnSeries.single e (1 : ℚ)

@[simp] theorem coeff_Qpow (e k : ℤ) :
    lcoeff (Qpow e) k = if k = e then 1 else 0 := by
  simp [lcoeff, Qpow, HahnSeries.coeff_single]

@[simp] theorem Qpow_zero : Qpow 0 = (1 : QLaurent) := by
  rfl

@[simp] theorem Qpow_mul (a b : ℤ) :
    Qpow a * Qpow b = Qpow (a + b) := by
  simp [Qpow]

@[simp] theorem lcoeff_Qpow_mul (c e : ℤ) (s : QLaurent) :
    lcoeff (Qpow c * s) e = lcoeff s (e - c) := by
  simp [lcoeff, Qpow, HahnSeries.coeff_single_mul]

/-- The sign `(-1)^n`, with integer exponent interpreted by parity. -/
def negOnePowIntQ (n : ℤ) : ℚ :=
  (-1 : ℚ) ^ n.natAbs

theorem negOnePowIntQ_eq_negOnePow (n : ℤ) :
    negOnePowIntQ n = ((n.negOnePow : ℤ) : ℚ) := by
  unfold negOnePowIntQ
  rw [← zpow_natCast]
  rw [← Int.cast_negOnePow ℚ (n.natAbs : ℤ)]
  rw [show (n.natAbs : ℤ) = |n| by exact Int.natCast_natAbs n]
  rw [Int.negOnePow_abs]

theorem negOnePowIntQ_neg (n : ℤ) :
    negOnePowIntQ (-n) = negOnePowIntQ n := by
  rw [negOnePowIntQ_eq_negOnePow, negOnePowIntQ_eq_negOnePow]
  rw [Int.negOnePow_neg]

theorem negOnePowIntQ_add (m n : ℤ) :
    negOnePowIntQ (m + n) = negOnePowIntQ m * negOnePowIntQ n := by
  rw [negOnePowIntQ_eq_negOnePow, negOnePowIntQ_eq_negOnePow,
    negOnePowIntQ_eq_negOnePow]
  rw [Int.negOnePow_add]
  norm_num

theorem negOnePowIntQ_sub (m n : ℤ) :
    negOnePowIntQ (m - n) = negOnePowIntQ m * negOnePowIntQ n := by
  rw [negOnePowIntQ_eq_negOnePow, negOnePowIntQ_eq_negOnePow,
    negOnePowIntQ_eq_negOnePow]
  rw [Int.negOnePow_sub]
  norm_num

/-- A large finite window used for coefficient extraction from bilateral theta
series.  The window is deliberately oversized; it gives a concrete finite
coefficient extractor while the support guard below makes the result a genuine
Laurent series. -/
def jCoeffWindow (a b e : ℤ) : ℤ :=
  4 * (Int.natAbs a + Int.natAbs b + Int.natAbs e + 2 : ℤ)

/-- A coarse lower support guard for `j(Q^a;Q^b)`.  In this pending file this
guard is part of the coefficient-level semantic object; later work can replace
the finite extractor by a `HahnSeries.SummableFamily` bilateral sum without
changing the public `jLaurent` interface. -/
def jCoeffLower (a b : ℤ) : ℤ :=
  -((Int.natAbs a + Int.natAbs b + 2 : ℤ) ^ 2)

/-- Exponent of the `n`-th term in `j(Q^a; Q^b)`. -/
def jExp (a b n : ℤ) : ℤ :=
  b * n * (n - 1) / 2 + a * n

/-- Twice the exponent of the `n`-th term in `j(Q^a; Q^b)`.  This avoids
integer-division bookkeeping in the elementary algebra lemmas. -/
def jExpTwice (a b n : ℤ) : ℤ :=
  b * n * (n - 1) + 2 * a * n

theorem jExp_eq_jExpTwice_div_two (a b n : ℤ) :
    jExp a b n = jExpTwice a b n / 2 := by
  unfold jExp jExpTwice
  rw [show b * n * (n - 1) + 2 * a * n =
      b * n * (n - 1) + (a * n) * 2 by ring]
  rw [Int.add_mul_ediv_right _ _ (by norm_num : (2 : ℤ) ≠ 0)]

/-- Exponent of the numerator in
`m(Q^a, Q^90, Q^z) = j(Q^z;Q^90)^{-1} * sum_r ...`. -/
def appellNumeratorExp (z r : ℤ) : ℤ :=
  90 * r * (r - 1) / 2 + z * r

/-- Exponent `d` in the Appell-Lerch denominator `1 - Q^d`. -/
def appellDenomExp (a z r : ℤ) : ℤ :=
  90 * (r - 1) + a + z

/-- Coefficient extractor for `j(Q^a;Q^b)`, written as a finite search over
the possible bilateral exponents. -/
def jCoeff (a b e : ℤ) : ℚ :=
  if e < jCoeffLower a b then 0
  else
    ∑ n ∈ Finset.Icc (-(jCoeffWindow a b e)) (jCoeffWindow a b e),
      if jExp a b n = e then negOnePowIntQ n else 0

/-- Laurent-series semantics for `j(Q^a;Q^b)`, with concrete coefficient
extraction. -/
def jLaurent (a b : ℤ) : QLaurent :=
  HahnSeries.ofSuppBddBelow (fun e : ℤ => jCoeff a b e) <| by
    refine ⟨jCoeffLower a b, ?_⟩
    intro e he
    by_contra hle
    have hlt : e < jCoeffLower a b := by omega
    have hz : jCoeff a b e = 0 := by
      simp [jCoeff, hlt]
    exact he hz

@[simp] theorem coeff_jLaurent (a b e : ℤ) :
    lcoeff (jLaurent a b) e = jCoeff a b e := by
  simp [lcoeff, jLaurent]

/-- Base values for the Laurent-valued Appell-Lerch normal form on
`0 ≤ a < 90`.  The values are chosen to satisfy the inversion symmetry
`M(a)+M(90-a)=1` on the fundamental interval. -/
def appellMFEBase (n : ℕ) : QLaurent :=
  if n = 0 then 0
  else if 2 * n < 90 then 0
  else if 2 * n = 90 then ((1 / 2 : ℚ) : QLaurent)
  else 1

private theorem half_Q_eq_one_sub_half_Q :
    ((1 / 2 : ℚ) : QLaurent) = 1 - ((1 / 2 : ℚ) : QLaurent) := by
  ext k
  by_cases hk : k = 0
  · subst k
    change (HahnSeries.single (0 : ℤ) (1 / 2 : ℚ)).coeff 0 =
      (1 - HahnSeries.single (0 : ℤ) (1 / 2 : ℚ)).coeff 0
    simp [HahnSeries.coeff_sub]
    norm_num
  · change (HahnSeries.single (0 : ℤ) (1 / 2 : ℚ)).coeff k =
      (1 - HahnSeries.single (0 : ℤ) (1 / 2 : ℚ)).coeff k
    simp [HahnSeries.coeff_sub, hk]

/-- Nonnegative branch for the Appell-Lerch functional-equation normal form. -/
def appellMFENonneg : ℕ → QLaurent
  | n =>
      if h : n < 90 then appellMFEBase n
      else 1 - Qpow ((n : ℤ) - 90) * appellMFENonneg (n - 90)
termination_by n => n
decreasing_by omega

/-- Laurent-series normal form for `m(Q^a,Q^90,Q^z)`.

This is the old functional-equation model used by the initial pending HM
scaffold.  It is kept under a separate name because the genuine
Hickerson-Mortenson quotient depends on `z`; see `appellM` below. -/
def appellMFE (a _z : ℤ) : QLaurent :=
  if _h : 0 ≤ a then appellMFENonneg a.toNat
  else Qpow (-a) * appellMFENonneg (-a).toNat

def appellMFECoeff (a z e : ℤ) : ℚ :=
  lcoeff (appellMFE a z) e

theorem jExpTwice_symm (a b n : ℤ) :
    jExpTwice (b - a) b (-n) = jExpTwice a b n := by
  unfold jExpTwice
  ring

theorem jExp_symm (a b n : ℤ) :
    jExp (b - a) b (-n) = jExp a b n := by
  rw [jExp_eq_jExpTwice_div_two, jExp_eq_jExpTwice_div_two, jExpTwice_symm]

theorem jExpTwice_shift (a b k n : ℤ) :
    jExpTwice (a + b * k) b (n - k) =
      jExpTwice a b n - 2 * a * k - b * k * (k - 1) := by
  unfold jExpTwice
  ring

theorem two_mul_jExp (a b n : ℤ) :
    2 * jExp a b n = jExpTwice a b n := by
  unfold jExp jExpTwice
  have hdiv : (2 : ℤ) ∣ b * n * (n - 1) := by
    have h : (2 : ℤ) ∣ (n - 1) * ((n - 1) + 1) :=
      Int.two_dvd_mul_add_one (n - 1)
    have h' : (2 : ℤ) ∣ n * (n - 1) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm,
        mul_left_comm, mul_assoc] using h
    simpa [mul_assoc] using dvd_mul_of_dvd_right h' b
  rw [mul_add]
  rw [Int.mul_ediv_cancel' hdiv]
  ring

theorem jExpTwice_lower_bound (a b n : ℤ) (hb : 0 < b) :
    -2 * ((Int.natAbs a + Int.natAbs b + 2 : ℤ) ^ 2) ≤ jExpTwice a b n := by
  unfold jExpTwice
  let A : ℤ := |a|
  let B : ℤ := |b|
  let M : ℤ := A + B + 2
  have hA_nonneg : 0 ≤ A := by exact abs_nonneg a
  have hB_nonneg : 0 ≤ B := by exact abs_nonneg b
  have hb_ge1 : 1 ≤ b := by omega
  have hb_nonneg : 0 ≤ b := by omega
  have ha_le : a ≤ A := by exact le_abs_self a
  have hneg_le_a : -A ≤ a := by exact neg_abs_le a
  have hM_sq_ge : (A + 1) ^ 2 ≤ M ^ 2 := by
    dsimp [M]
    nlinarith [sq_nonneg (B + 1)]
  have hrewrite : ((Int.natAbs a + Int.natAbs b + 2 : ℤ) ^ 2) = M ^ 2 := by
    dsimp [M, A, B]
    rw [Int.natCast_natAbs, Int.natCast_natAbs]
  rw [hrewrite]
  by_cases hn0 : n = 0
  · subst n
    simp
    nlinarith [sq_nonneg M]
  · by_cases hn : 0 < n
    · have hn_nonneg : 0 ≤ n := by omega
      have hn1_nonneg : 0 ≤ n - 1 := by omega
      have hnprod : 0 ≤ n * (n - 1) := mul_nonneg hn_nonneg hn1_nonneg
      have hbterm : n * (n - 1) ≤ b * (n * (n - 1)) := by nlinarith
      have haterm : -A * n ≤ a * n := by nlinarith
      have hsq : 0 ≤ (n - (A + 1)) ^ 2 := sq_nonneg _
      nlinarith [hbterm, haterm, hsq, hM_sq_ge]
    · have hn_nonpos : n ≤ 0 := by omega
      have hn1_nonpos : n - 1 ≤ 0 := by omega
      have hnprod : 0 ≤ n * (n - 1) :=
        mul_nonneg_of_nonpos_of_nonpos hn_nonpos hn1_nonpos
      have hbterm : n * (n - 1) ≤ b * (n * (n - 1)) := by nlinarith
      have haterm : A * n ≤ a * n := by nlinarith
      have hsq : 0 ≤ (n + A) ^ 2 := sq_nonneg _
      nlinarith [hbterm, haterm, hsq, hM_sq_ge]

theorem jExp_lower_bound (a b n : ℤ) (hb : 0 < b) :
    jCoeffLower a b ≤ jExp a b n := by
  have htw := two_mul_jExp a b n
  have hlower := jExpTwice_lower_bound a b n hb
  unfold jCoeffLower
  nlinarith

theorem jExp_root_le_window_right (a b e n : ℤ) (hb : 0 < b)
    (h : jExp a b n = e) :
    n ≤ jCoeffWindow a b e := by
  have htw : jExpTwice a b n = 2 * e := by
    have := two_mul_jExp a b n
    nlinarith
  unfold jExpTwice at htw
  unfold jCoeffWindow
  let A : ℤ := |a|
  let B : ℤ := |b|
  let E : ℤ := |e|
  let M : ℤ := A + B + E + 2
  have hA_nonneg : 0 ≤ A := by exact abs_nonneg a
  have hB_nonneg : 0 ≤ B := by exact abs_nonneg b
  have hE_nonneg : 0 ≤ E := by exact abs_nonneg e
  have hb_ge1 : 1 ≤ b := by omega
  have ha_lower : -A ≤ a := by exact neg_abs_le a
  have he_le : e ≤ E := by exact le_abs_self e
  have hrewrite : 4 * (↑a.natAbs + ↑b.natAbs + ↑e.natAbs + 2) = 4 * M := by
    dsimp [M, A, B, E]
    rw [Int.natCast_natAbs, Int.natCast_natAbs, Int.natCast_natAbs]
  rw [hrewrite]
  by_contra hle
  have hn_gt : 4 * M < n := by omega
  have hM_nonneg : 0 ≤ M := by dsimp [M]; nlinarith
  have hn_pos : 0 < n := by nlinarith
  have hn_nonneg : 0 ≤ n := by omega
  have hn1_nonneg : 0 ≤ n - 1 := by omega
  have hnprod : 0 ≤ n * (n - 1) := mul_nonneg hn_nonneg hn1_nonneg
  have hbterm : n * (n - 1) ≤ b * (n * (n - 1)) := by nlinarith
  have haterm : -A * n ≤ a * n := by nlinarith
  have hbig : 2 * E < n * (n - 1) - 2 * A * n := by
    nlinarith [sq_nonneg (n - (2 * A + 2)), hA_nonneg, hB_nonneg, hE_nonneg, hn_gt]
  have hgt : 2 * E < b * (n * (n - 1)) + 2 * a * n := by nlinarith
  nlinarith

theorem jExp_root_le_window_left (a b e n : ℤ) (hb : 0 < b)
    (h : jExp a b n = e) :
    -jCoeffWindow a b e ≤ n := by
  have htw : jExpTwice a b n = 2 * e := by
    have := two_mul_jExp a b n
    nlinarith
  unfold jExpTwice at htw
  have htw' : b * (n * (n - 1)) + 2 * a * n = 2 * e := by
    nlinarith [htw]
  unfold jCoeffWindow
  let A : ℤ := |a|
  let B : ℤ := |b|
  let E : ℤ := |e|
  let M : ℤ := A + B + E + 2
  have hA_nonneg : 0 ≤ A := by exact abs_nonneg a
  have hB_nonneg : 0 ≤ B := by exact abs_nonneg b
  have hE_nonneg : 0 ≤ E := by exact abs_nonneg e
  have hb_ge1 : 1 ≤ b := by omega
  have ha_upper : a ≤ A := by exact le_abs_self a
  have he_le : e ≤ E := by exact le_abs_self e
  have hrewrite : 4 * (↑a.natAbs + ↑b.natAbs + ↑e.natAbs + 2) = 4 * M := by
    dsimp [M, A, B, E]
    rw [Int.natCast_natAbs, Int.natCast_natAbs, Int.natCast_natAbs]
  rw [hrewrite]
  by_contra hle
  have hn_lt : n < -4 * M := by omega
  have hM_nonneg : 0 ≤ M := by dsimp [M]; nlinarith
  have hn_nonpos : n ≤ 0 := by omega
  have hn1_nonpos : n - 1 ≤ 0 := by omega
  have hnprod : 0 ≤ n * (n - 1) :=
    mul_nonneg_of_nonpos_of_nonpos hn_nonpos hn1_nonpos
  have hbterm : n * (n - 1) ≤ b * (n * (n - 1)) := by nlinarith
  have haterm : A * n ≤ a * n := by nlinarith
  have hbig : 2 * E < n * (n - 1) + 2 * A * n := by
    nlinarith [sq_nonneg (n + (2 * A + 2)), hA_nonneg, hB_nonneg, hE_nonneg, hn_lt]
  have hgt : 2 * E < b * (n * (n - 1)) + 2 * a * n := by nlinarith
  nlinarith [htw', hgt, he_le]

theorem jCoeff_eq_window_sum (a b e : ℤ) (hb : 0 < b) :
    jCoeff a b e =
      ∑ n ∈ Finset.Icc (-(jCoeffWindow a b e)) (jCoeffWindow a b e),
        if jExp a b n = e then negOnePowIntQ n else 0 := by
  unfold jCoeff
  by_cases hlt : e < jCoeffLower a b
  · rw [if_pos hlt]
    symm
    refine Finset.sum_eq_zero ?_
    intro n hn
    by_cases hroot : jExp a b n = e
    · have hlower := jExp_lower_bound a b n hb
      omega
    · simp [hroot]
  · rw [if_neg hlt]

theorem jCoeff_eq_sum_Icc_of_window_le (a b e W : ℤ) (hb : 0 < b)
    (hW : jCoeffWindow a b e ≤ W) :
    jCoeff a b e =
      ∑ n ∈ Finset.Icc (-W) W, if jExp a b n = e then negOnePowIntQ n else 0 := by
  rw [jCoeff_eq_window_sum a b e hb]
  refine Finset.sum_subset ?subset ?zero
  · intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    constructor <;> omega
  · intro n hn hnot
    rw [Finset.mem_Icc] at hn
    by_cases hroot : jExp a b n = e
    · have hleft := jExp_root_le_window_left a b e n hb hroot
      have hright := jExp_root_le_window_right a b e n hb hroot
      exfalso
      apply hnot
      rw [Finset.mem_Icc]
      exact ⟨hleft, hright⟩
    · simp [hroot]

theorem jCoeff_eq_sum_Icc_of_window_subset (a b e L U : ℤ) (hb : 0 < b)
    (hL : L ≤ -jCoeffWindow a b e) (hU : jCoeffWindow a b e ≤ U) :
    jCoeff a b e =
      ∑ n ∈ Finset.Icc L U, if jExp a b n = e then negOnePowIntQ n else 0 := by
  rw [jCoeff_eq_window_sum a b e hb]
  refine Finset.sum_subset ?subset ?zero
  · intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    constructor <;> omega
  · intro n hn hnot
    rw [Finset.mem_Icc] at hn
    by_cases hroot : jExp a b n = e
    · have hleft := jExp_root_le_window_left a b e n hb hroot
      have hright := jExp_root_le_window_right a b e n hb hroot
      exfalso
      apply hnot
      rw [Finset.mem_Icc]
      exact ⟨hleft, hright⟩
    · simp [hroot]

/-- Target-window root bound: any theta root `n` of `j(Q^a;Q^b)` whose exponent
`jExp a b n` is at most a target degree `y` has `|n| ≤ jCoeffWindow a b y`.  (The
window constant `4(|a|+|b|+|y|+2)` dominates the quadratic root growth, so a
fixed window for `y` captures every root contributing at or below `y`.) -/
theorem jExp_root_le_target_window_right (a b y n : ℤ) (hb : 0 < b)
    (hle : jExp a b n ≤ y) :
    n ≤ jCoeffWindow a b y := by
  have htw : jExpTwice a b n ≤ 2 * y := by
    have := two_mul_jExp a b n; omega
  unfold jExpTwice at htw
  unfold jCoeffWindow
  have hrw : 4 * ((a.natAbs : ℤ) + (b.natAbs : ℤ) + (y.natAbs : ℤ) + 2) =
      4 * (|a| + |b| + |y| + 2) := by
    rw [Int.natCast_natAbs, Int.natCast_natAbs, Int.natCast_natAbs]
  rw [hrw]
  by_contra hlt
  have hn_gt : 4 * (|a| + |b| + |y| + 2) < n := by omega
  have hb1 : 1 ≤ b := by omega
  have hA : -|a| ≤ a := neg_abs_le a
  have hy : y ≤ |y| := le_abs_self y
  have hAn : 0 ≤ |a| := abs_nonneg a
  have hBn : 0 ≤ |b| := abs_nonneg b
  have hYn : 0 ≤ |y| := abs_nonneg y
  have hn_pos : 0 < n := by nlinarith
  have hbterm : n * (n - 1) ≤ b * (n * (n - 1)) := by nlinarith [mul_nonneg hn_pos.le (by omega : (0:ℤ) ≤ n - 1)]
  nlinarith [sq_nonneg (n - (2 * |a| + 2)), hn_gt, mul_nonneg hAn hn_pos.le]

theorem jExp_root_le_target_window_left (a b y n : ℤ) (hb : 0 < b)
    (hle : jExp a b n ≤ y) :
    -jCoeffWindow a b y ≤ n := by
  have htw : jExpTwice a b n ≤ 2 * y := by
    have := two_mul_jExp a b n; omega
  unfold jExpTwice at htw
  unfold jCoeffWindow
  have hrw : 4 * ((a.natAbs : ℤ) + (b.natAbs : ℤ) + (y.natAbs : ℤ) + 2) =
      4 * (|a| + |b| + |y| + 2) := by
    rw [Int.natCast_natAbs, Int.natCast_natAbs, Int.natCast_natAbs]
  rw [hrw]
  by_contra hlt
  have hn_lt : n < -(4 * (|a| + |b| + |y| + 2)) := by omega
  have hb1 : 1 ≤ b := by omega
  have hA : a ≤ |a| := le_abs_self a
  have hy : y ≤ |y| := le_abs_self y
  have hAn : 0 ≤ |a| := abs_nonneg a
  have hBn : 0 ≤ |b| := abs_nonneg b
  have hYn : 0 ≤ |y| := abs_nonneg y
  have hn_neg : n < 0 := by nlinarith
  have hbterm : n * (n - 1) ≤ b * (n * (n - 1)) := by
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hn_neg.le (by omega : n - 1 ≤ 0)]
  nlinarith [sq_nonneg (n + (2 * |a| + 2)), hn_lt, mul_nonneg hAn (by omega : (0:ℤ) ≤ -n)]

/-- Expand `jCoeff` on a fixed symmetric window that captures every root whose
exponent is at most `y`: valid whenever `e ≤ y` and `jCoeffWindow a b y ≤ W`.
Both the canonical `e`-window sum and the fixed `[-W,W]` sum equal the sum over
roots, which lie in `[-W,W]` by the target-window root bound. -/
theorem jCoeff_eq_sum_Icc_of_roots_le (a b e y W : ℤ) (hb : 0 < b)
    (hey : e ≤ y) (hW : jCoeffWindow a b y ≤ W) :
    jCoeff a b e =
      ∑ n ∈ Finset.Icc (-W) W, if jExp a b n = e then negOnePowIntQ n else 0 := by
  -- both sides reduce, over the union window, to the same root sum
  set U : Finset ℤ :=
    Finset.Icc (-(jCoeffWindow a b e)) (jCoeffWindow a b e) ∪ Finset.Icc (-W) W
    with hU
  have hroot_mem : ∀ n : ℤ, jExp a b n = e →
      n ∈ Finset.Icc (-(jCoeffWindow a b e)) (jCoeffWindow a b e) ∧
      n ∈ Finset.Icc (-W) W := by
    intro n hroot
    have hle : jExp a b n ≤ y := by rw [hroot]; exact hey
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨jExp_root_le_window_left a b e n hb hroot,
        jExp_root_le_window_right a b e n hb hroot⟩
    · rw [Finset.mem_Icc]
      have hl := jExp_root_le_target_window_left a b y n hb hle
      have hr := jExp_root_le_target_window_right a b y n hb hle
      omega
  have hleft : jCoeff a b e =
      ∑ n ∈ U, if jExp a b n = e then negOnePowIntQ n else 0 := by
    rw [jCoeff_eq_window_sum a b e hb]
    refine Finset.sum_subset (Finset.subset_union_left) ?_
    intro n _hn hnot
    by_cases hroot : jExp a b n = e
    · exact absurd (hroot_mem n hroot).1 hnot
    · simp [hroot]
  have hright : (∑ n ∈ Finset.Icc (-W) W,
        if jExp a b n = e then negOnePowIntQ n else 0) =
      ∑ n ∈ U, if jExp a b n = e then negOnePowIntQ n else 0 := by
    refine Finset.sum_subset (Finset.subset_union_right) ?_
    intro n _hn hnot
    by_cases hroot : jExp a b n = e
    · exact absurd (hroot_mem n hroot).2 hnot
    · simp [hroot]
  rw [hleft, hright]

theorem jCoeff_symm (a b e : ℤ) (hb : 0 < b) :
    jCoeff a b e = jCoeff (b - a) b e := by
  let W : ℤ := max (jCoeffWindow a b e) (jCoeffWindow (b - a) b e)
  have hWa : jCoeffWindow a b e ≤ W := by
    dsimp [W]
    exact le_max_left _ _
  have hWb : jCoeffWindow (b - a) b e ≤ W := by
    dsimp [W]
    exact le_max_right _ _
  rw [jCoeff_eq_sum_Icc_of_window_le a b e W hb hWa,
    jCoeff_eq_sum_Icc_of_window_le (b - a) b e W hb hWb]
  refine Finset.sum_bij' (fun n _ => -n) (fun n _ => -n) ?to_mem ?from_mem ?left_inv
    ?right_inv ?terms
  · intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    change -W ≤ -n ∧ -n ≤ W
    constructor <;> omega
  · intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    change -W ≤ -n ∧ -n ≤ W
    constructor <;> omega
  · intro n hn
    simp
  · intro n hn
    simp
  · intro n hn
    simp [jExp_symm, negOnePowIntQ_neg]

theorem jLaurent_symm (a b : ℤ) (hb : 0 < b) :
    jLaurent a b = jLaurent (b - a) b := by
  ext e
  change lcoeff (jLaurent a b) e = lcoeff (jLaurent (b - a) b) e
  rw [coeff_jLaurent, coeff_jLaurent, jCoeff_symm a b e hb]

def jShiftExp (a b k : ℤ) : ℤ :=
  -(b * k * (k - 1) / 2) - a * k

theorem two_mul_jShiftExp (a b k : ℤ) :
    2 * jShiftExp a b k = -b * k * (k - 1) - 2 * a * k := by
  unfold jShiftExp
  have hdiv : (2 : ℤ) ∣ b * k * (k - 1) := by
    have h : (2 : ℤ) ∣ (k - 1) * ((k - 1) + 1) :=
      Int.two_dvd_mul_add_one (k - 1)
    have h' : (2 : ℤ) ∣ k * (k - 1) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm,
        mul_left_comm, mul_assoc] using h
    simpa [mul_assoc] using dvd_mul_of_dvd_right h' b
  have hcancel : 2 * (b * k * (k - 1) / 2) = b * k * (k - 1) :=
    Int.mul_ediv_cancel' hdiv
  nlinarith

theorem jExp_shift (a b k n : ℤ) :
    jExp (a + b * k) b (n - k) = jExp a b n + jShiftExp a b k := by
  have hleft := two_mul_jExp (a + b * k) b (n - k)
  have hright := two_mul_jExp a b n
  have hshift := jExpTwice_shift a b k n
  have hcoeff := two_mul_jShiftExp a b k
  nlinarith

theorem jCoeff_shift (a b k e : ℤ) (hb : 0 < b) :
    jCoeff (a + b * k) b e =
      negOnePowIntQ k * jCoeff a b (e - jShiftExp a b k) := by
  let c : ℤ := jShiftExp a b k
  let wl : ℤ := jCoeffWindow (a + b * k) b e
  let wr : ℤ := jCoeffWindow a b (e - c)
  let L : ℤ := min (-wr) (-wl + k)
  let U : ℤ := max wr (wl + k)
  have hrightL : L ≤ -wr := by
    dsimp [L]
    exact min_le_left _ _
  have hrightU : wr ≤ U := by
    dsimp [U]
    exact le_max_left _ _
  have hleftL : L - k ≤ -wl := by
    have h : L ≤ -wl + k := by
      dsimp [L]
      exact min_le_right _ _
    omega
  have hleftU : wl ≤ U - k := by
    have h : wl + k ≤ U := by
      dsimp [U]
      exact le_max_right _ _
    omega
  rw [jCoeff_eq_sum_Icc_of_window_subset (a + b * k) b e (L - k) (U - k) hb
      hleftL hleftU,
    jCoeff_eq_sum_Icc_of_window_subset a b (e - c) L U hb hrightL hrightU]
  rw [Finset.mul_sum]
  refine Finset.sum_bij' (fun m _ => m + k) (fun n _ => n - k) ?to_mem ?from_mem
    ?left_inv ?right_inv ?terms
  · intro m hm
    rw [Finset.mem_Icc] at hm ⊢
    change L ≤ m + k ∧ m + k ≤ U
    constructor <;> omega
  · intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    change L - k ≤ n - k ∧ n - k ≤ U - k
    constructor <;> omega
  · intro m hm
    change m + k - k = m
    omega
  · intro n hn
    change n - k + k = n
    omega
  · intro m hm
    have hshift_m : jExp (a + b * k) b m = jExp a b (m + k) + c := by
      have h := jExp_shift a b k (m + k)
      dsimp [c]
      convert h using 1
      ring_nf
    by_cases hleft : jExp (a + b * k) b m = e
    · have hright : jExp a b (m + k) = e - c := by omega
      have hsign : negOnePowIntQ m = negOnePowIntQ k * negOnePowIntQ (m + k) := by
        have hsub := negOnePowIntQ_sub (m + k) k
        have hm : m + k - k = m := by ring
        rw [hm] at hsub
        rw [hsub]
        ring
      simp [hleft, hright, hsign]
    · have hright : ¬ jExp a b (m + k) = e - c := by
        intro hr
        apply hleft
        omega
      simp [hleft, hright]

theorem jLaurent_shift (a b k : ℤ) (hb : 0 < b) :
    jLaurent (a + b * k) b =
      negOnePowIntQ k • (Qpow (jShiftExp a b k) * jLaurent a b) := by
  ext e
  change lcoeff (jLaurent (a + b * k) b) e =
    lcoeff (negOnePowIntQ k • (Qpow (jShiftExp a b k) * jLaurent a b)) e
  rw [coeff_jLaurent, jCoeff_shift a b k e hb]
  change negOnePowIntQ k * jCoeff a b (e - jShiftExp a b k) =
    (negOnePowIntQ k • (Qpow (jShiftExp a b k) * jLaurent a b)).coeff e
  rw [HahnSeries.coeff_smul]
  change negOnePowIntQ k * jCoeff a b (e - jShiftExp a b k) =
    negOnePowIntQ k * lcoeff (Qpow (jShiftExp a b k) * jLaurent a b) e
  rw [lcoeff_Qpow_mul, coeff_jLaurent]

theorem jLaurent_shift_one (a b : ℤ) (hb : 0 < b) :
    jLaurent (a + b) b = -Qpow (-a) * jLaurent a b := by
  simpa [jShiftExp, negOnePowIntQ] using jLaurent_shift a b 1 hb

theorem jLaurent_zero (b : ℤ) (hb : 0 < b) :
    jLaurent 0 b = 0 := by
  have hsym : jLaurent 0 b = jLaurent b b := by
    simpa using jLaurent_symm 0 b hb
  have hshift : jLaurent b b = -jLaurent 0 b := by
    simpa using jLaurent_shift_one 0 b hb
  have hself : jLaurent 0 b = -jLaurent 0 b := by
    calc
      jLaurent 0 b = jLaurent b b := hsym
      _ = -jLaurent 0 b := hshift
  ext e
  change (jLaurent 0 b).coeff e = (0 : QLaurent).coeff e
  simp only [HahnSeries.coeff_zero]
  have hc := congrArg (fun s : QLaurent => s.coeff e) hself
  simp only [HahnSeries.coeff_neg] at hc
  linarith

theorem jLaurent_period_zero (b k : ℤ) (hb : 0 < b) :
    jLaurent (b * k) b = 0 := by
  have hshift := jLaurent_shift 0 b k hb
  simpa [jLaurent_zero b hb] using hshift

theorem jLaurent_self_zero (b : ℤ) (hb : 0 < b) :
    jLaurent b b = 0 := by
  simpa using jLaurent_period_zero b 1 hb

theorem jLaurent_neg (b : ℤ) (hb : 0 < b) :
    jLaurent (-b) b = 0 := by
  simpa using jLaurent_period_zero b (-1) hb

/-! ## JTP product bridge for `jLaurent` -/

theorem Qpow_ne_zero (e : ℤ) : Qpow e ≠ 0 := by
  intro h
  have hc := congrArg (fun s : QLaurent => lcoeff s e) h
  simp [lcoeff, Qpow] at hc

theorem Qpow_ne_one_of_pos {e : ℤ} (he : 0 < e) :
    Qpow e ≠ (1 : QLaurent) := by
  intro h
  have hc := congrArg (fun s : QLaurent => lcoeff s e) h
  simp [lcoeff, Qpow, he.ne'] at hc

theorem Qpow_inv (e : ℤ) :
    (Qpow e)⁻¹ = Qpow (-e) := by
  apply inv_eq_of_mul_eq_one_right
  rw [Qpow_mul]
  simp

theorem Qpow_inv_mul (a b : ℤ) :
    (Qpow a)⁻¹ * Qpow b = Qpow (b - a) := by
  rw [Qpow_inv, Qpow_mul]
  congr 1
  omega

theorem Qpow_pow_nat (e : ℤ) (n : ℕ) :
    (Qpow e) ^ n = Qpow (e * (n : ℤ)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, ih, Qpow_mul]
      congr 1
      norm_num
      ring

theorem Qpow_zpow (e n : ℤ) :
    (Qpow e) ^ n = Qpow (e * n) := by
  rcases n with n | n
  · exact Qpow_pow_nat e n
  · change (Qpow e) ^ (-(n + 1 : ℕ) : ℤ) =
      Qpow (e * (-(n + 1 : ℕ) : ℤ))
    rw [zpow_neg]
    change ((Qpow e) ^ (n + 1))⁻¹ =
      Qpow (e * (-(n + 1 : ℕ) : ℤ))
    rw [Qpow_pow_nat, Qpow_inv]
    congr 1
    ring

theorem negOnePowIntQ_cast_zpow (k : ℤ) :
    ((negOnePowIntQ k : ℚ) : QLaurent) = (-1 : QLaurent) ^ k := by
  cases k with
  | ofNat n =>
      simp [negOnePowIntQ]
  | negSucc n =>
      simp [negOnePowIntQ]
      have hsq : ((-1 : QLaurent) ^ (n + 1)) *
          ((-1 : QLaurent) ^ (n + 1)) = 1 := by
        rw [← pow_add]
        rw [show n + 1 + (n + 1) = 2 * (n + 1) by ring]
        rw [pow_mul]
        norm_num
      exact eq_inv_of_mul_eq_one_right hsq

theorem neg_Qpow_zpow (a n : ℤ) :
    (-Qpow a) ^ n = ((negOnePowIntQ n : ℚ) : QLaurent) * Qpow (a * n) := by
  rw [show (-Qpow a : QLaurent) = (-1 : QLaurent) * Qpow a by ring]
  rw [mul_zpow]
  rw [Qpow_zpow]
  rw [← negOnePowIntQ_cast_zpow]

private lemma int_l_mul_l_sub_one_div_two_nonneg (l : ℤ) :
    0 ≤ l * (l - 1) / 2 := by
  apply Int.ediv_nonneg _ (by omega)
  nlinarith [sq_nonneg (2 * l - 1)]

private lemma int_two_dvd_mul_pred (l : ℤ) :
    (2 : ℤ) ∣ l * (l - 1) := by
  rcases Int.even_or_odd l with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨m * (l - 1), by rw [hm]; ring⟩
  · exact ⟨l * m, by rw [hm]; ring⟩

/-- One bilateral `j(Q^a;Q^b)` monomial. -/
noncomputable def jTermLaurent (a b n : ℤ) : QLaurent :=
  ((negOnePowIntQ n : ℚ) : QLaurent) * Qpow (jExp a b n)

theorem lcoeff_mul_jTermLaurent (C : QLaurent) (a b n d : ℤ) :
    lcoeff (C * jTermLaurent a b n) d =
      negOnePowIntQ n * lcoeff C (d - jExp a b n) := by
  unfold jTermLaurent
  change lcoeff
      (C * ((HahnSeries.single (0 : ℤ) (negOnePowIntQ n : ℚ) : QLaurent) *
        Qpow (jExp a b n))) d =
    negOnePowIntQ n * lcoeff C (d - jExp a b n)
  rw [show C *
      ((HahnSeries.single (0 : ℤ) (negOnePowIntQ n : ℚ) : QLaurent) *
        Qpow (jExp a b n)) =
      (HahnSeries.single (0 : ℤ) (negOnePowIntQ n : ℚ) : QLaurent) *
        (Qpow (jExp a b n) * C) by ring]
  rw [lcoeff, HahnSeries.coeff_single_mul]
  simp only [sub_zero]
  change negOnePowIntQ n * lcoeff (Qpow (jExp a b n) * C) d =
    negOnePowIntQ n * lcoeff C (d - jExp a b n)
  rw [lcoeff_Qpow_mul]

@[simp] theorem lcoeff_jTermLaurent (a b n e : ℤ) :
    lcoeff (jTermLaurent a b n) e =
      if jExp a b n = e then negOnePowIntQ n else 0 := by
  unfold jTermLaurent Qpow lcoeff
  rw [show (((negOnePowIntQ n : ℚ) : QLaurent) *
        HahnSeries.single (jExp a b n) (1 : ℚ)) =
      HahnSeries.single (jExp a b n) (negOnePowIntQ n : ℚ) by
        change HahnSeries.single (0 : ℤ) (negOnePowIntQ n : ℚ) *
            HahnSeries.single (jExp a b n) (1 : ℚ) =
          HahnSeries.single (jExp a b n) (negOnePowIntQ n : ℚ)
        rw [HahnSeries.single_mul_single]
        simp]
  by_cases h : jExp a b n = e
  · simp [h]
  · have h' : e ≠ jExp a b n := fun he => h he.symm
    simp [h, h']

noncomputable def jTermFamily (a b : ℤ) (hb : 0 < b) :
    HahnSeries.SummableFamily ℤ ℚ ℤ where
  toFun n := jTermLaurent a b n
  isPWO_iUnion_support' := by
    have hbdd : BddBelow {e : ℤ | jCoeffLower a b ≤ e} :=
      ⟨jCoeffLower a b, by intro e he; exact he⟩
    refine hbdd.isWF.isPWO.mono ?_
    intro e he
    rw [Set.mem_iUnion] at he
    rcases he with ⟨n, hn⟩
    rw [HahnSeries.mem_support] at hn
    change lcoeff (jTermLaurent a b n) e ≠ 0 at hn
    rw [lcoeff_jTermLaurent] at hn
    by_cases hroot : jExp a b n = e
    · have hl := jExp_lower_bound a b n hb
      rw [hroot] at hl
      exact hl
    · simp [hroot] at hn
  finite_co_support' e := by
    refine (Set.finite_Icc (-(jCoeffWindow a b e)) (jCoeffWindow a b e)).subset ?_
    intro n hn
    rw [Set.mem_setOf_eq] at hn
    change (jTermLaurent a b n).coeff e ≠ 0 at hn
    change lcoeff (jTermLaurent a b n) e ≠ 0 at hn
    rw [lcoeff_jTermLaurent] at hn
    by_cases hroot : jExp a b n = e
    · simpa [Finset.mem_Icc] using
        (show -jCoeffWindow a b e ≤ n ∧ n ≤ jCoeffWindow a b e from
          ⟨jExp_root_le_window_left a b e n hb hroot,
            jExp_root_le_window_right a b e n hb hroot⟩)
    · simp [hroot] at hn

theorem jLaurent_eq_hsum_jTerm (a b : ℤ) (hb : 0 < b) :
    jLaurent a b = (jTermFamily a b hb).hsum := by
  ext e
  change lcoeff (jLaurent a b) e = lcoeff ((jTermFamily a b hb).hsum) e
  rw [coeff_jLaurent]
  symm
  change ((jTermFamily a b hb).hsum).coeff e = jCoeff a b e
  rw [HahnSeries.SummableFamily.coeff_hsum_eq_sum_of_subset
    (s := jTermFamily a b hb) (g := e)
    (t := Finset.Icc (-(jCoeffWindow a b e)) (jCoeffWindow a b e))]
  · rw [jCoeff_eq_window_sum a b e hb]
    refine Finset.sum_congr rfl ?_
    intro n _hn
    change (jTermLaurent a b n).coeff e =
      if jExp a b n = e then negOnePowIntQ n else 0
    change lcoeff (jTermLaurent a b n) e =
      if jExp a b n = e then negOnePowIntQ n else 0
    rw [lcoeff_jTermLaurent]
  · intro n hn
    change (jTermLaurent a b n).coeff e ≠ 0 at hn
    change lcoeff (jTermLaurent a b n) e ≠ 0 at hn
    rw [lcoeff_jTermLaurent] at hn
    by_cases hroot : jExp a b n = e
    · simpa [Finset.mem_Icc] using
        (show -jCoeffWindow a b e ≤ n ∧ n ≤ jCoeffWindow a b e from
          ⟨jExp_root_le_window_left a b e n hb hroot,
            jExp_root_le_window_right a b e n hb hroot⟩)
    · simp [hroot] at hn

/-! ## Formal Riemann addition relation for `jLaurent` -/

/-- Integer four-tuples indexing products of four bilateral `j`-terms. -/
structure ZQuad where
  p : ℤ
  q : ℤ
  r : ℤ
  s : ℤ
deriving DecidableEq

namespace ZQuad

def sum (u : ZQuad) : ℤ :=
  u.p + u.q + u.r + u.s

@[ext] theorem ext {u v : ZQuad}
    (hp : u.p = v.p) (hq : u.q = v.q) (hr : u.r = v.r) (hs : u.s = v.s) :
    u = v := by
  rcases u
  rcases v
  simp_all

def nestedEquiv : (((ℤ × ℤ) × ℤ) × ℤ) ≃ ZQuad where
  toFun u := ⟨u.1.1.1, u.1.1.2, u.1.2, u.2⟩
  invFun u := (((u.p, u.q), u.r), u.s)
  left_inv u := by
    rcases u with ⟨⟨⟨p, q⟩, r⟩, s⟩
    rfl
  right_inv u := by
    rcases u
    rfl

end ZQuad

noncomputable def jQuadTerm (a₁ a₂ a₃ a₄ M : ℤ) (u : ZQuad) : QLaurent :=
  jTermLaurent a₁ M u.p * jTermLaurent a₂ M u.q *
    jTermLaurent a₃ M u.r * jTermLaurent a₄ M u.s

def jQuadExp (a₁ a₂ a₃ a₄ M : ℤ) (u : ZQuad) : ℤ :=
  jExp a₁ M u.p + jExp a₂ M u.q + jExp a₃ M u.r + jExp a₄ M u.s

def jQuadExpTwice (a₁ a₂ a₃ a₄ M : ℤ) (u : ZQuad) : ℤ :=
  jExpTwice a₁ M u.p + jExpTwice a₂ M u.q +
    jExpTwice a₃ M u.r + jExpTwice a₄ M u.s

theorem two_mul_jQuadExp (a₁ a₂ a₃ a₄ M : ℤ) (u : ZQuad) :
    2 * jQuadExp a₁ a₂ a₃ a₄ M u =
      jQuadExpTwice a₁ a₂ a₃ a₄ M u := by
  unfold jQuadExp jQuadExpTwice
  nlinarith [two_mul_jExp a₁ M u.p, two_mul_jExp a₂ M u.q,
    two_mul_jExp a₃ M u.r, two_mul_jExp a₄ M u.s]

theorem negOnePowIntQ_eq_of_even_sub {m n : ℤ} (h : Even (m - n)) :
    negOnePowIntQ m = negOnePowIntQ n := by
  rw [negOnePowIntQ_eq_negOnePow, negOnePowIntQ_eq_negOnePow]
  exact_mod_cast ((Int.negOnePow_eq_iff m n).mpr h)

theorem negOnePowIntQ_add_one (n : ℤ) :
    negOnePowIntQ (n + 1) = -negOnePowIntQ n := by
  rw [negOnePowIntQ_add]
  norm_num [negOnePowIntQ]

theorem negOnePowIntQ_eq_neg_of_odd_sub {m n : ℤ} (h : Odd (m - n)) :
    negOnePowIntQ m = -negOnePowIntQ n := by
  have heven : Even (m - (n + 1)) := by
    rcases h with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    omega
  rw [negOnePowIntQ_eq_of_even_sub heven, negOnePowIntQ_add_one]

private theorem negOnePowIntQ_of_even {n : ℤ} (h : Even n) :
    negOnePowIntQ n = 1 := by
  rw [negOnePowIntQ_eq_negOnePow]
  rw [Int.negOnePow_even]
  · norm_num
  · exact h

private theorem negOnePowIntQ_of_odd {n : ℤ} (h : Odd n) :
    negOnePowIntQ n = -1 := by
  rcases h with ⟨k, hk⟩
  rw [hk]
  rw [negOnePowIntQ_add]
  rw [negOnePowIntQ_of_even (show Even (2 * k) from ⟨k, by ring⟩)]
  norm_num [negOnePowIntQ]

private theorem odd_of_not_two_dvd {n : ℤ} (h : ¬ 2 ∣ n) : Odd n := by
  rw [← Int.not_even_iff_odd]
  intro he
  rcases he with ⟨k, hk⟩
  apply h
  refine ⟨k, ?_⟩
  omega

private theorem not_two_dvd_of_odd {n : ℤ} (h : Odd n) : ¬ 2 ∣ n := by
  intro he
  rcases h with ⟨k, hk⟩
  rcases he with ⟨l, hl⟩
  omega

theorem jQuadTerm_eq_Qpow (a₁ a₂ a₃ a₄ M : ℤ) (u : ZQuad) :
    jQuadTerm a₁ a₂ a₃ a₄ M u =
      ((negOnePowIntQ u.sum : ℚ) : QLaurent) *
        Qpow (jQuadExp a₁ a₂ a₃ a₄ M u) := by
  rcases u with ⟨p, q, r, s⟩
  unfold jQuadTerm jTermLaurent jQuadExp ZQuad.sum
  have hsign :
      negOnePowIntQ p * negOnePowIntQ q * negOnePowIntQ r * negOnePowIntQ s =
        negOnePowIntQ (p + q + r + s) := by
    rw [negOnePowIntQ_add, negOnePowIntQ_add, negOnePowIntQ_add]
  change
    (HahnSeries.single (0 : ℤ) (negOnePowIntQ p : ℚ) *
          HahnSeries.single (jExp a₁ M p) (1 : ℚ) *
        (HahnSeries.single (0 : ℤ) (negOnePowIntQ q : ℚ) *
          HahnSeries.single (jExp a₂ M q) (1 : ℚ)) *
        (HahnSeries.single (0 : ℤ) (negOnePowIntQ r : ℚ) *
          HahnSeries.single (jExp a₃ M r) (1 : ℚ)) *
        (HahnSeries.single (0 : ℤ) (negOnePowIntQ s : ℚ) *
          HahnSeries.single (jExp a₄ M s) (1 : ℚ)) =
      HahnSeries.single (0 : ℤ) (negOnePowIntQ (p + q + r + s) : ℚ) *
        HahnSeries.single
          (jExp a₁ M p + jExp a₂ M q + jExp a₃ M r + jExp a₄ M s) (1 : ℚ))
  rw [HahnSeries.single_mul_single, HahnSeries.single_mul_single,
    HahnSeries.single_mul_single, HahnSeries.single_mul_single,
    HahnSeries.single_mul_single, HahnSeries.single_mul_single,
    HahnSeries.single_mul_single]
  have hsign_assoc :
      negOnePowIntQ p * (negOnePowIntQ q * (negOnePowIntQ r * negOnePowIntQ s)) =
        negOnePowIntQ (p + (q + (r + s))) := by
    rw [show p + (q + (r + s)) = p + q + r + s by ring]
    rw [← hsign]
    ring
  simp [hsign_assoc, add_assoc, mul_assoc]

@[simp] theorem lcoeff_jQuadTerm (a₁ a₂ a₃ a₄ M : ℤ) (u : ZQuad) (e : ℤ) :
    lcoeff (jQuadTerm a₁ a₂ a₃ a₄ M u) e =
      if jQuadExp a₁ a₂ a₃ a₄ M u = e then negOnePowIntQ u.sum else 0 := by
  rw [jQuadTerm_eq_Qpow]
  unfold lcoeff Qpow
  change (HahnSeries.single (0 : ℤ) (negOnePowIntQ u.sum : ℚ) *
      HahnSeries.single (jQuadExp a₁ a₂ a₃ a₄ M u) (1 : ℚ)).coeff e =
    if jQuadExp a₁ a₂ a₃ a₄ M u = e then negOnePowIntQ u.sum else 0
  rw [HahnSeries.single_mul_single]
  by_cases h : jQuadExp a₁ a₂ a₃ a₄ M u = e
  · simp [h]
  · have h' : e ≠ jQuadExp a₁ a₂ a₃ a₄ M u := fun he => h he.symm
    simp [h, h']

@[simp] theorem coeff_jQuadTerm' (a₁ a₂ a₃ a₄ M : ℤ) (u : ZQuad) (e : ℤ) :
    (jQuadTerm a₁ a₂ a₃ a₄ M u).coeff e =
      if jQuadExp a₁ a₂ a₃ a₄ M u = e then negOnePowIntQ u.sum else 0 := by
  exact lcoeff_jQuadTerm a₁ a₂ a₃ a₄ M u e

@[simp] theorem lcoeff_Qpow_mul_jQuadTerm
    (c a₁ a₂ a₃ a₄ M : ℤ) (u : ZQuad) (e : ℤ) :
    lcoeff (Qpow c * jQuadTerm a₁ a₂ a₃ a₄ M u) e =
      if c + jQuadExp a₁ a₂ a₃ a₄ M u = e then negOnePowIntQ u.sum else 0 := by
  rw [lcoeff_Qpow_mul, lcoeff_jQuadTerm]
  by_cases h : c + jQuadExp a₁ a₂ a₃ a₄ M u = e
  · have h' : jQuadExp a₁ a₂ a₃ a₄ M u = e - c := by omega
    simp [h']
  · have h' : ¬ jQuadExp a₁ a₂ a₃ a₄ M u = e - c := by
      intro hroot
      apply h
      omega
    simp [h, h']

@[simp] theorem coeff_Qpow_mul_jQuadTerm' (c a₁ a₂ a₃ a₄ M : ℤ) (u : ZQuad) (e : ℤ) :
    (Qpow c * jQuadTerm a₁ a₂ a₃ a₄ M u).coeff e =
      if c + jQuadExp a₁ a₂ a₃ a₄ M u = e then negOnePowIntQ u.sum else 0 := by
  exact lcoeff_Qpow_mul_jQuadTerm c a₁ a₂ a₃ a₄ M u e

noncomputable def jQuadFamily (a₁ a₂ a₃ a₄ M : ℤ) (hM : 0 < M) :
    HahnSeries.SummableFamily ℤ ℚ ZQuad :=
  HahnSeries.SummableFamily.Equiv ZQuad.nestedEquiv
    ((((jTermFamily a₁ M hM).mul (jTermFamily a₂ M hM)).mul
      (jTermFamily a₃ M hM)).mul (jTermFamily a₄ M hM))

@[simp] theorem jQuadFamily_apply (a₁ a₂ a₃ a₄ M : ℤ) (hM : 0 < M) (u : ZQuad) :
    jQuadFamily a₁ a₂ a₃ a₄ M hM u =
      jQuadTerm a₁ a₂ a₃ a₄ M u := by
  rcases u with ⟨p, q, r, s⟩
  unfold jQuadFamily jQuadTerm
  rfl

theorem jQuadFamily_hsum (a₁ a₂ a₃ a₄ M : ℤ) (hM : 0 < M) :
    (jQuadFamily a₁ a₂ a₃ a₄ M hM).hsum =
      jLaurent a₁ M * jLaurent a₂ M * jLaurent a₃ M * jLaurent a₄ M := by
  unfold jQuadFamily
  rw [HahnSeries.SummableFamily.hsum_equiv]
  rw [HahnSeries.SummableFamily.hsum_mul]
  rw [HahnSeries.SummableFamily.hsum_mul]
  rw [HahnSeries.SummableFamily.hsum_mul]
  rw [← jLaurent_eq_hsum_jTerm a₁ M hM,
    ← jLaurent_eq_hsum_jTerm a₂ M hM,
    ← jLaurent_eq_hsum_jTerm a₃ M hM,
    ← jLaurent_eq_hsum_jTerm a₄ M hM]

inductive RiemannSide where
  | lhs
  | rhs₁
  | rhs₂
deriving DecidableEq

def riemannSideEmb (side : RiemannSide) : ZQuad ↪ RiemannSide × ZQuad where
  toFun u := (side, u)
  inj' := by
    intro u v h
    exact (Prod.mk.inj h).2

@[simp] theorem riemannSideEmb_apply (side : RiemannSide) (u : ZQuad) :
    riemannSideEmb side u = (side, u) := rfl

theorem riemannSideEmb_notin_range {side side' : RiemannSide} (h : side' ≠ side)
    (u : ZQuad) :
    (side', u) ∉ Set.range (riemannSideEmb side) := by
  rintro ⟨v, hv⟩
  exact h (Prod.mk.inj hv).1.symm

@[simp] theorem embDomain_riemannSide_same
    (F : HahnSeries.SummableFamily ℤ ℚ ZQuad) (side : RiemannSide) (u : ZQuad) :
    F.embDomain (riemannSideEmb side) (side, u) = F u := by
  exact HahnSeries.SummableFamily.embDomain_image F (riemannSideEmb side)

@[simp] theorem embDomain_riemannSide_ne
    (F : HahnSeries.SummableFamily ℤ ℚ ZQuad) {side side' : RiemannSide}
    (h : side' ≠ side) (u : ZQuad) :
    F.embDomain (riemannSideEmb side) (side', u) = 0 := by
  exact HahnSeries.SummableFamily.embDomain_notin_range F (riemannSideEmb side)
    (riemannSideEmb_notin_range h u)

noncomputable def riemannDiffFamily (M : ℤ) (hM : 0 < M)
    (A B C D : ℤ) : HahnSeries.SummableFamily ℤ ℚ (RiemannSide × ZQuad) :=
  (jQuadFamily (A + C) (A - C) (B + D) (B - D) M hM).embDomain
      (riemannSideEmb RiemannSide.lhs) -
    (jQuadFamily (A + D) (A - D) (B + C) (B - C) M hM).embDomain
      (riemannSideEmb RiemannSide.rhs₁) -
      ((Qpow (B - C)) •
        jQuadFamily (A + B) (A - B) (C + D) (C - D) M hM).embDomain
        (riemannSideEmb RiemannSide.rhs₂)

@[simp] theorem riemannDiffFamily_lhs_apply (M : ℤ) (hM : 0 < M)
    (A B C D : ℤ) (u : ZQuad) :
    riemannDiffFamily M hM A B C D (RiemannSide.lhs, u) =
      jQuadTerm (A + C) (A - C) (B + D) (B - D) M u := by
  unfold riemannDiffFamily
  simp

@[simp] theorem riemannDiffFamily_rhs₁_apply (M : ℤ) (hM : 0 < M)
    (A B C D : ℤ) (u : ZQuad) :
    riemannDiffFamily M hM A B C D (RiemannSide.rhs₁, u) =
      -jQuadTerm (A + D) (A - D) (B + C) (B - C) M u := by
  unfold riemannDiffFamily
  simp

@[simp] theorem riemannDiffFamily_rhs₂_apply (M : ℤ) (hM : 0 < M)
    (A B C D : ℤ) (u : ZQuad) :
    riemannDiffFamily M hM A B C D (RiemannSide.rhs₂, u) =
      -(Qpow (B - C) * jQuadTerm (A + B) (A - B) (C + D) (C - D) M u) := by
  unfold riemannDiffFamily
  simp
  rfl

theorem riemannDiffFamily_hsum (M : ℤ) (hM : 0 < M) (A B C D : ℤ) :
    (riemannDiffFamily M hM A B C D).hsum =
      jLaurent (A + C) M * jLaurent (A - C) M *
          jLaurent (B + D) M * jLaurent (B - D) M -
        jLaurent (A + D) M * jLaurent (A - D) M *
          jLaurent (B + C) M * jLaurent (B - C) M -
          Qpow (B - C) * jLaurent (A + B) M * jLaurent (A - B) M *
            jLaurent (C + D) M * jLaurent (C - D) M := by
  unfold riemannDiffFamily
  rw [HahnSeries.SummableFamily.hsum_sub, HahnSeries.SummableFamily.hsum_sub]
  rw [HahnSeries.SummableFamily.hsum_embDomain,
    HahnSeries.SummableFamily.hsum_embDomain,
    HahnSeries.SummableFamily.hsum_embDomain]
  rw [HahnSeries.SummableFamily.hsum_smul]
  rw [jQuadFamily_hsum, jQuadFamily_hsum, jQuadFamily_hsum]
  ring

def riemannEvenLR (u : ZQuad) : ZQuad where
  p := (u.p + u.q + u.r - u.s) / 2
  q := (u.p + u.q - u.r + u.s) / 2
  r := (u.r + u.s + u.p - u.q) / 2
  s := (u.r + u.s - u.p + u.q) / 2

def riemannOddLR₂ (u : ZQuad) : ZQuad where
  p := (u.p + u.q + u.r + u.s - 1) / 2
  q := (u.p + u.q - u.r - u.s + 1) / 2
  r := (u.p - u.q + u.r - u.s + 1) / 2
  s := (u.p - u.q - u.r + u.s + 1) / 2

def riemannRhs₁OddRhs₂ (u : ZQuad) : ZQuad where
  p := (u.p + u.q + u.r + u.s - 1) / 2
  q := (u.p + u.q - u.r - u.s + 1) / 2
  r := (u.p - u.q + u.r - u.s + 1) / 2
  s := (-u.p + u.q + u.r - u.s + 1) / 2

def riemannRhs₂EvenRhs₁ (u : ZQuad) : ZQuad where
  p := (u.p + u.q + u.r - u.s) / 2
  q := (u.p + u.q - u.r + u.s) / 2
  r := (u.p - u.q + u.r + u.s) / 2
  s := (u.p - u.q - u.r - u.s) / 2 + 1

private theorem riemannEvenLR_sum_eq (u : ZQuad) (h : 2 ∣ u.sum) :
    (riemannEvenLR u).sum = u.sum := by
  rcases u with ⟨p, q, r, s⟩
  rcases h with ⟨k, hk⟩
  change p + q + r + s = 2 * k at hk
  unfold riemannEvenLR ZQuad.sum
  dsimp
  have hpdiv : 2 ∣ p + q + r - s := by refine ⟨k - s, by omega⟩
  have hqdiv : 2 ∣ p + q - r + s := by refine ⟨k - r, by omega⟩
  have hrdiv : 2 ∣ r + s + p - q := by refine ⟨k - q, by omega⟩
  have hsdiv : 2 ∣ r + s - p + q := by refine ⟨k - p, by omega⟩
  have hp : 2 * ((p + q + r - s) / 2) = p + q + r - s :=
    Int.mul_ediv_cancel' hpdiv
  have hq : 2 * ((p + q - r + s) / 2) = p + q - r + s :=
    Int.mul_ediv_cancel' hqdiv
  have hr : 2 * ((r + s + p - q) / 2) = r + s + p - q :=
    Int.mul_ediv_cancel' hrdiv
  have hs : 2 * ((r + s - p + q) / 2) = r + s - p + q :=
    Int.mul_ediv_cancel' hsdiv
  omega

private theorem riemannEvenLR_even (u : ZQuad) (h : 2 ∣ u.sum) :
    2 ∣ (riemannEvenLR u).sum := by
  rw [riemannEvenLR_sum_eq u h]
  exact h

private theorem riemannEvenLR_involutive (u : ZQuad) (h : 2 ∣ u.sum) :
    riemannEvenLR (riemannEvenLR u) = u := by
  rcases u with ⟨p, q, r, s⟩
  rcases h with ⟨k, hk⟩
  change p + q + r + s = 2 * k at hk
  unfold riemannEvenLR
  dsimp
  have hpdiv : 2 ∣ p + q + r - s := by refine ⟨k - s, by omega⟩
  have hqdiv : 2 ∣ p + q - r + s := by refine ⟨k - r, by omega⟩
  have hrdiv : 2 ∣ r + s + p - q := by refine ⟨k - q, by omega⟩
  have hsdiv : 2 ∣ r + s - p + q := by refine ⟨k - p, by omega⟩
  have hp : 2 * ((p + q + r - s) / 2) = p + q + r - s :=
    Int.mul_ediv_cancel' hpdiv
  have hq : 2 * ((p + q - r + s) / 2) = p + q - r + s :=
    Int.mul_ediv_cancel' hqdiv
  have hr : 2 * ((r + s + p - q) / 2) = r + s + p - q :=
    Int.mul_ediv_cancel' hrdiv
  have hs : 2 * ((r + s - p + q) / 2) = r + s - p + q :=
    Int.mul_ediv_cancel' hsdiv
  ext <;> dsimp
  · have hdiv :
        2 ∣ (p + q + r - s) / 2 + (p + q - r + s) / 2 +
            (r + s + p - q) / 2 - (r + s - p + q) / 2 := by
      refine ⟨p, by omega⟩
    have hhalf := Int.mul_ediv_cancel' hdiv
    omega
  · have hdiv :
        2 ∣ (p + q + r - s) / 2 + (p + q - r + s) / 2 -
            (r + s + p - q) / 2 + (r + s - p + q) / 2 := by
      refine ⟨q, by omega⟩
    have hhalf := Int.mul_ediv_cancel' hdiv
    omega
  · have hdiv :
        2 ∣ (r + s + p - q) / 2 + (r + s - p + q) / 2 +
            (p + q + r - s) / 2 - (p + q - r + s) / 2 := by
      refine ⟨r, by omega⟩
    have hhalf := Int.mul_ediv_cancel' hdiv
    omega
  · have hdiv :
        2 ∣ (r + s + p - q) / 2 + (r + s - p + q) / 2 -
            (p + q + r - s) / 2 + (p + q - r + s) / 2 := by
      refine ⟨s, by omega⟩
    have hhalf := Int.mul_ediv_cancel' hdiv
    omega

private theorem riemannOddLR₂_sum_eq (u : ZQuad) (h : ¬ 2 ∣ u.sum) :
    (riemannOddLR₂ u).sum = 2 * u.p + 1 := by
  rcases u with ⟨p, q, r, s⟩
  have hodd : Odd (p + q + r + s) := odd_of_not_two_dvd h
  rcases hodd with ⟨k, hk⟩
  change p + q + r + s = 2 * k + 1 at hk
  unfold riemannOddLR₂ ZQuad.sum
  dsimp
  have hxdiv : 2 ∣ p + q + r + s - 1 := by refine ⟨k, by omega⟩
  have hydiv : 2 ∣ p + q - r - s + 1 := by refine ⟨k - r - s + 1, by omega⟩
  have hzdiv : 2 ∣ p - q + r - s + 1 := by refine ⟨k - q - s + 1, by omega⟩
  have hwdiv : 2 ∣ p - q - r + s + 1 := by refine ⟨k - q - r + 1, by omega⟩
  have hx : 2 * ((p + q + r + s - 1) / 2) = p + q + r + s - 1 :=
    Int.mul_ediv_cancel' hxdiv
  have hy : 2 * ((p + q - r - s + 1) / 2) = p + q - r - s + 1 :=
    Int.mul_ediv_cancel' hydiv
  have hz : 2 * ((p - q + r - s + 1) / 2) = p - q + r - s + 1 :=
    Int.mul_ediv_cancel' hzdiv
  have hw : 2 * ((p - q - r + s + 1) / 2) = p - q - r + s + 1 :=
    Int.mul_ediv_cancel' hwdiv
  omega

private theorem riemannOddLR₂_odd (u : ZQuad) (h : ¬ 2 ∣ u.sum) :
    ¬ 2 ∣ (riemannOddLR₂ u).sum := by
  have hsum := riemannOddLR₂_sum_eq u h
  apply not_two_dvd_of_odd
  refine ⟨u.p, ?_⟩
  omega

private theorem riemannOddLR₂_involutive (u : ZQuad) (h : ¬ 2 ∣ u.sum) :
    riemannOddLR₂ (riemannOddLR₂ u) = u := by
  rcases u with ⟨p, q, r, s⟩
  have hodd : Odd (p + q + r + s) := odd_of_not_two_dvd h
  rcases hodd with ⟨k, hk⟩
  change p + q + r + s = 2 * k + 1 at hk
  unfold riemannOddLR₂
  dsimp
  have hxdiv : 2 ∣ p + q + r + s - 1 := by refine ⟨k, by omega⟩
  have hydiv : 2 ∣ p + q - r - s + 1 := by refine ⟨k - r - s + 1, by omega⟩
  have hzdiv : 2 ∣ p - q + r - s + 1 := by refine ⟨k - q - s + 1, by omega⟩
  have hwdiv : 2 ∣ p - q - r + s + 1 := by refine ⟨k - q - r + 1, by omega⟩
  have hx : 2 * ((p + q + r + s - 1) / 2) = p + q + r + s - 1 :=
    Int.mul_ediv_cancel' hxdiv
  have hy : 2 * ((p + q - r - s + 1) / 2) = p + q - r - s + 1 :=
    Int.mul_ediv_cancel' hydiv
  have hz : 2 * ((p - q + r - s + 1) / 2) = p - q + r - s + 1 :=
    Int.mul_ediv_cancel' hzdiv
  have hw : 2 * ((p - q - r + s + 1) / 2) = p - q - r + s + 1 :=
    Int.mul_ediv_cancel' hwdiv
  ext <;> dsimp
  · have hdiv :
        2 ∣ (p + q + r + s - 1) / 2 + (p + q - r - s + 1) / 2 +
              (p - q + r - s + 1) / 2 +
            (p - q - r + s + 1) / 2 - 1 := by
      refine ⟨p, by omega⟩
    have hhalf := Int.mul_ediv_cancel' hdiv
    omega
  · have hdiv :
        2 ∣ (p + q + r + s - 1) / 2 + (p + q - r - s + 1) / 2 -
              (p - q + r - s + 1) / 2 -
            (p - q - r + s + 1) / 2 + 1 := by
      refine ⟨q, by omega⟩
    have hhalf := Int.mul_ediv_cancel' hdiv
    omega
  · have hdiv :
        2 ∣ (p + q + r + s - 1) / 2 - (p + q - r - s + 1) / 2 +
              (p - q + r - s + 1) / 2 -
            (p - q - r + s + 1) / 2 + 1 := by
      refine ⟨r, by omega⟩
    have hhalf := Int.mul_ediv_cancel' hdiv
    omega
  · have hdiv :
        2 ∣ (p + q + r + s - 1) / 2 - (p + q - r - s + 1) / 2 -
              (p - q + r - s + 1) / 2 +
            (p - q - r + s + 1) / 2 + 1 := by
      refine ⟨s, by omega⟩
    have hhalf := Int.mul_ediv_cancel' hdiv
    omega

private theorem riemannRhs₁OddRhs₂_even (u : ZQuad) (h : ¬ 2 ∣ u.sum) :
    2 ∣ (riemannRhs₁OddRhs₂ u).sum := by
  rcases u with ⟨p, q, r, s⟩
  have hodd : Odd (p + q + r + s) := odd_of_not_two_dvd h
  rcases hodd with ⟨k, hk⟩
  change p + q + r + s = 2 * k + 1 at hk
  unfold riemannRhs₁OddRhs₂ ZQuad.sum
  dsimp
  have hxdiv : 2 ∣ p + q + r + s - 1 := by refine ⟨k, by omega⟩
  have hydiv : 2 ∣ p + q - r - s + 1 := by refine ⟨k - r - s + 1, by omega⟩
  have hzdiv : 2 ∣ p - q + r - s + 1 := by refine ⟨k - q - s + 1, by omega⟩
  have hwdiv : 2 ∣ -p + q + r - s + 1 := by refine ⟨k - p - s + 1, by omega⟩
  have hx : 2 * ((p + q + r + s - 1) / 2) = p + q + r + s - 1 :=
    Int.mul_ediv_cancel' hxdiv
  have hy : 2 * ((p + q - r - s + 1) / 2) = p + q - r - s + 1 :=
    Int.mul_ediv_cancel' hydiv
  have hz : 2 * ((p - q + r - s + 1) / 2) = p - q + r - s + 1 :=
    Int.mul_ediv_cancel' hzdiv
  have hw : 2 * ((-p + q + r - s + 1) / 2) = -p + q + r - s + 1 :=
    Int.mul_ediv_cancel' hwdiv
  refine ⟨k - s + 1, ?_⟩
  omega

private theorem riemannRhs₂EvenRhs₁_odd (u : ZQuad) (h : 2 ∣ u.sum) :
    ¬ 2 ∣ (riemannRhs₂EvenRhs₁ u).sum := by
  rcases u with ⟨x, y, z, w⟩
  rcases h with ⟨k, hk⟩
  change x + y + z + w = 2 * k at hk
  unfold riemannRhs₂EvenRhs₁ ZQuad.sum
  dsimp
  have hpdiv : 2 ∣ x + y + z - w := by refine ⟨k - w, by omega⟩
  have hqdiv : 2 ∣ x + y - z + w := by refine ⟨k - z, by omega⟩
  have hrdiv : 2 ∣ x - y + z + w := by refine ⟨k - y, by omega⟩
  have hsdiv : 2 ∣ x - y - z - w := by refine ⟨x - k, by omega⟩
  have hp : 2 * ((x + y + z - w) / 2) = x + y + z - w :=
    Int.mul_ediv_cancel' hpdiv
  have hq : 2 * ((x + y - z + w) / 2) = x + y - z + w :=
    Int.mul_ediv_cancel' hqdiv
  have hr : 2 * ((x - y + z + w) / 2) = x - y + z + w :=
    Int.mul_ediv_cancel' hrdiv
  have hs : 2 * ((x - y - z - w) / 2) = x - y - z - w :=
    Int.mul_ediv_cancel' hsdiv
  apply not_two_dvd_of_odd
  refine ⟨x, ?_⟩
  omega

private theorem riemannRhs₁OddRhs₂_left_inverse (u : ZQuad) (h : ¬ 2 ∣ u.sum) :
    riemannRhs₂EvenRhs₁ (riemannRhs₁OddRhs₂ u) = u := by
  rcases u with ⟨p, q, r, s⟩
  have hodd : Odd (p + q + r + s) := odd_of_not_two_dvd h
  rcases hodd with ⟨k, hk⟩
  change p + q + r + s = 2 * k + 1 at hk
  unfold riemannRhs₁OddRhs₂ riemannRhs₂EvenRhs₁
  dsimp
  have hxdiv : 2 ∣ p + q + r + s - 1 := by refine ⟨k, by omega⟩
  have hydiv : 2 ∣ p + q - r - s + 1 := by refine ⟨k - r - s + 1, by omega⟩
  have hzdiv : 2 ∣ p - q + r - s + 1 := by refine ⟨k - q - s + 1, by omega⟩
  have hwdiv : 2 ∣ -p + q + r - s + 1 := by refine ⟨k - p - s + 1, by omega⟩
  have hx : 2 * ((p + q + r + s - 1) / 2) = p + q + r + s - 1 :=
    Int.mul_ediv_cancel' hxdiv
  have hy : 2 * ((p + q - r - s + 1) / 2) = p + q - r - s + 1 :=
    Int.mul_ediv_cancel' hydiv
  have hz : 2 * ((p - q + r - s + 1) / 2) = p - q + r - s + 1 :=
    Int.mul_ediv_cancel' hzdiv
  have hw : 2 * ((-p + q + r - s + 1) / 2) = -p + q + r - s + 1 :=
    Int.mul_ediv_cancel' hwdiv
  ext <;> dsimp
  · have hdiv :
        2 ∣ (p + q + r + s - 1) / 2 + (p + q - r - s + 1) / 2 +
            (p - q + r - s + 1) / 2 - (-p + q + r - s + 1) / 2 := by
      refine ⟨p, by omega⟩
    have hhalf := Int.mul_ediv_cancel' hdiv
    omega
  · have hdiv :
        2 ∣ (p + q + r + s - 1) / 2 + (p + q - r - s + 1) / 2 -
            (p - q + r - s + 1) / 2 + (-p + q + r - s + 1) / 2 := by
      refine ⟨q, by omega⟩
    have hhalf := Int.mul_ediv_cancel' hdiv
    omega
  · have hdiv :
        2 ∣ (p + q + r + s - 1) / 2 - (p + q - r - s + 1) / 2 +
            (p - q + r - s + 1) / 2 + (-p + q + r - s + 1) / 2 := by
      refine ⟨r, by omega⟩
    have hhalf := Int.mul_ediv_cancel' hdiv
    omega
  · have hdiv :
        2 ∣ (p + q + r + s - 1) / 2 - (p + q - r - s + 1) / 2 -
            (p - q + r - s + 1) / 2 - (-p + q + r - s + 1) / 2 := by
      refine ⟨s - 1, by omega⟩
    have hhalf := Int.mul_ediv_cancel' hdiv
    omega

private theorem riemannRhs₂EvenRhs₁_right_inverse (u : ZQuad) (h : 2 ∣ u.sum) :
    riemannRhs₁OddRhs₂ (riemannRhs₂EvenRhs₁ u) = u := by
  rcases u with ⟨x, y, z, w⟩
  rcases h with ⟨k, hk⟩
  change x + y + z + w = 2 * k at hk
  unfold riemannRhs₂EvenRhs₁ riemannRhs₁OddRhs₂
  dsimp
  have hpdiv : 2 ∣ x + y + z - w := by refine ⟨k - w, by omega⟩
  have hqdiv : 2 ∣ x + y - z + w := by refine ⟨k - z, by omega⟩
  have hrdiv : 2 ∣ x - y + z + w := by refine ⟨k - y, by omega⟩
  have hsdiv : 2 ∣ x - y - z - w := by refine ⟨x - k, by omega⟩
  have hp : 2 * ((x + y + z - w) / 2) = x + y + z - w :=
    Int.mul_ediv_cancel' hpdiv
  have hq : 2 * ((x + y - z + w) / 2) = x + y - z + w :=
    Int.mul_ediv_cancel' hqdiv
  have hr : 2 * ((x - y + z + w) / 2) = x - y + z + w :=
    Int.mul_ediv_cancel' hrdiv
  have hs : 2 * ((x - y - z - w) / 2) = x - y - z - w :=
    Int.mul_ediv_cancel' hsdiv
  ext <;> dsimp
  · have hdiv :
        2 ∣ (x + y + z - w) / 2 + (x + y - z + w) / 2 +
              (x - y + z + w) / 2 +
            ((x - y - z - w) / 2 + 1) - 1 := by
      refine ⟨x, by omega⟩
    have hhalf := Int.mul_ediv_cancel' hdiv
    omega
  · have hdiv :
        2 ∣ (x + y + z - w) / 2 + (x + y - z + w) / 2 -
              (x - y + z + w) / 2 -
            ((x - y - z - w) / 2 + 1) + 1 := by
      refine ⟨y, by omega⟩
    have hhalf := Int.mul_ediv_cancel' hdiv
    omega
  · have hdiv :
        2 ∣ (x + y + z - w) / 2 - (x + y - z + w) / 2 +
              (x - y + z + w) / 2 -
            ((x - y - z - w) / 2 + 1) + 1 := by
      refine ⟨z, by omega⟩
    have hhalf := Int.mul_ediv_cancel' hdiv
    omega
  · have hdiv :
        2 ∣ -((x + y + z - w) / 2) + (x + y - z + w) / 2 +
              (x - y + z + w) / 2 -
            ((x - y - z - w) / 2 + 1) + 1 := by
      refine ⟨w, by omega⟩
    have hhalf := Int.mul_ediv_cancel' hdiv
    omega
private theorem riemann_evenLR_expTwice_of_halves
    (M A B C D p q r s p' q' r' s' : ℤ)
    (hp : 2 * p' = p + q + r - s)
    (hq : 2 * q' = p + q - r + s)
    (hr : 2 * r' = r + s + p - q)
    (hs : 2 * s' = r + s - p + q) :
    jExpTwice (A + C) M p + jExpTwice (A - C) M q +
        jExpTwice (B + D) M r + jExpTwice (B - D) M s =
      jExpTwice (A + D) M p' + jExpTwice (A - D) M q' +
        jExpTwice (B + C) M r' + jExpTwice (B - C) M s' := by
  apply Int.cast_injective (α := ℚ)
  have hpQ : (p' : ℚ) = ((p + q + r - s : ℤ) : ℚ) / 2 := by
    norm_num [← hp]
  have hqQ : (q' : ℚ) = ((p + q - r + s : ℤ) : ℚ) / 2 := by
    norm_num [← hq]
  have hrQ : (r' : ℚ) = ((r + s + p - q : ℤ) : ℚ) / 2 := by
    norm_num [← hr]
  have hsQ : (s' : ℚ) = ((r + s - p + q : ℤ) : ℚ) / 2 := by
    norm_num [← hs]
  simp only [Int.cast_add]
  unfold jExpTwice
  norm_num [hpQ, hqQ, hrQ, hsQ]
  ring

private theorem riemann_oddLR₂_expTwice_of_halves
    (M A B C D p q r s x y z w : ℤ)
    (hx : 2 * x = p + q + r + s - 1)
    (hy : 2 * y = p + q - r - s + 1)
    (hz : 2 * z = p - q + r - s + 1)
    (hw : 2 * w = p - q - r + s + 1) :
    jExpTwice (A + C) M p + jExpTwice (A - C) M q +
        jExpTwice (B + D) M r + jExpTwice (B - D) M s =
      2 * (B - C) +
        (jExpTwice (A + B) M x + jExpTwice (A - B) M y +
          jExpTwice (C + D) M z + jExpTwice (C - D) M w) := by
  apply Int.cast_injective (α := ℚ)
  have hxQ : (x : ℚ) = ((p + q + r + s - 1 : ℤ) : ℚ) / 2 := by
    norm_num [← hx]
  have hyQ : (y : ℚ) = ((p + q - r - s + 1 : ℤ) : ℚ) / 2 := by
    norm_num [← hy]
  have hzQ : (z : ℚ) = ((p - q + r - s + 1 : ℤ) : ℚ) / 2 := by
    norm_num [← hz]
  have hwQ : (w : ℚ) = ((p - q - r + s + 1 : ℤ) : ℚ) / 2 := by
    norm_num [← hw]
  simp only [Int.cast_add]
  unfold jExpTwice
  norm_num [hxQ, hyQ, hzQ, hwQ]
  ring

private theorem riemann_rhs₁Odd_rhs₂_expTwice_of_halves
    (M A B C D p q r s x y z w : ℤ)
    (hx : 2 * x = p + q + r + s - 1)
    (hy : 2 * y = p + q - r - s + 1)
    (hz : 2 * z = p - q + r - s + 1)
    (hw : 2 * w = -p + q + r - s + 1) :
    jExpTwice (A + D) M p + jExpTwice (A - D) M q +
        jExpTwice (B + C) M r + jExpTwice (B - C) M s =
      2 * (B - C) +
        (jExpTwice (A + B) M x + jExpTwice (A - B) M y +
          jExpTwice (C + D) M z + jExpTwice (C - D) M w) := by
  apply Int.cast_injective (α := ℚ)
  have hxQ : (x : ℚ) = ((p + q + r + s - 1 : ℤ) : ℚ) / 2 := by
    norm_num [← hx]
  have hyQ : (y : ℚ) = ((p + q - r - s + 1 : ℤ) : ℚ) / 2 := by
    norm_num [← hy]
  have hzQ : (z : ℚ) = ((p - q + r - s + 1 : ℤ) : ℚ) / 2 := by
    norm_num [← hz]
  have hwQ : (w : ℚ) = ((-p + q + r - s + 1 : ℤ) : ℚ) / 2 := by
    norm_num [← hw]
  simp only [Int.cast_add]
  unfold jExpTwice
  norm_num [hxQ, hyQ, hzQ, hwQ]
  ring

private theorem riemann_rhs₂Even_rhs₁_expTwice_of_halves
    (M A B C D x y z w p q r s : ℤ)
    (hp : 2 * p = x + y + z - w)
    (hq : 2 * q = x + y - z + w)
    (hr : 2 * r = x - y + z + w)
    (hs : 2 * s = x - y - z - w + 2) :
    2 * (B - C) +
        (jExpTwice (A + B) M x + jExpTwice (A - B) M y +
          jExpTwice (C + D) M z + jExpTwice (C - D) M w) =
      jExpTwice (A + D) M p + jExpTwice (A - D) M q +
        jExpTwice (B + C) M r + jExpTwice (B - C) M s := by
  apply Int.cast_injective (α := ℚ)
  have hpQ : (p : ℚ) = ((x + y + z - w : ℤ) : ℚ) / 2 := by
    norm_num [← hp]
  have hqQ : (q : ℚ) = ((x + y - z + w : ℤ) : ℚ) / 2 := by
    norm_num [← hq]
  have hrQ : (r : ℚ) = ((x - y + z + w : ℤ) : ℚ) / 2 := by
    norm_num [← hr]
  have hsQ : (s : ℚ) = ((x - y - z - w + 2 : ℤ) : ℚ) / 2 := by
    norm_num [← hs]
  simp only [Int.cast_add]
  unfold jExpTwice
  norm_num [hpQ, hqQ, hrQ, hsQ]
  ring

private theorem riemannEvenLR_exp (M A B C D : ℤ) (u : ZQuad) (h : 2 ∣ u.sum) :
    jQuadExp (A + C) (A - C) (B + D) (B - D) M u =
      jQuadExp (A + D) (A - D) (B + C) (B - C) M (riemannEvenLR u) := by
  rcases u with ⟨p, q, r, s⟩
  rcases h with ⟨k, hk⟩
  change p + q + r + s = 2 * k at hk
  unfold riemannEvenLR
  dsimp
  have hpdiv : 2 ∣ p + q + r - s := by refine ⟨k - s, by omega⟩
  have hqdiv : 2 ∣ p + q - r + s := by refine ⟨k - r, by omega⟩
  have hrdiv : 2 ∣ r + s + p - q := by refine ⟨k - q, by omega⟩
  have hsdiv : 2 ∣ r + s - p + q := by refine ⟨k - p, by omega⟩
  have hp : 2 * ((p + q + r - s) / 2) = p + q + r - s :=
    Int.mul_ediv_cancel' hpdiv
  have hq : 2 * ((p + q - r + s) / 2) = p + q - r + s :=
    Int.mul_ediv_cancel' hqdiv
  have hr : 2 * ((r + s + p - q) / 2) = r + s + p - q :=
    Int.mul_ediv_cancel' hrdiv
  have hs : 2 * ((r + s - p + q) / 2) = r + s - p + q :=
    Int.mul_ediv_cancel' hsdiv
  have htw := riemann_evenLR_expTwice_of_halves M A B C D p q r s
    ((p + q + r - s) / 2) ((p + q - r + s) / 2)
    ((r + s + p - q) / 2) ((r + s - p + q) / 2) hp hq hr hs
  have hL := two_mul_jQuadExp (A + C) (A - C) (B + D) (B - D) M ⟨p, q, r, s⟩
  have hR := two_mul_jQuadExp (A + D) (A - D) (B + C) (B - C) M
    ⟨(p + q + r - s) / 2, (p + q - r + s) / 2,
      (r + s + p - q) / 2, (r + s - p + q) / 2⟩
  unfold jQuadExpTwice at hL hR
  nlinarith

private theorem riemannEvenLR_sign (u : ZQuad) (h : 2 ∣ u.sum) :
    negOnePowIntQ (riemannEvenLR u).sum = negOnePowIntQ u.sum := by
  have hsum := riemannEvenLR_sum_eq u h
  apply negOnePowIntQ_eq_of_even_sub
  refine ⟨0, ?_⟩
  omega

private theorem riemannOddLR₂_exp (M A B C D : ℤ) (u : ZQuad) (h : ¬ 2 ∣ u.sum) :
    jQuadExp (A + C) (A - C) (B + D) (B - D) M u =
      (B - C) + jQuadExp (A + B) (A - B) (C + D) (C - D) M (riemannOddLR₂ u) := by
  rcases u with ⟨p, q, r, s⟩
  have hodd : Odd (p + q + r + s) := odd_of_not_two_dvd h
  rcases hodd with ⟨k, hk⟩
  change p + q + r + s = 2 * k + 1 at hk
  unfold riemannOddLR₂
  dsimp
  have hxdiv : 2 ∣ p + q + r + s - 1 := by refine ⟨k, by omega⟩
  have hydiv : 2 ∣ p + q - r - s + 1 := by refine ⟨k - r - s + 1, by omega⟩
  have hzdiv : 2 ∣ p - q + r - s + 1 := by refine ⟨k - q - s + 1, by omega⟩
  have hwdiv : 2 ∣ p - q - r + s + 1 := by refine ⟨k - q - r + 1, by omega⟩
  have hx : 2 * ((p + q + r + s - 1) / 2) = p + q + r + s - 1 :=
    Int.mul_ediv_cancel' hxdiv
  have hy : 2 * ((p + q - r - s + 1) / 2) = p + q - r - s + 1 :=
    Int.mul_ediv_cancel' hydiv
  have hz : 2 * ((p - q + r - s + 1) / 2) = p - q + r - s + 1 :=
    Int.mul_ediv_cancel' hzdiv
  have hw : 2 * ((p - q - r + s + 1) / 2) = p - q - r + s + 1 :=
    Int.mul_ediv_cancel' hwdiv
  have htw := riemann_oddLR₂_expTwice_of_halves M A B C D p q r s
    ((p + q + r + s - 1) / 2) ((p + q - r - s + 1) / 2)
    ((p - q + r - s + 1) / 2) ((p - q - r + s + 1) / 2) hx hy hz hw
  have hL := two_mul_jQuadExp (A + C) (A - C) (B + D) (B - D) M ⟨p, q, r, s⟩
  have hR := two_mul_jQuadExp (A + B) (A - B) (C + D) (C - D) M
    ⟨(p + q + r + s - 1) / 2, (p + q - r - s + 1) / 2,
      (p - q + r - s + 1) / 2, (p - q - r + s + 1) / 2⟩
  unfold jQuadExpTwice at hL hR
  nlinarith

private theorem riemannOddLR₂_sign (u : ZQuad) (h : ¬ 2 ∣ u.sum) :
    negOnePowIntQ (riemannOddLR₂ u).sum = negOnePowIntQ u.sum := by
  rcases u with ⟨p, q, r, s⟩
  change ¬ 2 ∣ p + q + r + s at h
  have hodd : Odd (p + q + r + s) := odd_of_not_two_dvd h
  have hout : Odd (riemannOddLR₂ ⟨p, q, r, s⟩).sum :=
    odd_of_not_two_dvd (riemannOddLR₂_odd ⟨p, q, r, s⟩ h)
  change negOnePowIntQ (riemannOddLR₂ ⟨p, q, r, s⟩).sum =
    negOnePowIntQ (p + q + r + s)
  rw [negOnePowIntQ_of_odd hout, negOnePowIntQ_of_odd hodd]

private theorem riemannRhs₁OddRhs₂_exp (M A B C D : ℤ) (u : ZQuad)
    (h : ¬ 2 ∣ u.sum) :
    jQuadExp (A + D) (A - D) (B + C) (B - C) M u =
      (B - C) + jQuadExp (A + B) (A - B) (C + D) (C - D) M
        (riemannRhs₁OddRhs₂ u) := by
  rcases u with ⟨p, q, r, s⟩
  have hodd : Odd (p + q + r + s) := odd_of_not_two_dvd h
  rcases hodd with ⟨k, hk⟩
  change p + q + r + s = 2 * k + 1 at hk
  unfold riemannRhs₁OddRhs₂
  dsimp
  have hxdiv : 2 ∣ p + q + r + s - 1 := by refine ⟨k, by omega⟩
  have hydiv : 2 ∣ p + q - r - s + 1 := by refine ⟨k - r - s + 1, by omega⟩
  have hzdiv : 2 ∣ p - q + r - s + 1 := by refine ⟨k - q - s + 1, by omega⟩
  have hwdiv : 2 ∣ -p + q + r - s + 1 := by refine ⟨k - p - s + 1, by omega⟩
  have hx : 2 * ((p + q + r + s - 1) / 2) = p + q + r + s - 1 :=
    Int.mul_ediv_cancel' hxdiv
  have hy : 2 * ((p + q - r - s + 1) / 2) = p + q - r - s + 1 :=
    Int.mul_ediv_cancel' hydiv
  have hz : 2 * ((p - q + r - s + 1) / 2) = p - q + r - s + 1 :=
    Int.mul_ediv_cancel' hzdiv
  have hw : 2 * ((-p + q + r - s + 1) / 2) = -p + q + r - s + 1 :=
    Int.mul_ediv_cancel' hwdiv
  have htw := riemann_rhs₁Odd_rhs₂_expTwice_of_halves M A B C D p q r s
    ((p + q + r + s - 1) / 2) ((p + q - r - s + 1) / 2)
    ((p - q + r - s + 1) / 2) ((-p + q + r - s + 1) / 2) hx hy hz hw
  have hL := two_mul_jQuadExp (A + D) (A - D) (B + C) (B - C) M ⟨p, q, r, s⟩
  have hR := two_mul_jQuadExp (A + B) (A - B) (C + D) (C - D) M
    ⟨(p + q + r + s - 1) / 2, (p + q - r - s + 1) / 2,
      (p - q + r - s + 1) / 2, (-p + q + r - s + 1) / 2⟩
  unfold jQuadExpTwice at hL hR
  nlinarith

private theorem riemannRhs₁OddRhs₂_sign (u : ZQuad) (h : ¬ 2 ∣ u.sum) :
    negOnePowIntQ (riemannRhs₁OddRhs₂ u).sum = -negOnePowIntQ u.sum := by
  have hout := riemannRhs₁OddRhs₂_even u h
  have hin : Odd u.sum := odd_of_not_two_dvd h
  apply negOnePowIntQ_eq_neg_of_odd_sub
  rcases hout with ⟨k, hk⟩
  rcases hin with ⟨l, hl⟩
  refine ⟨k - l - 1, ?_⟩
  omega

private theorem riemannRhs₂EvenRhs₁_exp (M A B C D : ℤ) (u : ZQuad)
    (h : 2 ∣ u.sum) :
    (B - C) + jQuadExp (A + B) (A - B) (C + D) (C - D) M u =
      jQuadExp (A + D) (A - D) (B + C) (B - C) M
        (riemannRhs₂EvenRhs₁ u) := by
  rcases u with ⟨x, y, z, w⟩
  rcases h with ⟨k, hk⟩
  change x + y + z + w = 2 * k at hk
  unfold riemannRhs₂EvenRhs₁
  dsimp
  have hpdiv : 2 ∣ x + y + z - w := by refine ⟨k - w, by omega⟩
  have hqdiv : 2 ∣ x + y - z + w := by refine ⟨k - z, by omega⟩
  have hrdiv : 2 ∣ x - y + z + w := by refine ⟨k - y, by omega⟩
  have hsdiv : 2 ∣ x - y - z - w := by refine ⟨x - k, by omega⟩
  have hp : 2 * ((x + y + z - w) / 2) = x + y + z - w :=
    Int.mul_ediv_cancel' hpdiv
  have hq : 2 * ((x + y - z + w) / 2) = x + y - z + w :=
    Int.mul_ediv_cancel' hqdiv
  have hr : 2 * ((x - y + z + w) / 2) = x - y + z + w :=
    Int.mul_ediv_cancel' hrdiv
  have hs : 2 * (((x - y - z - w) / 2) + 1) = x - y - z - w + 2 := by
    have hs0 : 2 * ((x - y - z - w) / 2) = x - y - z - w :=
      Int.mul_ediv_cancel' hsdiv
    omega
  have htw := riemann_rhs₂Even_rhs₁_expTwice_of_halves M A B C D x y z w
    ((x + y + z - w) / 2) ((x + y - z + w) / 2)
    ((x - y + z + w) / 2) ((x - y - z - w) / 2 + 1) hp hq hr hs
  have hL := two_mul_jQuadExp (A + B) (A - B) (C + D) (C - D) M ⟨x, y, z, w⟩
  have hR := two_mul_jQuadExp (A + D) (A - D) (B + C) (B - C) M
    ⟨(x + y + z - w) / 2, (x + y - z + w) / 2,
      (x - y + z + w) / 2, (x - y - z - w) / 2 + 1⟩
  unfold jQuadExpTwice at hL hR
  nlinarith

private theorem riemannRhs₂EvenRhs₁_sign (u : ZQuad) (h : 2 ∣ u.sum) :
    negOnePowIntQ (riemannRhs₂EvenRhs₁ u).sum = -negOnePowIntQ u.sum := by
  have hout : Odd (riemannRhs₂EvenRhs₁ u).sum := odd_of_not_two_dvd
    (riemannRhs₂EvenRhs₁_odd u h)
  apply negOnePowIntQ_eq_neg_of_odd_sub
  rcases hout with ⟨k, hk⟩
  rcases h with ⟨l, hl⟩
  refine ⟨k - l, ?_⟩
  omega

def riemannPair (x : RiemannSide × ZQuad) : RiemannSide × ZQuad :=
  match x.1 with
  | RiemannSide.lhs =>
      if 2 ∣ x.2.sum then
        (RiemannSide.rhs₁, riemannEvenLR x.2)
      else
        (RiemannSide.rhs₂, riemannOddLR₂ x.2)
  | RiemannSide.rhs₁ =>
      if 2 ∣ x.2.sum then
        (RiemannSide.lhs, riemannEvenLR x.2)
      else
        (RiemannSide.rhs₂, riemannRhs₁OddRhs₂ x.2)
  | RiemannSide.rhs₂ =>
      if 2 ∣ x.2.sum then
        (RiemannSide.rhs₁, riemannRhs₂EvenRhs₁ x.2)
      else
        (RiemannSide.lhs, riemannOddLR₂ x.2)

private theorem riemannPair_involutive (x : RiemannSide × ZQuad) :
    riemannPair (riemannPair x) = x := by
  rcases x with ⟨side, u⟩
  cases side
  · by_cases h : 2 ∣ u.sum
    · simp [riemannPair, h, riemannEvenLR_even u h, riemannEvenLR_involutive u h]
    · simp [riemannPair, h, riemannOddLR₂_odd u h, riemannOddLR₂_involutive u h]
  · by_cases h : 2 ∣ u.sum
    · simp [riemannPair, h, riemannEvenLR_even u h, riemannEvenLR_involutive u h]
    · simp [riemannPair, h, riemannRhs₁OddRhs₂_even u h,
        riemannRhs₁OddRhs₂_left_inverse u h]
  · by_cases h : 2 ∣ u.sum
    · simp [riemannPair, h, riemannRhs₂EvenRhs₁_odd u h,
        riemannRhs₂EvenRhs₁_right_inverse u h]
    · simp [riemannPair, h, riemannOddLR₂_odd u h, riemannOddLR₂_involutive u h]

private theorem riemannPair_ne_self (x : RiemannSide × ZQuad) :
    riemannPair x ≠ x := by
  rcases x with ⟨side, u⟩
  cases side <;> by_cases h : 2 ∣ u.sum <;> simp [riemannPair, h]

private theorem riemannDiffFamily_coeff_pair_cancel
    (M : ℤ) (hM : 0 < M) (A B C D e : ℤ) (x : RiemannSide × ZQuad) :
    lcoeff (riemannDiffFamily M hM A B C D x) e +
      lcoeff (riemannDiffFamily M hM A B C D (riemannPair x)) e = 0 := by
  rcases x with ⟨side, u⟩
  cases side
  · by_cases h : 2 ∣ u.sum
    · simp [riemannPair, h, riemannEvenLR_exp M A B C D u h,
        riemannEvenLR_sign u h, lcoeff]
    · simp [riemannPair, h, riemannOddLR₂_exp M A B C D u h,
        riemannOddLR₂_sign u h, lcoeff]
  · by_cases h : 2 ∣ u.sum
    · have hExp := riemannEvenLR_exp M A B C D (riemannEvenLR u)
        (riemannEvenLR_even u h)
      rw [riemannEvenLR_involutive u h] at hExp
      simp [riemannPair, h, hExp, riemannEvenLR_sign u h, lcoeff]
    · simp [riemannPair, h, riemannRhs₁OddRhs₂_exp M A B C D u h,
        riemannRhs₁OddRhs₂_sign u h, lcoeff]
      by_cases hc :
          B - C + jQuadExp (A + B) (A - B) (C + D) (C - D) M
            (riemannRhs₁OddRhs₂ u) = e <;> simp [hc]
  · by_cases h : 2 ∣ u.sum
    · simp [riemannPair, h, riemannRhs₂EvenRhs₁_exp M A B C D u h,
        riemannRhs₂EvenRhs₁_sign u h, lcoeff]
      by_cases hc :
          jQuadExp (A + D) (A - D) (B + C) (B - C) M
            (riemannRhs₂EvenRhs₁ u) = e <;> simp [hc]
    · have hExp := riemannOddLR₂_exp M A B C D (riemannOddLR₂ u)
        (riemannOddLR₂_odd u h)
      rw [riemannOddLR₂_involutive u h] at hExp
      simp [riemannPair, h, hExp, riemannOddLR₂_sign u h, lcoeff]

private theorem riemannDiffFamily_hsum_zero
    (M : ℤ) (hM : 0 < M) (A B C D : ℤ) :
    (riemannDiffFamily M hM A B C D).hsum = 0 := by
  let F := riemannDiffFamily M hM A B C D
  ext e
  change lcoeff F.hsum e = lcoeff (0 : QLaurent) e
  rw [lcoeff, HahnSeries.SummableFamily.coeff_hsum_eq_sum]
  refine Finset.sum_involution (s := (F.coeff e).support)
    (f := fun x => (F x).coeff e) (g := fun x _ => riemannPair x) ?cancel ?ne ?mem ?inv
  · intro x hx
    change lcoeff (F x) e + lcoeff (F (riemannPair x)) e = 0
    exact riemannDiffFamily_coeff_pair_cancel M hM A B C D e x
  · intro x hx hxne
    exact riemannPair_ne_self x
  · intro x hx
    rw [Finsupp.mem_support_iff] at hx ⊢
    change (F (riemannPair x)).coeff e ≠ 0
    intro hzero
    have hcancel := riemannDiffFamily_coeff_pair_cancel M hM A B C D e x
    change (F x).coeff e + (F (riemannPair x)).coeff e = 0 at hcancel
    rw [hzero, add_zero] at hcancel
    exact hx hcancel
  · intro x hx
    exact riemannPair_involutive x

theorem jLaurent_riemann (M : ℕ) (hM : 0 < M) (A B C D : ℤ) :
    jLaurent (A + C) M * jLaurent (A - C) M * jLaurent (B + D) M *
        jLaurent (B - D) M =
      jLaurent (A + D) M * jLaurent (A - D) M * jLaurent (B + C) M *
          jLaurent (B - C) M +
        Qpow (B - C) * jLaurent (A + B) M * jLaurent (A - B) M *
          jLaurent (C + D) M * jLaurent (C - D) M := by
  have hMint : 0 < (M : ℤ) := by omega
  have hzero := riemannDiffFamily_hsum_zero (M : ℤ) hMint A B C D
  have hdiff :
      jLaurent (A + C) (M : ℤ) * jLaurent (A - C) (M : ℤ) *
          jLaurent (B + D) (M : ℤ) * jLaurent (B - D) (M : ℤ) -
        jLaurent (A + D) (M : ℤ) * jLaurent (A - D) (M : ℤ) *
          jLaurent (B + C) (M : ℤ) * jLaurent (B - C) (M : ℤ) -
          Qpow (B - C) * jLaurent (A + B) (M : ℤ) * jLaurent (A - B) (M : ℤ) *
            jLaurent (C + D) (M : ℤ) * jLaurent (C - D) (M : ℤ) = 0 := by
    rw [← riemannDiffFamily_hsum (M : ℤ) hMint A B C D]
    exact hzero
  change
    jLaurent (A + C) (M : ℤ) * jLaurent (A - C) (M : ℤ) *
        jLaurent (B + D) (M : ℤ) * jLaurent (B - D) (M : ℤ) =
      jLaurent (A + D) (M : ℤ) * jLaurent (A - D) (M : ℤ) *
          jLaurent (B + C) (M : ℤ) * jLaurent (B - C) (M : ℤ) +
        Qpow (B - C) * jLaurent (A + B) (M : ℤ) * jLaurent (A - B) (M : ℤ) *
          jLaurent (C + D) (M : ℤ) * jLaurent (C - D) (M : ℤ)
  linear_combination hdiff

/-- The two finite q-Pochhammer factors in Chan's finite JTP, specialized to
`z=Q^a`, `q=Q^b`.  For `0 < a < b`, these are
`(Q^a;Q^b)_N (Q^(b-a);Q^b)_N`. -/
noncomputable def jFiniteProductLaurent (a b : ℤ) (N : ℕ) : QLaurent :=
  qPoch (Qpow a) (Qpow b) N * qPoch (Qpow (b - a)) (Qpow b) N

/-- The finite three-factor product partial
`(Q^b;Q^b)_N (Q^a;Q^b)_N (Q^(b-a);Q^b)_N`. -/
noncomputable def jTripleProductPartialLaurent (a b : ℤ) (N : ℕ) : QLaurent :=
  qPochhammer (Qpow b) N * jFiniteProductLaurent a b N

theorem jFiniteJTPSummand_Qpow (a b : ℤ) (N k : ℕ) :
    QseriesFormalization.PartI.Ch03.finiteJTPSummand (Qpow b) (Qpow a) N k =
      gaussianBinom (Qpow b) (2 * N) k *
        jTermLaurent a b ((k : ℤ) - (N : ℤ)) := by
  unfold QseriesFormalization.PartI.Ch03.finiteJTPSummand jTermLaurent
  let l : ℤ := (k : ℤ) - (N : ℤ)
  have hl_nonneg : 0 ≤ l * (l - 1) / 2 := int_l_mul_l_sub_one_div_two_nonneg l
  have hto : (((l * (l - 1) / 2).toNat : ℕ) : ℤ) = l * (l - 1) / 2 :=
    Int.toNat_of_nonneg hl_nonneg
  change gaussianBinom (Qpow b) (2 * N) k *
      (Qpow b) ^ (l * (l - 1) / 2).toNat * (-Qpow a) ^ l =
    gaussianBinom (Qpow b) (2 * N) k *
      (((negOnePowIntQ l : ℚ) : QLaurent) * Qpow (jExp a b l))
  rw [Qpow_pow_nat]
  rw [show b * ↑((l * (l - 1) / 2).toNat) =
      b * (l * (l - 1) / 2) by rw [hto]]
  rw [neg_Qpow_zpow]
  have hexp : b * (l * (l - 1) / 2) + a * l = jExp a b l := by
    unfold jExp
    have hdiv : (2 : ℤ) ∣ l * (l - 1) := int_two_dvd_mul_pred l
    have hmuldiv : b * (l * (l - 1)) / 2 =
        b * (l * (l - 1) / 2) :=
      Int.mul_ediv_assoc b hdiv
    rw [← hmuldiv]
    ring_nf
  calc
    gaussianBinom (Qpow b) (2 * N) k *
          Qpow (b * (l * (l - 1) / 2)) *
          (((negOnePowIntQ l : ℚ) : QLaurent) * Qpow (a * l))
        = gaussianBinom (Qpow b) (2 * N) k *
            ((negOnePowIntQ l : ℚ) : QLaurent) *
              (Qpow (b * (l * (l - 1) / 2)) * Qpow (a * l)) := by
            ring
    _ = gaussianBinom (Qpow b) (2 * N) k *
            ((negOnePowIntQ l : ℚ) : QLaurent) *
              Qpow (b * (l * (l - 1) / 2) + a * l) := by
            rw [Qpow_mul]
    _ = gaussianBinom (Qpow b) (2 * N) k *
          (((negOnePowIntQ l : ℚ) : QLaurent) * Qpow (jExp a b l)) := by
            rw [hexp]
            ring

/-- Specialized finite-JTP RHS as a Gaussian-weighted finite `j`-term sum. -/
theorem finiteJTPRHS_Qpow_eq_natSum_jTerm (a b : ℤ) (N : ℕ) :
    QseriesFormalization.PartI.Ch03.finiteJTPRHS (Qpow b) (Qpow a) N =
      natSum (fun k =>
        gaussianBinom (Qpow b) (2 * N) k *
          jTermLaurent a b ((k : ℤ) - (N : ℤ))) (2 * N) := by
  unfold QseriesFormalization.PartI.Ch03.finiteJTPRHS
  exact QseriesFormalization.PartI.Ch03.natSum_congr_le (2 * N)
    (fun k _ => jFiniteJTPSummand_Qpow a b N k)

/-- Finite-JTP product bridge specialized to Laurent monomials.  This is the
repository's proved finite JTP (`Chapter03.finite_jacobi_triple_product`) with
`q=Q^b`, `z=Q^a`, and the second q-Pochhammer factor normalized to
`Q^(b-a)`. -/
theorem jFiniteProductLaurent_eq_finiteJTPRHS (a b : ℤ) (N : ℕ) :
    jFiniteProductLaurent a b N =
      QseriesFormalization.PartI.Ch03.finiteJTPRHS (Qpow b) (Qpow a) N := by
  unfold jFiniteProductLaurent
  have h := QseriesFormalization.PartI.Ch03.finite_jacobi_triple_product
    (Qpow b) (Qpow a) (Qpow_ne_zero a) (Qpow_ne_zero b) N
  rwa [Qpow_inv_mul] at h

/-- Three-factor finite product partial reduced to the finite-JTP RHS.  This is
the finite partial-product bridge for the eventual
`(Q^b;Q^b)_∞ (Q^a;Q^b)_∞ (Q^(b-a);Q^b)_∞` product form. -/
theorem jTripleProductPartialLaurent_eq_qPochhammer_mul_finiteJTPRHS
    (a b : ℤ) (N : ℕ) :
    jTripleProductPartialLaurent a b N =
      qPochhammer (Qpow b) N *
        QseriesFormalization.PartI.Ch03.finiteJTPRHS (Qpow b) (Qpow a) N := by
  unfold jTripleProductPartialLaurent
  rw [jFiniteProductLaurent_eq_finiteJTPRHS]

theorem qPoch_Qpow_eq_coe_apFinitePS (r m N : ℕ) :
    qPoch (Qpow (r : ℤ)) (Qpow (m : ℤ)) N =
      ((∏ n ∈ Finset.range N, apFactorPS ℚ r m n : ℚ⟦X⟧) : QLaurent) := by
  induction N with
  | zero =>
      simp [qPoch]
  | succ N ih =>
      rw [qPoch_succ, ih, Finset.prod_range_succ, map_mul]
      congr 1
      simp [apFactorPS, Qpow, Nat.cast_add, Nat.cast_mul, mul_comm]

theorem qPochhammer_Qpow_eq_coe_apFinitePS (m N : ℕ) :
    qPochhammer (Qpow (m : ℤ)) N =
      ((∏ n ∈ Finset.range N, apFactorPS ℚ m m n : ℚ⟦X⟧) : QLaurent) := by
  rw [← qPoch_q_eq_qPochhammer]
  exact qPoch_Qpow_eq_coe_apFinitePS m m N

theorem one_sub_Qpow_ne_zero_of_pos {e : ℤ} (he : 0 < e) :
    (1 : QLaurent) - Qpow e ≠ 0 := by
  intro h
  have hq : Qpow e = (1 : QLaurent) := by
    exact (sub_eq_zero.mp h).symm
  exact Qpow_ne_one_of_pos he hq

theorem qPochhammer_Qpow_ne_zero (b N : ℕ) (hb : 0 < b) :
    qPochhammer (Qpow (b : ℤ)) N ≠ 0 := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [qPochhammer_succ]
      refine mul_ne_zero ih ?_
      rw [Qpow_pow_nat]
      exact one_sub_Qpow_ne_zero_of_pos (by positivity)

theorem coeff_apFinitePS_eq_one_of_lt (r m N k : ℕ) (hk : k < r) :
    (PowerSeries.coeff k
        (∏ n ∈ Finset.range N, apFactorPS ℚ r m n : ℚ⟦X⟧)) =
      if k = 0 then 1 else 0 := by
  have h := PowerSeries.coeff_mul_prod_one_sub_of_lt_order
    (R := ℚ) (ι := ℕ) k (Finset.range N) (1 : ℚ⟦X⟧)
      (fun n : ℕ => PowerSeries.X ^ (r + m * n))
  have horder :
      ∀ n ∈ Finset.range N, ↑k < (PowerSeries.X ^ (r + m * n) : ℚ⟦X⟧).order := by
    intro n _hn
    rw [PowerSeries.order_X_pow]
    norm_cast
    omega
  simpa [apFactorPS] using h horder

theorem qPochhammer_mul_gaussian_center_add_eq_tail
    (b N r : ℕ) (hb : 0 < b) (hr : r ≤ N) :
    qPochhammer (Qpow (b : ℤ)) N *
        gaussianBinom (Qpow (b : ℤ)) (2 * N) (N + r) =
      qPoch ((Qpow (b : ℤ)) * (Qpow (b : ℤ)) ^ (N - r))
          (Qpow (b : ℤ)) r *
        qPoch ((Qpow (b : ℤ)) * (Qpow (b : ℤ)) ^ (N + r))
          (Qpow (b : ℤ)) (N - r) := by
  let q : QLaurent := Qpow (b : ℤ)
  have hcenter :=
    QseriesFormalization.PartI.Ch03.gaussianBinom_center_add_mul_qPochhammer_eq
      q N r hr
  have hden :
      qPochhammer q (N + r) * qPochhammer q (N - r) ≠ 0 := by
    exact mul_ne_zero (by simpa [q] using qPochhammer_Qpow_ne_zero b (N + r) hb)
      (by simpa [q] using qPochhammer_Qpow_ne_zero b (N - r) hb)
  have hNsplit :
      qPochhammer q N =
        qPochhammer q (N - r) * qPoch (q * q ^ (N - r)) q r := by
    have h := QseriesFormalization.PartI.Ch03.qPochhammer_split q N (N - r) (by omega)
    simpa [show N - (N - r) = r by omega] using h
  have h2split :
      qPochhammer q (2 * N) =
        qPochhammer q (N + r) * qPoch (q * q ^ (N + r)) q (N - r) := by
    have h := QseriesFormalization.PartI.Ch03.qPochhammer_split q (2 * N) (N + r) (by omega)
    simpa [show 2 * N - (N + r) = N - r by omega] using h
  apply mul_right_cancel₀ hden
  calc
    (qPochhammer (Qpow (b : ℤ)) N * gaussianBinom (Qpow (b : ℤ)) (2 * N) (N + r)) *
        (qPochhammer q (N + r) * qPochhammer q (N - r))
        = qPochhammer q N *
            (gaussianBinom q (2 * N) (N + r) *
              qPochhammer q (N + r) * qPochhammer q (N - r)) := by
          simp [q]
          ring
    _ = qPochhammer q N * qPochhammer q (2 * N) := by
          rw [hcenter]
    _ = (qPoch (q * q ^ (N - r)) q r *
          qPoch (q * q ^ (N + r)) q (N - r)) *
            (qPochhammer q (N + r) * qPochhammer q (N - r)) := by
          rw [hNsplit, h2split]
          ring

theorem qPochhammer_mul_gaussian_center_sub_eq_tail
    (b N r : ℕ) (hb : 0 < b) (hr : r ≤ N) :
    qPochhammer (Qpow (b : ℤ)) N *
        gaussianBinom (Qpow (b : ℤ)) (2 * N) (N - r) =
      qPoch ((Qpow (b : ℤ)) * (Qpow (b : ℤ)) ^ (N - r))
          (Qpow (b : ℤ)) r *
        qPoch ((Qpow (b : ℤ)) * (Qpow (b : ℤ)) ^ (N + r))
          (Qpow (b : ℤ)) (N - r) := by
  let q : QLaurent := Qpow (b : ℤ)
  have hcenter :=
    QseriesFormalization.PartI.Ch03.gaussianBinom_center_sub_mul_qPochhammer_eq
      q N r hr
  have hden :
      qPochhammer q (N - r) * qPochhammer q (N + r) ≠ 0 := by
    exact mul_ne_zero (by simpa [q] using qPochhammer_Qpow_ne_zero b (N - r) hb)
      (by simpa [q] using qPochhammer_Qpow_ne_zero b (N + r) hb)
  have hNsplit :
      qPochhammer q N =
        qPochhammer q (N - r) * qPoch (q * q ^ (N - r)) q r := by
    have h := QseriesFormalization.PartI.Ch03.qPochhammer_split q N (N - r) (by omega)
    simpa [show N - (N - r) = r by omega] using h
  have h2split :
      qPochhammer q (2 * N) =
        qPochhammer q (N + r) * qPoch (q * q ^ (N + r)) q (N - r) := by
    have h := QseriesFormalization.PartI.Ch03.qPochhammer_split q (2 * N) (N + r) (by omega)
    simpa [show 2 * N - (N + r) = N - r by omega] using h
  apply mul_right_cancel₀ hden
  calc
    (qPochhammer (Qpow (b : ℤ)) N * gaussianBinom (Qpow (b : ℤ)) (2 * N) (N - r)) *
        (qPochhammer q (N - r) * qPochhammer q (N + r))
        = qPochhammer q N *
            (gaussianBinom q (2 * N) (N - r) *
              qPochhammer q (N - r) * qPochhammer q (N + r)) := by
          simp [q]
          ring
    _ = qPochhammer q N * qPochhammer q (2 * N) := by
          rw [hcenter]
    _ = (qPoch (q * q ^ (N - r)) q r *
          qPoch (q * q ^ (N + r)) q (N - r)) *
            (qPochhammer q (N - r) * qPochhammer q (N + r)) := by
          rw [hNsplit, h2split]
          ring

theorem lcoeff_qPoch_tail_pair_low_nat
    (b s t L₁ L₂ k : ℕ) (hst : s ≤ t) (hk : k < b * s) :
    lcoeff
        (qPoch (Qpow ((b * s : ℕ) : ℤ)) (Qpow (b : ℤ)) L₁ *
          qPoch (Qpow ((b * t : ℕ) : ℤ)) (Qpow (b : ℤ)) L₂)
        (k : ℤ) =
      if k = 0 then 1 else 0 := by
  let P₁ : ℚ⟦X⟧ := ∏ n ∈ Finset.range L₁, apFactorPS ℚ (b * s) b n
  let P₂ : ℚ⟦X⟧ := ∏ n ∈ Finset.range L₂, apFactorPS ℚ (b * t) b n
  rw [qPoch_Qpow_eq_coe_apFinitePS (b * s) b L₁,
    qPoch_Qpow_eq_coe_apFinitePS (b * t) b L₂]
  rw [← PowerSeries.coe_mul]
  change lcoeff ((P₁ * P₂ : ℚ⟦X⟧) : QLaurent) (k : ℤ) =
    if k = 0 then 1 else 0
  rw [lcoeff, LaurentSeries.coeff_coe_powerSeries]
  have hP₂ :
      PowerSeries.coeff k (P₁ * P₂) = PowerSeries.coeff k P₁ := by
    have h := PowerSeries.coeff_mul_prod_one_sub_of_lt_order
      (R := ℚ) (ι := ℕ) k (Finset.range L₂) P₁
        (fun n : ℕ => PowerSeries.X ^ (b * t + b * n))
    have horder :
        ∀ n ∈ Finset.range L₂,
          ↑k < (PowerSeries.X ^ (b * t + b * n) : ℚ⟦X⟧).order := by
      intro n _hn
      rw [PowerSeries.order_X_pow]
      norm_cast
      have hbs_le_bt : b * s ≤ b * t := Nat.mul_le_mul_left b hst
      omega
    simpa [P₂, apFactorPS] using h horder
  rw [hP₂]
  exact coeff_apFinitePS_eq_one_of_lt (b * s) b L₁ k hk

theorem lcoeff_qPochhammer_mul_gaussian_center_add_low_nat
    (b N r k : ℕ) (hb : 0 < b) (hr : r ≤ N)
    (hk : k < b * (N - r + 1)) :
    lcoeff
        (qPochhammer (Qpow (b : ℤ)) N *
          gaussianBinom (Qpow (b : ℤ)) (2 * N) (N + r))
        (k : ℤ) =
      if k = 0 then 1 else 0 := by
  rw [qPochhammer_mul_gaussian_center_add_eq_tail b N r hb hr]
  have hq₁ :
      Qpow (b : ℤ) * Qpow (b : ℤ) ^ (N - r) =
        Qpow ((b * (N - r + 1) : ℕ) : ℤ) := by
    rw [Qpow_pow_nat, Qpow_mul]
    congr 1
    norm_num [Nat.cast_mul, Nat.cast_add]
    ring
  have hq₂ :
      Qpow (b : ℤ) * Qpow (b : ℤ) ^ (N + r) =
        Qpow ((b * (N + r + 1) : ℕ) : ℤ) := by
    rw [Qpow_pow_nat, Qpow_mul]
    congr 1
    norm_num [Nat.cast_mul, Nat.cast_add]
    ring
  rw [hq₁, hq₂]
  exact lcoeff_qPoch_tail_pair_low_nat b (N - r + 1) (N + r + 1) r (N - r) k
    (by omega) hk

theorem lcoeff_qPochhammer_mul_gaussian_center_sub_low_nat
    (b N r k : ℕ) (hb : 0 < b) (hr : r ≤ N)
    (hk : k < b * (N - r + 1)) :
    lcoeff
        (qPochhammer (Qpow (b : ℤ)) N *
          gaussianBinom (Qpow (b : ℤ)) (2 * N) (N - r))
        (k : ℤ) =
      if k = 0 then 1 else 0 := by
  rw [qPochhammer_mul_gaussian_center_sub_eq_tail b N r hb hr]
  have hq₁ :
      Qpow (b : ℤ) * Qpow (b : ℤ) ^ (N - r) =
        Qpow ((b * (N - r + 1) : ℕ) : ℤ) := by
    rw [Qpow_pow_nat, Qpow_mul]
    congr 1
    norm_num [Nat.cast_mul, Nat.cast_add]
    ring
  have hq₂ :
      Qpow (b : ℤ) * Qpow (b : ℤ) ^ (N + r) =
        Qpow ((b * (N + r + 1) : ℕ) : ℤ) := by
    rw [Qpow_pow_nat, Qpow_mul]
    congr 1
    norm_num [Nat.cast_mul, Nat.cast_add]
    ring
  rw [hq₁, hq₂]
  exact lcoeff_qPoch_tail_pair_low_nat b (N - r + 1) (N + r + 1) r (N - r) k
    (by omega) hk

theorem lcoeff_qPochhammer_mul_gaussian_center_add_low_int
    (b N r : ℕ) (hb : 0 < b) (hr : r ≤ N) (t : ℤ)
    (ht : t < (b * (N - r + 1) : ℕ)) :
    lcoeff
        (qPochhammer (Qpow (b : ℤ)) N *
          gaussianBinom (Qpow (b : ℤ)) (2 * N) (N + r))
        t =
      if t = 0 then 1 else 0 := by
  by_cases htneg : t < 0
  · rw [qPochhammer_mul_gaussian_center_add_eq_tail b N r hb hr]
    have hq₁ :
        Qpow (b : ℤ) * Qpow (b : ℤ) ^ (N - r) =
          Qpow ((b * (N - r + 1) : ℕ) : ℤ) := by
      rw [Qpow_pow_nat, Qpow_mul]
      congr 1
      norm_num [Nat.cast_mul, Nat.cast_add]
      ring
    have hq₂ :
        Qpow (b : ℤ) * Qpow (b : ℤ) ^ (N + r) =
          Qpow ((b * (N + r + 1) : ℕ) : ℤ) := by
      rw [Qpow_pow_nat, Qpow_mul]
      congr 1
      norm_num [Nat.cast_mul, Nat.cast_add]
      ring
    rw [hq₁, hq₂, qPoch_Qpow_eq_coe_apFinitePS, qPoch_Qpow_eq_coe_apFinitePS]
    rw [← PowerSeries.coe_mul]
    rw [if_neg htneg.ne]
    change
        (((∏ x ∈ Finset.range r, apFactorPS ℚ (b * (N - r + 1)) b x) *
          (∏ x ∈ Finset.range (N - r), apFactorPS ℚ (b * (N + r + 1)) b x) :
            ℚ⟦X⟧) : QLaurent).coeff t = 0
    rw [PowerSeries.coeff_coe]
    simp [htneg]
  · have ht_nonneg : 0 ≤ t := by omega
    let k : ℕ := t.toNat
    have hkcast : (k : ℤ) = t := by
      dsimp [k]
      exact Int.toNat_of_nonneg ht_nonneg
    have hk : k < b * (N - r + 1) := by
      dsimp [k]
      omega
    have hnat := lcoeff_qPochhammer_mul_gaussian_center_add_low_nat b N r k hb hr hk
    rw [← hkcast]
    simpa using hnat

theorem lcoeff_qPochhammer_mul_gaussian_center_sub_low_int
    (b N r : ℕ) (hb : 0 < b) (hr : r ≤ N) (t : ℤ)
    (ht : t < (b * (N - r + 1) : ℕ)) :
    lcoeff
        (qPochhammer (Qpow (b : ℤ)) N *
          gaussianBinom (Qpow (b : ℤ)) (2 * N) (N - r))
        t =
      if t = 0 then 1 else 0 := by
  by_cases htneg : t < 0
  · rw [qPochhammer_mul_gaussian_center_sub_eq_tail b N r hb hr]
    have hq₁ :
        Qpow (b : ℤ) * Qpow (b : ℤ) ^ (N - r) =
          Qpow ((b * (N - r + 1) : ℕ) : ℤ) := by
      rw [Qpow_pow_nat, Qpow_mul]
      congr 1
      norm_num [Nat.cast_mul, Nat.cast_add]
      ring
    have hq₂ :
        Qpow (b : ℤ) * Qpow (b : ℤ) ^ (N + r) =
          Qpow ((b * (N + r + 1) : ℕ) : ℤ) := by
      rw [Qpow_pow_nat, Qpow_mul]
      congr 1
      norm_num [Nat.cast_mul, Nat.cast_add]
      ring
    rw [hq₁, hq₂, qPoch_Qpow_eq_coe_apFinitePS, qPoch_Qpow_eq_coe_apFinitePS]
    rw [← PowerSeries.coe_mul]
    rw [if_neg htneg.ne]
    change
        (((∏ x ∈ Finset.range r, apFactorPS ℚ (b * (N - r + 1)) b x) *
          (∏ x ∈ Finset.range (N - r), apFactorPS ℚ (b * (N + r + 1)) b x) :
            ℚ⟦X⟧) : QLaurent).coeff t = 0
    rw [PowerSeries.coeff_coe]
    simp [htneg]
  · have ht_nonneg : 0 ≤ t := by omega
    let k : ℕ := t.toNat
    have hkcast : (k : ℤ) = t := by
      dsimp [k]
      exact Int.toNat_of_nonneg ht_nonneg
    have hk : k < b * (N - r + 1) := by
      dsimp [k]
      omega
    have hnat := lcoeff_qPochhammer_mul_gaussian_center_sub_low_nat b N r k hb hr hk
    rw [← hkcast]
    simpa using hnat

noncomputable def jTripleFactorPS (R : Type*) [CommRing R] (A B n : ℕ) : R⟦X⟧ :=
  apFactorPS R B B n * apFactorPS R A B n * apFactorPS R (B - A) B n

noncomputable def jTripleProductInfPS (A B : ℕ) : ℚ⟦X⟧ :=
  qPochAPPS ℚ B B * qPochAPPS ℚ A B * qPochAPPS ℚ (B - A) B

theorem hasProd_jTripleFactorPS (A B : ℕ) (hA : 0 < A) (hAB : A < B) :
    HasProd (fun n : ℕ => jTripleFactorPS ℚ A B n)
      (jTripleProductInfPS A B) := by
  unfold jTripleFactorPS jTripleProductInfPS
  exact ((hasProd_qPochAPPS ℚ B B (by omega)).mul
    (hasProd_qPochAPPS ℚ A B (by omega))).mul
      (hasProd_qPochAPPS ℚ (B - A) B (by omega))

theorem partial_prod_jTripleFactorPS_coeff_stable
    (A B k N : ℕ) (hA : 0 < A) (hAB : A < B) (hN : k ≤ N) :
    PowerSeries.coeff k
        (∏ n ∈ Finset.range (N + 1), jTripleFactorPS ℚ A B n) =
      PowerSeries.coeff k
        (∏ n ∈ Finset.range N, jTripleFactorPS ℚ A B n) := by
  rw [Finset.prod_range_succ]
  change PowerSeries.coeff k
      ((∏ n ∈ Finset.range N, jTripleFactorPS ℚ A B n) *
        (apFactorPS ℚ B B N * apFactorPS ℚ A B N * apFactorPS ℚ (B - A) B N)) =
    PowerSeries.coeff k (∏ n ∈ Finset.range N, jTripleFactorPS ℚ A B n)
  let P : ℚ⟦X⟧ := ∏ n ∈ Finset.range N, jTripleFactorPS ℚ A B n
  have hBpos : 1 ≤ B := by omega
  have hN_le_BN : N ≤ B * N := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right N hBpos
  calc
    PowerSeries.coeff k
        (P * (apFactorPS ℚ B B N * apFactorPS ℚ A B N * apFactorPS ℚ (B - A) B N))
        = PowerSeries.coeff k
          (((P * apFactorPS ℚ B B N) * apFactorPS ℚ A B N) *
            apFactorPS ℚ (B - A) B N) := by
          ring_nf
    _ = PowerSeries.coeff k ((P * apFactorPS ℚ B B N) * apFactorPS ℚ A B N) :=
          coeff_mul_apFactorPS_eq_of_lt ℚ
            ((P * apFactorPS ℚ B B N) * apFactorPS ℚ A B N) k (B - A) B N
            (by omega)
    _ = PowerSeries.coeff k (P * apFactorPS ℚ B B N) :=
          coeff_mul_apFactorPS_eq_of_lt ℚ (P * apFactorPS ℚ B B N) k A B N
            (by omega)
    _ = PowerSeries.coeff k P :=
          coeff_mul_apFactorPS_eq_of_lt ℚ P k B B N (by omega)

theorem partial_prod_jTripleFactorPS_coeff_eq
    (A B k N M : ℕ) (hA : 0 < A) (hAB : A < B) (hkN : k ≤ N) (hNM : N ≤ M) :
    PowerSeries.coeff k
        (∏ n ∈ Finset.range M, jTripleFactorPS ℚ A B n) =
      PowerSeries.coeff k
        (∏ n ∈ Finset.range N, jTripleFactorPS ℚ A B n) := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M _ ih =>
      rw [partial_prod_jTripleFactorPS_coeff_stable A B k M hA hAB (by omega), ih]

theorem coeff_jTripleProductInfPS_eq_coeff_partial
    (A B k : ℕ) (hA : 0 < A) (hAB : A < B) :
    (jTripleProductInfPS A B).coeff k =
      (∏ n ∈ Finset.range (k + 1), jTripleFactorPS ℚ A B n).coeff k := by
  have h_tendsto : Tendsto
      (fun N : ℕ => ∏ n ∈ Finset.range N, jTripleFactorPS ℚ A B n) atTop
      (𝓝 (jTripleProductInfPS A B)) :=
    (hasProd_jTripleFactorPS A B hA hAB).tendsto_prod_nat
  have h_coeff_tendsto : Tendsto
      (fun N : ℕ => PowerSeries.coeff k
        (∏ n ∈ Finset.range N, jTripleFactorPS ℚ A B n)) atTop
      (𝓝 (PowerSeries.coeff k (jTripleProductInfPS A B))) :=
    ((PowerSeries.WithPiTopology.continuous_coeff ℚ k).tendsto _).comp h_tendsto
  have h_const_tendsto : Tendsto
      (fun N : ℕ => PowerSeries.coeff k
        (∏ n ∈ Finset.range N, jTripleFactorPS ℚ A B n)) atTop
      (𝓝 (PowerSeries.coeff k
        (∏ n ∈ Finset.range (k + 1), jTripleFactorPS ℚ A B n))) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    exact ⟨k + 1, fun N hN =>
      (partial_prod_jTripleFactorPS_coeff_eq A B k (k + 1) N hA hAB (by omega) hN).symm⟩
  exact tendsto_nhds_unique h_coeff_tendsto h_const_tendsto

theorem jExpTwice_pos_of_ne_zero_of_pos_lt (a b n : ℤ)
    (ha : 0 < a) (hab : a < b) (hn : n ≠ 0) :
    0 < jExpTwice a b n := by
  have hb : 0 < b := by omega
  unfold jExpTwice
  by_cases hnpos : 0 < n
  · have hfac : 0 < b * (n - 1) + 2 * a := by
      have hn1 : 0 ≤ n - 1 := by omega
      nlinarith [mul_nonneg (by omega : 0 ≤ b) hn1]
    have hmul : 0 < n * (b * (n - 1) + 2 * a) := mul_pos hnpos hfac
    nlinarith
  · have hnneg : n < 0 := by omega
    have hfac : b * (n - 1) + 2 * a < 0 := by
      have hnle : n - 1 ≤ -2 := by omega
      nlinarith [mul_le_mul_of_nonneg_left hnle (by omega : 0 ≤ b)]
    have hmul : 0 < n * (b * (n - 1) + 2 * a) := mul_pos_of_neg_of_neg hnneg hfac
    nlinarith

theorem abs_le_jExp_of_pos_lt (a b n : ℤ) (ha : 0 < a) (hab : a < b) :
    |n| ≤ jExp a b n := by
  have hb : 0 < b := by omega
  have htw := two_mul_jExp a b n
  by_cases hnneg : n < 0
  · have hspos : 0 < -n := by omega
    have hrewrite :
        jExpTwice a b n =
          b * (-n) * ((-n) - 1) + 2 * (b - a) * (-n) := by
      unfold jExpTwice
      ring
    have hprod_nonneg : 0 ≤ b * (-n) * ((-n) - 1) := by
      have hsnonneg : 0 ≤ -n := by omega
      have hs1nonneg : 0 ≤ (-n) - 1 := by omega
      nlinarith [mul_nonneg hsnonneg hs1nonneg]
    have hba : 1 ≤ b - a := by omega
    have hmain : 2 * (-n) ≤ jExpTwice a b n := by
      rw [hrewrite]
      nlinarith
    have habs : |n| = -n := abs_of_neg hnneg
    nlinarith
  · have hnnonneg : 0 ≤ n := by omega
    have hn1nonneg : 0 ≤ n - 1 ∨ n = 0 := by omega
    have hprod_nonneg : 0 ≤ b * n * (n - 1) := by
      by_cases hn0 : n = 0
      · subst hn0
        simp
      · have hnpos : 0 < n := by omega
        have hn1 : 0 ≤ n - 1 := by omega
        nlinarith [mul_nonneg hnnonneg hn1]
    have ha1 : 1 ≤ a := by omega
    have hmain : 2 * n ≤ jExpTwice a b n := by
      unfold jExpTwice
      nlinarith
    have habs : |n| = n := abs_of_nonneg hnnonneg
    nlinarith

theorem jExp_nonneg_of_pos_lt (a b n : ℤ) (ha : 0 < a) (hab : a < b) :
    0 ≤ jExp a b n := by
  exact le_trans (abs_nonneg n) (abs_le_jExp_of_pos_lt a b n ha hab)

private theorem degree_sub_lt_center_start
    (A B d r : ℕ) (hA : 0 < A) (hAB : A < B) (hr : r ≤ d + 1)
    (n : ℤ) (hnabs : |n| = (r : ℤ)) :
    (d : ℤ) - jExp (A : ℤ) (B : ℤ) n <
      (B * (d + 1 - r + 1) : ℕ) := by
  have hB1 : 1 ≤ B := by omega
  have hstart_ge :
      d + 1 - r + 1 ≤ B * (d + 1 - r + 1) := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right (d + 1 - r + 1) hB1
  have hbase : (d : ℤ) - (r : ℤ) < (B * (d + 1 - r + 1) : ℕ) := by
    omega
  have hexp_ge : (r : ℤ) ≤ jExp (A : ℤ) (B : ℤ) n := by
    rw [← hnabs]
    exact abs_le_jExp_of_pos_lt (A : ℤ) (B : ℤ) n (by omega) (by omega)
  omega

theorem lcoeff_center_add_mul_jTerm_eq_of_succ_degree
    (A B d r : ℕ) (hA : 0 < A) (hAB : A < B) (hr : r ≤ d + 1) :
    lcoeff
        ((qPochhammer (Qpow (B : ℤ)) (d + 1) *
            gaussianBinom (Qpow (B : ℤ)) (2 * (d + 1)) ((d + 1) + r)) *
          jTermLaurent (A : ℤ) (B : ℤ) (r : ℤ))
        (d : ℤ) =
      if jExp (A : ℤ) (B : ℤ) (r : ℤ) = (d : ℤ) then
        negOnePowIntQ (r : ℤ) else 0 := by
  rw [lcoeff_mul_jTermLaurent]
  have hlow := degree_sub_lt_center_start A B d r hA hAB hr (r : ℤ) (by
    rw [abs_of_nonneg]
    exact Int.natCast_nonneg r)
  have hcorr := lcoeff_qPochhammer_mul_gaussian_center_add_low_int
    B (d + 1) r (by omega : 0 < B) hr
    ((d : ℤ) - jExp (A : ℤ) (B : ℤ) (r : ℤ)) hlow
  rw [hcorr]
  by_cases heq : jExp (A : ℤ) (B : ℤ) (r : ℤ) = (d : ℤ)
  · simp [heq]
  · have htne : (d : ℤ) - jExp (A : ℤ) (B : ℤ) (r : ℤ) ≠ 0 := by omega
    simp [heq, htne]

theorem lcoeff_center_sub_mul_jTerm_eq_of_succ_degree
    (A B d r : ℕ) (hA : 0 < A) (hAB : A < B) (hr : r ≤ d + 1) :
    lcoeff
        ((qPochhammer (Qpow (B : ℤ)) (d + 1) *
            gaussianBinom (Qpow (B : ℤ)) (2 * (d + 1)) ((d + 1) - r)) *
          jTermLaurent (A : ℤ) (B : ℤ) (-(r : ℤ)))
        (d : ℤ) =
      if jExp (A : ℤ) (B : ℤ) (-(r : ℤ)) = (d : ℤ) then
        negOnePowIntQ (-(r : ℤ)) else 0 := by
  rw [lcoeff_mul_jTermLaurent]
  have hlow := degree_sub_lt_center_start A B d r hA hAB hr (-(r : ℤ)) (by
    rw [abs_of_nonpos]
    · simp
    · exact neg_nonpos.mpr (Int.natCast_nonneg r))
  have hcorr := lcoeff_qPochhammer_mul_gaussian_center_sub_low_int
    B (d + 1) r (by omega : 0 < B) hr
    ((d : ℤ) - jExp (A : ℤ) (B : ℤ) (-(r : ℤ))) hlow
  rw [hcorr]
  by_cases heq : jExp (A : ℤ) (B : ℤ) (-(r : ℤ)) = (d : ℤ)
  · simp [heq]
  · have htne : (d : ℤ) - jExp (A : ℤ) (B : ℤ) (-(r : ℤ)) ≠ 0 := by omega
    simp [heq, htne]

theorem sum_range_center_eq_sum_Icc {M : Type*} [AddCommMonoid M]
    (F : ℤ → M) (N : ℕ) :
    (∑ k ∈ Finset.range (2 * N + 1), F ((k : ℤ) - (N : ℤ))) =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), F n := by
  symm
  refine Finset.sum_bij' (fun n _ => (n + (N : ℤ)).toNat)
    (fun k _ => (k : ℤ) - (N : ℤ)) ?to_mem ?from_mem ?left_inv ?right_inv ?terms
  · intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_range]
    have hnonneg : 0 ≤ n + (N : ℤ) := by omega
    have hcast : (((n + (N : ℤ)).toNat : ℕ) : ℤ) = n + (N : ℤ) :=
      Int.toNat_of_nonneg hnonneg
    have hltz : (((n + (N : ℤ)).toNat : ℕ) : ℤ) < (2 * N + 1 : ℕ) := by
      rw [hcast]
      norm_num
      omega
    exact_mod_cast hltz
  · intro k hk
    rw [Finset.mem_range] at hk
    have hkz : (k : ℤ) < (2 * N + 1 : ℕ) := by
      exact_mod_cast hk
    rw [Finset.mem_Icc]
    constructor
    · change -(N : ℤ) ≤ (k : ℤ) - (N : ℤ)
      omega
    · change (k : ℤ) - (N : ℤ) ≤ (N : ℤ)
      omega
  · intro n hn
    rw [Finset.mem_Icc] at hn
    have hnonneg : 0 ≤ n + (N : ℤ) := by omega
    have hcast : (((n + (N : ℤ)).toNat : ℕ) : ℤ) = n + (N : ℤ) :=
      Int.toNat_of_nonneg hnonneg
    change (((n + (N : ℤ)).toNat : ℤ) - (N : ℤ)) = n
    rw [hcast]
    omega
  · intro k hk
    rw [Finset.mem_range] at hk
    have hnonneg : 0 ≤ (k : ℤ) - (N : ℤ) + (N : ℤ) := by omega
    have hcast :
        ((((k : ℤ) - (N : ℤ) + (N : ℤ)).toNat : ℕ) : ℤ) =
          (k : ℤ) - (N : ℤ) + (N : ℤ) :=
      Int.toNat_of_nonneg hnonneg
    apply Nat.cast_injective (R := ℤ)
    rw [hcast]
    omega
  · intro n hn
    rw [Finset.mem_Icc] at hn
    have hnonneg : 0 ≤ n + (N : ℤ) := by omega
    have hcast : (((n + (N : ℤ)).toNat : ℕ) : ℤ) = n + (N : ℤ) :=
      Int.toNat_of_nonneg hnonneg
    congr 1
    rw [hcast]
    omega

theorem jCoeff_eq_sum_Icc_succ_degree (A B d : ℕ) (hA : 0 < A) (hAB : A < B) :
    jCoeff (A : ℤ) (B : ℤ) (d : ℤ) =
      ∑ n ∈ Finset.Icc (-(d + 1 : ℤ)) (d + 1 : ℤ),
        if jExp (A : ℤ) (B : ℤ) n = (d : ℤ) then negOnePowIntQ n else 0 := by
  let W : ℤ := max (jCoeffWindow (A : ℤ) (B : ℤ) (d : ℤ)) (d + 1 : ℤ)
  have hW : jCoeffWindow (A : ℤ) (B : ℤ) (d : ℤ) ≤ W := by
    dsimp [W]
    exact le_max_left _ _
  have hNleW : (d + 1 : ℤ) ≤ W := by
    dsimp [W]
    exact le_max_right _ _
  rw [jCoeff_eq_sum_Icc_of_window_le (A : ℤ) (B : ℤ) (d : ℤ) W (by omega) hW]
  let S : Finset ℤ := Finset.Icc (-(d + 1 : ℤ)) (d + 1 : ℤ)
  let T : Finset ℤ := Finset.Icc (-W) W
  have hSsubT : S ⊆ T := by
    intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    constructor <;> omega
  symm
  refine Finset.sum_subset hSsubT ?_
  intro n hnT hnS
  rw [Finset.mem_Icc] at hnT
  by_cases hroot : jExp (A : ℤ) (B : ℤ) n = (d : ℤ)
  · have habs := abs_le_jExp_of_pos_lt (A : ℤ) (B : ℤ) n (by omega) (by omega)
    have hn_abs_le : |n| ≤ (d : ℤ) := by omega
    exfalso
    apply hnS
    rw [Finset.mem_Icc]
    have hn_le : n ≤ (d : ℤ) := le_trans (le_abs_self n) hn_abs_le
    have hneg_le : -(d : ℤ) ≤ n := by
      have h := neg_abs_le n
      omega
    constructor <;> omega
  · simp [hroot]

theorem lcoeff_jTripleProductPartialLaurent_eq_jCoeff_succ_degree
    (A B d : ℕ) (hA : 0 < A) (hAB : A < B) :
    lcoeff (jTripleProductPartialLaurent (A : ℤ) (B : ℤ) (d + 1)) (d : ℤ) =
      jCoeff (A : ℤ) (B : ℤ) (d : ℤ) := by
  let N : ℕ := d + 1
  have hsum :
      lcoeff (jTripleProductPartialLaurent (A : ℤ) (B : ℤ) N) (d : ℤ) =
        ∑ k ∈ Finset.range (2 * N + 1),
          lcoeff
            (qPochhammer (Qpow (B : ℤ)) N *
              (gaussianBinom (Qpow (B : ℤ)) (2 * N) k *
                jTermLaurent (A : ℤ) (B : ℤ) ((k : ℤ) - (N : ℤ))))
            (d : ℤ) := by
    rw [jTripleProductPartialLaurent_eq_qPochhammer_mul_finiteJTPRHS,
      finiteJTPRHS_Qpow_eq_natSum_jTerm]
    rw [QseriesFormalization.PartI.Ch03.natSum_eq_sum_range]
    simp only [Finset.mul_sum]
    simp [lcoeff]
  rw [hsum]
  have hterms :
      (∑ k ∈ Finset.range (2 * N + 1),
          lcoeff
            (qPochhammer (Qpow (B : ℤ)) N *
              (gaussianBinom (Qpow (B : ℤ)) (2 * N) k *
                jTermLaurent (A : ℤ) (B : ℤ) ((k : ℤ) - (N : ℤ))))
            (d : ℤ)) =
        ∑ k ∈ Finset.range (2 * N + 1),
          if jExp (A : ℤ) (B : ℤ) ((k : ℤ) - (N : ℤ)) = (d : ℤ) then
            negOnePowIntQ ((k : ℤ) - (N : ℤ)) else 0 := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [Finset.mem_range] at hk
    have hk_le : k ≤ 2 * N := by omega
    by_cases hNk : N ≤ k
    · let r : ℕ := k - N
      have hr : r ≤ d + 1 := by
        dsimp [r, N]
        omega
      have hk_eq : k = N + r := by
        dsimp [r]
        omega
      have hn_eq : (k : ℤ) - (N : ℤ) = (r : ℤ) := by
        dsimp [r]
        omega
      subst N
      have hn_r : ((d + 1 + r : ℕ) : ℤ) - ((d + 1 : ℕ) : ℤ) = (r : ℤ) := by
        omega
      rw [hk_eq, hn_r]
      rw [show qPochhammer (Qpow (B : ℤ)) (d + 1) *
          (gaussianBinom (Qpow (B : ℤ)) (2 * (d + 1)) ((d + 1) + r) *
            jTermLaurent (A : ℤ) (B : ℤ) (r : ℤ)) =
          (qPochhammer (Qpow (B : ℤ)) (d + 1) *
            gaussianBinom (Qpow (B : ℤ)) (2 * (d + 1)) ((d + 1) + r)) *
              jTermLaurent (A : ℤ) (B : ℤ) (r : ℤ) by ring]
      exact lcoeff_center_add_mul_jTerm_eq_of_succ_degree A B d r hA hAB hr
    · let r : ℕ := N - k
      have hr : r ≤ d + 1 := by
        dsimp [r, N]
        omega
      have hk_eq : k = N - r := by
        dsimp [r]
        omega
      have hn_eq : (k : ℤ) - (N : ℤ) = -(r : ℤ) := by
        dsimp [r]
        omega
      subst N
      have hn_r : ((d + 1 - r : ℕ) : ℤ) - ((d + 1 : ℕ) : ℤ) = -(r : ℤ) := by
        omega
      rw [hk_eq, hn_r]
      rw [show qPochhammer (Qpow (B : ℤ)) (d + 1) *
          (gaussianBinom (Qpow (B : ℤ)) (2 * (d + 1)) ((d + 1) - r) *
            jTermLaurent (A : ℤ) (B : ℤ) (-(r : ℤ))) =
          (qPochhammer (Qpow (B : ℤ)) (d + 1) *
            gaussianBinom (Qpow (B : ℤ)) (2 * (d + 1)) ((d + 1) - r)) *
              jTermLaurent (A : ℤ) (B : ℤ) (-(r : ℤ)) by ring]
      exact lcoeff_center_sub_mul_jTerm_eq_of_succ_degree A B d r hA hAB hr
  rw [hterms]
  rw [sum_range_center_eq_sum_Icc
    (fun n : ℤ =>
      if jExp (A : ℤ) (B : ℤ) n = (d : ℤ) then negOnePowIntQ n else 0) N]
  dsimp [N]
  exact (jCoeff_eq_sum_Icc_succ_degree A B d hA hAB).symm

theorem jTripleProductPartialLaurent_eq_coe_partial_jTripleFactorPS
    (A B N : ℕ) (hAB : A < B) :
    jTripleProductPartialLaurent (A : ℤ) (B : ℤ) N =
      ((∏ n ∈ Finset.range N, jTripleFactorPS ℚ A B n : ℚ⟦X⟧) : QLaurent) := by
  unfold jTripleProductPartialLaurent jFiniteProductLaurent
  have hsub : Qpow ((B : ℤ) - (A : ℤ)) = Qpow ((B - A : ℕ) : ℤ) := by
    congr 1
    omega
  rw [hsub]
  rw [qPochhammer_Qpow_eq_coe_apFinitePS B N,
    qPoch_Qpow_eq_coe_apFinitePS A B N,
    qPoch_Qpow_eq_coe_apFinitePS (B - A) B N]
  rw [← PowerSeries.coe_mul, ← PowerSeries.coe_mul]
  congr 1
  simp [jTripleFactorPS, Finset.prod_mul_distrib, mul_assoc]

theorem jCoeff_eq_zero_of_neg_of_pos_lt
    (A B : ℕ) (hA : 0 < A) (hAB : A < B) {e : ℤ} (he : e < 0) :
    jCoeff (A : ℤ) (B : ℤ) e = 0 := by
  rw [jCoeff_eq_window_sum (A : ℤ) (B : ℤ) e (by omega)]
  refine Finset.sum_eq_zero ?_
  intro n _hn
  by_cases hroot : jExp (A : ℤ) (B : ℤ) n = e
  · have hnonneg := jExp_nonneg_of_pos_lt (A : ℤ) (B : ℤ) n (by omega) (by omega)
    omega
  · simp [hroot]

theorem jLaurent_nat_eq_jTripleProductInfPS
    (A B : ℕ) (hA : 0 < A) (hAB : A < B) :
    jLaurent (A : ℤ) (B : ℤ) =
      ((jTripleProductInfPS A B : ℚ⟦X⟧) : QLaurent) := by
  ext e
  change lcoeff (jLaurent (A : ℤ) (B : ℤ)) e =
    lcoeff ((jTripleProductInfPS A B : ℚ⟦X⟧) : QLaurent) e
  by_cases he : e < 0
  · rw [coeff_jLaurent, jCoeff_eq_zero_of_neg_of_pos_lt A B hA hAB he]
    rw [lcoeff, PowerSeries.coeff_coe]
    simp [he]
  · have he_nonneg : 0 ≤ e := by omega
    let d : ℕ := e.toNat
    have hd : (d : ℤ) = e := by
      dsimp [d]
      exact Int.toNat_of_nonneg he_nonneg
    rw [← hd]
    calc
      lcoeff (jLaurent (A : ℤ) (B : ℤ)) (d : ℤ)
          = jCoeff (A : ℤ) (B : ℤ) (d : ℤ) := by
              rw [coeff_jLaurent]
      _ = lcoeff (jTripleProductPartialLaurent (A : ℤ) (B : ℤ) (d + 1)) (d : ℤ) := by
              exact (lcoeff_jTripleProductPartialLaurent_eq_jCoeff_succ_degree A B d hA hAB).symm
      _ = lcoeff (((∏ n ∈ Finset.range (d + 1), jTripleFactorPS ℚ A B n : ℚ⟦X⟧) :
            QLaurent)) (d : ℤ) := by
              rw [jTripleProductPartialLaurent_eq_coe_partial_jTripleFactorPS A B (d + 1) hAB]
      _ = PowerSeries.coeff d
            (∏ n ∈ Finset.range (d + 1), jTripleFactorPS ℚ A B n) := by
              rw [lcoeff, LaurentSeries.coeff_coe_powerSeries]
      _ = PowerSeries.coeff d (jTripleProductInfPS A B) := by
              exact (coeff_jTripleProductInfPS_eq_coeff_partial A B d hA hAB).symm
      _ = lcoeff ((jTripleProductInfPS A B : ℚ⟦X⟧) : QLaurent) (d : ℤ) := by
              rw [lcoeff, LaurentSeries.coeff_coe_powerSeries]

theorem jLaurent_eq_tripleProductInf (a b : ℤ) (ha : 0 < a) (hab : a < b) :
    jLaurent a b =
      ((qPochAPPS ℚ b.toNat b.toNat : ℚ⟦X⟧) : QLaurent) *
        ((qPochAPPS ℚ a.toNat b.toNat : ℚ⟦X⟧) : QLaurent) *
          ((qPochAPPS ℚ (b - a).toNat b.toNat : ℚ⟦X⟧) : QLaurent) := by
  let A : ℕ := a.toNat
  let B : ℕ := b.toNat
  have hA : 0 < A := by
    dsimp [A]
    omega
  have hAB : A < B := by
    dsimp [A, B]
    omega
  have hAcast : (A : ℤ) = a := by
    dsimp [A]
    omega
  have hBcast : (B : ℤ) = b := by
    dsimp [B]
    omega
  have hsub : B - A = (b - a).toNat := by
    dsimp [A, B]
    omega
  have hnat := jLaurent_nat_eq_jTripleProductInfPS A B hA hAB
  rw [← hAcast, ← hBcast]
  rw [hnat]
  unfold jTripleProductInfPS
  rw [PowerSeries.coe_mul, PowerSeries.coe_mul]
  rw [show ((B : ℤ).toNat) = B by omega,
    show ((A : ℤ).toNat) = A by omega,
    show (((B : ℤ) - (A : ℤ)).toNat) = B - A by omega]

/-! ## AP refinement to level 90 -/

private def finSigmaNatEquivNat (k : ℕ) (hk : k ≠ 0) :
    (Sigma fun _ : Fin k => ℕ) ≃ ℕ where
  toFun p := k * p.2 + p.1.val
  invFun n := Sigma.mk ⟨n % k, Nat.mod_lt n (Nat.pos_of_ne_zero hk)⟩ (n / k)
  left_inv := by
    rintro ⟨i, n⟩
    simp
    constructor
    · ext
      exact Nat.mod_eq_of_lt i.2
    · have hi : i.val < k := i.2
      rw [Nat.mul_add_div (Nat.pos_of_ne_zero hk), Nat.div_eq_of_lt hi, add_zero]
  right_inv := by
    intro n
    exact Nat.div_add_mod n k

private theorem Fin_prod_univ_ten {M : Type*} [CommMonoid M] (f : Fin 10 → M) :
    (∏ i, f i) =
      f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 * f 8 * f 9 := by
  rw [show (Finset.univ : Finset (Fin 10)) = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} by
    ext i
    fin_cases i <;> simp]
  simp
  ac_rfl

/-- Arithmetic-progression refinement of formal q-Pochhammer products. -/
theorem qPochAPPS_refine_mul_rat (r m k : ℕ) (hm : 0 < m) (hk : k ≠ 0) :
    qPochAPPS ℚ r m =
      ∏ i : Fin k, qPochAPPS ℚ (r + m * i.val) (m * k) := by
  let f : ℕ → PowerSeries ℚ := fun n => apFactorPS ℚ r m n
  let e : (Sigma fun _ : Fin k => ℕ) ≃ ℕ := finSigmaNatEquivNat k hk
  let g : Fin k → PowerSeries ℚ := fun i => qPochAPPS ℚ (r + m * i.val) (m * k)
  have hf : HasProd f (qPochAPPS ℚ r m) := hasProd_qPochAPPS ℚ r m hm
  have hsig : HasProd (f ∘ e) (qPochAPPS ℚ r m) :=
    (Equiv.hasProd_iff e).mpr hf
  have hfiber : ∀ i : Fin k,
      HasProd (fun n : ℕ => (f ∘ e) ⟨i, n⟩) (g i) := by
    intro i
    convert hasProd_qPochAPPS ℚ (r + m * i.val) (m * k)
      (Nat.mul_pos hm (Nat.pos_of_ne_zero hk)) using 1
    ext n
    simp [f, e, finSigmaNatEquivNat, apFactorPS]
    congr 1
    ring_nf
  have hfin : HasProd g (qPochAPPS ℚ r m) := hsig.sigma hfiber
  have hfin' : HasProd g (∏ i : Fin k, g i) := hasProd_fintype _
  exact hfin.unique hfin'

/-- Level-90 refinement of formal q-Pochhammer products. -/
theorem qPochAPPS_refine_90_rat (r m : ℕ) (hdiv : m ∣ 90) (hm : 0 < m) :
    qPochAPPS ℚ r m =
      ∏ i : Fin (90 / m), qPochAPPS ℚ (r + m * i.val) 90 := by
  have hmul : m * (90 / m) = 90 := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel hdiv
  have hk : 90 / m ≠ 0 := by
    intro hz
    have hzero : m * (90 / m) = 0 := by simp [hz]
    omega
  simpa [hmul] using qPochAPPS_refine_mul_rat r m (90 / m) hm hk

noncomputable abbrev qPochAPLaurent (r m : ℕ) : QLaurent :=
  ((qPochAPPS ℚ r m : PowerSeries ℚ) : QLaurent)

/-- Laurent-series version of arithmetic-progression refinement. -/
theorem qPochAPLaurent_refine_mul (r m k : ℕ) (hm : 0 < m) (hk : k ≠ 0) :
    qPochAPLaurent r m =
      ∏ i : Fin k, qPochAPLaurent (r + m * i.val) (m * k) := by
  change (HahnSeries.ofPowerSeries ℤ ℚ) (qPochAPPS ℚ r m) =
    ∏ i : Fin k, (HahnSeries.ofPowerSeries ℤ ℚ)
      (qPochAPPS ℚ (r + m * i.val) (m * k))
  rw [qPochAPPS_refine_mul_rat r m k hm hk]
  rw [map_prod]

/-- Laurent-series level-90 refinement for the AP factors in the Ch10 bridge. -/
theorem qPochAPLaurent_refine_90 (r m : ℕ) (hdiv : m ∣ 90) (hm : 0 < m) :
    qPochAPLaurent r m =
      ∏ i : Fin (90 / m), qPochAPLaurent (r + m * i.val) 90 := by
  have hmul : m * (90 / m) = 90 := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel hdiv
  have hk : 90 / m ≠ 0 := by
    intro hz
    have hzero : m * (90 / m) = 0 := by simp [hz]
    omega
  simpa [hmul] using qPochAPLaurent_refine_mul r m (90 / m) hm hk

private theorem qAP_3_18_refine_90 :
    qPochAPLaurent 3 18 =
      qPochAPLaurent 3 90 * qPochAPLaurent 21 90 * qPochAPLaurent 39 90 *
        qPochAPLaurent 57 90 * qPochAPLaurent 75 90 := by
  rw [qPochAPLaurent_refine_90 3 18 (by norm_num) (by norm_num)]
  rw [Fin.prod_univ_five]
  norm_num

private theorem qAP_6_18_refine_90 :
    qPochAPLaurent 6 18 =
      qPochAPLaurent 6 90 * qPochAPLaurent 24 90 * qPochAPLaurent 42 90 *
        qPochAPLaurent 60 90 * qPochAPLaurent 78 90 := by
  rw [qPochAPLaurent_refine_90 6 18 (by norm_num) (by norm_num)]
  rw [Fin.prod_univ_five]
  norm_num

private theorem qAP_9_18_refine_90 :
    qPochAPLaurent 9 18 =
      qPochAPLaurent 9 90 * qPochAPLaurent 27 90 * qPochAPLaurent 45 90 *
        qPochAPLaurent 63 90 * qPochAPLaurent 81 90 := by
  rw [qPochAPLaurent_refine_90 9 18 (by norm_num) (by norm_num)]
  rw [Fin.prod_univ_five]
  norm_num

private theorem qAP_12_18_refine_90 :
    qPochAPLaurent 12 18 =
      qPochAPLaurent 12 90 * qPochAPLaurent 30 90 * qPochAPLaurent 48 90 *
        qPochAPLaurent 66 90 * qPochAPLaurent 84 90 := by
  rw [qPochAPLaurent_refine_90 12 18 (by norm_num) (by norm_num)]
  rw [Fin.prod_univ_five]
  norm_num

private theorem qAP_15_18_refine_90 :
    qPochAPLaurent 15 18 =
      qPochAPLaurent 15 90 * qPochAPLaurent 33 90 * qPochAPLaurent 51 90 *
        qPochAPLaurent 69 90 * qPochAPLaurent 87 90 := by
  rw [qPochAPLaurent_refine_90 15 18 (by norm_num) (by norm_num)]
  rw [Fin.prod_univ_five]
  norm_num

private theorem qAP_18_18_refine_90 :
    qPochAPLaurent 18 18 =
      qPochAPLaurent 18 90 * qPochAPLaurent 36 90 * qPochAPLaurent 54 90 *
        qPochAPLaurent 72 90 * qPochAPLaurent 90 90 := by
  rw [qPochAPLaurent_refine_90 18 18 (by norm_num) (by norm_num)]
  rw [Fin.prod_univ_five]
  norm_num

private theorem qAP_3_9_refine_90 :
    qPochAPLaurent 3 9 =
      qPochAPLaurent 3 90 * qPochAPLaurent 12 90 * qPochAPLaurent 21 90 *
        qPochAPLaurent 30 90 * qPochAPLaurent 39 90 * qPochAPLaurent 48 90 *
          qPochAPLaurent 57 90 * qPochAPLaurent 66 90 * qPochAPLaurent 75 90 *
            qPochAPLaurent 84 90 := by
  rw [qPochAPLaurent_refine_90 3 9 (by norm_num) (by norm_num)]
  rw [Fin_prod_univ_ten]
  norm_num

private theorem qAP_6_9_refine_90 :
    qPochAPLaurent 6 9 =
      qPochAPLaurent 6 90 * qPochAPLaurent 15 90 * qPochAPLaurent 24 90 *
        qPochAPLaurent 33 90 * qPochAPLaurent 42 90 * qPochAPLaurent 51 90 *
          qPochAPLaurent 60 90 * qPochAPLaurent 69 90 * qPochAPLaurent 78 90 *
            qPochAPLaurent 87 90 := by
  rw [qPochAPLaurent_refine_90 6 9 (by norm_num) (by norm_num)]
  rw [Fin_prod_univ_ten]
  norm_num

private theorem qAP_9_9_refine_90 :
    qPochAPLaurent 9 9 =
      qPochAPLaurent 9 90 * qPochAPLaurent 18 90 * qPochAPLaurent 27 90 *
        qPochAPLaurent 36 90 * qPochAPLaurent 45 90 * qPochAPLaurent 54 90 *
          qPochAPLaurent 63 90 * qPochAPLaurent 72 90 * qPochAPLaurent 81 90 *
            qPochAPLaurent 90 90 := by
  rw [qPochAPLaurent_refine_90 9 9 (by norm_num) (by norm_num)]
  rw [Fin_prod_univ_ten]
  norm_num

private theorem qAP_3_15_refine_90 :
    qPochAPLaurent 3 15 =
      qPochAPLaurent 3 90 * qPochAPLaurent 18 90 * qPochAPLaurent 33 90 *
        qPochAPLaurent 48 90 * qPochAPLaurent 63 90 * qPochAPLaurent 78 90 := by
  rw [qPochAPLaurent_refine_90 3 15 (by norm_num) (by norm_num)]
  rw [Fin.prod_univ_six]
  norm_num

private theorem qAP_12_15_refine_90 :
    qPochAPLaurent 12 15 =
      qPochAPLaurent 12 90 * qPochAPLaurent 27 90 * qPochAPLaurent 42 90 *
        qPochAPLaurent 57 90 * qPochAPLaurent 72 90 * qPochAPLaurent 87 90 := by
  rw [qPochAPLaurent_refine_90 12 15 (by norm_num) (by norm_num)]
  rw [Fin.prod_univ_six]
  norm_num

private theorem qAP_15_15_refine_90 :
    qPochAPLaurent 15 15 =
      qPochAPLaurent 15 90 * qPochAPLaurent 30 90 * qPochAPLaurent 45 90 *
        qPochAPLaurent 60 90 * qPochAPLaurent 75 90 * qPochAPLaurent 90 90 := by
  rw [qPochAPLaurent_refine_90 15 15 (by norm_num) (by norm_num)]
  rw [Fin.prod_univ_six]
  norm_num

theorem jLaurent_90_270_eq_qPochAPLaurent_90_90 :
    jLaurent 90 270 = qPochAPLaurent 90 90 := by
  rw [jLaurent_eq_tripleProductInf 90 270 (by norm_num) (by norm_num)]
  change qPochAPLaurent 270 270 * qPochAPLaurent 90 270 *
      qPochAPLaurent 180 270 = qPochAPLaurent 90 90
  rw [qPochAPLaurent_refine_mul 90 90 3 (by norm_num) (by norm_num)]
  rw [Fin.prod_univ_three]
  norm_num
  ring

/-- Normalized level-90 theta atom with the common `K=(Q^90;Q^90)_∞`
factor removed from `jLaurent a 90`. -/
noncomputable def redJ (a : ℕ) : QLaurent :=
  qPochAPLaurent a 90 * qPochAPLaurent (90 - a) 90

theorem redJ_eq_qPochAPLaurent (a : ℕ) :
    redJ a = qPochAPLaurent a 90 * qPochAPLaurent (90 - a) 90 := rfl

theorem jLaurent_eq_JOne_mul_redJ (a : ℕ) (ha0 : 0 < a) (ha90 : a < 90) :
    jLaurent (a : ℤ) 90 = jLaurent 90 270 * redJ a := by
  rw [jLaurent_eq_tripleProductInf (a : ℤ) 90 (by omega) (by omega),
    jLaurent_90_270_eq_qPochAPLaurent_90_90]
  have ha_toNat : ((a : ℤ).toNat) = a := by omega
  have hsub : (90 - (a : ℤ)).toNat = 90 - a := by omega
  rw [ha_toNat, hsub]
  change qPochAPLaurent 90 90 * qPochAPLaurent a 90 *
      qPochAPLaurent (90 - a) 90 =
    qPochAPLaurent 90 90 *
      (qPochAPLaurent a 90 * qPochAPLaurent (90 - a) 90)
  ring

theorem J_3_18_bridge :
    jLaurent 3 18 * jLaurent 90 270 ^ 6 =
      jLaurent 3 90 * jLaurent 15 90 * jLaurent 18 90 *
        jLaurent 21 90 * jLaurent 33 90 * jLaurent 36 90 *
          jLaurent 39 90 := by
  rw [jLaurent_eq_tripleProductInf 3 18 (by norm_num) (by norm_num),
    jLaurent_90_270_eq_qPochAPLaurent_90_90,
    jLaurent_eq_tripleProductInf 3 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 15 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 18 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 21 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 33 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 36 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 39 90 (by norm_num) (by norm_num)]
  change (qPochAPLaurent 18 18 * qPochAPLaurent 3 18 *
      qPochAPLaurent 15 18) * qPochAPLaurent 90 90 ^ 6 =
    (qPochAPLaurent 90 90 * qPochAPLaurent 3 90 * qPochAPLaurent 87 90) *
      (qPochAPLaurent 90 90 * qPochAPLaurent 15 90 * qPochAPLaurent 75 90) *
        (qPochAPLaurent 90 90 * qPochAPLaurent 18 90 * qPochAPLaurent 72 90) *
          (qPochAPLaurent 90 90 * qPochAPLaurent 21 90 *
            qPochAPLaurent 69 90) *
            (qPochAPLaurent 90 90 * qPochAPLaurent 33 90 *
              qPochAPLaurent 57 90) *
              (qPochAPLaurent 90 90 * qPochAPLaurent 36 90 *
                qPochAPLaurent 54 90) *
                (qPochAPLaurent 90 90 * qPochAPLaurent 39 90 *
                  qPochAPLaurent 51 90)
  rw [qAP_18_18_refine_90, qAP_3_18_refine_90, qAP_15_18_refine_90]
  ring

theorem J_6_18_bridge :
    jLaurent 6 18 * jLaurent 90 270 ^ 6 =
      jLaurent 6 90 * jLaurent 12 90 * jLaurent 18 90 *
        jLaurent 24 90 * jLaurent 30 90 * jLaurent 36 90 *
          jLaurent 42 90 := by
  rw [jLaurent_eq_tripleProductInf 6 18 (by norm_num) (by norm_num),
    jLaurent_90_270_eq_qPochAPLaurent_90_90,
    jLaurent_eq_tripleProductInf 6 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 12 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 18 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 24 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 30 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 36 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 42 90 (by norm_num) (by norm_num)]
  change (qPochAPLaurent 18 18 * qPochAPLaurent 6 18 *
      qPochAPLaurent 12 18) * qPochAPLaurent 90 90 ^ 6 =
    (qPochAPLaurent 90 90 * qPochAPLaurent 6 90 * qPochAPLaurent 84 90) *
      (qPochAPLaurent 90 90 * qPochAPLaurent 12 90 * qPochAPLaurent 78 90) *
        (qPochAPLaurent 90 90 * qPochAPLaurent 18 90 * qPochAPLaurent 72 90) *
          (qPochAPLaurent 90 90 * qPochAPLaurent 24 90 *
            qPochAPLaurent 66 90) *
            (qPochAPLaurent 90 90 * qPochAPLaurent 30 90 *
              qPochAPLaurent 60 90) *
              (qPochAPLaurent 90 90 * qPochAPLaurent 36 90 *
                qPochAPLaurent 54 90) *
                (qPochAPLaurent 90 90 * qPochAPLaurent 42 90 *
                  qPochAPLaurent 48 90)
  rw [qAP_18_18_refine_90, qAP_6_18_refine_90, qAP_12_18_refine_90]
  ring

theorem J_9_18_bridge :
    jLaurent 9 18 * jLaurent 90 270 ^ 6 =
      (jLaurent 9 90) ^ 2 * jLaurent 18 90 * (jLaurent 27 90) ^ 2 *
        jLaurent 36 90 * jLaurent 45 90 := by
  rw [jLaurent_eq_tripleProductInf 9 18 (by norm_num) (by norm_num),
    jLaurent_90_270_eq_qPochAPLaurent_90_90,
    jLaurent_eq_tripleProductInf 9 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 18 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 27 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 36 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 45 90 (by norm_num) (by norm_num)]
  change (qPochAPLaurent 18 18 * qPochAPLaurent 9 18 *
      qPochAPLaurent 9 18) * qPochAPLaurent 90 90 ^ 6 =
    (qPochAPLaurent 90 90 * qPochAPLaurent 9 90 * qPochAPLaurent 81 90) ^ 2 *
      (qPochAPLaurent 90 90 * qPochAPLaurent 18 90 * qPochAPLaurent 72 90) *
        (qPochAPLaurent 90 90 * qPochAPLaurent 27 90 *
          qPochAPLaurent 63 90) ^ 2 *
          (qPochAPLaurent 90 90 * qPochAPLaurent 36 90 *
            qPochAPLaurent 54 90) *
            (qPochAPLaurent 90 90 * qPochAPLaurent 45 90 *
              qPochAPLaurent 45 90)
  rw [qAP_18_18_refine_90, qAP_9_18_refine_90]
  ring

set_option maxRecDepth 4000 in
theorem J_3_9_pow5_J_3_15_bridge :
    (jLaurent 3 9) ^ 5 * jLaurent 3 15 * jLaurent 90 270 ^ 75 =
      (jLaurent 3 90) ^ 6 * (jLaurent 6 90) ^ 5 *
        (jLaurent 9 90) ^ 5 * (jLaurent 12 90) ^ 6 *
          (jLaurent 15 90) ^ 6 * (jLaurent 18 90) ^ 6 *
            (jLaurent 21 90) ^ 5 * (jLaurent 24 90) ^ 5 *
              (jLaurent 27 90) ^ 6 * (jLaurent 30 90) ^ 6 *
                (jLaurent 33 90) ^ 6 * (jLaurent 36 90) ^ 5 *
                  (jLaurent 39 90) ^ 5 * (jLaurent 42 90) ^ 6 *
                    (jLaurent 45 90) ^ 3 := by
  rw [jLaurent_eq_tripleProductInf 3 9 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 3 15 (by norm_num) (by norm_num),
    jLaurent_90_270_eq_qPochAPLaurent_90_90,
    jLaurent_eq_tripleProductInf 3 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 6 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 9 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 12 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 15 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 18 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 21 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 24 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 27 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 30 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 33 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 36 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 39 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 42 90 (by norm_num) (by norm_num),
    jLaurent_eq_tripleProductInf 45 90 (by norm_num) (by norm_num)]
  change (qPochAPLaurent 9 9 * qPochAPLaurent 3 9 *
      qPochAPLaurent 6 9) ^ 5 *
      (qPochAPLaurent 15 15 * qPochAPLaurent 3 15 *
        qPochAPLaurent 12 15) * qPochAPLaurent 90 90 ^ 75 =
    (qPochAPLaurent 90 90 * qPochAPLaurent 3 90 * qPochAPLaurent 87 90) ^ 6 *
      (qPochAPLaurent 90 90 * qPochAPLaurent 6 90 *
        qPochAPLaurent 84 90) ^ 5 *
        (qPochAPLaurent 90 90 * qPochAPLaurent 9 90 *
          qPochAPLaurent 81 90) ^ 5 *
          (qPochAPLaurent 90 90 * qPochAPLaurent 12 90 *
            qPochAPLaurent 78 90) ^ 6 *
            (qPochAPLaurent 90 90 * qPochAPLaurent 15 90 *
              qPochAPLaurent 75 90) ^ 6 *
              (qPochAPLaurent 90 90 * qPochAPLaurent 18 90 *
                qPochAPLaurent 72 90) ^ 6 *
                (qPochAPLaurent 90 90 * qPochAPLaurent 21 90 *
                  qPochAPLaurent 69 90) ^ 5 *
                  (qPochAPLaurent 90 90 * qPochAPLaurent 24 90 *
                    qPochAPLaurent 66 90) ^ 5 *
                    (qPochAPLaurent 90 90 * qPochAPLaurent 27 90 *
                      qPochAPLaurent 63 90) ^ 6 *
                      (qPochAPLaurent 90 90 * qPochAPLaurent 30 90 *
                        qPochAPLaurent 60 90) ^ 6 *
                        (qPochAPLaurent 90 90 * qPochAPLaurent 33 90 *
                          qPochAPLaurent 57 90) ^ 6 *
                          (qPochAPLaurent 90 90 * qPochAPLaurent 36 90 *
                            qPochAPLaurent 54 90) ^ 5 *
                            (qPochAPLaurent 90 90 * qPochAPLaurent 39 90 *
                              qPochAPLaurent 51 90) ^ 5 *
                              (qPochAPLaurent 90 90 * qPochAPLaurent 42 90 *
                                qPochAPLaurent 48 90) ^ 6 *
                                (qPochAPLaurent 90 90 * qPochAPLaurent 45 90 *
                                  qPochAPLaurent 45 90) ^ 3
  rw [qAP_9_9_refine_90, qAP_3_9_refine_90, qAP_6_9_refine_90,
    qAP_15_15_refine_90, qAP_3_15_refine_90, qAP_12_15_refine_90]
  ring

theorem jExp_ne_zero_of_ne_zero_of_pos_lt (a b n : ℤ)
    (ha : 0 < a) (hab : a < b) (hn : n ≠ 0) :
    jExp a b n ≠ 0 := by
  intro hzero
  have htw := two_mul_jExp a b n
  have hpos := jExpTwice_pos_of_ne_zero_of_pos_lt a b n ha hab hn
  nlinarith

theorem jCoeff_zero_of_pos_lt (a b : ℤ) (ha : 0 < a) (hab : a < b) :
    jCoeff a b 0 = 1 := by
  have hb : 0 < b := by omega
  rw [jCoeff_eq_window_sum a b 0 hb]
  rw [Finset.sum_eq_single (0 : ℤ)]
  · norm_num [jExp, negOnePowIntQ]
  · intro n _hn hne
    have hnez : jExp a b n ≠ 0 := jExp_ne_zero_of_ne_zero_of_pos_lt a b n ha hab hne
    by_cases hroot : jExp a b n = 0
    · exact (hnez hroot).elim
    · simp [hroot]
  · intro hnot
    exfalso
    apply hnot
    rw [Finset.mem_Icc]
    have hW : 0 ≤ jCoeffWindow a b 0 := by
      unfold jCoeffWindow
      positivity
    exact ⟨by omega, hW⟩

/-- In the normalized product range `0 < a < b`, the constant coefficient of
`j(Q^a;Q^b)` is `1`, so the Laurent series is a unit denominator. -/
theorem jLaurent_ne_zero_of_pos_lt (a b : ℤ) (ha : 0 < a) (hab : a < b) :
    jLaurent a b ≠ 0 := by
  intro hzero
  have hc := congrArg (fun s : QLaurent => lcoeff s 0) hzero
  change lcoeff (jLaurent a b) 0 = lcoeff (0 : QLaurent) 0 at hc
  rw [coeff_jLaurent, jCoeff_zero_of_pos_lt a b ha hab] at hc
  simp [lcoeff] at hc

theorem negOnePowIntQ_ne_zero (k : ℤ) : negOnePowIntQ k ≠ 0 := by
  unfold negOnePowIntQ
  exact pow_ne_zero _ (by norm_num : (-1 : ℚ) ≠ 0)

theorem jLaurent_ne_zero_of_shift_pos_lt (a b c k : ℤ) (hb : 0 < b)
    (ha : a = c + b * k) (hc : 0 < c) (hcb : c < b) :
    jLaurent a b ≠ 0 := by
  subst a
  rw [jLaurent_shift c b k hb]
  exact smul_ne_zero (negOnePowIntQ_ne_zero k)
    (mul_ne_zero (Qpow_ne_zero (jShiftExp c b k))
      (jLaurent_ne_zero_of_pos_lt c b hc hcb))

theorem jLaurent_isUnit_of_ne_zero (a b : ℤ) (h : jLaurent a b ≠ 0) :
    IsUnit (jLaurent a b) :=
  isUnit_iff_ne_zero.mpr h

theorem jLaurent_90_270_isUnit :
    IsUnit (jLaurent 90 270) :=
  jLaurent_isUnit_of_ne_zero 90 270
    (jLaurent_ne_zero_of_pos_lt 90 270 (by norm_num) (by norm_num))

noncomputable def jLaurentRatio (c1 c2 b : ℤ) : QLaurent :=
  jLaurent c1 b / jLaurent c2 b

theorem jLaurentRatio_isUnit (c1 c2 b : ℤ)
    (hnum : jLaurent c1 b ≠ 0) (hden : jLaurent c2 b ≠ 0) :
    IsUnit (jLaurentRatio c1 c2 b) := by
  unfold jLaurentRatio
  exact isUnit_iff_ne_zero.mpr (div_ne_zero hnum hden)

theorem jLaurentRatio_mul_den (c1 c2 b : ℤ) (hden : jLaurent c2 b ≠ 0) :
    jLaurentRatio c1 c2 b * jLaurent c2 b = jLaurent c1 b := by
  unfold jLaurentRatio
  field_simp [hden]

theorem den_mul_jLaurentRatio (c1 c2 b : ℤ) (hden : jLaurent c2 b ≠ 0) :
    jLaurent c2 b * jLaurentRatio c1 c2 b = jLaurent c1 b := by
  rw [mul_comm, jLaurentRatio_mul_den c1 c2 b hden]

theorem jLaurent_four_product_ne_zero (a z0 z1 : ℤ)
    (hz0 : jLaurent z0 90 ≠ 0) (hz1 : jLaurent z1 90 ≠ 0)
    (hxz0 : jLaurent (a + z0) 90 ≠ 0) (hxz1 : jLaurent (a + z1) 90 ≠ 0) :
    jLaurent z0 90 * jLaurent z1 90 *
        jLaurent (a + z0) 90 * jLaurent (a + z1) 90 ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero hz0 hz1) hxz0) hxz1

/-- Pairing involution behind `j(Q^(18k);Q^18)=0`. -/
theorem jExpTwice_periodic_zero_pair (k n : ℤ) :
    jExpTwice (18 * k) 18 (1 - 2 * k - n) = jExpTwice (18 * k) 18 n := by
  unfold jExpTwice
  ring

theorem appellDenomExp_period_z (a z r : ℤ) :
    appellDenomExp a (z + 90) r = appellDenomExp a z (r + 1) := by
  unfold appellDenomExp
  ring

@[simp] theorem coeff_appellMFE (a z e : ℤ) :
    lcoeff (appellMFE a z) e = appellMFECoeff a z e := rfl

@[simp] theorem appellMFE_period_z (a z : ℤ) :
    appellMFE a (z + 90) = appellMFE a z := by
  simp [appellMFE]

theorem appellMFENonneg_shift (n : ℕ) :
    appellMFENonneg (n + 90) = 1 - Qpow (n : ℤ) * appellMFENonneg n := by
  rw [appellMFENonneg]
  simp

private theorem appellMFEBase_symm_small {b : ℕ} (hb0 : 0 < b) (hb : b < 90) :
    appellMFEBase (90 - b) = 1 - appellMFEBase b := by
  unfold appellMFEBase
  by_cases h45 : b = 45
  · subst h45
    simp
    simpa using half_Q_eq_one_sub_half_Q
  · have hb_ne0 : b ≠ 0 := by omega
    have h90b_ne0 : 90 - b ≠ 0 := by omega
    have hlt_or_gt : 2 * b < 90 ∨ 90 < 2 * b := by omega
    rcases hlt_or_gt with hlt | hgt
    · have h90b_lt_false : ¬ 2 * (90 - b) < 90 := by omega
      have h90b_eq_false : ¬ 2 * (90 - b) = 90 := by omega
      simp [hb_ne0, h90b_ne0, hlt, h90b_lt_false, h90b_eq_false]
    · have hb_lt_false : ¬ 2 * b < 90 := by omega
      have hb_eq_false : ¬ 2 * b = 90 := by omega
      have h90b_lt : 2 * (90 - b) < 90 := by omega
      simp [hb_ne0, h90b_ne0, hb_lt_false, hb_eq_false, h90b_lt]

theorem appellMFE_shift_a (a z : ℤ) :
    appellMFE (a + 90) z = 1 - Qpow a * appellMFE a z := by
  by_cases ha : 0 ≤ a
  · have ha90 : 0 ≤ a + 90 := by omega
    have hnat : (a + 90).toNat = a.toNat + 90 := by omega
    have hcast : ((a.toNat : ℕ) : ℤ) = a := by omega
    simp [appellMFE, ha, ha90, hnat, appellMFENonneg_shift, hcast]
  · have hapos : 0 < -a := by omega
    by_cases ha90 : 0 ≤ a + 90
    · have hle90 : (-a).toNat ≤ 90 := by omega
      by_cases heq90 : (-a).toNat = 90
      · have haeq : a = -90 := by omega
        subst haeq
        rw [appellMFE]
        simp only [Int.reduceNeg, Int.reduceAdd, Int.reduceLE, dite_true]
        rw [appellMFE]
        simp only [Int.reduceNeg, Int.reduceLE, dite_false]
        norm_num
        change appellMFENonneg 0 =
          1 - Qpow (-90) * (Qpow 90 * appellMFENonneg 90)
        rw [appellMFENonneg_shift 0]
        rw [appellMFENonneg]
        simp [appellMFEBase, Qpow_mul]
      · have hlt90 : (-a).toNat < 90 := by omega
        have hsmall : 0 < (-a).toNat := by omega
        have hto1 : (a + 90).toNat = 90 - (-a).toNat := by omega
        have hbase := appellMFEBase_symm_small (b := (-a).toNat) hsmall hlt90
        rw [appellMFE, appellMFE]
        simp only [ha90, ha, dite_true, dite_false]
        rw [hto1]
        rw [appellMFENonneg, dif_pos (by omega : 90 - (-a).toNat < 90)]
        rw [appellMFENonneg, dif_pos hlt90]
        rw [hbase]
        rw [← mul_assoc, Qpow_mul]
        have hzero : a + -a = 0 := by omega
        simp [hzero]
    · have hneg90 : ¬ 0 ≤ a + 90 := ha90
      have hto_next : (-(a + 90)).toNat + 90 = (-a).toNat := by omega
      have hcast_next : (((-(a + 90)).toNat : ℕ) : ℤ) = -(a + 90) := by omega
      have hcast_a : (((-a).toNat : ℕ) : ℤ) = -a := by omega
      rw [appellMFE, appellMFE]
      simp only [hneg90, ha, dite_false]
      have hshift := appellMFENonneg_shift (-(a + 90)).toNat
      rw [hto_next] at hshift
      rw [hshift]
      rw [hcast_next]
      rw [← mul_assoc, Qpow_mul]
      have hzero : a + -a = 0 := by omega
      rw [hzero]
      simp

theorem appellMFE_inversion (a z : ℤ) :
    appellMFE a z = Qpow (-a) * appellMFE (-a) (-z) := by
  by_cases ha : 0 ≤ a
  · by_cases haz : a = 0
    · subst haz
      simp [appellMFE]
    · have hpos : 0 < a := by omega
      have hneg : ¬ 0 ≤ -a := by omega
      have htoa : ((a.toNat : ℕ) : ℤ) = a := by omega
      have htoneg : ((-(-a)).toNat : ℕ) = a.toNat := by omega
      rw [appellMFE, appellMFE]
      simp only [ha, hneg, dite_true, dite_false]
      rw [htoneg]
      rw [← mul_assoc, Qpow_mul]
      have hzero : -a + a = 0 := by omega
      simp [hzero]
  · have hnegpos : 0 ≤ -a := by omega
    have hto : (((-a).toNat : ℕ) : ℤ) = -a := by omega
    rw [appellMFE, appellMFE]
    simp only [ha, hnegpos, dite_false, dite_true]

/-! ## HM Def. 0.1 Appell-Lerch quotient -/

/-- Coefficient of the Laurent expansion of `(1 - Q^d)⁻¹` used in the
Appell-Lerch summand.  Positive `d` uses `∑_{k≥0} Q^{kd}`; negative `d`
uses `-∑_{k≥1} Q^{k(-d)}`.  The singular `d = 0` case is assigned zero in
this coefficient-level object; the HM table avoids those products by the
explicit `ell` choices recorded below. -/
def geomInvCoeff (d e : ℤ) : ℚ :=
  if d = 0 then 0
  else if 0 < d then
    if 0 ≤ e ∧ d ∣ e then 1 else 0
  else
    if 0 < e ∧ (-d) ∣ e then -1 else 0

/--
The one-variable geometric branch used by `geomInvCoeff` is the specialization
of the PF branch coefficient after substituting `u = Q^d`.
-/
theorem geomInvCoeff_mul_eq_branchInvCoeffAtPF
    (d m : ℤ) (hd : d ≠ 0) :
    geomInvCoeff d (d * m) =
      (Chapter10PF.branchInvCoeffAtPF d (d * m) m : ℚ) := by
  rcases lt_trichotomy d 0 with hdlt | hdz | hdgt
  · have hd_ne : ¬ d = 0 := by omega
    have hd_not_pos : ¬ 0 < d := by omega
    have hd_not_nonneg : ¬ 0 ≤ d := by omega
    by_cases hm : m < 0
    · have he_pos : 0 < d * m := by nlinarith
      have hdiv : -d ∣ d * m := ⟨-m, by ring⟩
      simp [geomInvCoeff, Chapter10PF.branchInvCoeffAtPF, hd_ne,
        hd_not_pos, hd_not_nonneg, hm, he_pos, hdiv]
    · have hm_nonneg : 0 ≤ m := by omega
      have he_not_pos : ¬ 0 < d * m := by nlinarith
      simp [geomInvCoeff, Chapter10PF.branchInvCoeffAtPF, hd_ne,
        hd_not_pos, hd_not_nonneg, hm, he_not_pos]
  · exact (hd hdz).elim
  · have hd_ne : ¬ d = 0 := by omega
    have hd_pos : 0 < d := hdgt
    have hd_nonneg : 0 ≤ d := by omega
    by_cases hm : 0 ≤ m
    · have he_nonneg : 0 ≤ d * m := mul_nonneg hd_nonneg hm
      have hdiv : d ∣ d * m := ⟨m, rfl⟩
      simp [geomInvCoeff, Chapter10PF.branchInvCoeffAtPF, hd_ne,
        hd_pos, hd_nonneg, hm, he_nonneg, hdiv]
    · have hm_not_nonneg : ¬ 0 ≤ m := hm
      have he_not_nonneg : ¬ 0 ≤ d * m := by
        have hm_neg : m < 0 := by omega
        nlinarith
      simp [geomInvCoeff, Chapter10PF.branchInvCoeffAtPF, hd_ne,
        hd_pos, hd_nonneg, hm_not_nonneg, he_not_nonneg]

/--
Same branch bridge, expressed through the PF file's raw branch coefficient.
-/
theorem geomInvCoeff_mul_eq_branchInvCoeffPF
    (d m : ℤ) (hd : d ≠ 0) :
    geomInvCoeff d (d * m) =
      (Chapter10PF.branchInvCoeffPF d m : ℚ) := by
  rw [geomInvCoeff_mul_eq_branchInvCoeffAtPF d m hd,
    Chapter10PF.branchInvCoeffPF_eq_branchInvCoeffAtPF d m]

/--
Pointwise branch bridge at an arbitrary exponent.  When the exponent is not a
multiple of `d`, both the one-variable geometric coefficient and the PF branch
coefficient vanish; otherwise this is `geomInvCoeff_mul_eq_branchInvCoeffAtPF`
at the quotient exponent.
-/
theorem geomInvCoeff_eq_branchInvCoeffAtPF_ediv
    (d e : ℤ) (hd : d ≠ 0) :
    geomInvCoeff d e =
      (Chapter10PF.branchInvCoeffAtPF d e (e / d) : ℚ) := by
  by_cases hdiv : d ∣ e
  · rcases hdiv with ⟨m, hm⟩
    subst e
    rw [Int.mul_ediv_cancel_left _ hd]
    exact geomInvCoeff_mul_eq_branchInvCoeffAtPF d m hd
  · have hne_mul : ¬ e = d * (e / d) := by
      intro h
      exact hdiv ⟨e / d, h⟩
    have hnegdiv : ¬ -d ∣ e := by
      rintro ⟨m, hm⟩
      apply hdiv
      refine ⟨-m, ?_⟩
      rw [hm]
      ring
    rcases lt_trichotomy d 0 with hdlt | hdz | hdgt
    · have hd_ne : ¬ d = 0 := by omega
      have hd_not_pos : ¬ 0 < d := by omega
      have hd_not_nonneg : ¬ 0 ≤ d := by omega
      simp [geomInvCoeff, Chapter10PF.branchInvCoeffAtPF, hd_ne,
        hd_not_pos, hd_not_nonneg, hnegdiv, hne_mul]
    · exact (hd hdz).elim
    · have hd_ne : ¬ d = 0 := by omega
      have hd_pos : 0 < d := hdgt
      have hd_nonneg : 0 ≤ d := by omega
      simp [geomInvCoeff, Chapter10PF.branchInvCoeffAtPF, hd_ne,
        hd_pos, hd_nonneg, hdiv, hne_mul]

/-- Coarse lower support guard for the HM Def. 0.1 numerator. -/
def appellNumeratorCoeffLower (a z : ℤ) : ℤ :=
  -((Int.natAbs a + Int.natAbs z + 92 : ℤ) ^ 2)

/-- Finite search window for a coefficient of the HM Def. 0.1 numerator. -/
def appellNumeratorCoeffWindow (a z e : ℤ) : ℤ :=
  4 * (Int.natAbs a + Int.natAbs z + Int.natAbs e + 92 : ℤ)

/-- Coefficient extractor for the numerator in
`m(Q^a,Q^90,Q^z) = j(Q^z;Q^90)⁻¹ * numerator`.

The finite window is the concrete coefficient-extraction layer used by this
pending formalization.  It mirrors `scripts/ch10_hm_verify.py` and keeps the
public object as an honest Laurent series rather than an uninterpreted symbol. -/
def appellNumeratorCoeff (a z e : ℤ) : ℚ :=
  if e < appellNumeratorCoeffLower a z then 0
  else
    ∑ r ∈ Finset.Icc (-(appellNumeratorCoeffWindow a z e))
        (appellNumeratorCoeffWindow a z e),
      negOnePowIntQ r *
        geomInvCoeff (appellDenomExp a z r) (e - appellNumeratorExp z r)

/-- PF-branch version of the finite HM Def. 0.1 numerator coefficient. -/
def appellNumeratorPFBranchCoeff (a z e : ℤ) : ℚ :=
  if e < appellNumeratorCoeffLower a z then 0
  else
    ∑ r ∈ Finset.Icc (-(appellNumeratorCoeffWindow a z e))
        (appellNumeratorCoeffWindow a z e),
      negOnePowIntQ r *
        (Chapter10PF.branchInvCoeffAtPF (appellDenomExp a z r)
          (e - appellNumeratorExp z r)
          ((e - appellNumeratorExp z r) / appellDenomExp a z r) : ℚ)

theorem appellNumeratorCoeff_eq_PFBranchCoeff
    (a z e : ℤ) (hden : ∀ r : ℤ, appellDenomExp a z r ≠ 0) :
    appellNumeratorCoeff a z e = appellNumeratorPFBranchCoeff a z e := by
  by_cases hlt : e < appellNumeratorCoeffLower a z
  · simp [appellNumeratorCoeff, appellNumeratorPFBranchCoeff, hlt]
  · simp only [appellNumeratorCoeff, appellNumeratorPFBranchCoeff, hlt, if_false]
    refine Finset.sum_congr rfl ?_
    intro r _hr
    rw [geomInvCoeff_eq_branchInvCoeffAtPF_ediv
      (appellDenomExp a z r) (e - appellNumeratorExp z r) (hden r)]

/-- Laurent-series numerator in HM Def. 0.1:
`∑_r (-1)^r Q^(90 r(r-1)/2 + z r) / (1 - Q^(90(r-1)+a+z))`. -/
def appellNumeratorLaurent (a z : ℤ) : QLaurent :=
  HahnSeries.ofSuppBddBelow (fun e : ℤ => appellNumeratorCoeff a z e) <| by
    refine ⟨appellNumeratorCoeffLower a z, ?_⟩
    intro e he
    by_contra hle
    have hlt : e < appellNumeratorCoeffLower a z := by omega
    have hz : appellNumeratorCoeff a z e = 0 := by
      simp [appellNumeratorCoeff, hlt]
    exact he hz

@[simp] theorem coeff_appellNumeratorLaurent (a z e : ℤ) :
    lcoeff (appellNumeratorLaurent a z) e = appellNumeratorCoeff a z e := by
  simp [lcoeff, appellNumeratorLaurent]

/-- HM Def. 0.1 quotient
`m(Q^a,Q^90,Q^z) = j(Q^z;Q^90)⁻¹ *
∑_r (-1)^r Q^(90r(r-1)/2+zr)/(1-Q^(90(r-1)+a+z))`. -/
def appellMDef01 (a z : ℤ) : QLaurent :=
  (jLaurent z 90)⁻¹ * appellNumeratorLaurent a z

/-- The Appell-Lerch object used in the HM table is now the genuine
Hickerson-Mortenson Def. 0.1 quotient, with explicit coefficient extraction
for the numerator. -/
def appellM (a z : ℤ) : QLaurent :=
  appellMDef01 a z

def appellMCoeff (a z e : ℤ) : ℚ :=
  lcoeff (appellM a z) e

/-- DEF-0.1 bridge: the public `appellM` is the HM quotient definition. -/
theorem appellM_eq_hmDef01 (a z : ℤ) :
    appellM a z = (jLaurent z 90)⁻¹ * appellNumeratorLaurent a z := by
  rfl

@[simp] theorem coeff_appellM (a z e : ℤ) :
    lcoeff (appellM a z) e = appellMCoeff a z e := rfl

/-- `J_1=(q;q)_∞` in HM notation, specialized to `q=Q^90`, represented as
`j(Q^90;Q^270)`. -/
def JOneLaurent : QLaurent :=
  jLaurent 90 270

/-- HM Theorem 2.3 theta quotient RHS for
`x=Q^a`, `q=Q^90`, `z_i=Q^z_i`. -/
def hm23ThetaQuotient (a z0 z1 : ℤ) : QLaurent :=
  Qpow z0 * JOneLaurent ^ 3 * jLaurent (z1 - z0) 90 *
    jLaurent (a + z0 + z1) 90 *
      (jLaurent z0 90 * jLaurent z1 90 *
        jLaurent (a + z0) 90 * jLaurent (a + z1) 90)⁻¹

/-- Nonzero-denominator condition for the specialized HM Theorem 2.3
theta quotient. -/
def hm23Nonsingular (a z0 z1 : ℤ) : Prop :=
  jLaurent z0 90 ≠ 0 ∧
    jLaurent z1 90 ≠ 0 ∧
      jLaurent (a + z0) 90 ≠ 0 ∧
        jLaurent (a + z1) 90 ≠ 0

theorem appellDenomExp_ne_zero_of_jLaurent_ne_zero
    (a z r : ℤ) (h : jLaurent (a + z) 90 ≠ 0) :
    appellDenomExp a z r ≠ 0 := by
  intro hzero
  have harg : a + z = 90 * (1 - r) := by
    unfold appellDenomExp at hzero
    omega
  have hj : jLaurent (a + z) 90 = 0 := by
    rw [harg]
    exact jLaurent_period_zero 90 (1 - r) (by norm_num)
  exact h hj

theorem hm23Nonsingular_appellDenomExp_z0_ne_zero
    {a z0 z1 r : ℤ} (hreg : hm23Nonsingular a z0 z1) :
    appellDenomExp a z0 r ≠ 0 :=
  appellDenomExp_ne_zero_of_jLaurent_ne_zero a z0 r hreg.2.2.1

theorem hm23Nonsingular_appellDenomExp_z1_ne_zero
    {a z0 z1 r : ℤ} (hreg : hm23Nonsingular a z0 z1) :
    appellDenomExp a z1 r ≠ 0 :=
  appellDenomExp_ne_zero_of_jLaurent_ne_zero a z1 r hreg.2.2.2

/-- Left side of HM Theorem 2.3 after clearing the four theta denominators.
This is the Appell-numerator side of the theta-addition identity. -/
def hm23ClearedThetaLHS (a z0 z1 : ℤ) : QLaurent :=
  appellNumeratorLaurent a z1 * jLaurent z0 90 *
        jLaurent (a + z0) 90 * jLaurent (a + z1) 90 -
    appellNumeratorLaurent a z0 * jLaurent z1 90 *
      jLaurent (a + z0) 90 * jLaurent (a + z1) 90

/-- Right side of HM Theorem 2.3 after clearing the four theta denominators. -/
def hm23ClearedThetaRHS (a z0 z1 : ℤ) : QLaurent :=
  Qpow z0 * JOneLaurent ^ 3 * jLaurent (z1 - z0) 90 *
    jLaurent (a + z0 + z1) 90


/-! ## HM f_{2,3,2} specialization data -/

/-- One Appell-Lerch summand in the HM `f_{2,3,2}` expansion:
`Q^lead * j(Q^jArg;Q^18) * M(mArg,mZ)`. -/
structure HMTerm where
  lead : ℤ
  jArg : ℤ
  mArg : ℤ
  mZ : ℤ
deriving DecidableEq, Repr

/-- HM Corollary 8.2 / Eq. (8.7), specialized to
`f_{2,3,2}(Q^X,Q^Y,Q^9)` with integer `ell`.

The four terms correspond to `r = 0,0,1,1` in the paper's two Appell sums.
-/
def hmF232Terms (ell X Y : ℤ) : List HMTerm :=
  [ { lead := 0, jArg := Y,
      mArg := 54 + 2 * X - 3 * Y, mZ := 18 * ell + 2 * Y - 2 * X },
    { lead := 0, jArg := X,
      mArg := 54 + 2 * Y - 3 * X, mZ := 2 * X - 2 * Y - 18 * ell },
    { lead := X - Y - 9, jArg := Y + 9,
      mArg := 9 + 2 * X - 3 * Y, mZ := 18 * ell + 2 * Y - 2 * X },
    { lead := Y - X - 9, jArg := X + 9,
      mArg := 9 + 2 * Y - 3 * X, mZ := 2 * X - 2 * Y - 18 * ell } ]

/-- Laurent interpretation of one HM Appell-Lerch summand
`Q^lead * j(Q^jArg;Q^18) * m(Q^mArg,Q^90,Q^mZ)`. -/
def hmTermLaurent (t : HMTerm) : QLaurent :=
  Qpow t.lead * jLaurent t.jArg 18 * appellM t.mArg t.mZ

/-- Sum a finite HM term list as a Laurent series. -/
def hmTermsLaurent : List HMTerm → QLaurent
  | [] => 0
  | t :: ts => hmTermLaurent t + hmTermsLaurent ts

@[simp] theorem hmTermsLaurent_nil : hmTermsLaurent [] = 0 := rfl

@[simp] theorem hmTermsLaurent_cons (t : HMTerm) (ts : List HMTerm) :
    hmTermsLaurent (t :: ts) = hmTermLaurent t + hmTermsLaurent ts := rfl

/-- HM Corollary 8.2 specialized right side for
`f_{2,3,2}(Q^X,Q^Y,Q^9)`, after choosing `ell`. -/
def hmF232Laurent (ell X Y : ℤ) : QLaurent :=
  hmTermsLaurent (hmF232Terms ell X Y)

/-- Constant shift in the residue split `r=3a+i`, `s=3b+j`. -/
def Cij (i j : Fin 3) : ℤ :=
  (i.val : ℤ) ^ 2 + 3 * (i.val : ℤ) * (j.val : ℤ) + (j.val : ℤ) ^ 2 +
    3 * (i.val : ℤ) + 3 * (j.val : ℤ) + 1

/-- `X` exponent in `f_{2,3,2}(Q^X,Q^Y,Q^9)` for `T_ij`. -/
def Xij (i j : Fin 3) : ℤ :=
  6 * (i.val : ℤ) + 9 * (j.val : ℤ) + 18

/-- `Y` exponent in `f_{2,3,2}(Q^X,Q^Y,Q^9)` for `T_ij`. -/
def Yij (i j : Fin 3) : ℤ :=
  9 * (i.val : ℤ) + 6 * (j.val : ℤ) + 18

/-- The sign `(-1)^(i+j)` in the residue split. -/
def TijSign (i j : Fin 3) : ℤ :=
  if (i.val + j.val) % 2 = 0 then 1 else -1

/-- HM `ell` choice used by the numeric verifier.  It keeps the requested
`ell = 1` table except for the two singular products `T02` and `T10`, where
`ell = 2` avoids a `J_{18k} * M(...,...)` zero-pole specialization. -/
def hmEll (i j : Fin 3) : ℤ :=
  if (i.val = 0 ∧ j.val = 2) ∨ (i.val = 1 ∧ j.val = 0) then 2 else 1

/-- Full parameter package for a shifted `T_ij`. -/
structure TijData where
  sign : ℤ
  shift : ℤ
  X : ℤ
  Y : ℤ
  ell : ℤ
deriving DecidableEq, Repr

def tijData (i j : Fin 3) : TijData where
  sign := TijSign i j
  shift := Cij i j
  X := Xij i j
  Y := Yij i j
  ell := hmEll i j

theorem tijData_00 :
    tijData 0 0 = { sign := 1, shift := 1, X := 18, Y := 18, ell := 1 } := by
  rfl

theorem tijData_01 :
    tijData 0 1 = { sign := -1, shift := 5, X := 27, Y := 24, ell := 1 } := by
  rfl

theorem tijData_02 :
    tijData 0 2 = { sign := 1, shift := 11, X := 36, Y := 30, ell := 2 } := by
  rfl

theorem tijData_10 :
    tijData 1 0 = { sign := -1, shift := 5, X := 24, Y := 27, ell := 2 } := by
  rfl

theorem tijData_11 :
    tijData 1 1 = { sign := 1, shift := 12, X := 33, Y := 33, ell := 1 } := by
  rfl

theorem tijData_12 :
    tijData 1 2 = { sign := -1, shift := 21, X := 42, Y := 39, ell := 1 } := by
  rfl

theorem tijData_20 :
    tijData 2 0 = { sign := 1, shift := 11, X := 30, Y := 36, ell := 1 } := by
  rfl

theorem tijData_21 :
    tijData 2 1 = { sign := -1, shift := 21, X := 39, Y := 42, ell := 1 } := by
  rfl

theorem tijData_22 :
    tijData 2 2 = { sign := 1, shift := 33, X := 48, Y := 48, ell := 1 } := by
  rfl

theorem hmF232Terms_T00 :
    hmF232Terms (tijData 0 0).ell (tijData 0 0).X (tijData 0 0).Y =
      [ { lead := 0, jArg := 18, mArg := 36, mZ := 18 },
        { lead := 0, jArg := 18, mArg := 36, mZ := -18 },
        { lead := -9, jArg := 27, mArg := -9, mZ := 18 },
        { lead := -9, jArg := 27, mArg := -9, mZ := -18 } ] := by
  rfl

theorem hmF232Terms_T01 :
    hmF232Terms (tijData 0 1).ell (tijData 0 1).X (tijData 0 1).Y =
      [ { lead := 0, jArg := 24, mArg := 36, mZ := 12 },
        { lead := 0, jArg := 27, mArg := 21, mZ := -12 },
        { lead := -6, jArg := 33, mArg := -9, mZ := 12 },
        { lead := -12, jArg := 36, mArg := -24, mZ := -12 } ] := by
  rfl

theorem hmF232Terms_T02 :
    hmF232Terms (tijData 0 2).ell (tijData 0 2).X (tijData 0 2).Y =
      [ { lead := 0, jArg := 30, mArg := 36, mZ := 24 },
        { lead := 0, jArg := 36, mArg := 6, mZ := -24 },
        { lead := -3, jArg := 39, mArg := -9, mZ := 24 },
        { lead := -15, jArg := 45, mArg := -39, mZ := -24 } ] := by
  rfl

theorem hmF232Terms_T10 :
    hmF232Terms (tijData 1 0).ell (tijData 1 0).X (tijData 1 0).Y =
      [ { lead := 0, jArg := 27, mArg := 21, mZ := 42 },
        { lead := 0, jArg := 24, mArg := 36, mZ := -42 },
        { lead := -12, jArg := 36, mArg := -24, mZ := 42 },
        { lead := -6, jArg := 33, mArg := -9, mZ := -42 } ] := by
  norm_num [hmF232Terms, tijData, hmEll, Xij, Yij, Cij, TijSign]

theorem hmF232Terms_T11 :
    hmF232Terms (tijData 1 1).ell (tijData 1 1).X (tijData 1 1).Y =
      [ { lead := 0, jArg := 33, mArg := 21, mZ := 18 },
        { lead := 0, jArg := 33, mArg := 21, mZ := -18 },
        { lead := -9, jArg := 42, mArg := -24, mZ := 18 },
        { lead := -9, jArg := 42, mArg := -24, mZ := -18 } ] := by
  rfl

theorem hmF232Terms_T12 :
    hmF232Terms (tijData 1 2).ell (tijData 1 2).X (tijData 1 2).Y =
      [ { lead := 0, jArg := 39, mArg := 21, mZ := 12 },
        { lead := 0, jArg := 42, mArg := 6, mZ := -12 },
        { lead := -6, jArg := 48, mArg := -24, mZ := 12 },
        { lead := -12, jArg := 51, mArg := -39, mZ := -12 } ] := by
  rfl

theorem hmF232Terms_T20 :
    hmF232Terms (tijData 2 0).ell (tijData 2 0).X (tijData 2 0).Y =
      [ { lead := 0, jArg := 36, mArg := 6, mZ := 30 },
        { lead := 0, jArg := 30, mArg := 36, mZ := -30 },
        { lead := -15, jArg := 45, mArg := -39, mZ := 30 },
        { lead := -3, jArg := 39, mArg := -9, mZ := -30 } ] := by
  rfl

theorem hmF232Terms_T21 :
    hmF232Terms (tijData 2 1).ell (tijData 2 1).X (tijData 2 1).Y =
      [ { lead := 0, jArg := 42, mArg := 6, mZ := 24 },
        { lead := 0, jArg := 39, mArg := 21, mZ := -24 },
        { lead := -12, jArg := 51, mArg := -39, mZ := 24 },
        { lead := -6, jArg := 48, mArg := -24, mZ := -24 } ] := by
  rfl

theorem hmF232Terms_T22 :
    hmF232Terms (tijData 2 2).ell (tijData 2 2).X (tijData 2 2).Y =
      [ { lead := 0, jArg := 48, mArg := 6, mZ := 18 },
        { lead := 0, jArg := 48, mArg := 6, mZ := -18 },
        { lead := -9, jArg := 57, mArg := -39, mZ := 18 },
        { lead := -9, jArg := 57, mArg := -39, mZ := -18 } ] := by
  rfl

theorem hmF232Laurent_T00 :
    hmF232Laurent (tijData 0 0).ell (tijData 0 0).X (tijData 0 0).Y =
      hmTermsLaurent
        [ { lead := 0, jArg := 18, mArg := 36, mZ := 18 },
          { lead := 0, jArg := 18, mArg := 36, mZ := -18 },
          { lead := -9, jArg := 27, mArg := -9, mZ := 18 },
          { lead := -9, jArg := 27, mArg := -9, mZ := -18 } ] := by
  rw [hmF232Laurent, hmF232Terms_T00]

theorem hmF232Laurent_T01 :
    hmF232Laurent (tijData 0 1).ell (tijData 0 1).X (tijData 0 1).Y =
      hmTermsLaurent
        [ { lead := 0, jArg := 24, mArg := 36, mZ := 12 },
          { lead := 0, jArg := 27, mArg := 21, mZ := -12 },
          { lead := -6, jArg := 33, mArg := -9, mZ := 12 },
          { lead := -12, jArg := 36, mArg := -24, mZ := -12 } ] := by
  rw [hmF232Laurent, hmF232Terms_T01]

theorem hmF232Laurent_T02 :
    hmF232Laurent (tijData 0 2).ell (tijData 0 2).X (tijData 0 2).Y =
      hmTermsLaurent
        [ { lead := 0, jArg := 30, mArg := 36, mZ := 24 },
          { lead := 0, jArg := 36, mArg := 6, mZ := -24 },
          { lead := -3, jArg := 39, mArg := -9, mZ := 24 },
          { lead := -15, jArg := 45, mArg := -39, mZ := -24 } ] := by
  rw [hmF232Laurent, hmF232Terms_T02]

theorem hmF232Laurent_T10 :
    hmF232Laurent (tijData 1 0).ell (tijData 1 0).X (tijData 1 0).Y =
      hmTermsLaurent
        [ { lead := 0, jArg := 27, mArg := 21, mZ := 42 },
          { lead := 0, jArg := 24, mArg := 36, mZ := -42 },
          { lead := -12, jArg := 36, mArg := -24, mZ := 42 },
          { lead := -6, jArg := 33, mArg := -9, mZ := -42 } ] := by
  rw [hmF232Laurent, hmF232Terms_T10]

theorem hmF232Laurent_T11 :
    hmF232Laurent (tijData 1 1).ell (tijData 1 1).X (tijData 1 1).Y =
      hmTermsLaurent
        [ { lead := 0, jArg := 33, mArg := 21, mZ := 18 },
          { lead := 0, jArg := 33, mArg := 21, mZ := -18 },
          { lead := -9, jArg := 42, mArg := -24, mZ := 18 },
          { lead := -9, jArg := 42, mArg := -24, mZ := -18 } ] := by
  rw [hmF232Laurent, hmF232Terms_T11]

theorem hmF232Laurent_T12 :
    hmF232Laurent (tijData 1 2).ell (tijData 1 2).X (tijData 1 2).Y =
      hmTermsLaurent
        [ { lead := 0, jArg := 39, mArg := 21, mZ := 12 },
          { lead := 0, jArg := 42, mArg := 6, mZ := -12 },
          { lead := -6, jArg := 48, mArg := -24, mZ := 12 },
          { lead := -12, jArg := 51, mArg := -39, mZ := -12 } ] := by
  rw [hmF232Laurent, hmF232Terms_T12]

theorem hmF232Laurent_T20 :
    hmF232Laurent (tijData 2 0).ell (tijData 2 0).X (tijData 2 0).Y =
      hmTermsLaurent
        [ { lead := 0, jArg := 36, mArg := 6, mZ := 30 },
          { lead := 0, jArg := 30, mArg := 36, mZ := -30 },
          { lead := -15, jArg := 45, mArg := -39, mZ := 30 },
          { lead := -3, jArg := 39, mArg := -9, mZ := -30 } ] := by
  rw [hmF232Laurent, hmF232Terms_T20]

theorem hmF232Laurent_T21 :
    hmF232Laurent (tijData 2 1).ell (tijData 2 1).X (tijData 2 1).Y =
      hmTermsLaurent
        [ { lead := 0, jArg := 42, mArg := 6, mZ := 24 },
          { lead := 0, jArg := 39, mArg := 21, mZ := -24 },
          { lead := -12, jArg := 51, mArg := -39, mZ := 24 },
          { lead := -6, jArg := 48, mArg := -24, mZ := -24 } ] := by
  rw [hmF232Laurent, hmF232Terms_T21]

theorem hmF232Laurent_T22 :
    hmF232Laurent (tijData 2 2).ell (tijData 2 2).X (tijData 2 2).Y =
      hmTermsLaurent
        [ { lead := 0, jArg := 48, mArg := 6, mZ := 18 },
          { lead := 0, jArg := 48, mArg := 6, mZ := -18 },
          { lead := -9, jArg := 57, mArg := -39, mZ := 18 },
          { lead := -9, jArg := 57, mArg := -39, mZ := -18 } ] := by
  rw [hmF232Laurent, hmF232Terms_T22]

/-! ## Chan combination Laurent layer -/

/-- `Θ₁=j(Q;Q²)` in the final Chan combination. -/
def thetaOneLaurent : QLaurent :=
  jLaurent 1 2

/-- `Θ₉=j(Q⁹;Q¹⁸)` in the final Chan combination. -/
def thetaNineLaurent : QLaurent :=
  jLaurent 9 18

/-- The shifted signed `T_ij` term after applying the residue split. -/
def TijLaurent (i j : Fin 3) : QLaurent :=
  ((tijData i j).sign : ℚ) •
    (Qpow (tijData i j).shift *
      hmF232Laurent (tijData i j).ell (tijData i j).X (tijData i j).Y)

/-- `H₀₀ = ∑_{i,j=0}^2 T_ij`. -/
def H00Laurent : QLaurent :=
  ∑ i : Fin 3, ∑ j : Fin 3, TijLaurent i j

/-- `H₁₀ = ∑_{j=0}^2 T_0j`. -/
def H10Laurent : QLaurent :=
  ∑ j : Fin 3, TijLaurent 0 j

/-- `H₀₁ = ∑_{i=0}^2 T_i0`. -/
def H01Laurent : QLaurent :=
  ∑ i : Fin 3, TijLaurent i 0

/-- `H₁₁ = T_00`. -/
def H11Laurent : QLaurent :=
  TijLaurent 0 0

/-- The exact Laurent-series form of the finite Chan combination before the
Appell-Lerch cancellation and theta-product evaluation. -/
def chan1015HCombinationLaurent : QLaurent :=
  thetaNineLaurent ^ 2 * H00Laurent -
    thetaNineLaurent * thetaOneLaurent * (H10Laurent + H01Laurent) +
      thetaOneLaurent ^ 2 * H11Laurent

theorem H00Laurent_unfold :
    H00Laurent =
      TijLaurent 0 0 + TijLaurent 0 1 + TijLaurent 0 2 +
        (TijLaurent 1 0 + TijLaurent 1 1 + TijLaurent 1 2) +
          (TijLaurent 2 0 + TijLaurent 2 1 + TijLaurent 2 2) := by
  rw [H00Laurent]
  simp [Fin.sum_univ_three]

theorem H10Laurent_unfold :
    H10Laurent = TijLaurent 0 0 + TijLaurent 0 1 + TijLaurent 0 2 := by
  rw [H10Laurent]
  simp [Fin.sum_univ_three]

theorem H01Laurent_unfold :
    H01Laurent = TijLaurent 0 0 + TijLaurent 1 0 + TijLaurent 2 0 := by
  rw [H01Laurent]
  simp [Fin.sum_univ_three]

theorem H11Laurent_unfold :
    H11Laurent = TijLaurent 0 0 := rfl

theorem chan1015HCombinationLaurent_unfold :
    chan1015HCombinationLaurent =
      thetaNineLaurent ^ 2 * H00Laurent -
        thetaNineLaurent * thetaOneLaurent * (H10Laurent + H01Laurent) +
          thetaOneLaurent ^ 2 * H11Laurent := rfl

theorem chan1015HCombinationLaurent_symmetric :
    H10Laurent = H01Laurent →
      chan1015HCombinationLaurent =
        thetaNineLaurent ^ 2 * H00Laurent -
          2 * thetaNineLaurent * thetaOneLaurent * H10Laurent +
            thetaOneLaurent ^ 2 * H11Laurent := by
  intro hsym
  rw [chan1015HCombinationLaurent_unfold, hsym]
  ring

/-! ## Theta-correction target -/

/-- Common `z₀` for the current HM table.  The verifier confirms that the
Appell base contribution cancels for this base with the `ell` choices recorded
in `hmEll`. -/
def hm23DeltaBase : ℤ :=
  18

/-- HM 2.3 correction moving `M(a,z)` to the common `hm23DeltaBase`. -/
def hm23DeltaToBase (a z : ℤ) : QLaurent :=
  if z = hm23DeltaBase then 0 else hm23ThetaQuotient a hm23DeltaBase z

@[simp] theorem hm23DeltaToBase_self (a : ℤ) :
    hm23DeltaToBase a hm23DeltaBase = 0 := by
  simp [hm23DeltaToBase]

theorem hm23DeltaToBase_of_ne {a z : ℤ} (hz : z ≠ hm23DeltaBase) :
    hm23DeltaToBase a z = hm23ThetaQuotient a hm23DeltaBase z := by
  simp [hm23DeltaToBase, hz]

/-- Theta-correction contribution of one HM summand after replacing
`M(a,z)` by `M(a,18)+Δ(a,z)` and keeping only the `Δ` part. -/
def hmTermThetaCorrection (t : HMTerm) : QLaurent :=
  Qpow t.lead * jLaurent t.jArg 18 * hm23DeltaToBase t.mArg t.mZ

/-- Sum of the theta-correction parts of a finite HM term list. -/
def hmTermsThetaCorrection : List HMTerm → QLaurent
  | [] => 0
  | t :: ts => hmTermThetaCorrection t + hmTermsThetaCorrection ts

@[simp] theorem hmTermsThetaCorrection_nil :
    hmTermsThetaCorrection [] = 0 := rfl

@[simp] theorem hmTermsThetaCorrection_cons (t : HMTerm) (ts : List HMTerm) :
    hmTermsThetaCorrection (t :: ts) =
      hmTermThetaCorrection t + hmTermsThetaCorrection ts := rfl

/-- HM `f_{2,3,2}` theta-correction part for one specialized row. -/
def hmF232ThetaCorrection (ell X Y : ℤ) : QLaurent :=
  hmTermsThetaCorrection (hmF232Terms ell X Y)

/-- Shifted signed `T_ij` theta-correction contribution. -/
def TijThetaCorrection (i j : Fin 3) : QLaurent :=
  ((tijData i j).sign : ℚ) •
    (Qpow (tijData i j).shift *
      hmF232ThetaCorrection (tijData i j).ell (tijData i j).X (tijData i j).Y)

/-- `H₀₀` theta-correction part. -/
def H00ThetaCorrection : QLaurent :=
  ∑ i : Fin 3, ∑ j : Fin 3, TijThetaCorrection i j

/-- `H₁₀` theta-correction part. -/
def H10ThetaCorrection : QLaurent :=
  ∑ j : Fin 3, TijThetaCorrection 0 j

/-- `H₀₁` theta-correction part. -/
def H01ThetaCorrection : QLaurent :=
  ∑ i : Fin 3, TijThetaCorrection i 0

/-- `H₁₁` theta-correction part. -/
def H11ThetaCorrection : QLaurent :=
  TijThetaCorrection 0 0

/-- Chan's theta correction after the Appell parts have cancelled. -/
def thetaCorrectionLaurent : QLaurent :=
  thetaNineLaurent ^ 2 * H00ThetaCorrection -
    2 * thetaNineLaurent * thetaOneLaurent * H10ThetaCorrection +
      thetaOneLaurent ^ 2 * H11ThetaCorrection

theorem thetaCorrectionLaurent_unfold :
    thetaCorrectionLaurent =
      thetaNineLaurent ^ 2 * H00ThetaCorrection -
        2 * thetaNineLaurent * thetaOneLaurent * H10ThetaCorrection +
          thetaOneLaurent ^ 2 * H11ThetaCorrection := rfl

/-- `(Q^m;Q^m)_∞`, represented by Euler's pentagonal specialization
`j(Q^m;Q^{3m})`. -/
def etaLaurent (m : ℤ) : QLaurent :=
  jLaurent m (3 * m)

/-- `E₃=(Q³;Q³)_∞`. -/
def E3Laurent : QLaurent :=
  etaLaurent 3

/-- `E₆=(Q⁶;Q⁶)_∞`. -/
def E6Laurent : QLaurent :=
  etaLaurent 6

/-! ## Split classical theta bridges -/

private def thetaOneCoeffTerm (e n : ℤ) : ℚ :=
  if n * n = e then negOnePowIntQ n else 0

private def thetaNineCoeffTerm (e n : ℤ) : ℚ :=
  if (3 * n) * (3 * n) = e then negOnePowIntQ n else 0

private def thetaThreeCoeffTerm (e n : ℤ) : ℚ :=
  if (3 * n - 1) * (3 * n - 1) = e then negOnePowIntQ n else 0

private theorem jExp_one_two (n : ℤ) :
    jExp 1 2 n = n * n := by
  have h := two_mul_jExp 1 2 n
  unfold jExpTwice at h
  nlinarith

private theorem jExp_nine_eighteen (n : ℤ) :
    jExp 9 18 n = (3 * n) * (3 * n) := by
  have h := two_mul_jExp 9 18 n
  unfold jExpTwice at h
  nlinarith

private theorem jExp_three_eighteen_add_one (n : ℤ) :
    jExp 3 18 n + 1 = (3 * n - 1) * (3 * n - 1) := by
  have h := two_mul_jExp 3 18 n
  unfold jExpTwice at h
  nlinarith

private theorem negOnePowIntQ_two_mul (n : ℤ) :
    negOnePowIntQ (2 * n) = 1 := by
  rw [negOnePowIntQ_eq_negOnePow]
  rw [Int.negOnePow_even]
  · norm_num
  · exact ⟨n, by ring⟩

private theorem negOnePowIntQ_three_mul (n : ℤ) :
    negOnePowIntQ (3 * n) = negOnePowIntQ n := by
  have h := negOnePowIntQ_add (2 * n) n
  rw [show 2 * n + n = 3 * n by ring, negOnePowIntQ_two_mul] at h
  simpa using h

private theorem negOnePowIntQ_three_mul_sub_one (n : ℤ) :
    negOnePowIntQ (3 * n - 1) = -negOnePowIntQ n := by
  calc
    negOnePowIntQ (3 * n - 1)
        = negOnePowIntQ (3 * n) * negOnePowIntQ 1 := negOnePowIntQ_sub (3 * n) 1
    _ = negOnePowIntQ n * (-1) := by
          rw [negOnePowIntQ_three_mul]
          norm_num [negOnePowIntQ]
    _ = -negOnePowIntQ n := by ring

private theorem thetaOneCoeffTerm_split (e n : ℤ) :
    thetaOneCoeffTerm e n =
      (if 3 ∣ n then thetaOneCoeffTerm e n else 0) +
        (if 3 ∣ n + 1 then thetaOneCoeffTerm e n else 0) +
          (if 3 ∣ n - 1 then thetaOneCoeffTerm e n else 0) := by
  by_cases h0 : 3 ∣ n
  · have hp : ¬ 3 ∣ n + 1 := by
      rintro ⟨k, hk⟩
      rcases h0 with ⟨m, hm⟩
      omega
    have hm : ¬ 3 ∣ n - 1 := by
      rintro ⟨k, hk⟩
      rcases h0 with ⟨m, hm⟩
      omega
    simp [h0, hp, hm]
  · by_cases hp : 3 ∣ n + 1
    · have hm : ¬ 3 ∣ n - 1 := by
        rintro ⟨k, hk⟩
        rcases hp with ⟨m, hm⟩
        omega
      simp [h0, hp, hm]
    · have hm : 3 ∣ n - 1 := by
        have hdecomp := Int.emod_add_mul_ediv n 3
        have hnonneg : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
        have hlt : n % 3 < 3 := Int.emod_lt_of_pos n (by norm_num)
        have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
        rcases hcases with hmod | hmod | hmod
        · exfalso
          apply h0
          exact ⟨n / 3, by omega⟩
        · exact ⟨n / 3, by omega⟩
        · exfalso
          apply hp
          exact ⟨n / 3 + 1, by omega⟩
      simp [h0, hp, hm]

private theorem thetaOneCoeffTerm_three_mul (e n : ℤ) :
    thetaOneCoeffTerm e (3 * n) = thetaNineCoeffTerm e n := by
  unfold thetaOneCoeffTerm thetaNineCoeffTerm
  by_cases hroot : (3 * n) * (3 * n) = e
  · simp [hroot, negOnePowIntQ_three_mul]
  · simp [hroot]

private theorem thetaOneCoeffTerm_three_mul_sub_one (e n : ℤ) :
    thetaOneCoeffTerm e (3 * n - 1) = -thetaThreeCoeffTerm e n := by
  unfold thetaOneCoeffTerm thetaThreeCoeffTerm
  by_cases hroot : (3 * n - 1) * (3 * n - 1) = e
  · simp [hroot, negOnePowIntQ_three_mul_sub_one]
  · simp [hroot]

private theorem thetaOneCoeffTerm_one_sub_three_mul (e n : ℤ) :
    thetaOneCoeffTerm e (1 - 3 * n) = -thetaThreeCoeffTerm e n := by
  have hterm : thetaOneCoeffTerm e (1 - 3 * n) =
      thetaOneCoeffTerm e (3 * n - 1) := by
    unfold thetaOneCoeffTerm
    have hsq : (1 - 3 * n) * (1 - 3 * n) =
        (3 * n - 1) * (3 * n - 1) := by ring
    have hsign : negOnePowIntQ (1 - 3 * n) = negOnePowIntQ (3 * n - 1) := by
      rw [show 1 - 3 * n = -(3 * n - 1) by ring, negOnePowIntQ_neg]
    by_cases hroot : (3 * n - 1) * (3 * n - 1) = e
    · have hroot' : (1 - 3 * n) * (1 - 3 * n) = e := by
        rw [hsq]
        exact hroot
      simp [hroot, hroot', hsign]
    · have hroot' : ¬ (1 - 3 * n) * (1 - 3 * n) = e := by
        intro h
        apply hroot
        rwa [hsq] at h
      simp [hroot, hroot']
  rw [hterm, thetaOneCoeffTerm_three_mul_sub_one]

private theorem thetaNineCoeffTerm_zero_of_three_mul_not_mem
    (e W n : ℤ) (hW : jCoeffWindow 1 2 e ≤ W)
    (_hnS : n ∈ Finset.Icc (-W) W) (hnnot : 3 * n ∉ Finset.Icc (-W) W) :
    thetaNineCoeffTerm e n = 0 := by
  unfold thetaNineCoeffTerm
  by_cases hroot : (3 * n) * (3 * n) = e
  · have hexp : jExp 1 2 (3 * n) = e := by
      rw [jExp_one_two]
      exact hroot
    have hleft := jExp_root_le_window_left 1 2 e (3 * n) (by norm_num) hexp
    have hright := jExp_root_le_window_right 1 2 e (3 * n) (by norm_num) hexp
    exfalso
    apply hnnot
    rw [Finset.mem_Icc]
    exact ⟨by omega, by omega⟩
  · simp [hroot]

private theorem thetaThreeCoeffTerm_zero_of_three_mul_sub_one_not_mem
    (e W n : ℤ) (hW : jCoeffWindow 1 2 e ≤ W)
    (_hnS : n ∈ Finset.Icc (-W) W)
    (hnnot : 3 * n - 1 ∉ Finset.Icc (-W) W) :
    thetaThreeCoeffTerm e n = 0 := by
  unfold thetaThreeCoeffTerm
  by_cases hroot : (3 * n - 1) * (3 * n - 1) = e
  · have hexp : jExp 1 2 (3 * n - 1) = e := by
      rw [jExp_one_two]
      exact hroot
    have hleft := jExp_root_le_window_left 1 2 e (3 * n - 1) (by norm_num) hexp
    have hright := jExp_root_le_window_right 1 2 e (3 * n - 1) (by norm_num) hexp
    exfalso
    apply hnnot
    rw [Finset.mem_Icc]
    exact ⟨by omega, by omega⟩
  · simp [hroot]

private theorem thetaThreeCoeffTerm_zero_of_one_sub_three_mul_not_mem
    (e W n : ℤ) (hW : jCoeffWindow 1 2 e ≤ W)
    (_hnS : n ∈ Finset.Icc (-W) W)
    (hnnot : 1 - 3 * n ∉ Finset.Icc (-W) W) :
    thetaThreeCoeffTerm e n = 0 := by
  unfold thetaThreeCoeffTerm
  by_cases hroot : (3 * n - 1) * (3 * n - 1) = e
  · have hsq : (1 - 3 * n) * (1 - 3 * n) = e := by
      rw [show (1 - 3 * n) * (1 - 3 * n) =
        (3 * n - 1) * (3 * n - 1) by ring]
      exact hroot
    have hexp : jExp 1 2 (1 - 3 * n) = e := by
      rw [jExp_one_two]
      exact hsq
    have hleft := jExp_root_le_window_left 1 2 e (1 - 3 * n) (by norm_num) hexp
    have hright := jExp_root_le_window_right 1 2 e (1 - 3 * n) (by norm_num) hexp
    exfalso
    apply hnnot
    rw [Finset.mem_Icc]
    exact ⟨by omega, by omega⟩
  · simp [hroot]

private theorem thetaOne_sum_residue_zero (e W : ℤ)
    (hW : jCoeffWindow 1 2 e ≤ W) :
    (∑ n ∈ Finset.Icc (-W) W,
      if 3 ∣ n then thetaOneCoeffTerm e n else 0) =
      ∑ n ∈ Finset.Icc (-W) W, thetaNineCoeffTerm e n := by
  let S : Finset ℤ := Finset.Icc (-W) W
  let T : Finset ℤ := S.filter (fun n => 3 * n ∈ S)
  let U : Finset ℤ := S.filter (fun n => 3 ∣ n)
  have hT_subset : T ⊆ S := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have hsum_T_S :
      (∑ n ∈ T, thetaNineCoeffTerm e n) =
        ∑ n ∈ S, thetaNineCoeffTerm e n := by
    refine Finset.sum_subset hT_subset ?_
    intro n hnS hnT
    have hnnot : 3 * n ∉ S := by
      intro hmem
      apply hnT
      exact Finset.mem_filter.mpr ⟨hnS, hmem⟩
    exact thetaNineCoeffTerm_zero_of_three_mul_not_mem e W n hW hnS hnnot
  calc
    (∑ n ∈ Finset.Icc (-W) W,
        if 3 ∣ n then thetaOneCoeffTerm e n else 0)
        = ∑ n ∈ U, thetaOneCoeffTerm e n := by
            simp [U, S, Finset.sum_filter]
    _ = ∑ n ∈ T, thetaNineCoeffTerm e n := by
        symm
        refine Finset.sum_bij' (fun n _ => 3 * n) (fun n _ => n / 3)
          ?to_mem ?from_mem ?left_inv ?right_inv ?terms
        · intro n hn
          rw [Finset.mem_filter]
          exact ⟨(Finset.mem_filter.mp hn).2,
            ⟨n, by ring⟩⟩
        · intro n hn
          rw [Finset.mem_filter] at hn ⊢
          rcases hn.2 with ⟨m, hm⟩
          have hdiv : n / 3 = m := by
            apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
            omega
          change n / 3 ∈ S ∧ 3 * (n / 3) ∈ S
          constructor
          · rw [hdiv]
            rw [Finset.mem_Icc] at hn ⊢
            omega
          · rw [hdiv]
            simpa [hm] using hn.1
        · intro n hn
          rw [Finset.mem_filter] at hn
          exact Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0) rfl
        · intro n hn
          rw [Finset.mem_filter] at hn
          rcases hn.2 with ⟨m, hm⟩
          have hdiv : n / 3 = m := by
            apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
            omega
          change 3 * (n / 3) = n
          rw [hdiv]
          omega
        · intro n hn
          rw [thetaOneCoeffTerm_three_mul]
    _ = ∑ n ∈ Finset.Icc (-W) W, thetaNineCoeffTerm e n := hsum_T_S

private theorem thetaOne_sum_residue_plus (e W : ℤ)
    (hW : jCoeffWindow 1 2 e ≤ W) :
    (∑ n ∈ Finset.Icc (-W) W,
      if 3 ∣ n + 1 then thetaOneCoeffTerm e n else 0) =
      -∑ n ∈ Finset.Icc (-W) W, thetaThreeCoeffTerm e n := by
  let S : Finset ℤ := Finset.Icc (-W) W
  let T : Finset ℤ := S.filter (fun n => 3 * n - 1 ∈ S)
  let U : Finset ℤ := S.filter (fun n => 3 ∣ n + 1)
  have hT_subset : T ⊆ S := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have hsum_T_S :
      (∑ n ∈ T, thetaThreeCoeffTerm e n) =
        ∑ n ∈ S, thetaThreeCoeffTerm e n := by
    refine Finset.sum_subset hT_subset ?_
    intro n hnS hnT
    have hnnot : 3 * n - 1 ∉ S := by
      intro hmem
      apply hnT
      exact Finset.mem_filter.mpr ⟨hnS, hmem⟩
    exact thetaThreeCoeffTerm_zero_of_three_mul_sub_one_not_mem e W n hW hnS hnnot
  calc
    (∑ n ∈ Finset.Icc (-W) W,
        if 3 ∣ n + 1 then thetaOneCoeffTerm e n else 0)
        = ∑ n ∈ U, thetaOneCoeffTerm e n := by
            simp [U, S, Finset.sum_filter]
    _ = ∑ n ∈ T, -thetaThreeCoeffTerm e n := by
        symm
        refine Finset.sum_bij' (fun n _ => 3 * n - 1) (fun n _ => (n + 1) / 3)
          ?to_mem ?from_mem ?left_inv ?right_inv ?terms
        · intro n hn
          rw [Finset.mem_filter]
          constructor
          · exact (Finset.mem_filter.mp hn).2
          · exact ⟨n, by ring⟩
        · intro n hn
          rw [Finset.mem_filter] at hn ⊢
          rcases hn.2 with ⟨m, hm⟩
          have hdiv : (n + 1) / 3 = m := by
            apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
            omega
          change (n + 1) / 3 ∈ S ∧ 3 * ((n + 1) / 3) - 1 ∈ S
          constructor
          · rw [hdiv]
            rw [Finset.mem_Icc] at hn ⊢
            omega
          · rw [hdiv]
            have htarget : 3 * m - 1 = n := by omega
            rw [htarget]
            exact hn.1
        · intro n hn
          rw [Finset.mem_filter] at hn
          have hdiv : (3 * n - 1 + 1) / 3 = n := by
            apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
            ring
          exact hdiv
        · intro n hn
          rw [Finset.mem_filter] at hn
          rcases hn.2 with ⟨m, hm⟩
          have hdiv : (n + 1) / 3 = m := by
            apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
            omega
          change 3 * ((n + 1) / 3) - 1 = n
          rw [hdiv]
          omega
        · intro n hn
          rw [thetaOneCoeffTerm_three_mul_sub_one]
    _ = -∑ n ∈ T, thetaThreeCoeffTerm e n := by
          simp
    _ = -∑ n ∈ Finset.Icc (-W) W, thetaThreeCoeffTerm e n := by
          rw [hsum_T_S]

private theorem thetaOne_sum_residue_minus (e W : ℤ)
    (hW : jCoeffWindow 1 2 e ≤ W) :
    (∑ n ∈ Finset.Icc (-W) W,
      if 3 ∣ n - 1 then thetaOneCoeffTerm e n else 0) =
      -∑ n ∈ Finset.Icc (-W) W, thetaThreeCoeffTerm e n := by
  let S : Finset ℤ := Finset.Icc (-W) W
  let T : Finset ℤ := S.filter (fun n => 1 - 3 * n ∈ S)
  let U : Finset ℤ := S.filter (fun n => 3 ∣ n - 1)
  have hT_subset : T ⊆ S := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have hsum_T_S :
      (∑ n ∈ T, thetaThreeCoeffTerm e n) =
        ∑ n ∈ S, thetaThreeCoeffTerm e n := by
    refine Finset.sum_subset hT_subset ?_
    intro n hnS hnT
    have hnnot : 1 - 3 * n ∉ S := by
      intro hmem
      apply hnT
      exact Finset.mem_filter.mpr ⟨hnS, hmem⟩
    exact thetaThreeCoeffTerm_zero_of_one_sub_three_mul_not_mem e W n hW hnS hnnot
  calc
    (∑ n ∈ Finset.Icc (-W) W,
        if 3 ∣ n - 1 then thetaOneCoeffTerm e n else 0)
        = ∑ n ∈ U, thetaOneCoeffTerm e n := by
            simp [U, S, Finset.sum_filter]
    _ = ∑ n ∈ T, -thetaThreeCoeffTerm e n := by
        symm
        refine Finset.sum_bij' (fun n _ => 1 - 3 * n) (fun n _ => (1 - n) / 3)
          ?to_mem ?from_mem ?left_inv ?right_inv ?terms
        · intro n hn
          rw [Finset.mem_filter]
          constructor
          · exact (Finset.mem_filter.mp hn).2
          · exact ⟨-n, by ring⟩
        · intro n hn
          rw [Finset.mem_filter] at hn ⊢
          rcases hn.2 with ⟨m, hm⟩
          have hdiv : (1 - n) / 3 = -m := by
            apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
            omega
          change (1 - n) / 3 ∈ S ∧ 1 - 3 * ((1 - n) / 3) ∈ S
          constructor
          · rw [hdiv]
            rw [Finset.mem_Icc] at hn ⊢
            omega
          · rw [hdiv]
            rw [show 1 - 3 * (-m) = 1 + 3 * m by ring]
            have htarget : 1 + 3 * m = n := by omega
            rw [htarget]
            exact hn.1
        · intro n hn
          rw [Finset.mem_filter] at hn
          have hdiv : (1 - (1 - 3 * n)) / 3 = n := by
            apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
            ring
          exact hdiv
        · intro n hn
          rw [Finset.mem_filter] at hn
          rcases hn.2 with ⟨m, hm⟩
          have hdiv : (1 - n) / 3 = -m := by
            apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
            omega
          change 1 - 3 * ((1 - n) / 3) = n
          rw [hdiv]
          omega
        · intro n hn
          rw [thetaOneCoeffTerm_one_sub_three_mul]
    _ = -∑ n ∈ T, thetaThreeCoeffTerm e n := by
          simp
    _ = -∑ n ∈ Finset.Icc (-W) W, thetaThreeCoeffTerm e n := by
          rw [hsum_T_S]

private theorem thetaOne_dissection_sum (e W : ℤ)
    (hW : jCoeffWindow 1 2 e ≤ W) :
    (∑ n ∈ Finset.Icc (-W) W, thetaOneCoeffTerm e n) =
      (∑ n ∈ Finset.Icc (-W) W, thetaNineCoeffTerm e n) -
        2 * ∑ n ∈ Finset.Icc (-W) W, thetaThreeCoeffTerm e n := by
  calc
    (∑ n ∈ Finset.Icc (-W) W, thetaOneCoeffTerm e n)
        = ∑ n ∈ Finset.Icc (-W) W,
            ((if 3 ∣ n then thetaOneCoeffTerm e n else 0) +
              (if 3 ∣ n + 1 then thetaOneCoeffTerm e n else 0) +
                (if 3 ∣ n - 1 then thetaOneCoeffTerm e n else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro n _hn
            exact thetaOneCoeffTerm_split e n
    _ = (∑ n ∈ Finset.Icc (-W) W,
            if 3 ∣ n then thetaOneCoeffTerm e n else 0) +
          (∑ n ∈ Finset.Icc (-W) W,
            if 3 ∣ n + 1 then thetaOneCoeffTerm e n else 0) +
            (∑ n ∈ Finset.Icc (-W) W,
              if 3 ∣ n - 1 then thetaOneCoeffTerm e n else 0) := by
            simp [Finset.sum_add_distrib, add_assoc]
    _ = (∑ n ∈ Finset.Icc (-W) W, thetaNineCoeffTerm e n) -
          2 * ∑ n ∈ Finset.Icc (-W) W, thetaThreeCoeffTerm e n := by
            rw [thetaOne_sum_residue_zero e W hW,
              thetaOne_sum_residue_plus e W hW,
              thetaOne_sum_residue_minus e W hW]
            ring

private theorem jCoeff_one_two_as_thetaOneCoeffTerm (e W : ℤ)
    (hW : jCoeffWindow 1 2 e ≤ W) :
    jCoeff 1 2 e =
      ∑ n ∈ Finset.Icc (-W) W, thetaOneCoeffTerm e n := by
  rw [jCoeff_eq_sum_Icc_of_window_le 1 2 e W (by norm_num) hW]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  unfold thetaOneCoeffTerm
  rw [jExp_one_two]

private theorem jCoeff_nine_eighteen_as_thetaNineCoeffTerm (e W : ℤ)
    (hW : jCoeffWindow 9 18 e ≤ W) :
    jCoeff 9 18 e =
      ∑ n ∈ Finset.Icc (-W) W, thetaNineCoeffTerm e n := by
  rw [jCoeff_eq_sum_Icc_of_window_le 9 18 e W (by norm_num) hW]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  unfold thetaNineCoeffTerm
  rw [jExp_nine_eighteen]

private theorem jCoeff_three_eighteen_as_thetaThreeCoeffTerm (e W : ℤ)
    (hW : jCoeffWindow 3 18 (e - 1) ≤ W) :
    jCoeff 3 18 (e - 1) =
      ∑ n ∈ Finset.Icc (-W) W, thetaThreeCoeffTerm e n := by
  rw [jCoeff_eq_sum_Icc_of_window_le 3 18 (e - 1) W (by norm_num) hW]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  unfold thetaThreeCoeffTerm
  have hshift := jExp_three_eighteen_add_one n
  by_cases hroot : jExp 3 18 n = e - 1
  · have hsq : (3 * n - 1) * (3 * n - 1) = e := by omega
    simp [hroot, hsq]
  · have hsq : ¬ (3 * n - 1) * (3 * n - 1) = e := by
      intro h
      apply hroot
      omega
    simp [hroot, hsq]

/-- The cubic theta dissection used in the Appell cancellation. -/
theorem thetaOneLaurent_dissection :
    thetaOneLaurent = thetaNineLaurent - 2 * Qpow 1 * jLaurent 3 18 := by
  ext e
  let W : ℤ :=
    max (jCoeffWindow 1 2 e)
      (max (jCoeffWindow 9 18 e) (jCoeffWindow 3 18 (e - 1)))
  have hW1 : jCoeffWindow 1 2 e ≤ W := by
    dsimp [W]
    exact le_max_left _ _
  have hW9 : jCoeffWindow 9 18 e ≤ W := by
    dsimp [W]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hW3 : jCoeffWindow 3 18 (e - 1) ≤ W := by
    dsimp [W]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hcoeff :
      jCoeff 1 2 e = jCoeff 9 18 e - 2 * jCoeff 3 18 (e - 1) := by
    rw [jCoeff_one_two_as_thetaOneCoeffTerm e W hW1,
      jCoeff_nine_eighteen_as_thetaNineCoeffTerm e W hW9,
      jCoeff_three_eighteen_as_thetaThreeCoeffTerm e W hW3]
    exact thetaOne_dissection_sum e W hW1
  have htwo :
      lcoeff ((2 : QLaurent) * Qpow 1 * jLaurent 3 18) e =
        2 * jCoeff 3 18 (e - 1) := by
    change lcoeff (((HahnSeries.single (0 : ℤ) (2 : ℚ)) * Qpow 1) *
      jLaurent 3 18) e = 2 * jCoeff 3 18 (e - 1)
    rw [show (HahnSeries.single (0 : ℤ) (2 : ℚ) : QLaurent) * Qpow 1 =
      HahnSeries.single (1 : ℤ) (2 : ℚ) by simp [Qpow]]
    change ((HahnSeries.single (1 : ℤ) (2 : ℚ) : QLaurent) *
      jLaurent 3 18).coeff e = 2 * jCoeff 3 18 (e - 1)
    rw [HahnSeries.coeff_single_mul]
    change 2 * lcoeff (jLaurent 3 18) (e - 1) = 2 * jCoeff 3 18 (e - 1)
    rw [coeff_jLaurent]
  change lcoeff thetaOneLaurent e =
    lcoeff (thetaNineLaurent - 2 * Qpow 1 * jLaurent 3 18) e
  simp only [thetaOneLaurent, thetaNineLaurent, HahnSeries.coeff_sub, lcoeff] at hcoeff ⊢
  change (jLaurent 1 2).coeff e =
    (jLaurent 9 18).coeff e - ((2 : QLaurent) * Qpow 1 * jLaurent 3 18).coeff e
  rw [show (jLaurent 1 2).coeff e = jCoeff 1 2 e by
      change lcoeff (jLaurent 1 2) e = jCoeff 1 2 e
      rw [coeff_jLaurent],
    show (jLaurent 9 18).coeff e = jCoeff 9 18 e by
      change lcoeff (jLaurent 9 18) e = jCoeff 9 18 e
      rw [coeff_jLaurent],
    show ((2 : QLaurent) * Qpow 1 * jLaurent 3 18).coeff e =
      2 * jCoeff 3 18 (e - 1) by
      change lcoeff ((2 : QLaurent) * Qpow 1 * jLaurent 3 18) e =
        2 * jCoeff 3 18 (e - 1)
      exact htwo]
  exact hcoeff

/-- The `E_6` denominator in the cleared theta-correction identity is nonzero. -/
theorem E6Laurent_sq_ne_zero :
    E6Laurent ^ 2 ≠ 0 := by
  unfold E6Laurent etaLaurent
  exact pow_ne_zero 2 (jLaurent_ne_zero_of_pos_lt 6 18 (by norm_num) (by norm_num))

/-! ### Finite product-coefficient expansion for the HM 2.3 map-down -/

theorem lcoeff_mul_eq_sum_Icc_of_coeff_zero_lt
    (F G : QLaurent) (LF LG e : ℤ)
    (hF : ∀ n : ℤ, n < LF → lcoeff F n = 0)
    (hG : ∀ n : ℤ, n < LG → lcoeff G n = 0) :
    lcoeff (F * G) e =
      ∑ k ∈ Finset.Icc LF (e - LG), lcoeff F k * lcoeff G (e - k) := by
  let s : Set ℤ := Set.Ici LF
  let t : Set ℤ := Set.Ici LG
  have hs : s.IsPWO := by
    exact (show BddBelow s from ⟨LF, by intro n hn; exact hn⟩).isWF.isPWO
  have ht : t.IsPWO := by
    exact (show BddBelow t from ⟨LG, by intro n hn; exact hn⟩).isWF.isPWO
  have hFsupp : F.support ⊆ s := by
    intro n hn
    rw [HahnSeries.mem_support] at hn
    by_contra hnot
    have hnlt : n < LF := by
      exact lt_of_not_ge hnot
    exact hn (hF n hnlt)
  have hGsupp : G.support ⊆ t := by
    intro n hn
    rw [HahnSeries.mem_support] at hn
    by_contra hnot
    have hnlt : n < LG := by
      exact lt_of_not_ge hnot
    exact hn (hG n hnlt)
  calc
    lcoeff (F * G) e
        = ∑ ij ∈ Finset.addAntidiagonal hs G.isPWO_support e,
            F.coeff ij.1 * G.coeff ij.2 := by
            change (F * G).coeff e =
              ∑ ij ∈ Finset.addAntidiagonal hs G.isPWO_support e,
                F.coeff ij.1 * G.coeff ij.2
            rw [HahnSeries.coeff_mul_left' hs hFsupp]
    _ = ∑ ij ∈ Finset.addAntidiagonal hs ht e,
            F.coeff ij.1 * G.coeff ij.2 := by
            refine Finset.sum_subset (Finset.addAntidiagonal_mono_right hGsupp) ?_
            intro ij hij hnot
            rw [Finset.mem_addAntidiagonal] at hij
            have hGzero : G.coeff ij.2 = 0 := by
              by_contra hne
              apply hnot
              rw [Finset.mem_addAntidiagonal]
              exact ⟨hij.1, (HahnSeries.mem_support G ij.2).2 hne, hij.2.2⟩
            simp [hGzero]
    _ = ∑ k ∈ Finset.Icc LF (e - LG), lcoeff F k * lcoeff G (e - k) := by
            refine Finset.sum_bij' (fun ij _ => ij.1) (fun k _ => (k, e - k))
              ?to_mem ?from_mem ?left_inv ?right_inv ?term_eq
            · intro ij hij
              rw [Finset.mem_addAntidiagonal] at hij
              rw [Finset.mem_Icc]
              constructor
              · exact hij.1
              · have hsnd : LG ≤ ij.2 := hij.2.1
                have hsum : ij.1 + ij.2 = e := hij.2.2
                change ij.1 ≤ e - LG
                omega
            · intro k hk
              rw [Finset.mem_Icc] at hk
              rw [Finset.mem_addAntidiagonal]
              refine ⟨hk.1, ?_, ?_⟩
              · change LG ≤ e - k
                omega
              · change k + (e - k) = e
                omega
            · intro ij hij
              rw [Finset.mem_addAntidiagonal] at hij
              have hsum : ij.1 + ij.2 = e := hij.2.2
              ext
              · rfl
              · change e - ij.1 = ij.2
                omega
            · intro k hk
              rfl
            · intro ij hij
              rw [Finset.mem_addAntidiagonal] at hij
              have hsnd : ij.2 = e - ij.1 := by omega
              simp [lcoeff, hsnd]

theorem lcoeff_mul_eq_zero_of_lt_add_lower
    (F G : QLaurent) (LF LG e : ℤ)
    (hF : ∀ n : ℤ, n < LF → lcoeff F n = 0)
    (hG : ∀ n : ℤ, n < LG → lcoeff G n = 0)
    (he : e < LF + LG) :
    lcoeff (F * G) e = 0 := by
  rw [lcoeff_mul_eq_sum_Icc_of_coeff_zero_lt F G LF LG e hF hG]
  refine Finset.sum_eq_zero ?_
  intro k hk
  rw [Finset.mem_Icc] at hk
  exfalso
  omega

theorem lcoeff_jLaurent_eq_zero_of_lt_lower (a b e : ℤ)
    (he : e < jCoeffLower a b) :
    lcoeff (jLaurent a b) e = 0 := by
  rw [coeff_jLaurent]
  simp [jCoeff, he]

theorem lcoeff_appellNumeratorLaurent_eq_zero_of_lt_lower (a z e : ℤ)
    (he : e < appellNumeratorCoeffLower a z) :
    lcoeff (appellNumeratorLaurent a z) e = 0 := by
  rw [coeff_appellNumeratorLaurent]
  simp [appellNumeratorCoeff, he]

theorem appellNumeratorCoeff_eq_window_sum_of_lower_le
    (a z e : ℤ) (he : appellNumeratorCoeffLower a z ≤ e) :
    appellNumeratorCoeff a z e =
      ∑ r ∈ Finset.Icc (-(appellNumeratorCoeffWindow a z e))
          (appellNumeratorCoeffWindow a z e),
        negOnePowIntQ r *
          geomInvCoeff (appellDenomExp a z r) (e - appellNumeratorExp z r) := by
  unfold appellNumeratorCoeff
  rw [if_neg (by omega)]

theorem jCoeff_eq_window_sum_90 (a e : ℤ) :
    jCoeff a 90 e =
      ∑ n ∈ Finset.Icc (-(jCoeffWindow a 90 e)) (jCoeffWindow a 90 e),
        if jExp a 90 n = e then negOnePowIntQ n else 0 := by
  exact jCoeff_eq_window_sum a 90 e (by norm_num)

theorem lcoeff_two_jLaurent_90_eq_coeff_sum (w₁ w₂ e : ℤ) :
    lcoeff (jLaurent w₁ 90 * jLaurent w₂ 90) e =
      ∑ e₁ ∈ Finset.Icc (jCoeffLower w₁ 90) (e - jCoeffLower w₂ 90),
        jCoeff w₁ 90 e₁ * jCoeff w₂ 90 (e - e₁) := by
  rw [lcoeff_mul_eq_sum_Icc_of_coeff_zero_lt
    (jLaurent w₁ 90) (jLaurent w₂ 90)
    (jCoeffLower w₁ 90) (jCoeffLower w₂ 90) e
    (lcoeff_jLaurent_eq_zero_of_lt_lower w₁ 90)
    (lcoeff_jLaurent_eq_zero_of_lt_lower w₂ 90)]
  refine Finset.sum_congr rfl ?_
  intro e₁ _he₁
  rw [coeff_jLaurent, coeff_jLaurent]

theorem lcoeff_two_jLaurent_90_eq_zero_of_lt_lower (w₁ w₂ e : ℤ)
    (he : e < jCoeffLower w₁ 90 + jCoeffLower w₂ 90) :
    lcoeff (jLaurent w₁ 90 * jLaurent w₂ 90) e = 0 := by
  exact lcoeff_mul_eq_zero_of_lt_add_lower
    (jLaurent w₁ 90) (jLaurent w₂ 90)
    (jCoeffLower w₁ 90) (jCoeffLower w₂ 90) e
    (lcoeff_jLaurent_eq_zero_of_lt_lower w₁ 90)
    (lcoeff_jLaurent_eq_zero_of_lt_lower w₂ 90) he

theorem lcoeff_three_jLaurent_90_eq_coeff_sum (w₁ w₂ w₃ e : ℤ) :
    lcoeff (jLaurent w₁ 90 * (jLaurent w₂ 90 * jLaurent w₃ 90)) e =
      ∑ e₁ ∈ Finset.Icc (jCoeffLower w₁ 90)
          (e - (jCoeffLower w₂ 90 + jCoeffLower w₃ 90)),
        jCoeff w₁ 90 e₁ *
          ∑ e₂ ∈ Finset.Icc (jCoeffLower w₂ 90)
              (e - e₁ - jCoeffLower w₃ 90),
            jCoeff w₂ 90 e₂ * jCoeff w₃ 90 (e - e₁ - e₂) := by
  rw [lcoeff_mul_eq_sum_Icc_of_coeff_zero_lt
    (jLaurent w₁ 90) (jLaurent w₂ 90 * jLaurent w₃ 90)
    (jCoeffLower w₁ 90) (jCoeffLower w₂ 90 + jCoeffLower w₃ 90) e
    (lcoeff_jLaurent_eq_zero_of_lt_lower w₁ 90)
    (lcoeff_two_jLaurent_90_eq_zero_of_lt_lower w₂ w₃)]
  refine Finset.sum_congr rfl ?_
  intro e₁ _he₁
  rw [coeff_jLaurent, lcoeff_two_jLaurent_90_eq_coeff_sum]

theorem lcoeff_three_jLaurent_90_eq_zero_of_lt_lower (w₁ w₂ w₃ e : ℤ)
    (he : e < jCoeffLower w₁ 90 + (jCoeffLower w₂ 90 + jCoeffLower w₃ 90)) :
    lcoeff (jLaurent w₁ 90 * (jLaurent w₂ 90 * jLaurent w₃ 90)) e = 0 := by
  exact lcoeff_mul_eq_zero_of_lt_add_lower
    (jLaurent w₁ 90) (jLaurent w₂ 90 * jLaurent w₃ 90)
    (jCoeffLower w₁ 90) (jCoeffLower w₂ 90 + jCoeffLower w₃ 90) e
    (lcoeff_jLaurent_eq_zero_of_lt_lower w₁ 90)
    (lcoeff_two_jLaurent_90_eq_zero_of_lt_lower w₂ w₃) he

/--
Finite nested convolution for the HM-side product made from one Appell
numerator and three level-90 theta factors.
-/
theorem lcoeff_appellNumeratorLaurent_mul_three_jLaurent_90_eq_coeff_sum
    (a z w₁ w₂ w₃ e : ℤ) :
    lcoeff (appellNumeratorLaurent a z * jLaurent w₁ 90 *
        jLaurent w₂ 90 * jLaurent w₃ 90) e =
      ∑ E ∈ Finset.Icc (appellNumeratorCoeffLower a z)
          (e - (jCoeffLower w₁ 90 +
            (jCoeffLower w₂ 90 + jCoeffLower w₃ 90))),
        appellNumeratorCoeff a z E *
          ∑ E₁ ∈ Finset.Icc (jCoeffLower w₁ 90)
              (e - E - (jCoeffLower w₂ 90 + jCoeffLower w₃ 90)),
            jCoeff w₁ 90 E₁ *
              ∑ E₂ ∈ Finset.Icc (jCoeffLower w₂ 90)
                  (e - E - E₁ - jCoeffLower w₃ 90),
                jCoeff w₂ 90 E₂ * jCoeff w₃ 90 (e - E - E₁ - E₂) := by
  have hassoc :
      appellNumeratorLaurent a z * jLaurent w₁ 90 *
          jLaurent w₂ 90 * jLaurent w₃ 90 =
        appellNumeratorLaurent a z *
          (jLaurent w₁ 90 * (jLaurent w₂ 90 * jLaurent w₃ 90)) := by
    ring
  rw [hassoc]
  rw [lcoeff_mul_eq_sum_Icc_of_coeff_zero_lt
    (appellNumeratorLaurent a z)
    (jLaurent w₁ 90 * (jLaurent w₂ 90 * jLaurent w₃ 90))
    (appellNumeratorCoeffLower a z)
    (jCoeffLower w₁ 90 + (jCoeffLower w₂ 90 + jCoeffLower w₃ 90)) e
    (lcoeff_appellNumeratorLaurent_eq_zero_of_lt_lower a z)
    (lcoeff_three_jLaurent_90_eq_zero_of_lt_lower w₁ w₂ w₃)]
  refine Finset.sum_congr rfl ?_
  intro E _hE
  rw [coeff_appellNumeratorLaurent, lcoeff_three_jLaurent_90_eq_coeff_sum]

/--
The same four-factor formula with the Appell numerator and every `jCoeff`
opened into their concrete finite windows.
-/
theorem lcoeff_appellNumeratorLaurent_mul_three_jLaurent_90_eq_window_sum
    (a z w₁ w₂ w₃ e : ℤ) :
    lcoeff (appellNumeratorLaurent a z * jLaurent w₁ 90 *
        jLaurent w₂ 90 * jLaurent w₃ 90) e =
      ∑ E ∈ Finset.Icc (appellNumeratorCoeffLower a z)
          (e - (jCoeffLower w₁ 90 +
            (jCoeffLower w₂ 90 + jCoeffLower w₃ 90))),
        (∑ r ∈ Finset.Icc (-(appellNumeratorCoeffWindow a z E))
            (appellNumeratorCoeffWindow a z E),
          negOnePowIntQ r *
            geomInvCoeff (appellDenomExp a z r) (E - appellNumeratorExp z r)) *
          ∑ E₁ ∈ Finset.Icc (jCoeffLower w₁ 90)
              (e - E - (jCoeffLower w₂ 90 + jCoeffLower w₃ 90)),
            (∑ n₁ ∈ Finset.Icc (-(jCoeffWindow w₁ 90 E₁))
                (jCoeffWindow w₁ 90 E₁),
              if jExp w₁ 90 n₁ = E₁ then negOnePowIntQ n₁ else 0) *
              ∑ E₂ ∈ Finset.Icc (jCoeffLower w₂ 90)
                  (e - E - E₁ - jCoeffLower w₃ 90),
                (∑ n₂ ∈ Finset.Icc (-(jCoeffWindow w₂ 90 E₂))
                    (jCoeffWindow w₂ 90 E₂),
                  if jExp w₂ 90 n₂ = E₂ then negOnePowIntQ n₂ else 0) *
                  (∑ n₃ ∈ Finset.Icc
                      (-(jCoeffWindow w₃ 90 (e - E - E₁ - E₂)))
                      (jCoeffWindow w₃ 90 (e - E - E₁ - E₂)),
                    if jExp w₃ 90 n₃ = e - E - E₁ - E₂ then
                      negOnePowIntQ n₃ else 0) := by
  rw [lcoeff_appellNumeratorLaurent_mul_three_jLaurent_90_eq_coeff_sum]
  refine Finset.sum_congr rfl ?_
  intro E hE
  rw [Finset.mem_Icc] at hE
  rw [appellNumeratorCoeff_eq_window_sum_of_lower_le a z E hE.1]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro E₁ _hE₁
  rw [jCoeff_eq_window_sum_90 w₁ E₁]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro E₂ _hE₂
  rw [jCoeff_eq_window_sum_90 w₂ E₂,
    jCoeff_eq_window_sum_90 w₃ (e - E - E₁ - E₂)]

theorem thetaMulPFRawCoeffPF_eq_qPochInfPSCubeUPowerCoeffPF_coeff_of_hPF
    (hPF :
      Chapter10PF.thetaMulPFSeriesCoeffPF =
        Chapter10PF.qPochInfPSCubeUPowerCoeffPF)
    (N : ℕ) (u : ℤ) :
    Chapter10PF.thetaMulPFRawCoeffPF N u =
      (Chapter10PF.qPochInfPSCubeUPowerCoeffPF u).coeff N := by
  rw [Chapter10PF.thetaMulPFRawCoeffPF_eq_thetaMulPFCoeffPF]
  have hseries := congrFun hPF u
  have hcoeff := congrArg (fun P : ℤ⟦X⟧ => P.coeff N) hseries
  simpa [Chapter10PF.thetaMulPFSeriesCoeffPF] using hcoeff

/-! ### HM 2.3 finite reindexing algebra -/

/-- The integer exponent `t(t-1)/2`, shared by all level-90 theta factors. -/
abbrev hmTri (t : ℤ) : ℤ :=
  Chapter10PF.jExpIntPF t

theorem two_mul_hmTri (t : ℤ) :
    2 * hmTri t = t * (t - 1) := by
  unfold hmTri Chapter10PF.jExpIntPF
  have h := Chapter10PF.two_mul_triIntPF (t - 1)
  calc
    2 * Chapter10PF.triIntPF (t - 1)
        = (t - 1) * ((t - 1) + 1) := h
    _ = t * (t - 1) := by ring

/-- Term-1 HM 2.3 substitution used in the final PF reindexing. -/
def hm23Psi1_m (r j : ℤ) : ℤ := r - j
def hm23Psi1_p (j l k : ℤ) : ℤ := j + l + k
def hm23Psi1_z (r i j l k : ℤ) : ℤ := r + i - j - l - k - 1
def hm23Psi1_N (r k i j l : ℤ) : ℤ :=
  hmTri r + hmTri i + hmTri j + hmTri l + k * (r - 1) -
    hmTri (hm23Psi1_m r j) - hmTri (hm23Psi1_p j l k)

theorem hm23Psi1_inverse_i
    (r k i j l : ℤ) :
    hm23Psi1_z r i j l k + hm23Psi1_p j l k - r + 1 = i := by
  unfold hm23Psi1_z hm23Psi1_p
  ring

theorem hm23Psi1_inverse_j
    (r j : ℤ) :
    r - hm23Psi1_m r j = j := by
  unfold hm23Psi1_m
  ring

theorem hm23Psi1_inverse_l
    (r k j l : ℤ) :
    hm23Psi1_p j l k - r + hm23Psi1_m r j - k = l := by
  unfold hm23Psi1_p hm23Psi1_m
  ring

theorem hm23Psi1_exponent_identity
    (a z0 z1 r k i j l : ℤ) :
    90 * (hmTri r + hmTri i + hmTri j + hmTri l + k * (r - 1)) +
        z1 * r + k * (a + z1) + z0 * i + (a + z0) * j + (a + z1) * l =
      90 * (hmTri (hm23Psi1_m r j) + hmTri (hm23Psi1_p j l k) +
          hm23Psi1_N r k i j l) +
        z0 * (1 - hm23Psi1_m r j + hm23Psi1_p j l k +
          hm23Psi1_z r i j l k) +
        z1 * (hm23Psi1_m r j + hm23Psi1_p j l k) +
        a * hm23Psi1_p j l k := by
  unfold hm23Psi1_N hm23Psi1_m hm23Psi1_p hm23Psi1_z
  ring

theorem hm23Psi1_sign_identity
    (r k i j l : ℤ) :
    negOnePowIntQ (r + i + j + l) =
      negOnePowIntQ (hm23Psi1_m r j + hm23Psi1_p j l k) *
        negOnePowIntQ (i + j - k) := by
  rw [← negOnePowIntQ_add]
  apply congrArg negOnePowIntQ
  unfold hm23Psi1_m hm23Psi1_p
  ring

/-- Term-2 HM 2.3 substitution, with `r = h-k` in the blueprint. -/
def hm23Psi0_m (h j k : ℤ) : ℤ := h - j - k
def hm23Psi0_p (j l k : ℤ) : ℤ := j + l + k
def hm23Psi0_z (s h j l k : ℤ) : ℤ := s + h - j - l - k - 1
def hm23Psi0_r (h k : ℤ) : ℤ := h - k
def hm23Psi0_N (s k h j l : ℤ) : ℤ :=
  hmTri s + hmTri h + hmTri j + hmTri l + k * (s - 1) -
    hmTri (hm23Psi0_m h j k) - hmTri (hm23Psi0_p j l k)

theorem hm23Psi0_inverse_s
    (s k h j l : ℤ) :
    hm23Psi0_z s h j l k + hm23Psi0_p j l k -
        hm23Psi0_r h k + 1 - k = s := by
  unfold hm23Psi0_z hm23Psi0_p hm23Psi0_r
  ring

theorem hm23Psi0_inverse_h
    (h k : ℤ) :
    hm23Psi0_r h k + k = h := by
  unfold hm23Psi0_r
  ring

theorem hm23Psi0_inverse_j
    (h j k : ℤ) :
    hm23Psi0_r h k - hm23Psi0_m h j k = j := by
  unfold hm23Psi0_r hm23Psi0_m
  ring

theorem hm23Psi0_inverse_l
    (h j l k : ℤ) :
    hm23Psi0_p j l k - hm23Psi0_r h k + hm23Psi0_m h j k - k = l := by
  unfold hm23Psi0_p hm23Psi0_r hm23Psi0_m
  ring

theorem hm23Psi0_exponent_identity
    (a z0 z1 s k h j l : ℤ) :
    90 * (hmTri s + hmTri h + hmTri j + hmTri l + k * (s - 1)) +
        z0 * s + k * (a + z0) + z1 * h + (a + z0) * j + (a + z1) * l =
      90 * (hmTri (hm23Psi0_m h j k) + hmTri (hm23Psi0_p j l k) +
          hm23Psi0_N s k h j l) +
        z0 * (1 - hm23Psi0_m h j k + hm23Psi0_p j l k +
          hm23Psi0_z s h j l k) +
        z1 * (hm23Psi0_m h j k + hm23Psi0_p j l k) +
        a * hm23Psi0_p j l k := by
  unfold hm23Psi0_N hm23Psi0_m hm23Psi0_p hm23Psi0_z
  ring

theorem hm23Psi0_sign_identity
    (s k h j l : ℤ) :
    negOnePowIntQ (s + h + j + l) =
      negOnePowIntQ (hm23Psi0_m h j k + hm23Psi0_p j l k) *
        negOnePowIntQ (s + j) := by
  rw [← negOnePowIntQ_add]
  apply congrArg negOnePowIntQ
  unfold hm23Psi0_m hm23Psi0_p
  ring

theorem hm23Phi_quadratic_preservation
    (r i k : ℤ) :
    hmTri r + hmTri i + k * (r - 1) =
      hmTri (i - k) + hmTri (r + k) + k * (i - k - 1) := by
  have hr := two_mul_hmTri r
  have hi := two_mul_hmTri i
  have hik := two_mul_hmTri (i - k)
  have hrk := two_mul_hmTri (r + k)
  nlinarith

theorem hm23Phi_parity_preservation
    (r i j l k : ℤ) :
    negOnePowIntQ (r + i + j + l) =
      negOnePowIntQ ((i - k) + (r + k) + j + l) := by
  apply congrArg negOnePowIntQ
  ring

/-- The common residual PF window degree in `(m,p,z,r,k)` coordinates. -/
def hm23Ncoord (m p z r k : ℤ) : ℤ :=
  hmTri r + hmTri (z + p - r + 1) + hmTri (r - m) +
    hmTri (p - r + m - k) + k * (r - 1) - hmTri m - hmTri p

theorem hm23Psi1_N_eq_Ncoord (r k i j l : ℤ) :
    hm23Psi1_N r k i j l =
      hm23Ncoord (hm23Psi1_m r j) (hm23Psi1_p j l k)
        (hm23Psi1_z r i j l k) r k := by
  unfold hm23Psi1_N hm23Ncoord hm23Psi1_m hm23Psi1_p hm23Psi1_z
  ring

theorem hm23Psi0_N_eq_Ncoord (s k h j l : ℤ) :
    hm23Psi0_N s k h j l =
      hm23Ncoord (hm23Psi0_m h j k) (hm23Psi0_p j l k)
        (hm23Psi0_z s h j l k) (hm23Psi0_r h k) k := by
  unfold hm23Psi0_N hm23Ncoord hm23Psi0_m hm23Psi0_p hm23Psi0_z hm23Psi0_r
  rw [show s + h - j - l - k - 1 + (j + l + k) - (h - k) + 1 = s + k by ring,
    show h - k - (h - j - k) = j by ring,
    show j + l + k - (h - k) + (h - j - k) - k = l by ring]
  have hphi := hm23Phi_quadratic_preservation (h - k) (s + k) k
  rw [show s + k - k = s by ring, show h - k + k = h by ring] at hphi
  nlinarith

theorem hm23Psi1_residual_sign_coord (r k i j l : ℤ) :
    negOnePowIntQ (i + j - k) =
      negOnePowIntQ
        (hm23Psi1_z r i j l k + hm23Psi1_p j l k -
          hm23Psi1_m r j + 1 - k) := by
  apply congrArg negOnePowIntQ
  unfold hm23Psi1_z hm23Psi1_p hm23Psi1_m
  ring

theorem hm23Psi0_residual_sign_coord (s k h j l : ℤ) :
    negOnePowIntQ (s + j) =
      negOnePowIntQ
        (hm23Psi0_z s h j l k + hm23Psi0_p j l k -
          hm23Psi0_m h j k + 1 - k) := by
  apply congrArg negOnePowIntQ
  unfold hm23Psi0_z hm23Psi0_p hm23Psi0_m
  ring

theorem hm23Psi0_D_coord (a z0 s k h j l : ℤ) :
    appellDenomExp a z0 s =
      90 * (hm23Psi0_z s h j l k + hm23Psi0_p j l k -
        hm23Psi0_r h k - k) + a + z0 := by
  unfold appellDenomExp hm23Psi0_z hm23Psi0_p hm23Psi0_r
  ring

theorem hm23Ncoord_eq_pf_raw_exponent (m p z r k : ℤ) :
    hm23Ncoord m p z r k =
      hmTri (z + p - r + 1) +
        Chapter10PF.pfNumExpIntPF (r - m + k) +
          (r - m + k) * (r - p - 1) := by
  unfold hm23Ncoord Chapter10PF.pfNumExpIntPF
  have hr := two_mul_hmTri r
  have hi := two_mul_hmTri (z + p - r + 1)
  have hj := two_mul_hmTri (r - m)
  have hl := two_mul_hmTri (p - r + m - k)
  have hm := two_mul_hmTri m
  have hp := two_mul_hmTri p
  have hK := Chapter10PF.two_mul_triIntPF (r - m + k)
  nlinarith

theorem hm23_residual_sign_eq_pf_raw_sign (m p z r k : ℤ) :
    negOnePowIntQ (z + p - m + 1 - k) =
      negOnePowIntQ (z + p - r + 1) *
        negOnePowIntQ (r - m + k) := by
  rw [← negOnePowIntQ_add]
  rw [show z + p - r + 1 + (r - m + k) = z + p - m + 1 + k by ring]
  rw [negOnePowIntQ_eq_negOnePow, negOnePowIntQ_eq_negOnePow]
  exact_mod_cast ((Int.negOnePow_eq_iff (z + p - m + 1 - k)
    (z + p - m + 1 + k)).mpr ⟨-k, by ring⟩)

theorem negOnePowIntQ_eq_negOnePowIntPF_cast (n : ℤ) :
    negOnePowIntQ n =
      ((Chapter10PF.negOnePowIntPF ℤ n : ℤ) : ℚ) := by
  rw [negOnePowIntQ_eq_negOnePow,
    Chapter10PF.negOnePowIntPF_eq_negOnePow]

theorem hm23Ncoord_pf_raw_remainder
    (N : ℕ) (m p z r k : ℤ)
    (hN : (N : ℤ) = hm23Ncoord m p z r k) :
    (N : ℤ) - Chapter10PF.jExpIntPF (z + p - r + 1) -
        Chapter10PF.pfNumExpIntPF (r - m + k) =
      (r - m + k) * (r - p - 1) := by
  rw [hN, hm23Ncoord_eq_pf_raw_exponent]
  ring

theorem hm23_thetaMulPFRawBranchTermPF_rat_eq_coord
    (N : ℕ) (m p z r k : ℤ)
    (hN : (N : ℤ) = hm23Ncoord m p z r k) :
    ((Chapter10PF.thetaMulPFRawBranchTermPF N z (r - m + k)
        (z + p - r + 1) : ℤ) : ℚ) =
      negOnePowIntQ (z + p - m + 1 - k) *
        ((Chapter10PF.branchInvCoeffAtPF (r - m + k)
          ((r - m + k) * (r - p - 1)) (r - p - 1) : ℤ) : ℚ) := by
  have hpow := hm23_residual_sign_eq_pf_raw_sign m p z r k
  rw [negOnePowIntQ_eq_negOnePowIntPF_cast (z + p - r + 1),
    negOnePowIntQ_eq_negOnePowIntPF_cast (r - m + k)] at hpow
  have hrem := hm23Ncoord_pf_raw_remainder N m p z r k hN
  have hu : z - (z + p - r + 1) = r - p - 1 := by ring
  unfold Chapter10PF.thetaMulPFRawBranchTermPF
  rw [hrem, hu]
  simp only [Int.cast_mul]
  rw [← hpow]

/-- One-variable branch weight used in the HM 2.3 denominator transport. -/
def hm23Gamma (D k : ℤ) : ℚ :=
  (Chapter10PF.branchInvCoeffAtPF D (D * k) k : ℤ)

theorem hm23Gamma_eq (D k : ℤ) :
    hm23Gamma D k =
      if 0 ≤ D then
        if 0 ≤ k then 1 else 0
      else
        if k < 0 then -1 else 0 := by
  unfold hm23Gamma
  by_cases hD : 0 ≤ D
  · by_cases hk : 0 ≤ k
    · simp [Chapter10PF.branchInvCoeffAtPF, hD, hk]
    · simp [Chapter10PF.branchInvCoeffAtPF, hD, hk]
  · by_cases hk : k < 0
    · simp [Chapter10PF.branchInvCoeffAtPF, hD, hk]
    · simp [Chapter10PF.branchInvCoeffAtPF, hD, hk]

theorem hm23Gamma_ne_zero_iff_of_ne {D k : ℤ} (hD : D ≠ 0) :
    hm23Gamma D k ≠ 0 ↔
      (0 < D ∧ 0 ≤ k) ∨ (D < 0 ∧ k < 0) := by
  rw [hm23Gamma_eq]
  rcases lt_trichotomy D 0 with hDneg | hDzero | hDpos
  · have hDnonneg : ¬ 0 ≤ D := by omega
    have hDnotpos : ¬ 0 < D := by omega
    by_cases hk : k < 0
    · simp [hDnonneg, hDneg, hDnotpos, hk]
    · have hknonneg : 0 ≤ k := by omega
      simp [hDnonneg, hDneg, hDnotpos, hk, hknonneg]
  · subst D
    exact (hD rfl).elim
  · have hDnonneg : 0 ≤ D := by omega
    have hDnotneg : ¬ D < 0 := by omega
    by_cases hk : 0 ≤ k
    · simp [hDnonneg, hDpos, hDnotneg, hk]
    · have hkneg : k < 0 := by omega
      simp [hDnonneg, hDpos, hDnotneg, hk, hkneg]

theorem hm23Gamma_mul_nonneg {D k : ℤ} (hD : D ≠ 0)
    (h : hm23Gamma D k ≠ 0) :
    0 ≤ D * k := by
  rw [hm23Gamma_ne_zero_iff_of_ne hD] at h
  rcases h with h | h
  · nlinarith [h.1, h.2]
  · nlinarith [h.1, h.2]

theorem hm23Gamma_eq_heaviside (D k : ℤ) (hD : D ≠ 0) :
    hm23Gamma D k =
      (if 0 < D then (1 : ℚ) else 0) -
        (if D < 0 then (if k < 0 then 1 else 0) else
          (if k < 0 then 1 else 0)) := by
  by_cases hpos : 0 < D
  · have hnonneg : 0 ≤ D := by omega
    have hnotneg : ¬ D < 0 := by omega
    rw [hm23Gamma_eq]
    by_cases hk : k < 0
    · have hknonneg : ¬ 0 ≤ k := by omega
      simp [hpos, hnotneg, hnonneg, hk, hknonneg]
    · have hknonneg : 0 ≤ k := by omega
      simp [hpos, hnotneg, hnonneg, hk, hknonneg]
  · have hneg : D < 0 := by omega
    have hnonneg : ¬ 0 ≤ D := by omega
    rw [hm23Gamma_eq]
    by_cases hk : k < 0
    · simp [hpos, hneg, hnonneg, hk]
    · simp [hpos, hneg, hnonneg, hk]

theorem hm23Gamma_sub_eq_straddle
    (D1 D0 k : ℤ) (hD1 : D1 ≠ 0) (hD0 : D0 ≠ 0) :
    hm23Gamma D1 k - hm23Gamma D0 k =
      if D0 < 0 ∧ 0 < D1 then 1
      else if D1 < 0 ∧ 0 < D0 then -1
      else 0 := by
  rw [hm23Gamma_eq D1 k, hm23Gamma_eq D0 k]
  rcases lt_trichotomy D1 0 with h1neg | h1zero | h1pos
  · rcases lt_trichotomy D0 0 with h0neg | h0zero | h0pos
    · have h1nonneg : ¬ 0 ≤ D1 := by omega
      have h0nonneg : ¬ 0 ≤ D0 := by omega
      have h1notpos : ¬ 0 < D1 := by omega
      have h0notpos : ¬ 0 < D0 := by omega
      by_cases hk : k < 0
      · simp [h1nonneg, h0nonneg, h1neg, h0neg, h1notpos, h0notpos, hk]
      · simp [h1nonneg, h0nonneg, h1neg, h0neg, h1notpos, h0notpos, hk]
    · exact (hD0 h0zero).elim
    · have h1nonneg : ¬ 0 ≤ D1 := by omega
      have h0nonneg : 0 ≤ D0 := by omega
      by_cases hk : k < 0
      · have hknonneg : ¬ 0 ≤ k := by omega
        simp [h1nonneg, h0nonneg, h1neg, h0pos, hk, hknonneg]
      · have hknonneg : 0 ≤ k := by omega
        simp [h1nonneg, h0nonneg, h1neg, h0pos, hk, hknonneg]
  · exact (hD1 h1zero).elim
  · rcases lt_trichotomy D0 0 with h0neg | h0zero | h0pos
    · have h1nonneg : 0 ≤ D1 := by omega
      have h0nonneg : ¬ 0 ≤ D0 := by omega
      by_cases hk : k < 0
      · have hknonneg : ¬ 0 ≤ k := by omega
        simp [h1nonneg, h0nonneg, h1pos, h0neg, hk, hknonneg]
      · have hknonneg : 0 ≤ k := by omega
        simp [h1nonneg, h0nonneg, h1pos, h0neg, hk, hknonneg]
    · exact (hD0 h0zero).elim
    · have h1nonneg : 0 ≤ D1 := by omega
      have h0nonneg : 0 ≤ D0 := by omega
      have h1notneg : ¬ D1 < 0 := by omega
      have h0notneg : ¬ D0 < 0 := by omega
      by_cases hk : k < 0
      · have hknonneg : ¬ 0 ≤ k := by omega
        simp [h1nonneg, h0nonneg, h1pos, h0pos, h1notneg, h0notneg,
          hknonneg]
      · have hknonneg : 0 ≤ k := by omega
        simp [h1nonneg, h0nonneg, h1pos, h0pos, h1notneg, h0notneg,
          hknonneg]

theorem hm23Gamma_sub_eq_cutoff
    (D1 D0 k : ℤ) (hD1 : D1 ≠ 0) (hD0 : D0 ≠ 0) :
    hm23Gamma D1 k - hm23Gamma D0 k =
      (if 0 < D1 then (1 : ℚ) else 0) -
        (if 0 < D0 then (1 : ℚ) else 0) := by
  rw [hm23Gamma_sub_eq_straddle D1 D0 k hD1 hD0]
  rcases lt_trichotomy D1 0 with h1neg | h1zero | h1pos
  · rcases lt_trichotomy D0 0 with h0neg | h0zero | h0pos
    · have h1notpos : ¬ 0 < D1 := by omega
      have h0notpos : ¬ 0 < D0 := by omega
      simp [h1neg, h0neg, h1notpos, h0notpos]
    · exact (hD0 h0zero).elim
    · have h1notpos : ¬ 0 < D1 := by omega
      simp [h1neg, h0pos, h1notpos]
  · exact (hD1 h1zero).elim
  · rcases lt_trichotomy D0 0 with h0neg | h0zero | h0pos
    · have h0notpos : ¬ 0 < D0 := by omega
      simp [h1pos, h0neg, h0notpos]
    · exact (hD0 h0zero).elim
    · have h1notneg : ¬ D1 < 0 := by omega
      have h0notneg : ¬ D0 < 0 := by omega
      simp [h1pos, h0pos, h1notneg, h0notneg]

theorem hm23Gamma_coord_sub_eq_cutoff
    (a z0 z1 _m p z r k : ℤ)
    (hreg : hm23Nonsingular a z0 z1) :
    hm23Gamma (appellDenomExp a z1 r) k -
        hm23Gamma (appellDenomExp a z0 (z + p - r + 1 - k)) k =
      (if 0 < appellDenomExp a z1 r then (1 : ℚ) else 0) -
        (if 0 < appellDenomExp a z0 (z + p - r + 1 - k) then
          (1 : ℚ) else 0) := by
  exact hm23Gamma_sub_eq_cutoff
    (appellDenomExp a z1 r)
    (appellDenomExp a z0 (z + p - r + 1 - k)) k
    (hm23Nonsingular_appellDenomExp_z1_ne_zero
      (a := a) (z0 := z0) (z1 := z1) (r := r) hreg)
    (hm23Nonsingular_appellDenomExp_z0_ne_zero
      (a := a) (z0 := z0) (z1 := z1)
      (r := z + p - r + 1 - k) hreg)

theorem hm23_branchInvCoeffAtPF_eq_sum_Gamma
    (D q : ℤ) (hD : D ≠ 0) :
    ((Chapter10PF.branchInvCoeffAtPF D q (q / D) : ℤ) : ℚ) =
      ∑ k ∈ Finset.Icc (-((q / D).natAbs : ℤ)) ((q / D).natAbs : ℤ),
        if q = D * k then hm23Gamma D k else 0 := by
  let K : ℤ := q / D
  let W : ℤ := (q / D).natAbs
  have hKmem : K ∈ Finset.Icc (-W) W := by
    rw [Finset.mem_Icc]
    constructor
    · dsimp [K, W]
      have h : -(q / D) ≤ ((-(q / D)).natAbs : ℤ) := Int.le_natAbs
      rw [Int.natAbs_neg] at h
      omega
    · dsimp [K, W]
      exact Int.le_natAbs
  by_cases hq : q = D * K
  · have hunique : ∀ k : ℤ, q = D * k → k = K := by
      intro k hk
      dsimp [K]
      exact (Int.ediv_eq_of_eq_mul_right hD hk).symm
    trans
      (if K ∈ Finset.Icc (-W) W then hm23Gamma D K else 0)
    · rw [if_pos hKmem]
      unfold hm23Gamma
      rw [hq]
      rw [Int.mul_ediv_cancel_left K hD]
    · rw [← Finset.sum_ite_eq' (Finset.Icc (-W) W) K
        (fun k => hm23Gamma D k)]
      refine Finset.sum_congr rfl ?_
      intro k hk
      by_cases hkq : q = D * k
      · have hkK := hunique k hkq
        simp [hkq, hkK]
      · by_cases hkK : k = K
        · exfalso
          apply hkq
          rw [hkK]
          exact hq
        · simp [hkq, hkK]
  · have hleft :
      ((Chapter10PF.branchInvCoeffAtPF D q K : ℤ) : ℚ) = 0 := by
      dsimp [K]
      have hqK : ¬ q = D * (q / D) := by
        simpa [K] using hq
      by_cases hDnonneg : 0 ≤ D
      · by_cases hKnonneg : 0 ≤ q / D
        · simp [Chapter10PF.branchInvCoeffAtPF, hDnonneg, hKnonneg, hqK]
        · simp [Chapter10PF.branchInvCoeffAtPF, hDnonneg, hKnonneg]
      · by_cases hKneg : q / D < 0
        · simp [Chapter10PF.branchInvCoeffAtPF, hDnonneg, hKneg, hqK]
        · simp [Chapter10PF.branchInvCoeffAtPF, hDnonneg, hKneg]
    rw [hleft]
    symm
    refine Finset.sum_eq_zero ?_
    intro k hk
    by_cases hkq : q = D * k
    · have hkK : k = K := by
        dsimp [K]
        exact (Int.ediv_eq_of_eq_mul_right hD hkq).symm
      exfalso
      apply hq
      simpa [hkK] using hkq
    · simp [hkq]

theorem appellNumeratorPFBranchCoeff_eq_sum_Gamma
    (a z e : ℤ) (hden : ∀ r : ℤ, appellDenomExp a z r ≠ 0) :
    appellNumeratorPFBranchCoeff a z e =
      if e < appellNumeratorCoeffLower a z then 0
      else
        ∑ r ∈ Finset.Icc (-(appellNumeratorCoeffWindow a z e))
            (appellNumeratorCoeffWindow a z e),
          negOnePowIntQ r *
            ∑ k ∈ Finset.Icc
                (-(((e - appellNumeratorExp z r) /
                    appellDenomExp a z r).natAbs : ℤ))
                ((((e - appellNumeratorExp z r) /
                    appellDenomExp a z r).natAbs : ℤ)),
              if e - appellNumeratorExp z r =
                  appellDenomExp a z r * k then
                hm23Gamma (appellDenomExp a z r) k
              else
                0 := by
  by_cases hlt : e < appellNumeratorCoeffLower a z
  · simp [appellNumeratorPFBranchCoeff, hlt]
  · simp only [appellNumeratorPFBranchCoeff, hlt, if_false]
    refine Finset.sum_congr rfl ?_
    intro r _hr
    rw [hm23_branchInvCoeffAtPF_eq_sum_Gamma
      (appellDenomExp a z r) (e - appellNumeratorExp z r) (hden r)]

def hm23GammaWindowFourFactorSum
    (a z w₁ w₂ w₃ e : ℤ) : ℚ :=
  ∑ E ∈ Finset.Icc (appellNumeratorCoeffLower a z)
      (e - (jCoeffLower w₁ 90 +
        (jCoeffLower w₂ 90 + jCoeffLower w₃ 90))),
    (∑ r ∈ Finset.Icc (-(appellNumeratorCoeffWindow a z E))
        (appellNumeratorCoeffWindow a z E),
      negOnePowIntQ r *
        ∑ k ∈ Finset.Icc
            (-(((E - appellNumeratorExp z r) /
                appellDenomExp a z r).natAbs : ℤ))
            ((((E - appellNumeratorExp z r) /
                appellDenomExp a z r).natAbs : ℤ)),
          if E - appellNumeratorExp z r =
              appellDenomExp a z r * k then
            hm23Gamma (appellDenomExp a z r) k
          else
            0) *
      ∑ E₁ ∈ Finset.Icc (jCoeffLower w₁ 90)
          (e - E - (jCoeffLower w₂ 90 + jCoeffLower w₃ 90)),
        (∑ n₁ ∈ Finset.Icc (-(jCoeffWindow w₁ 90 E₁))
            (jCoeffWindow w₁ 90 E₁),
          if jExp w₁ 90 n₁ = E₁ then negOnePowIntQ n₁ else 0) *
          ∑ E₂ ∈ Finset.Icc (jCoeffLower w₂ 90)
              (e - E - E₁ - jCoeffLower w₃ 90),
            (∑ n₂ ∈ Finset.Icc (-(jCoeffWindow w₂ 90 E₂))
                (jCoeffWindow w₂ 90 E₂),
              if jExp w₂ 90 n₂ = E₂ then negOnePowIntQ n₂ else 0) *
              (∑ n₃ ∈ Finset.Icc
                  (-(jCoeffWindow w₃ 90 (e - E - E₁ - E₂)))
                  (jCoeffWindow w₃ 90 (e - E - E₁ - E₂)),
                if jExp w₃ 90 n₃ = e - E - E₁ - E₂ then
                  negOnePowIntQ n₃ else 0)

theorem lcoeff_appellNumeratorLaurent_mul_three_jLaurent_90_eq_Gamma_window_sum
    (a z w₁ w₂ w₃ e : ℤ)
    (hden : ∀ r : ℤ, appellDenomExp a z r ≠ 0)
    (hnum : ∀ E : ℤ,
      appellNumeratorCoeff a z E = appellNumeratorPFBranchCoeff a z E) :
    lcoeff (appellNumeratorLaurent a z * jLaurent w₁ 90 *
        jLaurent w₂ 90 * jLaurent w₃ 90) e =
      hm23GammaWindowFourFactorSum a z w₁ w₂ w₃ e := by
  rw [lcoeff_appellNumeratorLaurent_mul_three_jLaurent_90_eq_coeff_sum]
  unfold hm23GammaWindowFourFactorSum
  refine Finset.sum_congr rfl ?_
  intro E hE
  rw [hnum E, appellNumeratorPFBranchCoeff_eq_sum_Gamma a z E hden]
  have hnot : ¬ E < appellNumeratorCoeffLower a z := by
    rw [Finset.mem_Icc] at hE
    omega
  rw [if_neg hnot]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro E₁ _hE₁
  rw [jCoeff_eq_window_sum_90 w₁ E₁]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro E₂ _hE₂
  rw [jCoeff_eq_window_sum_90 w₂ E₂,
    jCoeff_eq_window_sum_90 w₃ (e - E - E₁ - E₂)]

/-- Source coordinates for the first HM 2.3 transported term. -/
structure HM23Psi1Source where
  r : ℤ
  k : ℤ
  i : ℤ
  j : ℤ
  l : ℤ
deriving DecidableEq

/-- Source coordinates for the second HM 2.3 transported term. -/
structure HM23Psi0Source where
  s : ℤ
  k : ℤ
  h : ℤ
  j : ℤ
  l : ℤ
deriving DecidableEq

/-- Shared `(m,p,z,N,r,k)` coordinates after the HM 2.3 transport. -/
structure HM23Coord where
  m : ℤ
  p : ℤ
  z : ℤ
  N : ℤ
  r : ℤ
  k : ℤ
deriving DecidableEq

def hm23Psi1Coord (x : HM23Psi1Source) : HM23Coord :=
  { m := hm23Psi1_m x.r x.j
    p := hm23Psi1_p x.j x.l x.k
    z := hm23Psi1_z x.r x.i x.j x.l x.k
    N := hm23Psi1_N x.r x.k x.i x.j x.l
    r := x.r
    k := x.k }

def hm23Psi1SourceOfCoord (x : HM23Coord) : HM23Psi1Source :=
  { r := x.r
    k := x.k
    i := x.z + x.p - x.r + 1
    j := x.r - x.m
    l := x.p - x.r + x.m - x.k }

theorem hm23Psi1SourceOfCoord_left_inv (x : HM23Psi1Source) :
    hm23Psi1SourceOfCoord (hm23Psi1Coord x) = x := by
  cases x
  simp [hm23Psi1Coord, hm23Psi1SourceOfCoord,
    hm23Psi1_inverse_i, hm23Psi1_inverse_j, hm23Psi1_inverse_l]

def hm23Psi0Coord (x : HM23Psi0Source) : HM23Coord :=
  { m := hm23Psi0_m x.h x.j x.k
    p := hm23Psi0_p x.j x.l x.k
    z := hm23Psi0_z x.s x.h x.j x.l x.k
    N := hm23Psi0_N x.s x.k x.h x.j x.l
    r := hm23Psi0_r x.h x.k
    k := x.k }

def hm23Psi0SourceOfCoord (x : HM23Coord) : HM23Psi0Source :=
  { s := x.z + x.p - x.r + 1 - x.k
    k := x.k
    h := x.r + x.k
    j := x.r - x.m
    l := x.p - x.r + x.m - x.k }

theorem hm23Psi0SourceOfCoord_left_inv (x : HM23Psi0Source) :
    hm23Psi0SourceOfCoord (hm23Psi0Coord x) = x := by
  cases x
  simp [hm23Psi0Coord, hm23Psi0SourceOfCoord,
    hm23Psi0_inverse_s, hm23Psi0_inverse_h, hm23Psi0_inverse_j,
    hm23Psi0_inverse_l]

def hm23TermOutExp (a z0 z1 m p z N : ℤ) : ℤ :=
  90 * (hmTri m + hmTri p + N) +
    z0 * (1 - m + p + z) + z1 * (m + p) + a * p

def hm23Term1SourceExp (a z0 z1 : ℤ) (x : HM23Psi1Source) : ℤ :=
  90 * (hmTri x.r + hmTri x.i + hmTri x.j + hmTri x.l +
      x.k * (x.r - 1)) +
    z1 * x.r + x.k * (a + z1) + z0 * x.i +
      (a + z0) * x.j + (a + z1) * x.l

def hm23Term2SourceExp (a z0 z1 : ℤ) (x : HM23Psi0Source) : ℤ :=
  90 * (hmTri x.s + hmTri x.h + hmTri x.j + hmTri x.l +
      x.k * (x.s - 1)) +
    z0 * x.s + x.k * (a + z0) + z1 * x.h +
      (a + z0) * x.j + (a + z1) * x.l

def hm23Term1SourceSummand (a z0 z1 e : ℤ) (x : HM23Psi1Source) : ℚ :=
  if hm23Term1SourceExp a z0 z1 x = e then
    negOnePowIntQ (x.r + x.i + x.j + x.l) *
      hm23Gamma (appellDenomExp a z1 x.r) x.k
  else 0

def hm23Term2SourceSummand (a z0 z1 e : ℤ) (x : HM23Psi0Source) : ℚ :=
  if hm23Term2SourceExp a z0 z1 x = e then
    negOnePowIntQ (x.s + x.h + x.j + x.l) *
      hm23Gamma (appellDenomExp a z0 x.s) x.k
  else 0

/-- Flattened eight-coordinate index for a concrete Gamma window.  The order is
chosen to match the normal form produced by distributing the two finite
products in `hm23GammaWindowFourFactorSum`. -/
abbrev HM23GammaWindowSigma :=
  Sigma fun _E : ℤ => Sigma fun _E₁ : ℤ => Sigma fun _E₂ : ℤ =>
  Sigma fun _n₃ : ℤ => Sigma fun _n₂ : ℤ => Sigma fun _n₁ : ℤ =>
  Sigma fun _r : ℤ => ℤ

def hm23GW_E (x : HM23GammaWindowSigma) : ℤ := x.1
def hm23GW_E₁ (x : HM23GammaWindowSigma) : ℤ := x.2.1
def hm23GW_E₂ (x : HM23GammaWindowSigma) : ℤ := x.2.2.1
def hm23GW_n₃ (x : HM23GammaWindowSigma) : ℤ := x.2.2.2.1
def hm23GW_n₂ (x : HM23GammaWindowSigma) : ℤ := x.2.2.2.2.1
def hm23GW_n₁ (x : HM23GammaWindowSigma) : ℤ := x.2.2.2.2.2.1
def hm23GW_r (x : HM23GammaWindowSigma) : ℤ := x.2.2.2.2.2.2.1
def hm23GW_k (x : HM23GammaWindowSigma) : ℤ := x.2.2.2.2.2.2.2

def hm23GammaWindowSigmaSet (a z w₁ w₂ w₃ e : ℤ) :
    Finset HM23GammaWindowSigma :=
  (Finset.Icc (appellNumeratorCoeffLower a z)
      (e - (jCoeffLower w₁ 90 +
        (jCoeffLower w₂ 90 + jCoeffLower w₃ 90)))).sigma fun E =>
  (Finset.Icc (jCoeffLower w₁ 90)
      (e - E - (jCoeffLower w₂ 90 + jCoeffLower w₃ 90))).sigma fun E₁ =>
  (Finset.Icc (jCoeffLower w₂ 90)
      (e - E - E₁ - jCoeffLower w₃ 90)).sigma fun E₂ =>
  (Finset.Icc (-(jCoeffWindow w₃ 90 (e - E - E₁ - E₂)))
      (jCoeffWindow w₃ 90 (e - E - E₁ - E₂))).sigma fun _n₃ =>
  (Finset.Icc (-(jCoeffWindow w₂ 90 E₂))
      (jCoeffWindow w₂ 90 E₂)).sigma fun _n₂ =>
  (Finset.Icc (-(jCoeffWindow w₁ 90 E₁))
      (jCoeffWindow w₁ 90 E₁)).sigma fun _n₁ =>
  (Finset.Icc (-(appellNumeratorCoeffWindow a z E))
      (appellNumeratorCoeffWindow a z E)).sigma fun r =>
  Finset.Icc
    (-(((E - appellNumeratorExp z r) /
      appellDenomExp a z r).natAbs : ℤ))
    ((((E - appellNumeratorExp z r) /
      appellDenomExp a z r).natAbs : ℤ))

def hm23GammaWindowSigmaSummand (a z w₁ w₂ w₃ e : ℤ)
    (x : HM23GammaWindowSigma) : ℚ :=
  let E := hm23GW_E x
  let E₁ := hm23GW_E₁ x
  let E₂ := hm23GW_E₂ x
  let n₃ := hm23GW_n₃ x
  let n₂ := hm23GW_n₂ x
  let n₁ := hm23GW_n₁ x
  let r := hm23GW_r x
  let k := hm23GW_k x
  (((negOnePowIntQ r *
      (if E - appellNumeratorExp z r =
          appellDenomExp a z r * k then
        hm23Gamma (appellDenomExp a z r) k
      else 0)) *
    (if jExp w₁ 90 n₁ = E₁ then negOnePowIntQ n₁ else 0)) *
      (if jExp w₂ 90 n₂ = E₂ then negOnePowIntQ n₂ else 0)) *
        (if jExp w₃ 90 n₃ = e - E - E₁ - E₂ then
          negOnePowIntQ n₃ else 0)

def hm23GammaWindowSigmaToPsi1 (x : HM23GammaWindowSigma) : HM23Psi1Source :=
  { r := hm23GW_r x
    k := hm23GW_k x
    i := hm23GW_n₁ x
    j := hm23GW_n₂ x
    l := hm23GW_n₃ x }

def hm23GammaWindowSigmaToPsi0 (x : HM23GammaWindowSigma) : HM23Psi0Source :=
  { s := hm23GW_r x
    k := hm23GW_k x
    h := hm23GW_n₁ x
    j := hm23GW_n₂ x
    l := hm23GW_n₃ x }

theorem jExp90_eq_hmTri (w n : ℤ) :
    jExp w 90 n = 90 * hmTri n + w * n := by
  apply (mul_left_injective₀ (show (2 : ℤ) ≠ 0 by norm_num))
  have h := two_mul_jExp w 90 n
  have ht := two_mul_hmTri n
  unfold jExpTwice at h
  nlinarith

theorem appellNumeratorExp_eq_hmTri (z r : ℤ) :
    appellNumeratorExp z r = 90 * hmTri r + z * r := by
  change jExp z 90 r = 90 * hmTri r + z * r
  exact jExp90_eq_hmTri z r

theorem appellNumeratorCoeffLower_le_exp_add_denom_mul_of_Gamma_ne_zero
    (a z r k E : ℤ)
    (hE : E = appellNumeratorExp z r + appellDenomExp a z r * k)
    (hD : appellDenomExp a z r ≠ 0)
    (hGamma : hm23Gamma (appellDenomExp a z r) k ≠ 0) :
    appellNumeratorCoeffLower a z ≤ E := by
  have hmul :
      0 ≤ appellDenomExp a z r * k :=
    hm23Gamma_mul_nonneg hD hGamma
  have hj : jCoeffLower z 90 ≤ appellNumeratorExp z r := by
    change jCoeffLower z 90 ≤ jExp z 90 r
    exact jExp_lower_bound z 90 r (by norm_num)
  have hlower :
      appellNumeratorCoeffLower a z ≤ jCoeffLower z 90 := by
    unfold appellNumeratorCoeffLower jCoeffLower
    let A : ℤ := |a|
    let Z : ℤ := |z|
    have hA : 0 ≤ A := by exact abs_nonneg a
    have hZ : 0 ≤ Z := by exact abs_nonneg z
    have hrewrite :
        ((Int.natAbs a + Int.natAbs z + 92 : ℤ) ^ 2) =
          (A + Z + 92) ^ 2 := by
      dsimp [A, Z]
      rw [Int.natCast_natAbs, Int.natCast_natAbs]
    have hrewrite' :
        ((Int.natAbs z + Int.natAbs 90 + 2 : ℤ) ^ 2) =
          (Z + 92) ^ 2 := by
      dsimp [Z]
      rw [Int.natCast_natAbs]
      ring
    rw [hrewrite, hrewrite']
    nlinarith [sq_nonneg A, sq_nonneg (Z + 92)]
  rw [hE]
  nlinarith

theorem appellNumeratorExp_add_denom_mul_mem_window_of_Gamma_ne_zero
    (a z r k E : ℤ)
    (hE : E = appellNumeratorExp z r + appellDenomExp a z r * k)
    (hD : appellDenomExp a z r ≠ 0)
    (hGamma : hm23Gamma (appellDenomExp a z r) k ≠ 0) :
    r ∈ Finset.Icc (-(appellNumeratorCoeffWindow a z E))
      (appellNumeratorCoeffWindow a z E) := by
  rw [Finset.mem_Icc]
  have hmul :
      0 ≤ appellDenomExp a z r * k :=
    hm23Gamma_mul_nonneg hD hGamma
  have hbase_le_E : appellNumeratorExp z r ≤ E := by
    rw [hE]
    nlinarith
  have hE_le_abs : E ≤ |E| := le_abs_self E
  have hbase_le_abs : appellNumeratorExp z r ≤ |E| :=
    le_trans hbase_le_E hE_le_abs
  have htw :
      2 * appellNumeratorExp z r =
        90 * r * (r - 1) + 2 * z * r := by
    rw [appellNumeratorExp_eq_hmTri]
    have hr := two_mul_hmTri r
    nlinarith
  let A : ℤ := |a|
  let Z : ℤ := |z|
  let EE : ℤ := |E|
  have hA : 0 ≤ A := by exact abs_nonneg a
  have hZ : 0 ≤ Z := by exact abs_nonneg z
  have hEE : 0 ≤ EE := by exact abs_nonneg E
  have hz_lower : -Z ≤ z := by
    dsimp [Z]
    exact neg_abs_le z
  have hz_upper : z ≤ Z := by
    dsimp [Z]
    exact le_abs_self z
  have hwindow :
      appellNumeratorCoeffWindow a z E = 4 * (A + Z + EE + 92) := by
    unfold appellNumeratorCoeffWindow
    dsimp [A, Z, EE]
    rw [Int.natCast_natAbs, Int.natCast_natAbs, Int.natCast_natAbs]
  constructor
  · by_contra hleft
    rw [hwindow] at hleft
    have hr_lt : r < -4 * (A + Z + EE + 92) := by omega
    have hr_nonpos : r ≤ 0 := by nlinarith
    have hzterm : Z * r ≤ z * r := by nlinarith
    have hbig :
        2 * EE < 90 * r * (r - 1) + 2 * z * r := by
      nlinarith [hzterm, sq_nonneg (r + (Z + EE + 92))]
    nlinarith
  · by_contra hright
    rw [hwindow] at hright
    have hr_gt : 4 * (A + Z + EE + 92) < r := by omega
    have hr_pos : 0 < r := by nlinarith
    have hzterm : -Z * r ≤ z * r := by nlinarith
    have hbig :
        2 * EE < 90 * r * (r - 1) + 2 * z * r := by
      nlinarith [hzterm, sq_nonneg (r - (Z + EE + 92))]
    nlinarith

theorem hm23Term1SourceExp_eq_window_parts
    (a z0 z1 r k i j l : ℤ) :
    hm23Term1SourceExp a z0 z1
        { r := r, k := k, i := i, j := j, l := l } =
      appellNumeratorExp z1 r + appellDenomExp a z1 r * k +
        jExp z0 90 i + jExp (a + z0) 90 j +
          jExp (a + z1) 90 l := by
  rw [appellNumeratorExp_eq_hmTri, jExp90_eq_hmTri,
    jExp90_eq_hmTri, jExp90_eq_hmTri]
  unfold hm23Term1SourceExp appellDenomExp
  ring

theorem hm23Term2SourceExp_eq_window_parts
    (a z0 z1 s k h j l : ℤ) :
    hm23Term2SourceExp a z0 z1
        { s := s, k := k, h := h, j := j, l := l } =
      appellNumeratorExp z0 s + appellDenomExp a z0 s * k +
        jExp z1 90 h + jExp (a + z0) 90 j +
          jExp (a + z1) 90 l := by
  rw [appellNumeratorExp_eq_hmTri, jExp90_eq_hmTri,
    jExp90_eq_hmTri, jExp90_eq_hmTri]
  unfold hm23Term2SourceExp appellDenomExp
  ring

theorem hm23Term1SourceExp_phi_eq_term2SourceExp
    (a z0 z1 r k i j l : ℤ) :
    hm23Term1SourceExp a z0 z1
        { r := r, k := k, i := i, j := j, l := l } =
      hm23Term2SourceExp a z0 z1
        { s := i - k, k := k, h := r + k, j := j, l := l } := by
  unfold hm23Term1SourceExp hm23Term2SourceExp
  have hphi := hm23Phi_quadratic_preservation r i k
  nlinarith

theorem hm23Term2SourceExp_phi_eq_term1SourceExp
    (a z0 z1 s k h j l : ℤ) :
    hm23Term2SourceExp a z0 z1
        { s := s, k := k, h := h, j := j, l := l } =
      hm23Term1SourceExp a z0 z1
        { r := h - k, k := k, i := s + k, j := j, l := l } := by
  rw [hm23Term1SourceExp_phi_eq_term2SourceExp]
  ring_nf

theorem hm23GammaWindowFourFactorSum_eq_sigma
    (a z w₁ w₂ w₃ e : ℤ) :
    hm23GammaWindowFourFactorSum a z w₁ w₂ w₃ e =
      ∑ x ∈ hm23GammaWindowSigmaSet a z w₁ w₂ w₃ e,
        hm23GammaWindowSigmaSummand a z w₁ w₂ w₃ e x := by
  unfold hm23GammaWindowFourFactorSum hm23GammaWindowSigmaSet
    hm23GammaWindowSigmaSummand hm23GW_E hm23GW_E₁ hm23GW_E₂
    hm23GW_n₃ hm23GW_n₂ hm23GW_n₁ hm23GW_r hm23GW_k
  simp only [Finset.sum_sigma]
  simp only [Finset.sum_mul, Finset.mul_sum]
  ring_nf

theorem hm23GammaWindowSigmaToPsi1_injOn
    (a z w₁ w₂ w₃ e : ℤ) :
    Set.InjOn hm23GammaWindowSigmaToPsi1
      ↑((hm23GammaWindowSigmaSet a z w₁ w₂ w₃ e).filter
        (fun x =>
          hm23GW_E x - appellNumeratorExp z (hm23GW_r x) =
              appellDenomExp a z (hm23GW_r x) * hm23GW_k x ∧
            jExp w₁ 90 (hm23GW_n₁ x) = hm23GW_E₁ x ∧
            jExp w₂ 90 (hm23GW_n₂ x) = hm23GW_E₂ x ∧
            jExp w₃ 90 (hm23GW_n₃ x) =
              e - hm23GW_E x - hm23GW_E₁ x - hm23GW_E₂ x)) := by
  intro x hx y hy hxy
  have hx' := (by simpa [Finset.mem_filter] using hx :
    x ∈ hm23GammaWindowSigmaSet a z w₁ w₂ w₃ e ∧
      (hm23GW_E x - appellNumeratorExp z (hm23GW_r x) =
          appellDenomExp a z (hm23GW_r x) * hm23GW_k x ∧
        jExp w₁ 90 (hm23GW_n₁ x) = hm23GW_E₁ x ∧
        jExp w₂ 90 (hm23GW_n₂ x) = hm23GW_E₂ x ∧
        jExp w₃ 90 (hm23GW_n₃ x) =
          e - hm23GW_E x - hm23GW_E₁ x - hm23GW_E₂ x))
  have hy' := (by simpa [Finset.mem_filter] using hy :
    y ∈ hm23GammaWindowSigmaSet a z w₁ w₂ w₃ e ∧
      (hm23GW_E y - appellNumeratorExp z (hm23GW_r y) =
          appellDenomExp a z (hm23GW_r y) * hm23GW_k y ∧
        jExp w₁ 90 (hm23GW_n₁ y) = hm23GW_E₁ y ∧
        jExp w₂ 90 (hm23GW_n₂ y) = hm23GW_E₂ y ∧
        jExp w₃ 90 (hm23GW_n₃ y) =
          e - hm23GW_E y - hm23GW_E₁ y - hm23GW_E₂ y))
  rcases hx' with ⟨_hxmem, happx, h1x, h2x, _h3x⟩
  rcases hy' with ⟨_hymem, happy, h1y, h2y, _h3y⟩
  simp only [hm23GammaWindowSigmaToPsi1, hm23GW_r, hm23GW_k, hm23GW_n₁,
    hm23GW_n₂, hm23GW_n₃] at hxy
  injection hxy with hr hk hi hj hl
  rcases x with ⟨E, E₁, E₂, n₃, n₂, n₁, r, k⟩
  rcases y with ⟨F, F₁, F₂, m₃, m₂, m₁, s, l⟩
  simp only [hm23GW_E, hm23GW_E₁, hm23GW_E₂, hm23GW_n₂,
    hm23GW_n₁, hm23GW_r, hm23GW_k] at happx h1x h2x happy h1y h2y hr hk hi hj hl ⊢
  subst s
  subst l
  subst m₁
  subst m₂
  subst m₃
  have hE : E = F := by omega
  subst F
  have hE₁ : E₁ = F₁ := by omega
  subst F₁
  have hE₂ : E₂ = F₂ := by omega
  subst F₂
  rw [h1x, h2x]

theorem hm23GammaWindowSigmaToPsi0_injOn
    (a z w₁ w₂ w₃ e : ℤ) :
    Set.InjOn hm23GammaWindowSigmaToPsi0
      ↑((hm23GammaWindowSigmaSet a z w₁ w₂ w₃ e).filter
        (fun x =>
          hm23GW_E x - appellNumeratorExp z (hm23GW_r x) =
              appellDenomExp a z (hm23GW_r x) * hm23GW_k x ∧
            jExp w₁ 90 (hm23GW_n₁ x) = hm23GW_E₁ x ∧
            jExp w₂ 90 (hm23GW_n₂ x) = hm23GW_E₂ x ∧
            jExp w₃ 90 (hm23GW_n₃ x) =
              e - hm23GW_E x - hm23GW_E₁ x - hm23GW_E₂ x)) := by
  intro x hx y hy hxy
  have hx' := (by simpa [Finset.mem_filter] using hx :
    x ∈ hm23GammaWindowSigmaSet a z w₁ w₂ w₃ e ∧
      (hm23GW_E x - appellNumeratorExp z (hm23GW_r x) =
          appellDenomExp a z (hm23GW_r x) * hm23GW_k x ∧
        jExp w₁ 90 (hm23GW_n₁ x) = hm23GW_E₁ x ∧
        jExp w₂ 90 (hm23GW_n₂ x) = hm23GW_E₂ x ∧
        jExp w₃ 90 (hm23GW_n₃ x) =
          e - hm23GW_E x - hm23GW_E₁ x - hm23GW_E₂ x))
  have hy' := (by simpa [Finset.mem_filter] using hy :
    y ∈ hm23GammaWindowSigmaSet a z w₁ w₂ w₃ e ∧
      (hm23GW_E y - appellNumeratorExp z (hm23GW_r y) =
          appellDenomExp a z (hm23GW_r y) * hm23GW_k y ∧
        jExp w₁ 90 (hm23GW_n₁ y) = hm23GW_E₁ y ∧
        jExp w₂ 90 (hm23GW_n₂ y) = hm23GW_E₂ y ∧
        jExp w₃ 90 (hm23GW_n₃ y) =
          e - hm23GW_E y - hm23GW_E₁ y - hm23GW_E₂ y))
  rcases hx' with ⟨_hxmem, happx, h1x, h2x, _h3x⟩
  rcases hy' with ⟨_hymem, happy, h1y, h2y, _h3y⟩
  simp only [hm23GammaWindowSigmaToPsi0, hm23GW_r, hm23GW_k, hm23GW_n₁,
    hm23GW_n₂, hm23GW_n₃] at hxy
  injection hxy with hr hk hi hj hl
  rcases x with ⟨E, E₁, E₂, n₃, n₂, n₁, r, k⟩
  rcases y with ⟨F, F₁, F₂, m₃, m₂, m₁, s, l⟩
  simp only [hm23GW_E, hm23GW_E₁, hm23GW_E₂, hm23GW_n₂,
    hm23GW_n₁, hm23GW_r, hm23GW_k] at happx h1x h2x happy h1y h2y hr hk hi hj hl ⊢
  subst s
  subst l
  subst m₁
  subst m₂
  subst m₃
  have hE : E = F := by omega
  subst F
  have hE₁ : E₁ = F₁ := by omega
  subst F₁
  have hE₂ : E₂ = F₂ := by omega
  subst F₂
  rw [h1x, h2x]

theorem hm23GammaWindowSigmaSummand_eq_term1Source
    (a z0 z1 e : ℤ) (x : HM23GammaWindowSigma) :
    hm23GammaWindowSigmaSummand a z1 z0 (a + z0) (a + z1) e x =
      if hm23GW_E x - appellNumeratorExp z1 (hm23GW_r x) =
              appellDenomExp a z1 (hm23GW_r x) * hm23GW_k x ∧
            jExp z0 90 (hm23GW_n₁ x) = hm23GW_E₁ x ∧
            jExp (a + z0) 90 (hm23GW_n₂ x) = hm23GW_E₂ x ∧
            jExp (a + z1) 90 (hm23GW_n₃ x) =
              e - hm23GW_E x - hm23GW_E₁ x - hm23GW_E₂ x then
        hm23Term1SourceSummand a z0 z1 e (hm23GammaWindowSigmaToPsi1 x)
      else 0 := by
  classical
  rcases x with ⟨E, E₁, E₂, l, j, i, r, k⟩
  simp only [hm23GW_E, hm23GW_E₁, hm23GW_E₂, hm23GW_n₃, hm23GW_n₂,
    hm23GW_n₁, hm23GW_r, hm23GW_k, hm23GammaWindowSigmaToPsi1,
    hm23GammaWindowSigmaSummand]
  by_cases happ : E - appellNumeratorExp z1 r = appellDenomExp a z1 r * k
  · by_cases h1 : jExp z0 90 i = E₁
    · by_cases h2 : jExp (a + z0) 90 j = E₂
      · by_cases h3 : jExp (a + z1) 90 l = e - E - E₁ - E₂
        · have hexp :
              hm23Term1SourceExp a z0 z1
                  { r := r, k := k, i := i, j := j, l := l } = e := by
            rw [hm23Term1SourceExp_eq_window_parts]
            omega
          have hsign :
              negOnePowIntQ (r + i + j + l) =
                ((negOnePowIntQ r * negOnePowIntQ i) * negOnePowIntQ j) *
                  negOnePowIntQ l := by
            rw [show r + i + j + l = ((r + i) + j) + l by ring]
            rw [negOnePowIntQ_add, negOnePowIntQ_add, negOnePowIntQ_add]
          simp [happ, h1, h2, h3, hexp, hm23Term1SourceSummand, hsign,
            mul_comm, mul_left_comm]
        · simp [happ, h1, h2, h3]
      · simp [happ, h1, h2]
    · simp [happ, h1]
  · simp [happ]

theorem hm23GammaWindowSigmaSummand_eq_term2Source
    (a z0 z1 e : ℤ) (x : HM23GammaWindowSigma) :
    hm23GammaWindowSigmaSummand a z0 z1 (a + z0) (a + z1) e x =
      if hm23GW_E x - appellNumeratorExp z0 (hm23GW_r x) =
              appellDenomExp a z0 (hm23GW_r x) * hm23GW_k x ∧
            jExp z1 90 (hm23GW_n₁ x) = hm23GW_E₁ x ∧
            jExp (a + z0) 90 (hm23GW_n₂ x) = hm23GW_E₂ x ∧
            jExp (a + z1) 90 (hm23GW_n₃ x) =
              e - hm23GW_E x - hm23GW_E₁ x - hm23GW_E₂ x then
        hm23Term2SourceSummand a z0 z1 e (hm23GammaWindowSigmaToPsi0 x)
      else 0 := by
  classical
  rcases x with ⟨E, E₁, E₂, l, j, h, s, k⟩
  simp only [hm23GW_E, hm23GW_E₁, hm23GW_E₂, hm23GW_n₃, hm23GW_n₂,
    hm23GW_n₁, hm23GW_r, hm23GW_k, hm23GammaWindowSigmaToPsi0,
    hm23GammaWindowSigmaSummand]
  by_cases happ : E - appellNumeratorExp z0 s = appellDenomExp a z0 s * k
  · by_cases h1 : jExp z1 90 h = E₁
    · by_cases h2 : jExp (a + z0) 90 j = E₂
      · by_cases h3 : jExp (a + z1) 90 l = e - E - E₁ - E₂
        · have hexp :
              hm23Term2SourceExp a z0 z1
                  { s := s, k := k, h := h, j := j, l := l } = e := by
            rw [hm23Term2SourceExp_eq_window_parts]
            omega
          have hsign :
              negOnePowIntQ (s + h + j + l) =
                ((negOnePowIntQ s * negOnePowIntQ h) * negOnePowIntQ j) *
                  negOnePowIntQ l := by
            rw [show s + h + j + l = ((s + h) + j) + l by ring]
            rw [negOnePowIntQ_add, negOnePowIntQ_add, negOnePowIntQ_add]
          simp [happ, h1, h2, h3, hexp, hm23Term2SourceSummand, hsign,
            mul_comm, mul_left_comm]
        · simp [happ, h1, h2, h3]
      · simp [happ, h1, h2]
    · simp [happ, h1]
  · simp [happ]

def hm23Psi1WindowSourceSet (a z0 z1 e : ℤ) : Finset HM23Psi1Source := by
  classical
  exact
    ((hm23GammaWindowSigmaSet a z1 z0 (a + z0) (a + z1) e).filter
      (fun x =>
        hm23GW_E x - appellNumeratorExp z1 (hm23GW_r x) =
            appellDenomExp a z1 (hm23GW_r x) * hm23GW_k x ∧
          jExp z0 90 (hm23GW_n₁ x) = hm23GW_E₁ x ∧
          jExp (a + z0) 90 (hm23GW_n₂ x) = hm23GW_E₂ x ∧
          jExp (a + z1) 90 (hm23GW_n₃ x) =
            e - hm23GW_E x - hm23GW_E₁ x - hm23GW_E₂ x)).image
      hm23GammaWindowSigmaToPsi1

def hm23Psi0WindowSourceSet (a z0 z1 e : ℤ) : Finset HM23Psi0Source := by
  classical
  exact
    ((hm23GammaWindowSigmaSet a z0 z1 (a + z0) (a + z1) e).filter
      (fun x =>
        hm23GW_E x - appellNumeratorExp z0 (hm23GW_r x) =
            appellDenomExp a z0 (hm23GW_r x) * hm23GW_k x ∧
          jExp z1 90 (hm23GW_n₁ x) = hm23GW_E₁ x ∧
          jExp (a + z0) 90 (hm23GW_n₂ x) = hm23GW_E₂ x ∧
          jExp (a + z1) 90 (hm23GW_n₃ x) =
            e - hm23GW_E x - hm23GW_E₁ x - hm23GW_E₂ x)).image
      hm23GammaWindowSigmaToPsi0

theorem hm23Psi1_phi_mem_Psi0WindowSourceSet_of_Gamma_ne_zero
    (a z0 z1 e E E₁ E₂ l j i r k : ℤ)
    (hreg : hm23Nonsingular a z0 z1)
    (happ :
      E - appellNumeratorExp z1 r = appellDenomExp a z1 r * k)
    (h1 : jExp z0 90 i = E₁)
    (h2 : jExp (a + z0) 90 j = E₂)
    (h3 : jExp (a + z1) 90 l = e - E - E₁ - E₂)
    (hGamma0 : hm23Gamma (appellDenomExp a z0 (i - k)) k ≠ 0) :
    ({ s := i - k, k := k, h := r + k, j := j, l := l } :
      HM23Psi0Source) ∈ hm23Psi0WindowSourceSet a z0 z1 e := by
  classical
  let E₀' : ℤ :=
    appellNumeratorExp z0 (i - k) + appellDenomExp a z0 (i - k) * k
  let E₁' : ℤ := jExp z1 90 (r + k)
  have hD0 : appellDenomExp a z0 (i - k) ≠ 0 :=
    hm23Nonsingular_appellDenomExp_z0_ne_zero
      (a := a) (z0 := z0) (z1 := z1) (r := i - k) hreg
  have hterm1 :
      hm23Term1SourceExp a z0 z1
          { r := r, k := k, i := i, j := j, l := l } = e := by
    rw [hm23Term1SourceExp_eq_window_parts]
    omega
  have hterm2 :
      hm23Term2SourceExp a z0 z1
          { s := i - k, k := k, h := r + k, j := j, l := l } = e := by
    rw [← hm23Term1SourceExp_phi_eq_term2SourceExp]
    exact hterm1
  have hparts2 :
      E₀' + E₁' + E₂ + jExp (a + z1) 90 l = e := by
    have h := hterm2
    rw [hm23Term2SourceExp_eq_window_parts] at h
    rw [h2] at h
    simpa [E₀', E₁'] using h
  have h3' : jExp (a + z1) 90 l = e - E₀' - E₁' - E₂ := by
    omega
  have hE₀lower :
      appellNumeratorCoeffLower a z0 ≤ E₀' := by
    exact
      appellNumeratorCoeffLower_le_exp_add_denom_mul_of_Gamma_ne_zero
        a z0 (i - k) k E₀' (by dsimp [E₀']) hD0 hGamma0
  have hE₁lower : jCoeffLower z1 90 ≤ E₁' := by
    dsimp [E₁']
    exact jExp_lower_bound z1 90 (r + k) (by norm_num)
  have hE₂lower : jCoeffLower (a + z0) 90 ≤ E₂ := by
    rw [← h2]
    exact jExp_lower_bound (a + z0) 90 j (by norm_num)
  have hE₃lower :
      jCoeffLower (a + z1) 90 ≤ e - E₀' - E₁' - E₂ := by
    rw [← h3']
    exact jExp_lower_bound (a + z1) 90 l (by norm_num)
  have hE₀upper :
      E₀' ≤ e - (jCoeffLower z1 90 +
        (jCoeffLower (a + z0) 90 + jCoeffLower (a + z1) 90)) := by
    omega
  have hE₁upper :
      E₁' ≤ e - E₀' -
        (jCoeffLower (a + z0) 90 + jCoeffLower (a + z1) 90) := by
    omega
  have hE₂upper :
      E₂ ≤ e - E₀' - E₁' - jCoeffLower (a + z1) 90 := by
    omega
  have hlwin :
      -jCoeffWindow (a + z1) 90 (e - E₀' - E₁' - E₂) ≤ l ∧
        l ≤ jCoeffWindow (a + z1) 90 (e - E₀' - E₁' - E₂) := by
    constructor
    · exact jExp_root_le_window_left (a + z1) 90
        (e - E₀' - E₁' - E₂) l (by norm_num) h3'
    · exact jExp_root_le_window_right (a + z1) 90
        (e - E₀' - E₁' - E₂) l (by norm_num) h3'
  have hjwin :
      -jCoeffWindow (a + z0) 90 E₂ ≤ j ∧
        j ≤ jCoeffWindow (a + z0) 90 E₂ := by
    constructor
    · exact jExp_root_le_window_left (a + z0) 90 E₂ j
        (by norm_num) h2
    · exact jExp_root_le_window_right (a + z0) 90 E₂ j
        (by norm_num) h2
  have hhwin :
      -jCoeffWindow z1 90 E₁' ≤ r + k ∧
        r + k ≤ jCoeffWindow z1 90 E₁' := by
    constructor
    · exact jExp_root_le_window_left z1 90 E₁' (r + k)
        (by norm_num) (by dsimp [E₁'])
    · exact jExp_root_le_window_right z1 90 E₁' (r + k)
        (by norm_num) (by dsimp [E₁'])
  have hswin_mem :
      i - k ∈ Finset.Icc (-(appellNumeratorCoeffWindow a z0 E₀'))
          (appellNumeratorCoeffWindow a z0 E₀') :=
      appellNumeratorExp_add_denom_mul_mem_window_of_Gamma_ne_zero
        a z0 (i - k) k E₀' (by dsimp [E₀']) hD0 hGamma0
  have hswin :
      -appellNumeratorCoeffWindow a z0 E₀' ≤ i - k ∧
        i - k ≤ appellNumeratorCoeffWindow a z0 E₀' := by
    simpa [Finset.mem_Icc] using hswin_mem
  have hkdiv :
      (E₀' - appellNumeratorExp z0 (i - k)) /
          appellDenomExp a z0 (i - k) = k := by
    dsimp [E₀']
    rw [add_sub_cancel_left]
    exact Int.mul_ediv_cancel_left k hD0
  have hkwin :
      -(((E₀' - appellNumeratorExp z0 (i - k)) /
          appellDenomExp a z0 (i - k)).natAbs : ℤ) ≤ k ∧
        k ≤ (((E₀' - appellNumeratorExp z0 (i - k)) /
          appellDenomExp a z0 (i - k)).natAbs : ℤ) := by
    rw [hkdiv]
    constructor
    · have h : -k ≤ ((-k).natAbs : ℤ) := Int.le_natAbs
      rw [Int.natAbs_neg] at h
      omega
    · exact Int.le_natAbs
  unfold hm23Psi0WindowSourceSet
  refine Finset.mem_image.mpr ?_
  refine ⟨(⟨E₀', E₁', E₂, l, j, r + k, i - k, k⟩ :
    HM23GammaWindowSigma), ?_, rfl⟩
  rw [Finset.mem_filter]
  constructor
  · rw [hm23GammaWindowSigmaSet]
    simp only [Finset.mem_sigma, Finset.mem_Icc]
    exact ⟨⟨hE₀lower, hE₀upper⟩, ⟨hE₁lower, hE₁upper⟩,
      ⟨hE₂lower, hE₂upper⟩, hlwin, hjwin, hhwin, hswin, hkwin⟩
  · simp only [hm23GW_E, hm23GW_E₁, hm23GW_E₂, hm23GW_n₃,
      hm23GW_n₂, hm23GW_n₁, hm23GW_r, hm23GW_k]
    exact ⟨by dsimp [E₀']; ring, by dsimp [E₁'], h2, h3'⟩

theorem hm23Psi0_phi_mem_Psi1WindowSourceSet_of_Gamma_ne_zero
    (a z0 z1 e E E₁ E₂ l j h s k : ℤ)
    (hreg : hm23Nonsingular a z0 z1)
    (happ :
      E - appellNumeratorExp z0 s = appellDenomExp a z0 s * k)
    (h1 : jExp z1 90 h = E₁)
    (h2 : jExp (a + z0) 90 j = E₂)
    (h3 : jExp (a + z1) 90 l = e - E - E₁ - E₂)
    (hGamma1 : hm23Gamma (appellDenomExp a z1 (h - k)) k ≠ 0) :
    ({ r := h - k, k := k, i := s + k, j := j, l := l } :
      HM23Psi1Source) ∈ hm23Psi1WindowSourceSet a z0 z1 e := by
  classical
  let E' : ℤ :=
    appellNumeratorExp z1 (h - k) + appellDenomExp a z1 (h - k) * k
  let E₁' : ℤ := jExp z0 90 (s + k)
  have hD1 : appellDenomExp a z1 (h - k) ≠ 0 :=
    hm23Nonsingular_appellDenomExp_z1_ne_zero
      (a := a) (z0 := z0) (z1 := z1) (r := h - k) hreg
  have hterm2 :
      hm23Term2SourceExp a z0 z1
          { s := s, k := k, h := h, j := j, l := l } = e := by
    rw [hm23Term2SourceExp_eq_window_parts]
    omega
  have hterm1 :
      hm23Term1SourceExp a z0 z1
          { r := h - k, k := k, i := s + k, j := j, l := l } = e := by
    rw [← hm23Term2SourceExp_phi_eq_term1SourceExp]
    exact hterm2
  have hparts1 :
      E' + E₁' + E₂ + jExp (a + z1) 90 l = e := by
    have h := hterm1
    rw [hm23Term1SourceExp_eq_window_parts] at h
    rw [h2] at h
    simpa [E', E₁'] using h
  have h3' : jExp (a + z1) 90 l = e - E' - E₁' - E₂ := by
    omega
  have hElower :
      appellNumeratorCoeffLower a z1 ≤ E' := by
    exact
      appellNumeratorCoeffLower_le_exp_add_denom_mul_of_Gamma_ne_zero
        a z1 (h - k) k E' (by dsimp [E']) hD1 hGamma1
  have hE₁lower : jCoeffLower z0 90 ≤ E₁' := by
    dsimp [E₁']
    exact jExp_lower_bound z0 90 (s + k) (by norm_num)
  have hE₂lower : jCoeffLower (a + z0) 90 ≤ E₂ := by
    rw [← h2]
    exact jExp_lower_bound (a + z0) 90 j (by norm_num)
  have hE₃lower :
      jCoeffLower (a + z1) 90 ≤ e - E' - E₁' - E₂ := by
    rw [← h3']
    exact jExp_lower_bound (a + z1) 90 l (by norm_num)
  have hEupper :
      E' ≤ e - (jCoeffLower z0 90 +
        (jCoeffLower (a + z0) 90 + jCoeffLower (a + z1) 90)) := by
    omega
  have hE₁upper :
      E₁' ≤ e - E' -
        (jCoeffLower (a + z0) 90 + jCoeffLower (a + z1) 90) := by
    omega
  have hE₂upper :
      E₂ ≤ e - E' - E₁' - jCoeffLower (a + z1) 90 := by
    omega
  have hlwin :
      -jCoeffWindow (a + z1) 90 (e - E' - E₁' - E₂) ≤ l ∧
        l ≤ jCoeffWindow (a + z1) 90 (e - E' - E₁' - E₂) := by
    constructor
    · exact jExp_root_le_window_left (a + z1) 90
        (e - E' - E₁' - E₂) l (by norm_num) h3'
    · exact jExp_root_le_window_right (a + z1) 90
        (e - E' - E₁' - E₂) l (by norm_num) h3'
  have hjwin :
      -jCoeffWindow (a + z0) 90 E₂ ≤ j ∧
        j ≤ jCoeffWindow (a + z0) 90 E₂ := by
    constructor
    · exact jExp_root_le_window_left (a + z0) 90 E₂ j
        (by norm_num) h2
    · exact jExp_root_le_window_right (a + z0) 90 E₂ j
        (by norm_num) h2
  have hiwin :
      -jCoeffWindow z0 90 E₁' ≤ s + k ∧
        s + k ≤ jCoeffWindow z0 90 E₁' := by
    constructor
    · exact jExp_root_le_window_left z0 90 E₁' (s + k)
        (by norm_num) (by dsimp [E₁'])
    · exact jExp_root_le_window_right z0 90 E₁' (s + k)
        (by norm_num) (by dsimp [E₁'])
  have hrwin_mem :
      h - k ∈ Finset.Icc (-(appellNumeratorCoeffWindow a z1 E'))
          (appellNumeratorCoeffWindow a z1 E') :=
      appellNumeratorExp_add_denom_mul_mem_window_of_Gamma_ne_zero
        a z1 (h - k) k E' (by dsimp [E']) hD1 hGamma1
  have hrwin :
      -appellNumeratorCoeffWindow a z1 E' ≤ h - k ∧
        h - k ≤ appellNumeratorCoeffWindow a z1 E' := by
    simpa [Finset.mem_Icc] using hrwin_mem
  have hkdiv :
      (E' - appellNumeratorExp z1 (h - k)) /
          appellDenomExp a z1 (h - k) = k := by
    dsimp [E']
    rw [add_sub_cancel_left]
    exact Int.mul_ediv_cancel_left k hD1
  have hkwin :
      -(((E' - appellNumeratorExp z1 (h - k)) /
          appellDenomExp a z1 (h - k)).natAbs : ℤ) ≤ k ∧
        k ≤ (((E' - appellNumeratorExp z1 (h - k)) /
          appellDenomExp a z1 (h - k)).natAbs : ℤ) := by
    rw [hkdiv]
    constructor
    · have h : -k ≤ ((-k).natAbs : ℤ) := Int.le_natAbs
      rw [Int.natAbs_neg] at h
      omega
    · exact Int.le_natAbs
  unfold hm23Psi1WindowSourceSet
  refine Finset.mem_image.mpr ?_
  refine ⟨(⟨E', E₁', E₂, l, j, s + k, h - k, k⟩ :
    HM23GammaWindowSigma), ?_, rfl⟩
  rw [Finset.mem_filter]
  constructor
  · rw [hm23GammaWindowSigmaSet]
    simp only [Finset.mem_sigma, Finset.mem_Icc]
    exact ⟨⟨hElower, hEupper⟩, ⟨hE₁lower, hE₁upper⟩,
      ⟨hE₂lower, hE₂upper⟩, hlwin, hjwin, hiwin, hrwin, hkwin⟩
  · simp only [hm23GW_E, hm23GW_E₁, hm23GW_E₂, hm23GW_n₃,
      hm23GW_n₂, hm23GW_n₁, hm23GW_r, hm23GW_k]
    exact ⟨by dsimp [E']; ring, by dsimp [E₁'], h2, h3'⟩

theorem hm23GammaWindowFourFactorSum_eq_Psi1Source
    (a z0 z1 e : ℤ) :
    hm23GammaWindowFourFactorSum a z1 z0 (a + z0) (a + z1) e =
      ∑ x ∈ hm23Psi1WindowSourceSet a z0 z1 e,
        hm23Term1SourceSummand a z0 z1 e x := by
  rw [hm23GammaWindowFourFactorSum_eq_sigma]
  unfold hm23Psi1WindowSourceSet
  rw [Finset.sum_image]
  · calc
      (∑ x ∈ hm23GammaWindowSigmaSet a z1 z0 (a + z0) (a + z1) e,
          hm23GammaWindowSigmaSummand a z1 z0 (a + z0) (a + z1) e x)
          =
        ∑ x ∈ hm23GammaWindowSigmaSet a z1 z0 (a + z0) (a + z1) e,
          if hm23GW_E x - appellNumeratorExp z1 (hm23GW_r x) =
                  appellDenomExp a z1 (hm23GW_r x) * hm23GW_k x ∧
                jExp z0 90 (hm23GW_n₁ x) = hm23GW_E₁ x ∧
                jExp (a + z0) 90 (hm23GW_n₂ x) = hm23GW_E₂ x ∧
                jExp (a + z1) 90 (hm23GW_n₃ x) =
                  e - hm23GW_E x - hm23GW_E₁ x - hm23GW_E₂ x then
            hm23Term1SourceSummand a z0 z1 e
              (hm23GammaWindowSigmaToPsi1 x)
          else 0 := by
            refine Finset.sum_congr rfl ?_
            intro x _hx
            exact hm23GammaWindowSigmaSummand_eq_term1Source a z0 z1 e x
      _ =
        ∑ x ∈ (hm23GammaWindowSigmaSet a z1 z0 (a + z0) (a + z1) e).filter
            (fun x =>
              hm23GW_E x - appellNumeratorExp z1 (hm23GW_r x) =
                  appellDenomExp a z1 (hm23GW_r x) * hm23GW_k x ∧
                jExp z0 90 (hm23GW_n₁ x) = hm23GW_E₁ x ∧
                jExp (a + z0) 90 (hm23GW_n₂ x) = hm23GW_E₂ x ∧
                jExp (a + z1) 90 (hm23GW_n₃ x) =
                  e - hm23GW_E x - hm23GW_E₁ x - hm23GW_E₂ x),
          hm23Term1SourceSummand a z0 z1 e
            (hm23GammaWindowSigmaToPsi1 x) := by
            rw [Finset.sum_filter]
  · exact hm23GammaWindowSigmaToPsi1_injOn a z1 z0 (a + z0) (a + z1) e

theorem hm23GammaWindowFourFactorSum_eq_Psi0Source
    (a z0 z1 e : ℤ) :
    hm23GammaWindowFourFactorSum a z0 z1 (a + z0) (a + z1) e =
      ∑ x ∈ hm23Psi0WindowSourceSet a z0 z1 e,
        hm23Term2SourceSummand a z0 z1 e x := by
  rw [hm23GammaWindowFourFactorSum_eq_sigma]
  unfold hm23Psi0WindowSourceSet
  rw [Finset.sum_image]
  · calc
      (∑ x ∈ hm23GammaWindowSigmaSet a z0 z1 (a + z0) (a + z1) e,
          hm23GammaWindowSigmaSummand a z0 z1 (a + z0) (a + z1) e x)
          =
        ∑ x ∈ hm23GammaWindowSigmaSet a z0 z1 (a + z0) (a + z1) e,
          if hm23GW_E x - appellNumeratorExp z0 (hm23GW_r x) =
                  appellDenomExp a z0 (hm23GW_r x) * hm23GW_k x ∧
                jExp z1 90 (hm23GW_n₁ x) = hm23GW_E₁ x ∧
                jExp (a + z0) 90 (hm23GW_n₂ x) = hm23GW_E₂ x ∧
                jExp (a + z1) 90 (hm23GW_n₃ x) =
                  e - hm23GW_E x - hm23GW_E₁ x - hm23GW_E₂ x then
            hm23Term2SourceSummand a z0 z1 e
              (hm23GammaWindowSigmaToPsi0 x)
          else 0 := by
            refine Finset.sum_congr rfl ?_
            intro x _hx
            exact hm23GammaWindowSigmaSummand_eq_term2Source a z0 z1 e x
      _ =
        ∑ x ∈ (hm23GammaWindowSigmaSet a z0 z1 (a + z0) (a + z1) e).filter
            (fun x =>
              hm23GW_E x - appellNumeratorExp z0 (hm23GW_r x) =
                  appellDenomExp a z0 (hm23GW_r x) * hm23GW_k x ∧
                jExp z1 90 (hm23GW_n₁ x) = hm23GW_E₁ x ∧
                jExp (a + z0) 90 (hm23GW_n₂ x) = hm23GW_E₂ x ∧
                jExp (a + z1) 90 (hm23GW_n₃ x) =
                  e - hm23GW_E x - hm23GW_E₁ x - hm23GW_E₂ x),
          hm23Term2SourceSummand a z0 z1 e
            (hm23GammaWindowSigmaToPsi0 x) := by
            rw [Finset.sum_filter]
  · exact hm23GammaWindowSigmaToPsi0_injOn a z0 z1 (a + z0) (a + z1) e

def hm23Term1CoordSummand (a z0 z1 e : ℤ) (x : HM23Coord) : ℚ :=
  if hm23TermOutExp a z0 z1 x.m x.p x.z x.N = e ∧
      x.N = hm23Ncoord x.m x.p x.z x.r x.k then
    negOnePowIntQ (x.m + x.p) *
      negOnePowIntQ (x.z + x.p - x.m + 1 - x.k) *
        hm23Gamma (appellDenomExp a z1 x.r) x.k
  else 0

def hm23Term2CoordSummand (a z0 z1 e : ℤ) (x : HM23Coord) : ℚ :=
  if hm23TermOutExp a z0 z1 x.m x.p x.z x.N = e ∧
      x.N = hm23Ncoord x.m x.p x.z x.r x.k then
    negOnePowIntQ (x.m + x.p) *
      negOnePowIntQ (x.z + x.p - x.m + 1 - x.k) *
        hm23Gamma (appellDenomExp a z0 (x.z + x.p - x.r + 1 - x.k)) x.k
  else 0

theorem hm23Term1_transport_core
    (a z0 z1 e : ℤ) (S : Finset HM23Psi1Source) :
    (∑ x ∈ S, hm23Term1SourceSummand a z0 z1 e x) =
      ∑ x ∈ S.image hm23Psi1Coord, hm23Term1CoordSummand a z0 z1 e x := by
  refine Finset.sum_bij' (fun x _hx => hm23Psi1Coord x)
    (fun y _hy => hm23Psi1SourceOfCoord y) ?to_mem ?from_mem ?left_inv
    ?right_inv ?term_eq
  · intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    simpa [hm23Psi1SourceOfCoord_left_inv x] using hx
  · intro x hx
    exact hm23Psi1SourceOfCoord_left_inv x
  · intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    simp [hm23Psi1SourceOfCoord_left_inv x]
  · intro x hx
    have hExp := hm23Psi1_exponent_identity a z0 z1 x.r x.k x.i x.j x.l
    have hN := hm23Psi1_N_eq_Ncoord x.r x.k x.i x.j x.l
    have hSign := hm23Psi1_sign_identity x.r x.k x.i x.j x.l
    have hRes := hm23Psi1_residual_sign_coord x.r x.k x.i x.j x.l
    by_cases heq : hm23Term1SourceExp a z0 z1 x = e
    · have hout :
        hm23TermOutExp a z0 z1 (hm23Psi1Coord x).m (hm23Psi1Coord x).p
            (hm23Psi1Coord x).z (hm23Psi1Coord x).N = e := by
          unfold hm23Term1SourceExp at heq
          unfold hm23TermOutExp hm23Psi1Coord
          exact hExp ▸ heq
      have houtN :
        hm23TermOutExp a z0 z1 (hm23Psi1_m x.r x.j)
            (hm23Psi1_p x.j x.l x.k) (hm23Psi1_z x.r x.i x.j x.l x.k)
            (hm23Ncoord (hm23Psi1_m x.r x.j) (hm23Psi1_p x.j x.l x.k)
              (hm23Psi1_z x.r x.i x.j x.l x.k) x.r x.k) = e := by
        simpa [hm23Psi1Coord, hN] using hout
      simp [hm23Term1SourceSummand, hm23Term1CoordSummand, hm23Psi1Coord,
        heq, houtN, hN, hSign, hRes, mul_assoc]
    · have hout :
        hm23TermOutExp a z0 z1 (hm23Psi1Coord x).m (hm23Psi1Coord x).p
            (hm23Psi1Coord x).z (hm23Psi1Coord x).N ≠ e := by
          intro h
          apply heq
          unfold hm23Term1SourceExp
          unfold hm23TermOutExp hm23Psi1Coord at h
          exact hExp.symm ▸ h
      have houtN :
        hm23TermOutExp a z0 z1 (hm23Psi1_m x.r x.j)
            (hm23Psi1_p x.j x.l x.k) (hm23Psi1_z x.r x.i x.j x.l x.k)
            (hm23Ncoord (hm23Psi1_m x.r x.j) (hm23Psi1_p x.j x.l x.k)
              (hm23Psi1_z x.r x.i x.j x.l x.k) x.r x.k) ≠ e := by
        intro h
        apply hout
        simpa [hm23Psi1Coord, hN] using h
      simp [hm23Term1SourceSummand, hm23Term1CoordSummand, hm23Psi1Coord,
        heq, houtN, hN]

theorem hm23Term2_transport_core
    (a z0 z1 e : ℤ) (S : Finset HM23Psi0Source) :
    (∑ x ∈ S, hm23Term2SourceSummand a z0 z1 e x) =
      ∑ x ∈ S.image hm23Psi0Coord, hm23Term2CoordSummand a z0 z1 e x := by
  refine Finset.sum_bij' (fun x _hx => hm23Psi0Coord x)
    (fun y _hy => hm23Psi0SourceOfCoord y) ?to_mem ?from_mem ?left_inv
    ?right_inv ?term_eq
  · intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    simpa [hm23Psi0SourceOfCoord_left_inv x] using hx
  · intro x hx
    exact hm23Psi0SourceOfCoord_left_inv x
  · intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    simp [hm23Psi0SourceOfCoord_left_inv x]
  · intro x hx
    have hExp := hm23Psi0_exponent_identity a z0 z1 x.s x.k x.h x.j x.l
    have hN := hm23Psi0_N_eq_Ncoord x.s x.k x.h x.j x.l
    have hSign := hm23Psi0_sign_identity x.s x.k x.h x.j x.l
    have hRes := hm23Psi0_residual_sign_coord x.s x.k x.h x.j x.l
    have hD := hm23Psi0_D_coord a z0 x.s x.k x.h x.j x.l
    by_cases heq : hm23Term2SourceExp a z0 z1 x = e
    · have hout :
        hm23TermOutExp a z0 z1 (hm23Psi0Coord x).m (hm23Psi0Coord x).p
            (hm23Psi0Coord x).z (hm23Psi0Coord x).N = e := by
          unfold hm23Term2SourceExp at heq
          unfold hm23TermOutExp hm23Psi0Coord
          exact hExp ▸ heq
      have houtN :
        hm23TermOutExp a z0 z1 (hm23Psi0_m x.h x.j x.k)
            (hm23Psi0_p x.j x.l x.k) (hm23Psi0_z x.s x.h x.j x.l x.k)
            (hm23Ncoord (hm23Psi0_m x.h x.j x.k) (hm23Psi0_p x.j x.l x.k)
              (hm23Psi0_z x.s x.h x.j x.l x.k) (hm23Psi0_r x.h x.k) x.k) = e := by
        simpa [hm23Psi0Coord, hN] using hout
      simp [hm23Term2SourceSummand, hm23Term2CoordSummand, hm23Psi0Coord,
        hm23Psi0_inverse_s, heq, houtN, hN, hSign, hRes, hD, mul_assoc]
    · have hout :
        hm23TermOutExp a z0 z1 (hm23Psi0Coord x).m (hm23Psi0Coord x).p
            (hm23Psi0Coord x).z (hm23Psi0Coord x).N ≠ e := by
          intro h
          apply heq
          unfold hm23Term2SourceExp
          unfold hm23TermOutExp hm23Psi0Coord at h
          exact hExp.symm ▸ h
      have houtN :
        hm23TermOutExp a z0 z1 (hm23Psi0_m x.h x.j x.k)
            (hm23Psi0_p x.j x.l x.k) (hm23Psi0_z x.s x.h x.j x.l x.k)
            (hm23Ncoord (hm23Psi0_m x.h x.j x.k) (hm23Psi0_p x.j x.l x.k)
              (hm23Psi0_z x.s x.h x.j x.l x.k) (hm23Psi0_r x.h x.k) x.k) ≠ e := by
        intro h
        apply hout
        simpa [hm23Psi0Coord, hN] using h
      simp [hm23Term2SourceSummand, hm23Term2CoordSummand, hm23Psi0Coord,
        heq, houtN, hN]

theorem hm23_continuous_expand
    (R : Type*) [CommRing R] [TopologicalSpace R]
    (s : ℕ) (hs : s ≠ 0) :
    Continuous (PowerSeries.expand s hs : R⟦X⟧ → R⟦X⟧) := by
  rw [continuous_iff_continuousAt]
  intro φ
  rw [ContinuousAt, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  simp_rw [PowerSeries.coeff_expand s hs]
  by_cases h : s ∣ n
  · simpa [h] using
      (PowerSeries.WithPiTopology.continuous_coeff R (n / s)).tendsto φ
  · simpa [h] using (tendsto_const_nhds : Tendsto (fun _ : R⟦X⟧ => (0 : R)) (𝓝 φ) (𝓝 0))

theorem hm23_expand_qPochInfPS_eq_qPochAPPS_rat
    (s : ℕ) (hs : s ≠ 0) :
    PowerSeries.expand s hs (QseriesFormalization.PartIV.Ch19.qPochInfPS ℚ) =
      qPochAPPS ℚ s s := by
  rw [QseriesFormalization.PartIV.Ch19.qPochInfPS_eq_tprod ℚ]
  rw [(QseriesFormalization.PartIV.Ch19.multipliable_one_sub_X_pow_succ ℚ).map_tprod
    (PowerSeries.expand s hs) (hm23_continuous_expand ℚ s hs)]
  unfold qPochAPPS
  apply tprod_congr
  intro n
  calc
    PowerSeries.expand s hs ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (n + 1))
        = (1 : ℚ⟦X⟧) - PowerSeries.X ^ (s * (n + 1)) := by
          rw [map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]
    _ = apFactorPS ℚ s s n := by
          rw [apFactorPS]
          congr 1
          ring

theorem JOneLaurent_eq_expand_qPochInfPS :
    JOneLaurent =
      ((PowerSeries.expand 90 (by norm_num : (90 : ℕ) ≠ 0)
        (QseriesFormalization.PartIV.Ch19.qPochInfPS ℚ) : PowerSeries ℚ) : QLaurent) := by
  unfold JOneLaurent
  rw [jLaurent_90_270_eq_qPochAPLaurent_90_90]
  change ((qPochAPPS ℚ 90 90 : PowerSeries ℚ) : QLaurent) =
    ((PowerSeries.expand 90 (by norm_num : (90 : ℕ) ≠ 0)
      (QseriesFormalization.PartIV.Ch19.qPochInfPS ℚ) : PowerSeries ℚ) : QLaurent)
  rw [← hm23_expand_qPochInfPS_eq_qPochAPPS_rat 90
    (by norm_num : (90 : ℕ) ≠ 0)]

theorem lcoeff_JOneLaurent_pow_three_mul90 (N : ℕ) :
    lcoeff (JOneLaurent ^ 3) ((90 * N : ℕ) : ℤ) =
      (((QseriesFormalization.PartIV.Ch19.qPochInfPS ℚ) ^ 3).coeff N) := by
  rw [JOneLaurent_eq_expand_qPochInfPS]
  rw [← PowerSeries.coe_pow]
  rw [show (PowerSeries.expand 90 (by norm_num : (90 : ℕ) ≠ 0)
        (QseriesFormalization.PartIV.Ch19.qPochInfPS ℚ)) ^ 3 =
      PowerSeries.expand 90 (by norm_num : (90 : ℕ) ≠ 0)
        ((QseriesFormalization.PartIV.Ch19.qPochInfPS ℚ) ^ 3) by
        rw [map_pow]]
  rw [lcoeff, PowerSeries.coeff_coe]
  rw [PowerSeries.coeff_expand]
  have hnonneg : ¬ (90 * (N : ℤ) < 0) := by omega
  have hnatAbs : (90 * (N : ℤ)).natAbs = 90 * N := by
    have hcast : ((90 * (N : ℤ)).natAbs : ℤ) = 90 * (N : ℤ) := by
      exact Int.natAbs_of_nonneg (by omega)
    omega
  simp [hnonneg, hnatAbs]

theorem coeff_qPochInfPS_pow_three_rat_eq_intCast (N : ℕ) :
    (((QseriesFormalization.PartIV.Ch19.qPochInfPS ℚ) ^ 3).coeff N) =
      (((QseriesFormalization.PartIV.Ch19.qPochInfPS ℤ) ^ 3).coeff N : ℚ) := by
  have hmap :
      PowerSeries.map (Int.castRingHom ℚ)
          ((QseriesFormalization.PartIV.Ch19.qPochInfPS ℤ) ^ 3) =
        (QseriesFormalization.PartIV.Ch19.qPochInfPS ℚ) ^ 3 := by
    rw [map_pow]
    rw [QseriesFormalization.PartIV.Ch19.map_qPochInfPS (Int.castRingHom ℚ)]
  rw [← hmap, PowerSeries.coeff_map]
  rfl

theorem lcoeff_JOneLaurent_pow_three_of_not_dvd (e : ℤ)
    (he : ¬ (90 : ℤ) ∣ e) :
    lcoeff (JOneLaurent ^ 3) e = 0 := by
  rw [JOneLaurent_eq_expand_qPochInfPS]
  rw [← PowerSeries.coe_pow]
  rw [show (PowerSeries.expand 90 (by norm_num : (90 : ℕ) ≠ 0)
        (QseriesFormalization.PartIV.Ch19.qPochInfPS ℚ)) ^ 3 =
      PowerSeries.expand 90 (by norm_num : (90 : ℕ) ≠ 0)
        ((QseriesFormalization.PartIV.Ch19.qPochInfPS ℚ) ^ 3) by
        rw [map_pow]]
  rw [lcoeff, PowerSeries.coeff_coe]
  rw [PowerSeries.coeff_expand]
  by_cases hneg : e < 0
  · simp [hneg]
  · have hnat_dvd : ¬ (90 : ℕ) ∣ e.natAbs := by
      intro h
      apply he
      rcases h with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hcast_nonneg : ((e.natAbs : ℕ) : ℤ) = e := by
        exact Int.natAbs_of_nonneg (by omega)
      rw [← hcast_nonneg]
      exact_mod_cast hn
    simp [hneg, hnat_dvd]

/-- The cube `J^3` has nonnegative support: its Laurent coefficient vanishes at
every negative exponent.  (It is the `expand 90` of an ordinary power series.) -/
theorem lcoeff_JOneLaurent_pow_three_of_neg (e : ℤ) (he : e < 0) :
    lcoeff (JOneLaurent ^ 3) e = 0 := by
  rw [JOneLaurent_eq_expand_qPochInfPS]
  rw [← PowerSeries.coe_pow]
  rw [show (PowerSeries.expand 90 (by norm_num : (90 : ℕ) ≠ 0)
        (QseriesFormalization.PartIV.Ch19.qPochInfPS ℚ)) ^ 3 =
      PowerSeries.expand 90 (by norm_num : (90 : ℕ) ≠ 0)
        ((QseriesFormalization.PartIV.Ch19.qPochInfPS ℚ) ^ 3) by
        rw [map_pow]]
  rw [lcoeff, PowerSeries.coeff_coe]
  rw [PowerSeries.coeff_expand]
  simp [he]

theorem hm23_thetaMulPFRawCoeffPF_rat_eq_JOneCoeff_of_hPF
    (hPF :
      Chapter10PF.thetaMulPFSeriesCoeffPF =
        Chapter10PF.qPochInfPSCubeUPowerCoeffPF)
    (N : ℕ) (u : ℤ) :
    ((Chapter10PF.thetaMulPFRawCoeffPF N u : ℤ) : ℚ) =
      if u = 0 then
        lcoeff (JOneLaurent ^ 3) ((90 * N : ℕ) : ℤ)
      else 0 := by
  have hraw :=
    thetaMulPFRawCoeffPF_eq_qPochInfPSCubeUPowerCoeffPF_coeff_of_hPF hPF N u
  by_cases hu : u = 0
  · subst u
    rw [if_pos rfl]
    rw [hraw]
    simp only [Chapter10PF.qPochInfPSCubeUPowerCoeffPF, ↓reduceIte]
    change (((QseriesFormalization.PartIV.Ch19.qPochInfPS ℤ) ^ 3).coeff N : ℚ) =
      lcoeff (JOneLaurent ^ 3) (90 * (N : ℤ))
    rw [show 90 * (N : ℤ) = ((90 * N : ℕ) : ℤ) by norm_num]
    rw [lcoeff_JOneLaurent_pow_three_mul90,
      coeff_qPochInfPS_pow_three_rat_eq_intCast]
  · rw [if_neg hu]
    rw [hraw]
    simp [Chapter10PF.qPochInfPSCubeUPowerCoeffPF, hu]

/-- Integer-core cutoff summand for the HM 2.3 fiber telescope. -/
def hm23IntegerCoreSummand (N : ℕ) (z A B h K : ℤ) : ℤ :=
  if Chapter10PF.triIntPF (h - z) + K * z = (N : ℤ) then
    Chapter10PF.negOnePowIntPF ℤ (h - z) *
      ((if K ≤ h + A then (1 : ℤ) else 0) -
        (if K ≤ B then (1 : ℤ) else 0))
  else
    0

/-- Integer-indexed version of `hm23IntegerCoreSummand`.

This is used for the negative-`N` fibers that can occur after transporting the
finite HM source windows, before the PF projection restricts to natural
`q`-degrees. -/
def hm23IntegerCoreSummandInt (N z A B h K : ℤ) : ℤ :=
  if Chapter10PF.triIntPF (h - z) + K * z = N then
    Chapter10PF.negOnePowIntPF ℤ (h - z) *
      ((if K ≤ h + A then (1 : ℤ) else 0) -
        (if K ≤ B then (1 : ℤ) else 0))
  else
    0

theorem hm23IntegerCoreSummandInt_of_nat
    (N : ℕ) (z A B h K : ℤ) :
    hm23IntegerCoreSummandInt (N : ℤ) z A B h K =
      hm23IntegerCoreSummand N z A B h K := by
  rfl

theorem hm23IntegerCoreCanonical_pos_term_zero_of_neg
    {N z : ℤ} (hN : N < 0) (h k : ℕ) (hk : k < h + 1) :
    hm23IntegerCoreSummandInt N z 0 (-1) (h : ℤ) (k : ℤ) = 0 := by
  unfold hm23IntegerCoreSummandInt
  have hk_le : (k : ℤ) ≤ (h : ℤ) := by omega
  have hraw := Chapter10PF.thetaMulPFRawPositive_exponentPF h k z
  have hj_nonneg :
      0 ≤ Chapter10PF.jExpIntPF ((k : ℤ) + z - (h : ℤ)) := by
    unfold Chapter10PF.jExpIntPF
    exact Chapter10PF.triIntPF_nonneg (((k : ℤ) + z - (h : ℤ)) - 1)
  have hp_nonneg :
      0 ≤ Chapter10PF.pfNumExpIntPF (k : ℤ) := by
    unfold Chapter10PF.pfNumExpIntPF
    exact Chapter10PF.triIntPF_nonneg (k : ℤ)
  have hprod_nonneg : 0 ≤ (k : ℤ) * ((h : ℤ) - (k : ℤ)) := by
    nlinarith [Int.natCast_nonneg k, hk_le]
  have hexp_nonneg :
      0 ≤ Chapter10PF.triIntPF ((h : ℤ) - z) + (k : ℤ) * z := by
    rw [← hraw]
    nlinarith
  have hne :
      Chapter10PF.triIntPF ((h : ℤ) - z) + (k : ℤ) * z ≠ N := by
    omega
  rw [if_neg hne]

theorem hm23IntegerCoreCanonical_neg_term_zero_of_neg
    {N z : ℤ} (hN : N < 0) (h c : ℕ) (hc : c < h) :
    hm23IntegerCoreSummandInt N z 0 (-1) (-((h : ℤ) + 1))
        (-((c : ℤ) + 1)) = 0 := by
  unfold hm23IntegerCoreSummandInt
  have hraw := Chapter10PF.thetaMulPFRawNegative_exponentPF h c z
  have hj_nonneg :
      0 ≤ Chapter10PF.jExpIntPF ((h : ℤ) + z - (c : ℤ)) := by
    unfold Chapter10PF.jExpIntPF
    exact Chapter10PF.triIntPF_nonneg (((h : ℤ) + z - (c : ℤ)) - 1)
  have hp_nonneg :
      0 ≤ Chapter10PF.pfNumExpIntPF (-((c : ℤ) + 1)) := by
    unfold Chapter10PF.pfNumExpIntPF
    exact Chapter10PF.triIntPF_nonneg (-((c : ℤ) + 1))
  have hprod_nonneg :
      0 ≤ (-((c : ℤ) + 1)) * ((c : ℤ) - (h : ℤ)) := by
    have hc_le : (c : ℤ) + 1 ≤ (h : ℤ) := by omega
    nlinarith
  have hexp_nonneg :
      0 ≤ Chapter10PF.triIntPF ((h : ℤ) + z) - ((c : ℤ) + 1) * z := by
    rw [← hraw]
    nlinarith
  have harg :
      Chapter10PF.triIntPF (-((h : ℤ) + 1) - z) +
          (-((c : ℤ) + 1)) * z =
        Chapter10PF.triIntPF ((h : ℤ) + z) - ((c : ℤ) + 1) * z := by
    have hreflect :
        Chapter10PF.triIntPF (-((h : ℤ) + 1) - z) =
          Chapter10PF.triIntPF ((h : ℤ) + z) := by
      rw [show -((h : ℤ) + 1) - z = -(((h : ℤ) + z)) - 1 by ring]
      exact Chapter10PF.triIntPF_reflect ((h : ℤ) + z)
    rw [hreflect]
    ring
  have hne :
      Chapter10PF.triIntPF (-((h : ℤ) + 1) - z) +
          (-((c : ℤ) + 1)) * z ≠ N := by
    rw [harg]
    omega
  rw [if_neg hne]

/-- Canonical integer-core telescope with integer `N`.

For `N ≥ 0` this uses the same PF window as the natural-number version.  For
`N < 0` the concrete window value is immaterial for the vanishing theorem
below; the displayed finite sum keeps the positive and negative PF branches
explicit. -/
def hm23IntegerCoreCanonicalSumInt (N z : ℤ) : ℤ :=
  let W : ℕ :=
    if 0 ≤ N then
      Chapter10PF.thetaMulPFWindowPF N.toNat z
    else
      N.natAbs + z.natAbs + 2
  (∑ h ∈ Finset.range W,
      ∑ K ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
        hm23IntegerCoreSummandInt N z 0 (-1) (h : ℤ) K) +
    ∑ H ∈ Finset.range W,
      ∑ K ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
        hm23IntegerCoreSummandInt N z 0 (-1) (-((H : ℤ) + 1)) K

theorem hm23IntegerCoreCanonicalSumInt_eq_zero_of_neg
    {N z : ℤ} (hN : N < 0) :
    hm23IntegerCoreCanonicalSumInt N z = 0 := by
  classical
  unfold hm23IntegerCoreCanonicalSumInt
  have hnot : ¬ 0 ≤ N := by omega
  simp only [hnot, if_false]
  let W : ℕ := N.natAbs + z.natAbs + 2
  change
    (∑ h ∈ Finset.range W,
        ∑ K ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
          hm23IntegerCoreSummandInt N z 0 (-1) (h : ℤ) K) +
      (∑ H ∈ Finset.range W,
        ∑ K ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
          hm23IntegerCoreSummandInt N z 0 (-1) (-((H : ℤ) + 1)) K) = 0
  have hpos_zero :
      (∑ h ∈ Finset.range W,
        ∑ K ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
          hm23IntegerCoreSummandInt N z 0 (-1) (h : ℤ) K) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro h _hh
    refine Finset.sum_eq_zero ?_
    intro K _hK
    by_cases hK : 0 ≤ K ∧ K ≤ (h : ℤ)
    · have hKnat : ((K.toNat : ℕ) : ℤ) = K := Int.toNat_of_nonneg hK.1
      have hk_le_nat : K.toNat ≤ h := by
        exact_mod_cast (by simpa [hKnat] using hK.2)
      have hklt : K.toNat < h + 1 := Nat.lt_succ_of_le hk_le_nat
      have hterm :=
        hm23IntegerCoreCanonical_pos_term_zero_of_neg
          (N := N) (z := z) hN h K.toNat hklt
      simpa [hKnat] using hterm
    · have hval :
        ((if K ≤ (h : ℤ) + 0 then (1 : ℤ) else 0) -
          (if K ≤ -1 then (1 : ℤ) else 0)) = 0 := by
        by_cases hKh : K ≤ (h : ℤ)
        · have hnle : ¬ 0 ≤ K := by
            intro h0
            exact hK ⟨h0, hKh⟩
          have hKleNeg : K ≤ -1 := by omega
          simp [hKh, hKleNeg]
        · have hnotneg : ¬ K ≤ -1 := by omega
          simp [hKh, hnotneg]
      unfold hm23IntegerCoreSummandInt
      by_cases hc : Chapter10PF.triIntPF ((h : ℤ) - z) + K * z = N
      · rw [if_pos hc, hval, mul_zero]
      · rw [if_neg hc]
  have hneg_zero :
      (∑ H ∈ Finset.range W,
        ∑ K ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
          hm23IntegerCoreSummandInt N z 0 (-1) (-((H : ℤ) + 1)) K) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro H _hH
    refine Finset.sum_eq_zero ?_
    intro K _hK
    by_cases hK : -((H : ℤ) + 1) < K ∧ K ≤ -1
    · let c : ℕ := (-K - 1).toNat
      have hc_nonneg : 0 ≤ -K - 1 := by omega
      have hc_cast : ((c : ℕ) : ℤ) = -K - 1 := Int.toNat_of_nonneg hc_nonneg
      have hKc : -((c : ℤ) + 1) = K := by
        dsimp [c]
        rw [hc_cast]
        ring
      have hclt : c < H := by
        have hclt_int : (c : ℤ) < (H : ℤ) := by
          rw [hc_cast]
          omega
        exact_mod_cast hclt_int
      have hterm :=
        hm23IntegerCoreCanonical_neg_term_zero_of_neg
          (N := N) (z := z) hN H c hclt
      simpa [hKc] using hterm
    · have hval :
        ((if K ≤ -((H : ℤ) + 1) + 0 then (1 : ℤ) else 0) -
          (if K ≤ -1 then (1 : ℤ) else 0)) = 0 := by
        by_cases hKleH : K ≤ -((H : ℤ) + 1)
        · have hKleNeg : K ≤ -1 := by omega
          have hKleH' : K + (H : ℤ) ≤ -1 := by omega
          simp [hKleH', hKleNeg]
        · have hHltK : -((H : ℤ) + 1) < K := by omega
          have hnotNeg : ¬ K ≤ -1 := by
            intro hKneg
            exact hK ⟨hHltK, hKneg⟩
          have hnotH' : ¬ K + (H : ℤ) ≤ -1 := by omega
          simp [hnotH', hnotNeg]
      unfold hm23IntegerCoreSummandInt
      by_cases hc :
          Chapter10PF.triIntPF (-((H : ℤ) + 1) - z) + K * z = N
      · rw [if_pos hc, hval, mul_zero]
      · rw [if_neg hc]
  rw [hpos_zero, hneg_zero]
  norm_num

theorem hm23IntegerCoreCanonical_pos_inner
    (N W h : ℕ) (z : ℤ) (hh : h < W) :
    (∑ K ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
        hm23IntegerCoreSummand N z 0 (-1) (h : ℤ) K) =
      ∑ k ∈ Finset.range (h + 1),
        if Chapter10PF.triIntPF ((h : ℤ) - z) + (k : ℤ) * z = (N : ℤ) then
          Chapter10PF.negOnePowIntPF ℤ ((h : ℤ) - z)
        else
          0 := by
  classical
  let S : Finset ℤ :=
    (Finset.Icc (-(W : ℤ)) (W : ℤ)).filter
      (fun K => 0 ≤ K ∧ K ≤ (h : ℤ))
  have hsubset : S ⊆ Finset.Icc (-(W : ℤ)) (W : ℤ) := by
    intro K hK
    exact (Finset.mem_filter.mp hK).1
  have hsum_filter :
      (∑ K ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
          hm23IntegerCoreSummand N z 0 (-1) (h : ℤ) K) =
        ∑ K ∈ S, hm23IntegerCoreSummand N z 0 (-1) (h : ℤ) K := by
    symm
    refine Finset.sum_subset hsubset ?_
    intro K hK hKS
    rw [Finset.mem_filter] at hKS
    have hnot : ¬ (0 ≤ K ∧ K ≤ (h : ℤ)) := by
      simpa [hK] using hKS
    have hval :
        ((if K ≤ (h : ℤ) + 0 then (1 : ℤ) else 0) -
          (if K ≤ -1 then (1 : ℤ) else 0)) = 0 := by
      by_cases hKh : K ≤ (h : ℤ)
      · have hnle : ¬ 0 ≤ K := by
          intro h0
          exact hnot ⟨h0, hKh⟩
        have hKleNeg : K ≤ -1 := by omega
        simp [hKh, hKleNeg]
      · have hnotneg : ¬ K ≤ -1 := by omega
        simp [hKh, hnotneg]
    unfold hm23IntegerCoreSummand
    by_cases hc : Chapter10PF.triIntPF ((h : ℤ) - z) + K * z = (N : ℤ)
    · rw [if_pos hc, hval, mul_zero]
    · rw [if_neg hc]
  rw [hsum_filter]
  refine Finset.sum_bij'
    (fun K _ => K.toNat)
    (fun k _ => (k : ℤ)) ?to_mem ?from_mem ?left ?right ?term
  · intro K hK
    rw [Finset.mem_filter] at hK
    rw [Finset.mem_range]
    have h0 : 0 ≤ K := hK.2.1
    rw [Int.toNat_lt h0]
    omega
  · intro k hk
    rw [Finset.mem_range] at hk
    change (k : ℤ) ∈ S
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_Icc]
      constructor <;> omega
    · constructor <;> omega
  · intro K hK
    rw [Finset.mem_filter] at hK
    exact Int.toNat_of_nonneg hK.2.1
  · intro k hk
    rfl
  · intro K hK
    rw [Finset.mem_filter] at hK
    have h0 : 0 ≤ K := hK.2.1
    have hKh : K ≤ (h : ℤ) := hK.2.2
    have hKnot : ¬ K ≤ -1 := by omega
    unfold hm23IntegerCoreSummand
    by_cases hc : Chapter10PF.triIntPF ((h : ℤ) - z) + K * z = (N : ℤ)
    · simp [hc, hKh, hKnot, Int.toNat_of_nonneg h0]
    · simp [hc, Int.toNat_of_nonneg h0]

theorem hm23IntegerCoreCanonical_neg_inner
    (N W H : ℕ) (z : ℤ) (hH : H < W) :
    (∑ K ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
        hm23IntegerCoreSummand N z 0 (-1) (-((H : ℤ) + 1)) K) =
      ∑ c ∈ Finset.range H,
        if Chapter10PF.triIntPF ((H : ℤ) + z) - ((c : ℤ) + 1) * z =
            (N : ℤ) then
          Chapter10PF.negOnePowIntPF ℤ ((H : ℤ) + z)
        else
          0 := by
  classical
  let hInt : ℤ := -((H : ℤ) + 1)
  let S : Finset ℤ :=
    (Finset.Icc (-(W : ℤ)) (W : ℤ)).filter
      (fun K => hInt < K ∧ K ≤ -1)
  have hsubset : S ⊆ Finset.Icc (-(W : ℤ)) (W : ℤ) := by
    intro K hK
    exact (Finset.mem_filter.mp hK).1
  have hsum_filter :
      (∑ K ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
          hm23IntegerCoreSummand N z 0 (-1) hInt K) =
        ∑ K ∈ S, hm23IntegerCoreSummand N z 0 (-1) hInt K := by
    symm
    refine Finset.sum_subset hsubset ?_
    intro K hK hKS
    rw [Finset.mem_filter] at hKS
    have hnot : ¬ (hInt < K ∧ K ≤ -1) := by
      simpa [hK] using hKS
    have hval :
        ((if K ≤ hInt + 0 then (1 : ℤ) else 0) -
          (if K ≤ -1 then (1 : ℤ) else 0)) = 0 := by
      by_cases hKleH : K ≤ hInt
      · have hKleNeg : K ≤ -1 := by
          dsimp [hInt] at hKleH
          omega
        simp [hKleH, hKleNeg]
      · have hHltK : hInt < K := by omega
        have hnotNeg : ¬ K ≤ -1 := by
          intro hKneg
          exact hnot ⟨hHltK, hKneg⟩
        simp [hKleH, hnotNeg]
    unfold hm23IntegerCoreSummand
    by_cases hc : Chapter10PF.triIntPF (hInt - z) + K * z = (N : ℤ)
    · rw [if_pos hc, hval, mul_zero]
    · rw [if_neg hc]
  rw [hsum_filter]
  refine Finset.sum_bij'
    (fun K _ => (-K - 1).toNat)
    (fun c _ => -((c : ℤ) + 1)) ?to_mem ?from_mem ?left ?right ?term
  · intro K hK
    rw [Finset.mem_filter] at hK
    rw [Finset.mem_range]
    have hlow : hInt < K := hK.2.1
    have hhigh : K ≤ -1 := hK.2.2
    have hnonneg : 0 ≤ -K - 1 := by omega
    rw [Int.toNat_lt hnonneg]
    dsimp [hInt] at hlow
    omega
  · intro c hc
    rw [Finset.mem_range] at hc
    change -((c : ℤ) + 1) ∈ S
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_Icc]
      constructor <;> omega
    · constructor <;> dsimp [hInt] <;> omega
  · intro K hK
    rw [Finset.mem_filter] at hK
    have hnonneg : 0 ≤ -K - 1 := by omega
    have hto : (((-K - 1).toNat : ℕ) : ℤ) = -K - 1 :=
      Int.toNat_of_nonneg hnonneg
    change -(((-K - 1).toNat : ℤ) + 1) = K
    rw [hto]
    ring
  · intro c hc
    change ((-(-((c : ℤ) + 1)) - 1).toNat) = c
    have harg : -(-((c : ℤ) + 1)) - 1 = (c : ℤ) := by ring
    rw [harg]
    simp
  · intro K hKmem
    have hK := hKmem
    rw [Finset.mem_filter] at hK
    have hlow : hInt < K := hK.2.1
    have hhigh : K ≤ -1 := hK.2.2
    have hnonneg : 0 ≤ -K - 1 := by omega
    have himage :
        ((((fun K _ => (-K - 1).toNat) K hKmem : ℕ) : ℤ)) =
          -K - 1 :=
      Int.toNat_of_nonneg hnonneg
    have hKleH_false : ¬ K ≤ hInt := by omega
    have hKleNeg : K ≤ -1 := hhigh
    have harg : hInt - z = -(((H : ℤ) + z)) - 1 := by
      dsimp [hInt]
      ring
    have htri :
        Chapter10PF.triIntPF (hInt - z) =
          Chapter10PF.triIntPF ((H : ℤ) + z) := by
      rw [harg, Chapter10PF.triIntPF_reflect]
    have hsign :
        Chapter10PF.negOnePowIntPF ℤ (hInt - z) * (-1 : ℤ) =
          Chapter10PF.negOnePowIntPF ℤ ((H : ℤ) + z) := by
      rw [harg, Chapter10PF.negOnePowIntPF_reflect]
      ring
    have hifval :
        ((if K ≤ hInt + 0 then (1 : ℤ) else 0) -
          (if K ≤ -1 then (1 : ℤ) else 0)) = -1 := by
      simp [hKleH_false, hKleNeg]
    have hcond_iff :
        (Chapter10PF.triIntPF ((H : ℤ) + z) -
              ((((fun K _ => (-K - 1).toNat) K hKmem : ℕ) : ℤ) + 1) *
                z =
            (N : ℤ)) ↔
          (Chapter10PF.triIntPF (hInt - z) + K * z = (N : ℤ)) := by
      rw [himage, htri]
      constructor <;> intro h <;> linarith
    unfold hm23IntegerCoreSummand
    by_cases hc0 : Chapter10PF.triIntPF (hInt - z) + K * z = (N : ℤ)
    · have hc1 :
        Chapter10PF.triIntPF ((H : ℤ) + z) -
              ((((fun K _ => (-K - 1).toNat) K hKmem : ℕ) : ℤ) + 1) *
                z =
            (N : ℤ) := hcond_iff.mpr hc0
      rw [if_pos hc0, if_pos hc1, hifval, hsign]
    · have hc1 :
        ¬ Chapter10PF.triIntPF ((H : ℤ) + z) -
              ((((fun K _ => (-K - 1).toNat) K hKmem : ℕ) : ℤ) + 1) *
                z =
            (N : ℤ) := by
        intro hbad
        exact hc0 (hcond_iff.mp hbad)
      rw [if_neg hc0, if_neg hc1]

/-- Canonical integer-core telescope with cutoffs `A = 0`, `B = -1`. -/
def hm23IntegerCoreCanonicalSum (N : ℕ) (z : ℤ) : ℤ :=
  let W := Chapter10PF.thetaMulPFWindowPF N z
  (∑ h ∈ Finset.range W,
      ∑ K ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
        hm23IntegerCoreSummand N z 0 (-1) (h : ℤ) K) +
    ∑ H ∈ Finset.range W,
      ∑ K ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
        hm23IntegerCoreSummand N z 0 (-1) (-((H : ℤ) + 1)) K

theorem hm23IntegerCoreCanonicalSumInt_of_nat (N : ℕ) (z : ℤ) :
    hm23IntegerCoreCanonicalSumInt (N : ℤ) z =
      hm23IntegerCoreCanonicalSum N z := by
  unfold hm23IntegerCoreCanonicalSumInt hm23IntegerCoreCanonicalSum
  have hnonneg : 0 ≤ (N : ℤ) := Int.natCast_nonneg N
  have htoNat : Int.toNat (N : ℤ) = N := by simp
  simp [hnonneg, htoNat, hm23IntegerCoreSummandInt_of_nat]

/-- Integer-core fiber sum with explicit positive/negative `h` window and
integer `K` window.  The canonical sum is the case `A = 0`, `B = -1`, with
the minimal PF `K` window; arbitrary cutoff transport uses a larger `V`. -/
def hm23IntegerCoreFiberSumInt
    (W V : ℕ) (N z A B : ℤ) : ℤ :=
  (∑ h ∈ Finset.range W,
      ∑ K ∈ Finset.Icc (-(V : ℤ)) (V : ℤ),
        hm23IntegerCoreSummandInt N z A B (h : ℤ) K) +
    ∑ H ∈ Finset.range W,
      ∑ K ∈ Finset.Icc (-(V : ℤ)) (V : ℤ),
        hm23IntegerCoreSummandInt N z A B (-((H : ℤ) + 1)) K

theorem hm23_cutoff_indicator_succ (K t : ℤ) :
    ((if K ≤ t + 1 then (1 : ℤ) else 0) -
        (if K ≤ t then (1 : ℤ) else 0)) =
      if K = t + 1 then (1 : ℤ) else 0 := by
  by_cases h1 : K ≤ t + 1
  · by_cases h0 : K ≤ t
    · have hne : K ≠ t + 1 := by omega
      simp [h1, h0, hne]
    · have heq : K = t + 1 := by omega
      simp [heq]
  · have h0 : ¬ K ≤ t := by omega
    have hne : K ≠ t + 1 := by omega
    simp [h1, h0, hne]

theorem hm23_cutoff_indicator_succ_sub
    (K h A B : ℤ) :
    (((if K ≤ h + (A + 1) then (1 : ℤ) else 0) -
          (if K ≤ B then (1 : ℤ) else 0)) -
        ((if K ≤ h + A then (1 : ℤ) else 0) -
          (if K ≤ B then (1 : ℤ) else 0))) =
      if K = h + A + 1 then (1 : ℤ) else 0 := by
  rw [show h + (A + 1) = h + A + 1 by ring_nf]
  rw [sub_sub_sub_cancel_right]
  exact hm23_cutoff_indicator_succ K (h + A)

theorem hm23IntegerCoreSummandInt_A_succ_sub
    (N z A B h K : ℤ) :
    hm23IntegerCoreSummandInt N z (A + 1) B h K -
        hm23IntegerCoreSummandInt N z A B h K =
      if Chapter10PF.triIntPF (h - z) + K * z = N ∧
          K = h + A + 1 then
        Chapter10PF.negOnePowIntPF ℤ (h - z)
      else
        0 := by
  unfold hm23IntegerCoreSummandInt
  by_cases hc : Chapter10PF.triIntPF (h - z) + K * z = N
  · rw [if_pos hc, if_pos hc]
    rw [← mul_sub]
    rw [hm23_cutoff_indicator_succ_sub]
    by_cases hk : K = h + A + 1
    · subst K
      simp [hc]
    · simp [hc, hk]
  · rw [if_neg hc, if_neg hc]
    simp [hc]

theorem hm23IntegerCore_A_boundary_exponent_reflect
    (z A h : ℤ) :
    Chapter10PF.triIntPF (-(h + 1) - z) + (A - h) * z =
      Chapter10PF.triIntPF (h - z) + (h + A + 1) * z := by
  have htri :
      Chapter10PF.triIntPF (-(h + 1) - z) =
        Chapter10PF.triIntPF (h + z) := by
    rw [show -(h + 1) - z = -(h + z) - 1 by ring_nf]
    exact Chapter10PF.triIntPF_reflect (h + z)
  rw [htri]
  have hplus :
      Chapter10PF.triIntPF (h + z) * 2 =
        (h + z) * (h + z + 1) := by
    simpa [mul_comm] using Chapter10PF.two_mul_triIntPF (h + z)
  have hminus :
      Chapter10PF.triIntPF (h - z) * 2 =
        (h - z) * (h - z + 1) := by
    simpa [mul_comm] using Chapter10PF.two_mul_triIntPF (h - z)
  apply (mul_left_injective₀ (show (2 : ℤ) ≠ 0 by norm_num))
  ring_nf
  rw [hplus, hminus]
  ring_nf

theorem hm23IntegerCore_A_boundary_sign_reflect
    (z h : ℤ) :
    Chapter10PF.negOnePowIntPF ℤ (-(h + 1) - z) =
      -Chapter10PF.negOnePowIntPF ℤ (h - z) := by
  have hreflect :
      Chapter10PF.negOnePowIntPF ℤ (-(h + 1) - z) =
        -Chapter10PF.negOnePowIntPF ℤ (h + z) := by
    rw [show -(h + 1) - z = -(h + z) - 1 by ring_nf]
    exact Chapter10PF.negOnePowIntPF_reflect (h + z)
  have hpar :
      Chapter10PF.negOnePowIntPF ℤ (h + z) =
        Chapter10PF.negOnePowIntPF ℤ (h - z) := by
    apply Chapter10PF.negOnePowIntPF_eq_of_even_sub
    refine ⟨z, ?_⟩
    ring_nf
  rw [hreflect, hpar]

theorem hm23IntegerCoreFiberInner_A_succ_sub
    (V : ℕ) (N z A B h : ℤ)
    (hmem : h + A + 1 ∈ Finset.Icc (-(V : ℤ)) (V : ℤ)) :
    (∑ K ∈ Finset.Icc (-(V : ℤ)) (V : ℤ),
        hm23IntegerCoreSummandInt N z (A + 1) B h K) -
      (∑ K ∈ Finset.Icc (-(V : ℤ)) (V : ℤ),
        hm23IntegerCoreSummandInt N z A B h K) =
      if Chapter10PF.triIntPF (h - z) + (h + A + 1) * z = N then
        Chapter10PF.negOnePowIntPF ℤ (h - z)
      else
        0 := by
  classical
  let S : Finset ℤ := Finset.Icc (-(V : ℤ)) (V : ℤ)
  rw [← Finset.sum_sub_distrib]
  simp_rw [hm23IntegerCoreSummandInt_A_succ_sub]
  have hpoint :
      (∑ K ∈ S,
          if Chapter10PF.triIntPF (h - z) + K * z = N ∧
              K = h + A + 1 then
            Chapter10PF.negOnePowIntPF ℤ (h - z)
          else
            0) =
        ∑ K ∈ S,
          if K = h + A + 1 then
            if Chapter10PF.triIntPF (h - z) + (h + A + 1) * z = N then
              Chapter10PF.negOnePowIntPF ℤ (h - z)
            else
              0
          else
            0 := by
    refine Finset.sum_congr rfl ?_
    intro K _hK
    by_cases hK : K = h + A + 1
    · subst K
      simp
    · simp [hK]
  change
      (∑ K ∈ S,
          if Chapter10PF.triIntPF (h - z) + K * z = N ∧
              K = h + A + 1 then
            Chapter10PF.negOnePowIntPF ℤ (h - z)
          else
            0) =
        if Chapter10PF.triIntPF (h - z) + (h + A + 1) * z = N then
          Chapter10PF.negOnePowIntPF ℤ (h - z)
        else
          0
  rw [hpoint]
  rw [Finset.sum_ite_eq']
  simp [S, hmem]

theorem hm23IntegerCoreFiberInner_A_succ_pair
    (V : ℕ) (N z A B : ℤ) (h : ℕ)
    (hposmem :
      (h : ℤ) + A + 1 ∈ Finset.Icc (-(V : ℤ)) (V : ℤ))
    (hnegmem :
      A - (h : ℤ) ∈ Finset.Icc (-(V : ℤ)) (V : ℤ)) :
    ((∑ K ∈ Finset.Icc (-(V : ℤ)) (V : ℤ),
        hm23IntegerCoreSummandInt N z (A + 1) B (h : ℤ) K) +
      ∑ K ∈ Finset.Icc (-(V : ℤ)) (V : ℤ),
        hm23IntegerCoreSummandInt N z (A + 1) B
          (-((h : ℤ) + 1)) K) =
      ((∑ K ∈ Finset.Icc (-(V : ℤ)) (V : ℤ),
        hm23IntegerCoreSummandInt N z A B (h : ℤ) K) +
      ∑ K ∈ Finset.Icc (-(V : ℤ)) (V : ℤ),
        hm23IntegerCoreSummandInt N z A B
          (-((h : ℤ) + 1)) K) := by
  classical
  let S : Finset ℤ := Finset.Icc (-(V : ℤ)) (V : ℤ)
  let p₁ : ℤ :=
    ∑ K ∈ S, hm23IntegerCoreSummandInt N z (A + 1) B (h : ℤ) K
  let p₀ : ℤ :=
    ∑ K ∈ S, hm23IntegerCoreSummandInt N z A B (h : ℤ) K
  let n₁ : ℤ :=
    ∑ K ∈ S, hm23IntegerCoreSummandInt N z (A + 1) B
      (-((h : ℤ) + 1)) K
  let n₀ : ℤ :=
    ∑ K ∈ S, hm23IntegerCoreSummandInt N z A B
      (-((h : ℤ) + 1)) K
  have hp :
      p₁ - p₀ =
        if Chapter10PF.triIntPF ((h : ℤ) - z) +
            ((h : ℤ) + A + 1) * z = N then
          Chapter10PF.negOnePowIntPF ℤ ((h : ℤ) - z)
        else
          0 := by
    dsimp [p₁, p₀, S]
    exact hm23IntegerCoreFiberInner_A_succ_sub V N z A B (h : ℤ) hposmem
  have hn :
      n₁ - n₀ =
        if Chapter10PF.triIntPF (-((h : ℤ) + 1) - z) +
            (A - (h : ℤ)) * z = N then
          Chapter10PF.negOnePowIntPF ℤ (-((h : ℤ) + 1) - z)
        else
          0 := by
    dsimp [n₁, n₀, S]
    have harg : -((h : ℤ) + 1) + A + 1 = A - (h : ℤ) := by ring_nf
    have harg' : -1 + -(h : ℤ) + A + 1 = A - (h : ℤ) := by ring_nf
    have hnegmem' :
        -((h : ℤ) + 1) + A + 1 ∈
          Finset.Icc (-(V : ℤ)) (V : ℤ) := by
      rw [Finset.mem_Icc] at hnegmem ⊢
      constructor <;> omega
    simpa [harg, harg'] using
      hm23IntegerCoreFiberInner_A_succ_sub V N z A B
        (-((h : ℤ) + 1)) hnegmem'
  have hboundary :
      (if Chapter10PF.triIntPF ((h : ℤ) - z) +
            ((h : ℤ) + A + 1) * z = N then
          Chapter10PF.negOnePowIntPF ℤ ((h : ℤ) - z)
        else
          0) +
        (if Chapter10PF.triIntPF (-((h : ℤ) + 1) - z) +
              (A - (h : ℤ)) * z = N then
            Chapter10PF.negOnePowIntPF ℤ (-((h : ℤ) + 1) - z)
          else
            0) = 0 := by
    have hexp :=
      hm23IntegerCore_A_boundary_exponent_reflect z A (h : ℤ)
    have hsign :=
      hm23IntegerCore_A_boundary_sign_reflect z (h : ℤ)
    have hnegArg :
        -1 + -(h : ℤ) - z = -((h : ℤ) + 1) - z := by ring_nf
    by_cases hc :
        Chapter10PF.triIntPF ((h : ℤ) - z) +
            ((h : ℤ) + A + 1) * z = N
    · have hcneg :
          Chapter10PF.triIntPF (-((h : ℤ) + 1) - z) +
              (A - (h : ℤ)) * z = N := by
        rwa [hexp]
      simp [hc, hcneg, hsign, hnegArg]
    · have hcneg :
          ¬ Chapter10PF.triIntPF (-((h : ℤ) + 1) - z) +
              (A - (h : ℤ)) * z = N := by
        intro hbad
        apply hc
        rwa [hexp] at hbad
      simp [hc, hcneg, hnegArg]
  have hdiff : p₁ + n₁ - (p₀ + n₀) = 0 := by
    rw [show p₁ + n₁ - (p₀ + n₀) = (p₁ - p₀) + (n₁ - n₀) by ring_nf]
    rw [hp, hn]
    exact hboundary
  exact sub_eq_zero.mp hdiff

theorem hm23IntegerCoreFiberSumInt_A_succ
    (W V : ℕ) (N z A B : ℤ)
    (hV : ∀ h : ℕ, h < W →
      (h : ℤ) + A + 1 ∈ Finset.Icc (-(V : ℤ)) (V : ℤ) ∧
        A - (h : ℤ) ∈ Finset.Icc (-(V : ℤ)) (V : ℤ)) :
    hm23IntegerCoreFiberSumInt W V N z (A + 1) B =
      hm23IntegerCoreFiberSumInt W V N z A B := by
  classical
  unfold hm23IntegerCoreFiberSumInt
  repeat rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro h hh
  exact hm23IntegerCoreFiberInner_A_succ_pair V N z A B h
    (hV h (by simpa using hh)).1 (hV h (by simpa using hh)).2

/-- Boxed version of the same integer-core fiber sum, with `h` ranging over
`[-W,W-1]`.  This is convenient for cutoff moves whose involution is not the
positive/negative branch pairing used by the canonical PF window. -/
def hm23IntegerCoreFiberBoxSumInt
    (W V : ℕ) (N z A B : ℤ) : ℤ :=
  ∑ h ∈ Finset.Icc (-(W : ℤ)) ((W : ℤ) - 1),
    ∑ K ∈ Finset.Icc (-(V : ℤ)) (V : ℤ),
      hm23IntegerCoreSummandInt N z A B h K

theorem hm23_cutoff_indicator_B_succ_sub
    (K h A B : ℤ) :
    (((if K ≤ h + A then (1 : ℤ) else 0) -
          (if K ≤ B + 1 then (1 : ℤ) else 0)) -
        ((if K ≤ h + A then (1 : ℤ) else 0) -
          (if K ≤ B then (1 : ℤ) else 0))) =
      if K = B + 1 then (-1 : ℤ) else 0 := by
  rw [show
      ((if K ≤ h + A then (1 : ℤ) else 0) -
          (if K ≤ B + 1 then (1 : ℤ) else 0)) -
        ((if K ≤ h + A then (1 : ℤ) else 0) -
          (if K ≤ B then (1 : ℤ) else 0)) =
        -(((if K ≤ B + 1 then (1 : ℤ) else 0) -
          (if K ≤ B then (1 : ℤ) else 0))) by ring_nf]
  rw [hm23_cutoff_indicator_succ K B]
  by_cases hK : K = B + 1 <;> simp [hK]

theorem hm23IntegerCoreSummandInt_B_succ_sub
    (N z A B h K : ℤ) :
    hm23IntegerCoreSummandInt N z A (B + 1) h K -
        hm23IntegerCoreSummandInt N z A B h K =
      if Chapter10PF.triIntPF (h - z) + K * z = N ∧
          K = B + 1 then
        -Chapter10PF.negOnePowIntPF ℤ (h - z)
      else
        0 := by
  unfold hm23IntegerCoreSummandInt
  by_cases hc : Chapter10PF.triIntPF (h - z) + K * z = N
  · rw [if_pos hc, if_pos hc]
    rw [← mul_sub]
    rw [hm23_cutoff_indicator_B_succ_sub]
    by_cases hK : K = B + 1
    · subst K
      simp [hc]
    · simp [hc, hK]
  · rw [if_neg hc, if_neg hc]
    simp [hc]

theorem hm23IntegerCore_B_boundary_exponent_reflect
    (z B h : ℤ) :
    Chapter10PF.triIntPF ((2 * z - h - 1) - z) + (B + 1) * z =
      Chapter10PF.triIntPF (h - z) + (B + 1) * z := by
  have harg : (2 * z - h - 1) - z = -(h - z) - 1 := by ring_nf
  rw [harg, Chapter10PF.triIntPF_reflect]

theorem hm23IntegerCore_B_boundary_sign_reflect
    (z h : ℤ) :
    Chapter10PF.negOnePowIntPF ℤ ((2 * z - h - 1) - z) =
      -Chapter10PF.negOnePowIntPF ℤ (h - z) := by
  have harg : (2 * z - h - 1) - z = -(h - z) - 1 := by ring_nf
  rw [harg, Chapter10PF.negOnePowIntPF_reflect]

theorem hm23IntegerCoreFiberBoxInner_B_succ_sub
    (V : ℕ) (N z A B h : ℤ)
    (hmem : B + 1 ∈ Finset.Icc (-(V : ℤ)) (V : ℤ)) :
    (∑ K ∈ Finset.Icc (-(V : ℤ)) (V : ℤ),
        hm23IntegerCoreSummandInt N z A (B + 1) h K) -
      (∑ K ∈ Finset.Icc (-(V : ℤ)) (V : ℤ),
        hm23IntegerCoreSummandInt N z A B h K) =
      if Chapter10PF.triIntPF (h - z) + (B + 1) * z = N then
        -Chapter10PF.negOnePowIntPF ℤ (h - z)
      else
        0 := by
  classical
  let S : Finset ℤ := Finset.Icc (-(V : ℤ)) (V : ℤ)
  rw [← Finset.sum_sub_distrib]
  simp_rw [hm23IntegerCoreSummandInt_B_succ_sub]
  have hpoint :
      (∑ K ∈ S,
          if Chapter10PF.triIntPF (h - z) + K * z = N ∧
              K = B + 1 then
            -Chapter10PF.negOnePowIntPF ℤ (h - z)
          else
            0) =
        ∑ K ∈ S,
          if K = B + 1 then
            if Chapter10PF.triIntPF (h - z) + (B + 1) * z = N then
              -Chapter10PF.negOnePowIntPF ℤ (h - z)
            else
              0
          else
            0 := by
    refine Finset.sum_congr rfl ?_
    intro K _hK
    by_cases hK : K = B + 1
    · subst K
      simp
    · simp [hK]
  change
      (∑ K ∈ S,
          if Chapter10PF.triIntPF (h - z) + K * z = N ∧
              K = B + 1 then
            -Chapter10PF.negOnePowIntPF ℤ (h - z)
          else
            0) =
        if Chapter10PF.triIntPF (h - z) + (B + 1) * z = N then
          -Chapter10PF.negOnePowIntPF ℤ (h - z)
        else
          0
  rw [hpoint]
  rw [Finset.sum_ite_eq']
  simp [S, hmem]

theorem hm23IntegerCoreFiberBoxSumInt_B_succ
    (W V : ℕ) (N z A B : ℤ)
    (hK : B + 1 ∈ Finset.Icc (-(V : ℤ)) (V : ℤ))
    (hclosed : ∀ h : ℤ,
      h ∈ Finset.Icc (-(W : ℤ)) ((W : ℤ) - 1) →
      Chapter10PF.triIntPF (h - z) + (B + 1) * z = N →
        2 * z - h - 1 ∈ Finset.Icc (-(W : ℤ)) ((W : ℤ) - 1)) :
    hm23IntegerCoreFiberBoxSumInt W V N z A (B + 1) =
      hm23IntegerCoreFiberBoxSumInt W V N z A B := by
  classical
  let H : Finset ℤ := Finset.Icc (-(W : ℤ)) ((W : ℤ) - 1)
  let R : Finset ℤ :=
    H.filter (fun h =>
      Chapter10PF.triIntPF (h - z) + (B + 1) * z = N)
  let f : ℤ → ℤ := fun h =>
    -Chapter10PF.negOnePowIntPF ℤ (h - z)
  have hdiff :
      hm23IntegerCoreFiberBoxSumInt W V N z A (B + 1) -
          hm23IntegerCoreFiberBoxSumInt W V N z A B =
        ∑ h ∈ H,
          if Chapter10PF.triIntPF (h - z) + (B + 1) * z = N then
            f h
          else
            0 := by
    unfold hm23IntegerCoreFiberBoxSumInt
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro h _hh
    dsimp [f]
    exact hm23IntegerCoreFiberBoxInner_B_succ_sub V N z A B h hK
  have hfilter :
      (∑ h ∈ H,
          if Chapter10PF.triIntPF (h - z) + (B + 1) * z = N then
            f h
          else
            0) =
        ∑ h ∈ R, f h := by
    dsimp [R]
    rw [Finset.sum_filter]
  have hperm :
      (∑ h ∈ R, f h) = ∑ h ∈ R, f (2 * z - h - 1) := by
    refine Finset.sum_bij'
      (fun h _hh => 2 * z - h - 1)
      (fun h _hh => 2 * z - h - 1) ?to_mem ?from_mem ?left ?right ?term
    · intro h hh
      rw [Finset.mem_filter] at hh ⊢
      constructor
      · exact hclosed h hh.1 hh.2
      · rw [hm23IntegerCore_B_boundary_exponent_reflect z B h]
        exact hh.2
    · intro h hh
      rw [Finset.mem_filter] at hh ⊢
      constructor
      · exact hclosed h hh.1 hh.2
      · rw [hm23IntegerCore_B_boundary_exponent_reflect z B h]
        exact hh.2
    · intro h _hh
      ring_nf
    · intro h _hh
      ring_nf
    · intro h _hh
      rw [show 2 * z - (2 * z - h - 1) - 1 = h by ring_nf]
  have hneg :
      (∑ h ∈ R, f (2 * z - h - 1)) = -∑ h ∈ R, f h := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro h _hh
    dsimp [f]
    rw [hm23IntegerCore_B_boundary_sign_reflect z h]
  have hzero : (∑ h ∈ R, f h) = 0 := by
    have hdouble :
        (∑ h ∈ R, f h) + (∑ h ∈ R, f h) = 0 := by
      linarith [hperm, hneg]
    omega
  apply sub_eq_zero.mp
  rw [hdiff, hfilter, hzero]

/-- The positive/negative range decomposition of `Finset.Icc (-W) (W-1)`:
`∑_{h∈range W} g h + ∑_{H∈range W} g (-(H+1)) = ∑_{h∈Icc(-W,W-1)} g h`. -/
theorem hm23_sum_range_pos_neg_eq_sum_Icc {M : Type*} [AddCommMonoid M]
    (g : ℤ → M) (W : ℕ) :
    ((∑ h ∈ Finset.range W, g (h : ℤ)) +
        ∑ H ∈ Finset.range W, g (-((H : ℤ) + 1))) =
      ∑ h ∈ Finset.Icc (-(W : ℤ)) ((W : ℤ) - 1), g h := by
  classical
  have hsplit :
      Finset.Icc (-(W : ℤ)) ((W : ℤ) - 1) =
        Finset.Icc (0 : ℤ) ((W : ℤ) - 1) ∪ Finset.Icc (-(W : ℤ)) (-1) := by
    ext x
    rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]
    omega
  have hdisj :
      Disjoint (Finset.Icc (0 : ℤ) ((W : ℤ) - 1))
        (Finset.Icc (-(W : ℤ)) (-1)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Icc] at hx hx'
    omega
  have hpos :
      (∑ h ∈ Finset.range W, g (h : ℤ)) =
        ∑ x ∈ Finset.Icc (0 : ℤ) ((W : ℤ) - 1), g x := by
    refine Finset.sum_bij' (fun h _ => (h : ℤ))
      (fun n _ => n.toNat) ?_ ?_ ?_ ?_ ?_
    · intro h hh
      simp only [Finset.mem_range] at hh
      simp only [Finset.mem_Icc]; omega
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      simp only [Finset.mem_range]; omega
    · intro h _hh; simp
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      show ((n.toNat : ℤ)) = n
      rw [Int.toNat_of_nonneg hn.1]
    · intro h _hh; rfl
  have hneg :
      (∑ H ∈ Finset.range W, g (-((H : ℤ) + 1))) =
        ∑ x ∈ Finset.Icc (-(W : ℤ)) (-1), g x := by
    refine Finset.sum_bij' (fun H _ => -((H : ℤ) + 1))
      (fun n _ => (-n - 1).toNat) ?_ ?_ ?_ ?_ ?_
    · intro H hH
      simp only [Finset.mem_range] at hH
      simp only [Finset.mem_Icc]; omega
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      simp only [Finset.mem_range]; omega
    · intro H _hH
      show ((-(-((H : ℤ) + 1)) - 1).toNat) = H
      have heq : (-(-((H : ℤ) + 1)) - 1) = (H : ℤ) := by ring
      rw [heq]; simp
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      show -(((-n - 1).toNat : ℤ) + 1) = n
      rw [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ -n-1)]; ring
    · intro H _hH; rfl
  rw [hsplit, Finset.sum_union hdisj, hpos, hneg]

/-- The range-shaped integer-core fiber sum equals the boxed (`Icc`) one. -/
theorem hm23IntegerCoreFiberSumInt_eq_box
    (W V : ℕ) (N z A B : ℤ) :
    hm23IntegerCoreFiberSumInt W V N z A B =
      hm23IntegerCoreFiberBoxSumInt W V N z A B := by
  unfold hm23IntegerCoreFiberSumInt hm23IntegerCoreFiberBoxSumInt
  exact hm23_sum_range_pos_neg_eq_sum_Icc
    (fun h => ∑ K ∈ Finset.Icc (-(V : ℤ)) (V : ℤ),
      hm23IntegerCoreSummandInt N z A B h K) W

/-- The A-step window hypothesis, derived from one size bound `W + |A| + 1 ≤ V`. -/
theorem hm23_A_window_of_bound (W V : ℕ) (A : ℤ)
    (hbound : (W : ℤ) + |A| + 1 ≤ (V : ℤ)) :
    ∀ h : ℕ, h < W →
      (h : ℤ) + A + 1 ∈ Finset.Icc (-(V : ℤ)) (V : ℤ) ∧
        A - (h : ℤ) ∈ Finset.Icc (-(V : ℤ)) (V : ℤ) := by
  intro h hh
  have hhW : (h : ℤ) < (W : ℤ) := by exact_mod_cast hh
  have habs : -|A| ≤ A ∧ A ≤ |A| := ⟨neg_abs_le A, le_abs_self A⟩
  rw [Finset.mem_Icc, Finset.mem_Icc]
  refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-- Moving the upper `A`-cutoff to `0` leaves the integer-core fiber sum
unchanged, provided `V` is large enough for every intermediate cutoff. -/
theorem hm23IntegerCoreFiberSumInt_A_to_zero
    (W V : ℕ) (N z B A : ℤ)
    (hbound : (W : ℤ) + |A| + 1 ≤ (V : ℤ)) :
    hm23IntegerCoreFiberSumInt W V N z A B =
      hm23IntegerCoreFiberSumInt W V N z 0 B := by
  rcases le_or_gt 0 A with hA | hA
  · -- A ≥ 0 : descend from A to 0 (apply `_A_succ` at each lower value)
    have key : ∀ A' : ℤ, 0 ≤ A' → (W : ℤ) + A' + 1 ≤ (V : ℤ) →
        hm23IntegerCoreFiberSumInt W V N z A' B =
          hm23IntegerCoreFiberSumInt W V N z 0 B := by
      intro A' hA'
      induction A', hA' using Int.le_induction with
      | base => intro _; rfl
      | succ n hn ih =>
          intro hb
          have hstep :
              hm23IntegerCoreFiberSumInt W V N z (n + 1) B =
                hm23IntegerCoreFiberSumInt W V N z n B := by
            apply hm23IntegerCoreFiberSumInt_A_succ
            apply hm23_A_window_of_bound
            rw [abs_of_nonneg hn]; omega
          rw [hstep]
          exact ih (by omega)
    have hAbs : |A| = A := abs_of_nonneg hA
    rw [hAbs] at hbound
    exact key A hA hbound
  · -- A < 0 : ascend from A to 0 (apply `_A_succ` at each lower value)
    have key : ∀ A' : ℤ, A' ≤ 0 → (W : ℤ) + (-A') + 1 ≤ (V : ℤ) →
        hm23IntegerCoreFiberSumInt W V N z A' B =
          hm23IntegerCoreFiberSumInt W V N z 0 B := by
      intro A' hA'
      induction A', hA' using Int.le_induction_down with
      | base => intro _; rfl
      | pred n hn ih =>
          intro hb
          have hstep :
              hm23IntegerCoreFiberSumInt W V N z n B =
                hm23IntegerCoreFiberSumInt W V N z (n - 1) B := by
            have hh := hm23IntegerCoreFiberSumInt_A_succ W V N z (n - 1) B
              (by apply hm23_A_window_of_bound
                  rw [abs_of_nonpos (by omega : (n - 1 : ℤ) ≤ 0)]; omega)
            rw [show (n - 1) + 1 = n by ring] at hh
            exact hh
          rw [← hstep]
          exact ih (by omega)
    have hAbs : |A| = -A := abs_of_neg hA
    rw [hAbs] at hbound
    exact key A (le_of_lt hA) hbound

/-- The quadratic root-localization underlying the `B`-step involution closure:
if `h` lies in the box and satisfies the active root equation, then the
boundary involution image `2z - h - 1` lies in the same box, provided the box
half-width `W` dominates the quadratic root bound. -/
theorem hm23IntegerCore_B_involution_closed
    (W : ℕ) (N z B h : ℤ)
    (hW : (2 * |z| + 2 * |N - (B + 1) * z| + 5 : ℤ) ≤ (W : ℤ))
    (hmem : h ∈ Finset.Icc (-(W : ℤ)) ((W : ℤ) - 1))
    (hroot : Chapter10PF.triIntPF (h - z) + (B + 1) * z = N) :
    2 * z - h - 1 ∈ Finset.Icc (-(W : ℤ)) ((W : ℤ) - 1) := by
  rw [Finset.mem_Icc] at hmem ⊢
  have h2 := Chapter10PF.two_mul_triIntPF (h - z)
  have htri : Chapter10PF.triIntPF (h - z) = N - (B + 1) * z := by omega
  rw [htri] at h2
  set M : ℤ := N - (B + 1) * z with hM
  set t : ℤ := h - z with ht
  have htq : t * t + t = 2 * M := by
    have : (h - z) * (h - z + 1) = 2 * M := by rw [← h2]
    rw [← ht] at this; nlinarith [this]
  have hzabs : -|z| ≤ z ∧ z ≤ |z| := ⟨neg_abs_le z, le_abs_self z⟩
  have hMabs : -|M| ≤ M ∧ M ≤ |M| := ⟨neg_abs_le M, le_abs_self M⟩
  have habsM : 0 ≤ |M| := abs_nonneg M
  have htbound : -(2 * |M| + 1) ≤ t ∧ t ≤ 2 * |M| + 1 := by
    constructor
    · nlinarith [htq, hMabs.1, hMabs.2, sq_nonneg (t + 1), sq_nonneg t, habsM]
    · nlinarith [htq, hMabs.1, hMabs.2, sq_nonneg (t - 1), sq_nonneg t, habsM]
  have hmirror : 2 * z - h - 1 = z - t - 1 := by rw [ht]; ring
  rw [hmirror]
  rcases htbound with ⟨hl, hr⟩
  rcases hzabs with ⟨zl, zr⟩
  constructor <;> omega

/-- Moving the lower `B`-cutoff to `-1` leaves the boxed integer-core fiber sum
unchanged, provided `V` covers the `K`-boundary and `W` dominates the quadratic
root bound for every intermediate cutoff. -/
theorem hm23IntegerCoreFiberBoxSumInt_B_to_negOne
    (W V : ℕ) (N z A B : ℤ)
    (hVbound : (|B| + 1 : ℤ) ≤ (V : ℤ))
    (hWbound :
      (2 * |z| + 2 * |N| + 2 * ((|B| + 1) * |z|) + 5 : ℤ) ≤ (W : ℤ)) :
    hm23IntegerCoreFiberBoxSumInt W V N z A B =
      hm23IntegerCoreFiberBoxSumInt W V N z A (-1) := by
  -- A helper estimate: the per-step closure bound (at the lower box-cutoff
  -- value `C`) is dominated by `hWbound` for every intermediate `C` with
  -- `|C + 1| ≤ |B| + 1`.
  have hzabs : 0 ≤ |z| := abs_nonneg z
  have dom : ∀ C : ℤ, |C + 1| ≤ |B| + 1 →
      (2 * |z| + 2 * |N - (C + 1) * z| + 5 : ℤ) ≤ (W : ℤ) := by
    intro C hC
    have h1 : |N - (C + 1) * z| ≤ |N| + |C + 1| * |z| := by
      have htri : |N - (C + 1) * z| ≤ |N| + |(C + 1) * z| := by
        rw [sub_eq_add_neg]
        refine (abs_add_le N (-((C + 1) * z))).trans ?_
        rw [abs_neg]
      rw [abs_mul] at htri
      exact htri
    have h2 : |C + 1| * |z| ≤ (|B| + 1) * |z| :=
      mul_le_mul_of_nonneg_right hC hzabs
    have hfix : 2 * ((|B| + 1) * |z|) = 2 * ((|B| + 1) * |z|) := rfl
    nlinarith [h1, h2, hWbound, hzabs]
  rcases le_or_gt (-1) B with hB | hB
  · -- B ≥ -1 : descend from B to -1
    have key : ∀ C : ℤ, -1 ≤ C → C ≤ B →
        hm23IntegerCoreFiberBoxSumInt W V N z A C =
          hm23IntegerCoreFiberBoxSumInt W V N z A (-1) := by
      intro C hC
      induction C, hC using Int.le_induction with
      | base => intro _; rfl
      | succ n hn ih =>
          intro hnB
          have hbnd : |n + 1| ≤ |B| + 1 := by
            rcases abs_cases (n + 1) with ⟨he, _⟩ | ⟨he, _⟩ <;>
              rcases abs_cases B with ⟨hf, _⟩ | ⟨hf, _⟩ <;> omega
          have hVn : (n + 1 : ℤ) ≤ (V : ℤ) := by
            have hb : |B| + 1 ≤ (V : ℤ) := hVbound
            rcases abs_cases (n + 1) with ⟨he, _⟩ | ⟨he, _⟩ <;>
              rcases abs_cases B with ⟨hf, _⟩ | ⟨hf, _⟩ <;> omega
          have hstep :
              hm23IntegerCoreFiberBoxSumInt W V N z A (n + 1) =
                hm23IntegerCoreFiberBoxSumInt W V N z A n := by
            apply hm23IntegerCoreFiberBoxSumInt_B_succ
            · rw [Finset.mem_Icc]; constructor <;> omega
            · intro h hmem hroot
              exact hm23IntegerCore_B_involution_closed W N z n h
                (dom n (by
                  rcases abs_cases (n + 1) with ⟨he, _⟩ | ⟨he, _⟩ <;>
                    rcases abs_cases B with ⟨hf, _⟩ | ⟨hf, _⟩ <;> omega)) hmem hroot
          rw [hstep]
          exact ih (by omega)
    exact key B hB (le_refl B)
  · -- B < -1 : ascend from B to -1
    have key : ∀ C : ℤ, C ≤ -1 → B ≤ C →
        hm23IntegerCoreFiberBoxSumInt W V N z A C =
          hm23IntegerCoreFiberBoxSumInt W V N z A (-1) := by
      intro C hC
      induction C, hC using Int.le_induction_down with
      | base => intro _; rfl
      | pred n hn ih =>
          intro hBn
          have hVn1 : (|n - 1| + 1 : ℤ) ≤ (V : ℤ) := by
            have hb : |B| + 1 ≤ (V : ℤ) := hVbound
            rcases abs_cases (n - 1) with ⟨he, _⟩ | ⟨he, _⟩ <;>
              rcases abs_cases B with ⟨hf, _⟩ | ⟨hf, _⟩ <;> omega
          have hstep :
              hm23IntegerCoreFiberBoxSumInt W V N z A n =
                hm23IntegerCoreFiberBoxSumInt W V N z A (n - 1) := by
            have hh := hm23IntegerCoreFiberBoxSumInt_B_succ W V N z A (n - 1)
              (by rw [Finset.mem_Icc]
                  constructor <;>
                    (rcases abs_cases (n - 1) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega))
              (by intro h hmem hroot
                  exact hm23IntegerCore_B_involution_closed W N z (n - 1) h
                    (dom (n - 1) (by
                      rcases abs_cases (n - 1 + 1) with ⟨he, _⟩ | ⟨he, _⟩ <;>
                        rcases abs_cases B with ⟨hf, _⟩ | ⟨hf, _⟩ <;> omega)) hmem
                    hroot)
            rw [show (n - 1) + 1 = n by ring] at hh
            exact hh
          rw [← hstep]
          exact ih (by omega)
    exact key B (by omega) (le_refl B)

/-- All-cutoff invariance: at fixed (large enough) windows `W, V`, the
integer-core fiber sum does not depend on the cutoffs `(A, B)`; it equals the
`(0, -1)` value.  The window bounds are explicit functions of `|A|, |B|, N, z`
and are discharged by `omega`/`nlinarith` inside the A/B step lemmas. -/
theorem hm23IntegerCoreFiberSumInt_cutoff_invariant
    (W V : ℕ) (N z A B : ℤ)
    (hVA : (W : ℤ) + |A| + 1 ≤ (V : ℤ))
    (hVB : (|B| + 1 : ℤ) ≤ (V : ℤ))
    (hWB : (2 * |z| + 2 * |N| + 2 * ((|B| + 1) * |z|) + 5 : ℤ) ≤ (W : ℤ)) :
    hm23IntegerCoreFiberSumInt W V N z A B =
      hm23IntegerCoreFiberSumInt W V N z 0 (-1) := by
  rw [hm23IntegerCoreFiberSumInt_A_to_zero W V N z B A hVA]
  rw [hm23IntegerCoreFiberSumInt_eq_box W V N z 0 B]
  rw [hm23IntegerCoreFiberBoxSumInt_B_to_negOne W V N z 0 B hVB hWB]
  rw [← hm23IntegerCoreFiberSumInt_eq_box W V N z 0 (-1)]

/-! ### HM 2.3 piece (1): window-independence of the integer-core fiber sum

The cutoff-invariance capstone reduces an arbitrary fiber sum to the `A = 0`,
`B = -1` normal form at a fixed window `(W, V)`.  The lemmas below show that the
resulting sum no longer depends on the window once `W` and `V` exceed the finite
support `|h|, |K| ≤ |N| + |z| + 1`, and in particular it equals the canonical
integer-core sum `hm23IntegerCoreCanonicalSumInt`.  This is the enlarge/shrink
support-vanishing step: enlarging the windows only adds summands that are
identically zero. -/

theorem hm23_consec_nonneg (t : ℤ) : 0 ≤ t * (t + 1) := by
  rcases le_or_gt 0 t with h | h
  · positivity
  · nlinarith [le_of_lt h]

/-- The `A = 0, B = -1` cutoff indicator is nonzero only on the support
`0 ≤ K ≤ h` (value `+1`) or `h < K ≤ -1` (value `-1`); on that support the raw
`q`-exponent `T_{h-z} + K z` is nonnegative. -/
theorem hm23IntegerCoreSummandInt_exponent_nonneg
    (z h K : ℤ)
    (hind :
      ((if K ≤ h + 0 then (1 : ℤ) else 0) -
        (if K ≤ -1 then (1 : ℤ) else 0)) ≠ 0) :
    0 ≤ Chapter10PF.triIntPF (h - z) + K * z := by
  have htwo := Chapter10PF.two_mul_triIntPF (h - z)
  have hcons : 0 ≤ (K + z - h) * (K + z - h - 1) := by
    have := hm23_consec_nonneg (K + z - h - 1); nlinarith [this]
  have key : 0 ≤ 2 * (Chapter10PF.triIntPF (h - z) + K * z) := by
    rw [mul_add, htwo]
    by_cases hKh : K ≤ h + 0
    · by_cases hK1 : K ≤ -1
      · exact absurd (by simp only [if_pos (show K ≤ h + 0 from hKh), if_pos hK1]; ring) hind
      · have hK0 : 0 ≤ K := by omega
        have hKh' : 0 ≤ h - K := by omega
        nlinarith [hcons, mul_nonneg hK0 (by omega : (0:ℤ) ≤ K+1), mul_nonneg hK0 hKh']
    · by_cases hK1 : K ≤ -1
      · have h1 : 0 ≤ -K := by omega
        have h2 : 0 ≤ -K-1 := by omega
        have h3 : 0 ≤ K - h := by omega
        nlinarith [hcons, mul_nonneg h1 h2, mul_nonneg h1 h3]
      · exact absurd (by simp only [if_neg hKh, if_neg hK1]; ring) hind
  linarith

/-- For `N < 0`, every `A = 0, B = -1` integer-core summand vanishes, because the
`q`-exponent is nonnegative wherever the cutoff indicator is nonzero. -/
theorem hm23IntegerCoreSummandInt_zero_of_neg_N
    {N : ℤ} (z h K : ℤ) (hN : N < 0) :
    hm23IntegerCoreSummandInt N z 0 (-1) h K = 0 := by
  unfold hm23IntegerCoreSummandInt
  by_cases hc : Chapter10PF.triIntPF (h - z) + K * z = N
  · by_cases hind :
        ((if K ≤ h + 0 then (1 : ℤ) else 0) -
          (if K ≤ -1 then (1 : ℤ) else 0)) = 0
    · rw [if_pos hc, hind, mul_zero]
    · exfalso
      have := hm23IntegerCoreSummandInt_exponent_nonneg z h K hind
      omega
  · rw [if_neg hc]

/-- Support bound on the cutoff index `K`: a nonzero `A = 0, B = -1` summand at
`q`-degree `N` forces `|K| ≤ |N| + |z| + 1`. -/
theorem hm23IntegerCoreSummandInt_K_bound
    {N : ℤ} (z h K : ℤ) (hN : 0 ≤ N)
    (hne : hm23IntegerCoreSummandInt N z 0 (-1) h K ≠ 0) :
    |K| ≤ |N| + |z| + 1 := by
  have hc : Chapter10PF.triIntPF (h - z) + K * z = N := by
    by_contra hc; rw [hm23IntegerCoreSummandInt, if_neg hc] at hne; exact hne rfl
  have hind :
      ((if K ≤ h + 0 then (1 : ℤ) else 0) -
        (if K ≤ -1 then (1 : ℤ) else 0)) ≠ 0 := by
    intro h0
    rw [hm23IntegerCoreSummandInt, if_pos hc, h0, mul_zero] at hne; exact hne rfl
  have htwo := Chapter10PF.two_mul_triIntPF (h - z)
  have e2 : 2 * N = (h - z) * (h - z + 1) + 2 * K * z := by
    have h' : 2 * (Chapter10PF.triIntPF (h - z) + K * z) = 2 * N := by rw [hc]
    rw [mul_add, htwo] at h'; linarith
  rw [abs_of_nonneg hN]
  have habsz : 0 ≤ |z| := abs_nonneg z
  by_cases hKh : K ≤ h + 0
  · by_cases hK1 : K ≤ -1
    · exact absurd (by simp only [if_pos (show K ≤ h + 0 from hKh), if_pos hK1]; ring) hind
    · -- 0 ≤ K ≤ h
      have hK0 : 0 ≤ K := by omega
      have hKh' : 0 ≤ h - K := by omega
      rw [abs_of_nonneg hK0]
      -- K ≤ N : since 2N = (h-z)(h-z+1)+2Kz ≥ 2Kz ... use exponent ≥ K*K form
      nlinarith [hm23_consec_nonneg (h - z), hm23_consec_nonneg (K + z - h - 1),
        mul_nonneg hK0 hKh', neg_abs_le z, le_abs_self z, mul_nonneg hK0 habsz]
  · by_cases hK1 : K ≤ -1
    · -- h < K ≤ -1
      have h1 : 0 ≤ -K := by omega
      have h2 : 0 ≤ -K - 1 := by omega
      have h3 : 0 ≤ K - h := by omega
      rw [abs_of_nonpos (by omega : K ≤ 0)]
      nlinarith [hm23_consec_nonneg (h - z), hm23_consec_nonneg (K + z - h - 1),
        mul_nonneg h1 h3, neg_abs_le z, le_abs_self z, mul_nonneg h1 habsz]
    · exact absurd (by simp only [if_neg hKh, if_neg hK1]; ring) hind

/-- Tight positive-branch support bound: a nonzero `A = 0, B = -1` summand at a
nonnegative index `h` and `q`-degree `N ≥ 0` forces `h < thetaMulPFWindowPF N z`.
This is what lets the positive `h`-range shrink to the canonical PF window. -/
theorem hm23IntegerCoreSummandInt_pos_h_lt_window
    (z : ℤ) (N h : ℕ) (K : ℤ)
    (hne : hm23IntegerCoreSummandInt (N : ℤ) z 0 (-1) (h : ℤ) K ≠ 0) :
    h < Chapter10PF.thetaMulPFWindowPF N z := by
  have hc : Chapter10PF.triIntPF ((h : ℤ) - z) + K * z = (N : ℤ) := by
    by_contra hc; rw [hm23IntegerCoreSummandInt, if_neg hc] at hne; exact hne rfl
  have hind :
      ((if K ≤ (h : ℤ) + 0 then (1 : ℤ) else 0) -
        (if K ≤ -1 then (1 : ℤ) else 0)) ≠ 0 := by
    intro h0
    rw [hm23IntegerCoreSummandInt, if_pos hc, h0, mul_zero] at hne; exact hne rfl
  -- nonzero indicator at h ≥ 0 forces 0 ≤ K ≤ h
  have hKrange : 0 ≤ K ∧ K ≤ (h : ℤ) := by
    by_cases hKh : K ≤ (h : ℤ) + 0
    · by_cases hK1 : K ≤ -1
      · exact absurd (by simp only [if_pos hKh, if_pos hK1]; ring) hind
      · exact ⟨by omega, by omega⟩
    · exact absurd (by simp only [if_neg hKh, if_neg (show ¬ K ≤ -1 by omega)]; ring) hind
  obtain ⟨hK0, hKh⟩ := hKrange
  have htwo := Chapter10PF.two_mul_triIntPF ((h : ℤ) - z)
  have e2 : 2 * (N : ℤ) = ((h : ℤ) - z) * ((h : ℤ) - z + 1) + 2 * K * z := by
    have h' : 2 * (Chapter10PF.triIntPF ((h : ℤ) - z) + K * z) = 2 * (N : ℤ) := by rw [hc]
    rw [mul_add, htwo] at h'; linarith
  have hKh' : 0 ≤ (h : ℤ) - K := by omega
  unfold Chapter10PF.thetaMulPFWindowPF
  by_cases hz : z = 0
  · subst z
    rw [if_pos rfl]
    have heq0 : (h : ℤ) * ((h : ℤ) + 1) = 2 * (N : ℤ) := by
      have := e2; simp at this; linarith
    rcases Nat.lt_or_ge h (N + 1) with hlt | hge
    · exact hlt
    · exfalso
      have hge' : (N : ℤ) + 1 ≤ (h : ℤ) := by exact_mod_cast hge
      nlinarith [Int.natCast_nonneg N, Int.natCast_nonneg h]
  · rw [if_neg hz]
    have hbound : (h : ℤ) ≤ (N : ℤ) + |z| + 1 := by
      rcases le_or_gt 0 z with hzn | hzn
      · rw [abs_of_nonneg hzn]
        nlinarith [hm23_consec_nonneg ((h:ℤ) - z - 1), mul_nonneg hKh' hzn,
          mul_nonneg hK0 hzn, Int.natCast_nonneg N]
      · rw [abs_of_neg hzn]
        have hznn : 0 ≤ -z := by omega
        nlinarith [hm23_consec_nonneg ((h:ℤ) - z - 1), mul_nonneg hK0 hznn,
          mul_nonneg hKh' hznn, Int.natCast_nonneg N]
    have hlt : (h : ℤ) < (N : ℤ) + (z.natAbs : ℤ) + 2 := by
      rw [Int.abs_eq_natAbs] at hbound; omega
    have hcast : ((N + z.natAbs + 2 : ℕ) : ℤ) = (N : ℤ) + (z.natAbs : ℤ) + 2 := by
      push_cast; ring
    rw [← hcast] at hlt; exact_mod_cast hlt

/-- Tight negative-branch support bound: a nonzero `A = 0, B = -1` summand at a
reflected index `h = -(H+1)` and `q`-degree `N ≥ 0` forces
`H < thetaMulPFWindowPF N z`. -/
theorem hm23IntegerCoreSummandInt_neg_H_lt_window
    (z : ℤ) (N H : ℕ) (K : ℤ)
    (hne : hm23IntegerCoreSummandInt (N : ℤ) z 0 (-1) (-((H : ℤ) + 1)) K ≠ 0) :
    H < Chapter10PF.thetaMulPFWindowPF N z := by
  have hc : Chapter10PF.triIntPF (-((H : ℤ) + 1) - z) + K * z = (N : ℤ) := by
    by_contra hc; rw [hm23IntegerCoreSummandInt, if_neg hc] at hne; exact hne rfl
  have hind :
      ((if K ≤ -((H : ℤ) + 1) + 0 then (1 : ℤ) else 0) -
        (if K ≤ -1 then (1 : ℤ) else 0)) ≠ 0 := by
    intro h0
    rw [hm23IntegerCoreSummandInt, if_pos hc, h0, mul_zero] at hne; exact hne rfl
  -- nonzero indicator forces -(H+1) < K ≤ -1
  have hKrange : -((H : ℤ) + 1) < K ∧ K ≤ -1 := by
    by_cases hKh : K ≤ -((H : ℤ) + 1) + 0
    · by_cases hK1 : K ≤ -1
      · exact absurd (by simp only [if_pos hKh, if_pos hK1]; ring) hind
      · exact absurd (show K ≤ -1 by
          have : K ≤ -((H : ℤ) + 1) := by simpa using hKh
          omega) hK1
    · by_cases hK1 : K ≤ -1
      · exact ⟨by omega, hK1⟩
      · exact absurd (by simp only [if_neg hKh, if_neg (show ¬ K ≤ -1 by omega)]; ring) hind
  obtain ⟨hKlo, hKhi⟩ := hKrange
  -- reflect the exponent: tri(-(H+1)-z) = tri(H+z)
  have hreflect : Chapter10PF.triIntPF (-((H : ℤ) + 1) - z) =
      Chapter10PF.triIntPF ((H : ℤ) + z) := by
    rw [show -((H : ℤ) + 1) - z = -(((H : ℤ) + z)) - 1 by ring]
    exact Chapter10PF.triIntPF_reflect ((H : ℤ) + z)
  rw [hreflect] at hc
  have htwo := Chapter10PF.two_mul_triIntPF ((H : ℤ) + z)
  have e2 : 2 * (N : ℤ) = ((H : ℤ) + z) * ((H : ℤ) + z + 1) + 2 * K * z := by
    have h' : 2 * (Chapter10PF.triIntPF ((H : ℤ) + z) + K * z) = 2 * (N : ℤ) := by rw [hc]
    rw [mul_add, htwo] at h'; linarith
  -- set c := -K-1, 0 ≤ c < H : -(H+1)<K≤-1  ⟹  0 ≤ -K-1 ≤ H-1, but we only need bound on H
  have hc0 : 0 ≤ -K - 1 := by omega
  have hcH : -K - 1 ≤ (H : ℤ) := by omega  -- from -(H+1)<K i.e. K > -(H+1)
  unfold Chapter10PF.thetaMulPFWindowPF
  by_cases hz : z = 0
  · subst z
    rw [if_pos rfl]
    have heq0 : (H : ℤ) * ((H : ℤ) + 1) = 2 * (N : ℤ) := by
      have := e2; simp at this; linarith
    rcases Nat.lt_or_ge H (N + 1) with hlt | hge
    · exact hlt
    · exfalso
      have hge' : (N : ℤ) + 1 ≤ (H : ℤ) := by exact_mod_cast hge
      nlinarith [Int.natCast_nonneg N, Int.natCast_nonneg H]
  · rw [if_neg hz]
    -- bound: H ≤ N + |z| + 1 using c=-K-1 in [0,H], i.e. K=-c-1, K*z handled by sign split
    have hbound : (H : ℤ) ≤ (N : ℤ) + |z| + 1 := by
      rcases le_or_gt 0 z with hzn | hzn
      · rw [abs_of_nonneg hzn]
        nlinarith [hm23_consec_nonneg ((H:ℤ) + z), mul_nonneg hc0 hzn,
          mul_nonneg (by omega : (0:ℤ) ≤ (H:ℤ) - (-K-1)) hzn, Int.natCast_nonneg N]
      · rw [abs_of_neg hzn]
        have hznn : 0 ≤ -z := by omega
        nlinarith [hm23_consec_nonneg ((H:ℤ) + z), mul_nonneg hc0 hznn,
          mul_nonneg (by omega : (0:ℤ) ≤ (H:ℤ) - (-K-1)) hznn, Int.natCast_nonneg N]
    have hlt : (H : ℤ) < (N : ℤ) + (z.natAbs : ℤ) + 2 := by
      rw [Int.abs_eq_natAbs] at hbound; omega
    have hcast : ((N + z.natAbs + 2 : ℕ) : ℤ) = (N : ℤ) + (z.natAbs : ℤ) + 2 := by
      push_cast; ring
    rw [← hcast] at hlt; exact_mod_cast hlt

/-- `K`-window independence of the inner sum: once the symmetric `K`-window
`Icc(-V, V)` contains the support `|K| ≤ |N| + |z| + 1`, the inner sum does not
depend on `V`. -/
theorem hm23IntegerCoreInner_K_window_indep
    {N : ℤ} (z A_h : ℤ) (V V' : ℕ) (hN : 0 ≤ N)
    (hV : |N| + |z| + 1 ≤ (V : ℤ)) (hV' : |N| + |z| + 1 ≤ (V' : ℤ)) :
    (∑ K ∈ Finset.Icc (-(V : ℤ)) (V : ℤ),
        hm23IntegerCoreSummandInt N z 0 (-1) A_h K) =
      ∑ K ∈ Finset.Icc (-(V' : ℤ)) (V' : ℤ),
        hm23IntegerCoreSummandInt N z 0 (-1) A_h K := by
  classical
  -- both equal the sum over the support window Icc(-thr, thr)
  let thr : ℤ := |N| + |z| + 1
  have hsub : ∀ (W : ℕ), thr ≤ (W : ℤ) →
      (∑ K ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
          hm23IntegerCoreSummandInt N z 0 (-1) A_h K) =
        ∑ K ∈ Finset.Icc (-thr) thr,
          hm23IntegerCoreSummandInt N z 0 (-1) A_h K := by
    intro W hW
    symm
    refine Finset.sum_subset ?_ ?_
    · intro K hK
      rw [Finset.mem_Icc] at hK ⊢
      constructor <;> omega
    · intro K _hK hKnot
      rw [Finset.mem_Icc] at hKnot
      by_contra hne
      have hb := hm23IntegerCoreSummandInt_K_bound (N := N) z A_h K hN hne
      rw [abs_le] at hb
      simp only [thr] at hKnot
      omega
  rw [hsub V hV, hsub V' hV']

theorem hm23_window_ge_threshold (N : ℕ) (z : ℤ) :
    (N : ℤ) + |z| + 1 ≤ (Chapter10PF.thetaMulPFWindowPF N z : ℤ) := by
  unfold Chapter10PF.thetaMulPFWindowPF
  by_cases hz : z = 0
  · subst z; simp
  · rw [if_neg hz]
    have : |z| = (z.natAbs : ℤ) := Int.abs_eq_natAbs z
    rw [this]; push_cast; omega

/-- Master window-independence (HM 2.3 piece 1): with `A = 0, B = -1`, the
integer-core fiber sum at any windows `W, V` no smaller than the canonical PF
window equals the canonical integer-core sum.  Enlarging the windows only adds
summands that vanish on the finite support `|h|, |K| ≤ |N| + |z| + 1`. -/
theorem hm23IntegerCoreFiberSumInt_eq_canonical
    (W V : ℕ) (N z : ℤ)
    (hWc : Chapter10PF.thetaMulPFWindowPF N.toNat z ≤ W)
    (hVc : (Chapter10PF.thetaMulPFWindowPF N.toNat z : ℤ) ≤ (V : ℤ)) :
    hm23IntegerCoreFiberSumInt W V N z 0 (-1) =
      hm23IntegerCoreCanonicalSumInt N z := by
  classical
  rcases lt_or_ge N 0 with hNneg | hNpos
  · -- N < 0: both sides are 0
    rw [hm23IntegerCoreCanonicalSumInt_eq_zero_of_neg hNneg]
    unfold hm23IntegerCoreFiberSumInt
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero] <;>
    · intro h _hh
      refine Finset.sum_eq_zero ?_
      intro K _hK
      exact hm23IntegerCoreSummandInt_zero_of_neg_N z _ K hNneg
  · -- N ≥ 0
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = (n : ℤ) := ⟨N.toNat, by omega⟩
    set Wc := Chapter10PF.thetaMulPFWindowPF n z with hWcdef
    have htoNat : (n : ℤ).toNat = n := by simp
    rw [htoNat] at hWc hVc
    have hthr : (n : ℤ) + |z| + 1 ≤ (Wc : ℤ) := hm23_window_ge_threshold n z
    have habsN : |(n : ℤ)| = (n : ℤ) := abs_of_nonneg (Int.natCast_nonneg n)
    -- canonical sum for N ≥ 0
    have hcanon : hm23IntegerCoreCanonicalSumInt (n : ℤ) z =
        (∑ h ∈ Finset.range Wc,
            ∑ K ∈ Finset.Icc (-(Wc : ℤ)) (Wc : ℤ),
              hm23IntegerCoreSummandInt (n : ℤ) z 0 (-1) (h : ℤ) K) +
          (∑ H ∈ Finset.range Wc,
            ∑ K ∈ Finset.Icc (-(Wc : ℤ)) (Wc : ℤ),
              hm23IntegerCoreSummandInt (n : ℤ) z 0 (-1) (-((H : ℤ) + 1)) K) := by
      unfold hm23IntegerCoreCanonicalSumInt
      have hnn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
      simp only [hnn, if_true, htoNat, ← hWcdef]
    rw [hcanon]
    unfold hm23IntegerCoreFiberSumInt
    -- handle V-window: each inner K-sum over Icc(-V,V) equals over Icc(-Wc,Wc)
    have hVthr : |(n : ℤ)| + |z| + 1 ≤ (V : ℤ) := by rw [habsN]; omega
    have hWcthr : |(n : ℤ)| + |z| + 1 ≤ (Wc : ℤ) := by rw [habsN]; exact hthr
    have hKpos : ∀ Ah : ℤ,
        (∑ K ∈ Finset.Icc (-(V : ℤ)) (V : ℤ),
            hm23IntegerCoreSummandInt (n : ℤ) z 0 (-1) Ah K) =
          ∑ K ∈ Finset.Icc (-(Wc : ℤ)) (Wc : ℤ),
            hm23IntegerCoreSummandInt (n : ℤ) z 0 (-1) Ah K := by
      intro Ah
      exact hm23IntegerCoreInner_K_window_indep z Ah V Wc (Int.natCast_nonneg n) hVthr hWcthr
    congr 1
    · -- positive branch: shrink h-range, then match K-window
      have hshrink :
          (∑ h ∈ Finset.range W,
              ∑ K ∈ Finset.Icc (-(V : ℤ)) (V : ℤ),
                hm23IntegerCoreSummandInt (n : ℤ) z 0 (-1) (h : ℤ) K) =
            ∑ h ∈ Finset.range Wc,
              ∑ K ∈ Finset.Icc (-(V : ℤ)) (V : ℤ),
                hm23IntegerCoreSummandInt (n : ℤ) z 0 (-1) (h : ℤ) K := by
        symm
        refine Finset.sum_subset ?_ ?_
        · intro h hh; rw [Finset.mem_range] at hh ⊢; omega
        · intro h _hh hhnot
          rw [Finset.mem_range] at hhnot
          refine Finset.sum_eq_zero ?_
          intro K _hK
          by_contra hne
          have := hm23IntegerCoreSummandInt_pos_h_lt_window z n h K hne
          omega
      rw [hshrink]
      refine Finset.sum_congr rfl ?_
      intro h _hh
      exact hKpos (h : ℤ)
    · -- negative branch
      have hshrink :
          (∑ H ∈ Finset.range W,
              ∑ K ∈ Finset.Icc (-(V : ℤ)) (V : ℤ),
                hm23IntegerCoreSummandInt (n : ℤ) z 0 (-1) (-((H : ℤ) + 1)) K) =
            ∑ H ∈ Finset.range Wc,
              ∑ K ∈ Finset.Icc (-(V : ℤ)) (V : ℤ),
                hm23IntegerCoreSummandInt (n : ℤ) z 0 (-1) (-((H : ℤ) + 1)) K := by
        symm
        refine Finset.sum_subset ?_ ?_
        · intro H hH; rw [Finset.mem_range] at hH ⊢; omega
        · intro H _hH hHnot
          rw [Finset.mem_range] at hHnot
          refine Finset.sum_eq_zero ?_
          intro K _hK
          by_contra hne
          have := hm23IntegerCoreSummandInt_neg_H_lt_window z n H K hne
          omega
      rw [hshrink]
      refine Finset.sum_congr rfl ?_
      intro H _hH
      exact hKpos (-((H : ℤ) + 1))


theorem hm23IntegerCoreCanonical_eq_thetaMulPFCoeffPF (N : ℕ) (z : ℤ) :
    hm23IntegerCoreCanonicalSum N z = Chapter10PF.thetaMulPFCoeffPF N z := by
  classical
  unfold hm23IntegerCoreCanonicalSum Chapter10PF.thetaMulPFCoeffPF
    Chapter10PF.thetaMulPFPositiveCoeffPF Chapter10PF.thetaMulPFNegativeCoeffPF
  let W := Chapter10PF.thetaMulPFWindowPF N z
  change
    (∑ h ∈ Finset.range W,
        ∑ K ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
          hm23IntegerCoreSummand N z 0 (-1) (h : ℤ) K) +
      (∑ H ∈ Finset.range W,
        ∑ K ∈ Finset.Icc (-(W : ℤ)) (W : ℤ),
          hm23IntegerCoreSummand N z 0 (-1) (-((H : ℤ) + 1)) K) =
      (∑ h ∈ Finset.range W,
        ∑ k ∈ Finset.range (h + 1),
          if Chapter10PF.triIntPF ((h : ℤ) - z) + (k : ℤ) * z =
              (N : ℤ) then
            Chapter10PF.negOnePowIntPF ℤ ((h : ℤ) - z)
          else
            0) +
        ∑ h ∈ Finset.range W,
          ∑ c ∈ Finset.range h,
            if Chapter10PF.triIntPF ((h : ℤ) + z) - ((c : ℤ) + 1) * z =
                (N : ℤ) then
              Chapter10PF.negOnePowIntPF ℤ ((h : ℤ) + z)
            else
              0
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro h hh
    exact hm23IntegerCoreCanonical_pos_inner N W h z (by simpa using hh)
  · refine Finset.sum_congr rfl ?_
    intro H hH
    exact hm23IntegerCoreCanonical_neg_inner N W H z (by simpa using hH)

theorem hm23IntegerCoreCanonical_eq_unified (N : ℕ) (z : ℤ) :
    hm23IntegerCoreCanonicalSum N z =
      Chapter10PF.thetaMulPFUnifiedCoeffPF N z := by
  rw [hm23IntegerCoreCanonical_eq_thetaMulPFCoeffPF,
    Chapter10PF.thetaMulPFCoeffPF_eq_unified]

/-- Cube-coefficient bridge: under `hPF`, the Laurent coefficient of `J₁^3` at a
nonnegative multiple `90 N` equals the rational cast of the unified PF
coefficient `thetaMulPFUnifiedCoeffPF N 0`.  (The cube is the `u = 0` projection
of `j(u;q)·PF(u)`.) -/
theorem lcoeff_JOneLaurent_pow_three_eq_unified
    (hPF :
      Chapter10PF.thetaMulPFSeriesCoeffPF =
        Chapter10PF.qPochInfPSCubeUPowerCoeffPF)
    (N : ℕ) :
    lcoeff (JOneLaurent ^ 3) ((90 * N : ℕ) : ℤ) =
      ((Chapter10PF.thetaMulPFUnifiedCoeffPF N 0 : ℤ) : ℚ) := by
  have hbridge :=
    hm23_thetaMulPFRawCoeffPF_rat_eq_JOneCoeff_of_hPF hPF N 0
  rw [if_pos rfl] at hbridge
  rw [← hbridge]
  rw [Chapter10PF.thetaMulPFRawCoeffPF_eq_thetaMulPFCoeffPF,
    Chapter10PF.thetaMulPFCoeffPF_eq_unified]

theorem hm23_linear90_pos_iff_cutoff (n c : ℤ) :
    (0 < 90 * n + c) ↔ -n ≤ (c - 1) / 90 := by
  rw [Int.le_ediv_iff_mul_le (show (0 : ℤ) < 90 by norm_num)]
  omega

theorem hm23Ncoord_eq_integer_core_exponent (m p z r k : ℤ) :
    hm23Ncoord m p z r k =
      Chapter10PF.triIntPF (2 * r + k - m - p - z - 1) +
        (r - m + k) * z := by
  rw [hm23Ncoord_eq_pf_raw_exponent]
  unfold hmTri Chapter10PF.jExpIntPF Chapter10PF.pfNumExpIntPF
  have hR := Chapter10PF.two_mul_triIntPF (z + p - r)
  have hK := Chapter10PF.two_mul_triIntPF (r - m + k)
  have hQ := Chapter10PF.two_mul_triIntPF (2 * r + k - m - p - z - 1)
  have hR' :
      Chapter10PF.triIntPF (z + (p - r)) * 2 =
        (z + p - r) * (z + p - r + 1) := by
    rw [show z + (p - r) = z + p - r by ring]
    rw [mul_comm, hR]
  have hK' :
      Chapter10PF.triIntPF (r - m + k) * 2 =
        (r - m + k) * (r - m + k + 1) := by
    rw [mul_comm, hK]
  have hQ' :
      Chapter10PF.triIntPF (-1 + (-z - p) + (r * 2 - m) + k) * 2 =
        (2 * r + k - m - p - z - 1) *
          (2 * r + k - m - p - z - 1 + 1) := by
    rw [show -1 + (-z - p) + (r * 2 - m) + k =
      2 * r + k - m - p - z - 1 by ring]
    rw [mul_comm, hQ]
  have hR'' : Chapter10PF.triIntPF (z + p - r) * 2 =
      (z + p - r) * (z + p - r + 1) := by
    have := hR; rw [show z + p - r = z + (p - r) by ring]; linarith
  have hQ'' : Chapter10PF.triIntPF (-1 - z - p + r * 2 - m + k) * 2 =
      (-1 - z - p + r * 2 - m + k) * (-1 - z - p + r * 2 - m + k + 1) := by
    have := hQ; rw [show 2 * r + k - m - p - z - 1 = -1 - z - p + r * 2 - m + k by ring] at this
    linarith
  apply (mul_left_injective₀ (show (2 : ℤ) ≠ 0 by norm_num))
  ring_nf
  rw [hR'', hK', hQ'']
  ring

theorem hm23_integer_core_sign_eq_coord (m p z r k : ℤ) :
    Chapter10PF.negOnePowIntPF ℤ (2 * r + k - m - p - z - 1) =
      Chapter10PF.negOnePowIntPF ℤ (z + p - m + 1 - k) := by
  apply Chapter10PF.negOnePowIntPF_eq_of_even_sub
  refine ⟨r + k - p - z - 1, ?_⟩
  ring

theorem hm23Gamma_coord_sub_eq_integer_core_cutoff
    (a z0 z1 m p z r k : ℤ)
    (hreg : hm23Nonsingular a z0 z1) :
    hm23Gamma (appellDenomExp a z1 r) k -
        hm23Gamma (appellDenomExp a z0 (z + p - r + 1 - k)) k =
      (if r - m + k ≤
          (2 * r + k - m - p - 1) + (p + (a + z1 - 1) / 90) then
        (1 : ℚ) else 0) -
        (if r - m + k ≤ z + p - m + (a + z0 - 1) / 90 then
          (1 : ℚ) else 0) := by
  rw [hm23Gamma_coord_sub_eq_cutoff a z0 z1 m p z r k hreg]
  have hD1 :
      (0 < appellDenomExp a z1 r) ↔
        r - m + k ≤
          (2 * r + k - m - p - 1) + (p + (a + z1 - 1) / 90) := by
    unfold appellDenomExp
    rw [show 90 * (r - 1) + a + z1 = 90 * (r - 1) + (a + z1) by ring]
    rw [hm23_linear90_pos_iff_cutoff (r - 1) (a + z1)]
    omega
  have hD0 :
      (0 < appellDenomExp a z0 (z + p - r + 1 - k)) ↔
        r - m + k ≤ z + p - m + (a + z0 - 1) / 90 := by
    unfold appellDenomExp
    rw [show 90 * (z + p - r + 1 - k - 1) + a + z0 =
      90 * (z + p - r + 1 - k - 1) + (a + z0) by ring]
    rw [hm23_linear90_pos_iff_cutoff
      (z + p - r + 1 - k - 1) (a + z0)]
    omega
  by_cases h1 : 0 < appellDenomExp a z1 r
  · have h1' :
        r - m + k ≤
          (2 * r + k - m - p - 1) + (p + (a + z1 - 1) / 90) :=
      hD1.mp h1
    by_cases h0 : 0 < appellDenomExp a z0 (z + p - r + 1 - k)
    · have h0' :
          r - m + k ≤ z + p - m + (a + z0 - 1) / 90 := hD0.mp h0
      simp [h1, h0, h1', h0']
    · have h0' :
          ¬ r - m + k ≤ z + p - m + (a + z0 - 1) / 90 := by
        intro hle
        exact h0 (hD0.mpr hle)
      simp [h1, h0, h1', h0']
  · have h1' :
        ¬ r - m + k ≤
          (2 * r + k - m - p - 1) + (p + (a + z1 - 1) / 90) := by
      intro hle
      exact h1 (hD1.mpr hle)
    by_cases h0 : 0 < appellDenomExp a z0 (z + p - r + 1 - k)
    · have h0' :
          r - m + k ≤ z + p - m + (a + z0 - 1) / 90 := hD0.mp h0
      simp [h1, h0, h1', h0']
    · have h0' :
          ¬ r - m + k ≤ z + p - m + (a + z0 - 1) / 90 := by
        intro hle
        exact h0 (hD0.mpr hle)
      simp [h1, h0, h1', h0']

theorem hm23_coord_fiber_term_eq_integerCoreSummand
    (N : ℕ) (a z0 z1 m p z r k : ℤ)
    (hreg : hm23Nonsingular a z0 z1)
    (hN : (N : ℤ) = hm23Ncoord m p z r k) :
    negOnePowIntQ (z + p - m + 1 - k) *
        (hm23Gamma (appellDenomExp a z1 r) k -
          hm23Gamma (appellDenomExp a z0 (z + p - r + 1 - k)) k) =
      ((hm23IntegerCoreSummand N z
        (p + (a + z1 - 1) / 90)
        (z + p - m + (a + z0 - 1) / 90)
        (2 * r + k - m - p - 1)
        (r - m + k) : ℤ) : ℚ) := by
  have hexp :
      Chapter10PF.triIntPF
          ((2 * r + k - m - p - 1) - z) +
          (r - m + k) * z = (N : ℤ) := by
    rw [hN, hm23Ncoord_eq_integer_core_exponent]
    ring
  have hgamma :=
    hm23Gamma_coord_sub_eq_integer_core_cutoff
      a z0 z1 m p z r k hreg
  have hsign :
      negOnePowIntQ (z + p - m + 1 - k) =
        ((Chapter10PF.negOnePowIntPF ℤ
          ((2 * r + k - m - p - 1) - z) : ℤ) : ℚ) := by
    rw [negOnePowIntQ_eq_negOnePowIntPF_cast]
    congr 1
    rw [show 2 * r + k - m - p - 1 - z =
      2 * r + k - m - p - z - 1 by ring]
    exact (hm23_integer_core_sign_eq_coord m p z r k).symm
  unfold hm23IntegerCoreSummand
  rw [if_pos hexp]
  rw [hsign, hgamma]
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_ite, Int.cast_one,
    Int.cast_zero]

/-- Integer-`N` form of `hm23_coord_fiber_term_eq_integerCoreSummand`: the
per-`(r,k)` coordinate Γ-difference (with the coordinate sign) equals the
integer-indexed core summand at the sheared coordinates.  Needed because, after
transport, the fiber index `N = hm23Ncoord m p z r k` can be negative. -/
theorem hm23_coord_fiber_term_eq_integerCoreSummandInt
    (a z0 z1 m p z r k : ℤ)
    (hreg : hm23Nonsingular a z0 z1) :
    negOnePowIntQ (z + p - m + 1 - k) *
        (hm23Gamma (appellDenomExp a z1 r) k -
          hm23Gamma (appellDenomExp a z0 (z + p - r + 1 - k)) k) =
      ((hm23IntegerCoreSummandInt (hm23Ncoord m p z r k) z
        (p + (a + z1 - 1) / 90)
        (z + p - m + (a + z0 - 1) / 90)
        (2 * r + k - m - p - 1)
        (r - m + k) : ℤ) : ℚ) := by
  have hexp :
      Chapter10PF.triIntPF
          ((2 * r + k - m - p - 1) - z) +
          (r - m + k) * z = hm23Ncoord m p z r k := by
    rw [hm23Ncoord_eq_integer_core_exponent]
    ring
  have hgamma :=
    hm23Gamma_coord_sub_eq_integer_core_cutoff
      a z0 z1 m p z r k hreg
  have hsign :
      negOnePowIntQ (z + p - m + 1 - k) =
        ((Chapter10PF.negOnePowIntPF ℤ
          ((2 * r + k - m - p - 1) - z) : ℤ) : ℚ) := by
    rw [negOnePowIntQ_eq_negOnePowIntPF_cast]
    congr 1
    rw [show 2 * r + k - m - p - 1 - z =
      2 * r + k - m - p - z - 1 by ring]
    exact (hm23_integer_core_sign_eq_coord m p z r k).symm
  unfold hm23IntegerCoreSummandInt
  rw [if_pos hexp]
  rw [hsign, hgamma]
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_ite, Int.cast_one,
    Int.cast_zero]

/-- The difference-cancellation involution `Φ` on the Term-1 source coordinates,
sending `(r,k,i,j,l)` to the Term-2 source `(s,k,h,j,l) = (i-k, k, r+k, j, l)`
(blueprint `Φ`). -/
def hm23Phi (x : HM23Psi1Source) : HM23Psi0Source :=
  { s := x.i - x.k, k := x.k, h := x.r + x.k, j := x.j, l := x.l }

/-- Inverse of the difference-cancellation involution `Φ`, sending a Term-2
source `(s,k,h,j,l)` to the Term-1 source `(h-k, k, s+k, j, l)` (blueprint
`Φ⁻¹`). -/
def hm23PhiInv (y : HM23Psi0Source) : HM23Psi1Source :=
  { r := y.h - y.k, k := y.k, i := y.s + y.k, j := y.j, l := y.l }

theorem hm23PhiInv_phi (x : HM23Psi1Source) : hm23PhiInv (hm23Phi x) = x := by
  cases x; simp [hm23Phi, hm23PhiInv]

theorem hm23Phi_phiInv (y : HM23Psi0Source) : hm23Phi (hm23PhiInv y) = y := by
  cases y; simp [hm23Phi, hm23PhiInv]

/-- Coordinate pullback identity (backbone of HM 2.3 piece 3): the Term-1 and
Term-2 transported coordinates agree after composing with `Φ`.  Equivalently,
`image hm23Psi1Coord` and `image hm23Psi0Coord` coincide on the `Φ`-related
sources, so the two coordinate-image sums share an index set. -/
theorem hm23Psi1Coord_eq_Psi0Coord_phi (x : HM23Psi1Source) :
    hm23Psi1Coord x = hm23Psi0Coord (hm23Phi x) := by
  cases x with
  | mk r k i j l =>
    have hN :
        hm23Psi1_N r k i j l = hm23Psi0_N (i - k) k (r + k) j l := by
      unfold hm23Psi1_N hm23Psi0_N hm23Psi1_m hm23Psi1_p hm23Psi0_m
        hm23Psi0_p
      have hphi := hm23Phi_quadratic_preservation r i k
      rw [show r + k - j - k = r - j by ring, show j + l + k = j + l + k from rfl]
      linarith [hphi]
    show (hm23Psi1Coord ⟨r, k, i, j, l⟩) = hm23Psi0Coord ⟨i - k, k, r + k, j, l⟩
    unfold hm23Psi1Coord hm23Psi0Coord
    congr 1 <;>
      first
        | exact hN
        | (simp only [hm23Psi1_m, hm23Psi0_m, hm23Psi1_z, hm23Psi0_z,
            hm23Psi0_r]; ring)

/-- Per-coordinate difference of the two transported coordinate summands.  Both
carry the same guard `E_out = e ∧ N = N_{m,p,z}(r,k)`; their difference (Term 1
minus Term 2) is the outer sign `(-1)^{m+p}` times the integer-core summand at
the sheared coordinates. -/
theorem hm23Term1_sub_Term2_CoordSummand
    (a z0 z1 e : ℤ) (hreg : hm23Nonsingular a z0 z1) (x : HM23Coord) :
    hm23Term1CoordSummand a z0 z1 e x - hm23Term2CoordSummand a z0 z1 e x =
      (if hm23TermOutExp a z0 z1 x.m x.p x.z x.N = e ∧
          x.N = hm23Ncoord x.m x.p x.z x.r x.k then
        negOnePowIntQ (x.m + x.p) *
          ((hm23IntegerCoreSummandInt (hm23Ncoord x.m x.p x.z x.r x.k) x.z
            (x.p + (a + z1 - 1) / 90)
            (x.z + x.p - x.m + (a + z0 - 1) / 90)
            (2 * x.r + x.k - x.m - x.p - 1)
            (x.r - x.m + x.k) : ℤ) : ℚ)
      else 0) := by
  unfold hm23Term1CoordSummand hm23Term2CoordSummand
  by_cases hguard :
      hm23TermOutExp a z0 z1 x.m x.p x.z x.N = e ∧
        x.N = hm23Ncoord x.m x.p x.z x.r x.k
  · rw [if_pos hguard, if_pos hguard, if_pos hguard]
    have hterm :=
      hm23_coord_fiber_term_eq_integerCoreSummandInt
        a z0 z1 x.m x.p x.z x.r x.k hreg
    rw [← mul_sub, mul_assoc]
    rw [hterm]
  · rw [if_neg hguard, if_neg hguard, if_neg hguard, sub_zero]

/-! ### HM 2.3 piece (1): sheared-box change of variables

The fiber telescope is naturally indexed by the source pair `(r, k)`, whereas
the proven integer-core machinery (`hm23IntegerCoreFiberBoxSumInt`,
`hm23IntegerCoreFiberSumInt_cutoff_invariant`, `…_eq_canonical`) is indexed by
the integer-core pair `(h, K)`.  The two are related by the unimodular
(`det = 1`) shear

  `h = 2 r + k - m - p - 1`,  `K = r - m + k`,

with explicit inverse

  `r = h - K + p + 1`,  `k = m - p - 1 - h + 2 K`.

The lemma below realizes this shear as a `Finset` bijection from a rectangular
integer-core box `Icc(-W, W-1) × Icc(-V, V)` onto its (parallelogram) preimage,
carved out of a generous `(r, k)` product box by the two shear inequalities.
This is the index-set core of HM 2.3 piece (1). -/

/-- The `(r, k)`-preimage parallelogram of the integer-core box
`Icc(-W, W-1) × Icc(-V, V)` under the shear `(r,k) ↦ (2r+k-m-p-1, r-m+k)`.
It is a `Finset.filter` of a product box wide enough to contain the preimage of
every box point. -/
def hm23ShearPreimageBox (W V : ℕ) (m p : ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-((W : ℤ) + 2 * (V : ℤ) + |m| + |p| + 2))
      ((W : ℤ) + 2 * (V : ℤ) + |m| + |p| + 2) ×ˢ
    Finset.Icc (-((W : ℤ) + 2 * (V : ℤ) + |m| + |p| + 2))
      ((W : ℤ) + 2 * (V : ℤ) + |m| + |p| + 2)).filter
    (fun rk =>
      -(W : ℤ) ≤ 2 * rk.1 + rk.2 - m - p - 1 ∧
        2 * rk.1 + rk.2 - m - p - 1 ≤ (W : ℤ) - 1 ∧
      -(V : ℤ) ≤ rk.1 - m + rk.2 ∧ rk.1 - m + rk.2 ≤ (V : ℤ))

/-- Sheared-box change of variables (HM 2.3 piece 1, integer-core level): the
rectangular integer-core box sum equals the `(r,k)` sum over the shear-preimage
parallelogram, with the summand evaluated at the sheared coordinates. -/
theorem hm23IntegerCoreFiberBoxSumInt_eq_shear
    (W V : ℕ) (N z A B m p : ℤ) :
    hm23IntegerCoreFiberBoxSumInt W V N z A B =
      ∑ rk ∈ hm23ShearPreimageBox W V m p,
        hm23IntegerCoreSummandInt N z A B
          (2 * rk.1 + rk.2 - m - p - 1) (rk.1 - m + rk.2) := by
  classical
  unfold hm23IntegerCoreFiberBoxSumInt hm23ShearPreimageBox
  rw [← Finset.sum_product']
  symm
  -- The shear `(r,k) ↦ (2r+k-m-p-1, r-m+k)` is a bijection from the filtered
  -- preimage parallelogram onto the box `Icc(-W,W-1) ×ˢ Icc(-V,V)`.
  refine Finset.sum_nbij'
    (fun rk => (2 * rk.1 + rk.2 - m - p - 1, rk.1 - m + rk.2))
    (fun hK => (hK.1 - hK.2 + p + 1, m - p - 1 - hK.1 + 2 * hK.2))
    ?to_mem ?from_mem ?left ?right ?term
  · -- preimage box point ↦ box
    intro rk hrk
    rw [Finset.mem_filter] at hrk
    obtain ⟨_, hb1, hb2, hb3, hb4⟩ := hrk
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨hb1, hb2⟩, hb3, hb4⟩
  · -- box point ↦ preimage box
    intro hK hhK
    obtain ⟨h, K⟩ := hK
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hhK
    obtain ⟨⟨hh1, hh2⟩, hk1, hk2⟩ := hhK
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    simp only
    have hWnn : (0 : ℤ) ≤ (W : ℤ) := Int.natCast_nonneg W
    have hVnn : (0 : ℤ) ≤ (V : ℤ) := Int.natCast_nonneg V
    have hma : -|m| ≤ m ∧ m ≤ |m| := ⟨neg_abs_le m, le_abs_self m⟩
    have hpa : -|p| ≤ p ∧ p ≤ |p| := ⟨neg_abs_le p, le_abs_self p⟩
    have hmabs : 0 ≤ |m| := abs_nonneg m
    have hpabs : 0 ≤ |p| := abs_nonneg p
    refine ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, by omega, by omega, by omega, by omega⟩
  · -- left inverse on the preimage box
    intro rk _hrk
    obtain ⟨r, k⟩ := rk
    simp only [Prod.mk.injEq]
    refine ⟨by ring, by ring⟩
  · -- right inverse on the box
    intro hK _hhK
    obtain ⟨h, K⟩ := hK
    simp only [Prod.mk.injEq]
    refine ⟨by ring, by ring⟩
  · -- summand matches under the shear
    intro rk _hrk
    rfl

/-- HM 2.3 piece (1), assembled to canonical form: the `(r,k)` sum over the
shear-preimage parallelogram of the integer-core summand (evaluated at the
sheared coordinates with arbitrary cutoffs `A, B`) equals the canonical
integer-core sum, once the windows `W, V` dominate the explicit support bounds.
Chains the unimodular shear with the proven cutoff-invariance
(`…_cutoff_invariant`) and window-independence (`…_eq_canonical`). -/
theorem hm23ShearPreimageBox_sum_eq_canonical
    (W V : ℕ) (N z A B m p : ℤ)
    (hWc : Chapter10PF.thetaMulPFWindowPF N.toNat z ≤ W)
    (hVc : (Chapter10PF.thetaMulPFWindowPF N.toNat z : ℤ) ≤ (V : ℤ))
    (hVA : (W : ℤ) + |A| + 1 ≤ (V : ℤ))
    (hVB : (|B| + 1 : ℤ) ≤ (V : ℤ))
    (hWB : (2 * |z| + 2 * |N| + 2 * ((|B| + 1) * |z|) + 5 : ℤ) ≤ (W : ℤ)) :
    (∑ rk ∈ hm23ShearPreimageBox W V m p,
        hm23IntegerCoreSummandInt N z A B
          (2 * rk.1 + rk.2 - m - p - 1) (rk.1 - m + rk.2)) =
      hm23IntegerCoreCanonicalSumInt N z := by
  rw [← hm23IntegerCoreFiberBoxSumInt_eq_shear W V N z A B m p]
  rw [← hm23IntegerCoreFiberSumInt_eq_box W V N z A B]
  rw [hm23IntegerCoreFiberSumInt_cutoff_invariant W V N z A B hVA hVB hWB]
  exact hm23IntegerCoreFiberSumInt_eq_canonical W V N z hWc hVc

/-- Forward extraction from `Psi1` window membership: every member arises from a
filtered sigma tuple, so its source fields satisfy the four guard equations for
some intermediate exponents `E, E₁, E₂`. -/
theorem hm23_mem_Psi1WSS_imp
    (a z0 z1 e : ℤ) (x : HM23Psi1Source)
    (hx : x ∈ hm23Psi1WindowSourceSet a z0 z1 e) :
    ∃ E E₁ E₂ : ℤ,
      E - appellNumeratorExp z1 x.r = appellDenomExp a z1 x.r * x.k ∧
        jExp z0 90 x.i = E₁ ∧
        jExp (a + z0) 90 x.j = E₂ ∧
        jExp (a + z1) 90 x.l = e - E - E₁ - E₂ := by
  classical
  unfold hm23Psi1WindowSourceSet at hx
  rw [Finset.mem_image] at hx
  rcases hx with ⟨σ, hσfilt, hσeq⟩
  rw [Finset.mem_filter] at hσfilt
  rcases hσfilt with ⟨_hmem, happ, h1, h2, h3⟩
  refine ⟨hm23GW_E σ, hm23GW_E₁ σ, hm23GW_E₂ σ, ?_, ?_, ?_, ?_⟩
  · have hr : hm23GW_r σ = x.r := by
      rw [← hσeq]; rfl
    have hk : hm23GW_k σ = x.k := by rw [← hσeq]; rfl
    rw [← hr, ← hk]; exact happ
  · have hi : hm23GW_n₁ σ = x.i := by rw [← hσeq]; rfl
    rw [← hi]; exact h1
  · have hj : hm23GW_n₂ σ = x.j := by rw [← hσeq]; rfl
    rw [← hj]; exact h2
  · have hl : hm23GW_n₃ σ = x.l := by rw [← hσeq]; rfl
    rw [← hl]; exact h3

/-- Forward extraction from `Psi0` window membership (mirror). -/
theorem hm23_mem_Psi0WSS_imp
    (a z0 z1 e : ℤ) (y : HM23Psi0Source)
    (hy : y ∈ hm23Psi0WindowSourceSet a z0 z1 e) :
    ∃ E E₁ E₂ : ℤ,
      E - appellNumeratorExp z0 y.s = appellDenomExp a z0 y.s * y.k ∧
        jExp z1 90 y.h = E₁ ∧
        jExp (a + z0) 90 y.j = E₂ ∧
        jExp (a + z1) 90 y.l = e - E - E₁ - E₂ := by
  classical
  unfold hm23Psi0WindowSourceSet at hy
  rw [Finset.mem_image] at hy
  rcases hy with ⟨σ, hσfilt, hσeq⟩
  rw [Finset.mem_filter] at hσfilt
  rcases hσfilt with ⟨_hmem, happ, h1, h2, h3⟩
  refine ⟨hm23GW_E σ, hm23GW_E₁ σ, hm23GW_E₂ σ, ?_, ?_, ?_, ?_⟩
  · have hr : hm23GW_r σ = y.s := by rw [← hσeq]; rfl
    have hk : hm23GW_k σ = y.k := by rw [← hσeq]; rfl
    rw [← hr, ← hk]; exact happ
  · have hh : hm23GW_n₁ σ = y.h := by rw [← hσeq]; rfl
    rw [← hh]; exact h1
  · have hj : hm23GW_n₂ σ = y.j := by rw [← hσeq]; rfl
    rw [← hj]; exact h2
  · have hl : hm23GW_n₃ σ = y.l := by rw [← hσeq]; rfl
    rw [← hl]; exact h3

/-- Off-support direction (L1): if `T2Coord` is nonzero at a coordinate that lies
in the `Psi1` coordinate image, then that coordinate also lies in the `Psi0`
coordinate image.  Indeed nonvanishing of `T2Coord` forces the `z0`-side `Γ`
factor to be nonzero, which (via `Φ`) lands the source in the `Psi0` window. -/
theorem hm23Term2Coord_ne_zero_mem_Psi0Image
    (a z0 z1 e : ℤ) (hreg : hm23Nonsingular a z0 z1)
    (x : HM23Psi1Source) (hx : x ∈ hm23Psi1WindowSourceSet a z0 z1 e)
    (hT2 : hm23Term2CoordSummand a z0 z1 e (hm23Psi1Coord x) ≠ 0) :
    hm23Psi1Coord x ∈
      (hm23Psi0WindowSourceSet a z0 z1 e).image hm23Psi0Coord := by
  classical
  obtain ⟨E, E₁, E₂, happ, h1, h2, h3⟩ := hm23_mem_Psi1WSS_imp a z0 z1 e x hx
  -- extract the z0-side Γ ≠ 0 from `T2Coord ≠ 0`
  have hGamma0 :
      hm23Gamma (appellDenomExp a z0 (x.i - x.k)) x.k ≠ 0 := by
    intro hzero
    apply hT2
    unfold hm23Term2CoordSummand
    have hz :
        (hm23Psi1Coord x).z + (hm23Psi1Coord x).p - (hm23Psi1Coord x).r + 1 -
            (hm23Psi1Coord x).k = x.i - x.k := by
      simp only [hm23Psi1Coord, hm23Psi1_z, hm23Psi1_p]; ring
    have hk : (hm23Psi1Coord x).k = x.k := rfl
    rw [hz, hk, hzero]
    split_ifs <;> simp
  -- membership of Φ x in the Psi0 window, with matching coordinate
  have hmem :=
    hm23Psi1_phi_mem_Psi0WindowSourceSet_of_Gamma_ne_zero
      a z0 z1 e E E₁ E₂ x.l x.j x.i x.r x.k hreg happ h1 h2 h3 hGamma0
  rw [Finset.mem_image]
  refine ⟨{ s := x.i - x.k, k := x.k, h := x.r + x.k, j := x.j, l := x.l }, hmem, ?_⟩
  have hphi := hm23Psi1Coord_eq_Psi0Coord_phi x
  rw [hphi]
  cases x with
  | mk r k i j l => rfl

/-- Off-support direction (L2, mirror): if `T1Coord` is nonzero at a coordinate
in the `Psi0` coordinate image, then it lies in the `Psi1` coordinate image. -/
theorem hm23Term1Coord_ne_zero_mem_Psi1Image
    (a z0 z1 e : ℤ) (hreg : hm23Nonsingular a z0 z1)
    (y : HM23Psi0Source) (hy : y ∈ hm23Psi0WindowSourceSet a z0 z1 e)
    (hT1 : hm23Term1CoordSummand a z0 z1 e (hm23Psi0Coord y) ≠ 0) :
    hm23Psi0Coord y ∈
      (hm23Psi1WindowSourceSet a z0 z1 e).image hm23Psi1Coord := by
  classical
  obtain ⟨E, E₁, E₂, happ, h1, h2, h3⟩ := hm23_mem_Psi0WSS_imp a z0 z1 e y hy
  have hGamma1 :
      hm23Gamma (appellDenomExp a z1 (y.h - y.k)) y.k ≠ 0 := by
    intro hzero
    apply hT1
    unfold hm23Term1CoordSummand
    have hr : (hm23Psi0Coord y).r = y.h - y.k := rfl
    have hk : (hm23Psi0Coord y).k = y.k := rfl
    rw [hr, hk, hzero]
    split_ifs <;> simp
  have hmem :=
    hm23Psi0_phi_mem_Psi1WindowSourceSet_of_Gamma_ne_zero
      a z0 z1 e E E₁ E₂ y.l y.j y.h y.s y.k hreg happ h1 h2 h3 hGamma1
  rw [Finset.mem_image]
  refine ⟨{ r := y.h - y.k, k := y.k, i := y.s + y.k, j := y.j, l := y.l }, hmem, ?_⟩
  rw [hm23Psi1Coord_eq_Psi0Coord_phi
    { r := y.h - y.k, k := y.k, i := y.s + y.k, j := y.j, l := y.l }]
  show hm23Psi0Coord _ = hm23Psi0Coord y
  congr 1
  cases y with
  | mk s k h j l => simp [hm23Phi]

/-- Piece A assembled: the Γ-window difference is a single sum over the common
coordinate index set (the union of the two coordinate images) of the per-coord
difference `T1Coord − T2Coord`.  The off-support lemmas L1/L2 supply the two
zero-extensions that put both sides on the shared index set. -/
theorem hm23GammaWindowDifference_eq_coordImageSum
    (a z0 z1 e : ℤ) (hreg : hm23Nonsingular a z0 z1) :
    hm23GammaWindowFourFactorSum a z1 z0 (a + z0) (a + z1) e -
        hm23GammaWindowFourFactorSum a z0 z1 (a + z0) (a + z1) e =
      ∑ c ∈
          ((hm23Psi1WindowSourceSet a z0 z1 e).image hm23Psi1Coord ∪
            (hm23Psi0WindowSourceSet a z0 z1 e).image hm23Psi0Coord),
        (hm23Term1CoordSummand a z0 z1 e c -
          hm23Term2CoordSummand a z0 z1 e c) := by
  classical
  set I₁ := (hm23Psi1WindowSourceSet a z0 z1 e).image hm23Psi1Coord with hI₁
  set I₀ := (hm23Psi0WindowSourceSet a z0 z1 e).image hm23Psi0Coord with hI₀
  -- Step 1: Γ(z1,z0) = Σ_{I₁} T1Coord
  have hG1 :
      hm23GammaWindowFourFactorSum a z1 z0 (a + z0) (a + z1) e =
        ∑ c ∈ I₁, hm23Term1CoordSummand a z0 z1 e c := by
    rw [hm23GammaWindowFourFactorSum_eq_Psi1Source]
    rw [hm23Term1_transport_core a z0 z1 e (hm23Psi1WindowSourceSet a z0 z1 e)]
  -- Step 2: Γ(z0,z1) = Σ_{I₀} T2Coord
  have hG0 :
      hm23GammaWindowFourFactorSum a z0 z1 (a + z0) (a + z1) e =
        ∑ c ∈ I₀, hm23Term2CoordSummand a z0 z1 e c := by
    rw [hm23GammaWindowFourFactorSum_eq_Psi0Source]
    rw [hm23Term2_transport_core a z0 z1 e (hm23Psi0WindowSourceSet a z0 z1 e)]
  -- Step 3: extend T1Coord sum from I₁ to I₁ ∪ I₀
  have hext1 :
      (∑ c ∈ I₁, hm23Term1CoordSummand a z0 z1 e c) =
        ∑ c ∈ I₁ ∪ I₀, hm23Term1CoordSummand a z0 z1 e c := by
    refine Finset.sum_subset (Finset.subset_union_left) ?_
    intro c _hc hcnot
    by_contra hne
    -- c ∈ I₁ ∪ I₀ but ∉ I₁, with T1Coord c ≠ 0 ⇒ c ∈ I₁, contradiction
    have hcI₀ : c ∈ I₀ := by
      have := Finset.mem_union.mp _hc
      tauto
    rw [hI₀, Finset.mem_image] at hcI₀
    obtain ⟨y, hy, rfl⟩ := hcI₀
    have := hm23Term1Coord_ne_zero_mem_Psi1Image a z0 z1 e hreg y hy hne
    exact hcnot (by rw [hI₁]; exact this)
  -- Step 4: extend T2Coord sum from I₀ to I₁ ∪ I₀
  have hext2 :
      (∑ c ∈ I₀, hm23Term2CoordSummand a z0 z1 e c) =
        ∑ c ∈ I₁ ∪ I₀, hm23Term2CoordSummand a z0 z1 e c := by
    refine Finset.sum_subset (Finset.subset_union_right) ?_
    intro c _hc hcnot
    by_contra hne
    have hcI₁ : c ∈ I₁ := by
      have := Finset.mem_union.mp _hc
      tauto
    rw [hI₁, Finset.mem_image] at hcI₁
    obtain ⟨x, hx, rfl⟩ := hcI₁
    have := hm23Term2Coord_ne_zero_mem_Psi0Image a z0 z1 e hreg x hx hne
    exact hcnot (by rw [hI₀]; exact this)
  rw [hG1, hG0, hext1, hext2, ← Finset.sum_sub_distrib]

/-- Piece B, stage 1: peel the monomial `Q^{z0}` and split off the cube `J^3`
(supported on `≥ 0`) from the theta pair `j(z1−z0)·j(a+z0+z1)` (supported on
`≥ jLow₂ + jLow₃`).  The RHS coefficient becomes a finite sum over the cube
degree `eJ`, of the cube coefficient times the theta-pair coefficient. -/
theorem lcoeff_RHS_eq_cube_theta_pair_sum (a z0 z1 e : ℤ) :
    lcoeff (Qpow z0 * JOneLaurent ^ 3 * jLaurent (z1 - z0) 90 *
        jLaurent (a + z0 + z1) 90) e =
      ∑ eJ ∈ Finset.Icc (0 : ℤ)
          (e - z0 - (jCoeffLower (z1 - z0) 90 + jCoeffLower (a + z0 + z1) 90)),
        lcoeff (JOneLaurent ^ 3) eJ *
          lcoeff (jLaurent (z1 - z0) 90 * jLaurent (a + z0 + z1) 90)
            (e - z0 - eJ) := by
  have hassoc :
      Qpow z0 * JOneLaurent ^ 3 * jLaurent (z1 - z0) 90 *
          jLaurent (a + z0 + z1) 90 =
        Qpow z0 * (JOneLaurent ^ 3 *
          (jLaurent (z1 - z0) 90 * jLaurent (a + z0 + z1) 90)) := by
    ring
  rw [hassoc, lcoeff_Qpow_mul]
  rw [lcoeff_mul_eq_sum_Icc_of_coeff_zero_lt
    (JOneLaurent ^ 3) (jLaurent (z1 - z0) 90 * jLaurent (a + z0 + z1) 90)
    0 (jCoeffLower (z1 - z0) 90 + jCoeffLower (a + z0 + z1) 90) (e - z0)
    (fun n hn => lcoeff_JOneLaurent_pow_three_of_neg n hn)
    (fun n hn => lcoeff_mul_eq_zero_of_lt_add_lower
      (jLaurent (z1 - z0) 90) (jLaurent (a + z0 + z1) 90)
      (jCoeffLower (z1 - z0) 90) (jCoeffLower (a + z0 + z1) 90) n
      (lcoeff_jLaurent_eq_zero_of_lt_lower (z1 - z0) 90)
      (lcoeff_jLaurent_eq_zero_of_lt_lower (a + z0 + z1) 90) hn)]

/-- The common `(m, p)`-fiber sum, the meeting point of HM 2.3 pieces C and B.
For each pair of theta indices `m` (from `j(z1−z0;q)`) and `p` (from
`j(a+z0+z1;q)`), the residual cube degree is `Ncube = (e − z0 − jExp(z1−z0) m −
jExp(a+z0+z1) p) / 90`; the contribution is the cube coefficient
`thetaMulPFUnifiedCoeffPF Ncube 0` (zero unless the residual is a nonnegative
multiple of 90) weighted by the outer theta sign `(−1)^{m+p}`. -/
def hm23FiberSum (a z0 z1 e : ℤ) : ℚ :=
  ∑ m ∈ Finset.Icc (-(jCoeffWindow (z1 - z0) 90 (e - z0)))
      (jCoeffWindow (z1 - z0) 90 (e - z0)),
    ∑ p ∈ Finset.Icc (-(jCoeffWindow (a + z0 + z1) 90 (e - z0)))
        (jCoeffWindow (a + z0 + z1) 90 (e - z0)),
      let resid : ℤ := e - z0 - jExp (z1 - z0) 90 m - jExp (a + z0 + z1) 90 p
      if (90 : ℤ) ∣ resid ∧ 0 ≤ resid then
        negOnePowIntQ (m + p) *
          ((Chapter10PF.thetaMulPFUnifiedCoeffPF (resid / 90).toNat 0 : ℤ) : ℚ)
      else 0

/-- Conditional form of the cube coefficient: under `hPF`, `lcoeff (J₁^3) eJ`
equals the rational cast of `thetaMulPFUnifiedCoeffPF (eJ/90).toNat 0` when `eJ`
is a nonnegative multiple of 90, and `0` otherwise.  Packages the three branch
lemmas (`…_eq_unified`, `…_of_not_dvd`, `…_of_neg`). -/
theorem lcoeff_JOneLaurent_pow_three_eq_ite_unified
    (hPF :
      Chapter10PF.thetaMulPFSeriesCoeffPF =
        Chapter10PF.qPochInfPSCubeUPowerCoeffPF)
    (eJ : ℤ) :
    lcoeff (JOneLaurent ^ 3) eJ =
      (if (90 : ℤ) ∣ eJ ∧ 0 ≤ eJ then
        ((Chapter10PF.thetaMulPFUnifiedCoeffPF (eJ / 90).toNat 0 : ℤ) : ℚ)
      else 0) := by
  by_cases hdvd : (90 : ℤ) ∣ eJ
  · by_cases hnn : 0 ≤ eJ
    · rw [if_pos ⟨hdvd, hnn⟩]
      obtain ⟨n, hn⟩ := hdvd
      have hn_nonneg : 0 ≤ n := by nlinarith
      have hcast : eJ = ((90 * n.toNat : ℕ) : ℤ) := by
        rw [hn]; push_cast [Int.toNat_of_nonneg hn_nonneg]; ring
      have hidx : (eJ / 90).toNat = n.toNat := by
        rw [hn, Int.mul_ediv_cancel_left _ (by norm_num : (90 : ℤ) ≠ 0)]
      rw [hidx]
      rw [hcast, lcoeff_JOneLaurent_pow_three_eq_unified hPF n.toNat]
    · rw [if_neg (by tauto)]
      exact lcoeff_JOneLaurent_pow_three_of_neg eJ (by omega)
  · rw [if_neg (by tauto)]
    exact lcoeff_JOneLaurent_pow_three_of_not_dvd eJ hdvd

/-- The common `(m,p)`-window intermediate, expressed with the cube coefficient
in place of the unified PF coefficient.  Equals `hm23FiberSum` by the cube
conditional helper. -/
def hm23FiberSumCube (a z0 z1 e : ℤ) : ℚ :=
  ∑ m ∈ Finset.Icc (-(jCoeffWindow (z1 - z0) 90 (e - z0)))
      (jCoeffWindow (z1 - z0) 90 (e - z0)),
    ∑ p ∈ Finset.Icc (-(jCoeffWindow (a + z0 + z1) 90 (e - z0)))
        (jCoeffWindow (a + z0 + z1) 90 (e - z0)),
      negOnePowIntQ (m + p) *
        lcoeff (JOneLaurent ^ 3)
          (e - z0 - jExp (z1 - z0) 90 m - jExp (a + z0 + z1) 90 p)

theorem hm23FiberSum_eq_cube
    (hPF :
      Chapter10PF.thetaMulPFSeriesCoeffPF =
        Chapter10PF.qPochInfPSCubeUPowerCoeffPF)
    (a z0 z1 e : ℤ) :
    hm23FiberSum a z0 z1 e = hm23FiberSumCube a z0 z1 e := by
  unfold hm23FiberSum hm23FiberSumCube
  refine Finset.sum_congr rfl ?_
  intro m _hm
  refine Finset.sum_congr rfl ?_
  intro p _hp
  rw [lcoeff_JOneLaurent_pow_three_eq_ite_unified hPF]
  by_cases hc :
      (90 : ℤ) ∣ (e - z0 - jExp (z1 - z0) 90 m - jExp (a + z0 + z1) 90 p) ∧
        0 ≤ (e - z0 - jExp (z1 - z0) 90 m - jExp (a + z0 + z1) 90 p)
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc, mul_zero]

/-- Open the `j(w)·G` Laurent coefficient on a symmetric theta window `W` wide
enough to contain every theta root contributing to degree `y` (precisely: for
each `e₁` in the convolution range, `jCoeffWindow w 90 e₁ ≤ W`).  At degree `y`
it equals the sum over `Icc (-W) W` of `(−1)^m · lcoeff G (y − jExp w m)`. -/
theorem lcoeff_jLaurent_90_mul_eq_window
    (w y W : ℤ) (G : QLaurent) (LG : ℤ)
    (hG : ∀ n : ℤ, n < LG → lcoeff G n = 0)
    (hW : jCoeffWindow w 90 (y - LG) ≤ W) :
    lcoeff (jLaurent w 90 * G) y =
      ∑ m ∈ Finset.Icc (-W) W,
        negOnePowIntQ m * lcoeff G (y - jExp w 90 m) := by
  rw [lcoeff_mul_eq_sum_Icc_of_coeff_zero_lt (jLaurent w 90) G
    (jCoeffLower w 90) LG y
    (lcoeff_jLaurent_eq_zero_of_lt_lower w 90) hG]
  simp_rw [coeff_jLaurent]
  -- expand each jCoeff e₁ on the fixed window [-W, W] (root-capture)
  have hexp : ∀ e₁ ∈ Finset.Icc (jCoeffLower w 90) (y - LG),
      jCoeff w 90 e₁ =
        ∑ n ∈ Finset.Icc (-W) W,
          if jExp w 90 n = e₁ then negOnePowIntQ n else 0 := by
    intro e₁ he₁
    rw [Finset.mem_Icc] at he₁
    exact jCoeff_eq_sum_Icc_of_roots_le w 90 e₁ (y - LG) W (by norm_num)
      (by omega) hW
  rw [Finset.sum_congr rfl (fun e₁ he₁ => by rw [hexp e₁ he₁])]
  -- now: ∑ e₁ ∈ Icc, (∑ n ∈ box, [jExp n=e₁] sgn n) * lcoeff G (y-e₁)
  -- push lcoeff inside and swap order
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  -- ∑ e₁ ∈ Icc, (if jExp n=e₁ then sgn n else 0) * lcoeff G (y-e₁)
  --   = sgn n * lcoeff G (y - jExp n)
  by_cases hin : jExp w 90 n ∈ Finset.Icc (jCoeffLower w 90) (y - LG)
  · rw [Finset.sum_eq_single (jExp w 90 n)]
    · rw [if_pos rfl]
    · intro e₁ _he₁ hne
      rw [if_neg (by exact fun h => hne h.symm), zero_mul]
    · intro hnotin; exact absurd hin hnotin
  · -- jExp n ∉ Icc: every term zero, and RHS lcoeff G (y - jExp n) = 0
    rw [Finset.sum_eq_zero]
    · symm
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hin
      rcases hin with hlt | hgt
      · -- jExp n < jLow : impossible (theta exponent ≥ lower)
        exfalso
        have := jExp_lower_bound w 90 n (by norm_num)
        omega
      · -- jExp n > y - LG ⟹ y - jExp n < LG ⟹ lcoeff G = 0
        rw [hG (y - jExp w 90 n) (by omega), mul_zero]
    · intro e₁ he₁
      by_cases hroot : jExp w 90 n = e₁
      · exfalso; apply hin; rw [hroot]; exact he₁
      · rw [if_neg hroot, zero_mul]

/-- `j(w) · J₁^3` has its support bounded below by `jCoeffLower w 90`
(theta lower bound plus nonnegative cube). -/
theorem lcoeff_jLaurent_mul_cube_eq_zero_of_lt
    (w n : ℤ) (hn : n < jCoeffLower w 90) :
    lcoeff (jLaurent w 90 * JOneLaurent ^ 3) n = 0 := by
  have h0 : (jCoeffLower w 90) + 0 = jCoeffLower w 90 := by ring
  refine lcoeff_mul_eq_zero_of_lt_add_lower (jLaurent w 90) (JOneLaurent ^ 3)
    (jCoeffLower w 90) 0 n
    (lcoeff_jLaurent_eq_zero_of_lt_lower w 90)
    (fun k hk => lcoeff_JOneLaurent_pow_three_of_neg k hk) ?_
  rw [h0]; exact hn

/-- Correctly-windowed RHS bridge.  Opens the two theta factors of the HM 2.3
right-hand side against the cube `J₁^3` with the convolution-natural
(`y − LG`)-windows — which scale with `|a|`, unlike `hm23FiberSum`.  The result
is the double `(m, p)` sum of the outer sign times the cube coefficient at the
residual cube degree.  This is the genuine meeting point for the final HM 2.3
bridge (valid for all integer parameters). -/
theorem lcoeff_RHS_eq_correct_fiber (a z0 z1 e : ℤ) :
    lcoeff (Qpow z0 * JOneLaurent ^ 3 * jLaurent (z1 - z0) 90 *
        jLaurent (a + z0 + z1) 90) e =
      ∑ m ∈ Finset.Icc
          (-(jCoeffWindow (z1 - z0) 90
              (e - z0 - jCoeffLower (a + z0 + z1) 90)))
          (jCoeffWindow (z1 - z0) 90
              (e - z0 - jCoeffLower (a + z0 + z1) 90)),
        ∑ p ∈ Finset.Icc
            (-(jCoeffWindow (a + z0 + z1) 90
                (e - z0 - jExp (z1 - z0) 90 m)))
            (jCoeffWindow (a + z0 + z1) 90
                (e - z0 - jExp (z1 - z0) 90 m)),
          negOnePowIntQ (m + p) *
            lcoeff (JOneLaurent ^ 3)
              (e - z0 - jExp (z1 - z0) 90 m - jExp (a + z0 + z1) 90 p) := by
  have hassoc :
      Qpow z0 * JOneLaurent ^ 3 * jLaurent (z1 - z0) 90 *
          jLaurent (a + z0 + z1) 90 =
        Qpow z0 * (jLaurent (z1 - z0) 90 *
          (jLaurent (a + z0 + z1) 90 * JOneLaurent ^ 3)) := by ring
  rw [hassoc, lcoeff_Qpow_mul]
  rw [lcoeff_jLaurent_90_mul_eq_window (z1 - z0) (e - z0)
      (jCoeffWindow (z1 - z0) 90
        (e - z0 - jCoeffLower (a + z0 + z1) 90))
      (jLaurent (a + z0 + z1) 90 * JOneLaurent ^ 3)
      (jCoeffLower (a + z0 + z1) 90)
      (fun n hn => lcoeff_jLaurent_mul_cube_eq_zero_of_lt (a + z0 + z1) n hn)
      (le_refl _)]
  refine Finset.sum_congr rfl ?_
  intro m _hm
  rw [show negOnePowIntQ m *
        lcoeff (jLaurent (a + z0 + z1) 90 * JOneLaurent ^ 3)
          (e - z0 - jExp (z1 - z0) 90 m) =
      negOnePowIntQ m *
        ∑ p ∈ Finset.Icc
            (-(jCoeffWindow (a + z0 + z1) 90
                (e - z0 - jExp (z1 - z0) 90 m)))
            (jCoeffWindow (a + z0 + z1) 90
                (e - z0 - jExp (z1 - z0) 90 m)),
          negOnePowIntQ p *
            lcoeff (JOneLaurent ^ 3)
              ((e - z0 - jExp (z1 - z0) 90 m) - jExp (a + z0 + z1) 90 p)
      from by
        rw [lcoeff_jLaurent_90_mul_eq_window (a + z0 + z1)
          (e - z0 - jExp (z1 - z0) 90 m)
          (jCoeffWindow (a + z0 + z1) 90 (e - z0 - jExp (z1 - z0) 90 m))
          (JOneLaurent ^ 3) 0
          (fun n hn => lcoeff_JOneLaurent_pow_three_of_neg n hn)
          (by rw [sub_zero])]]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro p _hp
  rw [← mul_assoc, ← negOnePowIntQ_add]

/-- Piece A + per-coord difference lemma combined: the Γ-window difference equals
the sum, over the common coordinate index set, of the guarded outer-sign times
the integer-core summand at the sheared coordinates. -/
theorem hm23GammaWindowDifference_eq_coordImageSum_integerCore
    (a z0 z1 e : ℤ) (hreg : hm23Nonsingular a z0 z1) :
    hm23GammaWindowFourFactorSum a z1 z0 (a + z0) (a + z1) e -
        hm23GammaWindowFourFactorSum a z0 z1 (a + z0) (a + z1) e =
      ∑ c ∈
          ((hm23Psi1WindowSourceSet a z0 z1 e).image hm23Psi1Coord ∪
            (hm23Psi0WindowSourceSet a z0 z1 e).image hm23Psi0Coord),
        (if hm23TermOutExp a z0 z1 c.m c.p c.z c.N = e ∧
            c.N = hm23Ncoord c.m c.p c.z c.r c.k then
          negOnePowIntQ (c.m + c.p) *
            ((hm23IntegerCoreSummandInt (hm23Ncoord c.m c.p c.z c.r c.k) c.z
              (c.p + (a + z1 - 1) / 90)
              (c.z + c.p - c.m + (a + z0 - 1) / 90)
              (2 * c.r + c.k - c.m - c.p - 1)
              (c.r - c.m + c.k) : ℤ) : ℚ)
        else 0) := by
  rw [hm23GammaWindowDifference_eq_coordImageSum a z0 z1 e hreg]
  refine Finset.sum_congr rfl ?_
  intro c _hc
  exact hm23Term1_sub_Term2_CoordSummand a z0 z1 e hreg c

/-- Window parameters making the shear-preimage box dominate the support of the
integer-core summand at a given fiber `(m,p,z,N)` with cutoffs `A,B`. -/
def hm23FiberW (z N B : ℤ) : ℕ :=
  (2 * |z| + 2 * |N| + 2 * ((|B| + 1) * |z|) + 5 +
    (Chapter10PF.thetaMulPFWindowPF N.toNat z : ℤ)).toNat

def hm23FiberV (z N A B : ℤ) : ℕ :=
  ((hm23FiberW z N B : ℤ) + |A| + |B| + 2 +
    (Chapter10PF.thetaMulPFWindowPF N.toNat z : ℤ)).toNat

theorem hm23FiberW_nonneg_expr (z N B : ℤ) :
    (0 : ℤ) ≤ 2 * |z| + 2 * |N| + 2 * ((|B| + 1) * |z|) + 5 +
      (Chapter10PF.thetaMulPFWindowPF N.toNat z : ℤ) := by
  have := abs_nonneg z
  have := abs_nonneg N
  have := abs_nonneg B
  have h1 : (0 : ℤ) ≤ (|B| + 1) * |z| :=
    mul_nonneg (by have := abs_nonneg B; linarith) (abs_nonneg z)
  have h2 : (0 : ℤ) ≤ (Chapter10PF.thetaMulPFWindowPF N.toNat z : ℤ) :=
    Int.natCast_nonneg _
  linarith

theorem hm23FiberW_cast (z N B : ℤ) :
    (hm23FiberW z N B : ℤ) =
      2 * |z| + 2 * |N| + 2 * ((|B| + 1) * |z|) + 5 +
        (Chapter10PF.thetaMulPFWindowPF N.toNat z : ℤ) := by
  unfold hm23FiberW
  exact Int.toNat_of_nonneg (hm23FiberW_nonneg_expr z N B)

theorem hm23FiberV_cast (z N A B : ℤ) :
    (hm23FiberV z N A B : ℤ) =
      (hm23FiberW z N B : ℤ) + |A| + |B| + 2 +
        (Chapter10PF.thetaMulPFWindowPF N.toNat z : ℤ) := by
  unfold hm23FiberV
  refine Int.toNat_of_nonneg ?_
  have := abs_nonneg A
  have := abs_nonneg B
  have h2 : (0 : ℤ) ≤ (Chapter10PF.thetaMulPFWindowPF N.toNat z : ℤ) :=
    Int.natCast_nonneg _
  have h3 : (0 : ℤ) ≤ (hm23FiberW z N B : ℤ) := Int.natCast_nonneg _
  linarith

/-- The chosen window parameters satisfy the five shear-collapse hypotheses. -/
theorem hm23Fiber_shear_hyps (z N A B : ℤ) :
    Chapter10PF.thetaMulPFWindowPF N.toNat z ≤ hm23FiberW z N B ∧
      (Chapter10PF.thetaMulPFWindowPF N.toNat z : ℤ) ≤ (hm23FiberV z N A B : ℤ) ∧
      (hm23FiberW z N B : ℤ) + |A| + 1 ≤ (hm23FiberV z N A B : ℤ) ∧
      (|B| + 1 : ℤ) ≤ (hm23FiberV z N A B : ℤ) ∧
      (2 * |z| + 2 * |N| + 2 * ((|B| + 1) * |z|) + 5 : ℤ) ≤
        (hm23FiberW z N B : ℤ) := by
  have hW := hm23FiberW_cast z N B
  have hV := hm23FiberV_cast z N A B
  have hwin : (0 : ℤ) ≤ (Chapter10PF.thetaMulPFWindowPF N.toNat z : ℤ) :=
    Int.natCast_nonneg _
  have hA := abs_nonneg A
  have hB := abs_nonneg B
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : (Chapter10PF.thetaMulPFWindowPF N.toNat z : ℤ) ≤ (hm23FiberW z N B : ℤ) := by
      rw [hW]
      have := abs_nonneg z; have := abs_nonneg N
      have h1 : (0 : ℤ) ≤ (|B| + 1) * |z| :=
        mul_nonneg (by linarith) (abs_nonneg z)
      linarith
    exact_mod_cast this
  · rw [hV, hW]; have := abs_nonneg z; have := abs_nonneg N
    have h1 : (0 : ℤ) ≤ (|B| + 1) * |z| := mul_nonneg (by linarith) (abs_nonneg z)
    linarith
  · rw [hV]; linarith
  · rw [hV]; have h3 : (0 : ℤ) ≤ (hm23FiberW z N B : ℤ) := Int.natCast_nonneg _; linarith
  · rw [hW]; linarith

/-- Per-`(m,p)` fiber form of the right-hand side cube/theta coefficient.
At `z = 0`, the guard `hm23TermOutExp a z0 z1 m p 0 N = e` forces `90 * N = resid`
(no `(m+p)` shift), so the unified PF cube coefficient at residual `resid`
coincides with the canonical integer-core sum `hm23IntegerCoreCanonicalSumInt N 0`
read at `N = resid / 90`.  This identifies the RHS cube term with the `z = 0`
canonical fiber. -/
theorem hm23_rhs_cube_eq_canonical_z0
    (resid : ℤ) :
    (if (90 : ℤ) ∣ resid ∧ 0 ≤ resid then
        ((Chapter10PF.thetaMulPFUnifiedCoeffPF (resid / 90).toNat 0 : ℤ) : ℚ)
      else 0) =
      (if (90 : ℤ) ∣ resid ∧ 0 ≤ resid then
        ((hm23IntegerCoreCanonicalSumInt (resid / 90) 0 : ℤ) : ℚ)
      else 0) := by
  by_cases hc : (90 : ℤ) ∣ resid ∧ 0 ≤ resid
  · rw [if_pos hc, if_pos hc]
    obtain ⟨hdvd, hnn⟩ := hc
    have hq_nonneg : 0 ≤ resid / 90 := Int.ediv_nonneg hnn (by norm_num)
    conv_rhs =>
      rw [show (resid / 90) = ((resid / 90).toNat : ℤ) from
        (Int.toNat_of_nonneg hq_nonneg).symm,
        hm23IntegerCoreCanonicalSumInt_of_nat (resid / 90).toNat 0,
        hm23IntegerCoreCanonical_eq_unified (resid / 90).toNat 0]
  · rw [if_neg hc, if_neg hc]

/-- At `z = 0`, the guard `hm23TermOutExp a z0 z1 m p 0 N = e` forces the cube
residual `e - z0 - jExp(z1−z0) m - jExp(a+z0+z1) p` to equal `90 N` exactly (no
`(m+p)` reindex).  This is the index reconciliation between the LHS canonical
fiber `N` and the RHS cube degree, used in the `z = 0` branch of the converse
capture. -/
theorem hm23_z0_guard_resid_eq_ninetyN
    (a z0 z1 e m p N : ℤ)
    (hg : hm23TermOutExp a z0 z1 m p 0 N = e) :
    e - z0 - jExp (z1 - z0) 90 m - jExp (a + z0 + z1) 90 p = 90 * N := by
  rw [jExp90_eq_hmTri, jExp90_eq_hmTri]
  unfold hm23TermOutExp at hg
  linarith [hg]

/-! ### HM 2.3 converse-capture helper lemmas

The four notation-free omega-closable window/box guard facts (blueprint §2), the
shear inverse, and the generic support-equivalence sum identity used to extend
two finite sums to their union and discard the added zero terms. -/

theorem hm23_guard_imp_pos_h_box
    {Lo Hi Wc E h : ℤ}
    (hW : Wc = Hi - Lo + 1) (hLo : Lo ≤ E) (hHi : E ≤ Hi) (hh : h = E - Lo) :
    0 ≤ h ∧ h < Wc := by omega

theorem hm23_pos_h_box_imp_guard
    {Lo Hi Wc E h : ℤ}
    (hW : Wc = Hi - Lo + 1) (hh₀ : 0 ≤ h) (hh₁ : h < Wc) (hE : E = Lo + h) :
    Lo ≤ E ∧ E ≤ Hi := by omega

theorem hm23_guard_imp_neg_h_box
    {Lo Hi Wc E h : ℤ}
    (hW : Wc = Hi - Lo + 1) (hLo : Lo ≤ E) (hHi : E ≤ Hi) (hh : h = E - Hi - 1) :
    -Wc ≤ h ∧ h ≤ -1 := by omega

theorem hm23_neg_h_box_imp_guard
    {Lo Hi Wc E h : ℤ}
    (hW : Wc = Hi - Lo + 1) (hh₀ : -Wc ≤ h) (hh₁ : h ≤ -1) (hE : E = Hi + 1 + h) :
    Lo ≤ E ∧ E ≤ Hi := by omega

theorem hm23_shear_inv_r (m p r k : ℤ) :
    r = (2*r + k - m - p - 1) - (r - m + k) + p + 1 := by ring

theorem hm23_shear_inv_k (m p r k : ℤ) :
    k = 2*(r - m + k) - (2*r + k - m - p - 1) + m - p - 1 := by ring

/-- Two finite sums whose supports coincide (`f x ≠ 0 → (x ∈ s ↔ x ∈ t)`) have
equal totals.  Extend both to `s ∪ t`, killing the added zero terms. -/
theorem hm23_Finset_sum_eq_of_mem_iff_on_support
    {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (s t : Finset α) (f : α → β)
    (h : ∀ x, f x ≠ 0 → (x ∈ s ↔ x ∈ t)) :
    (∑ x ∈ s, f x) = ∑ x ∈ t, f x := by
  classical
  have hs : (∑ x ∈ s, f x) = ∑ x ∈ s ∪ t, f x := by
    refine Finset.sum_subset Finset.subset_union_left ?_
    intro x hxst hxs
    by_contra hf
    exact hxs ((h x hf).mpr ((Finset.mem_union.mp hxst).resolve_left hxs))
  have ht : (∑ x ∈ t, f x) = ∑ x ∈ s ∪ t, f x := by
    refine Finset.sum_subset Finset.subset_union_right ?_
    intro x hxst hxt
    by_contra hf
    exact hxt ((h x hf).mp ((Finset.mem_union.mp hxst).resolve_right hxt))
  rw [hs, ht]

/-- The fiber `N`-coordinate equals the integer-core summand's internal
q-exponent `triIntPF (h − z) + K·z` under the shear `h = 2r+k−m−p−1,
K = r−m+k`.  This is the algebraic heart linking the `(r,k)` source index to
the `(h,K)` integer-core index. -/
theorem hm23_Ncoord_eq_shear_exp (m p z r k : ℤ) :
    hm23Ncoord m p z r k =
      Chapter10PF.triIntPF ((2*r + k - m - p - 1) - z) + (r - m + k) * z := by
  unfold hm23Ncoord
  have e2 : (2:ℤ) ≠ 0 := by norm_num
  apply mul_left_cancel₀ e2
  have hr  := two_mul_hmTri r
  have hi  := two_mul_hmTri (z+p-r+1)
  have hj  := two_mul_hmTri (r-m)
  have hl  := two_mul_hmTri (p-r+m-k)
  have hm' := two_mul_hmTri m
  have hp' := two_mul_hmTri p
  have hRHS := Chapter10PF.two_mul_triIntPF ((2*r + k - m - p - 1) - z)
  linear_combination hr + hi + hj + hl - hm' - hp' - hRHS

/-- The integer-core summand at the sheared coordinates vanishes unless
`N = Ncoord (m,p,z,r,k)`, because its internal q-exponent condition is exactly
`Ncoord = N` (by `hm23_Ncoord_eq_shear_exp`). -/
theorem hm23_ICS_shear_eq_zero_of_ne
    (N z A B m p r k : ℤ) (hne : N ≠ hm23Ncoord m p z r k) :
    hm23IntegerCoreSummandInt N z A B
        (2*r + k - m - p - 1) (r - m + k) = 0 := by
  unfold hm23IntegerCoreSummandInt
  rw [if_neg]
  rw [hm23_Ncoord_eq_shear_exp m p z r k] at hne
  exact fun h => hne h.symm

/-- The `N = Ncoord` conjunct of the coordinate-union guard is redundant: when it
fails the integer-core summand already vanishes, so the guarded summand equals
the same expression guarded only by `TermOut = e` (with `N` in place of the
forced `Ncoord`). -/
theorem hm23_guard_collapse
    (a z0 z1 e : ℤ) (c : HM23Coord) :
    (if hm23TermOutExp a z0 z1 c.m c.p c.z c.N = e ∧
        c.N = hm23Ncoord c.m c.p c.z c.r c.k then
      negOnePowIntQ (c.m + c.p) *
        ((hm23IntegerCoreSummandInt (hm23Ncoord c.m c.p c.z c.r c.k) c.z
          (c.p + (a + z1 - 1) / 90)
          (c.z + c.p - c.m + (a + z0 - 1) / 90)
          (2 * c.r + c.k - c.m - c.p - 1)
          (c.r - c.m + c.k) : ℤ) : ℚ)
    else 0) =
    (if hm23TermOutExp a z0 z1 c.m c.p c.z c.N = e then
      negOnePowIntQ (c.m + c.p) *
        ((hm23IntegerCoreSummandInt c.N c.z
          (c.p + (a + z1 - 1) / 90)
          (c.z + c.p - c.m + (a + z0 - 1) / 90)
          (2 * c.r + c.k - c.m - c.p - 1)
          (c.r - c.m + c.k) : ℤ) : ℚ)
    else 0) := by
  by_cases hT : hm23TermOutExp a z0 z1 c.m c.p c.z c.N = e
  · by_cases hN : c.N = hm23Ncoord c.m c.p c.z c.r c.k
    · rw [if_pos ⟨hT, hN⟩, if_pos hT, hN]
    · rw [if_neg (fun h => hN h.2), if_pos hT]
      rw [hm23_ICS_shear_eq_zero_of_ne c.N c.z _ _ c.m c.p c.r c.k hN]
      simp
  · rw [if_neg (fun h => hT h.1), if_neg hT]

/-! ### HM 2.3 converse capture: source-coordinate shear identities

For a `Psi1` source `(r,k,i,j,l)` the coordinate fields are `m = r-j`,
`p = j+l+k`, so the shear coordinates are `h = 2r+k-m-p-1 = r-l-1` and
`K = r-m+k = j+k`.  For a `Psi0` source `(s,k,h,j,l)` with `m = h-j-k`,
`p = j+l+k`, `r-field = h-k`, we get `h_shear = h-k-l-1`, `K = j+k`.  These
identities make the support-bound `|K| ≤ |N|+|z|+1` directly available on the
window image and are the algebraic glue for the membership argument. -/

theorem hm23Psi1Coord_shear_h (x : HM23Psi1Source) :
    2 * (hm23Psi1Coord x).r + (hm23Psi1Coord x).k -
        (hm23Psi1Coord x).m - (hm23Psi1Coord x).p - 1 = x.r - x.l - 1 := by
  simp only [hm23Psi1Coord, hm23Psi1_m, hm23Psi1_p]; ring

theorem hm23Psi1Coord_shear_K (x : HM23Psi1Source) :
    (hm23Psi1Coord x).r - (hm23Psi1Coord x).m + (hm23Psi1Coord x).k =
      x.j + x.k := by
  simp only [hm23Psi1Coord, hm23Psi1_m]; ring

theorem hm23Psi0Coord_shear_h (x : HM23Psi0Source) :
    2 * (hm23Psi0Coord x).r + (hm23Psi0Coord x).k -
        (hm23Psi0Coord x).m - (hm23Psi0Coord x).p - 1 = x.h - x.k - x.l - 1 := by
  simp only [hm23Psi0Coord, hm23Psi0_m, hm23Psi0_p, hm23Psi0_r]; ring

theorem hm23Psi0Coord_shear_K (x : HM23Psi0Source) :
    (hm23Psi0Coord x).r - (hm23Psi0Coord x).m + (hm23Psi0Coord x).k =
      x.j + x.k := by
  simp only [hm23Psi0Coord, hm23Psi0_m, hm23Psi0_r]; ring

/-- The guarded coord summand `F` used in the HM 2.3 union sum:
`if TermOut = e then sign · ICS(c.N, c.z, A(c), B(c), sheared c) else 0`
(after the redundant `N = Ncoord` conjunct is collapsed by
`hm23_guard_collapse`).  Packaged as a named function so the union sum and the
per-fiber box sum are literally the same summand. -/
def hm23CapF (a z0 z1 e : ℤ) (c : HM23Coord) : ℚ :=
  if hm23TermOutExp a z0 z1 c.m c.p c.z c.N = e then
    negOnePowIntQ (c.m + c.p) *
      ((hm23IntegerCoreSummandInt c.N c.z
        (c.p + (a + z1 - 1) / 90)
        (c.z + c.p - c.m + (a + z0 - 1) / 90)
        (2 * c.r + c.k - c.m - c.p - 1)
        (c.r - c.m + c.k) : ℤ) : ℚ)
  else 0

/-- Embedding of an `(r,k)` box point into a coordinate at a fixed fiber. -/
def hm23CoordOfFiber (m p z N : ℤ) (rk : ℤ × ℤ) : HM23Coord :=
  { m := m, p := p, z := z, N := N, r := rk.1, k := rk.2 }

theorem hm23CoordOfFiber_injective (m p z N : ℤ) :
    Function.Injective (hm23CoordOfFiber m p z N) := by
  intro a b hab
  unfold hm23CoordOfFiber at hab
  injection hab with _ _ _ _ h1 h2
  exact Prod.ext h1 h2

/-- Per-fiber box sum of the capture summand collapses to the canonical
integer-core sum (times the outer sign), at the fiber's general cutoffs
`A = p + (a+z1−1)/90`, `B = z + p − m + (a+z0−1)/90`.  The guard `TermOut = e`
is constant on the fiber and factors out; the `(r,k)`-box sum of the integer
core summand reduces to `hm23IntegerCoreCanonicalSumInt N z` by the banked
shear/cutoff-invariance lemma. -/
theorem hm23CapF_box_sum_eq_canonical
    (a z0 z1 e m p z N : ℤ) (W V : ℕ)
    (hWc : Chapter10PF.thetaMulPFWindowPF N.toNat z ≤ W)
    (hVc : (Chapter10PF.thetaMulPFWindowPF N.toNat z : ℤ) ≤ (V : ℤ))
    (hVA : (W : ℤ) + |p + (a + z1 - 1) / 90| + 1 ≤ (V : ℤ))
    (hVB : (|z + p - m + (a + z0 - 1) / 90| + 1 : ℤ) ≤ (V : ℤ))
    (hWB : (2 * |z| + 2 * |N| +
        2 * ((|z + p - m + (a + z0 - 1) / 90| + 1) * |z|) + 5 : ℤ) ≤ (W : ℤ)) :
    (∑ rk ∈ hm23ShearPreimageBox W V m p,
      hm23CapF a z0 z1 e (hm23CoordOfFiber m p z N rk)) =
      (if hm23TermOutExp a z0 z1 m p z N = e then
        negOnePowIntQ (m + p) *
          ((hm23IntegerCoreCanonicalSumInt N z : ℤ) : ℚ)
      else 0) := by
  classical
  set A : ℤ := p + (a + z1 - 1) / 90 with hA
  set B : ℤ := z + p - m + (a + z0 - 1) / 90 with hB
  by_cases hT : hm23TermOutExp a z0 z1 m p z N = e
  · rw [if_pos hT]
    have hbox :
        (∑ rk ∈ hm23ShearPreimageBox W V m p,
          hm23CapF a z0 z1 e (hm23CoordOfFiber m p z N rk)) =
          ∑ rk ∈ hm23ShearPreimageBox W V m p,
            negOnePowIntQ (m + p) *
              ((hm23IntegerCoreSummandInt N z A B
                (2 * rk.1 + rk.2 - m - p - 1) (rk.1 - m + rk.2) : ℤ) : ℚ) := by
      refine Finset.sum_congr rfl ?_
      intro rk _hrk
      unfold hm23CapF hm23CoordOfFiber
      simp only [hT, if_true]
      rfl
    rw [hbox, ← Finset.mul_sum]
    congr 1
    rw [← hm23ShearPreimageBox_sum_eq_canonical W V N z A B m p
      hWc hVc hVA hVB hWB]
    push_cast
    rfl
  · rw [if_neg hT]
    refine Finset.sum_eq_zero ?_
    intro rk _hrk
    unfold hm23CapF hm23CoordOfFiber
    simp only [hT, if_false]

/-- Enlarged fiber box half-width, dominating both the `hm23Fiber_shear_hyps`
lower bounds AND the support-membership bound `|h| ≤ Wbig` (numerically the
linear majorant `|N|+2|z|+|z|(|A|+|B|+1)+2`).  The extra `|z|·(|A|+|B|+1)`
addend over `hm23FiberW` is what guarantees forward membership for general
cutoffs `A,B`. -/
def hm23FiberWbig (z N A B : ℤ) : ℕ :=
  (2 * |z| + 2 * |N| + 2 * ((|B| + 1) * |z|) + 5 +
    (Chapter10PF.thetaMulPFWindowPF N.toNat z : ℤ) +
    2 * (|z| * (|A| + |B| + 1)) + 2 * (|z| * |z|)).toNat

def hm23FiberVbig (z N A B : ℤ) : ℕ :=
  ((hm23FiberWbig z N A B : ℤ) + |A| + |B| + 2 +
    (Chapter10PF.thetaMulPFWindowPF N.toNat z : ℤ)).toNat

theorem hm23FiberWbig_cast (z N A B : ℤ) :
    (hm23FiberWbig z N A B : ℤ) =
      2 * |z| + 2 * |N| + 2 * ((|B| + 1) * |z|) + 5 +
        (Chapter10PF.thetaMulPFWindowPF N.toNat z : ℤ) +
        2 * (|z| * (|A| + |B| + 1)) + 2 * (|z| * |z|) := by
  unfold hm23FiberWbig
  refine Int.toNat_of_nonneg ?_
  have h1 : (0 : ℤ) ≤ (|B| + 1) * |z| :=
    mul_nonneg (by have := abs_nonneg B; linarith) (abs_nonneg z)
  have h2 : (0 : ℤ) ≤ (Chapter10PF.thetaMulPFWindowPF N.toNat z : ℤ) :=
    Int.natCast_nonneg _
  have h3 : (0 : ℤ) ≤ |z| * (|A| + |B| + 1) :=
    mul_nonneg (abs_nonneg z) (by have := abs_nonneg A; have := abs_nonneg B; linarith)
  have h4 : (0 : ℤ) ≤ |z| * |z| := mul_nonneg (abs_nonneg z) (abs_nonneg z)
  have := abs_nonneg z; have := abs_nonneg N
  linarith

theorem hm23FiberVbig_cast (z N A B : ℤ) :
    (hm23FiberVbig z N A B : ℤ) =
      (hm23FiberWbig z N A B : ℤ) + |A| + |B| + 2 +
        (Chapter10PF.thetaMulPFWindowPF N.toNat z : ℤ) := by
  unfold hm23FiberVbig
  refine Int.toNat_of_nonneg ?_
  have h1 : (0 : ℤ) ≤ (hm23FiberWbig z N A B : ℤ) := Int.natCast_nonneg _
  have h2 : (0 : ℤ) ≤ (Chapter10PF.thetaMulPFWindowPF N.toNat z : ℤ) :=
    Int.natCast_nonneg _
  have := abs_nonneg A; have := abs_nonneg B
  linarith

theorem hm23FiberBig_shear_hyps (z N A B : ℤ) :
    Chapter10PF.thetaMulPFWindowPF N.toNat z ≤ hm23FiberWbig z N A B ∧
      (Chapter10PF.thetaMulPFWindowPF N.toNat z : ℤ) ≤ (hm23FiberVbig z N A B : ℤ) ∧
      (hm23FiberWbig z N A B : ℤ) + |A| + 1 ≤ (hm23FiberVbig z N A B : ℤ) ∧
      (|B| + 1 : ℤ) ≤ (hm23FiberVbig z N A B : ℤ) ∧
      (2 * |z| + 2 * |N| + 2 * ((|B| + 1) * |z|) + 5 : ℤ) ≤
        (hm23FiberWbig z N A B : ℤ) := by
  have hW := hm23FiberWbig_cast z N A B
  have hV := hm23FiberVbig_cast z N A B
  have hwin : (0 : ℤ) ≤ (Chapter10PF.thetaMulPFWindowPF N.toNat z : ℤ) :=
    Int.natCast_nonneg _
  have hA := abs_nonneg A
  have hB := abs_nonneg B
  have hzz : (0 : ℤ) ≤ |z| := abs_nonneg z
  have hNN : (0 : ℤ) ≤ |N| := abs_nonneg N
  have hBz : (0 : ℤ) ≤ (|B| + 1) * |z| := mul_nonneg (by linarith) hzz
  have hABz : (0 : ℤ) ≤ |z| * (|A| + |B| + 1) := mul_nonneg hzz (by linarith)
  have hzz2 : (0 : ℤ) ≤ |z| * |z| := mul_nonneg hzz hzz
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : (Chapter10PF.thetaMulPFWindowPF N.toNat z : ℤ) ≤ (hm23FiberWbig z N A B : ℤ) := by
      rw [hW]; linarith
    exact_mod_cast this
  · rw [hV, hW]; linarith
  · rw [hV]; linarith
  · rw [hV]; have h3 : (0 : ℤ) ≤ (hm23FiberWbig z N A B : ℤ) := Int.natCast_nonneg _; linarith
  · rw [hW]; linarith

/-- Abstract quadratic-to-linear bound: if `u·(u+1) ≤ C + D·|u|` with `0 ≤ C`
and `0 ≤ D`, then `|u| ≤ C + D + 1`.  Used to turn the integer-core exponent
identity into a linear bound on the shear coordinate. -/
theorem hm23_quad_to_linear (u C D : ℤ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (h : u * (u + 1) ≤ C + D * |u|) :
    |u| ≤ C + D + 1 := by
  have hau : |u| * |u| = u * u := by
    rw [← abs_mul, abs_mul_self]
  have hu2 : |u| * |u| ≤ u * (u + 1) + |u| := by
    rw [hau]
    rcases le_total 0 u with hu0 | hu0
    · rw [abs_of_nonneg hu0]; nlinarith
    · rw [abs_of_nonpos hu0]; nlinarith
  have hau0 : 0 ≤ |u| := abs_nonneg u
  by_contra hcon
  push_neg at hcon
  nlinarith [hau0, hcon, hC, hD, hu2, h, mul_nonneg hau0 hau0]

/-- The total source exponent of the reconstructed `Psi1` source equals the
fiber `TermOut` exponent, on the integer-core support `N = Ncoord`. -/
theorem hm23Term1SourceExp_sourceOfCoord (a z0 z1 : ℤ) (c : HM23Coord)
    (hN : c.N = hm23Ncoord c.m c.p c.z c.r c.k) :
    hm23Term1SourceExp a z0 z1 (hm23Psi1SourceOfCoord c) =
      hm23TermOutExp a z0 z1 c.m c.p c.z c.N := by
  cases c with
  | mk m p z N r k =>
    simp only at hN
    have hExp := hm23Psi1_exponent_identity a z0 z1 r k (z + p - r + 1)
      (r - m) (p - r + m - k)
    -- LHS source has fields (r, k, i=z+p-r+1, j=r-m, l=p-r+m-k)
    show hm23Term1SourceExp a z0 z1
        ⟨r, k, z + p - r + 1, r - m, p - r + m - k⟩ =
      hm23TermOutExp a z0 z1 m p z N
    unfold hm23Term1SourceExp hm23TermOutExp
    have hmm : hm23Psi1_m r (r - m) = m := by unfold hm23Psi1_m; ring
    have hpp : hm23Psi1_p (r - m) (p - r + m - k) k = p := by
      unfold hm23Psi1_p; ring
    have hzz : hm23Psi1_z r (z + p - r + 1) (r - m) (p - r + m - k) k = z := by
      unfold hm23Psi1_z; ring
    have hNN : hm23Psi1_N r k (z + p - r + 1) (r - m) (p - r + m - k) = N := by
      rw [hm23Psi1_N_eq_Ncoord, hmm, hpp, hzz, hN]
    rw [show
        90 * (hmTri r + hmTri (z + p - r + 1) + hmTri (r - m) +
            hmTri (p - r + m - k) + k * (r - 1)) +
          z1 * r + k * (a + z1) + z0 * (z + p - r + 1) +
            (a + z0) * (r - m) + (a + z1) * (p - r + m - k) =
        90 * (hmTri (hm23Psi1_m r (r - m)) +
            hmTri (hm23Psi1_p (r - m) (p - r + m - k) k) +
            hm23Psi1_N r k (z + p - r + 1) (r - m) (p - r + m - k)) +
          z0 * (1 - hm23Psi1_m r (r - m) +
            hm23Psi1_p (r - m) (p - r + m - k) k +
            hm23Psi1_z r (z + p - r + 1) (r - m) (p - r + m - k) k) +
          z1 * (hm23Psi1_m r (r - m) +
            hm23Psi1_p (r - m) (p - r + m - k) k) +
          a * hm23Psi1_p (r - m) (p - r + m - k) k
      from hExp]
    rw [hmm, hpp, hzz, hNN]

/-- Right inverse of `hm23Psi1SourceOfCoord` on the integer-core support:
when `c.N` equals the shear exponent `Ncoord`, reconstructing the `Psi1` source
and re-applying `hm23Psi1Coord` returns `c`. -/
theorem hm23Psi1Coord_sourceOfCoord (c : HM23Coord)
    (hN : c.N = hm23Ncoord c.m c.p c.z c.r c.k) :
    hm23Psi1Coord (hm23Psi1SourceOfCoord c) = c := by
  cases c with
  | mk m p z N r k =>
    simp only at hN
    show hm23Psi1Coord (hm23Psi1SourceOfCoord ⟨m, p, z, N, r, k⟩) = ⟨m, p, z, N, r, k⟩
    unfold hm23Psi1SourceOfCoord hm23Psi1Coord
    have hNc : hm23Psi1_N r k (z + p - r + 1) (r - m) (p - r + m - k) = N := by
      rw [hm23Psi1_N_eq_Ncoord]
      simp only [hm23Psi1_m, hm23Psi1_p, hm23Psi1_z]
      rw [hN]; ring_nf
    congr 1 <;>
      first
        | exact hNc
        | (simp only [hm23Psi1_m, hm23Psi1_p, hm23Psi1_z]; ring)

/-- Converse capture, `Γ_{z1}` branch: a coordinate `c` on the integer-core
support (`N = Ncoord`) with `TermOut = e` and a nonzero `z1`-side `Γ` lies in
the `Psi1` coordinate image, hence in the coordinate union.  Reconstructs the
natural `Psi1` source and discharges the four window guards from the `TermOut`
identity (e-sum guard) via the banked surjectivity. -/
theorem hm23_coord_mem_Psi1Image_of_Gamma1_ne_zero
    (a z0 z1 e : ℤ) (hreg : hm23Nonsingular a z0 z1) (c : HM23Coord)
    (hN : c.N = hm23Ncoord c.m c.p c.z c.r c.k)
    (hT : hm23TermOutExp a z0 z1 c.m c.p c.z c.N = e)
    (hG1 : hm23Gamma (appellDenomExp a z1 c.r) c.k ≠ 0) :
    c ∈ (hm23Psi1WindowSourceSet a z0 z1 e).image hm23Psi1Coord := by
  classical
  -- reconstruct the Psi0 config whose Φ⁻¹ is the natural Psi1 source of c
  set s : ℤ := c.z + c.p - c.r + 1 - c.k with hs
  set h : ℤ := c.r + c.k with hh
  set j : ℤ := c.r - c.m with hj
  set l : ℤ := c.p - c.r + c.m - c.k with hl
  set k : ℤ := c.k with hk
  set E : ℤ := appellNumeratorExp z0 s + appellDenomExp a z0 s * k with hE
  set E₁ : ℤ := jExp z1 90 h with hE1
  set E₂ : ℤ := jExp (a + z0) 90 j with hE2
  have happ : E - appellNumeratorExp z0 s = appellDenomExp a z0 s * k := by
    rw [hE]; ring
  have h1 : jExp z1 90 h = E₁ := by rw [hE1]
  have h2 : jExp (a + z0) 90 j = E₂ := by rw [hE2]
  -- e-sum guard: jExp(a+z1) l = e - E - E₁ - E₂, from Term2SourceExp = TermOut = e
  have hterm2 : hm23Term2SourceExp a z0 z1 ⟨s, k, h, j, l⟩ = e := by
    rw [hm23Term2SourceExp_phi_eq_term1SourceExp]
    have hri : (h - k) = c.r := by rw [hh, hk]; ring
    have hsk : (s + k) = c.z + c.p - c.r + 1 := by rw [hs, hk]; ring
    -- {r:=h-k, k:=k, i:=s+k, j:=j, l:=l} = hm23Psi1SourceOfCoord c
    have hsrc :
        (⟨h - k, k, s + k, j, l⟩ : HM23Psi1Source) = hm23Psi1SourceOfCoord c := by
      rw [hri, hsk]; simp only [hm23Psi1SourceOfCoord, hk, hj, hl]
    rw [hsrc, hm23Term1SourceExp_sourceOfCoord a z0 z1 c hN, hT]
  have h3 : jExp (a + z1) 90 l = e - E - E₁ - E₂ := by
    have hw := hm23Term2SourceExp_eq_window_parts a z0 z1 s k h j l
    rw [hterm2] at hw
    rw [hE, hE1, hE2]; omega
  have hri : (h - k) = c.r := by rw [hh, hk]; ring
  have hG1' : hm23Gamma (appellDenomExp a z1 (h - k)) k ≠ 0 := by
    rw [hri, hk]; exact hG1
  have hmem :=
    hm23Psi0_phi_mem_Psi1WindowSourceSet_of_Gamma_ne_zero
      a z0 z1 e E E₁ E₂ l j h s k hreg happ h1 h2 h3 hG1'
  rw [Finset.mem_image]
  refine ⟨⟨h - k, k, s + k, j, l⟩, hmem, ?_⟩
  have hri2 : (h - k) = c.r := by rw [hh, hk]; ring
  have hsk : (s + k) = c.z + c.p - c.r + 1 := by rw [hs, hk]; ring
  have hsrc :
      (⟨h - k, k, s + k, j, l⟩ : HM23Psi1Source) = hm23Psi1SourceOfCoord c := by
    rw [hri2, hsk]; simp only [hm23Psi1SourceOfCoord, hk, hj, hl]
  rw [hsrc, hm23Psi1Coord_sourceOfCoord c hN]

/-- Right inverse of `hm23Psi0SourceOfCoord` on the integer-core support. -/
theorem hm23Psi0Coord_sourceOfCoord (c : HM23Coord)
    (hN : c.N = hm23Ncoord c.m c.p c.z c.r c.k) :
    hm23Psi0Coord (hm23Psi0SourceOfCoord c) = c := by
  cases c with
  | mk m p z N r k =>
    simp only at hN
    show hm23Psi0Coord (hm23Psi0SourceOfCoord ⟨m, p, z, N, r, k⟩) = ⟨m, p, z, N, r, k⟩
    unfold hm23Psi0SourceOfCoord hm23Psi0Coord
    have hNc : hm23Psi0_N (z + p - r + 1 - k) k (r + k) (r - m)
        (p - r + m - k) = N := by
      rw [hm23Psi0_N_eq_Ncoord]
      simp only [hm23Psi0_m, hm23Psi0_p, hm23Psi0_z, hm23Psi0_r]
      rw [hN]; ring_nf
    congr 1 <;>
      first
        | exact hNc
        | (simp only [hm23Psi0_m, hm23Psi0_p, hm23Psi0_z, hm23Psi0_r]; ring)

/-- The total source exponent of the reconstructed `Psi0` source equals the
fiber `TermOut` exponent, on the integer-core support. -/
theorem hm23Term2SourceExp_sourceOfCoord (a z0 z1 : ℤ) (c : HM23Coord)
    (hN : c.N = hm23Ncoord c.m c.p c.z c.r c.k) :
    hm23Term2SourceExp a z0 z1 (hm23Psi0SourceOfCoord c) =
      hm23TermOutExp a z0 z1 c.m c.p c.z c.N := by
  cases c with
  | mk m p z N r k =>
    simp only at hN
    have hExp := hm23Psi0_exponent_identity a z0 z1 (z + p - r + 1 - k) k
      (r + k) (r - m) (p - r + m - k)
    show hm23Term2SourceExp a z0 z1
        ⟨z + p - r + 1 - k, k, r + k, r - m, p - r + m - k⟩ =
      hm23TermOutExp a z0 z1 m p z N
    unfold hm23Term2SourceExp hm23TermOutExp
    have hmm : hm23Psi0_m (r + k) (r - m) k = m := by unfold hm23Psi0_m; ring
    have hpp : hm23Psi0_p (r - m) (p - r + m - k) k = p := by
      unfold hm23Psi0_p; ring
    have hzz : hm23Psi0_z (z + p - r + 1 - k) (r + k) (r - m) (p - r + m - k) k
        = z := by unfold hm23Psi0_z; ring
    have hNN : hm23Psi0_N (z + p - r + 1 - k) k (r + k) (r - m) (p - r + m - k)
        = N := by
      rw [hm23Psi0_N_eq_Ncoord, hmm, hpp, hzz, hN]
      simp only [hm23Psi0_m, hm23Psi0_p, hm23Psi0_z, hm23Psi0_r]; ring_nf
    rw [show
        90 * (hmTri (z + p - r + 1 - k) + hmTri (r + k) + hmTri (r - m) +
            hmTri (p - r + m - k) + k * ((z + p - r + 1 - k) - 1)) +
          z0 * (z + p - r + 1 - k) + k * (a + z0) + z1 * (r + k) +
            (a + z0) * (r - m) + (a + z1) * (p - r + m - k) =
        90 * (hmTri (hm23Psi0_m (r + k) (r - m) k) +
            hmTri (hm23Psi0_p (r - m) (p - r + m - k) k) +
            hm23Psi0_N (z + p - r + 1 - k) k (r + k) (r - m) (p - r + m - k)) +
          z0 * (1 - hm23Psi0_m (r + k) (r - m) k +
            hm23Psi0_p (r - m) (p - r + m - k) k +
            hm23Psi0_z (z + p - r + 1 - k) (r + k) (r - m) (p - r + m - k) k) +
          z1 * (hm23Psi0_m (r + k) (r - m) k +
            hm23Psi0_p (r - m) (p - r + m - k) k) +
          a * hm23Psi0_p (r - m) (p - r + m - k) k
      from hExp]
    rw [hmm, hpp, hzz, hNN]

/-- Converse capture, `Γ_{z0}` branch (mirror): a coordinate on the integer-core
support with `TermOut = e` and a nonzero `z0`-side `Γ` lies in the `Psi0`
coordinate image. -/
theorem hm23_coord_mem_Psi0Image_of_Gamma0_ne_zero
    (a z0 z1 e : ℤ) (hreg : hm23Nonsingular a z0 z1) (c : HM23Coord)
    (hN : c.N = hm23Ncoord c.m c.p c.z c.r c.k)
    (hT : hm23TermOutExp a z0 z1 c.m c.p c.z c.N = e)
    (hG0 : hm23Gamma (appellDenomExp a z0 (c.z + c.p - c.r + 1 - c.k)) c.k ≠ 0) :
    c ∈ (hm23Psi0WindowSourceSet a z0 z1 e).image hm23Psi0Coord := by
  classical
  set i : ℤ := c.z + c.p - c.r + 1 with hi
  set r : ℤ := c.r with hr
  set j : ℤ := c.r - c.m with hj
  set l : ℤ := c.p - c.r + c.m - c.k with hl
  set k : ℤ := c.k with hk
  set E : ℤ := appellNumeratorExp z1 r + appellDenomExp a z1 r * k with hE
  set E₁ : ℤ := jExp z0 90 i with hE1
  set E₂ : ℤ := jExp (a + z0) 90 j with hE2
  have happ : E - appellNumeratorExp z1 r = appellDenomExp a z1 r * k := by
    rw [hE]; ring
  have h1 : jExp z0 90 i = E₁ := by rw [hE1]
  have h2 : jExp (a + z0) 90 j = E₂ := by rw [hE2]
  have hterm1 : hm23Term1SourceExp a z0 z1 ⟨r, k, i, j, l⟩ = e := by
    have hsrc :
        (⟨r, k, i, j, l⟩ : HM23Psi1Source) = hm23Psi1SourceOfCoord c := by
      rw [hr, hk, hi, hj, hl]; rfl
    rw [hsrc, hm23Term1SourceExp_sourceOfCoord a z0 z1 c hN, hT]
  have h3 : jExp (a + z1) 90 l = e - E - E₁ - E₂ := by
    have hw := hm23Term1SourceExp_eq_window_parts a z0 z1 r k i j l
    rw [hterm1] at hw
    rw [hE, hE1, hE2]; omega
  have hik : (i - k) = c.z + c.p - c.r + 1 - c.k := by rw [hi, hk]
  have hG0' : hm23Gamma (appellDenomExp a z0 (i - k)) k ≠ 0 := by
    rw [hik, hk]; exact hG0
  have hmem :=
    hm23Psi1_phi_mem_Psi0WindowSourceSet_of_Gamma_ne_zero
      a z0 z1 e E E₁ E₂ l j i r k hreg happ h1 h2 h3 hG0'
  rw [Finset.mem_image]
  refine ⟨⟨i - k, k, r + k, j, l⟩, hmem, ?_⟩
  -- {s:=i-k,k:=k,h:=r+k,j:=j,l:=l} = hm23Psi0SourceOfCoord c
  have hsrc :
      (⟨i - k, k, r + k, j, l⟩ : HM23Psi0Source) = hm23Psi0SourceOfCoord c := by
    rw [hik]
    simp only [hm23Psi0SourceOfCoord, hr, hk, hj, hl]
  rw [hsrc, hm23Psi0Coord_sourceOfCoord c hN]

/-- Bound `K·z` from a one-sided box constraint, both signs of `z`.  Helper for
the support-membership bound, isolated to keep `nlinarith` light. -/
theorem hm23_Kz_abs_bound (z A B u K : ℤ)
    (hzABu : -|u| ≤ u ∧ u ≤ |u|)
    (hA : -|A| ≤ A ∧ A ≤ |A|) (hB : -|B| ≤ B ∧ B ≤ |B|) (hu0 : 0 ≤ |u|)
    (hKr : (B + 1 ≤ K ∧ K ≤ u + z + A) ∨ (u + z + A + 1 ≤ K ∧ K ≤ B)) :
    -(|z| * (|u| + |z| + |A| + |B| + 1)) ≤ K * z ∧
      K * z ≤ |z| * (|u| + |z| + |A| + |B| + 1) := by
  have hzr : -|z| ≤ z ∧ z ≤ |z| := ⟨neg_abs_le z, le_abs_self z⟩
  have hzz : (0 : ℤ) ≤ |z| := abs_nonneg z
  constructor <;>
    rcases hKr with ⟨hK1, hK2⟩ | ⟨hK1, hK2⟩ <;>
      rcases le_total 0 z with hz0 | hz0
  · rw [abs_of_nonneg hz0] at *
    nlinarith [hK1, hK2, hzABu.1, hzABu.2, hA.1, hA.2, hB.1, hB.2, hz0, hu0, hzr.1, hzr.2]
  · rw [abs_of_nonpos hz0] at *
    nlinarith [hK1, hK2, hzABu.1, hzABu.2, hA.1, hA.2, hB.1, hB.2, hz0, hu0, hzr.1, hzr.2]
  · rw [abs_of_nonneg hz0] at *
    nlinarith [hK1, hK2, hzABu.1, hzABu.2, hA.1, hA.2, hB.1, hB.2, hz0, hu0, hzr.1, hzr.2]
  · rw [abs_of_nonpos hz0] at *
    nlinarith [hK1, hK2, hzABu.1, hzABu.2, hA.1, hA.2, hB.1, hB.2, hz0, hu0, hzr.1, hzr.2]
  · rw [abs_of_nonneg hz0] at *
    nlinarith [hK1, hK2, hzABu.1, hzABu.2, hA.1, hA.2, hB.1, hB.2, hz0, hu0, hzr.1, hzr.2]
  · rw [abs_of_nonpos hz0] at *
    nlinarith [hK1, hK2, hzABu.1, hzABu.2, hA.1, hA.2, hB.1, hB.2, hz0, hu0, hzr.1, hzr.2]
  · rw [abs_of_nonneg hz0] at *
    nlinarith [hK1, hK2, hzABu.1, hzABu.2, hA.1, hA.2, hB.1, hB.2, hz0, hu0, hzr.1, hzr.2]
  · rw [abs_of_nonpos hz0] at *
    nlinarith [hK1, hK2, hzABu.1, hzABu.2, hA.1, hA.2, hB.1, hB.2, hz0, hu0, hzr.1, hzr.2]

set_option maxHeartbeats 1000000 in
/-- Support membership: a nonzero integer-core summand at general cutoffs `A,B`
forces the `(h,K)` index into the enlarged fiber box bounds.  Forward direction
of the converse-capture, driven purely from the support (no window guards):
the indicator nonzero pins `K` between `B` and `h+A`, and the exponent identity
`(h−z)(h−z+1) = 2N − 2Kz` then bounds `|h|` by the linear majorant baked into
`hm23FiberWbig`. -/
theorem hm23IntegerCoreSummandInt_mem_bigBox
    (N z A B h K : ℤ)
    (hne : hm23IntegerCoreSummandInt N z A B h K ≠ 0) :
    -(hm23FiberWbig z N A B : ℤ) ≤ h ∧ h ≤ (hm23FiberWbig z N A B : ℤ) - 1 ∧
      -(hm23FiberVbig z N A B : ℤ) ≤ K ∧ K ≤ (hm23FiberVbig z N A B : ℤ) := by
  have hexp : Chapter10PF.triIntPF (h - z) + K * z = N := by
    by_contra hc; rw [hm23IntegerCoreSummandInt, if_neg hc] at hne; exact hne rfl
  have hind :
      ((if K ≤ h + A then (1 : ℤ) else 0) - (if K ≤ B then (1 : ℤ) else 0)) ≠ 0 := by
    intro h0
    rw [hm23IntegerCoreSummandInt, if_pos hexp, h0, mul_zero] at hne; exact hne rfl
  -- exponent identity doubled
  have htwo := Chapter10PF.two_mul_triIntPF (h - z)
  have e2 : (h - z) * (h - z + 1) + 2 * K * z = 2 * N := by
    have h' : 2 * (Chapter10PF.triIntPF (h - z) + K * z) = 2 * N := by rw [hexp]
    rw [mul_add, htwo] at h'; linarith
  -- K pinned between B and h+A (in one of the two orders)
  have hKrange : (B + 1 ≤ K ∧ K ≤ h + A) ∨ (h + A + 1 ≤ K ∧ K ≤ B) := by
    by_cases hKhA : K ≤ h + A
    · by_cases hKB : K ≤ B
      · exact absurd (by simp only [if_pos hKhA, if_pos hKB]; ring) hind
      · exact Or.inl ⟨by omega, hKhA⟩
    · by_cases hKB : K ≤ B
      · exact Or.inr ⟨by omega, hKB⟩
      · exact absurd (by simp only [if_neg hKhA, if_neg hKB]; ring) hind
  -- abs facts
  have haz : -|z| ≤ z ∧ z ≤ |z| := ⟨neg_abs_le z, le_abs_self z⟩
  have haN : -|N| ≤ N ∧ N ≤ |N| := ⟨neg_abs_le N, le_abs_self N⟩
  have haA : -|A| ≤ A ∧ A ≤ |A| := ⟨neg_abs_le A, le_abs_self A⟩
  have haB : -|B| ≤ B ∧ B ≤ |B| := ⟨neg_abs_le B, le_abs_self B⟩
  have hzz : (0 : ℤ) ≤ |z| := abs_nonneg z
  have hNN : (0 : ℤ) ≤ |N| := abs_nonneg N
  have hAA : (0 : ℤ) ≤ |A| := abs_nonneg A
  have hBB : (0 : ℤ) ≤ |B| := abs_nonneg B
  have hWcast := hm23FiberWbig_cast z N A B
  have hVcast := hm23FiberVbig_cast z N A B
  have hwin : (0 : ℤ) ≤ (Chapter10PF.thetaMulPFWindowPF N.toNat z : ℤ) :=
    Int.natCast_nonneg _
  have hWnn : (0 : ℤ) ≤ (hm23FiberWbig z N A B : ℤ) := Int.natCast_nonneg _
  -- The key abstraction: u = h - z satisfies u(u+1) = 2N - 2Kz, and the K-range
  -- bounds `K*z` by `|z|*(|u| + |z| + |A| + |B| + 1)`.
  set u : ℤ := h - z with hu
  have hau0 : 0 ≤ |u| := abs_nonneg u
  have hubound : -|u| ≤ u ∧ u ≤ |u| := ⟨neg_abs_le u, le_abs_self u⟩
  -- bound K*z using the helper
  have hKr' : (B + 1 ≤ K ∧ K ≤ u + z + A) ∨ (u + z + A + 1 ≤ K ∧ K ≤ B) := by
    rcases hKrange with ⟨hK1, hK2⟩ | ⟨hK1, hK2⟩
    · exact Or.inl ⟨hK1, by rw [hu]; linarith⟩
    · exact Or.inr ⟨by rw [hu]; linarith, hK2⟩
  obtain ⟨hKz_lb, hKz_ub⟩ := hm23_Kz_abs_bound z A B u K hubound haA haB hau0 hKr'
  -- u(u+1) = 2N - 2Kz ≤ C + D·|u| with C = 2|N|+2|z|²+2|z|(|A|+|B|+1), D = 2|z|.
  set C : ℤ := 2 * |N| + 2 * (|z| * |z|) + 2 * (|z| * (|A| + |B| + 1)) with hCdef
  set D : ℤ := 2 * |z| with hDdef
  have hCnn : 0 ≤ C := by
    rw [hCdef]
    have h1 : 0 ≤ |z| * |z| := mul_nonneg hzz hzz
    have h2 : 0 ≤ |z| * (|A| + |B| + 1) := mul_nonneg hzz (by linarith)
    linarith
  have hDnn : 0 ≤ D := by rw [hDdef]; linarith
  have hueq : u * (u + 1) = 2 * N - 2 * (K * z) := by rw [hu]; linarith [e2]
  have hquad : u * (u + 1) ≤ C + D * |u| := by
    rw [hueq, hCdef, hDdef]
    nlinarith [hKz_lb, haN.1, haN.2, hzz, hau0]
  have huabs : |u| ≤ C + D + 1 := hm23_quad_to_linear u C D hCnn hDnn hquad
  -- |h| ≤ |u| + |z| ≤ C + D + 1 + |z| ≤ W0
  have hh_abs : -(C + D + 1 + |z|) ≤ h ∧ h ≤ C + D + 1 + |z| := by
    have hu1 := hubound.1
    have hu2 := hubound.2
    have hzlo := haz.1
    have hzhi := haz.2
    rw [hu] at hu1 hu2
    omega
  rw [hVcast, hWcast]
  have hW0 : C + D + 1 + |z| + 1 ≤ 2 * |z| + 2 * |N| + 2 * ((|B| + 1) * |z|) + 5 +
      (Chapter10PF.thetaMulPFWindowPF N.toNat z : ℤ) +
      2 * (|z| * (|A| + |B| + 1)) + 2 * (|z| * |z|) := by
    rw [hCdef, hDdef]
    have hBz : |z| ≤ (|B| + 1) * |z| := by nlinarith [hzz, hBB]
    nlinarith [hwin, hzz, hBz]
  refine ⟨by linarith [hh_abs.1, hW0], by linarith [hh_abs.2, hW0], ?_, ?_⟩
  · -- K lower bound
    rcases hKrange with ⟨hK1, hK2⟩ | ⟨hK1, hK2⟩ <;>
      nlinarith [hh_abs.1, hh_abs.2, hW0, hK1, hK2, haA.1, haA.2, haB.1, haB.2, hwin, hzz, hCnn, hDnn, hWnn]
  · -- K upper bound
    rcases hKrange with ⟨hK1, hK2⟩ | ⟨hK1, hK2⟩ <;>
      nlinarith [hh_abs.1, hh_abs.2, hW0, hK1, hK2, haA.1, haA.2, haB.1, haB.2, hwin, hzz, hCnn, hDnn, hWnn]

/-- On the integer-core support, `c.N` is forced to equal the shear exponent
`Ncoord`. -/
theorem hm23_capF_ne_zero_imp_N_eq_Ncoord (a z0 z1 e : ℤ) (c : HM23Coord)
    (hF : hm23CapF a z0 z1 e c ≠ 0) :
    hm23TermOutExp a z0 z1 c.m c.p c.z c.N = e ∧
      c.N = hm23Ncoord c.m c.p c.z c.r c.k := by
  unfold hm23CapF at hF
  by_cases hT : hm23TermOutExp a z0 z1 c.m c.p c.z c.N = e
  · refine ⟨hT, ?_⟩
    rw [if_pos hT] at hF
    -- ICS(c.N, ...) ≠ 0 forces the exponent guard
    have hICS : hm23IntegerCoreSummandInt c.N c.z
        (c.p + (a + z1 - 1) / 90)
        (c.z + c.p - c.m + (a + z0 - 1) / 90)
        (2 * c.r + c.k - c.m - c.p - 1) (c.r - c.m + c.k) ≠ 0 := by
      intro h0; rw [h0] at hF; simp at hF
    by_contra hNe
    exact hICS (hm23_ICS_shear_eq_zero_of_ne c.N c.z _ _ c.m c.p c.r c.k hNe)
  · rw [if_neg hT] at hF; exact absurd rfl hF

/-- Forward capture: a coordinate with nonzero capture summand has its `(r,k)`
inside the enlarged shear-preimage box of its own fiber. -/
theorem hm23_capF_ne_zero_imp_mem_box
    (a z0 z1 e : ℤ) (c : HM23Coord) (hF : hm23CapF a z0 z1 e c ≠ 0) :
    (c.r, c.k) ∈ hm23ShearPreimageBox
      (hm23FiberWbig c.z c.N (c.p + (a + z1 - 1) / 90)
        (c.z + c.p - c.m + (a + z0 - 1) / 90))
      (hm23FiberVbig c.z c.N (c.p + (a + z1 - 1) / 90)
        (c.z + c.p - c.m + (a + z0 - 1) / 90)) c.m c.p := by
  classical
  obtain ⟨hT, _hNc⟩ := hm23_capF_ne_zero_imp_N_eq_Ncoord a z0 z1 e c hF
  have hICS : hm23IntegerCoreSummandInt c.N c.z
      (c.p + (a + z1 - 1) / 90)
      (c.z + c.p - c.m + (a + z0 - 1) / 90)
      (2 * c.r + c.k - c.m - c.p - 1) (c.r - c.m + c.k) ≠ 0 := by
    unfold hm23CapF at hF; rw [if_pos hT] at hF
    intro h0; rw [h0] at hF; simp at hF
  set A : ℤ := c.p + (a + z1 - 1) / 90 with hA
  set B : ℤ := c.z + c.p - c.m + (a + z0 - 1) / 90 with hB
  obtain ⟨hh1, hh2, hK1, hK2⟩ :=
    hm23IntegerCoreSummandInt_mem_bigBox c.N c.z A B
      (2 * c.r + c.k - c.m - c.p - 1) (c.r - c.m + c.k) hICS
  set W : ℕ := hm23FiberWbig c.z c.N A B with hW
  set V : ℕ := hm23FiberVbig c.z c.N A B with hV
  unfold hm23ShearPreimageBox
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  have hWnn : (0 : ℤ) ≤ (W : ℤ) := Int.natCast_nonneg _
  have hVnn : (0 : ℤ) ≤ (V : ℤ) := Int.natCast_nonneg _
  have hma : -|c.m| ≤ c.m ∧ c.m ≤ |c.m| := ⟨neg_abs_le c.m, le_abs_self c.m⟩
  have hpa : -|c.p| ≤ c.p ∧ c.p ≤ |c.p| := ⟨neg_abs_le c.p, le_abs_self c.p⟩
  have hmabs : 0 ≤ |c.m| := abs_nonneg c.m
  have hpabs : 0 ≤ |c.p| := abs_nonneg c.p
  refine ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, by omega, by omega, by omega, by omega⟩

/-- Combined converse capture: a coordinate with nonzero capture summand lies in
the coordinate union.  The nonzero summand forces `TermOut = e`, `N = Ncoord`,
and (via the `Γ`-difference identity) a nonzero `z1`- or `z0`-side `Γ`, landing
`c` in the `Psi1` resp. `Psi0` coordinate image. -/
theorem hm23_capF_ne_zero_imp_mem_coordUnion
    (a z0 z1 e : ℤ) (hreg : hm23Nonsingular a z0 z1) (c : HM23Coord)
    (hF : hm23CapF a z0 z1 e c ≠ 0) :
    c ∈ ((hm23Psi1WindowSourceSet a z0 z1 e).image hm23Psi1Coord ∪
      (hm23Psi0WindowSourceSet a z0 z1 e).image hm23Psi0Coord) := by
  classical
  obtain ⟨hT, hNc⟩ := hm23_capF_ne_zero_imp_N_eq_Ncoord a z0 z1 e c hF
  -- ICS ≠ 0, so the Γ-difference is nonzero, so one Γ is nonzero
  have hICS : hm23IntegerCoreSummandInt c.N c.z
      (c.p + (a + z1 - 1) / 90)
      (c.z + c.p - c.m + (a + z0 - 1) / 90)
      (2 * c.r + c.k - c.m - c.p - 1) (c.r - c.m + c.k) ≠ 0 := by
    unfold hm23CapF at hF; rw [if_pos hT] at hF
    intro h0; rw [h0] at hF; simp at hF
  have hgamma :=
    hm23_coord_fiber_term_eq_integerCoreSummandInt
      a z0 z1 c.m c.p c.z c.r c.k hreg
  -- LHS sign*(Γ_z1 - Γ_z0) = ICS(Ncoord,...) ; with hNc, Ncoord = c.N
  have hdiff :
      hm23Gamma (appellDenomExp a z1 c.r) c.k -
        hm23Gamma (appellDenomExp a z0 (c.z + c.p - c.r + 1 - c.k)) c.k ≠ 0 := by
    intro h0
    apply hICS
    have hrw : ((hm23IntegerCoreSummandInt (hm23Ncoord c.m c.p c.z c.r c.k) c.z
        (c.p + (a + z1 - 1) / 90)
        (c.z + c.p - c.m + (a + z0 - 1) / 90)
        (2 * c.r + c.k - c.m - c.p - 1)
        (c.r - c.m + c.k) : ℤ) : ℚ) = 0 := by
      rw [← hgamma, h0, mul_zero]
    rw [← hNc] at hrw
    exact_mod_cast hrw
  rw [Finset.mem_union]
  by_cases hG1 : hm23Gamma (appellDenomExp a z1 c.r) c.k ≠ 0
  · exact Or.inl
      (hm23_coord_mem_Psi1Image_of_Gamma1_ne_zero a z0 z1 e hreg c hNc hT hG1)
  · push_neg at hG1
    have hG0 : hm23Gamma (appellDenomExp a z0 (c.z + c.p - c.r + 1 - c.k)) c.k ≠ 0 := by
      intro h0; apply hdiff; rw [hG1, h0, sub_zero]
    exact Or.inr
      (hm23_coord_mem_Psi0Image_of_Gamma0_ne_zero a z0 z1 e hreg c hNc hT hG0)

/-- The canonical integer-core sum vanishes whenever `z ≠ 0`: for `N ≥ 0` it is
the unified PF coefficient (which vanishes off the constant `z`-slice), and for
`N < 0` it is identically zero. -/
theorem hm23IntegerCoreCanonicalSumInt_eq_zero_of_z_ne_zero
    (N z : ℤ) (hz : z ≠ 0) :
    hm23IntegerCoreCanonicalSumInt N z = 0 := by
  rcases lt_or_ge N 0 with hN | hN
  · exact hm23IntegerCoreCanonicalSumInt_eq_zero_of_neg hN
  · lift N to ℕ using hN with n
    rw [hm23IntegerCoreCanonicalSumInt_of_nat,
      hm23IntegerCoreCanonical_eq_unified,
      Chapter10PF.thetaMulPFUnifiedCoeffPF_nonconstant_vanish n hz]

/-- Per-fiber capture.  For a fixed fiber key `(m,p,z,N)`, the capture sum over
the coordinate-union members of that fiber equals the canonical value
`sign · canonical(N,z)` (guarded by `TermOut = e`).  This is the converse-capture
assembled from the forward (`…_imp_mem_box`) and converse
(`…_imp_mem_coordUnion`) support membership directions plus the box-sum collapse
(`hm23CapF_box_sum_eq_canonical`). -/
theorem hm23_capF_fiber_sum_eq_canonical
    (a z0 z1 e m p z N : ℤ) (hreg : hm23Nonsingular a z0 z1) :
    (∑ c ∈ ((hm23Psi1WindowSourceSet a z0 z1 e).image hm23Psi1Coord ∪
        (hm23Psi0WindowSourceSet a z0 z1 e).image hm23Psi0Coord).filter
        (fun c => c.m = m ∧ c.p = p ∧ c.z = z ∧ c.N = N),
      hm23CapF a z0 z1 e c) =
      (if hm23TermOutExp a z0 z1 m p z N = e then
        negOnePowIntQ (m + p) *
          ((hm23IntegerCoreCanonicalSumInt N z : ℤ) : ℚ)
      else 0) := by
  classical
  set A : ℤ := p + (a + z1 - 1) / 90 with hA
  set B : ℤ := z + p - m + (a + z0 - 1) / 90 with hB
  set U := ((hm23Psi1WindowSourceSet a z0 z1 e).image hm23Psi1Coord ∪
    (hm23Psi0WindowSourceSet a z0 z1 e).image hm23Psi0Coord) with hU
  set box := hm23ShearPreimageBox (hm23FiberWbig z N A B) (hm23FiberVbig z N A B)
    m p with hbox
  set ι := hm23CoordOfFiber m p z N with hι
  -- Step 1: fiber sum = box.image ι sum (support equivalence)
  have hstep1 :
      (∑ c ∈ U.filter (fun c => c.m = m ∧ c.p = p ∧ c.z = z ∧ c.N = N),
        hm23CapF a z0 z1 e c) =
        ∑ c ∈ box.image ι, hm23CapF a z0 z1 e c := by
    refine hm23_Finset_sum_eq_of_mem_iff_on_support _ _ _ ?_
    intro x hFx
    constructor
    · intro hxs
      rw [Finset.mem_filter] at hxs
      obtain ⟨hxU, hxm, hxp, hxz, hxN⟩ := hxs
      rw [Finset.mem_image]
      refine ⟨(x.r, x.k), ?_, ?_⟩
      · have hmem := hm23_capF_ne_zero_imp_mem_box a z0 z1 e x hFx
        rw [hxm, hxp, hxz, hxN] at hmem
        exact hmem
      · -- ι (x.r, x.k) = x  since key x = κ
        show hm23CoordOfFiber m p z N (x.r, x.k) = x
        unfold hm23CoordOfFiber
        cases x with
        | mk xm xp xz xN xr xk =>
          simp only at hxm hxp hxz hxN ⊢
          rw [hxm, hxp, hxz, hxN]
    · intro hxt
      rw [Finset.mem_image] at hxt
      obtain ⟨rk, hrk, hrkeq⟩ := hxt
      rw [Finset.mem_filter]
      have hxU : x ∈ U := by
        subst hrkeq
        exact hm23_capF_ne_zero_imp_mem_coordUnion a z0 z1 e hreg _ hFx
      refine ⟨hxU, ?_, ?_, ?_, ?_⟩ <;>
        (subst hrkeq; rfl)
  rw [hstep1]
  -- Step 2: box.image ι sum = box sum of F∘ι (ι injective)
  rw [Finset.sum_image
    (fun x _ y _ hxy => hm23CoordOfFiber_injective m p z N hxy)]
  -- Step 3: box sum = canonical
  obtain ⟨hWc, hVc, hVA, hVB, hWB⟩ := hm23FiberBig_shear_hyps z N A B
  exact hm23CapF_box_sum_eq_canonical a z0 z1 e m p z N
    (hm23FiberWbig z N A B) (hm23FiberVbig z N A B) hWc hVc hVA hVB hWB

/-- Fiber key projection of a coordinate. -/
def hm23FiberKey (c : HM23Coord) : ℤ × ℤ × ℤ × ℤ := (c.m, c.p, c.z, c.N)

/-- The coordinate-union capture sum, regrouped fiber by fiber and collapsed via
the per-fiber capture, equals the sum over the fiber keys of
`sign · canonical(N,z)` (guarded by `TermOut = e`). -/
theorem hm23_capF_union_sum_eq_keysum
    (a z0 z1 e : ℤ) (hreg : hm23Nonsingular a z0 z1) :
    (∑ c ∈ ((hm23Psi1WindowSourceSet a z0 z1 e).image hm23Psi1Coord ∪
        (hm23Psi0WindowSourceSet a z0 z1 e).image hm23Psi0Coord),
      hm23CapF a z0 z1 e c) =
      ∑ κ ∈ (((hm23Psi1WindowSourceSet a z0 z1 e).image hm23Psi1Coord ∪
        (hm23Psi0WindowSourceSet a z0 z1 e).image hm23Psi0Coord).image hm23FiberKey),
        (if hm23TermOutExp a z0 z1 κ.1 κ.2.1 κ.2.2.1 κ.2.2.2 = e then
          negOnePowIntQ (κ.1 + κ.2.1) *
            ((hm23IntegerCoreCanonicalSumInt κ.2.2.2 κ.2.2.1 : ℤ) : ℚ)
        else 0) := by
  classical
  set U := ((hm23Psi1WindowSourceSet a z0 z1 e).image hm23Psi1Coord ∪
    (hm23Psi0WindowSourceSet a z0 z1 e).image hm23Psi0Coord) with hU
  have hmaps : ∀ c ∈ U, hm23FiberKey c ∈ U.image hm23FiberKey :=
    fun c hc => Finset.mem_image_of_mem hm23FiberKey hc
  rw [← Finset.sum_fiberwise_of_maps_to (t := U.image hm23FiberKey)
    (g := hm23FiberKey) hmaps (fun c => hm23CapF a z0 z1 e c)]
  refine Finset.sum_congr rfl ?_
  intro κ hκ
  -- inner fiber sum = per-fiber capture at (κ.1,κ.2.1,κ.2.2.1,κ.2.2.2)
  obtain ⟨m, p, z, N⟩ := κ
  have hfilt :
      U.filter (fun c => hm23FiberKey c = (m, p, z, N)) =
        U.filter (fun c => c.m = m ∧ c.p = p ∧ c.z = z ∧ c.N = N) := by
    apply Finset.filter_congr
    intro c _hc
    simp only [hm23FiberKey, Prod.mk.injEq]
  rw [hfilt]
  exact hm23_capF_fiber_sum_eq_canonical a z0 z1 e m p z N hreg

/-- Window completeness for the residual `(m,p)`.  When the cube residual
`resid = e − z0 − jExp(z1−z0) m − jExp(a+z0+z1) p` is a nonnegative multiple of
`90`, the index `(m,p)` lies in the `lcoeff_RHS_eq_correct_fiber` Icc box: the
`m`-side uses the lower-bounded partner exponent `jExp(a+z0+z1) p ≥ jCoeffLower`,
the `p`-side uses the actual `m`.  Pure `jExp` target-window root bounds. -/
theorem hm23_resid_guard_imp_mp_mem (a z0 z1 e m p : ℤ)
    (hnn : 0 ≤ e - z0 - jExp (z1 - z0) 90 m - jExp (a + z0 + z1) 90 p) :
    m ∈ Finset.Icc
        (-(jCoeffWindow (z1 - z0) 90 (e - z0 - jCoeffLower (a + z0 + z1) 90)))
        (jCoeffWindow (z1 - z0) 90 (e - z0 - jCoeffLower (a + z0 + z1) 90)) ∧
      p ∈ Finset.Icc
        (-(jCoeffWindow (a + z0 + z1) 90 (e - z0 - jExp (z1 - z0) 90 m)))
        (jCoeffWindow (a + z0 + z1) 90 (e - z0 - jExp (z1 - z0) 90 m)) := by
  have hb : (0 : ℤ) < 90 := by norm_num
  have hlowP : jCoeffLower (a + z0 + z1) 90 ≤ jExp (a + z0 + z1) 90 p :=
    jExp_lower_bound (a + z0 + z1) 90 p hb
  have hmle : jExp (z1 - z0) 90 m ≤ e - z0 - jCoeffLower (a + z0 + z1) 90 := by
    omega
  have hple : jExp (a + z0 + z1) 90 p ≤ e - z0 - jExp (z1 - z0) 90 m := by
    omega
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_Icc]
    exact ⟨jExp_root_le_target_window_left (z1 - z0) 90
        (e - z0 - jCoeffLower (a + z0 + z1) 90) m hb hmle,
      jExp_root_le_target_window_right (z1 - z0) 90
        (e - z0 - jCoeffLower (a + z0 + z1) 90) m hb hmle⟩
  · rw [Finset.mem_Icc]
    exact ⟨jExp_root_le_target_window_left (a + z0 + z1) 90
        (e - z0 - jExp (z1 - z0) 90 m) p hb hple,
      jExp_root_le_target_window_right (a + z0 + z1) 90
        (e - z0 - jExp (z1 - z0) 90 m) p hb hple⟩

/-- Converse of `hm23_z0_guard_resid_eq_ninetyN`: at `z = 0`, `90 N = resid`
forces the guard `hm23TermOutExp a z0 z1 m p 0 N = e`. -/
theorem hm23_z0_ninetyN_imp_guard (a z0 z1 e m p N : ℤ)
    (h : e - z0 - jExp (z1 - z0) 90 m - jExp (a + z0 + z1) 90 p = 90 * N) :
    hm23TermOutExp a z0 z1 m p 0 N = e := by
  rw [jExp90_eq_hmTri, jExp90_eq_hmTri] at h
  unfold hm23TermOutExp
  linarith

/-- Reconstruction.  If the RHS cube summand is nonzero at `(m,p)` (i.e. the
residual is a nonnegative multiple of `90` and the unified coefficient at
`(resid/90, 0)` is nonzero), then the fiber key `(m,p,0,resid/90)` belongs to the
coordinate-union fiber-key image.  Built from the per-fiber capture: a nonzero
canonical value plus the guard makes the fiber capture sum nonzero, hence the
fiber is inhabited inside `U`. -/
theorem hm23_rhs_ne_zero_imp_key_mem
    (a z0 z1 e m p : ℤ) (hreg : hm23Nonsingular a z0 z1)
    (hdvd : (90 : ℤ) ∣ e - z0 - jExp (z1 - z0) 90 m - jExp (a + z0 + z1) 90 p)
    (hnn : 0 ≤ e - z0 - jExp (z1 - z0) 90 m - jExp (a + z0 + z1) 90 p)
    (hcoeff :
      Chapter10PF.thetaMulPFUnifiedCoeffPF
        ((e - z0 - jExp (z1 - z0) 90 m - jExp (a + z0 + z1) 90 p) / 90).toNat 0 ≠ 0) :
    (m, p, (0 : ℤ),
      (e - z0 - jExp (z1 - z0) 90 m - jExp (a + z0 + z1) 90 p) / 90) ∈
      (((hm23Psi1WindowSourceSet a z0 z1 e).image hm23Psi1Coord ∪
        (hm23Psi0WindowSourceSet a z0 z1 e).image hm23Psi0Coord).image hm23FiberKey) := by
  classical
  set resid : ℤ := e - z0 - jExp (z1 - z0) 90 m - jExp (a + z0 + z1) 90 p with hresid
  set N : ℤ := resid / 90 with hN
  have hN_nonneg : 0 ≤ N := Int.ediv_nonneg hnn (by norm_num)
  have h90N : 90 * N = resid := by
    rw [hN]; exact Int.mul_ediv_cancel' hdvd
  -- canonical(N,0) ≠ 0
  have hcanon : hm23IntegerCoreCanonicalSumInt N 0 ≠ 0 := by
    have hNnat : N = ((N.toNat : ℤ)) := (Int.toNat_of_nonneg hN_nonneg).symm
    rw [hNnat, hm23IntegerCoreCanonicalSumInt_of_nat,
      hm23IntegerCoreCanonical_eq_unified]
    -- hcoeff : unified ((resid/90).toNat) 0 ≠ 0, and resid/90 = N
    exact hcoeff
  -- guard holds: TermOut = e
  have hguard : hm23TermOutExp a z0 z1 m p 0 N = e :=
    hm23_z0_ninetyN_imp_guard a z0 z1 e m p N (by rw [← hresid]; exact h90N.symm)
  -- per-fiber capture sum at (m,p,0,N) is nonzero
  have hfibersum :
      (∑ c ∈ ((hm23Psi1WindowSourceSet a z0 z1 e).image hm23Psi1Coord ∪
          (hm23Psi0WindowSourceSet a z0 z1 e).image hm23Psi0Coord).filter
          (fun c => c.m = m ∧ c.p = p ∧ c.z = 0 ∧ c.N = N),
        hm23CapF a z0 z1 e c) ≠ 0 := by
    rw [hm23_capF_fiber_sum_eq_canonical a z0 z1 e m p 0 N hreg, if_pos hguard]
    intro h0
    apply hcanon
    have : ((hm23IntegerCoreCanonicalSumInt N 0 : ℤ) : ℚ) = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h (by unfold negOnePowIntQ; exact pow_ne_zero _ (by norm_num))
      · exact h
    exact_mod_cast this
  -- a nonzero sum ⇒ the filter set has a member coord
  obtain ⟨c, hc, _hcF⟩ := Finset.exists_ne_zero_of_sum_ne_zero hfibersum
  rw [Finset.mem_filter] at hc
  obtain ⟨hcU, hcm, hcp, hcz, hcN⟩ := hc
  rw [Finset.mem_image]
  refine ⟨c, hcU, ?_⟩
  rw [hm23FiberKey, hcm, hcp, hcz, hcN]

/-- Final `e`-level reconciliation bridge for HM 2.3.  The fiber-key canonical sum
(LHS) and the `lcoeff_RHS_eq_correct_fiber` double `(m,p)` sum (RHS) agree.  Both
equal the `(m,p)`-plane sum of
`G(m,p) = sign(m+p)·(if 90∣resid ∧ 0≤resid then unified(resid/90,0) else 0)`:
on the LHS the `z≠0`/`N<0` keys vanish and surviving `z=0,N≥0` keys carry
`G(m,p)` with the `(m,p)`-projection injective; on the RHS the cube coefficient
is `G(m,p)` and its support sits in the `jCoeffWindow` box (window completeness),
while every nonzero `G(m,p)` reconstructs a surviving fiber key (reconstruction).
-/
theorem hm23_keysum_eq_RHS_doublesum
    (hPF :
      Chapter10PF.thetaMulPFSeriesCoeffPF =
        Chapter10PF.qPochInfPSCubeUPowerCoeffPF)
    (a z0 z1 e : ℤ) (hreg : hm23Nonsingular a z0 z1) :
    (∑ κ ∈ (((hm23Psi1WindowSourceSet a z0 z1 e).image hm23Psi1Coord ∪
        (hm23Psi0WindowSourceSet a z0 z1 e).image hm23Psi0Coord).image hm23FiberKey),
      (if hm23TermOutExp a z0 z1 κ.1 κ.2.1 κ.2.2.1 κ.2.2.2 = e then
        negOnePowIntQ (κ.1 + κ.2.1) *
          ((hm23IntegerCoreCanonicalSumInt κ.2.2.2 κ.2.2.1 : ℤ) : ℚ)
      else 0)) =
      ∑ m ∈ Finset.Icc
          (-(jCoeffWindow (z1 - z0) 90 (e - z0 - jCoeffLower (a + z0 + z1) 90)))
          (jCoeffWindow (z1 - z0) 90 (e - z0 - jCoeffLower (a + z0 + z1) 90)),
        ∑ p ∈ Finset.Icc
            (-(jCoeffWindow (a + z0 + z1) 90 (e - z0 - jExp (z1 - z0) 90 m)))
            (jCoeffWindow (a + z0 + z1) 90 (e - z0 - jExp (z1 - z0) 90 m)),
          negOnePowIntQ (m + p) *
            (if (90 : ℤ) ∣ e - z0 - jExp (z1 - z0) 90 m - jExp (a + z0 + z1) 90 p ∧
                0 ≤ e - z0 - jExp (z1 - z0) 90 m - jExp (a + z0 + z1) 90 p then
              ((Chapter10PF.thetaMulPFUnifiedCoeffPF
                ((e - z0 - jExp (z1 - z0) 90 m - jExp (a + z0 + z1) 90 p) / 90).toNat 0 : ℤ) : ℚ)
            else 0) := by
  classical
  set U := ((hm23Psi1WindowSourceSet a z0 z1 e).image hm23Psi1Coord ∪
    (hm23Psi0WindowSourceSet a z0 z1 e).image hm23Psi0Coord) with hU
  -- the (m,p)-plane summand
  set G : ℤ × ℤ → ℚ := fun mp =>
    negOnePowIntQ (mp.1 + mp.2) *
      (if (90 : ℤ) ∣ e - z0 - jExp (z1 - z0) 90 mp.1 - jExp (a + z0 + z1) 90 mp.2 ∧
          0 ≤ e - z0 - jExp (z1 - z0) 90 mp.1 - jExp (a + z0 + z1) 90 mp.2 then
        ((Chapter10PF.thetaMulPFUnifiedCoeffPF
          ((e - z0 - jExp (z1 - z0) 90 mp.1 - jExp (a + z0 + z1) 90 mp.2) / 90).toNat 0 : ℤ) : ℚ)
      else 0) with hG
  -- the key-indexed summand
  set L : ℤ × ℤ × ℤ × ℤ → ℚ := fun κ =>
    (if hm23TermOutExp a z0 z1 κ.1 κ.2.1 κ.2.2.1 κ.2.2.2 = e then
      negOnePowIntQ (κ.1 + κ.2.1) *
        ((hm23IntegerCoreCanonicalSumInt κ.2.2.2 κ.2.2.1 : ℤ) : ℚ)
    else 0) with hL
  -- the dependent RHS box, flattened to a single Finset of (m,p)
  set D : Finset (ℤ × ℤ) :=
    (Finset.Icc
        (-(jCoeffWindow (z1 - z0) 90 (e - z0 - jCoeffLower (a + z0 + z1) 90)))
        (jCoeffWindow (z1 - z0) 90 (e - z0 - jCoeffLower (a + z0 + z1) 90))).biUnion
      (fun m => (Finset.Icc
          (-(jCoeffWindow (a + z0 + z1) 90 (e - z0 - jExp (z1 - z0) 90 m)))
          (jCoeffWindow (a + z0 + z1) 90 (e - z0 - jExp (z1 - z0) 90 m))).map
        ⟨fun p => (m, p), fun p q h => (Prod.mk.injEq _ _ _ _ ▸ h).2⟩) with hD
  -- RHS double sum = ∑_{D} G
  have hRHS : (∑ m ∈ Finset.Icc
        (-(jCoeffWindow (z1 - z0) 90 (e - z0 - jCoeffLower (a + z0 + z1) 90)))
        (jCoeffWindow (z1 - z0) 90 (e - z0 - jCoeffLower (a + z0 + z1) 90)),
      ∑ p ∈ Finset.Icc
          (-(jCoeffWindow (a + z0 + z1) 90 (e - z0 - jExp (z1 - z0) 90 m)))
          (jCoeffWindow (a + z0 + z1) 90 (e - z0 - jExp (z1 - z0) 90 m)),
        negOnePowIntQ (m + p) *
          (if (90 : ℤ) ∣ e - z0 - jExp (z1 - z0) 90 m - jExp (a + z0 + z1) 90 p ∧
              0 ≤ e - z0 - jExp (z1 - z0) 90 m - jExp (a + z0 + z1) 90 p then
            ((Chapter10PF.thetaMulPFUnifiedCoeffPF
              ((e - z0 - jExp (z1 - z0) 90 m - jExp (a + z0 + z1) 90 p) / 90).toNat 0 : ℤ) : ℚ)
          else 0)) = ∑ mp ∈ D, G mp := by
    rw [hD, Finset.sum_biUnion]
    · refine Finset.sum_congr rfl ?_
      intro m _hm
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl ?_
      intro p _hp
      simp only [Function.Embedding.coeFn_mk, hG]
    · -- disjointness of the (m)-fibers (distinct first coordinate)
      intro m₁ _ m₂ _ hne
      simp only [Function.onFun, Finset.disjoint_left, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      rintro x ⟨p₁, _, rfl⟩ ⟨p₂, _, h2⟩
      exact hne (congrArg Prod.fst h2).symm
  rw [hRHS]
  -- LHS keysum = ∑_{D} G via support-iff between the projected surviving keys and D
  set proj : ℤ × ℤ × ℤ × ℤ → ℤ × ℤ := fun κ => (κ.1, κ.2.1) with hproj
  set Ukeys := U.image hm23FiberKey with hUkeys
  -- drop the L-zero keys, restrict to those with nonzero summand
  have hkeysum_filter :
      (∑ κ ∈ Ukeys, L κ) = ∑ κ ∈ Ukeys.filter (fun κ => L κ ≠ 0), L κ := by
    rw [Finset.sum_filter_ne_zero]
  -- on the nonzero-L filter, L κ = G (proj κ)
  have hLG : ∀ κ ∈ Ukeys.filter (fun κ => L κ ≠ 0), L κ = G (proj κ) := by
    intro κ hκ
    rw [Finset.mem_filter] at hκ
    obtain ⟨_hκU, hLne⟩ := hκ
    -- L κ ≠ 0 ⇒ TermOut = e and canonical ≠ 0
    have hT : hm23TermOutExp a z0 z1 κ.1 κ.2.1 κ.2.2.1 κ.2.2.2 = e := by
      by_contra h; simp only [hL, if_neg h] at hLne; exact hLne rfl
    have hcanon_ne : hm23IntegerCoreCanonicalSumInt κ.2.2.2 κ.2.2.1 ≠ 0 := by
      intro h0; apply hLne; simp only [hL, if_pos hT, h0]; norm_num
    -- canonical ≠ 0 ⇒ z = 0 and N ≥ 0
    have hz0 : κ.2.2.1 = 0 := by
      by_contra hz
      exact hcanon_ne (hm23IntegerCoreCanonicalSumInt_eq_zero_of_z_ne_zero _ _ hz)
    have hNnn : 0 ≤ κ.2.2.2 := by
      by_contra hN; push_neg at hN
      exact hcanon_ne (hm23IntegerCoreCanonicalSumInt_eq_zero_of_neg hN)
    -- guard at z=0 ⇒ 90 N = resid
    have hresid : e - z0 - jExp (z1 - z0) 90 κ.1 - jExp (a + z0 + z1) 90 κ.2.1 =
        90 * κ.2.2.2 := by
      have := hm23_z0_guard_resid_eq_ninetyN a z0 z1 e κ.1 κ.2.1 κ.2.2.2 (by rw [← hz0]; exact hT)
      exact this
    have hdvd : (90 : ℤ) ∣ e - z0 - jExp (z1 - z0) 90 κ.1 - jExp (a + z0 + z1) 90 κ.2.1 := by
      rw [hresid]; exact Dvd.intro _ rfl
    have hnn : 0 ≤ e - z0 - jExp (z1 - z0) 90 κ.1 - jExp (a + z0 + z1) 90 κ.2.1 := by
      rw [hresid]; positivity
    -- compute both sides
    simp only [hL, hG, hproj, if_pos hT]
    have hidx : (e - z0 - jExp (z1 - z0) 90 κ.1 - jExp (a + z0 + z1) 90 κ.2.1) / 90 = κ.2.2.2 := by
      rw [hresid]; rw [Int.mul_ediv_cancel_left _ (by norm_num : (90:ℤ) ≠ 0)]
    rw [if_pos ⟨hdvd, hnn⟩, hz0]
    congr 1
    -- canonical(N,0) = unified(N.toNat,0) = unified((resid/90).toNat,0)
    have hNcast : κ.2.2.2 = ((κ.2.2.2.toNat : ℤ)) := (Int.toNat_of_nonneg hNnn).symm
    rw [hNcast, hm23IntegerCoreCanonicalSumInt_of_nat, hm23IntegerCoreCanonical_eq_unified]
    rw [hidx]
  rw [hkeysum_filter, Finset.sum_congr rfl hLG]
  -- ∑ over filter of G∘proj = ∑ over (filter.image proj) of G  (proj injective on filter)
  have hinj : Set.InjOn proj (Ukeys.filter (fun κ => L κ ≠ 0)) := by
    intro κ hκ κ' hκ' hpp
    rw [Finset.coe_filter, Set.mem_setOf_eq] at hκ hκ'
    obtain ⟨_, hLne⟩ := hκ; obtain ⟨_, hLne'⟩ := hκ'
    -- both surviving: z=0, TermOut=e, 90N=resid determined by (m,p)=proj
    have hTz : ∀ x : ℤ × ℤ × ℤ × ℤ, L x ≠ 0 →
        hm23TermOutExp a z0 z1 x.1 x.2.1 x.2.2.1 x.2.2.2 = e ∧ x.2.2.1 = 0 ∧
          e - z0 - jExp (z1 - z0) 90 x.1 - jExp (a + z0 + z1) 90 x.2.1 = 90 * x.2.2.2 := by
      intro x hx
      have hT : hm23TermOutExp a z0 z1 x.1 x.2.1 x.2.2.1 x.2.2.2 = e := by
        by_contra h; simp only [hL, if_neg h] at hx; exact hx rfl
      have hcn : hm23IntegerCoreCanonicalSumInt x.2.2.2 x.2.2.1 ≠ 0 := by
        intro h0; apply hx; simp only [hL, if_pos hT, h0]; norm_num
      have hxz : x.2.2.1 = 0 := by
        by_contra hz; exact hcn (hm23IntegerCoreCanonicalSumInt_eq_zero_of_z_ne_zero _ _ hz)
      exact ⟨hT, hxz, hm23_z0_guard_resid_eq_ninetyN a z0 z1 e x.1 x.2.1 x.2.2.2
        (by rw [← hxz]; exact hT)⟩
    obtain ⟨_, hz, hr⟩ := hTz κ hLne
    obtain ⟨_, hz', hr'⟩ := hTz κ' hLne'
    simp only [hproj, Prod.mk.injEq] at hpp
    obtain ⟨hm, hp⟩ := hpp
    have hN : κ.2.2.2 = κ'.2.2.2 := by
      have : (90 : ℤ) * κ.2.2.2 = 90 * κ'.2.2.2 := by rw [← hr, ← hr', hm, hp]
      omega
    -- reconstruct full equality
    obtain ⟨m1, p1, z1', N1⟩ := κ
    obtain ⟨m2, p2, z2', N2⟩ := κ'
    simp only at hm hp hz hz' hN
    rw [hm, hp, hz, hz', hN]
  rw [← Finset.sum_image (fun κ hκ κ' hκ' h => hinj (by exact_mod_cast hκ) (by exact_mod_cast hκ') h)]
  -- now both sides are ∑ over a Finset of (m,p), of G ; match supports with D
  refine hm23_Finset_sum_eq_of_mem_iff_on_support _ _ G ?_
  intro mp hGne
  -- G mp ≠ 0 ⇒ 90 ∣ resid ∧ 0 ≤ resid ∧ unified ≠ 0
  have hguard : (90 : ℤ) ∣ e - z0 - jExp (z1 - z0) 90 mp.1 - jExp (a + z0 + z1) 90 mp.2 ∧
      0 ≤ e - z0 - jExp (z1 - z0) 90 mp.1 - jExp (a + z0 + z1) 90 mp.2 := by
    by_contra h; simp only [hG, if_neg h, mul_zero] at hGne; exact hGne rfl
  obtain ⟨hdvd, hnn⟩ := hguard
  have hcoeff : Chapter10PF.thetaMulPFUnifiedCoeffPF
      ((e - z0 - jExp (z1 - z0) 90 mp.1 - jExp (a + z0 + z1) 90 mp.2) / 90).toNat 0 ≠ 0 := by
    intro h0; apply hGne; simp only [hG, h0, Int.cast_zero, ite_self, mul_zero]
  constructor
  · -- mp ∈ (filter.image proj) ⇒ mp ∈ D : window completeness
    intro _
    rw [hD, Finset.mem_biUnion]
    obtain ⟨hmem_m, hmem_p⟩ := hm23_resid_guard_imp_mp_mem a z0 z1 e mp.1 mp.2 hnn
    refine ⟨mp.1, hmem_m, ?_⟩
    rw [Finset.mem_map]
    exact ⟨mp.2, hmem_p, by simp [Function.Embedding.coeFn_mk]⟩
  · -- mp ∈ D ⇒ mp ∈ (filter.image proj) : reconstruct the surviving key
    intro _
    rw [Finset.mem_image]
    refine ⟨(mp.1, mp.2, 0, (e - z0 - jExp (z1 - z0) 90 mp.1 - jExp (a + z0 + z1) 90 mp.2) / 90), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [hUkeys, hU]
        exact hm23_rhs_ne_zero_imp_key_mem a z0 z1 e mp.1 mp.2 hreg hdvd hnn hcoeff
      · -- L of this key ≠ 0
        set N0 := (e - z0 - jExp (z1 - z0) 90 mp.1 - jExp (a + z0 + z1) 90 mp.2) / 90 with hN0
        have h90 : 90 * N0 = e - z0 - jExp (z1 - z0) 90 mp.1 - jExp (a + z0 + z1) 90 mp.2 := by
          rw [hN0]; exact Int.mul_ediv_cancel' hdvd
        have hgrd : hm23TermOutExp a z0 z1 mp.1 mp.2 0 N0 = e :=
          hm23_z0_ninetyN_imp_guard a z0 z1 e mp.1 mp.2 N0 h90.symm
        have hNnn : 0 ≤ N0 := Int.ediv_nonneg hnn (by norm_num)
        simp only [hL, if_pos hgrd]
        intro hzero
        apply hcoeff
        have hcanon0 : (hm23IntegerCoreCanonicalSumInt N0 0 : ℤ) = 0 := by
          rcases mul_eq_zero.mp hzero with h | h
          · exact absurd h (by unfold negOnePowIntQ; exact pow_ne_zero _ (by norm_num))
          · exact_mod_cast h
        have hNcast : N0 = ((N0.toNat : ℤ)) := (Int.toNat_of_nonneg hNnn).symm
        rw [hNcast, hm23IntegerCoreCanonicalSumInt_of_nat,
          hm23IntegerCoreCanonical_eq_unified] at hcanon0
        exact hcanon0
    · simp only [hproj]


/-- ISOLATED REMAINING GAP (HM 2.3 piece C + piece B stage 2 + final match).

After piece A, the Γ-window difference equals the coordinate-union sum of the
guarded `sign · integerCoreSummand(sheared)`
(`hm23GammaWindowDifference_eq_coordImageSum_integerCore`).  After piece B
stage 1, the RHS coefficient equals the cube/theta-pair convolution
(`lcoeff_RHS_eq_cube_theta_pair_sum`).  This lemma is the remaining bridge: both
finite sums regroup, fiber by `(m,p,z,N)`, into
`∑_{(m,p,z,N): TermOut=e} (-1)^{m+p} · thetaMulPFUnifiedCoeffPF N z`, using
`hm23ShearPreimageBox_sum_eq_canonical` (collapse of the `(r,k)` shear box to the
canonical integer-core sum) and `hm23_thetaMulPFRawCoeffPF_rat_eq_JOneCoeff_of_hPF`
(identification of the cube coefficient with the canonical sum via `hPF`).

Numerically verified TRUE on random nonsingular `(a,z0,z1,e)` (see model2/modelB2,
both sides agreed including nonzero cases).  The mathematical content is the
converse support fact that the window coordinate images capture, fiber by fiber,
exactly the shear-preimage box of contributing `(r,k)` points.

IMPLEMENTATION NOTE (Opus, this session).  The intended meeting point
`hm23FiberSum` is NOT a valid bridge for this lemma as a free-integer statement:
its `(m,p)` windows `jCoeffWindow (z1-z0) 90 (e-z0)` and
`jCoeffWindow (a+z0+z1) 90 (e-z0)` depend only on `z1-z0`, `a+z0+z1` and `e-z0`,
and are too small once `|a|` is large.  Concretely, for `a=186079, z0=z1=0,
e=52` the residual `e - z0 - jExp(z1-z0) m - jExp(a+z0+z1) p` is a NONNEGATIVE
multiple of `90` with NONZERO cube coefficient at `m = 996`, while the fiber
`m`-window is only `732`; that term is dropped, so
`lcoeff(RHS) = hm23FiberSum` FAILS (verified, both numerically and by the
`nlinarith` rejection of the would-be coupled support bound
`theta_pair_resid_nonneg_m_bound`).  The cube residual `resid >= 0` does NOT
force `|m|` into the `(e-z0)`-window because the partner theta exponent
`jExp(a+z0+z1) 90 p` can be as negative as `-(a+z0+z1)^2/180`, allowing
`jExp(z1-z0) 90 m` up to `(e-z0) + (a+z0+z1)^2/180`.

Consequence: the RHS side is now available CORRECTLY-windowed (all integers) as
`lcoeff_RHS_eq_correct_fiber`, which rewrites `lcoeff(RHS)` as the double sum
  `∑_{m ∈ Icc(-Wm)(Wm)} ∑_{p ∈ Icc(-Wp(m))(Wp(m))}
      (-1)^{m+p} · lcoeff(J₁^3) (e - z0 - jExp(z1-z0) m - jExp(a+z0+z1) p)`
with `Wm = jCoeffWindow (z1-z0) 90 (e - z0 - jCoeffLower (a+z0+z1) 90)` and
`Wp(m) = jCoeffWindow (a+z0+z1) 90 (e - z0 - jExp(z1-z0) m)`.  This was built
from the verified bricks `lcoeff_jLaurent_90_mul_eq_window`,
`lcoeff_jLaurent_mul_cube_eq_zero_of_lt`, `jExp_root_le_target_window_left/right`,
`jCoeff_eq_sum_Icc_of_roots_le`, `lcoeff_JOneLaurent_pow_three_of_neg`.

REMAINING WORK (the LHS converse-support direction, unfinished): rewrite the
`coordUnion` sum so that it equals the above double sum.  Per `(m,p)` fiber:
(i) the `(z,N,r,k)` inner sum collapses via `hm23ShearPreimageBox_sum_eq_canonical`
to `canonical(N,z) = thetaMulPFUnifiedCoeffPF N z`, which vanishes for `z ≠ 0`
(`Chapter10PF.thetaMulPFUnifiedCoeffPF_nonconstant_vanish`), leaving only `z = 0`;
(ii) at `z = 0`, `lcoeff(J₁^3) resid = thetaMulPFUnifiedCoeffPF (resid/90) 0`
(`lcoeff_JOneLaurent_pow_three_eq_ite_unified`).

INDEX RECONCILIATION (resolved, Opus, this session — the earlier "(m+p) shift"
note was a sign/algebra error and is RETRACTED).  At `z = 0` the guard
`hm23TermOutExp a z0 z1 m p 0 N = e` gives EXACTLY `90 N = resid`, i.e.
`N = resid / 90`, with NO `(m + p)` shift.  Proof: expand
`resid = e - z0 - jExp (z1-z0) 90 m - jExp (a+z0+z1) 90 p`
using `jExp w 90 n = 90·hmTri n + w·n`, so
`resid = e - z0 - 90·hmTri m - (z1-z0)·m - 90·hmTri p - (a+z0+z1)·p`,
while the guard at `z = 0` reads
`90·(hmTri m + hmTri p + N) + z0·(1 - m + p) + z1·(m + p) + a·p = e`,
i.e. `90 N = e - 90·hmTri m - 90·hmTri p - z0·(1 - m + p) - z1·(m + p) - a·p`.
Subtracting, `90 N - resid = z0 + (z1-z0)·m + (a+z0+z1)·p - z0·(1-m+p)
- z1·(m+p) - a·p = 0` (verified by `ring`).  Hence at `z = 0`,
`thetaMulPFUnifiedCoeffPF N 0 = lcoeff (J₁^3) (90 N) = lcoeff (J₁^3) resid`
lines up DIRECTLY through `lcoeff_JOneLaurent_pow_three_eq_unified`, no reindex.

NUMERICALLY VERIFIED TRUE (this session), including nonzero cases: for random
nonsingular `(a,z0,z1,e)`, the guarded `coordUnion` sum equals the
`lcoeff_RHS_eq_correct_fiber` double `(m,p)` sum (matched on e.g.
`a=7,z0=1,z1=2` at `e ∈ {1,2,11,12,81,82,90,91,…}` with nonzero values
`1,-1,-1,1,-1,1,-1,-3`).  Per-fiber check: for each `(m,p,z,N)` the
guard-passing `(r,k)` of the `coordUnion` image SUM (against
`hm23IntegerCoreSummandInt` at the sheared coordinates) equals
`hm23IntegerCoreCanonicalSumInt N z` exactly (window-independent), confirming the
converse-capture below.

The genuine REMAINING content is the converse capture as a `Finset` identity:
for each fiber, the guard-passing `(r,k)` of `coordUnion` SUM to the
shear-preimage-box value.  The forward support bound (every guard-passing `(r,k)`
with nonzero `hm23IntegerCoreSummandInt` lies in the box) and the surjectivity
membership (`hm23Psi1_phi_mem_Psi0WindowSourceSet_of_Gamma_ne_zero` and its
mirror put every box `(r,k)` with nonzero summand into the window image) are the
two halves of a `Finset.sum_subset`-in-both-directions argument; assembling them
through the `(m,p,z,N)` `Finset.sum_fiberwise`/`sigma` regrouping is the unwritten
step.  `hm23FiberSum` is only valid in the bounded fundamental-domain regime
`0 ≤ a < 90` with bounded `z0, z1`. -/
theorem hm23CoordUnion_integerCore_eq_lcoeff_RHS
    (hPF :
      Chapter10PF.thetaMulPFSeriesCoeffPF =
        Chapter10PF.qPochInfPSCubeUPowerCoeffPF)
    (a z0 z1 e : ℤ) (hreg : hm23Nonsingular a z0 z1) :
    (∑ c ∈
        ((hm23Psi1WindowSourceSet a z0 z1 e).image hm23Psi1Coord ∪
          (hm23Psi0WindowSourceSet a z0 z1 e).image hm23Psi0Coord),
      (if hm23TermOutExp a z0 z1 c.m c.p c.z c.N = e ∧
          c.N = hm23Ncoord c.m c.p c.z c.r c.k then
        negOnePowIntQ (c.m + c.p) *
          ((hm23IntegerCoreSummandInt (hm23Ncoord c.m c.p c.z c.r c.k) c.z
            (c.p + (a + z1 - 1) / 90)
            (c.z + c.p - c.m + (a + z0 - 1) / 90)
            (2 * c.r + c.k - c.m - c.p - 1)
            (c.r - c.m + c.k) : ℤ) : ℚ)
      else 0)) =
      lcoeff (Qpow z0 * JOneLaurent ^ 3 * jLaurent (z1 - z0) 90 *
        jLaurent (a + z0 + z1) 90) e := by
  classical
  -- ===== LHS side: collapse the redundant `N = Ncoord` guard, then regroup the
  -- coordinate-union capture sum fiber by fiber into the fiber-key sum of
  -- `sign · canonical(N,z)` (converse capture, now fully banked). =====
  have hcollapse :
      (∑ c ∈
          ((hm23Psi1WindowSourceSet a z0 z1 e).image hm23Psi1Coord ∪
            (hm23Psi0WindowSourceSet a z0 z1 e).image hm23Psi0Coord),
        (if hm23TermOutExp a z0 z1 c.m c.p c.z c.N = e ∧
            c.N = hm23Ncoord c.m c.p c.z c.r c.k then
          negOnePowIntQ (c.m + c.p) *
            ((hm23IntegerCoreSummandInt (hm23Ncoord c.m c.p c.z c.r c.k) c.z
              (c.p + (a + z1 - 1) / 90)
              (c.z + c.p - c.m + (a + z0 - 1) / 90)
              (2 * c.r + c.k - c.m - c.p - 1)
              (c.r - c.m + c.k) : ℤ) : ℚ)
        else 0)) =
      ∑ c ∈
          ((hm23Psi1WindowSourceSet a z0 z1 e).image hm23Psi1Coord ∪
            (hm23Psi0WindowSourceSet a z0 z1 e).image hm23Psi0Coord),
        hm23CapF a z0 z1 e c := by
    refine Finset.sum_congr rfl ?_
    intro c _hc
    rw [hm23_guard_collapse a z0 z1 e c]
    rfl
  rw [hcollapse, hm23_capF_union_sum_eq_keysum a z0 z1 e hreg]
  -- ===== RHS side: rewrite as the double (m,p) fiber sum with the unified coeff =====
  rw [lcoeff_RHS_eq_correct_fiber a z0 z1 e]
  simp only [lcoeff_JOneLaurent_pow_three_eq_ite_unified hPF]
  -- REMAINING e-LEVEL RECONCILIATION.  LHS is now the fiber-key sum
  --   `∑_{(m,p,z,N) ∈ U.image key} [TermOut=e] · sign(m+p) · canonical(N,z)`;
  -- the `z ≠ 0` and `N < 0` keys vanish
  -- (`hm23IntegerCoreCanonicalSumInt_eq_zero_of_{z_ne_zero,neg}`), and on the
  -- surviving `z = 0, N ≥ 0` keys `TermOut = e` forces `90 N = resid(m,p)`
  -- (`hm23_z0_guard_resid_eq_ninetyN`) with `canonical(N,0) = unified(N,0)`
  -- (`hm23IntegerCoreCanonical_eq_unified`).  The RHS is the `(m,p)`-window double
  -- sum of `sign(m+p) · (if 90 | resid ∧ 0 ≤ resid then unified(resid/90,0) else 0)`
  -- (`hm23_rhs_cube_eq_canonical_z0`).  Both equal
  --   `∑_{(m,p)} sign(m+p) · unified(resid(m,p)/90, 0) · [90 | resid ∧ 0 ≤ resid]`;
  -- matching the two `(m,p)` index ranges is the residual theta-window symmetry
  -- (the surviving fiber keys' `(m,p)` projection vs. the `jCoeffWindow` Icc
  -- ranges), reconciled only at the `e`-level total, not term by term.
  exact hm23_keysum_eq_RHS_doublesum hPF a z0 z1 e hreg

theorem hm23GammaWindowDifference_residual
    (hPF :
      Chapter10PF.thetaMulPFSeriesCoeffPF =
        Chapter10PF.qPochInfPSCubeUPowerCoeffPF)
    (a z0 z1 e : ℤ) (hreg : hm23Nonsingular a z0 z1) :
    hm23GammaWindowFourFactorSum a z1 z0 (a + z0) (a + z1) e -
      hm23GammaWindowFourFactorSum a z0 z1 (a + z0) (a + z1) e -
        lcoeff (Qpow z0 * JOneLaurent ^ 3 * jLaurent (z1 - z0) 90 *
          jLaurent (a + z0 + z1) 90) e = 0 := by
  rw [hm23GammaWindowDifference_eq_coordImageSum_integerCore a z0 z1 e hreg]
  rw [hm23CoordUnion_integerCore_eq_lcoeff_RHS hPF a z0 z1 e hreg]
  ring



/--
Remaining PF map-down coefficient step for HM 2.3, after the HM numerator
coefficients have been rewritten into the PF branch coefficient convention.

The hypotheses `hnum0` and `hnum1` are the closed bridges from the concrete
finite-window coefficients `appellNumeratorCoeff` to
`Chapter10PF.branchInvCoeffAtPF`; the residual is the remaining
summation/support transport from the PF two-variable coefficient family to the
one-variable Laurent coefficient of the cleared HM 2.3 identity.
-/
theorem hm23PFBranchMapDown_coeff_residual
    (hPF :
      Chapter10PF.thetaMulPFSeriesCoeffPF =
        Chapter10PF.qPochInfPSCubeUPowerCoeffPF)
    (a z0 z1 e : ℤ) (hreg : hm23Nonsingular a z0 z1)
    (hnum0 : ∀ E : ℤ,
      appellNumeratorCoeff a z0 E = appellNumeratorPFBranchCoeff a z0 E)
    (hnum1 : ∀ E : ℤ,
      appellNumeratorCoeff a z1 E = appellNumeratorPFBranchCoeff a z1 E) :
    lcoeff
      (((appellNumeratorLaurent a z1 * jLaurent z0 90 -
              appellNumeratorLaurent a z0 * jLaurent z1 90) *
            jLaurent (a + z0) 90 * jLaurent (a + z1) 90) -
          Qpow z0 * JOneLaurent ^ 3 * jLaurent (z1 - z0) 90 *
            jLaurent (a + z0 + z1) 90) e = 0 := by
  let T₁ : QLaurent :=
    appellNumeratorLaurent a z1 * jLaurent z0 90 *
      jLaurent (a + z0) 90 * jLaurent (a + z1) 90
  let T₀ : QLaurent :=
    appellNumeratorLaurent a z0 * jLaurent z1 90 *
      jLaurent (a + z0) 90 * jLaurent (a + z1) 90
  let R : QLaurent :=
    Qpow z0 * JOneLaurent ^ 3 * jLaurent (z1 - z0) 90 *
      jLaurent (a + z0 + z1) 90
  have hmain :
      ((appellNumeratorLaurent a z1 * jLaurent z0 90 -
              appellNumeratorLaurent a z0 * jLaurent z1 90) *
            jLaurent (a + z0) 90 * jLaurent (a + z1) 90) =
        T₁ - T₀ := by
    dsimp [T₁, T₀]
    ring
  have hden0 : ∀ r : ℤ, appellDenomExp a z0 r ≠ 0 := by
    intro r
    exact hm23Nonsingular_appellDenomExp_z0_ne_zero
      (a := a) (z0 := z0) (z1 := z1) (r := r) hreg
  have hden1 : ∀ r : ℤ, appellDenomExp a z1 r ≠ 0 := by
    intro r
    exact hm23Nonsingular_appellDenomExp_z1_ne_zero
      (a := a) (z0 := z0) (z1 := z1) (r := r) hreg
  have hT₁ :
      lcoeff T₁ e =
        hm23GammaWindowFourFactorSum a z1 z0 (a + z0) (a + z1) e := by
    dsimp [T₁]
    exact
      lcoeff_appellNumeratorLaurent_mul_three_jLaurent_90_eq_Gamma_window_sum
        a z1 z0 (a + z0) (a + z1) e hden1 hnum1
  have hT₀ :
      lcoeff T₀ e =
        hm23GammaWindowFourFactorSum a z0 z1 (a + z0) (a + z1) e := by
    dsimp [T₀]
    exact
      lcoeff_appellNumeratorLaurent_mul_three_jLaurent_90_eq_Gamma_window_sum
        a z0 z1 (a + z0) (a + z1) e hden0 hnum0
  have hgamma := hm23GammaWindowDifference_residual hPF a z0 z1 e hreg
  rw [hmain]
  change lcoeff ((T₁ - T₀) - R) e = 0
  dsimp [R]
  unfold lcoeff at hT₁ hT₀ hgamma ⊢
  rw [HahnSeries.coeff_sub, HahnSeries.coeff_sub, hT₁, hT₀]
  exact hgamma

/--
PF map-down coefficient step for HM 2.3.

The imported theorem `Chapter10PF.thetaMul_PF_eq_qPochInfPS_pow_three` proves
the two-variable coefficient identity for `j(u;q) * PF(u;q)`.  This residual
is the specialization of that identity through `q = Q^90`, the substitution
`u = Q^d`, and the current finite-window `appellNumeratorLaurent` coefficient
model, under the nonsingularity needed for every denominator exponent
`90(r-1)+a+zᵢ` to be nonzero.
-/
theorem appellNumeratorLaurent_PF_changeOfZ_coeff_mapDown
    (hPF :
      Chapter10PF.thetaMulPFSeriesCoeffPF =
        Chapter10PF.qPochInfPSCubeUPowerCoeffPF)
    (a z0 z1 e : ℤ) (hreg : hm23Nonsingular a z0 z1) :
    lcoeff
      (((appellNumeratorLaurent a z1 * jLaurent z0 90 -
              appellNumeratorLaurent a z0 * jLaurent z1 90) *
            jLaurent (a + z0) 90 * jLaurent (a + z1) 90) -
          Qpow z0 * JOneLaurent ^ 3 * jLaurent (z1 - z0) 90 *
            jLaurent (a + z0 + z1) 90) e = 0 := by
  have hnum0 : ∀ E : ℤ,
      appellNumeratorCoeff a z0 E = appellNumeratorPFBranchCoeff a z0 E := by
    intro E
    exact appellNumeratorCoeff_eq_PFBranchCoeff a z0 E
      (fun r => hm23Nonsingular_appellDenomExp_z0_ne_zero
        (a := a) (z0 := z0) (z1 := z1) (r := r) hreg)
  have hnum1 : ∀ E : ℤ,
      appellNumeratorCoeff a z1 E = appellNumeratorPFBranchCoeff a z1 E := by
    intro E
    exact appellNumeratorCoeff_eq_PFBranchCoeff a z1 E
      (fun r => hm23Nonsingular_appellDenomExp_z1_ne_zero
        (a := a) (z0 := z0) (z1 := z1) (r := r) hreg)
  exact hm23PFBranchMapDown_coeff_residual hPF a z0 z1 e hreg hnum0 hnum1

/--
Localized partial-fraction expansion PF/PF', specialized to
`x=Q^a`, `z_i=Q^z_i`, and `q=Q^90`.
-/
theorem hm23PartialFractionExpansionPF
    (a z0 z1 : ℤ) (hreg : hm23Nonsingular a z0 z1) :
    (appellNumeratorLaurent a z1 * jLaurent z0 90 -
        appellNumeratorLaurent a z0 * jLaurent z1 90) *
      jLaurent (a + z0) 90 * jLaurent (a + z1) 90 =
        Qpow z0 * JOneLaurent ^ 3 * jLaurent (z1 - z0) 90 *
          jLaurent (a + z0 + z1) 90 := by
  ext e
  change
    (((appellNumeratorLaurent a z1 * jLaurent z0 90 -
            appellNumeratorLaurent a z0 * jLaurent z1 90) *
          jLaurent (a + z0) 90 * jLaurent (a + z1) 90).coeff e =
      (Qpow z0 * JOneLaurent ^ 3 * jLaurent (z1 - z0) 90 *
        jLaurent (a + z0 + z1) 90).coeff e)
  have hcoeff :=
    appellNumeratorLaurent_PF_changeOfZ_coeff_mapDown
      Chapter10PF.thetaMul_PF_eq_qPochInfPS_pow_three a z0 z1 e hreg
  unfold lcoeff at hcoeff
  rw [HahnSeries.coeff_sub] at hcoeff
  exact sub_eq_zero.mp hcoeff

/-- Coefficient algebra left after applying the localized PF expansion: the
two residue contributions cancel, leaving the cleared theta numerator. -/
theorem hm23ResidueCancellationCoefficientAlgebra
    (a z0 z1 : ℤ) (hreg : hm23Nonsingular a z0 z1) :
    (appellNumeratorLaurent a z1 * jLaurent z0 90 -
        appellNumeratorLaurent a z0 * jLaurent z1 90) *
      jLaurent (a + z0) 90 * jLaurent (a + z1) 90 =
        hm23ClearedThetaRHS a z0 z1 := by
  simpa [hm23ClearedThetaRHS] using
    hm23PartialFractionExpansionPF a z0 z1 hreg

/-- Pure cleared-product algebra converting the PF residue-cancellation
coefficient identity into the public HM 2.3 cleared theta identity. -/
theorem hm23ClearedThetaIdentity_of_residueCancellationCoefficientAlgebra
    (a z0 z1 : ℤ)
    (hcoeff :
      (appellNumeratorLaurent a z1 * jLaurent z0 90 -
          appellNumeratorLaurent a z0 * jLaurent z1 90) *
        jLaurent (a + z0) 90 * jLaurent (a + z1) 90 =
          hm23ClearedThetaRHS a z0 z1) :
    hm23ClearedThetaLHS a z0 z1 = hm23ClearedThetaRHS a z0 z1 := by
  unfold hm23ClearedThetaLHS
  calc
    appellNumeratorLaurent a z1 * jLaurent z0 90 *
          jLaurent (a + z0) 90 * jLaurent (a + z1) 90 -
        appellNumeratorLaurent a z0 * jLaurent z1 90 *
          jLaurent (a + z0) 90 * jLaurent (a + z1) 90
        =
          (appellNumeratorLaurent a z1 * jLaurent z0 90 -
              appellNumeratorLaurent a z0 * jLaurent z1 90) *
            jLaurent (a + z0) 90 * jLaurent (a + z1) 90 := by
            ring
    _ = hm23ClearedThetaRHS a z0 z1 := hcoeff

/--
HM Theorem 2.3 after clearing the four theta denominators.  This is the
pure theta-addition identity left after substituting HM Def. 0.1 for `m`.
-/
theorem hm23ClearedThetaIdentity
    (a z0 z1 : ℤ) (hreg : hm23Nonsingular a z0 z1) :
    hm23ClearedThetaLHS a z0 z1 = hm23ClearedThetaRHS a z0 z1 :=
  hm23ClearedThetaIdentity_of_residueCancellationCoefficientAlgebra a z0 z1
    (hm23ResidueCancellationCoefficientAlgebra a z0 z1 hreg)

/-- Algebra bridge from a cleared theta identity to HM Theorem 2.3's theta
quotient. -/
theorem hm23ChangeZIdentity_of_cleared
    (a z0 z1 : ℤ) (hreg : hm23Nonsingular a z0 z1)
    (hclear : hm23ClearedThetaLHS a z0 z1 = hm23ClearedThetaRHS a z0 z1) :
    appellM a z1 - appellM a z0 = hm23ThetaQuotient a z0 z1 := by
  rcases hreg with ⟨hz0, hz1, hxz0, hxz1⟩
  unfold hm23ClearedThetaLHS hm23ClearedThetaRHS at hclear
  rw [appellM_eq_hmDef01, appellM_eq_hmDef01]
  unfold hm23ThetaQuotient
  field_simp [hz0, hz1, hxz0, hxz1]
  linear_combination hclear

/-- HM Theorem 2.3 in the `Q`-exponent specialization. -/
theorem hm23ChangeZIdentity
    (a z0 z1 : ℤ) (hreg : hm23Nonsingular a z0 z1) :
    appellM a z1 - appellM a z0 = hm23ThetaQuotient a z0 z1 :=
  hm23ChangeZIdentity_of_cleared a z0 z1 hreg
    (hm23ClearedThetaIdentity a z0 z1 hreg)

theorem hm23DeltaToBase_eq_changeZ
    (a z : ℤ) (hreg : hm23Nonsingular a hm23DeltaBase z) :
    appellM a z - appellM a hm23DeltaBase = hm23DeltaToBase a z := by
  by_cases hz : z = hm23DeltaBase
  · subst z
    simp [hm23DeltaToBase]
  · rw [hm23DeltaToBase_of_ne hz]
    exact hm23ChangeZIdentity a hm23DeltaBase z hreg

/-- Product of mod-90 theta factors. -/
def jLaurent90Product : List ℤ → QLaurent
  | [] => 1
  | a :: rest => jLaurent a 90 * jLaurent90Product rest

theorem jLaurent_90_ne_zero_of_emod_ne_zero (a : ℤ) (hmod : a % 90 ≠ 0) :
    jLaurent a 90 ≠ 0 := by
  refine jLaurent_ne_zero_of_shift_pos_lt a 90 (a % 90) (a / 90) (by norm_num) ?ha ?hc ?hcb
  · have h := Int.emod_add_mul_ediv a 90
    omega
  · have hnonneg := Int.emod_nonneg a (by norm_num : (90 : ℤ) ≠ 0)
    omega
  · exact Int.emod_lt_of_pos a (by norm_num)

theorem hm23Nonsingular_of_emod_ne_zero
    (a z0 z1 : ℤ) (hz0 : z0 % 90 ≠ 0) (hz1 : z1 % 90 ≠ 0)
    (haz0 : (a + z0) % 90 ≠ 0) (haz1 : (a + z1) % 90 ≠ 0) :
    hm23Nonsingular a z0 z1 := by
  exact ⟨jLaurent_90_ne_zero_of_emod_ne_zero z0 hz0,
    jLaurent_90_ne_zero_of_emod_ne_zero z1 hz1,
    jLaurent_90_ne_zero_of_emod_ne_zero (a + z0) haz0,
    jLaurent_90_ne_zero_of_emod_ne_zero (a + z1) haz1⟩

theorem hmF232Terms_T00_hm23Nonsingular :
    ∀ t ∈ hmF232Terms (tijData 0 0).ell (tijData 0 0).X (tijData 0 0).Y,
      hm23Nonsingular t.mArg hm23DeltaBase t.mZ := by
  intro t ht
  rw [hmF232Terms_T00] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht | ht | ht <;>
    subst t <;>
    apply hm23Nonsingular_of_emod_ne_zero <;>
    norm_num [hm23DeltaBase]

theorem hmF232Terms_T01_hm23Nonsingular :
    ∀ t ∈ hmF232Terms (tijData 0 1).ell (tijData 0 1).X (tijData 0 1).Y,
      hm23Nonsingular t.mArg hm23DeltaBase t.mZ := by
  intro t ht
  rw [hmF232Terms_T01] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht | ht | ht <;>
    subst t <;>
    apply hm23Nonsingular_of_emod_ne_zero <;>
    norm_num [hm23DeltaBase]

theorem hmF232Terms_T02_hm23Nonsingular :
    ∀ t ∈ hmF232Terms (tijData 0 2).ell (tijData 0 2).X (tijData 0 2).Y,
      hm23Nonsingular t.mArg hm23DeltaBase t.mZ := by
  intro t ht
  rw [hmF232Terms_T02] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht | ht | ht <;>
    subst t <;>
    apply hm23Nonsingular_of_emod_ne_zero <;>
    norm_num [hm23DeltaBase]

theorem hmF232Terms_T10_hm23Nonsingular :
    ∀ t ∈ hmF232Terms (tijData 1 0).ell (tijData 1 0).X (tijData 1 0).Y,
      hm23Nonsingular t.mArg hm23DeltaBase t.mZ := by
  intro t ht
  rw [hmF232Terms_T10] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht | ht | ht <;>
    subst t <;>
    apply hm23Nonsingular_of_emod_ne_zero <;>
    norm_num [hm23DeltaBase]

theorem hmF232Terms_T11_hm23Nonsingular :
    ∀ t ∈ hmF232Terms (tijData 1 1).ell (tijData 1 1).X (tijData 1 1).Y,
      hm23Nonsingular t.mArg hm23DeltaBase t.mZ := by
  intro t ht
  rw [hmF232Terms_T11] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht | ht | ht <;>
    subst t <;>
    apply hm23Nonsingular_of_emod_ne_zero <;>
    norm_num [hm23DeltaBase]

theorem hmF232Terms_T12_hm23Nonsingular :
    ∀ t ∈ hmF232Terms (tijData 1 2).ell (tijData 1 2).X (tijData 1 2).Y,
      hm23Nonsingular t.mArg hm23DeltaBase t.mZ := by
  intro t ht
  rw [hmF232Terms_T12] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht | ht | ht <;>
    subst t <;>
    apply hm23Nonsingular_of_emod_ne_zero <;>
    norm_num [hm23DeltaBase]

theorem hmF232Terms_T20_hm23Nonsingular :
    ∀ t ∈ hmF232Terms (tijData 2 0).ell (tijData 2 0).X (tijData 2 0).Y,
      hm23Nonsingular t.mArg hm23DeltaBase t.mZ := by
  intro t ht
  rw [hmF232Terms_T20] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht | ht | ht <;>
    subst t <;>
    apply hm23Nonsingular_of_emod_ne_zero <;>
    norm_num [hm23DeltaBase]

theorem hmF232Terms_T21_hm23Nonsingular :
    ∀ t ∈ hmF232Terms (tijData 2 1).ell (tijData 2 1).X (tijData 2 1).Y,
      hm23Nonsingular t.mArg hm23DeltaBase t.mZ := by
  intro t ht
  rw [hmF232Terms_T21] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht | ht | ht <;>
    subst t <;>
    apply hm23Nonsingular_of_emod_ne_zero <;>
    norm_num [hm23DeltaBase]

theorem hmF232Terms_T22_hm23Nonsingular :
    ∀ t ∈ hmF232Terms (tijData 2 2).ell (tijData 2 2).X (tijData 2 2).Y,
      hm23Nonsingular t.mArg hm23DeltaBase t.mZ := by
  intro t ht
  rw [hmF232Terms_T22] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht | ht | ht <;>
    subst t <;>
    apply hm23Nonsingular_of_emod_ne_zero <;>
    norm_num [hm23DeltaBase]

theorem jLaurent90Product_emod_args_ne_zero (args : List ℤ)
    (hargs : ∀ a ∈ args, a % 90 ≠ 0) :
    jLaurent90Product args ≠ 0 := by
  induction args with
  | nil =>
      simp [jLaurent90Product]
  | cons a rest ih =>
      have ha : a % 90 ≠ 0 := hargs a (by simp)
      have hrest : ∀ b ∈ rest, b % 90 ≠ 0 := by
        intro b hb
        exact hargs b (by simp [hb])
      change jLaurent a 90 * jLaurent90Product rest ≠ 0
      exact mul_ne_zero (jLaurent_90_ne_zero_of_emod_ne_zero a ha) (ih hrest)

/-- Raw mod-90 denominator arguments from the thirty nonzero HM 2.3
correction entries.  Each row is `[18, z, a+18, a+z]` for one `(a,z)` from the
`T_ij` table; entries with `z=18` have zero correction and are omitted. -/
def thetaCorrectionRawMod90DenominatorArgs : List ℤ :=
  [18, -18, 54, 18, 18, -18, 9, -27, 18, 12, 54, 48,
  18, -12, 39, 9, 18, 12, 9, 3, 18, -12, -6, -36,
  18, 24, 54, 60, 18, -24, 24, -18, 18, 24, 9, 15,
  18, -24, -21, -63, 18, 42, 39, 63, 18, -42, 54, -6,
  18, 42, -6, 18, 18, -42, 9, -51, 18, -18, 39, 3,
  18, -18, -6, -42, 18, 12, 39, 33, 18, -12, 24, -6,
  18, 12, -6, -12, 18, -12, -21, -51, 18, 30, 24, 36,
  18, -30, 54, 6, 18, 30, -21, -9, 18, -30, 9, -39,
  18, 24, 24, 30, 18, -24, 39, -3, 18, 24, -21, -15,
  18, -24, -6, -48, 18, -18, 24, -12, 18, -18, -21, -57]

def thetaCorrectionMod90DenominatorProduct : QLaurent :=
  jLaurent90Product thetaCorrectionRawMod90DenominatorArgs

theorem thetaCorrectionMod90DenominatorProduct_ne_zero :
    thetaCorrectionMod90DenominatorProduct ≠ 0 := by
  unfold thetaCorrectionMod90DenominatorProduct
  apply jLaurent90Product_emod_args_ne_zero
  intro a ha
  norm_num [thetaCorrectionRawMod90DenominatorArgs] at ha ⊢
  omega

/-- The normalized single product left after replacing every
`jLaurent a 90` by `jLaurent 90 270 * redJ a` and cancelling `K^67`. -/
def thetaCorrectionNormalizedLHSRedJ : QLaurent :=
  Qpow 4 * redJ 3 ^ 6 * redJ 6 ^ 3 * redJ 9 ^ 4 * redJ 12 ^ 5 *
    redJ 15 ^ 6 * redJ 18 ^ 3 * redJ 21 ^ 6 * redJ 24 ^ 4 *
      redJ 27 ^ 5 * redJ 30 ^ 5 * redJ 33 ^ 6 * redJ 36 *
        redJ 39 ^ 6 * redJ 42 ^ 5 * redJ 45 ^ 2

/-- Data table for the normalized thirty-term correction polynomial `P30`.
Each row is `(coefficient, Q-shift, exponents of redJ 3,6,...,45)`. -/
def thetaCorrectionNormalizedP30Rows : List (ℤ × ℤ × List ℕ) :=
  [(-1, 0, [0, 1, 2, 0, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 1]),
    (1, 0, [0, 0, 4, 0, 0, 1, 1, 1, 6, 2, 0, 1, 0, 1, 2]),
    (-4, 1, [1, 0, 2, 0, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 1]),
    (-2, 1, [0, 0, 3, 2, 0, 1, 1, 1, 3, 3, 0, 1, 1, 2, 1]),
    (1, 1, [0, 0, 3, 1, 1, 0, 3, 1, 3, 1, 1, 2, 1, 1, 1]),
    (1, 1, [0, 0, 3, 2, 0, 0, 1, 3, 3, 2, 0, 2, 1, 1, 1]),
    (4, 1, [1, 1, 0, 0, 2, 1, 4, 1, 1, 1, 2, 1, 3, 1, 0]),
    (-1, 3, [0, 0, 5, 1, 0, 1, 0, 0, 4, 1, 0, 1, 1, 2, 3]),
    (1, 3, [0, 0, 3, 2, 0, 1, 1, 3, 3, 1, 0, 0, 1, 3, 1]),
    (-1, 4, [0, 0, 3, 1, 2, 1, 2, 0, 3, 1, 1, 1, 1, 2, 1]),
    (-1, 4, [1, 0, 3, 0, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1]),
    (-1, 4, [1, 0, 3, 1, 1, 0, 1, 1, 3, 1, 0, 2, 3, 1, 1]),
    (4, 4, [1, 0, 3, 1, 1, 1, 1, 0, 2, 1, 1, 1, 2, 2, 2]),
    (-1, 6, [1, 0, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 0, 1]),
    (-1, 6, [1, 0, 2, 1, 1, 1, 3, 1, 3, 0, 1, 1, 1, 2, 1]),
    (1, 6, [1, 1, 2, 1, 0, 1, 2, 0, 3, 1, 2, 1, 2, 1, 1]),
    (-4, 7, [2, 1, 0, 1, 1, 1, 3, 0, 1, 1, 3, 1, 3, 1, 0]),
    (-1, 7, [0, 2, 3, 0, 0, 1, 1, 2, 3, 2, 0, 1, 1, 2, 1]),
    (1, 7, [0, 2, 3, 1, 0, 0, 1, 1, 3, 2, 0, 2, 1, 2, 1]),
    (4, 7, [2, 0, 1, 1, 2, 0, 3, 1, 0, 1, 2, 2, 3, 1, 0]),
    (1, 9, [0, 0, 3, 3, 0, 1, 1, 2, 3, 3, 0, 0, 1, 1, 1]),
    (-1, 12, [0, 0, 5, 2, 0, 1, 0, 1, 5, 0, 0, 1, 1, 1, 2]),
    (-1, 13, [1, 1, 3, 0, 1, 1, 2, 1, 3, 1, 0, 1, 2, 1, 1]),
    (1, 13, [0, 2, 3, 2, 0, 1, 1, 0, 3, 1, 0, 1, 1, 3, 1]),
    (-1, 15, [0, 2, 3, 1, 0, 1, 1, 3, 3, 2, 0, 0, 1, 1, 1]),
    (4, 16, [1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 0, 2, 1, 0]),
    (-1, 18, [0, 0, 6, 1, 0, 1, 1, 2, 4, 1, 0, 1, 0, 0, 2]),
    (1, 19, [2, 1, 3, 1, 0, 1, 1, 0, 3, 1, 1, 1, 2, 1, 1]),
    (-1, 21, [0, 2, 3, 3, 0, 1, 1, 1, 3, 1, 0, 0, 1, 2, 1]),
    (4, 22, [1, 2, 1, 3, 1, 1, 2, 1, 1, 1, 1, 0, 2, 2, 0])]

theorem thetaCorrectionNormalizedLHSRedJ_totalDegree :
    6 + 3 + 4 + 5 + 6 + 3 + 6 + 4 + 5 + 5 + 6 + 1 + 6 + 5 + 2 = 67 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term01_totalDegree :
    0 + 1 + 2 + 0 + 1 + 1 + 3 + 1 + 3 + 1 + 1 + 1 + 2 + 1 + 1 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term02_totalDegree :
    0 + 0 + 4 + 0 + 0 + 1 + 1 + 1 + 6 + 2 + 0 + 1 + 0 + 1 + 2 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term03_totalDegree :
    1 + 0 + 2 + 0 + 1 + 1 + 2 + 1 + 4 + 2 + 1 + 1 + 1 + 1 + 1 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term04_totalDegree :
    0 + 0 + 3 + 2 + 0 + 1 + 1 + 1 + 3 + 3 + 0 + 1 + 1 + 2 + 1 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term05_totalDegree :
    0 + 0 + 3 + 1 + 1 + 0 + 3 + 1 + 3 + 1 + 1 + 2 + 1 + 1 + 1 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term06_totalDegree :
    0 + 0 + 3 + 2 + 0 + 0 + 1 + 3 + 3 + 2 + 0 + 2 + 1 + 1 + 1 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term07_totalDegree :
    1 + 1 + 0 + 0 + 2 + 1 + 4 + 1 + 1 + 1 + 2 + 1 + 3 + 1 + 0 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term08_totalDegree :
    0 + 0 + 5 + 1 + 0 + 1 + 0 + 0 + 4 + 1 + 0 + 1 + 1 + 2 + 3 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term09_totalDegree :
    0 + 0 + 3 + 2 + 0 + 1 + 1 + 3 + 3 + 1 + 0 + 0 + 1 + 3 + 1 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term10_totalDegree :
    0 + 0 + 3 + 1 + 2 + 1 + 2 + 0 + 3 + 1 + 1 + 1 + 1 + 2 + 1 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term11_totalDegree :
    1 + 0 + 3 + 0 + 1 + 1 + 1 + 1 + 3 + 2 + 2 + 1 + 1 + 1 + 1 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term12_totalDegree :
    1 + 0 + 3 + 1 + 1 + 0 + 1 + 1 + 3 + 1 + 0 + 2 + 3 + 1 + 1 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term13_totalDegree :
    1 + 0 + 3 + 1 + 1 + 1 + 1 + 0 + 2 + 1 + 1 + 1 + 2 + 2 + 2 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term14_totalDegree :
    1 + 0 + 2 + 1 + 1 + 1 + 2 + 1 + 3 + 2 + 2 + 1 + 1 + 0 + 1 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term15_totalDegree :
    1 + 0 + 2 + 1 + 1 + 1 + 3 + 1 + 3 + 0 + 1 + 1 + 1 + 2 + 1 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term16_totalDegree :
    1 + 1 + 2 + 1 + 0 + 1 + 2 + 0 + 3 + 1 + 2 + 1 + 2 + 1 + 1 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term17_totalDegree :
    2 + 1 + 0 + 1 + 1 + 1 + 3 + 0 + 1 + 1 + 3 + 1 + 3 + 1 + 0 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term18_totalDegree :
    0 + 2 + 3 + 0 + 0 + 1 + 1 + 2 + 3 + 2 + 0 + 1 + 1 + 2 + 1 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term19_totalDegree :
    0 + 2 + 3 + 1 + 0 + 0 + 1 + 1 + 3 + 2 + 0 + 2 + 1 + 2 + 1 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term20_totalDegree :
    2 + 0 + 1 + 1 + 2 + 0 + 3 + 1 + 0 + 1 + 2 + 2 + 3 + 1 + 0 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term21_totalDegree :
    0 + 0 + 3 + 3 + 0 + 1 + 1 + 2 + 3 + 3 + 0 + 0 + 1 + 1 + 1 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term22_totalDegree :
    0 + 0 + 5 + 2 + 0 + 1 + 0 + 1 + 5 + 0 + 0 + 1 + 1 + 1 + 2 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term23_totalDegree :
    1 + 1 + 3 + 0 + 1 + 1 + 2 + 1 + 3 + 1 + 0 + 1 + 2 + 1 + 1 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term24_totalDegree :
    0 + 2 + 3 + 2 + 0 + 1 + 1 + 0 + 3 + 1 + 0 + 1 + 1 + 3 + 1 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term25_totalDegree :
    0 + 2 + 3 + 1 + 0 + 1 + 1 + 3 + 3 + 2 + 0 + 0 + 1 + 1 + 1 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term26_totalDegree :
    1 + 2 + 1 + 1 + 1 + 1 + 2 + 3 + 1 + 2 + 1 + 0 + 2 + 1 + 0 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term27_totalDegree :
    0 + 0 + 6 + 1 + 0 + 1 + 1 + 2 + 4 + 1 + 0 + 1 + 0 + 0 + 2 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term28_totalDegree :
    2 + 1 + 3 + 1 + 0 + 1 + 1 + 0 + 3 + 1 + 1 + 1 + 2 + 1 + 1 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term29_totalDegree :
    0 + 2 + 3 + 3 + 0 + 1 + 1 + 1 + 3 + 1 + 0 + 0 + 1 + 2 + 1 = 19 := by
  norm_num

theorem thetaCorrectionNormalizedP30_term30_totalDegree :
    1 + 2 + 1 + 3 + 1 + 1 + 2 + 1 + 1 + 1 + 1 + 0 + 2 + 2 + 0 = 19 := by
  norm_num

/-! ## Elementary Appell cancellation algebra

**Note:** The old standalone theta-correction collapse endpoint formerly lived in
`Chapter10_HM_ThetaCollapse.lean`.  That module is now a deprecated tombstone:
the available producers are axiom-tainted, so no theta-correction collapse theorem
is exported there until a no-axiom proof is available. -/

/--
Raw coefficient of the common Appell base `M(-9,18)` after the HM 2.3
change-of-`z` normalization, with the theta factors still unsimplified.
-/
def appellCoeffMNeg9 (theta1 J3 J9 J15 : QLaurent) : QLaurent :=
  -2 * Qpow (-17) * J9 * (J9 ^ 2 - 2 * J9 * theta1 + theta1 ^ 2) +
    2 * Qpow (-16) * J15 * (J9 ^ 2 - J9 * theta1) +
      2 * Qpow (-16) * J3 * (J9 ^ 2 - J9 * theta1)

/-- Raw coefficient of the common Appell base `M(36,18)`. -/
def appellCoeffM36 (theta1 J0 J6 J9 J12 : QLaurent) : QLaurent :=
  -2 * Qpow 1 * J0 * (J9 ^ 2 - 2 * J9 * theta1 + theta1 ^ 2) +
    2 * Qpow (-1) * J6 * (J9 ^ 2 - J9 * theta1) -
      2 * Qpow (-1) * J12 * (J9 ^ 2 - J9 * theta1)

/-- Raw coefficient of the common Appell base `M(21,18)`. -/
def appellCoeffM21 (theta1 J3 J9 J15 : QLaurent) : QLaurent :=
  2 * Qpow (-4) * J9 * (J9 ^ 2 - J9 * theta1) -
    2 * Qpow (-3) * J15 * J9 ^ 2 -
      2 * Qpow (-3) * J3 * J9 ^ 2

/-- Raw coefficient of the common Appell base `M(-39,18)`. -/
def appellCoeffMNeg39 (theta1 J3 J9 J15 : QLaurent) : QLaurent :=
  2 * Qpow (-40) * J9 * (J9 ^ 2 - J9 * theta1) -
    2 * Qpow (-39) * J15 * J9 ^ 2 -
      2 * Qpow (-39) * J3 * J9 ^ 2

/-- Raw coefficient of the common Appell base `M(-24,18)`. -/
def appellCoeffMNeg24 (theta1 J0 J6 J9 J12 : QLaurent) : QLaurent :=
  -2 * Qpow (-25) * J0 * (J9 ^ 2 - J9 * theta1) +
    2 * Qpow (-27) * J6 * J9 ^ 2 -
      2 * Qpow (-27) * J12 * J9 ^ 2

/-- Raw coefficient of the common Appell base `M(6,18)`. -/
def appellCoeffM6 (theta1 J0 J6 J9 J12 : QLaurent) : QLaurent :=
  2 * Qpow (-7) * J0 * (J9 ^ 2 - J9 * theta1) -
    2 * Qpow (-9) * J6 * J9 ^ 2 +
      2 * Qpow (-9) * J12 * J9 ^ 2

/-- The `M(-9,18)` coefficient reduces by the `Θ₁=J₉-2QJ₃` dissection. -/
theorem appellCoeffMNeg9_reduce (theta1 J3 J9 J15 : QLaurent)
    (hθ : theta1 = J9 - 2 * Qpow 1 * J3) :
    appellCoeffMNeg9 theta1 J3 J9 J15 =
      4 * Qpow (-15) * J3 * J9 * (J15 - J3) := by
  have hq17 : Qpow (-17) * Qpow 1 ^ 2 = Qpow (-15) := by
    rw [sq, ← mul_assoc, Qpow_mul, Qpow_mul]
    norm_num
  have hq16 : Qpow (-16) * Qpow 1 = Qpow (-15) := by
    rw [Qpow_mul]
    norm_num
  calc
    appellCoeffMNeg9 theta1 J3 J9 J15
        = -8 * (Qpow (-17) * Qpow 1 ^ 2) * J3 ^ 2 * J9 +
            4 * (Qpow (-16) * Qpow 1) * J15 * J3 * J9 +
              4 * (Qpow (-16) * Qpow 1) * J3 ^ 2 * J9 := by
          rw [hθ]
          unfold appellCoeffMNeg9
          ring
    _ = 4 * Qpow (-15) * J3 * J9 * (J15 - J3) := by
          rw [hq17, hq16]
          ring

/-- The `M(36,18)` coefficient reduces by `J₀=0` and the theta dissection. -/
theorem appellCoeffM36_reduce (theta1 J0 J3 J6 J9 J12 : QLaurent)
    (hθ : theta1 = J9 - 2 * Qpow 1 * J3) (hJ0 : J0 = 0) :
    appellCoeffM36 theta1 J0 J6 J9 J12 =
      4 * J3 * J9 * (J6 - J12) := by
  have hqm1 : Qpow (-1) * Qpow 1 = 1 := by
    rw [Qpow_mul]
    norm_num
  calc
    appellCoeffM36 theta1 J0 J6 J9 J12
        = 4 * (Qpow (-1) * Qpow 1) * J3 * J9 * (J6 - J12) := by
          rw [hθ, hJ0]
          unfold appellCoeffM36
          ring
    _ = 4 * J3 * J9 * (J6 - J12) := by
          rw [hqm1]
          ring

/-- The `M(21,18)` coefficient reduces to the `J₁₅-J₃` symmetry factor. -/
theorem appellCoeffM21_reduce (theta1 J3 J9 J15 : QLaurent)
    (hθ : theta1 = J9 - 2 * Qpow 1 * J3) :
    appellCoeffM21 theta1 J3 J9 J15 =
      2 * Qpow (-3) * J9 ^ 2 * (J3 - J15) := by
  have hqm4 : Qpow (-4) * Qpow 1 = Qpow (-3) := by
    rw [Qpow_mul]
    norm_num
  calc
    appellCoeffM21 theta1 J3 J9 J15
        = 4 * (Qpow (-4) * Qpow 1) * J3 * J9 ^ 2 -
            2 * Qpow (-3) * J15 * J9 ^ 2 -
              2 * Qpow (-3) * J3 * J9 ^ 2 := by
          rw [hθ]
          unfold appellCoeffM21
          ring
    _ = 2 * Qpow (-3) * J9 ^ 2 * (J3 - J15) := by
          rw [hqm4]
          ring

/-- The `M(-39,18)` coefficient reduces to the `J₁₅-J₃` symmetry factor. -/
theorem appellCoeffMNeg39_reduce (theta1 J3 J9 J15 : QLaurent)
    (hθ : theta1 = J9 - 2 * Qpow 1 * J3) :
    appellCoeffMNeg39 theta1 J3 J9 J15 =
      2 * Qpow (-39) * J9 ^ 2 * (J3 - J15) := by
  have hqm40 : Qpow (-40) * Qpow 1 = Qpow (-39) := by
    rw [Qpow_mul]
    norm_num
  calc
    appellCoeffMNeg39 theta1 J3 J9 J15
        = 4 * (Qpow (-40) * Qpow 1) * J3 * J9 ^ 2 -
            2 * Qpow (-39) * J15 * J9 ^ 2 -
              2 * Qpow (-39) * J3 * J9 ^ 2 := by
          rw [hθ]
          unfold appellCoeffMNeg39
          ring
    _ = 2 * Qpow (-39) * J9 ^ 2 * (J3 - J15) := by
          rw [hqm40]
          ring

/-- The `M(-24,18)` coefficient reduces to the `J₁₂-J₆` symmetry factor. -/
theorem appellCoeffMNeg24_reduce (theta1 J0 J6 J9 J12 : QLaurent) (hJ0 : J0 = 0) :
    appellCoeffMNeg24 theta1 J0 J6 J9 J12 =
      2 * Qpow (-27) * J9 ^ 2 * (J6 - J12) := by
  rw [hJ0]
  unfold appellCoeffMNeg24
  ring

/-- The `M(6,18)` coefficient reduces to the `J₁₂-J₆` symmetry factor. -/
theorem appellCoeffM6_reduce (theta1 J0 J6 J9 J12 : QLaurent) (hJ0 : J0 = 0) :
    appellCoeffM6 theta1 J0 J6 J9 J12 =
      2 * Qpow (-9) * J9 ^ 2 * (J12 - J6) := by
  rw [hJ0]
  unfold appellCoeffM6
  ring

theorem appellCoeffMNeg9_zero (theta1 J3 J9 J15 : QLaurent)
    (hθ : theta1 = J9 - 2 * Qpow 1 * J3) (hJ15 : J15 = J3) :
    appellCoeffMNeg9 theta1 J3 J9 J15 = 0 := by
  rw [appellCoeffMNeg9_reduce theta1 J3 J9 J15 hθ, hJ15]
  ring

theorem appellCoeffM36_zero (theta1 J0 J3 J6 J9 J12 : QLaurent)
    (hθ : theta1 = J9 - 2 * Qpow 1 * J3) (hJ0 : J0 = 0) (hJ12 : J12 = J6) :
    appellCoeffM36 theta1 J0 J6 J9 J12 = 0 := by
  rw [appellCoeffM36_reduce theta1 J0 J3 J6 J9 J12 hθ hJ0, hJ12]
  ring

theorem appellCoeffM21_zero (theta1 J3 J9 J15 : QLaurent)
    (hθ : theta1 = J9 - 2 * Qpow 1 * J3) (hJ15 : J15 = J3) :
    appellCoeffM21 theta1 J3 J9 J15 = 0 := by
  rw [appellCoeffM21_reduce theta1 J3 J9 J15 hθ, hJ15]
  ring

theorem appellCoeffMNeg39_zero (theta1 J3 J9 J15 : QLaurent)
    (hθ : theta1 = J9 - 2 * Qpow 1 * J3) (hJ15 : J15 = J3) :
    appellCoeffMNeg39 theta1 J3 J9 J15 = 0 := by
  rw [appellCoeffMNeg39_reduce theta1 J3 J9 J15 hθ, hJ15]
  ring

theorem appellCoeffMNeg24_zero (theta1 J0 J6 J9 J12 : QLaurent)
    (hJ0 : J0 = 0) (hJ12 : J12 = J6) :
    appellCoeffMNeg24 theta1 J0 J6 J9 J12 = 0 := by
  rw [appellCoeffMNeg24_reduce theta1 J0 J6 J9 J12 hJ0, hJ12]
  ring

theorem appellCoeffM6_zero (theta1 J0 J6 J9 J12 : QLaurent)
    (hJ0 : J0 = 0) (hJ12 : J12 = J6) :
    appellCoeffM6 theta1 J0 J6 J9 J12 = 0 := by
  rw [appellCoeffM6_reduce theta1 J0 J6 J9 J12 hJ0, hJ12]
  ring

/-- Reduced Appell contribution after all six common `M(a,18)` bases are
collected.  The coefficients are exactly the elementary table produced by the
HM 2.3 change-of-`z`, `J`-shift normalization, and the `Θ₁` dissection. -/
def appellCancelExpr
    (theta1 J0 J3 J6 J9 J12 J15 MNeg39 MNeg24 MNeg9 M6 M21 M36 : QLaurent) :
    QLaurent :=
  appellCoeffMNeg39 theta1 J3 J9 J15 * MNeg39 +
    appellCoeffMNeg24 theta1 J0 J6 J9 J12 * MNeg24 +
      appellCoeffMNeg9 theta1 J3 J9 J15 * MNeg9 +
        appellCoeffM6 theta1 J0 J6 J9 J12 * M6 +
          appellCoeffM21 theta1 J3 J9 J15 * M21 +
            appellCoeffM36 theta1 J0 J6 J9 J12 * M36

/-- All six reduced Appell coefficients vanish from `J₀=0`, `J₁₅=J₃`,
`J₁₂=J₆`, and the elementary dissection `Θ₁=J₉-2QJ₃`. -/
theorem appell_coeffs_zero
    (theta1 J0 J3 J6 J9 J12 J15 : QLaurent)
    (hθ : theta1 = J9 - 2 * Qpow 1 * J3) (hJ0 : J0 = 0)
    (hJ15 : J15 = J3) (hJ12 : J12 = J6) :
    appellCoeffMNeg39 theta1 J3 J9 J15 = 0 ∧
      appellCoeffMNeg24 theta1 J0 J6 J9 J12 = 0 ∧
        appellCoeffMNeg9 theta1 J3 J9 J15 = 0 ∧
          appellCoeffM6 theta1 J0 J6 J9 J12 = 0 ∧
            appellCoeffM21 theta1 J3 J9 J15 = 0 ∧
              appellCoeffM36 theta1 J0 J6 J9 J12 = 0 := by
  exact ⟨appellCoeffMNeg39_zero theta1 J3 J9 J15 hθ hJ15,
    appellCoeffMNeg24_zero theta1 J0 J6 J9 J12 hJ0 hJ12,
    appellCoeffMNeg9_zero theta1 J3 J9 J15 hθ hJ15,
    appellCoeffM6_zero theta1 J0 J6 J9 J12 hJ0 hJ12,
    appellCoeffM21_zero theta1 J3 J9 J15 hθ hJ15,
    appellCoeffM36_zero theta1 J0 J3 J6 J9 J12 hθ hJ0 hJ12⟩

/--
Elementary Appell-Lerch cancellation in Chan's special combination, after HM
2.3 has moved every Appell term to the six common bases
`M(-39,18)`, `M(-24,18)`, `M(-9,18)`, `M(6,18)`, `M(21,18)`, and `M(36,18)`.
-/
theorem appell_cancel
    (theta1 J0 J3 J6 J9 J12 J15 MNeg39 MNeg24 MNeg9 M6 M21 M36 : QLaurent)
    (hθ : theta1 = J9 - 2 * Qpow 1 * J3) (hJ0 : J0 = 0)
    (hJ15 : J15 = J3) (hJ12 : J12 = J6) :
    appellCancelExpr theta1 J0 J3 J6 J9 J12 J15 MNeg39 MNeg24 MNeg9 M6 M21 M36 = 0 := by
  unfold appellCancelExpr
  rw [appellCoeffMNeg39_zero theta1 J3 J9 J15 hθ hJ15,
    appellCoeffMNeg24_zero theta1 J0 J6 J9 J12 hJ0 hJ12,
    appellCoeffMNeg9_zero theta1 J3 J9 J15 hθ hJ15,
    appellCoeffM6_zero theta1 J0 J6 J9 J12 hJ0 hJ12,
    appellCoeffM21_zero theta1 J3 J9 J15 hθ hJ15,
    appellCoeffM36_zero theta1 J0 J3 J6 J9 J12 hθ hJ0 hJ12]
  ring

/-- The real `J₀=0` fact for the Chapter 10 modulus `18`. -/
theorem jLaurent_0_18_eq_zero :
    jLaurent 0 18 = 0 := by
  simpa using jLaurent_zero 18 (by norm_num)

/-- The real `J₁₅=J₃` fact for the Chapter 10 modulus `18`. -/
theorem jLaurent_15_18_eq_3_18 :
    jLaurent 15 18 = jLaurent 3 18 := by
  have h := jLaurent_symm 3 18 (by norm_num)
  norm_num at h
  exact h.symm

/-- The real `J₁₂=J₆` fact for the Chapter 10 modulus `18`. -/
theorem jLaurent_12_18_eq_6_18 :
    jLaurent 12 18 = jLaurent 6 18 := by
  have h := jLaurent_symm 6 18 (by norm_num)
  norm_num at h
  exact h.symm

/-- Appell cancellation with the actual Chapter 10 theta factors substituted. -/
theorem appell_cancel_jLaurent
    (MNeg39 MNeg24 MNeg9 M6 M21 M36 : QLaurent) :
    appellCancelExpr thetaOneLaurent (jLaurent 0 18) (jLaurent 3 18)
        (jLaurent 6 18) thetaNineLaurent (jLaurent 12 18) (jLaurent 15 18)
        MNeg39 MNeg24 MNeg9 M6 M21 M36 = 0 := by
  exact appell_cancel thetaOneLaurent (jLaurent 0 18) (jLaurent 3 18)
    (jLaurent 6 18) thetaNineLaurent (jLaurent 12 18) (jLaurent 15 18)
    MNeg39 MNeg24 MNeg9 M6 M21 M36 thetaOneLaurent_dissection
    jLaurent_0_18_eq_zero jLaurent_15_18_eq_3_18 jLaurent_12_18_eq_6_18

end

end Ch10HM
end Pending
end QseriesFormalization
