import QseriesFormalization.Pending.Chapter10_RootPairGeneral
import Mathlib

/-!
# General coefficient kernel for the Hahn-series Hecke--Appell proof

This file formalizes the coefficientwise route for arbitrary positive `n,p`.
The theta correction is intentionally represented by its coefficient function:
for `n ≥ 2` it need not be an element of the q-first Hahn ring, although every
fixed coefficient is a finite sum.
-/

namespace QseriesFormalization.Pending.Ch10GeneralHahnCoeff

open QseriesFormalization.Pending.Ch10RootPairGeneral
open scoped Classical

noncomputable section

/-- Integer sign with the paper's convention `sg(0)=1`. -/
def intSign (z : ℤ) : ℤ := if 0 ≤ z then 1 else -1

/-- The sign `(-1)^z`, interpreted using the parity of an integer. -/
def negOnePow (z : ℤ) : ℚ := (-1 : ℚ) ^ z.natAbs

/-- The common q-exponent on the theta shell. -/
def shellExponent (n p r s w : ℤ) : ℤ :=
  heckeExp n p r s + genN n p * C2 (w + 1)

/-- Indicator of a fixed q-degree on the theta shell. -/
def shellIndicator (n p e r s w : ℤ) : ℚ :=
  if e = shellExponent n p r s w then 1 else 0

private theorem C2_succ_nonneg (w : ℤ) : 0 ≤ C2 (w + 1) := by
  have htwo := two_mul_C2 (w + 1)
  simp only [C2Twice] at htwo
  by_cases hw : 0 ≤ w
  · nlinarith
  · have hw' : w ≤ -1 := by omega
    nlinarith

theorem genN_pos {n p : ℤ} (hn : 0 < n) (hp : 0 < p) : 0 < genN n p := by
  rw [genN_eq]
  exact mul_pos (mul_pos hn hp) (by omega)

/-- A fixed `(q,x,y)` coefficient meets only finitely many theta shells. -/
theorem shellIndicator_support_finite
    (n p e r s : ℤ) (hn : 0 < n) (hp : 0 < p) :
    (Function.support (shellIndicator n p e r s)).Finite := by
  classical
  let D : ℤ := e - heckeExp n p r s
  let M : ℤ := 2 * |D| + 2
  refine (Set.finite_Icc (-M) M).subset ?_
  intro w hw
  rw [Function.mem_support] at hw
  have heq : e = shellExponent n p r s w := by
    by_contra hne
    exact hw (by simp [shellIndicator, hne])
  have hN := genN_pos hn hp
  have hC := C2_succ_nonneg w
  have hD : D = genN n p * C2 (w + 1) := by
    dsimp [D]
    rw [heq]
    simp [shellExponent]
  have hN1 : 1 ≤ genN n p := by omega
  have hCleD : C2 (w + 1) ≤ D := by
    rw [hD]
    nlinarith
  have hDabs : D ≤ |D| := le_abs_self D
  have htwo := two_mul_C2 (w + 1)
  simp only [C2Twice] at htwo
  rw [Set.mem_Icc]
  constructor <;> dsimp [M] <;> nlinarith

/-- Two indices on the same fixed theta shell are the usual quadratic pair. -/
theorem shell_fiber_pair
    (n p e r s w z : ℤ) (hn : 0 < n) (hp : 0 < p)
    (hw : e = shellExponent n p r s w)
    (hz : e = shellExponent n p r s z) :
    z = w ∨ z = -w - 1 := by
  have hN := genN_pos hn hp
  have hmul : genN n p * C2 (z + 1) = genN n p * C2 (w + 1) := by
    rw [hw] at hz
    simpa [shellExponent] using hz.symm
  have hC : C2 (z + 1) = C2 (w + 1) := by
    nlinarith
  have hz2 := two_mul_C2 (z + 1)
  have hw2 := two_mul_C2 (w + 1)
  simp only [C2Twice] at hz2 hw2
  have hprod : (z - w) * (z + w + 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hprod with h | h
  · left; omega
  · right; omega

/-- Twice the leading q-exponent of the denominator monomial in row `t`. -/
def denominatorExponentTwice (n p t k : ℤ) : ℤ :=
  gammaTwice n p t k

/-- Signed geometric-branch coefficient, using a doubled leading exponent. -/
def branchCoefficient (gammaTwice ell : ℤ) : ℚ :=
  if 0 < gammaTwice then
    if 0 ≤ ell then 1 else 0
  else if gammaTwice < 0 then
    if ell < 0 then -1 else 0
  else 0

theorem branchCoefficient_eq_signs {gammaTwice ell : ℤ}
    (hgamma : gammaTwice ≠ 0) :
    branchCoefficient gammaTwice ell =
      ((intSign ell + intSign gammaTwice : ℤ) : ℚ) / 2 := by
  unfold branchCoefficient intSign
  by_cases hg : 0 < gammaTwice
  · have hgn : ¬ gammaTwice < 0 := by omega
    have hg0 : 0 ≤ gammaTwice := le_of_lt hg
    by_cases he : 0 ≤ ell <;> norm_num [hg, hgn, hg0, he]
  · have hgl : gammaTwice < 0 := by omega
    have hgn : ¬ 0 ≤ gammaTwice := by omega
    by_cases he : ell < 0
    · have he0 : ¬ 0 ≤ ell := not_le_of_gt he
      norm_num [hg, hgl, hgn, he, he0]
    · have he0 : 0 ≤ ell := le_of_not_gt he
      norm_num [hg, hgl, hgn, he, he0]

/-- Coefficientwise inverse law for the signed Hahn geometric branch:
`(1-M) * ∑ c_ℓ M^ℓ = 1`. -/
theorem branchCoefficient_sub_shift {gammaTwice ell : ℤ}
    (hgamma : gammaTwice ≠ 0) :
    branchCoefficient gammaTwice ell - branchCoefficient gammaTwice (ell - 1) =
      if ell = 0 then 1 else 0 := by
  unfold branchCoefficient
  by_cases hg : 0 < gammaTwice
  · have hgn : ¬ gammaTwice < 0 := by omega
    by_cases h0 : ell = 0
    · subst ell
      norm_num [hg, hgn]
    · by_cases he : 0 < ell
      · have he0 : 0 ≤ ell := le_of_lt he
        have hem : 0 ≤ ell - 1 := by omega
        have he1 : 1 ≤ ell := by omega
        norm_num [hg, hgn, h0, he0, hem, he1]
      · have he0 : ¬ 0 ≤ ell := by omega
        have hem : ¬ 0 ≤ ell - 1 := by omega
        have helt : ell < 1 := by omega
        norm_num [hg, hgn, h0, he0, hem, helt]
  · have hgl : gammaTwice < 0 := by omega
    by_cases h0 : ell = 0
    · subst ell
      norm_num [hg, hgl]
    · by_cases he : ell < 0
      · have hem : ell - 1 < 0 := by omega
        norm_num [hg, hgl, h0, he, hem]
      · have hem : ¬ ell - 1 < 0 := by omega
        norm_num [hg, hgl, h0, he, hem]

theorem intSign_denominatorExponentTwice
    (n p t k : ℤ) (hn : 0 < n) (hp : 0 < p) :
    intSign (denominatorExponentTwice n p t k) = -intSign (WTwice n t k) := by
  by_cases hW : 0 ≤ WTwice n t k
  · have hg := gammaTwice_neg_of_WTwice_nonneg n p t k hn hp hW
    simp [denominatorExponentTwice, intSign, hW, not_le_of_gt hg]
  · have hWneg : WTwice n t k < 0 := by omega
    have hg := gammaTwice_pos_of_WTwice_neg n p t k hn hp hWneg
    simp [denominatorExponentTwice, intSign, hW, le_of_lt hg]

theorem branchCoefficient_denominator_eq
    (n p t k ell : ℤ) (hn : 0 < n) (hp : 0 < p) :
    branchCoefficient (denominatorExponentTwice n p t k) ell =
      ((intSign ell - intSign (WTwice n t k) : ℤ) : ℚ) / 2 := by
  unfold denominatorExponentTwice
  rw [branchCoefficient_eq_signs (gammaTwice_ne_zero n p t k hn hp)]
  have hsign := intSign_denominatorExponentTwice n p t k hn hp
  unfold denominatorExponentTwice at hsign
  rw [hsign]
  push_cast
  ring

/-- Raw q-exponent after the `x,y` monomial constraints have fixed `t,ell,u`. -/
def sRowRawExponent (n p r t ell k : ℤ) : ℤ :=
  let u := r + (n + p) * ell
  n * C2 t + n * C2 u + (n + p) * t * u + genN n p * C2 k +
    ell * (genN n p * (k - 1) + genA0 n p - t * genDelta n p)

theorem sRowRawExponent_eq_shell (n p r t ell k : ℤ) :
    sRowRawExponent n p r t ell k =
      shellExponent n p r (n * ell + t) (k + ell - 1) := by
  simpa [sRowRawExponent, shellExponent, add_assoc] using
    row_exponent_identity r t ell k n p

/-- One raw coefficient contribution from the cleared `s`-split Appell rows. -/
def sRowRawKernel (n p e r s k : ℤ) : ℚ :=
  let ell := s / n
  let t := s % n
  negOnePow (r + s) * branchCoefficient (denominatorExponentTwice n p t k) ell *
    (if e = sRowRawExponent n p r t ell k then 1 else 0)

/-- Raw coefficient of the sum of all cleared `s`-split Appell rows. -/
def sRowRawCoefficient (n p e r s : ℤ) : ℚ :=
  ∑ᶠ k : ℤ, sRowRawKernel n p e r s k

private theorem div_decomposition (s n : ℤ) :
    n * (s / n) + s % n = s := by
  have h := Int.emod_add_mul_ediv s n
  linarith

private theorem emod_nonneg_of_pos (s n : ℤ) (hn : 0 < n) : 0 ≤ s % n :=
  Int.emod_nonneg _ (ne_of_gt hn)

private theorem emod_lt_of_pos (s n : ℤ) (hn : 0 < n) : s % n < n :=
  Int.emod_lt_of_pos _ hn

/-! ### Faithful residue-row bridge before the residue `t` is forced -/

/-- The q-exponent in the displayed cleared `s`-row before substituting the
forced theta index `u = r + (n+p)ℓ`. -/
def sRowResidueExponent (n p t u ell k : ℤ) : ℤ :=
  n * C2 t + n * C2 u + (n + p) * t * u + genN n p * C2 k +
    ell * (genN n p * (k - 1) + genA0 n p - t * genDelta n p)

/-- Coefficient contribution of residue row `t` in the displayed cleared
Appell sum. The `x,y` coefficient equations determine `ell` and `u`, while
the explicit condition records that the chosen residue really reconstructs
`s`. -/
def sRowResidueKernel (n p e r s t k : ℤ) : ℚ :=
  let ell := (s - t) / n
  let u := r + (n + p) * ell
  if 0 ≤ t ∧ t < n ∧ s = n * ell + t then
    negOnePow (t + u + n * ell - (n + p) * ell) *
      branchCoefficient (denominatorExponentTwice n p t k) ell *
        (if e = sRowResidueExponent n p t u ell k then 1 else 0)
  else 0

/-- Coefficient of the explicit finite residue sum of cleared `s`-rows. -/
def sRowResidueCoefficient (n p e r s : ℤ) : ℚ :=
  ∑ t ∈ Finset.Icc (0 : ℤ) (n - 1), ∑ᶠ k : ℤ, sRowResidueKernel n p e r s t k

private theorem quotient_remainder_unique
    (s n t ell : ℤ) (hn : 0 < n) (ht0 : 0 ≤ t) (htn : t < n)
    (hdecomp : s = n * ell + t) :
    ell = s / n ∧ t = s % n := by
  have hs := div_decomposition s n
  have hr0 := emod_nonneg_of_pos s n hn
  have hrn := emod_lt_of_pos s n hn
  have hell : ell = s / n := by
    apply le_antisymm
    · by_contra hle
      have hgap : 0 ≤ n * (ell - s / n - 1) :=
        mul_nonneg (le_of_lt hn) (by omega)
      nlinarith
    · by_contra hle
      have hgap : 0 ≤ n * (s / n - ell - 1) :=
        mul_nonneg (le_of_lt hn) (by omega)
      nlinarith
  constructor
  · exact hell
  · rw [hell] at hdecomp
    nlinarith

private theorem sub_emod_ediv (s n : ℤ) (hn : 0 < n) :
    (s - s % n) / n = s / n := by
  have hs := div_decomposition s n
  have hn0 : n ≠ 0 := ne_of_gt hn
  calc
    (s - s % n) / n = (n * (s / n)) / n := by congr 1; omega
    _ = s / n := Int.mul_ediv_cancel_left _ hn0

private theorem sRowResidueKernel_emod
    (n p e r s k : ℤ) (hn : 0 < n) :
    sRowResidueKernel n p e r s (s % n) k =
      sRowRawKernel n p e r s k := by
  have ht0 := emod_nonneg_of_pos s n hn
  have htn := emod_lt_of_pos s n hn
  have hs := div_decomposition s n
  have hell := sub_emod_ediv s n hn
  unfold sRowResidueKernel sRowRawKernel sRowResidueExponent
  dsimp only
  rw [hell]
  simp only [ht0, htn, hs, and_self, if_true]
  have hsign :
      s % n + (r + (n + p) * (s / n)) + n * (s / n) -
          (n + p) * (s / n) = r + s := by
    nlinarith
  rw [hsign]
  rfl

/-- Monomial forcing collapses the explicit finite residue sum to the raw
coefficient kernel used in the general row proof. -/
theorem sRowResidueCoefficient_eq_raw
    (n p e r s : ℤ) (hn : 0 < n) :
    sRowResidueCoefficient n p e r s = sRowRawCoefficient n p e r s := by
  classical
  unfold sRowResidueCoefficient sRowRawCoefficient
  have hmem : s % n ∈ Finset.Icc (0 : ℤ) (n - 1) := by
    rw [Finset.mem_Icc]
    constructor
    · exact emod_nonneg_of_pos s n hn
    · have := emod_lt_of_pos s n hn
      omega
  rw [Finset.sum_eq_single_of_mem (s % n) hmem]
  · apply finsum_congr
    intro k
    exact sRowResidueKernel_emod n p e r s k hn
  · intro t ht htne
    apply finsum_eq_zero_of_forall_eq_zero
    intro k
    unfold sRowResidueKernel
    dsimp only
    rw [if_neg]
    intro hrow
    have hu := quotient_remainder_unique s n t ((s - t) / n)
      hn hrow.1 hrow.2.1 hrow.2.2
    exact htne hu.2

/-- Doubled `V_w = s - nw - (n+1)/2`, kept integral for every parity of `n`. -/
def VTwice (n s w : ℤ) : ℤ := 2 * s - 2 * n * w - n - 1

/-- The target normal form for one `s`-row shell contribution. -/
def sRowNormalKernel (n p e r s w : ℤ) : ℚ :=
  negOnePow (r + s) *
    (((intSign s - intSign (VTwice n s w) : ℤ) : ℚ) / 2) *
    shellIndicator n p e r s w

/-- Target coefficient normal form for all cleared `s`-split Appell rows. -/
def sRowNormalCoefficient (n p e r s : ℤ) : ℚ :=
  ∑ᶠ w : ℤ, sRowNormalKernel n p e r s w

private def kToW (ell : ℤ) : ℤ ≃ ℤ where
  toFun k := k + ell - 1
  invFun w := w - ell + 1
  left_inv := by intro k; ring
  right_inv := by intro w; ring

theorem intSign_ediv_eq (s n : ℤ) (hn : 0 < n) :
    intSign (s / n) = intSign s := by
  have ht0 := emod_nonneg_of_pos s n hn
  have htn := emod_lt_of_pos s n hn
  have hs := div_decomposition s n
  have hiff := ell_nonneg_iff_s_nonneg n (s % n) (s / n) hn ht0 htn
  rw [hs] at hiff
  unfold intSign
  by_cases h : 0 ≤ s / n
  · have hs0 : 0 ≤ s := hiff.mp h
    simp [h, hs0]
  · have hs0 : ¬ 0 ≤ s := by
      intro hs0
      exact h (hiff.mpr hs0)
    simp [h, hs0]

theorem VTwice_kToW (n s k : ℤ) :
    VTwice n s (kToW (s / n) k) = WTwice n (s % n) k := by
  have hs := div_decomposition s n
  change 2 * s - 2 * n * (k + s / n - 1) - n - 1 =
    2 * (s % n) + n - 1 - 2 * n * k
  nth_rewrite 1 [← hs]
  ring

private theorem sRowRawKernel_eq_normal
    (n p e r s k : ℤ) (hn : 0 < n) (hp : 0 < p) :
    sRowRawKernel n p e r s k =
      sRowNormalKernel n p e r s (kToW (s / n) k) := by
  let ell := s / n
  let t := s % n
  have ht0 : 0 ≤ t := emod_nonneg_of_pos s n hn
  have htn : t < n := emod_lt_of_pos s n hn
  have hs : n * ell + t = s := by
    dsimp [ell, t]
    exact div_decomposition s n
  have hbranch := branchCoefficient_denominator_eq n p t k ell hn hp
  have hsign : intSign ell = intSign s := by
    dsimp [ell]
    exact intSign_ediv_eq s n hn
  have hV : VTwice n s (kToW ell k) = WTwice n t k := by
    dsimp [ell, t]
    exact VTwice_kToW n s k
  have hexp := sRowRawExponent_eq_shell n p r t ell k
  rw [hs] at hexp
  unfold sRowRawKernel sRowNormalKernel shellIndicator
  dsimp only
  rw [hbranch, hsign, hV, hexp]
  rfl

/-- General `s`-row coefficient formula from the Hahn branch expansion. -/
theorem sRowRawCoefficient_eq_normal
    (n p e r s : ℤ) (hn : 0 < n) (hp : 0 < p) :
    sRowRawCoefficient n p e r s = sRowNormalCoefficient n p e r s := by
  unfold sRowRawCoefficient sRowNormalCoefficient
  calc
    (∑ᶠ k : ℤ, sRowRawKernel n p e r s k) =
        ∑ᶠ k : ℤ, sRowNormalKernel n p e r s (kToW (s / n) k) := by
      apply finsum_congr
      intro k
      exact sRowRawKernel_eq_normal n p e r s k hn hp
    _ = ∑ᶠ w : ℤ, sRowNormalKernel n p e r s w :=
      finsum_comp_equiv (kToW (s / n))

/-! ## Symmetric `r`-split rows -/

/-- Raw q-exponent after the `r`-row monomial constraints have fixed `t,ell,v`. -/
def rRowRawExponent (n p s t ell k : ℤ) : ℤ :=
  let v := s + (n + p) * ell
  n * C2 t + n * C2 v + (n + p) * t * v + genN n p * C2 k +
    ell * (genN n p * (k - 1) + genA0 n p - t * genDelta n p)

theorem rRowRawExponent_eq_shell (n p s t ell k : ℤ) :
    rRowRawExponent n p s t ell k =
      shellExponent n p (n * ell + t) s (-k - ell) := by
  have h := row_exponent_identity s t ell k n p
  rw [heckeExp_comm] at h
  have hC : C2 (k + ell) = C2 (-k - ell + 1) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      C2_neg_eq_succ (-k - ell)
  rw [hC] at h
  simpa [rRowRawExponent, shellExponent, hC, add_assoc] using h

/-- One raw coefficient contribution from the cleared `r`-split Appell rows. -/
def rRowRawKernel (n p e r s k : ℤ) : ℚ :=
  let ell := r / n
  let t := r % n
  negOnePow (r + s) * branchCoefficient (denominatorExponentTwice n p t k) ell *
    (if e = rRowRawExponent n p s t ell k then 1 else 0)

/-- Raw coefficient of the sum of all cleared `r`-split Appell rows. -/
def rRowRawCoefficient (n p e r s : ℤ) : ℚ :=
  ∑ᶠ k : ℤ, rRowRawKernel n p e r s k

/-! ### Faithful symmetric residue-row bridge -/

/-- The q-exponent in the displayed cleared `r`-row before substituting the
forced theta index `v = s + (n+p)ℓ`. -/
def rRowResidueExponent (n p t v ell k : ℤ) : ℤ :=
  n * C2 t + n * C2 v + (n + p) * t * v + genN n p * C2 k +
    ell * (genN n p * (k - 1) + genA0 n p - t * genDelta n p)

/-- Coefficient contribution of residue row `t` in the displayed symmetric
cleared Appell sum. -/
def rRowResidueKernel (n p e r s t k : ℤ) : ℚ :=
  let ell := (r - t) / n
  let v := s + (n + p) * ell
  if 0 ≤ t ∧ t < n ∧ r = n * ell + t then
    negOnePow (t + v + n * ell - (n + p) * ell) *
      branchCoefficient (denominatorExponentTwice n p t k) ell *
        (if e = rRowResidueExponent n p t v ell k then 1 else 0)
  else 0

/-- Coefficient of the explicit finite residue sum of cleared `r`-rows. -/
def rRowResidueCoefficient (n p e r s : ℤ) : ℚ :=
  ∑ t ∈ Finset.Icc (0 : ℤ) (n - 1), ∑ᶠ k : ℤ, rRowResidueKernel n p e r s t k

private theorem rRowResidueKernel_emod
    (n p e r s k : ℤ) (hn : 0 < n) :
    rRowResidueKernel n p e r s (r % n) k =
      rRowRawKernel n p e r s k := by
  have ht0 := emod_nonneg_of_pos r n hn
  have htn := emod_lt_of_pos r n hn
  have hr := div_decomposition r n
  have hell := sub_emod_ediv r n hn
  unfold rRowResidueKernel rRowRawKernel rRowResidueExponent
  dsimp only
  rw [hell]
  simp only [ht0, htn, hr, and_self, if_true]
  have hsign :
      r % n + (s + (n + p) * (r / n)) + n * (r / n) -
          (n + p) * (r / n) = r + s := by
    nlinarith
  rw [hsign]
  rfl

/-- Monomial forcing collapses the explicit symmetric residue sum to the raw
coefficient kernel used in the general row proof. -/
theorem rRowResidueCoefficient_eq_raw
    (n p e r s : ℤ) (hn : 0 < n) :
    rRowResidueCoefficient n p e r s = rRowRawCoefficient n p e r s := by
  classical
  unfold rRowResidueCoefficient rRowRawCoefficient
  have hmem : r % n ∈ Finset.Icc (0 : ℤ) (n - 1) := by
    rw [Finset.mem_Icc]
    constructor
    · exact emod_nonneg_of_pos r n hn
    · have := emod_lt_of_pos r n hn
      omega
  rw [Finset.sum_eq_single_of_mem (r % n) hmem]
  · apply finsum_congr
    intro k
    exact rRowResidueKernel_emod n p e r s k hn
  · intro t ht htne
    apply finsum_eq_zero_of_forall_eq_zero
    intro k
    unfold rRowResidueKernel
    dsimp only
    rw [if_neg]
    intro hrow
    have hu := quotient_remainder_unique r n t ((r - t) / n)
      hn hrow.1 hrow.2.1 hrow.2.2
    exact htne hu.2

/-- Doubled `U_w = r + nw + (n-1)/2`, kept integral for every parity of `n`. -/
def UTwice (n r w : ℤ) : ℤ := 2 * r + 2 * n * w + n - 1

/-- The target normal form for one `r`-row shell contribution. -/
def rRowNormalKernel (n p e r s w : ℤ) : ℚ :=
  negOnePow (r + s) *
    (((intSign r - intSign (UTwice n r w) : ℤ) : ℚ) / 2) *
    shellIndicator n p e r s w

/-- Target coefficient normal form for all cleared `r`-split Appell rows. -/
def rRowNormalCoefficient (n p e r s : ℤ) : ℚ :=
  ∑ᶠ w : ℤ, rRowNormalKernel n p e r s w

private def kToWR (ell : ℤ) : ℤ ≃ ℤ where
  toFun k := -k - ell
  invFun w := -w - ell
  left_inv := by intro k; ring
  right_inv := by intro w; ring

theorem UTwice_kToWR (n r k : ℤ) :
    UTwice n r (kToWR (r / n) k) = WTwice n (r % n) k := by
  have hr := div_decomposition r n
  change 2 * r + 2 * n * (-k - r / n) + n - 1 =
    2 * (r % n) + n - 1 - 2 * n * k
  nth_rewrite 1 [← hr]
  ring

private theorem rRowRawKernel_eq_normal
    (n p e r s k : ℤ) (hn : 0 < n) (hp : 0 < p) :
    rRowRawKernel n p e r s k =
      rRowNormalKernel n p e r s (kToWR (r / n) k) := by
  let ell := r / n
  let t := r % n
  have hr : n * ell + t = r := by
    dsimp [ell, t]
    exact div_decomposition r n
  have hbranch := branchCoefficient_denominator_eq n p t k ell hn hp
  have hsign : intSign ell = intSign r := by
    dsimp [ell]
    exact intSign_ediv_eq r n hn
  have hU : UTwice n r (kToWR ell k) = WTwice n t k := by
    dsimp [ell, t]
    exact UTwice_kToWR n r k
  have hexp := rRowRawExponent_eq_shell n p s t ell k
  rw [hr] at hexp
  unfold rRowRawKernel rRowNormalKernel shellIndicator
  dsimp only
  rw [hbranch, hsign, hU, hexp]
  rfl

/-- General `r`-row coefficient formula from the Hahn branch expansion. -/
theorem rRowRawCoefficient_eq_normal
    (n p e r s : ℤ) (hn : 0 < n) (hp : 0 < p) :
    rRowRawCoefficient n p e r s = rRowNormalCoefficient n p e r s := by
  unfold rRowRawCoefficient rRowNormalCoefficient
  calc
    (∑ᶠ k : ℤ, rRowRawKernel n p e r s k) =
        ∑ᶠ k : ℤ, rRowNormalKernel n p e r s (kToWR (r / n) k) := by
      apply finsum_congr
      intro k
      exact rRowRawKernel_eq_normal n p e r s k hn hp
    _ = ∑ᶠ w : ℤ, rRowNormalKernel n p e r s w :=
      finsum_comp_equiv (kToWR (r / n))

/-! ## General coefficientwise assembly -/

/-- The two-variable same-sign coefficient in rational form. Doubled wall
coordinates may be supplied because doubling does not change their sign. -/
def sameSignCoefficient (a b : ℤ) : ℚ :=
  ((intSign a + intSign b : ℤ) : ℚ) / 2

/-- One coefficient contribution from `barJ * f_{n,n+p,n}`. -/
def heckeKernel (n p e r s w : ℤ) : ℚ :=
  negOnePow (r + s) * sameSignCoefficient r s * shellIndicator n p e r s w

/-- Coefficient of `barJ * f_{n,n+p,n}`. -/
def heckeCoefficient (n p e r s : ℤ) : ℚ :=
  ∑ᶠ w : ℤ, heckeKernel n p e r s w

/-- One coefficient contribution from the wall correction `barTheta_{n,p}`. -/
def thetaKernel (n p e r s w : ℤ) : ℚ :=
  negOnePow (r + s) * sameSignCoefficient (UTwice n r w) (VTwice n s w) *
    shellIndicator n p e r s w

/-- Coefficient function of the wall correction `barTheta_{n,p}`. -/
def thetaCoefficient (n p e r s : ℤ) : ℚ :=
  ∑ᶠ w : ℤ, thetaKernel n p e r s w

private theorem support_of_mul_shell_finite
    (n p e r s : ℤ) (c : ℤ → ℚ) (hn : 0 < n) (hp : 0 < p) :
    (Function.support (fun w => c w * shellIndicator n p e r s w)).Finite := by
  refine (shellIndicator_support_finite n p e r s hn hp).subset ?_
  intro w hw
  rw [Function.mem_support] at hw ⊢
  intro hshell
  exact hw (by simp [hshell])

private theorem sRowNormalKernel_support_finite
    (n p e r s : ℤ) (hn : 0 < n) (hp : 0 < p) :
    (Function.support (sRowNormalKernel n p e r s)).Finite := by
  refine (shellIndicator_support_finite n p e r s hn hp).subset ?_
  intro w hw
  rw [Function.mem_support] at hw ⊢
  intro hshell
  exact hw (by simp [sRowNormalKernel, hshell])

private theorem rRowNormalKernel_support_finite
    (n p e r s : ℤ) (hn : 0 < n) (hp : 0 < p) :
    (Function.support (rRowNormalKernel n p e r s)).Finite := by
  refine (shellIndicator_support_finite n p e r s hn hp).subset ?_
  intro w hw
  rw [Function.mem_support] at hw ⊢
  intro hshell
  exact hw (by simp [rRowNormalKernel, hshell])

private theorem thetaKernel_support_finite
    (n p e r s : ℤ) (hn : 0 < n) (hp : 0 < p) :
    (Function.support (thetaKernel n p e r s)).Finite := by
  refine (shellIndicator_support_finite n p e r s hn hp).subset ?_
  intro w hw
  rw [Function.mem_support] at hw ⊢
  intro hshell
  exact hw (by simp [thetaKernel, hshell])

private theorem coefficient_kernel_assembly (n p e r s w : ℤ) :
    heckeKernel n p e r s w =
      sRowNormalKernel n p e r s w + rRowNormalKernel n p e r s w +
        thetaKernel n p e r s w := by
  unfold heckeKernel sRowNormalKernel rRowNormalKernel thetaKernel
    sameSignCoefficient
  push_cast
  ring

/--
The general boundary-cleared Hecke--Appell identity, coefficient by coefficient.

The two raw Appell coefficients are those obtained after expanding the signed
Hahn geometric inverse and solving the `x,y` monomial constraints. The wall
correction is a coefficient function rather than a Hahn-series value because
it can contain arbitrarily placed negative q-powers.
-/
theorem general_boundary_cleared_coefficient
    (n p e r s : ℤ) (hn : 0 < n) (hp : 0 < p) :
    heckeCoefficient n p e r s =
      sRowRawCoefficient n p e r s + rRowRawCoefficient n p e r s +
        thetaCoefficient n p e r s := by
  rw [sRowRawCoefficient_eq_normal n p e r s hn hp,
    rRowRawCoefficient_eq_normal n p e r s hn hp]
  unfold heckeCoefficient sRowNormalCoefficient rRowNormalCoefficient thetaCoefficient
  have hs := sRowNormalKernel_support_finite n p e r s hn hp
  have hr := rRowNormalKernel_support_finite n p e r s hn hp
  have ht := thetaKernel_support_finite n p e r s hn hp
  rw [← finsum_add_distrib hs hr]
  have hsr :
      (Function.support (fun w =>
        sRowNormalKernel n p e r s w + rRowNormalKernel n p e r s w)).Finite := by
    refine (hs.union hr).subset ?_
    intro w hw
    rw [Function.mem_support] at hw
    simp only [Set.mem_union, Function.mem_support]
    by_cases hs0 : sRowNormalKernel n p e r s w = 0
    · right
      intro hr0
      exact hw (by simp [hs0, hr0])
    · left
      exact hs0
  rw [← finsum_add_distrib hsr ht]
  apply finsum_congr
  intro w
  exact coefficient_kernel_assembly n p e r s w

/--
The general boundary-cleared identity stated with the explicit finite residue
families appearing in the cleared Appell formula.  Unlike
`general_boundary_cleared_coefficient`, this statement does not expose the
post-forcing raw row kernels: the two monomial-forcing bridges are part of the
proof.
-/
theorem general_boundary_cleared_residue_coefficient
    (n p e r s : ℤ) (hn : 0 < n) (hp : 0 < p) :
    heckeCoefficient n p e r s =
      sRowResidueCoefficient n p e r s + rRowResidueCoefficient n p e r s +
        thetaCoefficient n p e r s := by
  rw [sRowResidueCoefficient_eq_raw n p e r s hn,
    rRowResidueCoefficient_eq_raw n p e r s hn]
  exact general_boundary_cleared_coefficient n p e r s hn hp

end

end QseriesFormalization.Pending.Ch10GeneralHahnCoeff

