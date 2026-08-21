import QseriesFormalization.Basic

/-!
# General Root-Pair Row-Coefficient Theorem

Formalization of the general row-coefficient theorem from
`paper/root-pair-involution/root_pair_note.tex` for all coprime (n, p).

The main identity:  barJ · f_{n,n+p,n} = barJ · g_{n,n+p,n} + barTheta_{n,p}
-/

namespace QseriesFormalization.Pending.Ch10RootPairGeneral

/-! ## 1. Binomial coefficient C2 = binom(k,2) -/

def C2Twice (k : ℤ) : ℤ := k * (k - 1)
def C2 (k : ℤ) : ℤ := k * (k - 1) / 2

private theorem two_dvd_mul_pred (k : ℤ) : (2 : ℤ) ∣ k * (k - 1) := by
  rcases Int.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact ⟨r * (r + r - 1), by subst hr; ring⟩
  · exact ⟨(2 * r + 1) * r, by subst hr; ring⟩

theorem two_mul_C2 (k : ℤ) : 2 * C2 k = C2Twice k := by
  simp only [C2, C2Twice]
  obtain ⟨c, hc⟩ := two_dvd_mul_pred k
  rw [hc]; omega

theorem C2_zero : C2 0 = 0 := by simp [C2]
theorem C2_one : C2 1 = 0 := by simp [C2]

theorem C2Twice_shift (k : ℤ) : C2Twice (k + 1) = C2Twice k + 2 * k := by
  simp only [C2Twice]; ring

/-! ## 2. General parameters -/

abbrev genB (n p : ℤ) : ℤ := n + p
def genDelta (n p : ℤ) : ℤ := p * (2 * n + p)
def genN (n p : ℤ) : ℤ := n * genDelta n p

theorem genN_eq (n p : ℤ) : genN n p = n * p * (2 * n + p) := by
  simp only [genN, genDelta]; ring

def genA0Twice (n p : ℤ) : ℤ := n * p * (2 * n + p + 1)
def genA0 (n p : ℤ) : ℤ := n * p * (2 * n + p + 1) / 2

private theorem two_dvd_genA0_num (n p : ℤ) : (2 : ℤ) ∣ n * p * (2 * n + p + 1) := by
  rcases Int.even_or_odd p with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact ⟨n * r * (2 * n + p + 1), by subst hr; ring⟩
  · exact ⟨n * p * (n + r + 1), by subst hr; ring⟩

theorem two_mul_genA0 (n p : ℤ) : 2 * genA0 n p = genA0Twice n p := by
  simp only [genA0, genA0Twice]
  obtain ⟨c, hc⟩ := two_dvd_genA0_num n p
  rw [hc]; omega

def heckeExpTwice (n p r s : ℤ) : ℤ :=
  n * C2Twice r + 2 * (n + p) * r * s + n * C2Twice s

def heckeExp (n p r s : ℤ) : ℤ :=
  n * C2 r + (n + p) * r * s + n * C2 s

theorem two_mul_heckeExp (n p r s : ℤ) :
    2 * heckeExp n p r s = heckeExpTwice n p r s := by
  simp only [heckeExp, heckeExpTwice]
  linear_combination n * two_mul_C2 r + n * two_mul_C2 s

/-! ## 3. Wall parameter pL -/

def pL (a b n p : ℤ) : ℤ := 4 * a * n - 2 * a * p - 4 * a + 4 * b + 2 * n - p

theorem pL_add_p_even (a b n p : ℤ) :
    ∃ k : ℤ, pL a b n p + p = 2 * k :=
  ⟨2 * a * n - a * p - 2 * a + 2 * b + n, by simp only [pL]; ring⟩

def pLHalf (a b n p : ℤ) : ℤ := 2 * a * n - a * p - 2 * a + 2 * b + n

theorem pL_add_p_eq_two_mul_pLHalf (a b n p : ℤ) :
    pL a b n p + p = 2 * pLHalf a b n p := by
  simp only [pL, pLHalf]; ring

/-! ## 4. Row exponent identity (Proposition 2.6) — algebraic heart -/

theorem row_exponent_identity_twice (r t ell k n p : ℤ) :
    n * C2Twice t + n * C2Twice (r + (n + p) * ell) +
      2 * (n + p) * t * (r + (n + p) * ell) +
      genN n p * C2Twice k +
      ell * (2 * genN n p * (k - 1) + genA0Twice n p - 2 * t * genDelta n p) =
    heckeExpTwice n p r (n * ell + t) + genN n p * C2Twice (k + ell) := by
  simp only [C2Twice, genN, genDelta, genA0Twice, heckeExpTwice]
  ring

theorem row_exponent_identity (r t ell k n p : ℤ) :
    n * C2 t + n * C2 (r + (n + p) * ell) +
      (n + p) * t * (r + (n + p) * ell) +
      genN n p * C2 k +
      ell * (genN n p * (k - 1) + genA0 n p - t * genDelta n p) =
    heckeExp n p r (n * ell + t) + genN n p * C2 (k + ell) := by
  have h2 : ∀ (a b : ℤ), 2 * a = 2 * b → a = b := fun _ _ h => by linarith
  apply h2
  linear_combination
    row_exponent_identity_twice r t ell k n p
    + n * two_mul_C2 t
    + n * two_mul_C2 (r + (n + p) * ell)
    + genN n p * two_mul_C2 k
    - two_mul_heckeExp n p r (n * ell + t)
    - genN n p * two_mul_C2 (k + ell)
    + ell * two_mul_genA0 n p

/-! ## 5. Symmetric row exponent identity (r ↔ s version) -/

theorem heckeExpTwice_comm (n p r s : ℤ) :
    heckeExpTwice n p r s = heckeExpTwice n p s r := by
  simp only [heckeExpTwice, C2Twice]; ring

theorem heckeExp_comm (n p r s : ℤ) :
    heckeExp n p r s = heckeExp n p s r := by
  have h := heckeExpTwice_comm n p r s
  have h1 := two_mul_heckeExp n p r s
  have h2 := two_mul_heckeExp n p s r
  linarith

theorem row_exponent_identity_r_twice (s t ell k n p : ℤ) :
    n * C2Twice t + n * C2Twice (s + (n + p) * ell) +
      2 * (n + p) * t * (s + (n + p) * ell) +
      genN n p * C2Twice k +
      ell * (2 * genN n p * (k - 1) + genA0Twice n p - 2 * t * genDelta n p) =
    heckeExpTwice n p (n * ell + t) s + genN n p * C2Twice (k + ell) := by
  rw [heckeExpTwice_comm]
  exact row_exponent_identity_twice s t ell k n p

/-! ## 6. Branch sign lemma (Lemma 2.4) -/

def gammaTwice (n p t k : ℤ) : ℤ :=
  2 * genN n p * (k - 1) + genA0Twice n p - 2 * t * genDelta n p

theorem gammaTwice_eq_delta_A (n p t k : ℤ) :
    gammaTwice n p t k = genDelta n p * (2 * (n * k - t) - n) + n * p := by
  simp only [gammaTwice, genN, genDelta, genA0Twice]; ring

def WTwice (n t k : ℤ) : ℤ := 2 * t + n - 1 - 2 * n * k

theorem WTwice_eq_sub_2A (n t k : ℤ) :
    WTwice n t k = n - 1 - 2 * (n * k - t) := by
  simp only [WTwice]; ring

theorem gammaTwice_neg_of_WTwice_nonneg (n p t k : ℤ)
    (hn : 0 < n) (hp : 0 < p)
    (hW : 0 ≤ WTwice n t k) :
    gammaTwice n p t k < 0 := by
  rw [gammaTwice_eq_delta_A]
  rw [WTwice_eq_sub_2A] at hW
  have hA : 2 * (n * k - t) ≤ n - 1 := by linarith
  have hShift : 2 * (n * k - t) - n ≤ -1 := by linarith
  have hDelta_pos : 0 < genDelta n p := by
    simp only [genDelta]; nlinarith
  have hProd : genDelta n p * (2 * (n * k - t) - n) ≤ -genDelta n p := by
    nlinarith
  have hCancel : -genDelta n p + n * p = -p * (n + p) := by
    simp only [genDelta]; ring
  nlinarith

theorem gammaTwice_pos_of_WTwice_neg (n p t k : ℤ)
    (hn : 0 < n) (hp : 0 < p)
    (hW : WTwice n t k < 0) :
    0 < gammaTwice n p t k := by
  rw [gammaTwice_eq_delta_A]
  rw [WTwice_eq_sub_2A] at hW
  have hA : 0 ≤ 2 * (n * k - t) - n := by omega
  have hDelta_pos : 0 < genDelta n p := by
    simp only [genDelta]; nlinarith
  have hNP : 0 < n * p := mul_pos hn hp
  nlinarith [mul_nonneg (le_of_lt hDelta_pos) hA]

theorem gammaTwice_ne_zero (n p t k : ℤ)
    (hn : 0 < n) (hp : 0 < p) :
    gammaTwice n p t k ≠ 0 := by
  by_cases hW : 0 ≤ WTwice n t k
  · exact ne_of_lt (gammaTwice_neg_of_WTwice_nonneg n p t k hn hp hW)
  · exact ne_of_gt (gammaTwice_pos_of_WTwice_neg n p t k hn hp (by linarith))

theorem gammaTwice_pos_iff_WTwice_neg (n p t k : ℤ)
    (hn : 0 < n) (hp : 0 < p) :
    0 < gammaTwice n p t k ↔ WTwice n t k < 0 := by
  constructor
  · intro hg
    by_contra hW
    push Not at hW
    linarith [gammaTwice_neg_of_WTwice_nonneg n p t k hn hp hW]
  · exact gammaTwice_pos_of_WTwice_neg n p t k hn hp

theorem gammaTwice_neg_iff_WTwice_nonneg (n p t k : ℤ)
    (hn : 0 < n) (hp : 0 < p) :
    gammaTwice n p t k < 0 ↔ 0 ≤ WTwice n t k := by
  constructor
  · intro hg
    by_contra hW
    push Not at hW
    linarith [gammaTwice_pos_of_WTwice_neg n p t k hn hp hW]
  · exact gammaTwice_neg_of_WTwice_nonneg n p t k hn hp

/-! ## 7. Sign of ℓ equals sign of s -/

theorem ell_nonneg_iff_s_nonneg (n t ell : ℤ)
    (hn : 0 < n) (ht0 : 0 ≤ t) (htn : t < n) :
    0 ≤ ell ↔ 0 ≤ n * ell + t := by
  constructor
  · intro h; nlinarith
  · intro h
    by_contra hc
    push Not at hc
    have : ell ≤ -1 := by omega
    nlinarith

theorem ell_neg_iff_s_neg (n t ell : ℤ)
    (hn : 0 < n) (ht0 : 0 ≤ t) (htn : t < n) :
    ell < 0 ↔ n * ell + t < 0 := by
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-! ## 8. Ψ preservation under wall involution -/

theorem psi_preserved (C L P Q : ℤ) :
    let Q' := C * P + L - Q
    P ^ 2 + Q' ^ 2 - C * P * Q' - L * (P + Q') =
      P ^ 2 + Q ^ 2 - C * P * Q - L * (P + Q) := by
  ring

theorem wall_involution_involutive (C L P Q : ℤ) :
    C * P + L - (C * P + L - Q) = Q := by ring

/-! ## 9. C2 arithmetic lemmas -/

theorem C2Twice_neg_eq_succ (w : ℤ) : C2Twice (-w) = C2Twice (w + 1) := by
  simp only [C2Twice]; ring

theorem C2_neg_eq_succ (w : ℤ) : C2 (-w) = C2 (w + 1) := by
  have h := C2Twice_neg_eq_succ w
  have h1 := two_mul_C2 (-w)
  have h2 := two_mul_C2 (w + 1)
  linarith

theorem C2Twice_add (k ell : ℤ) :
    C2Twice (k + ell) = C2Twice k + C2Twice ell + 2 * k * ell := by
  simp only [C2Twice]; ring

/-! ## 10. Kronecker partial fraction — placeholder -/

-- Kronecker partial fraction (Lemma A.1 in the paper) is not formalized here;
-- it is a classical identity proved by residue/principal-part analysis.

end QseriesFormalization.Pending.Ch10RootPairGeneral
