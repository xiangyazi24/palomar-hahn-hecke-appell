/-
# Chapter 10, two-variable Hahn-series infrastructure (source route for Chan Eq 10.15)

This file builds the q-first lexicographic Hahn-series kernel used by the SOURCE-route
proof of Chan's Eq 10.15 (design: `docs/chatgpt-designs-2026-06-04/chan3-Ch10-twovar-source-route.md`).

Layers implemented here:

* **A** — the q-first lexicographic Hahn kernel: `ExpXY`, `ExpQXY`, `K`, `S`, `expQXY`,
  `monom`, `coeffQXY`, `coeffXY` (the q-slice, with its support proved PWO via the order
  embedding `a ↦ expQXY a i j`), `CTxy`, and `embedQ : K →+* S` together with
  `CTxy_embedQ_mul`.  Plus `monom_mul`, `monom_ne_zero`, and the extensionality lemmas.

* **B** — integer quadratic helpers: `Tn`, `Tplus`, `P10`, parity lemmas, `T_add_three`,
  and the closed-form recurrence lemma `coeff_recurrence_closed_form`.

* **C** — `thetaMon` as the `hsum` of a `HahnSeries.SummableFamily` indexed by `ℤ`
  (with the summability obligations discharged from `0 < A`), its coefficient formula,
  the functional equation (10.33), and the symmetry specials.

Internal convention: `q = Q^3`, so the nome exponent `A` is `3` for `q` and `6` for `q²`.
-/
import Mathlib
import QseriesFormalization.Chapter19
import QseriesFormalization.Chapter19_JacobiTripleSignChar
import QseriesFormalization.Pending.JacobiCubeAnalyticToFormal
import QseriesFormalization.Pending.JTP_FormalPS_Pentagonal
import QseriesFormalization.Pending.Chapter10_HM

open scoped Classical
open Set

namespace QseriesFormalization
namespace Ch10TwoVar

/-! ## Layer A — the q-first lexicographic Hahn kernel -/

/-- `(x-degree, y-degree)`, lexicographic. -/
abbrev ExpXY  := Lex (ℤ × ℤ)
/-- `(Q-degree, x-degree, y-degree)`, lexicographic, q-first. -/
abbrev ExpQXY := Lex (ℤ × ExpXY)
/-- `ℚ((Q))`: the coefficient field of Q-Laurent-Hahn series. -/
abbrev K := HahnSeries ℤ ℚ
/-- The q-adic x/y Laurent–Hahn ring. -/
abbrev S := HahnSeries ExpQXY ℚ

/-- The exponent `Q^a x^i y^j` as an element of the index monoid. -/
noncomputable def expQXY (a i j : ℤ) : ExpQXY := toLex (a, toLex (i, j))

/-- The monomial `c · Q^a x^i y^j`. -/
noncomputable def monom (a i j : ℤ) (c : ℚ) : S := HahnSeries.single (expQXY a i j) c

/-- Local replacement for `HahnSeries.coeff_single_mul` on `S = HahnSeries ExpQXY ℚ`.
Mathlib v4.30's `coeff_single_mul` requires `IsOrderedAddMonoid Γ'`, which suffers from a
typeclass diamond for `ExpQXY = Lex (ℤ × Lex (ℤ × ℤ))`.  We bypass it via
`coeff_single_mul_add`, which resolves through `IsOrderedCancelAddMonoid` instead. -/
theorem HahnSeries.coeff_single_mul_S {c : ℚ} {F : S} {g e : ExpQXY} :
    (HahnSeries.single e c * F).coeff g = c * F.coeff (g - e) := by
  have := HahnSeries.coeff_single_mul_add (Γ := ExpQXY) (R := ℚ)
    (r := c) (x := F) (a := g - e) (b := e)
  simp [sub_add_cancel] at this
  exact this

/-- The exponent map is additive. -/
@[simp] theorem expQXY_add (a i j a' i' j' : ℤ) :
    expQXY a i j + expQXY a' i' j' = expQXY (a + a') (i + i') (j + j') := rfl

@[simp] theorem expQXY_zero : expQXY 0 0 0 = (0 : ExpQXY) := rfl

/-- The exponent map is injective in all three slots. -/
theorem expQXY_inj {a i j a' i' j' : ℤ} (h : expQXY a i j = expQXY a' i' j') :
    a = a' ∧ i = i' ∧ j = j' := by
  unfold expQXY at h
  simp only [Prod.ext_iff, EmbeddingLike.apply_eq_iff_eq] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

@[simp] theorem expQXY_eq_iff {a i j a' i' j' : ℤ} :
    expQXY a i j = expQXY a' i' j' ↔ a = a' ∧ i = i' ∧ j = j' :=
  ⟨expQXY_inj, by rintro ⟨rfl, rfl, rfl⟩; rfl⟩

/-- Strict monotonicity of the Q-degree slot at fixed `(i,j)`. -/
theorem expQXY_strictMono (i j : ℤ) : StrictMono (fun a => expQXY a i j) := by
  intro a b h
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

/-- Product of monomials. -/
theorem monom_mul (a i j : ℤ) (c d : ℚ) (a' i' j' : ℤ) :
    monom a i j c * monom a' i' j' d = monom (a + a') (i + i') (j + j') (c * d) := by
  unfold monom
  rw [HahnSeries.single_mul_single, expQXY_add]

/-- A monomial with nonzero coefficient is nonzero. -/
theorem monom_ne_zero {a i j : ℤ} {c : ℚ} (h : c ≠ 0) : monom a i j c ≠ 0 :=
  HahnSeries.single_ne_zero h

@[simp] theorem monom_zero (a i j : ℤ) : monom a i j 0 = 0 := HahnSeries.single_eq_zero

/-- Congruence for `monom` in all four arguments. -/
theorem monom_eq_monom {a i j : ℤ} {c : ℚ} {a' i' j' : ℤ} {c' : ℚ}
    (ha : a = a') (hi : i = i') (hj : j = j') (hc : c = c') :
    monom a i j c = monom a' i' j' c' := by
  rw [ha, hi, hj, hc]

/-- The `Q^a x^i y^j` coefficient of `F`. -/
noncomputable def coeffQXY (F : S) (a i j : ℤ) : ℚ := F.coeff (expQXY a i j)

@[simp] theorem coeffQXY_monom (a i j : ℤ) (c : ℚ) (a' i' j' : ℤ) :
    coeffQXY (monom a i j c) a' i' j' =
      if (a' = a ∧ i' = i ∧ j' = j) then c else 0 := by
  unfold coeffQXY monom
  rw [HahnSeries.coeff_single]
  simp only [expQXY_eq_iff]

/-- Two Hahn series in `S` are equal iff all `coeffQXY` agree. -/
theorem ext_coeffQXY {F G : S} (h : ∀ a i j, coeffQXY F a i j = coeffQXY G a i j) : F = G := by
  apply HahnSeries.ext
  funext g
  obtain ⟨a, m⟩ := g
  obtain ⟨i, j⟩ := m
  exact h a i j

/-! ### The q-slice `coeffXY` -/

/-- The support of the q-slice `a ↦ coeffQXY F a i j` is partially well-ordered in `ℤ`. -/
theorem slice_isPWO (F : S) (i j : ℤ) :
    {a : ℤ | F.coeff (expQXY a i j) ≠ 0}.IsPWO := by
  rw [Set.isPWO_iff_exists_monotone_subseq]
  intro f hf
  have hFpwo := F.isPWO_support
  rw [Set.isPWO_iff_exists_monotone_subseq] at hFpwo
  have hf' : ∀ n, (fun a => expQXY (f a) i j) n ∈ F.support := by
    intro n
    have := hf n
    simpa [HahnSeries.mem_support] using this
  obtain ⟨g, hg⟩ := hFpwo (fun n => expQXY (f n) i j) hf'
  refine ⟨g, ?_⟩
  intro a b hab
  have hle := hg hab
  by_contra hcon
  push_neg at hcon
  exact absurd hle (not_le.mpr (expQXY_strictMono i j hcon))

/-- The q-slice of `F` at `x^i y^j`, as an element of `K = ℚ((Q))`. -/
noncomputable def coeffXY (F : S) (i j : ℤ) : K where
  coeff := fun a => coeffQXY F a i j
  isPWO_support' := by
    refine (slice_isPWO F i j).mono ?_
    intro a ha
    exact ha

@[simp] theorem coeffXY_coeff (F : S) (i j a : ℤ) :
    (coeffXY F i j).coeff a = coeffQXY F a i j := rfl

/-- The constant-in-`x,y` term of `F`, as an element of `K`. -/
noncomputable def CTxy (F : S) : K := coeffXY F 0 0

@[simp] theorem CTxy_coeff (F : S) (a : ℤ) : (CTxy F).coeff a = coeffQXY F a 0 0 := rfl

/-! ### The Q-embedding `embedQ : K →+* S` -/

/-- The additive monoid embedding `ℤ ↪ ExpQXY`, `a ↦ Q^a` (i.e. `expQXY a 0 0`). -/
noncomputable def expQHom : ℤ →+ ExpQXY where
  toFun := fun a => expQXY a 0 0
  map_zero' := expQXY_zero
  map_add' := by intro a b; rw [expQXY_add]; norm_num

theorem expQHom_apply (a : ℤ) : expQHom a = expQXY a 0 0 := rfl

theorem expQHom_injective : Function.Injective expQHom := by
  intro a b h
  rw [expQHom_apply, expQHom_apply, expQXY_eq_iff] at h
  exact h.1

theorem expQHom_le_iff (a b : ℤ) : expQHom a ≤ expQHom b ↔ a ≤ b := by
  rw [expQHom_apply, expQHom_apply]
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    exact absurd h (not_le.mpr (expQXY_strictMono 0 0 hcon))
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · exact le_of_lt (expQXY_strictMono 0 0 h)
    · rw [h]

/-- The ring homomorphism `K →+* S` that includes `ℚ((Q))` as the `x^0 y^0` part. -/
noncomputable def embedQ : K →+* S :=
  HahnSeries.embDomainRingHom expQHom expQHom_injective expQHom_le_iff

theorem embedQ_coeff (f : K) (a : ℤ) :
    (embedQ f).coeff (expQXY a 0 0) = f.coeff a := by
  unfold embedQ
  simp only [HahnSeries.embDomainRingHom]
  show (HahnSeries.embDomain
    ⟨⟨expQHom, expQHom_injective⟩, fun {a b} => expQHom_le_iff a b⟩ f).coeff (expQXY a 0 0) = _
  rw [show expQXY a 0 0 = (⟨⟨expQHom, expQHom_injective⟩,
      fun {a b} => expQHom_le_iff a b⟩ : ℤ ↪o ExpQXY) a from rfl]
  rw [HahnSeries.embDomain_coeff]

/-- `embedQ f` is supported on the `x^0 y^0` fiber only. -/
theorem embedQ_coeff_of_ne (f : K) (a i j : ℤ) (h : ¬ (i = 0 ∧ j = 0)) :
    (embedQ f).coeff (expQXY a i j) = 0 := by
  unfold embedQ
  simp only [HahnSeries.embDomainRingHom]
  show (HahnSeries.embDomain
    ⟨⟨expQHom, expQHom_injective⟩, fun {a b} => expQHom_le_iff a b⟩ f).coeff (expQXY a i j) = _
  rw [HahnSeries.embDomain_notin_range]
  rintro ⟨b, hb⟩
  rw [show (⟨⟨expQHom, expQHom_injective⟩,
      fun {a b} => expQHom_le_iff a b⟩ : ℤ ↪o ExpQXY) b = expQXY b 0 0 from rfl] at hb
  rw [expQXY_eq_iff] at hb
  exact h ⟨hb.2.1.symm, hb.2.2.symm⟩

@[simp] theorem coeffQXY_embedQ (f : K) (a : ℤ) :
    coeffQXY (embedQ f) a 0 0 = f.coeff a := by
  unfold coeffQXY
  exact embedQ_coeff f a

/-- `embedQ` of `single` is a `monom` in the `x^0 y^0` plane. -/
theorem embedQ_single (a : ℤ) (c : ℚ) :
    embedQ (HahnSeries.single a c) = monom a 0 0 c := by
  apply ext_coeffQXY
  intro a' i' j'
  unfold coeffQXY monom
  rw [HahnSeries.coeff_single]
  by_cases hij : i' = 0 ∧ j' = 0
  · obtain ⟨rfl, rfl⟩ := hij
    rw [embedQ_coeff, HahnSeries.coeff_single]
    simp only [expQXY_eq_iff, and_true]
    by_cases h : a' = a <;> simp [h]
  · rw [embedQ_coeff_of_ne (HahnSeries.single a c) a' i' j' hij]
    rw [if_neg]
    rintro h
    rw [expQXY_eq_iff] at h
    exact hij ⟨h.2.1, h.2.2⟩

/-- The support of `embedQ f` lies in the `x^0 y^0` plane. -/
theorem embedQ_support_subset (f : K) :
    (embedQ f).support ⊆ Set.range (fun b : ℤ => expQXY b 0 0) := by
  intro g hg
  obtain ⟨a, m⟩ := g
  obtain ⟨i, j⟩ := m
  by_cases hij : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := hij; exact ⟨a, rfl⟩
  · exact absurd (HahnSeries.mem_support _ _ |>.mp hg) (by
      simp only [not_not]; exact embedQ_coeff_of_ne f a i j hij)

/-- **Key multiplicativity of `CTxy` against `embedQ`** (constant-coefficient extraction).
The constant-in-`x,y` term of `embedQ f * F` is `f · CTxy F` in `K`. -/
theorem CTxy_embedQ_mul (f : K) (F : S) :
    CTxy (embedQ f * F) = f * CTxy F := by
  apply HahnSeries.ext
  funext a
  rw [CTxy_coeff, coeffQXY, HahnSeries.coeff_mul, HahnSeries.coeff_mul]
  -- Bijection between the ExpQXY-antidiagonal at (expQXY a 0 0) and the ℤ-antidiagonal at a,
  -- via b ↦ expQXY b 0 0 (both factors forced into the x^0 y^0 plane).
  apply Finset.sum_bij'
    (i := fun p _ => ((ofLex p.1).1, (ofLex p.2).1))
    (j := fun q _ => (expQXY q.1 0 0, expQXY q.2 0 0))
  · -- i maps into the ℤ-antidiagonal
    rintro ⟨g1, g2⟩ hp
    rw [Finset.mem_addAntidiagonal] at hp ⊢
    obtain ⟨hg1, hg2, hsum⟩ := hp
    obtain ⟨b, rfl⟩ := embedQ_support_subset f hg1
    refine ⟨?_, ?_, ?_⟩
    · rw [HahnSeries.mem_support, embedQ_coeff] at hg1
      simpa using hg1
    · -- (ofLex g2).1 ∈ (CTxy F).support
      have hg2eq : g2 = expQXY ((ofLex g2).1) 0 0 := by
        have : g2 = expQXY b 0 0 + g2 - expQXY b 0 0 := by abel
        -- from hsum: expQXY b 0 0 + g2 = expQXY a 0 0
        rw [show g2 = expQXY a 0 0 - expQXY b 0 0 by rw [← hsum]; abel]
        rw [show expQXY a 0 0 - expQXY b 0 0 = expQXY (a - b) 0 0 by
          rw [sub_eq_add_neg, sub_eq_add_neg]
          rw [show -expQXY b 0 0 = expQXY (-b) 0 0 by
            rw [← expQHom_apply, ← expQHom_apply, ← map_neg]]
          rw [expQXY_add]; norm_num]
        rfl
      rw [HahnSeries.mem_support, CTxy_coeff, coeffQXY]
      rw [HahnSeries.mem_support] at hg2
      rw [hg2eq] at hg2
      simpa using hg2
    · -- Q-degrees add to a
      have : (ofLex (expQXY b 0 0)).1 + (ofLex g2).1 = (ofLex (expQXY a 0 0 : ExpQXY)).1 := by
        rw [← hsum]; rfl
      simpa [expQXY] using this
  · -- j maps into the ExpQXY-antidiagonal
    rintro ⟨b, b'⟩ hq
    rw [Finset.mem_addAntidiagonal] at hq ⊢
    obtain ⟨hb, hb', hsum⟩ := hq
    refine ⟨?_, ?_, ?_⟩
    · rw [HahnSeries.mem_support, embedQ_coeff]
      rw [HahnSeries.mem_support] at hb; simpa using hb
    · rw [HahnSeries.mem_support]
      rw [HahnSeries.mem_support, CTxy_coeff, coeffQXY] at hb'
      simpa using hb'
    · rw [expQXY_add, hsum]; norm_num
  · -- left inverse
    rintro ⟨g1, g2⟩ hp
    rw [Finset.mem_addAntidiagonal] at hp
    obtain ⟨hg1, hg2, hsum⟩ := hp
    obtain ⟨b, rfl⟩ := embedQ_support_subset f hg1
    have hg2eq : g2 = expQXY ((ofLex g2).1) 0 0 := by
      rw [show g2 = expQXY a 0 0 - expQXY b 0 0 by rw [← hsum]; abel]
      rw [show expQXY a 0 0 - expQXY b 0 0 = expQXY (a - b) 0 0 by
        rw [sub_eq_add_neg, sub_eq_add_neg,
          show -expQXY b 0 0 = expQXY (-b) 0 0 by rw [← expQHom_apply, ← expQHom_apply, ← map_neg]]
        rw [expQXY_add]; norm_num]
      rfl
    simp only [Prod.mk.injEq]
    exact ⟨rfl, hg2eq.symm⟩
  · -- right inverse
    rintro ⟨b, b'⟩ _
    simp [expQXY]
  · -- the summands agree
    rintro ⟨g1, g2⟩ hp
    rw [Finset.mem_addAntidiagonal] at hp
    obtain ⟨hg1, hg2, hsum⟩ := hp
    obtain ⟨b, rfl⟩ := embedQ_support_subset f hg1
    have hg2eq : g2 = expQXY ((ofLex g2).1) 0 0 := by
      rw [show g2 = expQXY a 0 0 - expQXY b 0 0 by rw [← hsum]; abel]
      rw [show expQXY a 0 0 - expQXY b 0 0 = expQXY (a - b) 0 0 by
        rw [sub_eq_add_neg, sub_eq_add_neg,
          show -expQXY b 0 0 = expQXY (-b) 0 0 by rw [← expQHom_apply, ← expQHom_apply, ← map_neg]]
        rw [expQXY_add]; norm_num]
      rfl
    rw [embedQ_coeff, CTxy_coeff, coeffQXY]
    have hbeq : (ofLex (expQXY b 0 0)).1 = b := rfl
    rw [hbeq]
    conv_lhs => rw [hg2eq]

/-- **Generalized slicing lemma.**  Multiplying by `embedQ f` (which lives in the
`x⁰y⁰` plane) acts as the `K`-scalar `f` on every x/y-slice:
`coeffXY (embedQ f * F) i j = f · coeffXY F i j`.
(The `i = j = 0` case is `CTxy_embedQ_mul`.) -/
theorem coeffXY_embedQ_mul (f : K) (F : S) (i j : ℤ) :
    coeffXY (embedQ f * F) i j = f * coeffXY F i j := by
  apply HahnSeries.ext
  funext a
  rw [coeffXY_coeff, coeffQXY, HahnSeries.coeff_mul, HahnSeries.coeff_mul]
  apply Finset.sum_bij'
    (i := fun p _ => ((ofLex p.1).1, (ofLex p.2).1))
    (j := fun q _ => (expQXY q.1 0 0, expQXY q.2 i j))
  · rintro ⟨g1, g2⟩ hp
    rw [Finset.mem_addAntidiagonal] at hp ⊢
    obtain ⟨hg1, hg2, hsum⟩ := hp
    obtain ⟨b, rfl⟩ := embedQ_support_subset f hg1
    have hg2eq : g2 = expQXY (a - b) i j := by
      rw [show g2 = expQXY a i j - expQXY b 0 0 by rw [← hsum]; abel]
      rw [show expQXY a i j - expQXY b 0 0 = expQXY (a - b) i j by
        rw [sub_eq_add_neg, sub_eq_add_neg,
          show -expQXY b 0 0 = expQXY (-b) 0 0 by rw [← expQHom_apply, ← expQHom_apply, ← map_neg]]
        rw [expQXY_add]; norm_num]
    refine ⟨?_, ?_, ?_⟩
    · rw [HahnSeries.mem_support, embedQ_coeff] at hg1
      simpa using hg1
    · subst hg2eq
      rw [HahnSeries.mem_support, coeffXY_coeff, coeffQXY]
      rw [HahnSeries.mem_support] at hg2
      show F.coeff (expQXY (a - b) i j) ≠ 0
      simpa using hg2
    · have : (ofLex (expQXY b 0 0)).1 + (ofLex g2).1 = (ofLex (expQXY a i j : ExpQXY)).1 := by
        rw [← hsum]; rfl
      simpa [expQXY] using this
  · rintro ⟨b, b'⟩ hq
    rw [Finset.mem_addAntidiagonal] at hq ⊢
    obtain ⟨hb, hb', hsum⟩ := hq
    refine ⟨?_, ?_, ?_⟩
    · rw [HahnSeries.mem_support, embedQ_coeff]
      rw [HahnSeries.mem_support] at hb; simpa using hb
    · rw [HahnSeries.mem_support]
      rw [HahnSeries.mem_support, coeffXY_coeff, coeffQXY] at hb'
      simpa using hb'
    · rw [expQXY_add, hsum]; norm_num
  · rintro ⟨g1, g2⟩ hp
    rw [Finset.mem_addAntidiagonal] at hp
    obtain ⟨hg1, hg2, hsum⟩ := hp
    obtain ⟨b, rfl⟩ := embedQ_support_subset f hg1
    have hg2eq : g2 = expQXY (a - b) i j := by
      rw [show g2 = expQXY a i j - expQXY b 0 0 by rw [← hsum]; abel]
      rw [show expQXY a i j - expQXY b 0 0 = expQXY (a - b) i j by
        rw [sub_eq_add_neg, sub_eq_add_neg,
          show -expQXY b 0 0 = expQXY (-b) 0 0 by rw [← expQHom_apply, ← expQHom_apply, ← map_neg]]
        rw [expQXY_add]; norm_num]
    simp only [Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    conv_rhs => rw [hg2eq]
    rw [hg2eq]; rfl
  · rintro ⟨b, b'⟩ _
    simp [expQXY]
  · rintro ⟨g1, g2⟩ hp
    rw [Finset.mem_addAntidiagonal] at hp
    obtain ⟨hg1, hg2, hsum⟩ := hp
    obtain ⟨b, rfl⟩ := embedQ_support_subset f hg1
    have hg2eq : g2 = expQXY (a - b) i j := by
      rw [show g2 = expQXY a i j - expQXY b 0 0 by rw [← hsum]; abel]
      rw [show expQXY a i j - expQXY b 0 0 = expQXY (a - b) i j by
        rw [sub_eq_add_neg, sub_eq_add_neg,
          show -expQXY b 0 0 = expQXY (-b) 0 0 by rw [← expQHom_apply, ← expQHom_apply, ← map_neg]]
        rw [expQXY_add]; norm_num]
    subst hg2eq
    rw [embedQ_coeff, coeffXY_coeff, coeffQXY]
    rfl

/-- **Monomial-times-slice lemma.**  `coeffXY (monom a i 0 c * F) l 0` equals the `K`-series
`single a c · coeffXY F (l - i) 0`:  the monomial shifts the x-slice by `i` and the Q-degree by `a`. -/
theorem coeffXY_monom_mul (a i : ℤ) (c : ℚ) (F : S) (l : ℤ) :
    coeffXY (monom a i 0 c * F) l 0 = HahnSeries.single a c * coeffXY F (l - i) 0 := by
  have hneg : -expQXY a i 0 = expQXY (-a) (-i) 0 := by
    rw [neg_eq_iff_add_eq_zero, expQXY_add]
    rw [show a + -a = 0 by ring, show i + -i = 0 by ring, show (0 : ℤ) + 0 = 0 by ring]
    exact expQXY_zero
  apply HahnSeries.ext
  funext b
  rw [coeffXY_coeff, coeffQXY]
  rw [HahnSeries.coeff_single_mul, coeffXY_coeff, coeffQXY]
  -- LHS: (monom a i 0 c * F).coeff (expQXY b l 0); RHS: c * F.coeff (expQXY (b-a) (l-i) 0)
  show (HahnSeries.single (expQXY a i 0) c * F).coeff (expQXY b l 0)
      = c * F.coeff (expQXY (b - a) (l - i) 0)
  rw [HahnSeries.coeff_single_mul_S]
  rw [show expQXY b l 0 - expQXY a i 0 = expQXY (b - a) (l - i) 0 by
    rw [sub_eq_add_neg, sub_eq_add_neg, hneg, expQXY_add,
      show b + -a = b - a by ring, show l + -i = l - i by ring, show (0 : ℤ) + 0 = 0 by ring]]

/-! ## Layer B — integer quadratic helpers -/

/-- `T n = n(n-1)/2`. -/
def Tn (n : ℤ) : ℤ := n * (n - 1) / 2
/-- `T⁺ n = n(n+1)/2`. -/
def Tplus (n : ℤ) : ℤ := n * (n + 1) / 2
/-- `P₁₀ n = n(5n+3)/2`. -/
def P10 (n : ℤ) : ℤ := n * (5 * n + 3) / 2

/-- `n(n-1)` is even. -/
theorem even_n_mul_pred (n : ℤ) : (2 : ℤ) ∣ n * (n - 1) := by
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨k * (n - 1), by rw [hk]; ring⟩
  · exact ⟨n * k, by rw [hk]; ring⟩

theorem even_n_mul_succ (n : ℤ) : (2 : ℤ) ∣ n * (n + 1) := by
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨k * (n + 1), by rw [hk]; ring⟩
  · exact ⟨n * (k + 1), by rw [hk]; ring⟩

theorem even_n_mul_5n_add_3 (n : ℤ) : (2 : ℤ) ∣ n * (5 * n + 3) := by
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨k * (5 * n + 3), by rw [hk]; ring⟩
  · exact ⟨n * (5 * k + 4), by rw [hk]; ring⟩

/-- Closed form `2 * T n = n(n-1)`. -/
theorem two_mul_Tn (n : ℤ) : 2 * Tn n = n * (n - 1) := by
  unfold Tn
  rw [mul_comm]; exact Int.ediv_mul_cancel (even_n_mul_pred n)

theorem two_mul_Tplus (n : ℤ) : 2 * Tplus n = n * (n + 1) := by
  unfold Tplus
  rw [mul_comm]; exact Int.ediv_mul_cancel (even_n_mul_succ n)

theorem two_mul_P10 (n : ℤ) : 2 * P10 n = n * (5 * n + 3) := by
  unfold P10
  rw [mul_comm]; exact Int.ediv_mul_cancel (even_n_mul_5n_add_3 n)

/-- `T⁺ n = T n + n`. -/
theorem Tplus_eq_Tn_add (n : ℤ) : Tplus n = Tn n + n := by
  have h1 := two_mul_Tplus n
  have h2 := two_mul_Tn n
  have key : 2 * Tplus n = 2 * (Tn n + n) := by
    rw [mul_add, h1, h2]; ring
  omega

/-- `T(-n) = T⁺ n`. -/
theorem Tn_neg (n : ℤ) : Tn (-n) = Tplus n := by
  have h1 := two_mul_Tn (-n)
  have h2 := two_mul_Tplus n
  have : 2 * Tn (-n) = 2 * Tplus n := by rw [h1, h2]; ring
  omega

/-- `P₁₀(-n) = n(5n - 3)/2`, the reindex used in the diagonal extraction. -/
theorem two_mul_P10_neg (n : ℤ) : 2 * P10 (-n) = n * (5 * n - 3) := by
  have := two_mul_P10 (-n); rw [this]; ring

/-- `T(n+3)` in terms of `T n`. -/
theorem T_add_three (n : ℤ) : Tn (n + 3) = Tn n + 3 * n + 3 := by
  have h1 := two_mul_Tn (n + 3)
  have h2 := two_mul_Tn n
  have : 2 * Tn (n + 3) = 2 * (Tn n + 3 * n + 3) := by rw [h1]; rw [show (2:ℤ) * (Tn n + 3*n+3) = 2 * Tn n + 6*n + 6 by ring, h2]; ring
  omega

/-- The single `Q^m` in `K = ℚ((Q))`. -/
noncomputable def Qpow (m : ℤ) : K := HahnSeries.single m 1

@[simp] theorem Qpow_mul (m n : ℤ) : Qpow m * Qpow n = Qpow (m + n) := by
  unfold Qpow; rw [HahnSeries.single_mul_single, mul_one]

@[simp] theorem Qpow_zero : Qpow 0 = 1 := rfl

theorem Qpow_ne_zero (m : ℤ) : Qpow m ≠ 0 := HahnSeries.single_ne_zero one_ne_zero

@[simp] theorem Qpow_inv (m : ℤ) : (Qpow m)⁻¹ = Qpow (-m) := by
  unfold Qpow; rw [HahnSeries.inv_single]; norm_num

theorem Qpow_mul_Qpow_neg (m : ℤ) : Qpow m * Qpow (-m) = 1 := by
  rw [Qpow_mul, add_neg_cancel, Qpow_zero]

/-- `Qpow e ^ n = Qpow (e·n)` for `n : ℕ`. -/
theorem Qpow_pow_nat (e : ℤ) (n : ℕ) : Qpow e ^ n = Qpow (e * (n : ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, Qpow_mul]; congr 1; push_cast; ring

/-- `Qpow e ^ n = Qpow (e·n)` for `n : ℤ` (zpow). -/
theorem Qpow_zpow (e n : ℤ) : Qpow e ^ n = Qpow (e * n) := by
  rcases n with n | n
  · exact Qpow_pow_nat e n
  · change (Qpow e) ^ (-(n + 1 : ℕ) : ℤ) = Qpow (e * (-(n + 1 : ℕ) : ℤ))
    rw [zpow_neg]
    change ((Qpow e) ^ (n + 1))⁻¹ = Qpow (e * (-(n + 1 : ℕ) : ℤ))
    rw [Qpow_pow_nat, Qpow_inv]
    congr 1; ring

/-- The downward form of the step-3 recurrence: `a n = - Qpow(-(6n+9)) · a(n+3)`. -/
theorem recurrence_down (a : ℤ → K)
    (hrec : ∀ n, a (n + 3) = - Qpow (6 * n + 9) * a n) (n : ℤ) :
    a n = - Qpow (-(6 * n + 9)) * a (n + 3) := by
  rw [hrec n]
  rw [show - Qpow (-(6 * n + 9)) * (- Qpow (6 * n + 9) * a n)
        = (Qpow (-(6 * n + 9)) * Qpow (6 * n + 9)) * a n by ring]
  rw [Qpow_mul, neg_add_cancel, Qpow_zero, one_mul]

/-- **Closed-form recurrence lemma.**  If a `K`-valued sequence satisfies the step-3
recurrence `a(n+3) = - Qpow(6n+9) · a(n)`, then `a(s + 3t) = (-1)^t · Qpow(9t² + 6st) · a(s)`
for all integers `s, t`. -/
theorem coeff_recurrence_closed_form (a : ℤ → K)
    (hrec : ∀ n, a (n + 3) = - Qpow (6 * n + 9) * a n) :
    ∀ s t : ℤ, a (s + 3 * t) = (-1) ^ t * Qpow (9 * t ^ 2 + 6 * s * t) * a s := by
  intro s t
  refine Int.induction_on t ?_ ?_ ?_
  · simp
  · intro k ih
    have hstep := hrec (s + 3 * k)
    rw [show s + 3 * ((k : ℤ) + 1) = (s + 3 * k) + 3 by ring, hstep, ih]
    rw [show ((-1 : K)) ^ ((k : ℤ) + 1) = (-1) ^ (k : ℤ) * (-1) by
      rw [zpow_add₀ (by norm_num : (-1 : K) ≠ 0)]; norm_num]
    -- merge the two Qpow factors on the LHS into one.
    rw [show - Qpow (6 * (s + 3 * k) + 9) * ((-1) ^ (k:ℤ) * Qpow (9 * (k:ℤ) ^ 2 + 6 * s * k) * a s)
          = (-1) ^ (k:ℤ) * (-1) * (Qpow (6 * (s + 3 * k) + 9) * Qpow (9 * (k:ℤ) ^ 2 + 6 * s * k)) * a s
          by ring]
    rw [Qpow_mul]
    rw [show 6 * (s + 3 * k) + 9 + (9 * (k:ℤ) ^ 2 + 6 * s * k)
          = 9 * ((k:ℤ) + 1) ^ 2 + 6 * s * ((k:ℤ) + 1) by ring]
  · intro k ih
    -- target index s + 3*(-(k+1)).  Use downward recurrence at n = s + 3*(-(k+1)).
    have hdown := recurrence_down a hrec (s + 3 * (-(k : ℤ) - 1))
    have hkey : a (s + 3 * (-(k:ℤ) - 1) + 3) = a (s + 3 * (-↑k)) := by congr 1; ring
    rw [hkey, ih] at hdown
    rw [hdown]
    rw [show ((-1 : K)) ^ (-(k:ℤ) - 1) = (-1) ^ (-(k:ℤ)) * (-1) by
      rw [show (-(k:ℤ) - 1) = (-(k:ℤ)) + (-1) by ring, zpow_add₀ (by norm_num : (-1 : K) ≠ 0)]
      norm_num]
    -- merge the two Qpow factors on the LHS.
    rw [show - Qpow (-(6 * (s + 3 * (-(k:ℤ) - 1)) + 9)) *
            ((-1) ^ (-(k:ℤ)) * Qpow (9 * (-(k:ℤ)) ^ 2 + 6 * s * (-(k:ℤ))) * a s)
          = (-1) ^ (-(k:ℤ)) * (-1) *
            (Qpow (-(6 * (s + 3 * (-(k:ℤ) - 1)) + 9)) *
              Qpow (9 * (-(k:ℤ)) ^ 2 + 6 * s * (-(k:ℤ)))) * a s by ring]
    rw [Qpow_mul]
    rw [show -(6 * (s + 3 * (-(k:ℤ) - 1)) + 9) + (9 * (-(k:ℤ)) ^ 2 + 6 * s * (-(k:ℤ)))
          = 9 * (-(k:ℤ) - 1) ^ 2 + 6 * s * (-(k:ℤ) - 1) by ring]

/-! ## Layer C — `thetaMon` as the hsum of a summable family -/

/-- The Q-degree of the `n`-th term of `thetaMon A e i j`. -/
def thetaQDeg (A e n : ℤ) : ℤ := A * Tn n + e * n

/-- For `0 < A`, the Q-degree map `n ↦ A·T n + e·n` is bounded below. -/
theorem thetaQDeg_bddBelow (A e : ℤ) (hA : 0 < A) :
    BddBelow (Set.range (fun n => thetaQDeg A e n)) := by
  -- 2 * thetaQDeg = A n(n-1) + 2 e n = A n² + (2e - A) n.  Complete the square (in ℤ):
  -- 4 A * (2 thetaQDeg) = (2 A n + (2e - A))² - (2e - A)², so thetaQDeg ≥ -(2e-A)²/(8A)-ish.
  -- We give a crude explicit lower bound.
  refine ⟨- (A + (2 * e - A) ^ 2), ?_⟩
  rintro x ⟨n, rfl⟩
  unfold thetaQDeg
  have h2 := two_mul_Tn n
  -- A * Tn n = A * (n(n-1)) / 2 ; multiply the target inequality by 2 and use nonneg squares.
  have hkey : 8 * A * (A * Tn n + e * n) =
      (2 * A * n + (2 * e - A)) ^ 2 - (2 * e - A) ^ 2 := by
    have : 2 * (A * Tn n) = A * (n * (n - 1)) := by rw [← h2]; ring
    nlinarith [this]
  nlinarith [sq_nonneg (2 * A * n + (2 * e - A)), hA, sq_nonneg (2 * e - A)]

/-- For `0 < A`, only finitely many `n` give a fixed Q-degree (quadratic has ≤ 2 roots). -/
theorem thetaQDeg_finite_fiber (A e : ℤ) (hA : 0 < A) (N : ℤ) :
    {n : ℤ | thetaQDeg A e n = N}.Finite := by
  -- `n ↦ thetaQDeg A e n` is strictly monotone for `n ≥ some n₀` and strictly antitone below,
  -- so each level set has at most two elements.  We bound it inside an interval.
  -- 8A·N = (2An+(2e-A))² - (2e-A)², so (2An+(2e-A))² = 8A·N + (2e-A)² is fixed ⟹ finite n.
  apply Set.Finite.subset (Set.finite_Icc
    (-(8 * A * N + (2 * e - A) ^ 2 + (2 * e - A) ^ 2 + 1))
    (8 * A * N + (2 * e - A) ^ 2 + (2 * e - A) ^ 2 + 1))
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  rw [Set.mem_Icc]
  have h2 := two_mul_Tn n
  have hsq : (2 * A * n + (2 * e - A)) ^ 2 = 8 * A * N + (2 * e - A) ^ 2 := by
    have heq : 8 * A * (A * Tn n + e * n) =
        (2 * A * n + (2 * e - A)) ^ 2 - (2 * e - A) ^ 2 := by
      have : 2 * (A * Tn n) = A * (n * (n - 1)) := by rw [← h2]; ring
      nlinarith [this]
    unfold thetaQDeg at hn
    rw [hn] at heq
    linarith [heq]
  -- Let M = 8AN + (2e-A)² = (2An+c)² ≥ 0 and c = 2e-A.  We show |n| ≤ M + A.
  set M : ℤ := 8 * A * N + (2 * e - A) ^ 2 with hM
  set c : ℤ := 2 * e - A with hc
  have hMnonneg : 0 ≤ M := by rw [← hsq]; positivity
  have hAge1 : 1 ≤ A := hA
  -- key: (2An + c)² = M, with M ≥ 0.  Then -(M) ≤ 2An + c ≤ M.
  have hub : 2 * A * n + c ≤ M := by nlinarith [hsq, sq_nonneg (2 * A * n + c - 1)]
  have hlb : -M ≤ 2 * A * n + c := by nlinarith [hsq, sq_nonneg (2 * A * n + c + 1)]
  -- from hub/hlb: -M - c ≤ 2An ≤ M - c.  Hence |n| ≤ 2A|n| = |2An| ≤ M + |c| ≤ M + c² + 1.
  have hAn_ub : 2 * A * n ≤ M - c := by linarith
  have hAn_lb : -M - c ≤ 2 * A * n := by linarith
  have hcc : -c ≤ c ^ 2 + 1 ∧ c ≤ c ^ 2 + 1 := by
    constructor <;> nlinarith [sq_nonneg (c - 1), sq_nonneg (c + 1)]
  refine ⟨?_, ?_⟩
  · -- lower bound on n
    rcases le_or_gt 0 n with hn0 | hn0
    · -- n ≥ 0 ≥ -(M+c²+1)
      nlinarith [hMnonneg, sq_nonneg c, hn0]
    · -- n < 0: n(2A-1) ≤ 0 ⟹ 2An ≤ n, and -M-c ≤ 2An ⟹ n ≥ -M-c ≥ -(M+c²+1)
      nlinarith [hAn_lb, hAge1, hn0, mul_nonneg (by linarith : (0:ℤ) ≤ 2*A - 1) (by linarith : (0:ℤ) ≤ -n), hcc.2]
  · rcases le_or_gt 0 n with hn0 | hn0
    · -- n ≥ 0: n(2A-1) ≥ 0 ⟹ n ≤ 2An ≤ M-c ≤ M+c²+1
      nlinarith [hAn_ub, hAge1, hn0, mul_nonneg (by linarith : (0:ℤ) ≤ 2*A - 1) hn0, hcc.1]
    · -- n < 0 ≤ M+c²+1
      nlinarith [hMnonneg, sq_nonneg c, hn0]

/-- The candidate exponent of the `n`-th term of `thetaMon A e i j`. -/
noncomputable def thetaExp (A e i j n : ℤ) : ExpQXY :=
  expQXY (thetaQDeg A e n) (i * n) (j * n)

/-- For `0 < A`, only finitely many `n` give a fixed candidate exponent. -/
theorem thetaExp_finite_fiber (A e i j : ℤ) (hA : 0 < A) (g : ExpQXY) :
    {n : ℤ | thetaExp A e i j n = g}.Finite := by
  -- the Q-degree slot pins `n` to a fixed value, of which finitely many exist.
  obtain ⟨N, m⟩ := g
  apply Set.Finite.subset (thetaQDeg_finite_fiber A e hA N)
  intro n hn
  simp only [Set.mem_setOf_eq, thetaExp, expQXY] at hn ⊢
  have := (Prod.ext_iff.mp (EmbeddingLike.apply_eq_iff_eq _ |>.mp hn)).1
  exact this

/-- For `0 < A`, the range of candidate exponents is partially well-ordered in `ExpQXY`. -/
theorem thetaExp_range_isPWO (A e i j : ℤ) (hA : 0 < A) :
    (Set.range (fun n => thetaExp A e i j n)).IsPWO := by
  apply Set.PartiallyWellOrderedOn.subsetProdLex
  · -- Q-degree projection of the range is bounded below ⟹ IsWF ⟹ IsPWO in ℤ.
    have hsub : (fun (x : ℤ ×ₗ ExpXY) => (ofLex x).1) '' Set.range (fun n => thetaExp A e i j n)
        ⊆ Set.range (fun n => thetaQDeg A e n) := by
      rintro a ⟨z, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    refine (BddBelow.isWF ?_).isPWO.mono hsub
    obtain ⟨b, hb⟩ := thetaQDeg_bddBelow A e hA
    exact ⟨b, hb⟩
  · -- each fiber is finite, hence PWO.
    intro a
    apply Set.Finite.isPWO
    -- {y | toLex (a,y) ∈ range} = image of {n | thetaQDeg A e n = a} under n ↦ toLex (i n, j n).
    apply Set.Finite.subset (Set.Finite.image
      (fun n => (toLex (i * n, j * n) : ExpXY)) (thetaQDeg_finite_fiber A e hA a))
    rintro y ⟨n, hn⟩
    simp only at hn
    -- hn : thetaExp A e i j n = toLex (a, y)
    refine ⟨n, ?_, ?_⟩
    · -- Q-degree slot: thetaQDeg A e n = a
      have h1 : (ofLex (thetaExp A e i j n)).1 = a := by rw [hn]; rfl
      simpa [thetaExp, expQXY] using h1
    · -- x/y slot: toLex (i n, j n) = y
      have h2 : (ofLex (thetaExp A e i j n)).2 = y := by rw [hn]; rfl
      simpa [thetaExp, expQXY] using h2

/-- The summable family `n ↦ monom (A·T n + e·n) (i·n) (j·n) ((-1)^n)`, for `0 < A`. -/
noncomputable def thetaFamily (A e i j : ℤ) (hA : 0 < A) :
    HahnSeries.SummableFamily ExpQXY ℚ ℤ where
  toFun := fun n => monom (thetaQDeg A e n) (i * n) (j * n) ((-1) ^ n)
  isPWO_iUnion_support' := by
    refine (thetaExp_range_isPWO A e i j hA).mono (Set.iUnion_subset (fun n => ?_))
    intro x hx
    refine ⟨n, ?_⟩
    have : x = expQXY (thetaQDeg A e n) (i * n) (j * n) :=
      HahnSeries.support_single_subset hx
    rw [this]; rfl
  finite_co_support' := by
    intro g
    -- {n | coeff of n-th monom at g ≠ 0} ⊆ {n | thetaExp ... n = g}, which is finite.
    apply Set.Finite.subset (thetaExp_finite_fiber A e i j hA g)
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    by_contra hne
    apply hn
    unfold monom
    rw [HahnSeries.coeff_single_of_ne]
    intro hcon
    exact hne (hcon ▸ rfl)

/-- `thetaMon A e i j`: the theta function `Θ` with weight `Q^e x^i y^j` and nome `Q^A`. -/
noncomputable def thetaMon (A e i j : ℤ) (hA : 0 < A) : S :=
  (thetaFamily A e i j hA).hsum

/-- Coefficient formula for `thetaMon`. -/
theorem thetaMon_coeff (A e i j : ℤ) (hA : 0 < A) (g : ExpQXY) :
    (thetaMon A e i j hA).coeff g =
      ∑ᶠ n, (monom (thetaQDeg A e n) (i * n) (j * n) ((-1) ^ n)).coeff g := by
  unfold thetaMon
  rw [HahnSeries.SummableFamily.coeff_hsum]
  rfl

/-- `T(n+1) = T n + n`. -/
theorem Tn_add_one (n : ℤ) : Tn (n + 1) = Tn n + n := by
  have h1 := two_mul_Tn (n + 1)
  have h2 := two_mul_Tn n
  have : 2 * Tn (n + 1) = 2 * (Tn n + n) := by
    rw [h1, show (2:ℤ) * (Tn n + n) = 2 * Tn n + 2 * n by ring, h2]; ring
  omega

/-- `T(n+2) = T n + 2n + 1`. -/
theorem Tn_add_two (n : ℤ) : Tn (n + 2) = Tn n + 2 * n + 1 := by
  have h1 := two_mul_Tn (n + 2)
  have h2 := two_mul_Tn n
  have : 2 * Tn (n + 2) = 2 * (Tn n + 2 * n + 1) := by
    rw [h1, show (2:ℤ) * (Tn n + 2*n+1) = 2 * Tn n + 4*n + 2 by ring, h2]; ring
  omega

/-- The `n`-th term of the `(e+A)`-family, scaled by `monom e i j (-1)`, equals the
`(n+1)`-th term of the `e`-family.  This is the term-level form of the functional equation. -/
theorem thetaMon_term_shift (A e i j n : ℤ) :
    monom e i j (-1) * monom (thetaQDeg A (e + A) n) (i * n) (j * n) ((-1) ^ n)
      = monom (thetaQDeg A e (n + 1)) (i * (n + 1)) (j * (n + 1)) ((-1) ^ (n + 1)) := by
  rw [monom_mul]
  congr 1
  · -- Q-degree: e + thetaQDeg A (e+A) n = thetaQDeg A e (n+1)
    unfold thetaQDeg
    rw [Tn_add_one]; ring
  · ring
  · ring
  · rw [show (n : ℤ) + 1 = n + 1 from rfl, zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]
    simp [mul_comm]

/-- **Functional equation (10.33)** for `thetaMon`:
`Θ = - (Q^e x^i y^j) · Θ'` where `Θ'` has weight shifted by the nome exponent `A`.
We absorb the sign into the leading monomial: `monom e i j (-1) = -(monom e i j 1)`. -/
theorem thetaMon_fe (A e i j : ℤ) (hA : 0 < A) :
    thetaMon A e i j hA = monom e i j (-1) * thetaMon A (e + A) i j hA := by
  apply HahnSeries.ext
  funext g
  rw [thetaMon_coeff]
  -- RHS: monom e i j (-1) = single (expQXY e i j) (-1); use coeff_single_mul.
  show _ = (HahnSeries.single (expQXY e i j) (-1) * thetaMon A (e + A) i j hA).coeff g
  rw [HahnSeries.coeff_single_mul_S, thetaMon_coeff]
  -- pull the scalar (-1) inside the finsum
  rw [mul_finsum' _ _ (by
    -- finite support of n ↦ (term).coeff (g - expQXY e i j)
    exact (thetaFamily A (e + A) i j hA).finite_co_support' (g - expQXY e i j))]
  -- reindex n ↦ n+1 on the LHS so both finsums match termwise
  rw [← finsum_comp_equiv (Equiv.addRight (1 : ℤ))]
  apply finsum_congr
  intro n
  simp only [Equiv.coe_addRight]
  -- goal: (term_e (n+1)).coeff g = -1 * (term_{e+A} n).coeff (g - expQXY e i j)
  have hshift := thetaMon_term_shift A e i j n
  -- LHS term = monom e i j (-1) * (term_{e+A} n); take coeff g via coeff_single_mul.
  rw [← hshift]
  show _ = (-1 : ℚ) * _
  rw [show monom e i j (-1) = HahnSeries.single (expQXY e i j) (-1) from rfl]
  rw [HahnSeries.coeff_single_mul_S]

/-- `monom e i j (-1) = - monom e i j 1`. -/
theorem monom_neg_one (e i j : ℤ) : monom e i j (-1) = - monom e i j 1 := by
  unfold monom
  rw [← HahnSeries.single_neg]

/-- **Functional equation (10.33)**, in the design's exact form:
`Θ(A,e,i,j) = - (Q^e x^i y^j) · Θ(A, e+A, i, j)`. -/
theorem thetaMon_fe' (A e i j : ℤ) (hA : 0 < A) :
    thetaMon A e i j hA = - monom e i j 1 * thetaMon A (e + A) i j hA := by
  rw [thetaMon_fe A e i j hA, monom_neg_one, neg_mul]

/-- `(-1)^(-n) = (-1)^n` in `ℚ`. -/
theorem negOne_zpow_neg (n : ℤ) : ((-1 : ℚ)) ^ (-n) = (-1) ^ n := by
  rw [zpow_neg]
  -- (-1)^n is its own inverse since it squares to 1.
  have hsq : ((-1 : ℚ) ^ n) * ((-1 : ℚ) ^ n) = 1 := by
    rw [← zpow_add₀ (by norm_num : (-1:ℚ) ≠ 0)]
    rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [show n + n = 2 * (k + k) by omega, zpow_mul]; norm_num
    · rw [show n + n = 2 * (2 * k + 1) by omega, zpow_mul]; norm_num
  exact eq_comm.mp (eq_inv_of_mul_eq_one_left hsq)

/-- The x-symmetry Q-degree identity: `thetaQDeg 3 3 (-n) = thetaQDeg 3 0 n`. -/
theorem thetaQDeg_x_sym (n : ℤ) : thetaQDeg 3 3 (-n) = thetaQDeg 3 0 n := by
  unfold thetaQDeg
  have h1 := two_mul_Tn (-n)
  have h2 := two_mul_Tn n
  have e1 : (-n) * (-n - 1) = n * (n + 1) := by ring
  rw [e1] at h1
  -- h1: 2*Tn(-n) = n(n+1), h2: 2*Tn n = n(n-1); difference is linear: n(n+1)-n(n-1)=2n.
  have hlin : n * (n + 1) - n * (n - 1) = 2 * n := by ring
  omega

/-! ### Symmetry specials -/

/-- `Θ(q/x) = Θ(x)`: `thetaMon 3 3 (-1) 0 = thetaMon 3 0 1 0` (the x-symmetry). -/
theorem theta_q_div_x_eq_theta_x :
    thetaMon 3 3 (-1) 0 (by norm_num) = thetaMon 3 0 1 0 (by norm_num) := by
  apply HahnSeries.ext
  funext g
  rw [thetaMon_coeff, thetaMon_coeff]
  -- reindex n ↦ -n: the (-1)-weighted x-family at exponent 3 maps onto the +1 family.
  rw [← finsum_comp_equiv (Equiv.neg ℤ)]
  apply finsum_congr
  intro n
  simp only [Equiv.neg_apply]
  exact monom_eq_monom (thetaQDeg_x_sym n)
    (show (-1 : ℤ) * (-n) = 1 * n by ring) (show (0 : ℤ) * (-n) = 0 * n by ring)
    (negOne_zpow_neg n) ▸ rfl

/-- `Θ(q/y) = Θ(y)`: `thetaMon 3 3 0 (-1) = thetaMon 3 0 0 1` (the y-symmetry). -/
theorem theta_q_div_y_eq_theta_y :
    thetaMon 3 3 0 (-1) (by norm_num) = thetaMon 3 0 0 1 (by norm_num) := by
  apply HahnSeries.ext
  funext g
  rw [thetaMon_coeff, thetaMon_coeff]
  rw [← finsum_comp_equiv (Equiv.neg ℤ)]
  apply finsum_congr
  intro n
  simp only [Equiv.neg_apply]
  exact monom_eq_monom (thetaQDeg_x_sym n)
    (show (0 : ℤ) * (-n) = 0 * n by ring) (show (-1 : ℤ) * (-n) = 1 * n by ring)
    (negOne_zpow_neg n) ▸ rfl

/-! ## Layer D — q-Pochhammer bridge

We import the committed formal-power-series infrastructure (`qPochInfPS`, the cube
identity `qPochInfPS^3 = jacobiThetaPS`) and transport it into `K = ℚ((Q))` via
`HahnSeries.ofPowerSeries` composed with `PowerSeries.expand` (the `q = Q^3` rescaling).
-/

open QseriesFormalization.PartIV.Ch19 (qPochInfPS jacobiThetaPS jacobiTripleSign
  coeff_jacobiThetaPS)

/-- `ofPowerSeries ℤ ℚ : ℚ⟦X⟧ →+* K`, sending `X ↦ Q` (i.e. `single 1 1`). -/
noncomputable def ofPSK : PowerSeries ℚ →+* K := HahnSeries.ofPowerSeries ℤ ℚ

@[simp] theorem ofPSK_coeff_nat (f : PowerSeries ℚ) (n : ℕ) :
    (ofPSK f).coeff (n : ℤ) = PowerSeries.coeff n f := by
  unfold ofPSK
  exact HahnSeries.ofPowerSeries_apply_coeff f n

/-- `ofPSK f` is supported on nonnegative `ℤ`-exponents. -/
theorem ofPSK_coeff_neg (f : PowerSeries ℚ) (a : ℤ) (ha : a < 0) :
    (ofPSK f).coeff a = 0 := by
  unfold ofPSK
  rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
  rintro ⟨n, hn⟩
  have : (n : ℤ) = a := hn
  omega

/-- `poch_q := (Q^3;Q^3)_∞`, the cube root `q = Q^3` rescaling of `(q;q)_∞`. -/
noncomputable def poch_q : K := ofPSK (PowerSeries.expand 3 (by norm_num) (qPochInfPS ℚ))

/-- `poch_q2 := (Q^6;Q^6)_∞`. -/
noncomputable def poch_q2 : K := ofPSK (PowerSeries.expand 6 (by norm_num) (qPochInfPS ℚ))

/-- The constant coefficient of `qPochInfPS ℚ` is `1`. -/
theorem constantCoeff_qPochInfPS_rat :
    PowerSeries.constantCoeff (qPochInfPS ℚ) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have := QseriesFormalization.PartIV.Ch19.coeff_zero_qPochInfPS ℚ
  simpa using this

/-- `poch_q` has constant term `1`, hence is nonzero. -/
theorem poch_q_coeff_zero : poch_q.coeff 0 = 1 := by
  unfold poch_q
  have h0 : (0 : ℤ) = ((0 : ℕ) : ℤ) := by norm_num
  rw [h0, ofPSK_coeff_nat]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_expand,
    constantCoeff_qPochInfPS_rat]

theorem poch_q2_coeff_zero : poch_q2.coeff 0 = 1 := by
  unfold poch_q2
  have h0 : (0 : ℤ) = ((0 : ℕ) : ℤ) := by norm_num
  rw [h0, ofPSK_coeff_nat]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_expand,
    constantCoeff_qPochInfPS_rat]

theorem poch_q_ne_zero : poch_q ≠ 0 := by
  intro h
  have := poch_q_coeff_zero
  rw [h, HahnSeries.coeff_zero] at this
  exact one_ne_zero this.symm

theorem poch_q2_ne_zero : poch_q2 ≠ 0 := by
  intro h
  have := poch_q2_coeff_zero
  rw [h, HahnSeries.coeff_zero] at this
  exact one_ne_zero this.symm

/-- `embedQ` of a power of `f` is the power of `embedQ f` (a `RingHom.map_pow`). -/
theorem embedQ_pow (f : K) (m : ℕ) : embedQ (f ^ m) = (embedQ f) ^ m := by
  exact map_pow embedQ f m

theorem embedQ_mul (f g : K) : embedQ (f * g) = embedQ f * embedQ g := map_mul embedQ f g

theorem embedQ_one : embedQ (1 : K) = 1 := map_one embedQ

/-! ### A `K`-level theta summable family

The one-variable theta sums `∑' t, single (3·T t) (w t)` (in `K = ℚ((Q))`) needed for
`theta_one_zero` and the Jacobi derivative.  The Q-degree `3·T t = thetaQDeg 3 0 t` is
bounded below with finite fibers (reusing the layer-C bounds), so the family is summable. -/

/-- The `K`-summable family `t ↦ single (3·T t) (w t)`. -/
noncomputable def kThetaFamily (w : ℤ → ℚ) :
    HahnSeries.SummableFamily ℤ ℚ ℤ where
  toFun := fun t => HahnSeries.single (thetaQDeg 3 0 t) (w t)
  isPWO_iUnion_support' := by
    have hb := thetaQDeg_bddBelow 3 0 (by norm_num)
    refine (hb.isWF.isPWO).mono (Set.iUnion_subset (fun t => ?_))
    intro x hx
    have hxe : x = thetaQDeg 3 0 t := HahnSeries.support_single_subset hx
    exact ⟨t, hxe.symm⟩
  finite_co_support' := by
    intro g
    apply Set.Finite.subset (thetaQDeg_finite_fiber 3 0 (by norm_num) g)
    intro t ht
    simp only [Set.mem_setOf_eq] at ht
    by_contra hne
    apply ht
    rw [HahnSeries.coeff_single_of_ne]
    intro hcon
    exact hne hcon.symm

/-- The hsum of `kThetaFamily w`. -/
noncomputable def kTheta (w : ℤ → ℚ) : K := (kThetaFamily w).hsum

/-- Coefficient of `kTheta w` at a Q-degree `m`: the finsum of the single-term coefficients. -/
theorem kTheta_coeff (w : ℤ → ℚ) (m : ℤ) :
    (kTheta w).coeff m =
      ∑ᶠ t, (HahnSeries.single (thetaQDeg 3 0 t) (w t)).coeff m := by
  unfold kTheta
  rw [HahnSeries.SummableFamily.coeff_hsum]
  rfl

/-- `T t = T (1 - t)`: the involution at the heart of the `t ↦ 1-t` pairing. -/
theorem Tn_one_sub (t : ℤ) : Tn (1 - t) = Tn t := by
  have h1 := two_mul_Tn (1 - t)
  have h2 := two_mul_Tn t
  have : (1 - t) * (1 - t - 1) = t * (t - 1) := by ring
  omega

/-- `thetaQDeg 3 0 (1 - t) = thetaQDeg 3 0 t`: Q-degree invariance under `t ↦ 1-t`. -/
theorem thetaQDeg_one_sub (t : ℤ) : thetaQDeg 3 0 (1 - t) = thetaQDeg 3 0 t := by
  unfold thetaQDeg
  rw [Tn_one_sub]; ring

/-- If `w` is anti-invariant under `t ↦ 1-t` (i.e. `w (1-t) = - w t`), then `kTheta w = 0`.
This is the `t ↦ 1-t` cancellation underlying `j(1;q) = 0`. -/
theorem kTheta_eq_zero_of_anti (w : ℤ → ℚ) (hw : ∀ t, w (1 - t) = - w t) :
    kTheta w = 0 := by
  apply HahnSeries.ext
  funext m
  rw [kTheta_coeff, HahnSeries.coeff_zero]
  -- reindex t ↦ 1-t : the term at (1-t) is the negation of the term at t.
  have hreindex : (∑ᶠ t, (HahnSeries.single (thetaQDeg 3 0 t) (w t)).coeff m)
      = ∑ᶠ t, (HahnSeries.single (thetaQDeg 3 0 (1 - t)) (w (1 - t))).coeff m := by
    rw [← finsum_comp_equiv (Equiv.subLeft (1 : ℤ))]
    rfl
  have hneg : (∑ᶠ t, (HahnSeries.single (thetaQDeg 3 0 (1 - t)) (w (1 - t))).coeff m)
      = - ∑ᶠ t, (HahnSeries.single (thetaQDeg 3 0 t) (w t)).coeff m := by
    rw [← finsum_neg_distrib]
    apply finsum_congr
    intro t
    rw [thetaQDeg_one_sub, hw t, HahnSeries.single_neg, HahnSeries.coeff_neg]
  have := hreindex.trans hneg
  linarith [this]

/-- `(-1)^(1-t) = -(-1)^t` in `ℚ` (for `t : ℤ`). -/
theorem negOne_zpow_one_sub (t : ℤ) : ((-1 : ℚ)) ^ (1 - t) = - (-1) ^ t := by
  rw [show (1 - t) = (-t) + 1 by ring, zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0),
    negOne_zpow_neg t, zpow_one]
  ring

/-- **`theta_one_zero` (the classical `j(1;q) = 0`).**  The one-variable theta at `u = 1`
vanishes: `∑' t, Q^{3·T t} (-1)^t = 0` (packaged as `kTheta`). -/
theorem theta_one_zero : kTheta (fun t => (-1) ^ t) = 0 := by
  apply kTheta_eq_zero_of_anti
  intro t
  exact negOne_zpow_one_sub t

/-! ### Jacobi's derivative identity `-∑ (-1)^t t q^{T t} = (q;q)_∞^3` -/

/-- `poch_q^3` is the `q = Q^3` rescaling of `(q;q)_∞^3 = jacobiThetaPS`. -/
theorem poch_q_cube_eq :
    poch_q ^ 3 = ofPSK (PowerSeries.expand 3 (by norm_num) (jacobiThetaPS ℚ)) := by
  unfold poch_q
  rw [← map_pow, ← map_pow,
    QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS]

/-- Coefficient of `poch_q^3` at `m`: nonzero only at nonnegative multiples of `3`. -/
theorem poch_q_cube_coeff (m : ℤ) :
    (poch_q ^ 3).coeff m =
      if h : 0 ≤ m ∧ (3 : ℤ) ∣ m then ((jacobiTripleSign (m / 3).toNat : ℤ) : ℚ) else 0 := by
  rw [poch_q_cube_eq]
  by_cases h : 0 ≤ m ∧ (3 : ℤ) ∣ m
  · rw [dif_pos h]
    obtain ⟨hm0, k, hk⟩ := h
    have hk0 : 0 ≤ k := by omega
    obtain ⟨kn, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
    rw [show m = ((3 * kn : ℕ) : ℤ) by rw [hk]; push_cast; ring]
    rw [ofPSK_coeff_nat]
    rw [PowerSeries.coeff_expand_mul 3 (by norm_num)]
    rw [coeff_jacobiThetaPS]
    congr 2
    omega
  · rw [dif_neg h]
    rcases lt_or_ge m 0 with hlt | hge
    · exact ofPSK_coeff_neg _ m hlt
    · -- m ≥ 0 but 3 ∤ m
      have hnd : ¬ (3 : ℤ) ∣ m := by tauto
      obtain ⟨mn, rfl⟩ := Int.eq_ofNat_of_zero_le hge
      rw [ofPSK_coeff_nat]
      rw [PowerSeries.coeff_expand_of_not_dvd 3 (by norm_num)]
      intro hdvd
      apply hnd
      obtain ⟨c, hc⟩ := hdvd
      exact ⟨c, by omega⟩

/-- The coefficient of `kTheta w` at `m` as a finsum of an if-indicator over `ℤ`. -/
theorem kTheta_coeff_if (w : ℤ → ℚ) (m : ℤ) :
    (kTheta w).coeff m = ∑ᶠ t, (if thetaQDeg 3 0 t = m then w t else 0) := by
  rw [kTheta_coeff]
  apply finsum_congr
  intro t
  rw [HahnSeries.coeff_single]
  by_cases h : thetaQDeg 3 0 t = m
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hc => h hc.symm)]

/-- The fiber `{t : 3·T t = m}` is finite (reusing the layer-C finite-fiber bound). -/
theorem kTheta_fiber_finite (m : ℤ) : {t : ℤ | thetaQDeg 3 0 t = m}.Finite :=
  thetaQDeg_finite_fiber 3 0 (by norm_num) m

/-- The fiber `{t : 3·T t = 3·T t₀}` equals `{t₀, 1 - t₀}` (the two solutions of `T t = T t₀`). -/
theorem fiber_eq_pair (t₀ : ℤ) :
    {t : ℤ | thetaQDeg 3 0 t = thetaQDeg 3 0 t₀} = {t₀, 1 - t₀} := by
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  unfold thetaQDeg
  constructor
  · intro h
    -- 3*Tn t = 3*Tn t₀ ⟹ Tn t = Tn t₀ ⟹ t = t₀ or t = 1-t₀ (T t = t(t-1)/2 quadratic).
    have hT : Tn t = Tn t₀ := by omega
    have h2 := two_mul_Tn t
    have h2' := two_mul_Tn t₀
    have hq : t * (t - 1) = t₀ * (t₀ - 1) := by omega
    -- (t - t₀)(t + t₀ - 1) = 0
    have hfac : (t - t₀) * (t + t₀ - 1) = 0 := by ring_nf; nlinarith [hq]
    rcases mul_eq_zero.mp hfac with h' | h'
    · left; omega
    · right; omega
  · rintro (rfl | rfl)
    · rfl
    · have := Tn_one_sub t₀
      omega

/-- `t₀ ≠ 1 - t₀` over `ℤ` (no half-integer fixed point). -/
theorem ne_one_sub (t₀ : ℤ) : t₀ ≠ 1 - t₀ := by omega

/-- **The coefficient of `kTheta w` at a degree `3·T t₀` is the fiber-pair sum
`w t₀ + w (1 - t₀)`.** -/
theorem kTheta_coeff_at_fiber (w : ℤ → ℚ) (t₀ : ℤ) :
    (kTheta w).coeff (thetaQDeg 3 0 t₀) = w t₀ + w (1 - t₀) := by
  rw [kTheta_coeff_if]
  -- support of (fun t => if 3 T t = 3 T t₀ then w t else 0) ⊆ fiber = {t₀, 1-t₀}.
  have hfin : {t : ℤ | thetaQDeg 3 0 t = thetaQDeg 3 0 t₀}.Finite :=
    kTheta_fiber_finite _
  have hsubset : Function.support (fun t => if thetaQDeg 3 0 t = thetaQDeg 3 0 t₀ then w t else 0)
      ⊆ {t : ℤ | thetaQDeg 3 0 t = thetaQDeg 3 0 t₀} := by
    intro t ht
    simp only [Function.mem_support] at ht
    by_contra hc
    simp only [Set.mem_setOf_eq] at hc
    rw [if_neg hc] at ht
    exact ht rfl
  rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset)
    (by rwa [Set.Finite.coe_toFinset])]
  -- the finite fiber set equals {t₀, 1-t₀}.
  have hset : hfin.toFinset = ({t₀, 1 - t₀} : Finset ℤ) := by
    apply Finset.ext
    intro t
    rw [Set.Finite.mem_toFinset]
    rw [fiber_eq_pair t₀]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
  rw [hset, Finset.sum_insert (by simp [ne_one_sub t₀]), Finset.sum_singleton]
  rw [if_pos rfl, if_pos (by unfold thetaQDeg; have := Tn_one_sub t₀; omega)]

/-! ### Jacobi's derivative identity, finished -/

/-- `Tn t ≥ 0` for all integers (product of consecutive integers). -/
theorem Tn_nonneg (t : ℤ) : 0 ≤ Tn t := by
  have h := two_mul_Tn t
  have hprod : 0 ≤ t * (t - 1) := by
    rcases le_or_gt 1 t with h1 | h1
    · exact mul_nonneg (by omega) (by omega)
    · nlinarith [h1]
  omega

/-- The pair-sum weight of the derivative kernel at `t₀`:
`g t₀ + g (1-t₀) = (-1)^{t₀}(2t₀-1)` where `g t = (-1)^t · t`. -/
theorem deriv_pair_weight (t₀ : ℤ) :
    ((-1 : ℚ) ^ t₀ * t₀) + ((-1) ^ (1 - t₀) * (1 - t₀)) = (-1) ^ t₀ * (2 * t₀ - 1) := by
  rw [negOne_zpow_one_sub t₀]
  ring

/-- For `t₀ ≥ 1`: `Tn t₀ = (t₀-1)·t₀/2` is the `(t₀-1)`-th triangular number, and
`jacobiTripleSign` there is `(-1)^{t₀-1}(2t₀-1) = -(-1)^{t₀}(2t₀-1)`. -/
theorem jts_at_Tn_eq (t₀ : ℤ) (ht : 1 ≤ t₀) :
    ((QseriesFormalization.PartIV.Ch19.jacobiTripleSign (Tn t₀).toNat : ℤ) : ℚ)
      = - ((-1) ^ t₀ * (2 * t₀ - 1)) := by
  -- k := (t₀ - 1).toNat, so t₀ = k + 1 and Tn t₀ = k(k+1)/2.
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, t₀ = (k : ℤ) + 1 := ⟨(t₀ - 1).toNat, by omega⟩
  have hTn : (Tn ((k : ℤ) + 1)).toNat = k * (k + 1) / 2 := by
    have h2 := two_mul_Tn ((k : ℤ) + 1)
    have hev : 2 ∣ k * (k + 1) := (Nat.even_mul_succ_self k).two_dvd
    have hZ : Tn ((k : ℤ) + 1) = (((k * (k + 1) / 2 : ℕ)) : ℤ) := by
      have hmul : (((k * (k + 1) / 2 : ℕ)) : ℤ) * 2 = (k : ℤ) * ((k : ℤ) + 1) := by
        have : (k * (k + 1) / 2 : ℕ) * 2 = k * (k + 1) := Nat.div_mul_cancel hev
        have := congrArg (Nat.cast : ℕ → ℤ) this
        push_cast at this ⊢
        linarith [this]
      have hpoly : ((k : ℤ) + 1) * ((k : ℤ) + 1 - 1) = (k : ℤ) * ((k : ℤ) + 1) := by ring
      rw [hpoly] at h2
      omega
    rw [hZ, Int.toNat_natCast]
  rw [hTn, QseriesFormalization.PartIV.Ch19.jacobiTripleSign_triangular k]
  -- (-1)^k(2k+1) = -((-1)^{k+1}(2(k+1)-1)) over ℚ.
  push_cast
  rw [show ((k : ℤ) + 1) = (k : ℤ) + 1 from rfl,
    zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0), zpow_natCast, zpow_one]
  ring

/-- **Jacobi's derivative identity (rescaled to `K`):**
`-∑' t, Q^{3·T t} (-1)^t · t = poch_q³`. -/
theorem jacobi_derivative_poch_cube :
    - (kTheta (fun t => (-1) ^ t * t)) = poch_q ^ 3 := by
  apply HahnSeries.ext
  funext m
  rw [HahnSeries.coeff_neg, poch_q_cube_coeff]
  by_cases hm : 0 ≤ m ∧ (3 : ℤ) ∣ m
  · rw [dif_pos hm]
    obtain ⟨hm0, k3, hk3⟩ := hm
    set N : ℤ := m / 3 with hN
    have hmN : m = 3 * N := by rw [hN]; omega
    have hN0 : 0 ≤ N := by omega
    by_cases htri : ∃ t₀ : ℤ, 1 ≤ t₀ ∧ Tn t₀ = N
    · obtain ⟨t₀, ht1, htN⟩ := htri
      have hdeg : thetaQDeg 3 0 t₀ = m := by unfold thetaQDeg; rw [htN]; omega
      rw [hdeg.symm, kTheta_coeff_at_fiber]
      have hNtoNat : (m / 3).toNat = (Tn t₀).toNat := by rw [← hN, ← htN]
      rw [hNtoNat, jts_at_Tn_eq t₀ ht1]
      push_cast
      have := deriv_pair_weight t₀
      push_cast at this
      rw [this]
    · -- N not a triangular T-value ⟹ both coeffs are 0.
      push_neg at htri
      -- LHS coeff at m is 0 (no t with 3 T t = m).
      have hLHS : (kTheta (fun t => (-1) ^ t * t)).coeff m = 0 := by
        rw [kTheta_coeff_if]
        apply finsum_eq_zero_of_forall_eq_zero
        intro t
        by_cases hc : thetaQDeg 3 0 t = m
        · exfalso
          -- then 3 T t = m = 3 N ⟹ T t = N; one of t, 1-t is ≥ 1, contradicting htri.
          have hTtN : Tn t = N := by unfold thetaQDeg at hc; omega
          rcases le_or_gt 1 t with h1 | h1
          · exact htri t h1 hTtN
          · -- t ≤ 0 ⟹ 1 - t ≥ 1 and Tn (1-t) = Tn t = N.
            exact htri (1 - t) (by omega) (by rw [Tn_one_sub]; exact hTtN)
        · rw [if_neg hc]
      rw [hLHS, neg_zero]
      -- RHS coeff is jacobiTripleSign (m/3).toNat; must show it is 0.
      have hnt : ∀ a ≤ (m / 3).toNat, (m / 3).toNat ≠ a * (a + 1) / 2 := by
        intro a _ ha
        apply htri ((a : ℤ) + 1) (by omega)
        have h2 := two_mul_Tn ((a : ℤ) + 1)
        have hNa : N = ((m / 3).toNat : ℤ) := by rw [← hN]; omega
        have hev : 2 ∣ a * (a + 1) := (Nat.even_mul_succ_self a).two_dvd
        have hcast : ((a * (a + 1) / 2 : ℕ) : ℤ) * 2 = (a : ℤ) * ((a : ℤ) + 1) := by
          have : (a * (a + 1) / 2 : ℕ) * 2 = a * (a + 1) := Nat.div_mul_cancel hev
          have := congrArg (Nat.cast : ℕ → ℤ) this
          push_cast at this ⊢; linarith [this]
        have hpoly : ((a : ℤ) + 1) * ((a : ℤ) + 1 - 1) = (a : ℤ) * ((a : ℤ) + 1) := by ring
        rw [hpoly] at h2
        -- N = ↑(m/3).toNat = ↑(a*(a+1)/2); and Tn(a+1)*2 = a*(a+1) = ↑(...)*2.
        rw [hNa, ha]
        omega
      rw [QseriesFormalization.PartIV.Ch19.jacobiTripleSign_of_not_triangular _ hnt]
      norm_num
  · rw [dif_neg hm]
    -- m < 0 or 3 ∤ m ⟹ LHS coeff is 0 too.
    have hLHS : (kTheta (fun t => (-1) ^ t * t)).coeff m = 0 := by
      rw [kTheta_coeff_if]
      apply finsum_eq_zero_of_forall_eq_zero
      intro t
      by_cases hc : thetaQDeg 3 0 t = m
      · exfalso
        apply hm
        unfold thetaQDeg at hc
        have hTn := Tn_nonneg t
        refine ⟨by omega, ?_⟩
        exact ⟨Tn t, by omega⟩
      · rw [if_neg hc]
    rw [hLHS, neg_zero]

/-! ## Layer E — Zwegers Lemma 10.1 (functional-equation route)

The classical identity (Chen, Eq. 10.34; Zwegers 2010, Lemma 3.1)
`∑_{k,l} (-1)^{k+l}(δ(k)-δ(l)) q^{(k²+l²)/3} x^l = -x⁻¹q^{1/3} (q²;q²)∞/(q;q)∞ Θ(x;q²)Θ(x;q)`,
proved here in the `poch_q2`-cleared form to avoid `K`-division.
-/

/-- Chan's residue `δ`: `δ(k) = 1` if `3 ∣ k`, else `0`. -/
def delta3 (k : ℤ) : ℚ := if (3 : ℤ) ∣ k then 1 else 0

@[simp] theorem delta3_of_dvd {k : ℤ} (h : (3 : ℤ) ∣ k) : delta3 k = 1 := if_pos h
@[simp] theorem delta3_of_not_dvd {k : ℤ} (h : ¬ (3 : ℤ) ∣ k) : delta3 k = 0 := if_neg h

/-! ### The 2D summable family for the Zwegers LHS

Q-degree `k²+l²` is bounded below by `0` with finite fibers (lattice points on a
circle), so the family indexed by `ℤ × ℤ` is summable in `S`. -/

/-- The candidate exponent of the `(k,l)`-th Zwegers term: `Q^{k²+l²} x^l`. -/
noncomputable def zExp (k l : ℤ) : ExpQXY := expQXY (k ^ 2 + l ^ 2) l 0

/-- The `(k,l)` coefficient weight `(-1)^{k+l}(δ k − δ l)`. -/
noncomputable def zW (k l : ℤ) : ℚ := (-1) ^ (k + l) * (delta3 k - delta3 l)

/-- For a fixed Q-degree `N`, only finitely many `(k,l)` have `k²+l² = N`. -/
theorem zDeg_finite_fiber (N : ℤ) : {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 2 = N}.Finite := by
  apply Set.Finite.subset (Set.finite_Icc
    ((-(N.natAbs : ℤ), -(N.natAbs : ℤ)) : ℤ × ℤ)
    (((N.natAbs : ℤ), (N.natAbs : ℤ)) : ℤ × ℤ))
  rintro ⟨k, l⟩ hkl
  simp only [Set.mem_setOf_eq] at hkl
  have hk2 : k ^ 2 ≤ N := by nlinarith [sq_nonneg l]
  have hl2 : l ^ 2 ≤ N := by nlinarith [sq_nonneg k]
  have hNn : (N : ℤ) ≤ (N.natAbs : ℤ) := Int.le_natAbs
  rw [Set.mem_Icc, Prod.le_def, Prod.le_def]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    nlinarith [sq_nonneg k, sq_nonneg l, sq_nonneg (k - 1), sq_nonneg (k + 1),
      sq_nonneg (l - 1), sq_nonneg (l + 1), hk2, hl2, hNn]

/-- The range of `(k,l) ↦ zExp k l` is partially well-ordered in `ExpQXY`. -/
theorem zExp_range_isPWO : (Set.range (fun p : ℤ × ℤ => zExp p.1 p.2)).IsPWO := by
  apply Set.PartiallyWellOrderedOn.subsetProdLex
  · -- Q-degree projection bounded below by 0.
    have hsub : (fun (z : ℤ ×ₗ ExpXY) => (ofLex z).1) ''
        Set.range (fun p : ℤ × ℤ => zExp p.1 p.2) ⊆ Set.Ici (0 : ℤ) := by
      rintro a ⟨z, ⟨⟨k, l⟩, rfl⟩, rfl⟩
      simp only [zExp, expQXY, ofLex_toLex, Set.mem_Ici]
      positivity
    refine (?_ : (Set.Ici (0 : ℤ)).IsPWO).mono hsub
    exact (bddBelow_Ici.isWF).isPWO
  · -- each Q-degree fiber is finite.
    intro N
    apply Set.Finite.isPWO
    apply Set.Finite.subset (Set.Finite.image
      (fun p : ℤ × ℤ => (toLex (p.2, (0 : ℤ)) : ExpXY)) (zDeg_finite_fiber N))
    rintro y ⟨⟨k, l⟩, hkl⟩
    simp only at hkl
    refine ⟨(k, l), ?_, ?_⟩
    · have h1 : (ofLex (zExp k l)).1 = N := by rw [hkl]; rfl
      simpa [zExp, expQXY] using h1
    · have h2 : (ofLex (zExp k l)).2 = y := by rw [hkl]; rfl
      simpa [zExp, expQXY] using h2

/-- The 2D summable family `(k,l) ↦ monom (k²+l²) l 0 ((-1)^{k+l}(δ k − δ l))`. -/
noncomputable def zFamily : HahnSeries.SummableFamily ExpQXY ℚ (ℤ × ℤ) where
  toFun := fun p => monom (p.1 ^ 2 + p.2 ^ 2) p.2 0 (zW p.1 p.2)
  isPWO_iUnion_support' := by
    refine zExp_range_isPWO.mono (Set.iUnion_subset (fun p => ?_))
    intro g hg
    refine ⟨p, ?_⟩
    have : g = expQXY (p.1 ^ 2 + p.2 ^ 2) p.2 0 :=
      HahnSeries.support_single_subset hg
    rw [this]; rfl
  finite_co_support' := by
    intro g
    apply Set.Finite.subset (zDeg_finite_fiber ((ofLex g).1))
    rintro ⟨k, l⟩ hkl
    simp only [Set.mem_setOf_eq] at hkl ⊢
    by_contra hne
    apply hkl
    unfold monom
    rw [HahnSeries.coeff_single_of_ne]
    intro hcon
    apply hne
    -- hcon : g = expQXY (k²+l²) l 0; Q-degree of g is (ofLex g).1 = k²+l².
    rw [hcon]; rfl

/-- `zwegersLHS_x`: the left-hand side of Zwegers' Lemma 10.1. -/
noncomputable def zwegersLHS_x : S := zFamily.hsum

/-- The `Q`-degree-`a` coefficient of the `x`-slice of `zwegersLHS_x` at `x^l` is the
2D finsum of the family-term coefficients at `expQXY a l 0`. -/
theorem coeffXY_zwegersLHS_x_coeff (l a : ℤ) :
    (coeffXY zwegersLHS_x l 0).coeff a
      = ∑ᶠ p : ℤ × ℤ, (monom (p.1 ^ 2 + p.2 ^ 2) p.2 0 (zW p.1 p.2)).coeff (expQXY a l 0) := by
  rw [coeffXY_coeff, coeffQXY]
  unfold zwegersLHS_x
  rw [HahnSeries.SummableFamily.coeff_hsum]
  rfl

/-- **Bare step-3 FE for the `x`-slice of `zwegersLHS_x`.**  Reindex `(k,l) ↦ (k, l+3)`:
the term at `(k,l+3)` is `monom (k²+l²+6l+9) (l+3) 0 (-zW k l)`, so the `x^{l+3}` slice
equals `-Qpow(6l+9)` times the `x^l` slice. -/
theorem zwegersLHS_x_slice_fe (l : ℤ) :
    coeffXY zwegersLHS_x (l + 3) 0 = - Qpow (6 * l + 9) * coeffXY zwegersLHS_x l 0 := by
  apply HahnSeries.ext
  funext a
  rw [show - Qpow (6 * l + 9) * coeffXY zwegersLHS_x l 0
        = - (Qpow (6 * l + 9) * coeffXY zwegersLHS_x l 0) by ring]
  rw [HahnSeries.coeff_neg]
  rw [show (Qpow (6 * l + 9) * coeffXY zwegersLHS_x l 0).coeff a
        = (coeffXY zwegersLHS_x l 0).coeff (a - (6 * l + 9)) by
    unfold Qpow
    rw [HahnSeries.coeff_single_mul, one_mul]]
  rw [coeffXY_zwegersLHS_x_coeff, coeffXY_zwegersLHS_x_coeff]
  rw [← finsum_neg_distrib]
  -- reindex p = (k, m) ↦ (k, m+3) on the LHS sum.
  rw [← finsum_comp_equiv ((Equiv.refl ℤ).prodCongr (Equiv.addRight (3 : ℤ)))]
  apply finsum_congr
  rintro ⟨k, m⟩
  simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.coe_addRight, Prod.map_apply, id_eq]
  unfold monom
  rw [HahnSeries.coeff_single, HahnSeries.coeff_single]
  by_cases hm : m = l
  · subst hm
    have hdvd : (3 : ℤ) ∣ (m + 3) ↔ (3 : ℤ) ∣ m := by
      constructor <;> intro h <;> omega
    have hdelta : delta3 (m + 3) = delta3 m := by
      unfold delta3
      by_cases h3 : (3 : ℤ) ∣ m
      · rw [if_pos h3, if_pos (hdvd.mpr h3)]
      · rw [if_neg h3, if_neg (fun hc => h3 (hdvd.mp hc))]
    have hzW : zW k (m + 3) = - zW k m := by
      unfold zW
      rw [hdelta]
      rw [show k + (m + 3) = (k + m) + 3 by ring,
        zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]
      norm_num
    have hL : (expQXY a (m + 3) 0 = expQXY (k ^ 2 + (m + 3) ^ 2) (m + 3) 0)
        ↔ a = k ^ 2 + (m + 3) ^ 2 := by
      constructor
      · intro hc; exact (expQXY_inj hc).1
      · intro hc; rw [hc]
    have hR : (expQXY (a - (6 * m + 9)) m 0 = expQXY (k ^ 2 + m ^ 2) m 0)
        ↔ a = k ^ 2 + (m + 3) ^ 2 := by
      constructor
      · intro hc; have := (expQXY_inj hc).1; nlinarith [this]
      · intro hc; rw [show a - (6 * m + 9) = k ^ 2 + m ^ 2 by rw [hc]; ring]
    by_cases hcond : a = k ^ 2 + (m + 3) ^ 2
    · rw [if_pos (hL.mpr hcond), if_pos (hR.mpr hcond), hzW]
    · rw [if_neg (fun hc => hcond (hL.mp hc)), if_neg (fun hc => hcond (hR.mp hc)), neg_zero]
  · -- x-degrees mismatch on both sides ⟹ both coefficients are 0.
    rw [if_neg ?_, if_neg ?_, neg_zero]
    · intro hc; exact hm (by have := (expQXY_inj hc).2.1; omega)
    · intro hc; exact hm (by have := (expQXY_inj hc).2.1; omega)

/-! ### Uniqueness from the step-3 functional equation -/

/-- **Uniqueness lemma.**  If a `K`-valued sequence satisfies the step-3 recurrence
`a(n+3) = -Qpow(6n+9)·a(n)` and vanishes at `0, 1, 2`, then it vanishes everywhere.
(Write `n = r + 3t` with `r ∈ {0,1,2}` and apply `coeff_recurrence_closed_form`.) -/
theorem coeff_eq_zero_of_fe_step3 (a : ℤ → K)
    (hrec : ∀ n, a (n + 3) = - Qpow (6 * n + 9) * a n)
    (h0 : a 0 = 0) (h1 : a 1 = 0) (h2 : a 2 = 0) :
    ∀ n, a n = 0 := by
  intro n
  -- n = r + 3 t with r = n % 3 ∈ {0,1,2}, t = n / 3 (Int.emod / ediv).
  set r : ℤ := n % 3 with hr
  set t : ℤ := n / 3 with ht
  have hn : n = r + 3 * t := by rw [hr, ht]; omega
  have hrange : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  have hcf := coeff_recurrence_closed_form a hrec r t
  rw [← hn] at hcf
  rw [hcf]
  rcases hrange with h | h | h
  · rw [h, h0, mul_zero]
  · rw [h, h1, mul_zero]
  · rw [h, h2, mul_zero]

/-- **Reducing `LHS = RHS` to: FE on both sides + agreement of the three initial
x-coefficients.**  This is the uniqueness skeleton of Zwegers' Lemma 10.1: if the
per-x-power coefficient slices `a_L(n) = coeffXY F n 0` and `a_R(n) = coeffXY G n 0`
both satisfy the step-3 functional equation and agree at `n = 0, 1, 2`, then `F = G`. -/
theorem eq_of_fe_step3_and_initial (F G : S)
    (hFL : ∀ n, coeffXY F (n + 3) 0 = - Qpow (6 * n + 9) * coeffXY F n 0)
    (hGL : ∀ n, coeffXY G (n + 3) 0 = - Qpow (6 * n + 9) * coeffXY G n 0)
    (hzero : ∀ i j, j ≠ 0 → ∀ a, coeffQXY F a i j = 0 ∧ coeffQXY G a i j = 0)
    (h0 : coeffXY F 0 0 = coeffXY G 0 0)
    (h1 : coeffXY F 1 0 = coeffXY G 1 0)
    (h2 : coeffXY F 2 0 = coeffXY G 2 0) :
    F = G := by
  -- difference slice d(n) := coeffXY F n 0 - coeffXY G n 0 satisfies FE and vanishes at 0,1,2.
  set d : ℤ → K := fun n => coeffXY F n 0 - coeffXY G n 0 with hd
  have hdrec : ∀ n, d (n + 3) = - Qpow (6 * n + 9) * d n := by
    intro n; simp only [hd]; rw [hFL n, hGL n]; ring
  have hzeros := coeff_eq_zero_of_fe_step3 d hdrec
    (by simp only [hd]; rw [h0]; ring)
    (by simp only [hd]; rw [h1]; ring)
    (by simp only [hd]; rw [h2]; ring)
  -- hence coeffXY F n 0 = coeffXY G n 0 for ALL x-powers n.
  have hxeq : ∀ n, coeffXY F n 0 = coeffXY G n 0 := by
    intro n; have := hzeros n; simp only [hd] at this; exact sub_eq_zero.mp this
  -- combine with the `y ≠ 0` vanishing to get full equality of coefficients.
  apply ext_coeffQXY
  intro a i j
  by_cases hj : j = 0
  · subst hj
    have hF := congrArg (fun (s : K) => s.coeff a) (hxeq i)
    simpa only [coeffXY_coeff] using hF
  · obtain ⟨hFj, hGj⟩ := hzero i j hj a
    rw [hFj, hGj]

/-! ### Plane-support infrastructure (`y⁰`- and `x⁰`-supported series) -/

/-- `F` is supported in the `y = 0` plane. -/
def YZeroSupported (F : S) : Prop := ∀ a i j, j ≠ 0 → coeffQXY F a i j = 0
/-- `F` is supported in the `x = 0` plane. -/
def XZeroSupported (F : S) : Prop := ∀ a i j, i ≠ 0 → coeffQXY F a i j = 0

theorem YZeroSupported.neg {F : S} (h : YZeroSupported F) : YZeroSupported (-F) := by
  intro a i j hj; rw [coeffQXY, HahnSeries.coeff_neg, ← coeffQXY, h a i j hj, neg_zero]

theorem XZeroSupported.neg {F : S} (h : XZeroSupported F) : XZeroSupported (-F) := by
  intro a i j hi; rw [coeffQXY, HahnSeries.coeff_neg, ← coeffQXY, h a i j hi, neg_zero]

/-- `monom a i 0 c` is `y⁰`-supported. -/
theorem YZeroSupported_monom (a i : ℤ) (c : ℚ) : YZeroSupported (monom a i 0 c) := by
  intro a' i' j' hj'
  rw [coeffQXY_monom]
  rw [if_neg (by rintro ⟨_, _, hj⟩; exact hj' hj)]

/-- `monom a 0 j c` is `x⁰`-supported. -/
theorem XZeroSupported_monom (a j : ℤ) (c : ℚ) : XZeroSupported (monom a 0 j c) := by
  intro a' i' j' hi'
  rw [coeffQXY_monom]
  rw [if_neg (by rintro ⟨_, hi, _⟩; exact hi' hi)]

/-- `embedQ f` is `y⁰`-supported (it lives in the `x⁰y⁰` plane). -/
theorem YZeroSupported_embedQ (f : K) : YZeroSupported (embedQ f) := by
  intro a i j hj
  exact embedQ_coeff_of_ne f a i j (by tauto)

/-- `embedQ f` is `x⁰`-supported. -/
theorem XZeroSupported_embedQ (f : K) : XZeroSupported (embedQ f) := by
  intro a i j hi
  exact embedQ_coeff_of_ne f a i j (by tauto)

/-- Eta for `expQXY`: any `g : ExpQXY` is `expQXY` of its three projections. -/
theorem expQXY_eta (g : ExpQXY) :
    g = expQXY (ofLex g).1 (ofLex (ofLex g).2).1 (ofLex (ofLex g).2).2 := rfl

/-- The `y`-degree projection of `expQXY a i j` is `j`. -/
@[simp] theorem ydeg_expQXY (a i j : ℤ) : (ofLex (ofLex (expQXY a i j)).2).2 = j := rfl
/-- The `x`-degree projection of `expQXY a i j` is `i`. -/
@[simp] theorem xdeg_expQXY (a i j : ℤ) : (ofLex (ofLex (expQXY a i j)).2).1 = i := rfl
/-- The `q`-degree projection of `expQXY a i j` is `a`. -/
@[simp] theorem qdeg_expQXY (a i j : ℤ) : (ofLex (expQXY a i j)).1 = a := rfl

/-- The `y`-degree projection is additive on `ExpQXY`. -/
theorem ydeg_add (g1 g2 : ExpQXY) :
    (ofLex (ofLex (g1 + g2)).2).2 = (ofLex (ofLex g1).2).2 + (ofLex (ofLex g2).2).2 := rfl
/-- The `x`-degree projection is additive on `ExpQXY`. -/
theorem xdeg_add (g1 g2 : ExpQXY) :
    (ofLex (ofLex (g1 + g2)).2).1 = (ofLex (ofLex g1).2).1 + (ofLex (ofLex g2).2).1 := rfl

/-- `thetaMon A e i 0` is `y⁰`-supported (every term has `y`-degree `0·n = 0`). -/
theorem YZeroSupported_thetaMon (A e i : ℤ) (hA : 0 < A) :
    YZeroSupported (thetaMon A e i 0 hA) := by
  intro a i' j' hj'
  rw [coeffQXY, thetaMon_coeff]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  rw [show (0 : ℤ) * n = 0 by ring]
  unfold monom
  rw [HahnSeries.coeff_single_of_ne]
  intro hcon
  exact hj' ((expQXY_inj hcon.symm).2.2).symm

/-- `thetaMon A e 0 j` is `x⁰`-supported. -/
theorem XZeroSupported_thetaMon (A e j : ℤ) (hA : 0 < A) :
    XZeroSupported (thetaMon A e 0 j hA) := by
  intro a i' j' hi'
  rw [coeffQXY, thetaMon_coeff]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  rw [show (0 : ℤ) * n = 0 by ring]
  unfold monom
  rw [HahnSeries.coeff_single_of_ne]
  intro hcon
  exact hi' ((expQXY_inj hcon.symm).2.1).symm

/-- The product of two `y⁰`-supported series is `y⁰`-supported. -/
theorem YZeroSupported.mul {F G : S} (hF : YZeroSupported F) (hG : YZeroSupported G) :
    YZeroSupported (F * G) := by
  intro a i j hj
  rw [coeffQXY, HahnSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨g1, g2⟩ hmem
  rw [Finset.mem_addAntidiagonal] at hmem
  obtain ⟨_, _, hsum⟩ := hmem
  -- y-degrees of g1, g2 sum to j ≠ 0, so one is nonzero.
  have hjsum : (ofLex (ofLex g1).2).2 + (ofLex (ofLex g2).2).2 = j := by
    rw [← ydeg_add, hsum, ydeg_expQXY]
  by_cases h1 : (ofLex (ofLex g1).2).2 ≠ 0
  · have hF0 : F.coeff g1 = 0 := by
      have := hF (ofLex g1).1 (ofLex (ofLex g1).2).1 (ofLex (ofLex g1).2).2 h1
      rwa [coeffQXY, ← expQXY_eta] at this
    rw [hF0, zero_mul]
  · push_neg at h1
    have h2 : (ofLex (ofLex g2).2).2 ≠ 0 := by omega
    have hG0 : G.coeff g2 = 0 := by
      have := hG (ofLex g2).1 (ofLex (ofLex g2).2).1 (ofLex (ofLex g2).2).2 h2
      rwa [coeffQXY, ← expQXY_eta] at this
    rw [hG0, mul_zero]

/-- The product of two `x⁰`-supported series is `x⁰`-supported. -/
theorem XZeroSupported.mul {F G : S} (hF : XZeroSupported F) (hG : XZeroSupported G) :
    XZeroSupported (F * G) := by
  intro a i j hi
  rw [coeffQXY, HahnSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨g1, g2⟩ hmem
  rw [Finset.mem_addAntidiagonal] at hmem
  obtain ⟨_, _, hsum⟩ := hmem
  have hisum : (ofLex (ofLex g1).2).1 + (ofLex (ofLex g2).2).1 = i := by
    rw [← xdeg_add, hsum, xdeg_expQXY]
  by_cases h1 : (ofLex (ofLex g1).2).1 ≠ 0
  · have hF0 : F.coeff g1 = 0 := by
      have := hF (ofLex g1).1 (ofLex (ofLex g1).2).1 (ofLex (ofLex g1).2).2 h1
      rwa [coeffQXY, ← expQXY_eta] at this
    rw [hF0, zero_mul]
  · push_neg at h1
    have h2 : (ofLex (ofLex g2).2).1 ≠ 0 := by omega
    have hG0 : G.coeff g2 = 0 := by
      have := hG (ofLex g2).1 (ofLex (ofLex g2).2).1 (ofLex (ofLex g2).2).2 h2
      rwa [coeffQXY, ← expQXY_eta] at this
    rw [hG0, mul_zero]

/-- If every term of a summable family is `y⁰`-supported, so is its `hsum`. -/
theorem YZeroSupported_hsum {α : Type*} (s : HahnSeries.SummableFamily ExpQXY ℚ α)
    (h : ∀ x, YZeroSupported (s x)) : YZeroSupported s.hsum := by
  intro a i j hj
  rw [coeffQXY, HahnSeries.SummableFamily.coeff_hsum]
  apply finsum_eq_zero_of_forall_eq_zero
  intro x
  have := h x a i j hj
  rwa [coeffQXY] at this

/-- If every term of a summable family is `x⁰`-supported, so is its `hsum`. -/
theorem XZeroSupported_hsum {α : Type*} (s : HahnSeries.SummableFamily ExpQXY ℚ α)
    (h : ∀ x, XZeroSupported (s x)) : XZeroSupported s.hsum := by
  intro a i j hi
  rw [coeffQXY, HahnSeries.SummableFamily.coeff_hsum]
  apply finsum_eq_zero_of_forall_eq_zero
  intro x
  have := h x a i j hi
  rwa [coeffQXY] at this

/-- `zwegersLHS_x` is `y⁰`-supported (every family term `monom (k²+l²) l 0 (…)` is). -/
theorem YZeroSupported_zwegersLHS_x : YZeroSupported zwegersLHS_x := by
  unfold zwegersLHS_x
  apply YZeroSupported_hsum
  rintro ⟨k, l⟩
  exact YZeroSupported_monom _ _ _

/-! ### The Zwegers RHS and the main identity (Lemma 10.1, `x`-version)

We state Zwegers' Lemma 10.1 in the `poch_q2`-cleared form
`embedQ poch_q2 · LHS = - (Q x⁻¹) · embedQ poch_q · Θ(x;q²) · Θ(x;q)`
(verified numerically; design `chan3-Ch10-twovar-source-route.md`).  `thetaX_q := thetaMon 3 0 1 0`,
`thetaX_q2 := thetaMon 6 0 1 0`. -/

/-- `Θ(x;q) = thetaMon 3 0 1 0`. -/
noncomputable def thetaX_q : S := thetaMon 3 0 1 0 (by norm_num)
/-- `Θ(x;q²) = thetaMon 6 0 1 0`. -/
noncomputable def thetaX_q2 : S := thetaMon 6 0 1 0 (by norm_num)

/-- The product family `Θ(x;q²)·Θ(x;q)` as a `SummableFamily` over `ℤ × ℤ`. -/
noncomputable def thetaProdX : HahnSeries.SummableFamily ExpQXY ℚ (ℤ × ℤ) :=
  HahnSeries.SummableFamily.mul (thetaFamily 6 0 1 0 (by norm_num)) (thetaFamily 3 0 1 0 (by norm_num))

theorem thetaProdX_hsum : thetaProdX.hsum = thetaX_q2 * thetaX_q := by
  unfold thetaProdX thetaX_q2 thetaX_q thetaMon
  rw [HahnSeries.SummableFamily.hsum_mul]

/-- The product family term at `(n2,n1)`. -/
theorem thetaProdX_term (n2 n1 : ℤ) :
    thetaProdX (n2, n1)
      = monom (6 * Tn n2 + 3 * Tn n1) (n2 + n1) 0 ((-1) ^ (n2 + n1)) := by
  unfold thetaProdX
  show monom (thetaQDeg 6 0 n2) (1 * n2) (0 * n2) ((-1) ^ n2)
        * monom (thetaQDeg 3 0 n1) (1 * n1) (0 * n1) ((-1) ^ n1) = _
  rw [monom_mul]
  apply monom_eq_monom
  · unfold thetaQDeg; ring
  · ring
  · ring
  · rw [zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]

/-- The `Q`-degree-`a` coefficient of the `x`-slice of `Θ(x;q²)·Θ(x;q)` at `x^m`. -/
theorem coeffXY_thetaProdX_coeff (m a : ℤ) :
    (coeffXY (thetaX_q2 * thetaX_q) m 0).coeff a
      = ∑ᶠ p : ℤ × ℤ,
          (monom (6 * Tn p.1 + 3 * Tn p.2) (p.1 + p.2) 0 ((-1) ^ (p.1 + p.2))).coeff (expQXY a m 0) := by
  rw [coeffXY_coeff, coeffQXY, ← thetaProdX_hsum, HahnSeries.SummableFamily.coeff_hsum]
  apply finsum_congr
  rintro ⟨n2, n1⟩
  rw [thetaProdX_term]

/-- **Bare step-3 FE for the `x`-slice of `Θ(x;q²)·Θ(x;q)`.**  Reindex `(n2,n1) ↦ (n2+1,n1+2)`. -/
theorem thetaProdX_slice_fe (m : ℤ) :
    coeffXY (thetaX_q2 * thetaX_q) (m + 3) 0
      = - Qpow (6 * m + 3) * coeffXY (thetaX_q2 * thetaX_q) m 0 := by
  apply HahnSeries.ext
  funext a
  rw [show - Qpow (6 * m + 3) * coeffXY (thetaX_q2 * thetaX_q) m 0
        = - (Qpow (6 * m + 3) * coeffXY (thetaX_q2 * thetaX_q) m 0) by ring]
  rw [HahnSeries.coeff_neg]
  rw [show (Qpow (6 * m + 3) * coeffXY (thetaX_q2 * thetaX_q) m 0).coeff a
        = (coeffXY (thetaX_q2 * thetaX_q) m 0).coeff (a - (6 * m + 3)) by
    unfold Qpow
    rw [HahnSeries.coeff_single_mul, one_mul]]
  rw [coeffXY_thetaProdX_coeff, coeffXY_thetaProdX_coeff]
  rw [← finsum_neg_distrib]
  rw [← finsum_comp_equiv ((Equiv.addRight (1 : ℤ)).prodCongr (Equiv.addRight (2 : ℤ)))]
  apply finsum_congr
  rintro ⟨n2, n1⟩
  simp only [Equiv.prodCongr_apply, Equiv.coe_addRight, Prod.map_apply]
  unfold monom
  rw [HahnSeries.coeff_single, HahnSeries.coeff_single]
  by_cases hxd : n2 + n1 = m
  · have hdeg : 6 * Tn (n2 + 1) + 3 * Tn (n1 + 2)
        = (6 * Tn n2 + 3 * Tn n1) + (6 * m + 3) := by
      rw [Tn_add_one, Tn_add_two]; rw [← hxd]; ring
    have hsign : ((-1 : ℚ)) ^ ((n2 + 1) + (n1 + 2)) = - (-1) ^ (n2 + n1) := by
      rw [show (n2 + 1) + (n1 + 2) = (n2 + n1) + 3 by ring,
        zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]
      norm_num
    have hxL : (n2 + 1) + (n1 + 2) = m + 3 := by omega
    have hL : (expQXY a (m + 3) 0
          = expQXY (6 * Tn (n2 + 1) + 3 * Tn (n1 + 2)) ((n2 + 1) + (n1 + 2)) 0)
        ↔ a = 6 * Tn (n2 + 1) + 3 * Tn (n1 + 2) := by
      constructor
      · intro hc; exact (expQXY_inj hc).1
      · intro hc; rw [hc, hxL]
    have hR : (expQXY (a - (6 * m + 3)) m 0 = expQXY (6 * Tn n2 + 3 * Tn n1) (n2 + n1) 0)
        ↔ a = 6 * Tn (n2 + 1) + 3 * Tn (n1 + 2) := by
      constructor
      · intro hc
        have h1 := (expQXY_inj hc).1
        rw [hdeg]; omega
      · intro hc
        rw [show a - (6 * m + 3) = 6 * Tn n2 + 3 * Tn n1 by rw [hc, hdeg]; ring]
        rw [hxd]
    by_cases hcond : a = 6 * Tn (n2 + 1) + 3 * Tn (n1 + 2)
    · rw [if_pos (hL.mpr hcond), if_pos (hR.mpr hcond), hsign]
    · rw [if_neg (fun hc => hcond (hL.mp hc)), if_neg (fun hc => hcond (hR.mp hc)), neg_zero]
  · rw [if_neg ?_, if_neg ?_, neg_zero]
    · intro hc; exact hxd (by have := (expQXY_inj hc).2.1; omega)
    · intro hc; exact hxd (by have := (expQXY_inj hc).2.1; omega)

/-- `zwegersRHS_x` (cleared form): `- (Q x⁻¹) · embedQ poch_q · Θ(x;q²) · Θ(x;q)`. -/
noncomputable def zwegersRHS_x : S :=
  - monom 1 (-1) 0 1 * embedQ poch_q * thetaX_q2 * thetaX_q

/-! The five irreducible analytic inputs of Zwegers' proof (Chen Eq. 10.34–10.38), each a
one-variable `K`-identity / per-slice functional equation, numerically verified in
`chan3-Ch10-twovar-source-route.md` and `/tmp/zwfe.py`.  These are the genuinely-resistant
pieces (per the design's flagged candidates), isolated with exact statements;
everything that consumes them is proved unconditionally. -/

/-- Step-3 FE for the cleared LHS slice (Chen Eq. 10.35 translated).  The `embedQ poch_q2`
factor passes through the slice (`coeffXY_embedQ_mul`) and the bare slice satisfies the FE
(`zwegersLHS_x_slice_fe`). -/
theorem zwegers_FE_LHS_x (n : ℤ) :
    coeffXY (embedQ poch_q2 * zwegersLHS_x) (n + 3) 0
      = - Qpow (6 * n + 9) * coeffXY (embedQ poch_q2 * zwegersLHS_x) n 0 := by
  rw [coeffXY_embedQ_mul, coeffXY_embedQ_mul, zwegersLHS_x_slice_fe]
  ring

/-- The `x`-slice of `zwegersRHS_x` is `single 1 (-1) · poch_q · (slice of `Θ(x;q²)·Θ(x;q)` at `l+1`)`. -/
theorem coeffXY_zwegersRHS_x (l : ℤ) :
    coeffXY zwegersRHS_x l 0
      = HahnSeries.single 1 (-1 : ℚ) * poch_q * coeffXY (thetaX_q2 * thetaX_q) (l + 1) 0 := by
  have hassoc : zwegersRHS_x
      = monom 1 (-1) 0 (-1) * (embedQ poch_q * (thetaX_q2 * thetaX_q)) := by
    unfold zwegersRHS_x
    rw [show (- monom 1 (-1) 0 1 : S) = monom 1 (-1) 0 (-1) by rw [← monom_neg_one]]
    ring
  rw [hassoc, coeffXY_monom_mul, coeffXY_embedQ_mul]
  rw [show l - (-1) = l + 1 by ring]
  rw [mul_assoc]

/-- Step-3 FE for the cleared RHS slice (Chen Eq. 10.35).  The `monom`/`embedQ` factors pass
through the slice; the product `Θ(x;q²)·Θ(x;q)` slice satisfies its own FE (`thetaProdX_slice_fe`). -/
theorem zwegers_FE_RHS_x (n : ℤ) :
    coeffXY zwegersRHS_x (n + 3) 0
      = - Qpow (6 * n + 9) * coeffXY zwegersRHS_x n 0 := by
  rw [coeffXY_zwegersRHS_x, coeffXY_zwegersRHS_x]
  rw [show (n + 3 + 1 : ℤ) = (n + 1) + 3 by ring]
  rw [thetaProdX_slice_fe]
  rw [show (6 * (n + 1) + 3 : ℤ) = 6 * n + 9 by ring]
  ring

/-- The cleared LHS lives in the `y⁰` plane (`embedQ poch_q2` and every LHS term have `y`-degree 0). -/
theorem zwegers_yplane_LHS_x (i j : ℤ) (hj : j ≠ 0) (a : ℤ) :
    coeffQXY (embedQ poch_q2 * zwegersLHS_x) a i j = 0 :=
  ((YZeroSupported_embedQ poch_q2).mul YZeroSupported_zwegersLHS_x) a i j hj

/-- The cleared RHS lives in the `y⁰` plane (all factors have `y`-degree 0). -/
theorem zwegers_yplane_RHS_x (i j : ℤ) (hj : j ≠ 0) (a : ℤ) :
    coeffQXY zwegersRHS_x a i j = 0 := by
  unfold zwegersRHS_x thetaX_q2 thetaX_q
  exact ((((YZeroSupported_monom 1 (-1) 1).neg.mul (YZeroSupported_embedQ poch_q)).mul
    (YZeroSupported_thetaMon 6 0 1 (by norm_num))).mul
    (YZeroSupported_thetaMon 3 0 1 (by norm_num))) a i j hj

/-! ### General one-variable `K`-theta objects `J(z;Q^A)` and the Zwegers slice reductions

We reduce both slices `coeffXY zwegersLHS_x j 0` (`j=0,1,2`) and
`coeffXY (thetaX_q2*thetaX_q) m 0` (`m=1,2,3`) to one-variable theta sums
`J = ∑'_r single (A·T r + e·r) (w r)` (a `K`-element), then to the two product
identities `P0`/`P12`. -/

/-- The general `K`-summable theta family `r ↦ single (A·T r + e·r) (w r)`, for `0 < A`
(mirror of `kThetaGen`, with arbitrary nome exponent `A`). -/
noncomputable def JKFamily (A e : ℤ) (hA : 0 < A) (w : ℤ → ℚ) :
    HahnSeries.SummableFamily ℤ ℚ ℤ where
  toFun := fun r => HahnSeries.single (thetaQDeg A e r) (w r)
  isPWO_iUnion_support' := by
    have hb := thetaQDeg_bddBelow A e hA
    refine (hb.isWF.isPWO).mono (Set.iUnion_subset (fun r => ?_))
    intro x hx
    have hxe : x = thetaQDeg A e r := HahnSeries.support_single_subset hx
    exact ⟨r, hxe.symm⟩
  finite_co_support' := by
    intro g
    apply Set.Finite.subset (thetaQDeg_finite_fiber A e hA g)
    intro r hr
    simp only [Set.mem_setOf_eq] at hr
    by_contra hne
    apply hr
    rw [HahnSeries.coeff_single_of_ne]
    intro hcon
    exact hne hcon.symm

/-- `J(z;Q^A) = ∑'_r (w r)·Q^{A·T r + e·r}` as a `K`-element. -/
noncomputable def JK (A e : ℤ) (hA : 0 < A) (w : ℤ → ℚ) : K := (JKFamily A e hA w).hsum

/-- Coefficient of `JK` at `m` as an indicator finsum. -/
theorem JK_coeff (A e : ℤ) (hA : 0 < A) (w : ℤ → ℚ) (m : ℤ) :
    (JK A e hA w).coeff m = ∑ᶠ r : ℤ, (if thetaQDeg A e r = m then w r else 0) := by
  unfold JK
  rw [HahnSeries.SummableFamily.coeff_hsum]
  apply finsum_congr
  intro r
  show (HahnSeries.single (thetaQDeg A e r) (w r)).coeff m = _
  rw [HahnSeries.coeff_single]
  by_cases h : thetaQDeg A e r = m
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hc => h hc.symm)]

/-- The four `J`'s appearing in the Zwegers slices (in `Q`-notation, `q=Q³`):
`J(Q^15;Q^18)`, `J(Q^9;Q^18)`, `J(-1;Q^9)`, `J(-Q^6;Q^9)`. -/
noncomputable def JQ15 : K := JK 18 15 (by norm_num) (fun r => (-1) ^ r)
noncomputable def JQ9  : K := JK 18 9  (by norm_num) (fun r => (-1) ^ r)
noncomputable def Jneg1 : K := JK 9 0 (by norm_num) (fun _ => 1)
noncomputable def JnegQ6 : K := JK 9 6 (by norm_num) (fun _ => 1)

/-- **Theta-product slice collapse (2D → 1D).**  The `x^m` slice coefficient of `Θ(x;q²)Θ(x;q)`
collapses to a one-variable diagonal finsum over `n` (with `p = (n, m−n)`). -/
theorem coeffXY_thetaProdX_collapse (m a : ℤ) :
    (coeffXY (thetaX_q2 * thetaX_q) m 0).coeff a
      = ∑ᶠ n : ℤ, (if 6 * Tn n + 3 * Tn (m - n) = a then ((-1 : ℚ) ^ m) else 0) := by
  rw [coeffXY_thetaProdX_coeff]
  -- the summand as an explicit indicator in `(p.1, p.2)`.
  have hg : ∀ p : ℤ × ℤ,
      (monom (6 * Tn p.1 + 3 * Tn p.2) (p.1 + p.2) 0 ((-1) ^ (p.1 + p.2))).coeff (expQXY a m 0)
        = (if (6 * Tn p.1 + 3 * Tn p.2 = a ∧ p.1 + p.2 = m) then ((-1 : ℚ) ^ (p.1 + p.2)) else 0) := by
    rintro ⟨n2, n1⟩
    unfold monom
    rw [HahnSeries.coeff_single]
    by_cases hc : a = 6 * Tn n2 + 3 * Tn n1 ∧ m = n2 + n1
    · rw [if_pos (by rw [hc.1, hc.2])]
      rw [if_pos ⟨hc.1.symm, hc.2.symm⟩]
    · rw [if_neg (by rintro he; exact hc ⟨(expQXY_inj he).1, (expQXY_inj he).2.1⟩)]
      rw [if_neg (by rintro ⟨h1, h2⟩; exact hc ⟨h1.symm, h2.symm⟩)]
  simp_rw [hg]
  -- the support of `p ↦ indicator` is finite (only `p.2 = m − p.1` contributes, finite fibres in `a`).
  have hfin : (Function.support
      (fun p : ℤ × ℤ => if (6 * Tn p.1 + 3 * Tn p.2 = a ∧ p.1 + p.2 = m) then ((-1 : ℚ) ^ (p.1 + p.2)) else 0)).Finite := by
    apply Set.Finite.subset (thetaProdX.finite_co_support' (expQXY a m 0))
    rintro ⟨n2, n1⟩ hp
    simp only [Function.mem_support, ne_eq] at hp
    simp only [Set.mem_setOf_eq]
    show (thetaProdX (n2, n1)).coeff (expQXY a m 0) ≠ 0
    rw [thetaProdX_term, hg (n2, n1)]
    exact hp
  rw [finsum_curry _ hfin]
  apply finsum_congr
  intro n
  -- inner sum over the second coordinate collapses at `s = m − n`.
  rw [finsum_eq_single _ (m - n)]
  · simp only
    rw [show n + (m - n) = m by ring]
    by_cases hcond : 6 * Tn n + 3 * Tn (m - n) = a
    · rw [if_pos ⟨hcond, by ring⟩, if_pos hcond]
    · rw [if_neg (by rintro ⟨h1, _⟩; exact hcond h1), if_neg hcond]
  · intro s hs
    rw [if_neg]
    rintro ⟨_, h2⟩
    exact hs (by omega)

/-- **Circle-sum slice collapse (2D → 1D).**  The `x^l` slice coefficient of `zwegersLHS_x`
collapses to a one-variable circle finsum over `k` (with `p = (k, l)`). -/
theorem coeffXY_zwegersLHS_x_collapse (l a : ℤ) :
    (coeffXY zwegersLHS_x l 0).coeff a
      = ∑ᶠ k : ℤ, (if k ^ 2 + l ^ 2 = a then zW k l else 0) := by
  rw [coeffXY_zwegersLHS_x_coeff]
  have hg : ∀ p : ℤ × ℤ,
      (monom (p.1 ^ 2 + p.2 ^ 2) p.2 0 (zW p.1 p.2)).coeff (expQXY a l 0)
        = (if (p.1 ^ 2 + p.2 ^ 2 = a ∧ p.2 = l) then zW p.1 p.2 else 0) := by
    rintro ⟨k, s⟩
    unfold monom
    rw [HahnSeries.coeff_single]
    by_cases hc : a = k ^ 2 + s ^ 2 ∧ l = s
    · rw [if_pos (by rw [hc.1, hc.2]), if_pos ⟨hc.1.symm, hc.2.symm⟩]
    · rw [if_neg (by rintro he; exact hc ⟨(expQXY_inj he).1, (expQXY_inj he).2.1⟩)]
      rw [if_neg (by rintro ⟨h1, h2⟩; exact hc ⟨h1.symm, h2.symm⟩)]
  simp_rw [hg]
  have hfin : (Function.support
      (fun p : ℤ × ℤ => if (p.1 ^ 2 + p.2 ^ 2 = a ∧ p.2 = l) then zW p.1 p.2 else 0)).Finite := by
    apply Set.Finite.subset (zFamily.finite_co_support' (expQXY a l 0))
    rintro ⟨k, s⟩ hp
    simp only [Function.mem_support, ne_eq] at hp
    simp only [Set.mem_setOf_eq]
    show (zFamily (k, s)).coeff (expQXY a l 0) ≠ 0
    rw [show zFamily (k, s) = monom (k ^ 2 + s ^ 2) s 0 (zW k s) from rfl]
    rw [hg (k, s)]
    exact hp
  rw [finsum_curry _ hfin]
  apply finsum_congr
  intro k
  rw [finsum_eq_single _ l]
  · by_cases hcond : k ^ 2 + l ^ 2 = a
    · rw [if_pos ⟨hcond, rfl⟩, if_pos hcond]
    · rw [if_neg (by rintro ⟨h1, _⟩; exact hcond h1), if_neg hcond]
  · intro s hs
    rw [if_neg]
    rintro ⟨_, h2⟩
    exact hs h2

/-- A finsum over `ℤ` whose summand vanishes off multiples of `3` collapses to a finsum over
the index `r` with `k = 3r`. -/
theorem finsum_multiples_three {M : Type*} [AddCommMonoid M] (f : ℤ → M)
    (hsupp : ∀ k, ¬ (3 ∣ k) → f k = 0) :
    (∑ᶠ k : ℤ, f k) = ∑ᶠ r : ℤ, f (3 * r) := by
  have hrange : Function.support f ⊆ Set.range (fun r : ℤ => 3 * r) := by
    intro k hk
    simp only [Function.mem_support] at hk
    by_contra hc
    refine hk (hsupp k ?_)
    rintro ⟨r, hr⟩
    exact hc ⟨r, by simp only []; omega⟩
  rw [← finsum_mem_range (f := f) (g := fun r : ℤ => 3 * r) (fun a b h => by simpa using h)]
  rw [eq_comm, ← finsum_mem_inter_support, Set.inter_eq_right.mpr hrange,
      ← Set.univ_inter (Function.support f), finsum_mem_inter_support, finsum_mem_univ]

/-- `thetaQDeg 18 9 r = 9r²` and `thetaQDeg 18 15 r = 9r²+6r = (3r+1)²−1`. -/
theorem thetaQDeg_18_9 (r : ℤ) : thetaQDeg 18 9 r = 9 * r ^ 2 := by
  unfold thetaQDeg; have h := two_mul_Tn r; nlinarith [h]
theorem thetaQDeg_18_15 (r : ℤ) : thetaQDeg 18 15 r = (3 * r + 1) ^ 2 - 1 := by
  unfold thetaQDeg; have h := two_mul_Tn r; nlinarith [h]

/-- `(-1)^{3r} = (-1)^r` in `ℚ`. -/
theorem negOne_zpow_three_mul (r : ℤ) : ((-1 : ℚ)) ^ (3 * r) = (-1) ^ r := by
  rw [zpow_mul]; norm_num

/-- `zW k 1 = 0` when `3 ∤ k` (so the `j=1` circle slice is supported on multiples of `3`). -/
theorem zW_one_off (k : ℤ) (hk : ¬ (3 ∣ k)) : zW k 1 = 0 := by
  unfold zW delta3
  rw [if_neg hk, if_neg (by decide : ¬ (3 : ℤ) ∣ 1)]; ring
theorem zW_two_off (k : ℤ) (hk : ¬ (3 ∣ k)) : zW k 2 = 0 := by
  unfold zW delta3
  rw [if_neg hk, if_neg (by decide : ¬ (3 : ℤ) ∣ 2)]; ring

/-- `zW k 0 = 0` when `3 ∣ k` (so the `j=0` slice is supported on `{3∤k}`). -/
theorem zW_zero_off (k : ℤ) (hk : (3 : ℤ) ∣ k) : zW k 0 = 0 := by
  unfold zW delta3
  rw [if_pos hk, if_pos (Dvd.intro 0 rfl : (3 : ℤ) ∣ 0)]; ring
/-- `zW (3r+1) 0 = (-1)^r`. -/
theorem zW_three_one (r : ℤ) : zW (3 * r + 1) 0 = (-1 : ℚ) ^ r := by
  unfold zW delta3
  rw [if_neg (by omega : ¬ (3 : ℤ) ∣ (3 * r + 1)), if_pos (Dvd.intro 0 rfl : (3 : ℤ) ∣ 0)]
  rw [show (3 : ℤ) * r + 1 + 0 = (3 * r) + 1 by ring, zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0),
      negOne_zpow_three_mul]
  norm_num
/-- `zW (-(3r+1)) 0 = (-1)^r`. -/
theorem zW_neg_three_one (r : ℤ) : zW (-(3 * r + 1)) 0 = (-1 : ℚ) ^ r := by
  unfold zW delta3
  rw [if_neg (by omega : ¬ (3 : ℤ) ∣ -(3 * r + 1)), if_pos (Dvd.intro 0 rfl : (3 : ℤ) ∣ 0)]
  rw [show -(3 * r + 1) + 0 = (-(3 * r)) + (-1) by ring,
      zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0),
      show -(3 * r) = 3 * (-r) by ring, negOne_zpow_three_mul (-r), negOne_zpow_neg r]
  norm_num

/-- **Slice `L₀`** `[x⁰] zwegersLHS_x = single 1 2 · J(Q¹⁵;Q¹⁸)`  (the `ℤ⊕ℤ ≅ {3∤k}` bijection
`inl r ↦ 3r+1, inr r ↦ −(3r+1)`; both branches give `(3r+1)²` with sign `(-1)^r`). -/
theorem zwegersLHS_x_slice_zero :
    coeffXY zwegersLHS_x 0 0 = HahnSeries.single 1 (2 : ℚ) * JQ15 := by
  apply HahnSeries.ext; funext a
  rw [coeffXY_zwegersLHS_x_collapse]
  have hsm : (HahnSeries.single (1 : ℤ) (2 : ℚ) * JQ15).coeff a = 2 * JQ15.coeff (a - 1) := by
    rw [HahnSeries.coeff_single_mul]
  rw [hsm, JQ15, JK_coeff]
  set g : ℤ → ℚ := fun k => if k ^ 2 + 0 ^ 2 = a then zW k 0 else 0 with hg
  -- support of g ⊆ {k | k²=a}, which is finite (≤ 2 elements).
  have hgsub : Function.support g ⊆ {k : ℤ | k ^ 2 = a} := by
    intro k hk
    simp only [hg, Function.mem_support, ne_eq] at hk
    simp only [Set.mem_setOf_eq]
    by_contra h
    apply hk; rw [if_neg (by simpa using h)]
  have hsqfin : {k : ℤ | k ^ 2 = a}.Finite := by
    apply Set.Finite.subset (Set.finite_Icc (-(a^2+a+1)) (a^2+a+1))
    intro k hk; simp only [Set.mem_setOf_eq] at hk; simp only [Set.mem_Icc]
    constructor <;> nlinarith [sq_nonneg (k-1), sq_nonneg (k+1), hk, sq_nonneg k, sq_nonneg a]
  have hgfin : (Function.support g).Finite := hsqfin.subset hgsub
  -- {3∤k} = range(3r+1) ∪ range(3r+2), disjoint, and g vanishes off it.
  have hsupp3 : Function.support g ⊆ {k : ℤ | ¬ (3 : ℤ) ∣ k} := by
    intro k hk
    simp only [hg, Function.mem_support, ne_eq] at hk
    simp only [Set.mem_setOf_eq]
    intro hd
    apply hk
    by_cases h : k ^ 2 + 0 ^ 2 = a
    · rw [if_pos h, zW_zero_off k hd]
    · rw [if_neg h]
  have hcover : {k : ℤ | ¬ (3 : ℤ) ∣ k}
      = Set.range (fun r : ℤ => 3 * r + 1) ∪ Set.range (fun r : ℤ => 3 * r + 2) := by
    ext k; simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_range]
    constructor
    · intro hd
      have h3 : k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases h3 with h | h
      · exact Or.inl ⟨k / 3, by omega⟩
      · exact Or.inr ⟨k / 3, by omega⟩
    · rintro (⟨r, rfl⟩ | ⟨r, rfl⟩) <;> omega
  have hdisj : Disjoint (Set.range (fun r : ℤ => 3 * r + 1)) (Set.range (fun r : ℤ => 3 * r + 2)) := by
    rw [Set.disjoint_left]
    rintro k ⟨r, rfl⟩ ⟨s, hs⟩; simp only [] at hs; omega
  -- rewrite the finsum as a sum over {3∤k}, then split.
  rw [show (∑ᶠ k : ℤ, g k) = ∑ᶠ k ∈ {k : ℤ | ¬ (3 : ℤ) ∣ k}, g k by
    rw [← finsum_mem_inter_support, Set.inter_eq_right.mpr hsupp3,
        ← Set.univ_inter (Function.support g), finsum_mem_inter_support, finsum_mem_univ]]
  rw [hcover]
  rw [finsum_mem_union' hdisj
      (hgfin.subset (Set.inter_subset_right))
      (hgfin.subset (Set.inter_subset_right))]
  rw [finsum_mem_range (fun a b h => by simpa using h),
      finsum_mem_range (fun a b h => by simpa using h)]
  -- first branch: g(3r+1) = if (3r+1)²=a then (-1)^r
  have hbranch1 : (∑ᶠ r : ℤ, g (3 * r + 1)) = ∑ᶠ r : ℤ, (if thetaQDeg 18 15 r = a - 1 then (-1 : ℚ) ^ r else 0) := by
    apply finsum_congr; intro r
    simp only [hg]
    rw [show (3 * r + 1) ^ 2 + 0 ^ 2 = thetaQDeg 18 15 r + 1 by rw [thetaQDeg_18_15]; ring]
    by_cases h : thetaQDeg 18 15 r = a - 1
    · rw [if_pos (by omega), if_pos h, zW_three_one]
    · rw [if_neg (by omega), if_neg h]
  -- second branch: reindex r ↦ -1-r so that 3r+2 ↦ -(3·?+1); g(3r+2)=g(-(3(-1-r)+1))
  have hbranch2 : (∑ᶠ r : ℤ, g (3 * r + 2)) = ∑ᶠ r : ℤ, (if thetaQDeg 18 15 r = a - 1 then (-1 : ℚ) ^ r else 0) := by
    rw [← finsum_comp_equiv (Equiv.subLeft (-1 : ℤ))]
    apply finsum_congr; intro r
    simp only [hg, Equiv.subLeft_apply]
    rw [show 3 * (-1 - r) + 2 = -(3 * r + 1) by ring]
    rw [show (-(3 * r + 1)) ^ 2 + 0 ^ 2 = thetaQDeg 18 15 r + 1 by rw [thetaQDeg_18_15]; ring]
    by_cases h : thetaQDeg 18 15 r = a - 1
    · rw [if_pos (by omega), if_pos h, zW_neg_three_one]
    · rw [if_neg (by omega), if_neg h]
  rw [hbranch1, hbranch2]; ring

/-- **Slice `L₁`** `[x¹] zwegersLHS_x = single 1 (-1) · J(Q⁹;Q¹⁸)`  (`k=3r`,
`(3r)²+1 = 1 + 9r²`, sign `(-1)^{3r+1} = -(-1)^r`). -/
theorem zwegersLHS_x_slice_one :
    coeffXY zwegersLHS_x 1 0 = HahnSeries.single 1 (-1 : ℚ) * JQ9 := by
  apply HahnSeries.ext; funext a
  rw [coeffXY_zwegersLHS_x_collapse]
  have hsm : (HahnSeries.single (1 : ℤ) (-1 : ℚ) * JQ9).coeff a = - JQ9.coeff (a - 1) := by
    rw [HahnSeries.coeff_single_mul]; ring
  rw [hsm, JQ9, JK_coeff, ← finsum_neg_distrib]
  rw [finsum_multiples_three (fun k => if k ^ 2 + 1 ^ 2 = a then zW k 1 else 0)
      (fun k hk => by
        simp only
        by_cases h : k ^ 2 + 1 ^ 2 = a
        · rw [if_pos h, zW_one_off k hk]
        · rw [if_neg h])]
  apply finsum_congr; intro r
  have hz : zW (3 * r) 1 = - (-1 : ℚ) ^ r := by
    unfold zW delta3
    rw [if_pos (Dvd.intro r rfl : (3 : ℤ) ∣ 3 * r), if_neg (by decide : ¬ (3 : ℤ) ∣ 1)]
    rw [show (3 : ℤ) * r + 1 = (3 * r) + 1 by ring, zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0),
        negOne_zpow_three_mul]
    norm_num
  have hdeg : (3 * r) ^ 2 + 1 ^ 2 = thetaQDeg 18 9 r + 1 := by rw [thetaQDeg_18_9]; ring
  by_cases h : thetaQDeg 18 9 r = a - 1
  · rw [if_pos (by rw [hdeg]; omega), if_pos h, hz]
  · rw [if_neg (by rw [hdeg]; omega), if_neg h, neg_zero]

/-- **Slice `L₂`** `[x²] zwegersLHS_x = single 4 1 · J(Q⁹;Q¹⁸)`  (`k=3r`,
`(3r)²+4 = 4 + 9r²`, sign `(-1)^{3r+2} = (-1)^r`). -/
theorem zwegersLHS_x_slice_two :
    coeffXY zwegersLHS_x 2 0 = HahnSeries.single 4 (1 : ℚ) * JQ9 := by
  apply HahnSeries.ext; funext a
  rw [coeffXY_zwegersLHS_x_collapse]
  have hsm : (HahnSeries.single (4 : ℤ) (1 : ℚ) * JQ9).coeff a = JQ9.coeff (a - 4) := by
    rw [HahnSeries.coeff_single_mul]; ring
  rw [hsm, JQ9, JK_coeff]
  rw [finsum_multiples_three (fun k => if k ^ 2 + 2 ^ 2 = a then zW k 2 else 0)
      (fun k hk => by
        simp only
        by_cases h : k ^ 2 + 2 ^ 2 = a
        · rw [if_pos h, zW_two_off k hk]
        · rw [if_neg h])]
  apply finsum_congr; intro r
  have hz : zW (3 * r) 2 = (-1 : ℚ) ^ r := by
    unfold zW delta3
    rw [if_pos (Dvd.intro r rfl : (3 : ℤ) ∣ 3 * r), if_neg (by decide : ¬ (3 : ℤ) ∣ 2)]
    rw [show (3 : ℤ) * r + 2 = (3 * r) + 2 by ring, zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0),
        negOne_zpow_three_mul]
    norm_num
  have hdeg : (3 * r) ^ 2 + 2 ^ 2 = thetaQDeg 18 9 r + 4 := by rw [thetaQDeg_18_9]; ring
  by_cases h : thetaQDeg 18 9 r = a - 4
  · rw [if_pos (by rw [hdeg]; omega), if_pos h, hz]
  · rw [if_neg (by rw [hdeg]; omega), if_neg h]

/-- **Slice `C₁`** `[x¹] Θ(x;q²)Θ(x;q) = −J(−1;Q⁹)`  (`6Tn+3Tn(1−n)=9Tn n`, sign `(-1)¹`). -/
theorem thetaProdX_slice_one : coeffXY (thetaX_q2 * thetaX_q) 1 0 = - Jneg1 := by
  apply HahnSeries.ext; funext a
  rw [coeffXY_thetaProdX_collapse, HahnSeries.coeff_neg, Jneg1, JK_coeff]
  rw [← finsum_neg_distrib]
  apply finsum_congr; intro n
  rw [show 6 * Tn n + 3 * Tn (1 - n) = 9 * Tn n by rw [Tn_one_sub]; ring]
  rw [show thetaQDeg 9 0 n = 9 * Tn n by unfold thetaQDeg; ring]
  by_cases h : 9 * Tn n = a
  · rw [if_pos h, if_pos h]; norm_num
  · rw [if_neg h, if_neg h]; norm_num

/-- **Slice `C₂`** `[x²] Θ(x;q²)Θ(x;q) = J(−Q⁶;Q⁹)`  (reindex `n=r+1`, `9Tn r+6r=thetaQDeg 9 6 r`). -/
theorem thetaProdX_slice_two : coeffXY (thetaX_q2 * thetaX_q) 2 0 = JnegQ6 := by
  apply HahnSeries.ext; funext a
  rw [coeffXY_thetaProdX_collapse, JnegQ6, JK_coeff]
  rw [← finsum_comp_equiv (Equiv.addRight (1 : ℤ))]
  apply finsum_congr; intro r
  simp only [Equiv.coe_addRight]
  have hdeg : 6 * Tn (r + 1) + 3 * Tn (2 - (r + 1)) = thetaQDeg 9 6 r := by
    rw [Tn_add_one, show (2 : ℤ) - (r + 1) = 1 - r by ring, Tn_one_sub]
    unfold thetaQDeg; ring
  by_cases h : thetaQDeg 9 6 r = a
  · rw [if_pos (by rw [hdeg]; exact h), if_pos h]; norm_num
  · rw [if_neg (by rw [hdeg]; exact h), if_neg h]

/-- **Slice `C₃`** `[x³] Θ(x;q²)Θ(x;q) = single 3 (-1) · J(−Q⁶;Q⁹) = −q·J(−Q⁶;Q⁹)`
  (reindex `n=1−r`, `6Tn n+3Tn(3−n)=3+thetaQDeg 9 6 r`, sign `(-1)³`). -/
theorem thetaProdX_slice_three :
    coeffXY (thetaX_q2 * thetaX_q) 3 0 = HahnSeries.single 3 (-1 : ℚ) * JnegQ6 := by
  apply HahnSeries.ext; funext a
  rw [coeffXY_thetaProdX_collapse]
  have hsm : (HahnSeries.single (3 : ℤ) (-1 : ℚ) * JnegQ6).coeff a
        = - JnegQ6.coeff (a - 3) := by
    rw [HahnSeries.coeff_single_mul]; ring
  rw [hsm]
  rw [JnegQ6, JK_coeff, ← finsum_neg_distrib]
  rw [← finsum_comp_equiv (Equiv.subLeft (1 : ℤ))]
  apply finsum_congr; intro r
  simp only [Equiv.subLeft_apply]
  have hdeg : 6 * Tn (1 - r) + 3 * Tn (3 - (1 - r)) = thetaQDeg 9 6 r + 3 := by
    rw [Tn_one_sub, show (3 : ℤ) - (1 - r) = r + 2 by ring, Tn_add_two]
    unfold thetaQDeg; ring
  by_cases h : thetaQDeg 9 6 r = a - 3
  · rw [if_pos (by rw [hdeg]; omega), if_pos h]; norm_num
  · rw [if_neg (by rw [hdeg]; omega), if_neg h]; norm_num

/-! ### Layer F — K-level arithmetic-progression `q`-Pochhammer products

We transport the committed formal-power-series AP product `qPochAPPS ℚ r m = (X^r;X^m)_∞`
(`JTPFormalPSPentagonal`) into `K = ℚ((Q))` via the ring map `ofPSK` (`X ↦ Q`), obtaining the
infinite products `apK r m = (Q^r;Q^m)_∞` and (with the `(1+X^…)` factors) the signed variants.
The single-factor coefficient-stabilization lemma `coeff_mul_apFactorPS_eq_of_lt` (Pentagonal)
is the only analytic input; everything below is the AP-product *algebra* that, together with the
two Jacobi-triple-product product-forms (isolated as `JTP_*` below), reduces `P0`/`P12` to the
common mod-18 AP product.  Numerically verified (`/tmp/zwnum.py`). -/

open scoped PowerSeries.WithPiTopology
open QseriesFormalization.Pending.JTPFormalPSPentagonal (qPochAPPS apFactorPS
  hasProd_qPochAPPS multipliable_apFactorPS tendsto_qPochAPPS_partial coeff_mul_apFactorPS_eq_of_lt)

/-- `apK r m = (Q^r;Q^m)_∞ ∈ K`, the image under `ofPSK` of the formal AP product. -/
noncomputable def apK (r m : ℕ) : K := ofPSK (qPochAPPS ℚ r m)

/-- The partial product `∏_{n<N} (1 - X^{r+m n})` in `ℚ⟦X⟧`. -/
noncomputable def apPartialPS (r m N : ℕ) : PowerSeries ℚ :=
  ∏ n ∈ Finset.range N, apFactorPS ℚ r m n

/-- **Coefficient stabilization for a single AP product (over `ℚ⟦X⟧`).**  Multiplying the partial
product by the `N`-th factor `(1 - X^{r+mN})` does not change coefficients below `r+mN`. -/
theorem apPartialPS_coeff_stable (r m k N : ℕ) (hk : k < r + m * N) :
    PowerSeries.coeff k (apPartialPS r m (N + 1)) = PowerSeries.coeff k (apPartialPS r m N) := by
  rw [apPartialPS, apPartialPS, Finset.prod_range_succ]
  exact coeff_mul_apFactorPS_eq_of_lt ℚ (∏ n ∈ Finset.range N, apFactorPS ℚ r m n) k r m N hk

/-- The partial-product coefficient is eventually constant in `N` (for `N ≥ N₀` with
`k < r + m N₀`). -/
theorem apPartialPS_coeff_eq (r m k N M : ℕ) (hm : 0 < m) (hkN : k < r + m * N) (hNM : N ≤ M) :
    PowerSeries.coeff k (apPartialPS r m M) = PowerSeries.coeff k (apPartialPS r m N) := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M hNM ih =>
      rw [apPartialPS_coeff_stable r m k M (by nlinarith), ih]

/-- **The `apK` coefficient equals a finite partial-product coefficient.**  For any `k`, taking the
partial product up to index `N` with `r + m N > k` (e.g. `N = k+1` since `m ≥ 1`) computes the
coefficient.  This is the transport of `qPochAPPS = ∏'` to coefficient level. -/
theorem apK_coeff_nat (r m k : ℕ) (hm : 0 < m) :
    (apK r m).coeff (k : ℤ) = PowerSeries.coeff k (apPartialPS r m (k + 1)) := by
  unfold apK
  rw [ofPSK_coeff_nat]
  -- `qPochAPPS = ∏'`, and the coefficient is the limit of partial products, which stabilizes.
  have htend := tendsto_qPochAPPS_partial ℚ r m hm
  -- The coefficient map `PowerSeries.coeff k` is continuous for the X-adic / product topology.
  have hcoeff : Filter.Tendsto (fun N : ℕ => PowerSeries.coeff k (apPartialPS r m N))
      Filter.atTop (nhds (PowerSeries.coeff k (qPochAPPS ℚ r m))) := by
    have hc : Continuous (fun f : PowerSeries ℚ => PowerSeries.coeff k f) :=
      PowerSeries.WithPiTopology.continuous_coeff ℚ k
    exact (hc.tendsto _).comp htend
  -- The sequence is eventually constant equal to `coeff k (apPartialPS r m (k+1))`.
  have hconst : ∀ N ≥ k + 1, PowerSeries.coeff k (apPartialPS r m N)
      = PowerSeries.coeff k (apPartialPS r m (k + 1)) := by
    intro N hN
    exact apPartialPS_coeff_eq r m k (k + 1) N hm (by nlinarith) hN
  -- A tendsto sequence that is eventually constant `c` has limit `c`.
  have hlim : PowerSeries.coeff k (qPochAPPS ℚ r m)
      = PowerSeries.coeff k (apPartialPS r m (k + 1)) := by
    refine tendsto_nhds_unique hcoeff ?_
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop (k + 1)] with N hN
    exact (hconst N hN).symm
  rw [hlim]

/-- The `N`-th factor of the AP product `(X^d;X^d)` is the `expand d` image of `1 - X^{n+1}`. -/
theorem apFactorPS_dd_eq_expand (d n : ℕ) (hd : d ≠ 0) :
    apFactorPS ℚ d d n
      = PowerSeries.expand d hd (QseriesFormalization.PartIV.Ch19.oneSubXPow ℚ n) := by
  unfold apFactorPS QseriesFormalization.PartIV.Ch19.oneSubXPow
  rw [map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]
  congr 2
  ring

/-- The partial AP product `∏_{n<N}(1 - X^{d+dn})` is `expand d` of the finite `q`-Pochhammer. -/
theorem apPartialPS_dd_eq_expand (d N : ℕ) (hd : d ≠ 0) :
    apPartialPS d d N
      = PowerSeries.expand d hd (QseriesFormalization.PartIV.Ch19.qPochFinitePS ℚ N) := by
  unfold apPartialPS QseriesFormalization.PartIV.Ch19.qPochFinitePS
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro n _
  exact apFactorPS_dd_eq_expand d n hd

/-- **`poch`-to-`apK` bridge.**  `ofPSK (expand d (qPochInfPS ℚ)) = apK d d`, i.e. the
`q = Q^d`-rescaled `(q;q)_∞` is the genuine AP product `(Q^d;Q^d)_∞`. -/
theorem ofPSK_expand_qPochInfPS_eq_apK (d : ℕ) (hd : d ≠ 0) :
    ofPSK (PowerSeries.expand d hd (qPochInfPS ℚ)) = apK d d := by
  apply HahnSeries.ext
  funext m
  -- both supported on ℕ; for negative m both are 0.
  rcases lt_or_ge m 0 with hlt | hge
  · rw [ofPSK_coeff_neg _ m hlt]
    unfold apK; rw [ofPSK_coeff_neg _ m hlt]
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hge
    rw [ofPSK_coeff_nat, apK_coeff_nat d d k (Nat.pos_of_ne_zero hd),
        apPartialPS_dd_eq_expand d (k + 1) hd]
    -- Now both sides are `coeff k (expand d (·))`; reduce to qPochInfPS = qPochFinitePS coeff.
    by_cases hdk : d ∣ k
    · obtain ⟨t, rfl⟩ := hdk
      rw [PowerSeries.coeff_expand_mul (p := d) (hp := hd), PowerSeries.coeff_expand_mul (p := d) (hp := hd)]
      -- coeff t (qPochInfPS) = coeff t (qPochFinitePS (d*t+1)); t < d*t+1.
      have ht : t < d * t + 1 := by nlinarith [Nat.pos_of_ne_zero hd]
      rw [QseriesFormalization.PartIV.Ch19.coeff_qPochInfPS_eq_coeff_finite_product_of_lt ℚ t (d * t + 1) ht]
      rfl
    · rw [PowerSeries.coeff_expand (p := d) (hp := hd), PowerSeries.coeff_expand (p := d) (hp := hd),
          if_neg hdk, if_neg hdk]

/-- `poch_q = (Q³;Q³)_∞ = apK 3 3`. -/
theorem poch_q_eq_apK : poch_q = apK 3 3 := ofPSK_expand_qPochInfPS_eq_apK 3 (by norm_num)

/-- `poch_q2 = (Q⁶;Q⁶)_∞ = apK 6 6`. -/
theorem poch_q2_eq_apK : poch_q2 = apK 6 6 := ofPSK_expand_qPochInfPS_eq_apK 6 (by norm_num)

/-! ### Negative AP products `apKneg r m = (−Q^r;Q^m)_∞` and the sign-pairing

We mirror `apK` with the `(1 + X^{r+mn})` factors.  Multipliability is the same `order → ∞`
argument (sign-independent).  The single nontrivial fact is the **sign-pairing**
`(Q^k;Q^m)_∞ · (−Q^k;Q^m)_∞ = (Q^{2k};Q^{2m})_∞`, i.e. `apK k m · apKneg k m = apK (2k) (2m)`,
which is the factorwise `(1−X^j)(1+X^j) = 1−X^{2j}` lifted through `HasProd.mul`. -/

/-- The formal factor `1 + X^(r + m n)`. -/
noncomputable def apFactorNegPS (r m n : ℕ) : PowerSeries ℚ :=
  (1 : PowerSeries ℚ) + PowerSeries.X ^ (r + m * n)

/-- The formal negative AP product `(−Q^r;Q^m)_∞ = ∏_{n≥0} (1 + X^(r+mn))`. -/
noncomputable def qPochAPNegPS (r m : ℕ) : PowerSeries ℚ :=
  ∏' n : ℕ, apFactorNegPS r m n

/-- The negative AP product is multipliable when the step is positive (sign-independent
order → ∞ argument, mirroring `multipliable_apFactorPS`). -/
theorem multipliable_apFactorNegPS (r m : ℕ) (hm : 0 < m) :
    Multipliable fun n : ℕ => apFactorNegPS r m n := by
  simp_rw [apFactorNegPS]
  apply PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun k =>
    Filter.eventually_atTop.mpr ⟨k + 1, ?_⟩
  intro n hn
  rw [PowerSeries.order_X_pow]
  norm_cast
  have hm1 : 1 ≤ m := Nat.succ_le_iff.mpr hm
  calc
    k < n := by omega
    _ ≤ m * n := Nat.le_mul_of_pos_left n hm1
    _ ≤ r + m * n := Nat.le_add_left _ _

/-- HasProd form of `qPochAPNegPS`. -/
theorem hasProd_qPochAPNegPS (r m : ℕ) (hm : 0 < m) :
    HasProd (fun n : ℕ => apFactorNegPS r m n) (qPochAPNegPS r m) :=
  (multipliable_apFactorNegPS r m hm).hasProd

/-- `apKneg r m = (−Q^r;Q^m)_∞ ∈ K`, the image under `ofPSK` of the formal negative AP product. -/
noncomputable def apKneg (r m : ℕ) : K := ofPSK (qPochAPNegPS r m)

/-- **Factorwise sign-pairing.**  `(1 − X^{r+mn})(1 + X^{r+mn}) = 1 − X^{2(r+mn)} = 1 − X^{2r + 2m·n}`,
i.e. the positive and negative AP factors pair to a double-step positive factor. -/
theorem apFactorPS_mul_apFactorNegPS (r m n : ℕ) :
    apFactorPS ℚ r m n * apFactorNegPS r m n = apFactorPS ℚ (2 * r) (2 * m) n := by
  show ((1 : PowerSeries ℚ) - PowerSeries.X ^ (r + m * n)) * apFactorNegPS r m n
      = (1 : PowerSeries ℚ) - PowerSeries.X ^ (2 * r + 2 * m * n)
  rw [apFactorNegPS, show 2 * r + 2 * m * n = 2 * (r + m * n) by ring, pow_mul]
  ring

/-- **The sign-pairing (formal-PS level).**  `(Q^r;Q^m)_∞ · (−Q^r;Q^m)_∞ = (Q^{2r};Q^{2m})_∞`. -/
theorem qPochAPPS_mul_qPochAPNegPS (r m : ℕ) (hm : 0 < m) :
    qPochAPPS ℚ r m * qPochAPNegPS r m = qPochAPPS ℚ (2 * r) (2 * m) := by
  have hpos := hasProd_qPochAPPS ℚ r m hm
  have hneg := hasProd_qPochAPNegPS r m hm
  have hmul : HasProd (fun n : ℕ => apFactorPS ℚ r m n * apFactorNegPS r m n)
      (qPochAPPS ℚ r m * qPochAPNegPS r m) := hpos.mul hneg
  have hdbl : HasProd (fun n : ℕ => apFactorPS ℚ (2 * r) (2 * m) n)
      (qPochAPPS ℚ (2 * r) (2 * m)) := hasProd_qPochAPPS ℚ (2 * r) (2 * m) (by omega)
  have hfun : (fun n : ℕ => apFactorPS ℚ r m n * apFactorNegPS r m n)
      = (fun n : ℕ => apFactorPS ℚ (2 * r) (2 * m) n) := by
    funext n
    exact apFactorPS_mul_apFactorNegPS r m n
  rw [hfun] at hmul
  exact hmul.unique hdbl

/-- **The sign-pairing (`K`-level).**  `apK r m · apKneg r m = apK (2r) (2m)`. -/
theorem apK_mul_apKneg (r m : ℕ) (hm : 0 < m) :
    apK r m * apKneg r m = apK (2 * r) (2 * m) := by
  unfold apK apKneg
  rw [← map_mul, qPochAPPS_mul_qPochAPNegPS r m hm]

/-! ### The two product identities `P0`/`P12` (JTP + mod-18 AP splitting)

Both `(P0)` and `(P12)` reduce, by the Jacobi triple product and the AP-product pairing
`(q;q³)(−q;q³)=(q²;q⁶)` etc., to the *same* mod-18 arithmetic-progression product.  See the design
doc §"The two product identities".  Numerically verified (`/tmp/zwnum.py`) to high order. -/

/-! #### Bridges to the HM Laurent layer (`jLaurent`, `qPochAPLaurent`)

`K = HahnSeries ℤ ℚ = QLaurent` definitionally, so the HM objects live in `K`.  We bridge the
alternating thetas `JQ15`, `JQ9` to `jLaurent` (HM's coefficient-defined alternating theta), and
`apK` is literally `qPochAPLaurent`. -/

section HMBridge
open QseriesFormalization.Pending.Ch10HM

/-- `apK r m` is literally `qPochAPLaurent r m` (both = `ofPSK (qPochAPPS …)`). -/
theorem apK_eq_qPochAPLaurent (r m : ℕ) : apK r m = qPochAPLaurent r m := rfl

/-- Exponent match: `thetaQDeg b a r = jExp a b r` (TwoVar uses `b·Tn r + a·r`, HM uses
`b·r·(r-1)/2 + a·r`; they agree since `2 ∣ r·(r-1)`). -/
theorem thetaQDeg_eq_jExp (a b r : ℤ) : thetaQDeg b a r = jExp a b r := by
  unfold thetaQDeg jExp Tn
  have hdvd : (2 : ℤ) ∣ r * (r - 1) := by
    rcases Int.even_or_odd r with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact Dvd.intro (k * (r - 1)) (by rw [hk]; ring)
    · exact Dvd.intro (r * k) (by rw [hk]; ring)
  rw [show b * (r * (r - 1) / 2) = b * (r * (r - 1)) / 2 by
        rw [Int.mul_ediv_assoc b hdvd]]
  rw [show b * r * (r - 1) = b * (r * (r - 1)) by ring]

/-- Sign match: the TwoVar `(-1)^r` (in `ℚ`, `r : ℤ` via `zpow`-style) equals HM's
`negOnePowIntQ r`.  In `JQ15`/`JQ9` the weight is `fun r => (-1) ^ r` with `r : ℤ`; but `(-1 : ℚ)`
is a unit so `(-1)^r` is `zpow`.  We only ever evaluate at the integers, and `negOnePowIntQ r =
(-1)^|r|` agrees with `(-1)^r` by parity. -/
theorem negOnePow_int_eq_negOnePowIntQ (r : ℤ) :
    ((-1 : ℚ) ^ r) = negOnePowIntQ r := by
  rw [negOnePowIntQ_eq_negOnePow]
  rcases Int.even_or_odd r with hr | hr
  · obtain ⟨k, rfl⟩ := hr
    rw [Int.negOnePow_even _ ⟨k, by ring⟩]
    rw [show k + k = 2 * k by ring, zpow_mul]
    norm_num
  · obtain ⟨k, rfl⟩ := hr
    rw [Int.negOnePow_odd _ ⟨k, rfl⟩]
    rw [zpow_add₀ (by norm_num), zpow_mul]
    norm_num

/-- **Alternating-theta bridge.**  For `0 < a < b`, the TwoVar alternating theta
`JK b a (fun r => (-1)^r)` equals HM's coefficient-defined `jLaurent a b`. -/
theorem JK_eq_jLaurent (a b : ℤ) (ha : 0 < a) (hab : a < b) (hb : 0 < b) :
    JK b a hb (fun r => (-1) ^ r) = jLaurent a b := by
  apply HahnSeries.ext
  funext m
  rw [JK_coeff]
  change _ = lcoeff (jLaurent a b) m
  rw [coeff_jLaurent, jCoeff_eq_window_sum a b m hb]
  -- Rewrite each summand of the `JK` finsum into HM's indicator form.
  have hsummand : ∀ r : ℤ,
      (if thetaQDeg b a r = m then ((-1 : ℚ)) ^ r else 0)
        = (if jExp a b r = m then negOnePowIntQ r else 0) := by
    intro r
    rw [thetaQDeg_eq_jExp, negOnePow_int_eq_negOnePowIntQ]
  simp_rw [hsummand]
  -- The finsum over ℤ collapses to the window finset sum (support ⊆ window).
  apply finsum_eq_sum_of_support_subset
  intro r hr
  simp only [Function.mem_support, ne_eq] at hr
  rw [Finset.coe_Icc, Set.mem_Icc]
  by_cases hroot : jExp a b r = m
  · constructor
    · have := jExp_root_le_window_left a b m r hb hroot; omega
    · have := jExp_root_le_window_right a b m r hb hroot; omega
  · exact absurd (by simp [hroot]) hr

theorem JQ15_eq_jLaurent : JQ15 = jLaurent 15 18 :=
  JK_eq_jLaurent 15 18 (by norm_num) (by norm_num) (by norm_num)

theorem JQ9_eq_jLaurent : JQ9 = jLaurent 9 18 :=
  JK_eq_jLaurent 9 18 (by norm_num) (by norm_num) (by norm_num)

end HMBridge

/-! #### RHS product forms and AP refinements (free from the HM Laurent layer)

The alternating thetas `JQ15`/`JQ9` factor by the (positive) Jacobi triple product
`jLaurent_eq_tripleProductInf`, and the pochhammers `poch_q = apK 3 3`, `poch_q2 = apK 6 6`
refine into mod-18 APs by `qPochAPLaurent_refine_mul`.  These are the RHS-side ingredients
of `P0`/`P12`; all are transported verbatim from the committed HM layer. -/

section RHSForms
open QseriesFormalization.Pending.Ch10HM

/-- `JQ15 = J(Q¹⁵;Q¹⁸)` as a triple product `(Q¹⁸;Q¹⁸)(Q¹⁵;Q¹⁸)(Q³;Q¹⁸)`. -/
theorem JQ15_prod : JQ15 = apK 18 18 * apK 15 18 * apK 3 18 := by
  rw [JQ15_eq_jLaurent, jLaurent_eq_tripleProductInf 15 18 (by norm_num) (by norm_num)]
  norm_num
  rfl

/-- `JQ9 = J(Q⁹;Q¹⁸)` as a triple product `(Q¹⁸;Q¹⁸)(Q⁹;Q¹⁸)(Q⁹;Q¹⁸)`. -/
theorem JQ9_prod : JQ9 = apK 18 18 * apK 9 18 * apK 9 18 := by
  rw [JQ9_eq_jLaurent, jLaurent_eq_tripleProductInf 9 18 (by norm_num) (by norm_num)]
  norm_num
  rfl

/-- `apK 3 3 = (Q³;Q¹⁸)(Q⁶;Q¹⁸)(Q⁹;Q¹⁸)(Q¹²;Q¹⁸)(Q¹⁵;Q¹⁸)(Q¹⁸;Q¹⁸)` (mod-18 refinement, `k=6`). -/
theorem apK_3_3_refine : apK 3 3
    = apK 3 18 * apK 6 18 * apK 9 18 * apK 12 18 * apK 15 18 * apK 18 18 := by
  simp only [apK_eq_qPochAPLaurent]
  rw [qPochAPLaurent_refine_mul 3 3 6 (by norm_num) (by norm_num), Fin.prod_univ_six]
  norm_num

/-- `apK 6 6 = (Q⁶;Q¹⁸)(Q¹²;Q¹⁸)(Q¹⁸;Q¹⁸)` (mod-18 refinement, `k=3`). -/
theorem apK_6_6_refine : apK 6 6 = apK 6 18 * apK 12 18 * apK 18 18 := by
  simp only [apK_eq_qPochAPLaurent]
  rw [qPochAPLaurent_refine_mul 6 6 3 (by norm_num) (by norm_num), Fin.prod_univ_three]
  norm_num

/-- `apK 9 9 = (Q⁹;Q¹⁸)(Q¹⁸;Q¹⁸)` (mod-18 refinement, `k=2`). -/
theorem apK_9_9_refine : apK 9 9 = apK 9 18 * apK 18 18 := by
  simp only [apK_eq_qPochAPLaurent]
  rw [qPochAPLaurent_refine_mul 9 9 2 (by norm_num) (by norm_num), Fin.prod_univ_two]
  norm_num

/-- The constant coefficient of an AP product `apK r m` is `1` (for `0 < r`): the only factor
contributing below degree `r` is the constant `1`. -/
theorem apK_coeff_zero (r m : ℕ) (hr : 0 < r) (hm : 0 < m) : (apK r m).coeff 0 = 1 := by
  have h := apK_coeff_nat r m 0 hm
  rw [Nat.cast_zero] at h
  rw [h, apPartialPS, Finset.prod_range_one]
  show PowerSeries.coeff 0 ((1 : PowerSeries ℚ) - PowerSeries.X ^ (r + m * 0)) = 1
  have hr0 : (0 : ℕ) ≠ r + m * 0 := by omega
  rw [LinearMap.map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow, if_neg hr0]
  norm_num

/-- `apK r m ≠ 0` for `0 < r` (its constant coefficient is `1`). -/
theorem apK_ne_zero (r m : ℕ) (hr : 0 < r) (hm : 0 < m) : apK r m ≠ 0 := by
  intro h
  have := apK_coeff_zero r m hr hm
  rw [h] at this
  simp at this

/-! #### Mod-18 refinements of the level-9 AP products (for the `P12` clearing). -/

/-- `apK 3 9 = (Q³;Q¹⁸)(Q¹²;Q¹⁸)` (mod-18 refinement, `k=2`). -/
theorem apK_3_9_refine : apK 3 9 = apK 3 18 * apK 12 18 := by
  simp only [apK_eq_qPochAPLaurent]
  rw [qPochAPLaurent_refine_mul 3 9 2 (by norm_num) (by norm_num), Fin.prod_univ_two]
  norm_num

/-- `apK 6 9 = (Q⁶;Q¹⁸)(Q¹⁵;Q¹⁸)` (mod-18 refinement, `k=2`). -/
theorem apK_6_9_refine : apK 6 9 = apK 6 18 * apK 15 18 := by
  simp only [apK_eq_qPochAPLaurent]
  rw [qPochAPLaurent_refine_mul 6 9 2 (by norm_num) (by norm_num), Fin.prod_univ_two]
  norm_num

end RHSForms

/-! ### The two negative Jacobi triple product *product forms* (genuine analytic input)

These are the sole remaining analytic facts: the bilateral all-`+1`-weight theta
`J(−z;q) = ∑_r z^r q^{T r}` equals the Jacobi-triple-product
`(q;q)_∞ (−z;q)_∞ (−q/z;q)_∞`, instantiated at `(z,q) = (1,Q⁹)` and `(Q⁶,Q⁹)`:

  `Jneg1  = 2·(−Q⁹;Q⁹)_∞²·(Q⁹;Q⁹)_∞ = 2·apKneg 9 9·apKneg 9 9·apK 9 9`,
  `JnegQ6 = (−Q³;Q⁹)_∞·(−Q⁶;Q⁹)_∞·(Q⁹;Q⁹)_∞ = apKneg 3 9·apKneg 6 9·apK 9 9`.

(The factor `2` for `Jneg1` is the `z=1` degeneracy: the `r ↦ 1−r` symmetry of the
exponent `9·T(r)` doubles the constant term.)  Both are the negative-`z`
(`z ↦ −Qpow a`) instance of HM's `jLaurent_eq_tripleProductInf` chain; numerically
verified to `Q^400`. -/

section NegJTPChain
open QseriesFormalization.Pending.Ch10HM

/-! #### The negative-`z` Jacobi triple product chain (`0 < a < b`)

We mirror HM's positive chain (`jLaurent_eq_tripleProductInf`) but instantiate Chan's finite
JTP at `z = −Qpow a`.  Then `(−z)^l = (Qpow a)^l = Qpow(a·l)`, so the alternating `(-1)^l`
weight disappears and the RHS becomes the **all-`+1`** theta `∑_r Q^{b·T(r)+a·r}`.  The product
factors `(z;q)_N (z⁻¹q;q)_N` become the `apKneg` partials `(−Q^a;Q^b)_N (−Q^{b-a};Q^b)_N`.
All product-side / Gaussian-binomial / window machinery is sign-independent and reused verbatim
from HM; only the term-weight changes from `negOnePowIntQ` to `1`. -/

/-- Cutoff lemma for the negative factor: `(P·(1+X^{r+mN})).coeff k = P.coeff k` for `k < r+mN`. -/
theorem coeff_mul_apFactorNegPS_eq_of_lt (P : PowerSeries ℚ) (k r m N : ℕ)
    (hk : k < r + m * N) :
    (P * apFactorNegPS r m N).coeff k = P.coeff k := by
  rw [apFactorNegPS, mul_add, mul_one, map_add, PowerSeries.coeff_mul_X_pow']
  simp [Nat.not_le_of_gt hk]

/-- The negative finite `q`-Pochhammer `(−Q^r;Q^m)_N` as `ofPSK` of the formal product. -/
theorem qPochNeg_Qpow_eq_ofPSK_apFiniteNegPS (r m N : ℕ) :
    qPoch (-(Qpow (r : ℤ))) (Qpow (m : ℤ)) N =
      ofPSK (∏ n ∈ Finset.range N, apFactorNegPS r m n) := by
  induction N with
  | zero => simp [qPoch]
  | succ N ih =>
      rw [qPoch_succ, ih, Finset.prod_range_succ, map_mul]
      congr 1
      have hXpow : ofPSK (PowerSeries.X ^ (r + m * N)) = Qpow ((r + m * N : ℕ) : ℤ) := by
        unfold ofPSK Qpow
        rw [map_pow, HahnSeries.ofPowerSeries_X, HahnSeries.single_pow]
        congr 1 <;> simp
      rw [apFactorNegPS, map_add, map_one, hXpow]
      rw [show -(Qpow (r : ℤ)) * Qpow (m : ℤ) ^ N = -(Qpow (r : ℤ) * Qpow (m : ℤ) ^ N) by ring,
        Qpow_pow_nat, Qpow_mul]
      rw [show (1 : K) - -(Qpow ((r : ℤ) + (m : ℤ) * (N : ℤ)))
            = 1 + Qpow ((r : ℤ) + (m : ℤ) * (N : ℤ)) by ring]
      have hc : ((r + m * N : ℕ) : ℤ) = (r : ℤ) + (m : ℤ) * (N : ℤ) := by push_cast; ring
      rw [hc]

/-- Chan's finite-JTP summand at `z = −Qpow a` is the Gaussian-weighted **all-`+1`** theta term
`[2N,k]_{Q^b}·Q^{jExp a b (k−N)}` (no `(-1)` weight). -/
theorem negJTPSummand_Qpow (a b : ℤ) (N k : ℕ) :
    QseriesFormalization.PartI.Ch03.finiteJTPSummand (Qpow b) (-(Qpow a)) N k =
      gaussianBinom (Qpow b) (2 * N) k * Qpow (jExp a b ((k : ℤ) - (N : ℤ))) := by
  unfold QseriesFormalization.PartI.Ch03.finiteJTPSummand
  set l : ℤ := (k : ℤ) - (N : ℤ) with hl
  have hl_nonneg : 0 ≤ l * (l - 1) / 2 := by
    apply Int.ediv_nonneg _ (by omega)
    nlinarith [sq_nonneg (2 * l - 1)]
  have hto : (((l * (l - 1) / 2).toNat : ℕ) : ℤ) = l * (l - 1) / 2 :=
    Int.toNat_of_nonneg hl_nonneg
  have hnegneg : (-(-(Qpow a))) ^ l = Qpow (a * l) := by
    rw [neg_neg, Qpow_zpow]
  change gaussianBinom (Qpow b) (2 * N) k * (Qpow b) ^ ((l * (l - 1) / 2).toNat)
      * (-(-(Qpow a))) ^ l = _
  rw [hnegneg, Qpow_pow_nat]
  rw [show b * ↑((l * (l - 1) / 2).toNat) = b * (l * (l - 1) / 2) by rw [hto]]
  have hexp : b * (l * (l - 1) / 2) + a * l = jExp a b l := by
    unfold jExp
    have hdvd : (2 : ℤ) ∣ l * (l - 1) := by
      rcases Int.even_or_odd l with ⟨m, hm⟩ | ⟨m, hm⟩
      · exact ⟨m * (l - 1), by rw [hm]; ring⟩
      · exact ⟨l * m, by rw [hm]; ring⟩
    rw [show b * l * (l - 1) = b * (l * (l - 1)) by ring, Int.mul_ediv_assoc b hdvd]
  rw [mul_assoc, Qpow_mul, hexp]

/-- The finite negative-product partial as a Gaussian-weighted finite all-`+1` theta sum. -/
theorem negFiniteJTPRHS_Qpow_eq_natSum (a b : ℤ) (N : ℕ) :
    QseriesFormalization.PartI.Ch03.finiteJTPRHS (Qpow b) (-(Qpow a)) N =
      QseriesFormalization.natSum (fun k =>
        gaussianBinom (Qpow b) (2 * N) k *
          Qpow (jExp a b ((k : ℤ) - (N : ℤ)))) (2 * N) := by
  unfold QseriesFormalization.PartI.Ch03.finiteJTPRHS
  exact QseriesFormalization.PartI.Ch03.natSum_congr_le (2 * N)
    (fun k _ => negJTPSummand_Qpow a b N k)

/-- The negative finite product `(−Q^a;Q^b)_N (−Q^{b-a};Q^b)_N = finiteJTPRHS (Q^b) (−Q^a) N`. -/
theorem negFiniteProduct_eq_finiteJTPRHS (a b : ℤ) (N : ℕ) :
    qPoch (-(Qpow a)) (Qpow b) N * qPoch (-(Qpow (b - a))) (Qpow b) N =
      QseriesFormalization.PartI.Ch03.finiteJTPRHS (Qpow b) (-(Qpow a)) N := by
  have h := QseriesFormalization.PartI.Ch03.finite_jacobi_triple_product (Qpow b) (-(Qpow a))
    (neg_ne_zero.mpr (Qpow_ne_zero a)) (Qpow_ne_zero b) N
  have hinv : (-(Qpow a))⁻¹ * Qpow b = -(Qpow (b - a)) := by
    rw [show (-(Qpow a))⁻¹ = -(Qpow a)⁻¹ from inv_neg, Qpow_inv, neg_mul, Qpow_mul]
    congr 2; ring
  rwa [hinv] at h

/-! ##### Bridge: my `Qpow`/`.coeff` are defeq to HM's `Qpow`/`lcoeff`. -/

theorem Qpow_eq_hm (m : ℤ) : Qpow m = QseriesFormalization.Pending.Ch10HM.Qpow m := rfl
theorem coeff_eq_lcoeff (s : K) (e : ℤ) : s.coeff e = lcoeff s e := rfl

/-! ##### The negative triple-product partial and its coefficient (heart of the chain). -/

/-- The finite negative triple-product partial `(Q^b;Q^b)_N (−Q^a;Q^b)_N (−Q^{b-a};Q^b)_N`. -/
noncomputable def jNegProductPartial (a b : ℤ) (N : ℕ) : K :=
  qPochhammer (Qpow b) N * (qPoch (-(Qpow a)) (Qpow b) N * qPoch (-(Qpow (b - a))) (Qpow b) N)

/-- Public version of HM's (private) degree bound, for `0 < A < B`:
if `|n| = r ≤ d+1` then `d − jExp A B n < B·(d+1−r+1)`.  Proof via the public `abs_le_jExp_of_pos_lt`. -/
theorem degree_sub_lt_center_start_pos (A B d r : ℕ) (hA : 0 < A) (hAB : A < B) (hr : r ≤ d + 1)
    (n : ℤ) (hnabs : |n| = (r : ℤ)) :
    (d : ℤ) - jExp (A : ℤ) (B : ℤ) n < (B * (d + 1 - r + 1) : ℕ) := by
  have hB1 : 1 ≤ B := by omega
  have hstart_ge : d + 1 - r + 1 ≤ B * (d + 1 - r + 1) := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right (d + 1 - r + 1) hB1
  have hexp_ge : (r : ℤ) ≤ jExp (A : ℤ) (B : ℤ) n := by
    rw [← hnabs]; exact abs_le_jExp_of_pos_lt (A : ℤ) (B : ℤ) n (by omega) (by omega)
  have hcast : ((B * (d + 1 - r + 1) : ℕ) : ℤ) = (B : ℤ) * ((d : ℤ) + 2 - (r : ℤ)) := by
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_sub (by omega : r ≤ d + 1)]
    push_cast; ring
  rw [hcast]
  have hrle : (r : ℤ) ≤ (d : ℤ) + 1 := by exact_mod_cast hr
  nlinarith [hexp_ge, hrle, hB1,
    mul_nonneg (by omega : (0:ℤ) ≤ B - 1) (by omega : (0:ℤ) ≤ (d:ℤ) + 1 - (r:ℤ))]

/-- All-`+1` heart lemma, center-add branch (`k = (d+1)+r`, `n = +r`). -/
theorem lcoeff_center_add_mul_Qpow_jExp_eq
    (A B d r : ℕ) (hA : 0 < A) (hAB : A < B) (hr : r ≤ d + 1) :
    lcoeff
        ((qPochhammer (QseriesFormalization.Pending.Ch10HM.Qpow (B : ℤ)) (d + 1) *
            gaussianBinom (QseriesFormalization.Pending.Ch10HM.Qpow (B : ℤ)) (2 * (d + 1)) ((d + 1) + r)) *
          Qpow (jExp (A : ℤ) (B : ℤ) (r : ℤ)))
        (d : ℤ) =
      if jExp (A : ℤ) (B : ℤ) (r : ℤ) = (d : ℤ) then 1 else 0 := by
  rw [Qpow_eq_hm, mul_comm, lcoeff_Qpow_mul]
  have hlow := degree_sub_lt_center_start_pos A B d r hA hAB hr (r : ℤ) (by
    rw [abs_of_nonneg]; exact Int.natCast_nonneg r)
  have hcorr := lcoeff_qPochhammer_mul_gaussian_center_add_low_int
    B (d + 1) r (by omega : 0 < B) hr
    ((d : ℤ) - jExp (A : ℤ) (B : ℤ) (r : ℤ)) hlow
  rw [hcorr]
  by_cases heq : jExp (A : ℤ) (B : ℤ) (r : ℤ) = (d : ℤ)
  · simp [heq]
  · have htne : (d : ℤ) - jExp (A : ℤ) (B : ℤ) (r : ℤ) ≠ 0 := by omega
    simp [heq, htne]

/-- All-`+1` heart lemma, center-sub branch (`k = (d+1)−r`, `n = −r`). -/
theorem lcoeff_center_sub_mul_Qpow_jExp_eq
    (A B d r : ℕ) (hA : 0 < A) (hAB : A < B) (hr : r ≤ d + 1) :
    lcoeff
        ((qPochhammer (QseriesFormalization.Pending.Ch10HM.Qpow (B : ℤ)) (d + 1) *
            gaussianBinom (QseriesFormalization.Pending.Ch10HM.Qpow (B : ℤ)) (2 * (d + 1)) ((d + 1) - r)) *
          Qpow (jExp (A : ℤ) (B : ℤ) (-(r : ℤ))))
        (d : ℤ) =
      if jExp (A : ℤ) (B : ℤ) (-(r : ℤ)) = (d : ℤ) then 1 else 0 := by
  rw [Qpow_eq_hm, mul_comm, lcoeff_Qpow_mul]
  have hlow := degree_sub_lt_center_start_pos A B d r hA hAB hr (-(r : ℤ)) (by
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

/-- The all-`+1` theta coefficient at `d` as a finite window sum (`0 < A < B`). -/
theorem JK_one_coeff_eq_sum_Icc_succ
    (A B d : ℕ) (hA : 0 < A) (hAB : A < B) :
    (JK (B : ℤ) (A : ℤ) (by omega) (fun _ => 1)).coeff (d : ℤ) =
      ∑ n ∈ Finset.Icc (-(d + 1 : ℤ)) (d + 1 : ℤ),
        if jExp (A : ℤ) (B : ℤ) n = (d : ℤ) then (1 : ℚ) else 0 := by
  rw [JK_coeff]
  have hsummand : ∀ n : ℤ,
      (if thetaQDeg (B : ℤ) (A : ℤ) n = (d : ℤ) then (1 : ℚ) else 0)
        = (if jExp (A : ℤ) (B : ℤ) n = (d : ℤ) then (1 : ℚ) else 0) := by
    intro n; rw [thetaQDeg_eq_jExp]
  simp_rw [hsummand]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc (-(d + 1 : ℤ)) (d + 1 : ℤ))]
  intro n hn
  simp only [Function.mem_support, ne_eq] at hn
  rw [Finset.coe_Icc, Set.mem_Icc]
  by_cases hroot : jExp (A : ℤ) (B : ℤ) n = (d : ℤ)
  · have habs := abs_le_jExp_of_pos_lt (A : ℤ) (B : ℤ) n (by omega) (by omega)
    rw [hroot] at habs
    have hn_le : n ≤ (d : ℤ) := le_trans (le_abs_self n) habs
    have hneg_le : -(d : ℤ) ≤ n := by have := neg_abs_le n; omega
    constructor <;> omega
  · exact absurd (by simp [hroot]) hn

/-- **Heart of the chain.**  The coefficient of the `(d+1)`-partial negative product at `d`
equals the all-`+1` theta coefficient at `d`. -/
theorem lcoeff_jNegProductPartial_eq_thetaCoeff
    (A B d : ℕ) (hA : 0 < A) (hAB : A < B) :
    (jNegProductPartial (A : ℤ) (B : ℤ) (d + 1)).coeff (d : ℤ) =
      (JK (B : ℤ) (A : ℤ) (by omega) (fun _ => 1)).coeff (d : ℤ) := by
  rw [JK_one_coeff_eq_sum_Icc_succ A B d hA hAB]
  have hsum :
      (jNegProductPartial (A : ℤ) (B : ℤ) (d + 1)).coeff (d : ℤ) =
        ∑ k ∈ Finset.range (2 * (d + 1) + 1),
          lcoeff
            (qPochhammer (Qpow (B : ℤ)) (d + 1) *
              (gaussianBinom (Qpow (B : ℤ)) (2 * (d + 1)) k *
                Qpow (jExp (A : ℤ) (B : ℤ) ((k : ℤ) - ((d + 1 : ℕ) : ℤ))))) (d : ℤ) := by
    unfold jNegProductPartial
    rw [negFiniteProduct_eq_finiteJTPRHS, negFiniteJTPRHS_Qpow_eq_natSum]
    rw [QseriesFormalization.PartI.Ch03.natSum_eq_sum_range]
    simp only [Finset.mul_sum]
    simp [lcoeff]
  rw [hsum]
  have hterms :
      (∑ k ∈ Finset.range (2 * (d + 1) + 1),
          lcoeff
            (qPochhammer (Qpow (B : ℤ)) (d + 1) *
              (gaussianBinom (Qpow (B : ℤ)) (2 * (d + 1)) k *
                Qpow (jExp (A : ℤ) (B : ℤ) ((k : ℤ) - ((d + 1 : ℕ) : ℤ))))) (d : ℤ)) =
        ∑ k ∈ Finset.range (2 * (d + 1) + 1),
          if jExp (A : ℤ) (B : ℤ) ((k : ℤ) - ((d + 1 : ℕ) : ℤ)) = (d : ℤ) then (1 : ℚ) else 0 := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [Finset.mem_range] at hk
    by_cases hNk : d + 1 ≤ k
    · let r : ℕ := k - (d + 1)
      have hr : r ≤ d + 1 := by dsimp [r]; omega
      have hk_eq : k = (d + 1) + r := by dsimp [r]; omega
      have hn_eq : (k : ℤ) - ((d + 1 : ℕ) : ℤ) = (r : ℤ) := by dsimp [r]; omega
      rw [hn_eq, hk_eq]
      rw [show qPochhammer (Qpow (B : ℤ)) (d + 1) *
          (gaussianBinom (Qpow (B : ℤ)) (2 * (d + 1)) ((d + 1) + r) *
            Qpow (jExp (A : ℤ) (B : ℤ) (r : ℤ))) =
          (qPochhammer (Qpow (B : ℤ)) (d + 1) *
            gaussianBinom (Qpow (B : ℤ)) (2 * (d + 1)) ((d + 1) + r)) *
              Qpow (jExp (A : ℤ) (B : ℤ) (r : ℤ)) by ring]
      exact lcoeff_center_add_mul_Qpow_jExp_eq A B d r hA hAB hr
    · let r : ℕ := (d + 1) - k
      have hr : r ≤ d + 1 := by dsimp [r]; omega
      have hk_eq : k = (d + 1) - r := by dsimp [r]; omega
      have hn_eq : (k : ℤ) - ((d + 1 : ℕ) : ℤ) = -(r : ℤ) := by dsimp [r]; omega
      rw [hn_eq, hk_eq]
      rw [show qPochhammer (Qpow (B : ℤ)) (d + 1) *
          (gaussianBinom (Qpow (B : ℤ)) (2 * (d + 1)) ((d + 1) - r) *
            Qpow (jExp (A : ℤ) (B : ℤ) (-(r : ℤ)))) =
          (qPochhammer (Qpow (B : ℤ)) (d + 1) *
            gaussianBinom (Qpow (B : ℤ)) (2 * (d + 1)) ((d + 1) - r)) *
              Qpow (jExp (A : ℤ) (B : ℤ) (-(r : ℤ))) by ring]
      exact lcoeff_center_sub_mul_Qpow_jExp_eq A B d r hA hAB hr
  rw [hterms]
  rw [sum_range_center_eq_sum_Icc
    (fun n : ℤ => if jExp (A : ℤ) (B : ℤ) n = (d : ℤ) then (1 : ℚ) else 0) (d + 1)]
  have hbnd : (((d + 1 : ℕ) : ℤ)) = (d : ℤ) + 1 := by push_cast; ring
  rw [hbnd]

/-! ##### Product side: the partial product as a formal power series and its stabilization. -/

/-- The `n`-th formal factor of the negative triple product. -/
noncomputable def jNegTripleFactorPS (A B n : ℕ) : PowerSeries ℚ :=
  apFactorPS ℚ B B n * apFactorNegPS A B n * apFactorNegPS (B - A) B n

/-- The infinite negative triple product on the formal-PS side. -/
noncomputable def jNegTripleProductInfPS (A B : ℕ) : PowerSeries ℚ :=
  qPochAPPS ℚ B B * qPochAPNegPS A B * qPochAPNegPS (B - A) B

theorem hasProd_jNegTripleFactorPS (A B : ℕ) (hAB : A < B) :
    HasProd (fun n : ℕ => jNegTripleFactorPS A B n) (jNegTripleProductInfPS A B) := by
  unfold jNegTripleFactorPS jNegTripleProductInfPS
  exact ((hasProd_qPochAPPS ℚ B B (by omega)).mul
    (hasProd_qPochAPNegPS A B (by omega))).mul
      (hasProd_qPochAPNegPS (B - A) B (by omega))

/-- `jNegProductPartial A B N = ofPSK(∏_{n<N} jNegTripleFactorPS A B n)` (`A < B`). -/
theorem jNegProductPartial_eq_ofPSK_partial (A B N : ℕ) (hAB : A < B) :
    jNegProductPartial (A : ℤ) (B : ℤ) N =
      ofPSK (∏ n ∈ Finset.range N, jNegTripleFactorPS A B n) := by
  unfold jNegProductPartial
  have hsub : (B : ℤ) - (A : ℤ) = ((B - A : ℕ) : ℤ) := by omega
  rw [hsub]
  simp only [Qpow_eq_hm]
  rw [qPochhammer_Qpow_eq_coe_apFinitePS B N]
  rw [show (((∏ n ∈ Finset.range N, apFactorPS ℚ B B n : PowerSeries ℚ)) : K)
        = ofPSK (∏ n ∈ Finset.range N, apFactorPS ℚ B B n) from rfl]
  rw [show (-(QseriesFormalization.Pending.Ch10HM.Qpow (A : ℤ))) = -(Qpow (A : ℤ)) from rfl,
      show (-(QseriesFormalization.Pending.Ch10HM.Qpow ((B - A : ℕ) : ℤ))) = -(Qpow ((B - A : ℕ) : ℤ)) from rfl,
      show QseriesFormalization.Pending.Ch10HM.Qpow (B : ℤ) = Qpow (B : ℤ) from rfl]
  rw [qPochNeg_Qpow_eq_ofPSK_apFiniteNegPS A B N, qPochNeg_Qpow_eq_ofPSK_apFiniteNegPS (B - A) B N]
  rw [← map_mul, ← map_mul]
  congr 1
  simp only [jNegTripleFactorPS, Finset.prod_mul_distrib]
  ring

/-- Coefficient stabilization of the partial negative product (`k < B·N` covers the `A = 0`
boundary, where `apFactorNegPS A B N` has order `A + B·N = B·N`). -/
theorem partial_prod_jNegTripleFactorPS_coeff_stable
    (A B k N : ℕ) (hAB : A < B) (hN : k < B * N) :
    PowerSeries.coeff k (∏ n ∈ Finset.range (N + 1), jNegTripleFactorPS A B n) =
      PowerSeries.coeff k (∏ n ∈ Finset.range N, jNegTripleFactorPS A B n) := by
  rw [Finset.prod_range_succ]
  change PowerSeries.coeff k
      ((∏ n ∈ Finset.range N, jNegTripleFactorPS A B n) *
        (apFactorPS ℚ B B N * apFactorNegPS A B N * apFactorNegPS (B - A) B N)) =
    PowerSeries.coeff k (∏ n ∈ Finset.range N, jNegTripleFactorPS A B n)
  let P : PowerSeries ℚ := ∏ n ∈ Finset.range N, jNegTripleFactorPS A B n
  calc
    PowerSeries.coeff k
        (P * (apFactorPS ℚ B B N * apFactorNegPS A B N * apFactorNegPS (B - A) B N))
        = PowerSeries.coeff k
          (((P * apFactorPS ℚ B B N) * apFactorNegPS A B N) * apFactorNegPS (B - A) B N) := by
          ring_nf
    _ = PowerSeries.coeff k ((P * apFactorPS ℚ B B N) * apFactorNegPS A B N) :=
          coeff_mul_apFactorNegPS_eq_of_lt
            ((P * apFactorPS ℚ B B N) * apFactorNegPS A B N) k (B - A) B N (by omega)
    _ = PowerSeries.coeff k (P * apFactorPS ℚ B B N) :=
          coeff_mul_apFactorNegPS_eq_of_lt (P * apFactorPS ℚ B B N) k A B N (by omega)
    _ = PowerSeries.coeff k P :=
          coeff_mul_apFactorPS_eq_of_lt ℚ P k B B N (by omega)

theorem partial_prod_jNegTripleFactorPS_coeff_eq
    (A B k N M : ℕ) (hAB : A < B) (hkN : k < N) (hNM : N ≤ M) :
    PowerSeries.coeff k (∏ n ∈ Finset.range M, jNegTripleFactorPS A B n) =
      PowerSeries.coeff k (∏ n ∈ Finset.range N, jNegTripleFactorPS A B n) := by
  have hB1 : 1 ≤ B := by omega
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M hM ih =>
      have hkBM : k < B * M := by
        have : M ≤ B * M := by simpa [Nat.mul_comm] using Nat.mul_le_mul_right M hB1
        omega
      rw [partial_prod_jNegTripleFactorPS_coeff_stable A B k M hAB hkBM, ih]

theorem coeff_jNegTripleProductInfPS_eq_coeff_partial
    (A B k : ℕ) (hAB : A < B) :
    (jNegTripleProductInfPS A B).coeff k =
      PowerSeries.coeff k (∏ n ∈ Finset.range (k + 1), jNegTripleFactorPS A B n) := by
  have hhp := hasProd_jNegTripleFactorPS A B hAB
  have htend := hhp.tendsto_prod_nat
  have hcoeff := (PowerSeries.WithPiTopology.continuous_coeff ℚ k).continuousAt.tendsto.comp htend
  have hconst : Filter.Tendsto
      (fun N => PowerSeries.coeff k (∏ n ∈ Finset.range N, jNegTripleFactorPS A B n))
      Filter.atTop (nhds (PowerSeries.coeff k (∏ n ∈ Finset.range (k + 1), jNegTripleFactorPS A B n))) := by
    apply tendsto_atTop_of_eventually_const (i₀ := k + 1)
    intro N hN
    exact partial_prod_jNegTripleFactorPS_coeff_eq A B k (k + 1) N hAB (by omega) hN
  exact tendsto_nhds_unique hcoeff hconst

/-- The negative triple-product infinite PS, coefficient-zero on negative degree (so its `ofPSK`
agrees with the all-`+1` theta below the cutoff). -/
theorem JK_one_coeff_eq_zero_of_neg
    (A B : ℕ) (hA : 0 < A) (hAB : A < B) {e : ℤ} (he : e < 0) :
    (JK (B : ℤ) (A : ℤ) (by omega) (fun _ => 1)).coeff e = 0 := by
  rw [JK_coeff]
  have hz : ∀ r : ℤ, (if thetaQDeg (B : ℤ) (A : ℤ) r = e then (1 : ℚ) else 0) = 0 := by
    intro r
    have hne : thetaQDeg (B : ℤ) (A : ℤ) r ≠ e := by
      rw [thetaQDeg_eq_jExp]
      have := jExp_nonneg_of_pos_lt (A : ℤ) (B : ℤ) r (by omega) (by omega)
      omega
    rw [if_neg hne]
  rw [finsum_congr hz, finsum_zero]

/-- **Negative JTP product theorem (`0 < A < B`).**
`J(Q^A;Q^B) = (Q^B;Q^B)_∞ (−Q^A;Q^B)_∞ (−Q^{B-A};Q^B)_∞`, i.e. all-`+1` theta = `apK·apKneg·apKneg`. -/
theorem JK_one_eq_apKneg_prod (A B : ℕ) (hA : 0 < A) (hAB : A < B) :
    JK (B : ℤ) (A : ℤ) (by omega) (fun _ => 1) = apK B B * apKneg A B * apKneg (B - A) B := by
  have hinf : apK B B * apKneg A B * apKneg (B - A) B = ofPSK (jNegTripleProductInfPS A B) := by
    unfold apK apKneg jNegTripleProductInfPS
    rw [map_mul, map_mul]
  rw [hinf]
  apply HahnSeries.ext
  funext e
  by_cases he : e < 0
  · rw [JK_one_coeff_eq_zero_of_neg A B hA hAB he, ofPSK_coeff_neg _ e he]
  · obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ e)
    rw [ofPSK_coeff_nat]
    rw [coeff_jNegTripleProductInfPS_eq_coeff_partial A B d hAB]
    rw [← (lcoeff_jNegProductPartial_eq_thetaCoeff A B d hA hAB)]
    rw [jNegProductPartial_eq_ofPSK_partial A B (d + 1) hAB, ofPSK_coeff_nat]

/-! ##### The degenerate `A = 0` case (for `Jneg1`, `z = 1`).

The general theorem needs `0 < A` only through the window/degree bounds
`abs_le_jExp_of_pos_lt` and `degree_sub_lt_center_start` (the Gaussian collapse and product side
are `A`-independent).  For `A = 0` those *exact* bounds fail at `n = 1` (`jExp 0 B 1 = 0`), but the
weaker facts they are used for still hold.  We reprove just those two facts for `A = 0`, then mirror
the heart / extensionality with `A = 0`. -/

/-- `jExp 0 B n = B·T(n) ≥ 0`. -/
theorem jExp_zero_eq (B n : ℤ) : jExp 0 B n = B * (n * (n - 1) / 2) := by
  unfold jExp
  have hdvd : (2 : ℤ) ∣ n * (n - 1) := by
    rcases Int.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact ⟨m * (n - 1), by rw [hm]; ring⟩
    · exact ⟨n * m, by rw [hm]; ring⟩
  rw [show B * n * (n - 1) = B * (n * (n - 1)) by ring, Int.mul_ediv_assoc B hdvd]
  ring

theorem jExp_zero_nonneg (B n : ℤ) (hB : 0 < B) : 0 ≤ jExp 0 B n := by
  rw [jExp_zero_eq]
  have hT : 0 ≤ n * (n - 1) / 2 := by
    apply Int.ediv_nonneg _ (by omega); nlinarith [sq_nonneg (2 * n - 1)]
  exact mul_nonneg (by omega) hT

/-- Window bound at `A = 0`: a root `jExp 0 B n = d` has `|n| ≤ d+1` (`0 < B`, `d : ℕ`). -/
theorem abs_le_window_jExp_zero (B : ℕ) (d : ℕ) (n : ℤ) (hB : 0 < B)
    (hroot : jExp 0 (B : ℤ) n = (d : ℤ)) : |n| ≤ (d : ℤ) + 1 := by
  by_contra hcon
  push_neg at hcon
  have hexp : jExp 0 (B : ℤ) n = (B : ℤ) * (n * (n - 1) / 2) := jExp_zero_eq (B : ℤ) n
  -- `|n| ≥ d+2` ⇒ `n(n-1)/2 ≥ (d+1)(d+2)/2 ≥ d+1` ⇒ `jExp = B·(…) ≥ d+1 > d`.
  have hge : (d : ℤ) + 1 ≤ n * (n - 1) / 2 := by
    have h2 : (((d : ℤ) + 1) * ((d : ℤ) + 2)) ≤ n * (n - 1) := by
      rcases lt_or_ge n 0 with hn | hn
      · have hn2 : n ≤ -((d : ℤ) + 2) := by
          have := abs_of_neg hn; omega
        nlinarith
      · have hn2 : (d : ℤ) + 2 ≤ n := by
          have := abs_of_nonneg hn; omega
        nlinarith
    have hdiv : (((d : ℤ) + 1) * ((d : ℤ) + 2)) / 2 ≤ n * (n - 1) / 2 :=
      Int.ediv_le_ediv (by norm_num) h2
    have hge2 : (d : ℤ) + 1 ≤ (((d : ℤ) + 1) * ((d : ℤ) + 2)) / 2 := by
      rw [Int.le_ediv_iff_mul_le (by norm_num)]; nlinarith
    omega
  have hBge : (B : ℤ) * ((d : ℤ) + 1) ≤ (B : ℤ) * (n * (n - 1) / 2) :=
    mul_le_mul_of_nonneg_left hge (by omega)
  rw [hexp] at hroot
  have hB1 : (1 : ℤ) ≤ B := by omega
  nlinarith

/-- Degree bound at `A = 0`: if `|n| = r ≤ d+1` then `d − jExp 0 B n < B·(d+1−r+1)`. -/
theorem degree_sub_lt_center_start_zero (B d r : ℕ) (hB : 0 < B) (hr : r ≤ d + 1)
    (n : ℤ) (hnabs : |n| = (r : ℤ)) :
    (d : ℤ) - jExp 0 (B : ℤ) n < (B * (d + 1 - r + 1) : ℕ) := by
  have hB1 : (1 : ℤ) ≤ B := by exact_mod_cast hB
  -- `jExp 0 B n = B·(n(n-1)/2) ≥ B·(r(r-1)/2)` since `n(n-1)/2 ≥ r(r-1)/2` for `|n| = r`.
  have hexp : jExp 0 (B : ℤ) n = (B : ℤ) * (n * (n - 1) / 2) := jExp_zero_eq (B : ℤ) n
  have hTge : (r : ℤ) * ((r : ℤ) - 1) / 2 ≤ n * (n - 1) / 2 := by
    apply Int.ediv_le_ediv (by norm_num)
    have hnn : (r : ℤ) ≤ |n| := le_of_eq hnabs.symm
    rcases abs_cases n with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1] at hnabs; nlinarith [hnabs]
    · rw [h1] at hnabs; nlinarith [hnabs]
  have hjge : (B : ℤ) * ((r : ℤ) * ((r : ℤ) - 1) / 2) ≤ jExp 0 (B : ℤ) n := by
    rw [hexp]; exact mul_le_mul_of_nonneg_left hTge (by omega)
  -- Goal: d - jExp < B*(d+2-r).  Cast nat subtraction (r ≤ d+1) and finish with nlinarith.
  have hcast : ((B * (d + 1 - r + 1) : ℕ) : ℤ) = (B : ℤ) * ((d : ℤ) + 2 - (r : ℤ)) := by
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_sub (by omega : r ≤ d + 1)]
    push_cast; ring
  rw [hcast]
  have hrle : (r : ℤ) ≤ (d : ℤ) + 1 := by exact_mod_cast hr
  have hr0 : (0 : ℤ) ≤ (r : ℤ) := Int.natCast_nonneg r
  -- `r(r-1)` is even, so `2·(r(r-1)/2) = r(r-1)`.
  have heven : 2 * ((r : ℤ) * ((r : ℤ) - 1) / 2) = (r : ℤ) * ((r : ℤ) - 1) := by
    have hdvd : (2 : ℤ) ∣ (r : ℤ) * ((r : ℤ) - 1) := by
      rcases Int.even_or_odd (r : ℤ) with ⟨m, hm⟩ | ⟨m, hm⟩
      · exact ⟨m * ((r : ℤ) - 1), by rw [hm]; ring⟩
      · exact ⟨(r : ℤ) * m, by rw [hm]; ring⟩
    rw [Int.mul_ediv_cancel' hdvd]
  set s : ℤ := (r : ℤ) * ((r : ℤ) - 1) / 2 with hs
  -- `jExp ≥ B·s`, `2s = r(r-1)`, `B ≥ 1`, `r ≤ d+1`.  Then `d - jExp < B(d+2-r)`.
  -- `s ≥ r-1`:  `2s - 2(r-1) = (r-1)(r-2) ≥ 0` for integer `r`.
  have hsge : (r : ℤ) - 1 ≤ s := by
    have hprod : (0 : ℤ) ≤ ((r : ℤ) - 1) * ((r : ℤ) - 2) := by
      rcases lt_or_ge (r : ℤ) 2 with h | h
      · have h1 : (r : ℤ) - 1 ≤ 0 := by omega
        have h2 : (r : ℤ) - 2 ≤ 0 := by omega
        nlinarith
      · exact mul_nonneg (by omega) (by omega)
    nlinarith [heven, hprod]
  have hge : (d : ℤ) + 1 ≤ (d : ℤ) + 2 - (r : ℤ) + s := by omega
  -- `B(d+2-r+s) ≥ B(d+1) ≥ d+1 > d ≥ d - jExp`, so `d - jExp < B(d+2-r)`.
  nlinarith [hjge, hB1, hr0, hge,
    mul_le_mul_of_nonneg_left hge (by omega : (0:ℤ) ≤ B),
    mul_nonneg (by omega : (0:ℤ) ≤ B - 1) (by omega : (0:ℤ) ≤ (d:ℤ) + 1)]

/-! ##### `A = 0` heart and extensionality. -/

/-- All-`+1` heart lemma at `A = 0`, center-add branch. -/
theorem lcoeff_center_add_mul_Qpow_jExp_zero_eq
    (B d r : ℕ) (hB : 0 < B) (hr : r ≤ d + 1) :
    lcoeff
        ((qPochhammer (QseriesFormalization.Pending.Ch10HM.Qpow (B : ℤ)) (d + 1) *
            gaussianBinom (QseriesFormalization.Pending.Ch10HM.Qpow (B : ℤ)) (2 * (d + 1)) ((d + 1) + r)) *
          Qpow (jExp 0 (B : ℤ) (r : ℤ)))
        (d : ℤ) =
      if jExp 0 (B : ℤ) (r : ℤ) = (d : ℤ) then 1 else 0 := by
  rw [Qpow_eq_hm, mul_comm, lcoeff_Qpow_mul]
  have hlow := degree_sub_lt_center_start_zero B d r hB hr (r : ℤ) (by
    rw [abs_of_nonneg]; exact Int.natCast_nonneg r)
  have hcorr := lcoeff_qPochhammer_mul_gaussian_center_add_low_int
    B (d + 1) r (by omega : 0 < B) hr
    ((d : ℤ) - jExp 0 (B : ℤ) (r : ℤ)) hlow
  rw [hcorr]
  by_cases heq : jExp 0 (B : ℤ) (r : ℤ) = (d : ℤ)
  · simp [heq]
  · have htne : (d : ℤ) - jExp 0 (B : ℤ) (r : ℤ) ≠ 0 := by omega
    simp [heq, htne]

/-- All-`+1` heart lemma at `A = 0`, center-sub branch. -/
theorem lcoeff_center_sub_mul_Qpow_jExp_zero_eq
    (B d r : ℕ) (hB : 0 < B) (hr : r ≤ d + 1) :
    lcoeff
        ((qPochhammer (QseriesFormalization.Pending.Ch10HM.Qpow (B : ℤ)) (d + 1) *
            gaussianBinom (QseriesFormalization.Pending.Ch10HM.Qpow (B : ℤ)) (2 * (d + 1)) ((d + 1) - r)) *
          Qpow (jExp 0 (B : ℤ) (-(r : ℤ))))
        (d : ℤ) =
      if jExp 0 (B : ℤ) (-(r : ℤ)) = (d : ℤ) then 1 else 0 := by
  rw [Qpow_eq_hm, mul_comm, lcoeff_Qpow_mul]
  have hlow := degree_sub_lt_center_start_zero B d r hB hr (-(r : ℤ)) (by
    rw [abs_of_nonpos]
    · simp
    · exact neg_nonpos.mpr (Int.natCast_nonneg r))
  have hcorr := lcoeff_qPochhammer_mul_gaussian_center_sub_low_int
    B (d + 1) r (by omega : 0 < B) hr
    ((d : ℤ) - jExp 0 (B : ℤ) (-(r : ℤ))) hlow
  rw [hcorr]
  by_cases heq : jExp 0 (B : ℤ) (-(r : ℤ)) = (d : ℤ)
  · simp [heq]
  · have htne : (d : ℤ) - jExp 0 (B : ℤ) (-(r : ℤ)) ≠ 0 := by omega
    simp [heq, htne]

/-- All-`+1` theta coefficient at `A = 0` as a finite window sum. -/
theorem JK_one_coeff_zero_eq_sum_Icc_succ (B d : ℕ) (hB : 0 < B) :
    (JK (B : ℤ) (0 : ℤ) (by omega) (fun _ => 1)).coeff (d : ℤ) =
      ∑ n ∈ Finset.Icc (-(d + 1 : ℤ)) (d + 1 : ℤ),
        if jExp 0 (B : ℤ) n = (d : ℤ) then (1 : ℚ) else 0 := by
  rw [JK_coeff]
  have hsummand : ∀ n : ℤ,
      (if thetaQDeg (B : ℤ) (0 : ℤ) n = (d : ℤ) then (1 : ℚ) else 0)
        = (if jExp 0 (B : ℤ) n = (d : ℤ) then (1 : ℚ) else 0) := by
    intro n; rw [thetaQDeg_eq_jExp]
  simp_rw [hsummand]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc (-(d + 1 : ℤ)) (d + 1 : ℤ))]
  intro n hn
  simp only [Function.mem_support, ne_eq] at hn
  rw [Finset.coe_Icc, Set.mem_Icc]
  by_cases hroot : jExp 0 (B : ℤ) n = (d : ℤ)
  · have habs := abs_le_window_jExp_zero B d n hB hroot
    have hn_le : n ≤ (d : ℤ) + 1 := le_trans (le_abs_self n) habs
    have hneg_le : -((d : ℤ) + 1) ≤ n := by have := neg_abs_le n; omega
    constructor <;> omega
  · exact absurd (by simp [hroot]) hn

/-- `A = 0` heart: partial-product coeff = all-`+1` theta coeff. -/
theorem lcoeff_jNegProductPartial_zero_eq_thetaCoeff (B d : ℕ) (hB : 0 < B) :
    (jNegProductPartial (0 : ℤ) (B : ℤ) (d + 1)).coeff (d : ℤ) =
      (JK (B : ℤ) (0 : ℤ) (by omega) (fun _ => 1)).coeff (d : ℤ) := by
  rw [JK_one_coeff_zero_eq_sum_Icc_succ B d hB]
  have hsum :
      (jNegProductPartial (0 : ℤ) (B : ℤ) (d + 1)).coeff (d : ℤ) =
        ∑ k ∈ Finset.range (2 * (d + 1) + 1),
          lcoeff
            (qPochhammer (Qpow (B : ℤ)) (d + 1) *
              (gaussianBinom (Qpow (B : ℤ)) (2 * (d + 1)) k *
                Qpow (jExp 0 (B : ℤ) ((k : ℤ) - ((d + 1 : ℕ) : ℤ))))) (d : ℤ) := by
    unfold jNegProductPartial
    rw [negFiniteProduct_eq_finiteJTPRHS, negFiniteJTPRHS_Qpow_eq_natSum]
    rw [QseriesFormalization.PartI.Ch03.natSum_eq_sum_range]
    simp only [Finset.mul_sum]
    simp [lcoeff]
  rw [hsum]
  have hterms :
      (∑ k ∈ Finset.range (2 * (d + 1) + 1),
          lcoeff
            (qPochhammer (Qpow (B : ℤ)) (d + 1) *
              (gaussianBinom (Qpow (B : ℤ)) (2 * (d + 1)) k *
                Qpow (jExp 0 (B : ℤ) ((k : ℤ) - ((d + 1 : ℕ) : ℤ))))) (d : ℤ)) =
        ∑ k ∈ Finset.range (2 * (d + 1) + 1),
          if jExp 0 (B : ℤ) ((k : ℤ) - ((d + 1 : ℕ) : ℤ)) = (d : ℤ) then (1 : ℚ) else 0 := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [Finset.mem_range] at hk
    by_cases hNk : d + 1 ≤ k
    · let r : ℕ := k - (d + 1)
      have hr : r ≤ d + 1 := by dsimp [r]; omega
      have hk_eq : k = (d + 1) + r := by dsimp [r]; omega
      have hn_eq : (k : ℤ) - ((d + 1 : ℕ) : ℤ) = (r : ℤ) := by dsimp [r]; omega
      rw [hn_eq, hk_eq]
      rw [show qPochhammer (Qpow (B : ℤ)) (d + 1) *
          (gaussianBinom (Qpow (B : ℤ)) (2 * (d + 1)) ((d + 1) + r) *
            Qpow (jExp 0 (B : ℤ) (r : ℤ))) =
          (qPochhammer (Qpow (B : ℤ)) (d + 1) *
            gaussianBinom (Qpow (B : ℤ)) (2 * (d + 1)) ((d + 1) + r)) *
              Qpow (jExp 0 (B : ℤ) (r : ℤ)) by ring]
      exact lcoeff_center_add_mul_Qpow_jExp_zero_eq B d r hB hr
    · let r : ℕ := (d + 1) - k
      have hr : r ≤ d + 1 := by dsimp [r]; omega
      have hk_eq : k = (d + 1) - r := by dsimp [r]; omega
      have hn_eq : (k : ℤ) - ((d + 1 : ℕ) : ℤ) = -(r : ℤ) := by dsimp [r]; omega
      rw [hn_eq, hk_eq]
      rw [show qPochhammer (Qpow (B : ℤ)) (d + 1) *
          (gaussianBinom (Qpow (B : ℤ)) (2 * (d + 1)) ((d + 1) - r) *
            Qpow (jExp 0 (B : ℤ) (-(r : ℤ)))) =
          (qPochhammer (Qpow (B : ℤ)) (d + 1) *
            gaussianBinom (Qpow (B : ℤ)) (2 * (d + 1)) ((d + 1) - r)) *
              Qpow (jExp 0 (B : ℤ) (-(r : ℤ))) by ring]
      exact lcoeff_center_sub_mul_Qpow_jExp_zero_eq B d r hB hr
  rw [hterms]
  rw [sum_range_center_eq_sum_Icc
    (fun n : ℤ => if jExp 0 (B : ℤ) n = (d : ℤ) then (1 : ℚ) else 0) (d + 1)]
  have hbnd : (((d + 1 : ℕ) : ℤ)) = (d : ℤ) + 1 := by push_cast; ring
  rw [hbnd]

/-- All-`+1` theta coeff is zero on negative degrees, `A = 0`. -/
theorem JK_one_coeff_zero_eq_zero_of_neg (B : ℕ) (hB : 0 < B) {e : ℤ} (he : e < 0) :
    (JK (B : ℤ) (0 : ℤ) (by omega) (fun _ => 1)).coeff e = 0 := by
  rw [JK_coeff]
  have hz : ∀ r : ℤ, (if thetaQDeg (B : ℤ) (0 : ℤ) r = e then (1 : ℚ) else 0) = 0 := by
    intro r
    have hne : thetaQDeg (B : ℤ) (0 : ℤ) r ≠ e := by
      rw [thetaQDeg_eq_jExp]
      have := jExp_zero_nonneg (B : ℤ) r (by omega)
      omega
    rw [if_neg hne]
  rw [finsum_congr hz, finsum_zero]

/-- **Negative JTP product theorem at `A = 0`.**
`J(1;Q^B) = (Q^B;Q^B)_∞ (−1;Q^B)_∞ (−Q^B;Q^B)_∞`, i.e. `JK B 0 (·1) = apK B B·apKneg 0 B·apKneg B B`. -/
theorem JK_one_eq_apKneg_prod_zero (B : ℕ) (hB : 0 < B) :
    JK (B : ℤ) (0 : ℤ) (by omega) (fun _ => 1) = apK B B * apKneg 0 B * apKneg B B := by
  have hinf : apK B B * apKneg 0 B * apKneg B B = ofPSK (jNegTripleProductInfPS 0 B) := by
    unfold apK apKneg jNegTripleProductInfPS
    rw [show B - 0 = B from rfl, map_mul, map_mul]
  rw [hinf]
  apply HahnSeries.ext
  funext e
  by_cases he : e < 0
  · rw [JK_one_coeff_zero_eq_zero_of_neg B hB he, ofPSK_coeff_neg _ e he]
  · push_neg at he
    obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le he
    rw [ofPSK_coeff_nat]
    rw [coeff_jNegTripleProductInfPS_eq_coeff_partial 0 B d hB]
    rw [← (lcoeff_jNegProductPartial_zero_eq_thetaCoeff B d hB)]
    have hcast0 : jNegProductPartial ((0 : ℕ) : ℤ) ((B : ℕ) : ℤ) (d + 1)
        = jNegProductPartial (0 : ℤ) (B : ℤ) (d + 1) := by norm_num
    rw [← hcast0, jNegProductPartial_eq_ofPSK_partial 0 B (d + 1) hB, ofPSK_coeff_nat]

end NegJTPChain

/-- `qPochAPNegPS 0 m = 2·qPochAPNegPS m m` (the `n=0` factor `1+X^0=2` factors out). -/
theorem qPochAPNegPS_zero_eq_two_mul (m : ℕ) (hm : 0 < m) :
    qPochAPNegPS 0 m = (2 : PowerSeries ℚ) * qPochAPNegPS m m := by
  unfold qPochAPNegPS
  have hshift : (fun n : ℕ => apFactorNegPS 0 m (n + 1)) = (fun n : ℕ => apFactorNegPS m m n) := by
    funext n
    unfold apFactorNegPS
    congr 2
    ring
  have hmul : Multipliable (fun n : ℕ => apFactorNegPS 0 m (n + 1)) := by
    rw [hshift]; exact multipliable_apFactorNegPS m m hm
  rw [tprod_eq_zero_mul' hmul, hshift]
  congr 1
  unfold apFactorNegPS
  norm_num

/-- `apKneg 0 m = 2·apKneg m m` (the `K`-level statement). -/
theorem apKneg_zero_eq_two_mul (m : ℕ) (hm : 0 < m) :
    apKneg 0 m = HahnSeries.single 0 (2 : ℚ) * apKneg m m := by
  unfold apKneg
  rw [qPochAPNegPS_zero_eq_two_mul m hm, map_mul]
  congr 1
  -- ofPSK (2 : PowerSeries ℚ) = single 0 2 = (2 : K).
  have h2 : ofPSK (2 : PowerSeries ℚ) = (2 : K) := map_ofNat ofPSK 2
  rw [h2]
  rw [show HahnSeries.single (0 : ℤ) (2 : ℚ)
        = HahnSeries.single (0 : ℤ) (1 : ℚ) + HahnSeries.single (0 : ℤ) (1 : ℚ) by
    rw [← HahnSeries.single_add]; norm_num]
  rw [HahnSeries.single_zero_one]
  norm_num

/-- **Negative JTP, `z = 1` instance.** `J(−1;Q⁹) = 2·(−Q⁹;Q⁹)_∞²·(Q⁹;Q⁹)_∞`. -/
theorem Jneg1_prod : Jneg1 = HahnSeries.single 0 (2 : ℚ) * (apKneg 9 9 * apKneg 9 9 * apK 9 9) := by
  have h := JK_one_eq_apKneg_prod_zero 9 (by norm_num)
  have hcast : JK ((9 : ℕ) : ℤ) (0 : ℤ) (by norm_num) (fun _ => 1) = Jneg1 := by
    norm_num [Jneg1]
  rw [hcast] at h
  -- h : Jneg1 = apK 9 9 · apKneg 0 9 · apKneg 9 9
  rw [h, apKneg_zero_eq_two_mul 9 (by norm_num)]
  ring

/-- **Negative JTP, `z = Q⁶` instance.** `J(−Q⁶;Q⁹) = (−Q³;Q⁹)_∞·(−Q⁶;Q⁹)_∞·(Q⁹;Q⁹)_∞`. -/
theorem JnegQ6_prod : JnegQ6 = apKneg 3 9 * apKneg 6 9 * apK 9 9 := by
  have h := JK_one_eq_apKneg_prod 6 9 (by norm_num) (by norm_num)
  -- `JnegQ6 = JK 9 6 (fun _ => 1)`; the general theorem gives `apK 9 9·apKneg 6 9·apKneg 3 9`.
  simp only [show (9 - 6 : ℕ) = 3 from rfl] at h
  have hcast : JK ((9 : ℕ) : ℤ) ((6 : ℕ) : ℤ) (by norm_num) (fun _ => 1) = JnegQ6 := by
    norm_num [JnegQ6]
  rw [hcast] at h
  rw [h]; ring

/-! ### `P0`/`P12` reduced to the two `apKneg`-cleared negative-JTP identities

All the AP-product *algebra* below is now fully proved (RHS triple products `JQ15_prod`/`JQ9_prod`,
the mod-18 refinements `apK_*_refine`, the sign-pairing `apK_mul_apKneg`, the nonzero lemmas
`apK_ne_zero`, and the domain structure of `K = HahnSeries ℤ ℚ`).  Multiplying `P0` through by the
nonzero factor `apK 9 18` and `P12` through by `apK 3 18·apK 15 18`, and cancelling, reduces each to
a single **cleared negative Jacobi-triple-product identity** (numerically verified, `verify6.py`):

  `Jneg1 · apK 9 18                = single 0 2 · apK 18 18`,
  `JnegQ6 · apK 3 18 · apK 15 18   = apK 9 18 · apK 18 18`.

These two are the genuine remaining analytic input — the bilateral all-`+1`-weight theta sum
`J(−z;q) = ∑_r z^r q^{T r}` equals an arithmetic-progression product.  They are the negative-`z`
(`z ↦ −Qpow a`) instance of HM's `jLaurent_eq_tripleProductInf` chain (finite JTP `z = −Qpow a` →
coefficient stabilization → infinite `(±Q^·;Q^·)_∞` product). -/

theorem init_product_P0 :
    poch_q * Jneg1 = HahnSeries.single 0 (2 : ℚ) * (poch_q2 * JQ15) := by
  -- The cleared negative-JTP identity for `J(-1;Q⁹)`, derived from the product form `Jneg1_prod`
  -- and the sign-pairing cancellation `apK 9 18 · apKneg 9 9 = 1`.
  have h1818 : apK 18 18 ≠ 0 := apK_ne_zero 18 18 (by norm_num) (by norm_num)
  -- `apK 9 18 · apKneg 9 9 = 1` (from `apK 9 9 = apK 9 18·apK 18 18` and `apK 9 9·apKneg 9 9 = apK 18 18`).
  have hcancel : apK 9 18 * apKneg 9 9 = 1 := by
    apply mul_right_cancel₀ h1818
    have hp := apK_mul_apKneg 9 9 (by norm_num)
    rw [one_mul]
    calc apK 9 18 * apKneg 9 9 * apK 18 18
        = apK 9 9 * apKneg 9 9 := by rw [apK_9_9_refine]; ring
      _ = apK (2 * 9) (2 * 9) := hp
      _ = apK 18 18 := by norm_num
  have hJneg1 : Jneg1 * apK 9 18 = HahnSeries.single 0 (2 : ℚ) * apK 18 18 := by
    rw [Jneg1_prod, apK_9_9_refine]
    -- LHS = single02 · apKneg99² · (apK918·apK1818) · apK918
    --     = single02 · (apK918·apKneg99)² · apK1818 = single02 · apK1818.
    rw [show HahnSeries.single 0 (2 : ℚ) * (apKneg 9 9 * apKneg 9 9 * (apK 9 18 * apK 18 18)) * apK 9 18
          = HahnSeries.single 0 (2 : ℚ) * (apK 9 18 * apKneg 9 9) * (apK 9 18 * apKneg 9 9) * apK 18 18
          by ring]
    rw [hcancel]
    ring
  have h918 : apK 9 18 ≠ 0 := apK_ne_zero 9 18 (by norm_num) (by norm_num)
  -- Cancel `apK 9 18` on the right.
  apply mul_right_cancel₀ h918
  rw [poch_q_eq_apK, poch_q2_eq_apK, JQ15_prod, apK_3_3_refine, apK_6_6_refine]
  -- LHS: apK33 · (Jneg1 · apK918) = apK33 · single02 · apK1818.
  rw [show apK 3 18 * apK 6 18 * apK 9 18 * apK 12 18 * apK 15 18 * apK 18 18 * Jneg1 * apK 9 18
        = (apK 3 18 * apK 6 18 * apK 9 18 * apK 12 18 * apK 15 18 * apK 18 18) * (Jneg1 * apK 9 18)
        by ring, hJneg1]
  ring

theorem init_product_P12 :
    poch_q * JnegQ6 = poch_q2 * JQ9 := by
  -- The cleared negative-JTP identity for `J(-Q⁶;Q⁹)`, derived from `JnegQ6_prod` and the
  -- sign-pairing cancellation `apKneg 3 9·apKneg 6 9·apK 3 18·apK 15 18 = 1`.
  have h618 : apK 6 18 ≠ 0 := apK_ne_zero 6 18 (by norm_num) (by norm_num)
  have h1218 : apK 12 18 ≠ 0 := apK_ne_zero 12 18 (by norm_num) (by norm_num)
  -- `apKneg 3 9·apK 3 18·apK 12 18 = apK 6 18`  (pairing 3 9 + refine 3 9).
  have hpair39 : apKneg 3 9 * apK 3 18 * apK 12 18 = apK 6 18 := by
    have hp := apK_mul_apKneg 3 9 (by norm_num)
    calc apKneg 3 9 * apK 3 18 * apK 12 18
        = apK 3 9 * apKneg 3 9 := by rw [apK_3_9_refine]; ring
      _ = apK (2 * 3) (2 * 9) := hp
      _ = apK 6 18 := by norm_num
  -- `apKneg 6 9·apK 6 18·apK 15 18 = apK 12 18`  (pairing 6 9 + refine 6 9).
  have hpair69 : apKneg 6 9 * apK 6 18 * apK 15 18 = apK 12 18 := by
    have hp := apK_mul_apKneg 6 9 (by norm_num)
    calc apKneg 6 9 * apK 6 18 * apK 15 18
        = apK 6 9 * apKneg 6 9 := by rw [apK_6_9_refine]; ring
      _ = apK (2 * 6) (2 * 9) := hp
      _ = apK 12 18 := by norm_num
  -- `apKneg 3 9·apKneg 6 9·apK 3 18·apK 15 18 = 1`.
  have hcancel : apKneg 3 9 * apKneg 6 9 * apK 3 18 * apK 15 18 = 1 := by
    apply mul_right_cancel₀ (mul_ne_zero h618 h1218)
    rw [one_mul]
    calc apKneg 3 9 * apKneg 6 9 * apK 3 18 * apK 15 18 * (apK 6 18 * apK 12 18)
        = (apKneg 3 9 * apK 3 18 * apK 12 18) * (apKneg 6 9 * apK 6 18 * apK 15 18) := by ring
      _ = apK 6 18 * apK 12 18 := by rw [hpair39, hpair69]
  have hJnegQ6 : JnegQ6 * apK 3 18 * apK 15 18 = apK 9 18 * apK 18 18 := by
    rw [JnegQ6_prod, apK_9_9_refine]
    -- LHS = apKneg39·apKneg69·(apK918·apK1818)·apK318·apK1518
    --     = (apKneg39·apKneg69·apK318·apK1518)·apK918·apK1818 = apK918·apK1818.
    rw [show apKneg 3 9 * apKneg 6 9 * (apK 9 18 * apK 18 18) * apK 3 18 * apK 15 18
          = (apKneg 3 9 * apKneg 6 9 * apK 3 18 * apK 15 18) * (apK 9 18 * apK 18 18) by ring]
    rw [hcancel, one_mul]
  have h318 : apK 3 18 ≠ 0 := apK_ne_zero 3 18 (by norm_num) (by norm_num)
  have h1518 : apK 15 18 ≠ 0 := apK_ne_zero 15 18 (by norm_num) (by norm_num)
  -- Cancel `apK 3 18` then `apK 15 18` on the right.
  apply mul_right_cancel₀ h1518
  apply mul_right_cancel₀ h318
  rw [poch_q_eq_apK, poch_q2_eq_apK, JQ9_prod, apK_3_3_refine, apK_6_6_refine]
  rw [show apK 3 18 * apK 6 18 * apK 9 18 * apK 12 18 * apK 15 18 * apK 18 18 * JnegQ6
            * apK 15 18 * apK 3 18
        = (apK 3 18 * apK 6 18 * apK 9 18 * apK 12 18 * apK 15 18 * apK 18 18)
            * (JnegQ6 * apK 3 18 * apK 15 18) by ring, hJnegQ6]
  ring

/-- The genuine analytic core of the three initial `x`-coefficient agreements, reduced (via the
slicing lemmas `thetaProdX_slice_*`/`zwegersLHS_x_slice_*`) to the two product identities
`init_product_P0`/`init_product_P12`:
`poch_q2 · (coeffXY zwegersLHS_x j 0) = single 1 (-1) · poch_q · (coeffXY (Θ(x;q²)Θ(x;q)) (j+1) 0)`.
Numerically verified (`/tmp/zwnum.py`) for `j = 0,1,2`. -/
theorem zwegers_init_x_core (j : ℤ) (hj : j = 0 ∨ j = 1 ∨ j = 2) :
    poch_q2 * coeffXY zwegersLHS_x j 0
      = HahnSeries.single 1 (-1 : ℚ) * poch_q * coeffXY (thetaX_q2 * thetaX_q) (j + 1) 0 := by
  -- single-product combination facts used in the dispatch.
  have hs12 : (HahnSeries.single (1 : ℤ) (2 : ℚ))
      = - (HahnSeries.single (1 : ℤ) (-1 : ℚ)) * HahnSeries.single (0 : ℤ) (2 : ℚ) := by
    rw [neg_mul, HahnSeries.single_mul_single]; norm_num
  have hs41 : (HahnSeries.single (4 : ℤ) (1 : ℚ))
      = HahnSeries.single (1 : ℤ) (-1 : ℚ) * HahnSeries.single (3 : ℤ) (-1 : ℚ) := by
    rw [HahnSeries.single_mul_single]; norm_num
  rcases hj with rfl | rfl | rfl
  · -- j = 0 :  uses P0.  RHS slice at x¹ = −Jneg1.
    rw [zwegersLHS_x_slice_zero, show ((0 : ℤ) + 1) = 1 by ring, thetaProdX_slice_one]
    rw [hs12]
    rw [show HahnSeries.single (1 : ℤ) (-1 : ℚ) * poch_q * (-Jneg1)
          = - (HahnSeries.single (1 : ℤ) (-1 : ℚ) * (poch_q * Jneg1)) by ring]
    rw [init_product_P0]
    ring
  · -- j = 1 :  uses P12.  RHS slice at x² = JnegQ6.
    rw [zwegersLHS_x_slice_one, show ((1 : ℤ) + 1) = 2 by ring, thetaProdX_slice_two]
    rw [show poch_q2 * (HahnSeries.single (1 : ℤ) (-1 : ℚ) * JQ9)
          = HahnSeries.single (1 : ℤ) (-1 : ℚ) * (poch_q2 * JQ9) by ring,
        ← init_product_P12]
    ring
  · -- j = 2 :  uses P12 again.  RHS slice at x³ = single 3 (-1)·JnegQ6.
    rw [zwegersLHS_x_slice_two, show ((2 : ℤ) + 1) = 3 by ring, thetaProdX_slice_three]
    rw [hs41]
    rw [show poch_q2 * (HahnSeries.single (1 : ℤ) (-1 : ℚ) * HahnSeries.single (3 : ℤ) (-1 : ℚ) * JQ9)
          = HahnSeries.single (1 : ℤ) (-1 : ℚ) * HahnSeries.single (3 : ℤ) (-1 : ℚ) * (poch_q2 * JQ9) by ring,
        ← init_product_P12]
    ring

/-- The three initial `x`-coefficients agree (Chen Eq. 10.36–10.38).  Reduced via the slicing
lemmas `coeffXY_embedQ_mul` and `coeffXY_zwegersRHS_x` to the isolated core
`zwegers_init_x_core`. -/
theorem zwegers_init_x (j : ℤ) (hj : j = 0 ∨ j = 1 ∨ j = 2) :
    coeffXY (embedQ poch_q2 * zwegersLHS_x) j 0 = coeffXY zwegersRHS_x j 0 := by
  rw [coeffXY_embedQ_mul, coeffXY_zwegersRHS_x]
  exact zwegers_init_x_core j hj

/-- **Zwegers' Lemma 10.1 (`x`-version), `poch_q2`-cleared.**
`embedQ poch_q2 · (∑_{k,l} (-1)^{k+l}(δ k − δ l) Q^{k²+l²} x^l) = - (Q x⁻¹) (q;q)∞ Θ(x;q²) Θ(x;q)`.

Proved unconditionally from the uniqueness skeleton `eq_of_fe_step3_and_initial` together with the
analytic inputs above. -/
theorem zwegers_lemma_10_1_x :
    embedQ poch_q2 * zwegersLHS_x = zwegersRHS_x := by
  apply eq_of_fe_step3_and_initial _ _ zwegers_FE_LHS_x zwegers_FE_RHS_x
    (fun i j hj a => ⟨zwegers_yplane_LHS_x i j hj a, zwegers_yplane_RHS_x i j hj a⟩)
    (zwegers_init_x 0 (by tauto)) (zwegers_init_x 1 (by tauto)) (zwegers_init_x 2 (by tauto))

/-! ### `y`-version (by the same argument with `x ↔ y`). -/

/-- `Θ(y;q) = thetaMon 3 0 0 1`. -/
noncomputable def thetaY_q : S := thetaMon 3 0 0 1 (by norm_num)
/-- `Θ(y;q²) = thetaMon 6 0 0 1`. -/
noncomputable def thetaY_q2 : S := thetaMon 6 0 0 1 (by norm_num)

/-- The 2D summable family for the Zwegers LHS, `y`-version
(`monom (k²+l²) 0 l ((-1)^{k+l}(δ k − δ l))`). -/
noncomputable def zFamilyY : HahnSeries.SummableFamily ExpQXY ℚ (ℤ × ℤ) where
  toFun := fun p => monom (p.1 ^ 2 + p.2 ^ 2) 0 p.2 (zW p.1 p.2)
  isPWO_iUnion_support' := by
    -- mirror of zFamily: Q-degree k²+l² bddBelow with finite fibers; x/y slot now (0, l).
    have hrange : (Set.range (fun p : ℤ × ℤ => expQXY (p.1 ^ 2 + p.2 ^ 2) 0 p.2)).IsPWO := by
      apply Set.PartiallyWellOrderedOn.subsetProdLex
      · have hsub : (fun (z : ℤ ×ₗ ExpXY) => (ofLex z).1) ''
            Set.range (fun p : ℤ × ℤ => expQXY (p.1 ^ 2 + p.2 ^ 2) 0 p.2) ⊆ Set.Ici (0 : ℤ) := by
          rintro a ⟨z, ⟨⟨k, l⟩, rfl⟩, rfl⟩
          simp only [expQXY, ofLex_toLex, Set.mem_Ici]; positivity
        refine (?_ : (Set.Ici (0 : ℤ)).IsPWO).mono hsub
        exact (bddBelow_Ici.isWF).isPWO
      · intro N
        apply Set.Finite.isPWO
        apply Set.Finite.subset (Set.Finite.image
          (fun p : ℤ × ℤ => (toLex ((0 : ℤ), p.2) : ExpXY)) (zDeg_finite_fiber N))
        rintro y ⟨⟨k, l⟩, hkl⟩
        simp only at hkl
        refine ⟨(k, l), ?_, ?_⟩
        · have h1 : (ofLex (expQXY (k ^ 2 + l ^ 2) 0 l)).1 = N := by rw [hkl]; rfl
          simpa [expQXY] using h1
        · have h2 : (ofLex (expQXY (k ^ 2 + l ^ 2) 0 l)).2 = y := by rw [hkl]; rfl
          simpa [expQXY] using h2
    refine hrange.mono (Set.iUnion_subset (fun p => ?_))
    intro g hg
    refine ⟨p, ?_⟩
    have hgeq : g = expQXY (p.1 ^ 2 + p.2 ^ 2) 0 p.2 := HahnSeries.support_single_subset hg
    rw [hgeq]
  finite_co_support' := by
    intro g
    apply Set.Finite.subset (zDeg_finite_fiber ((ofLex g).1))
    rintro ⟨k, l⟩ hkl
    simp only [Set.mem_setOf_eq] at hkl ⊢
    by_contra hne
    apply hkl
    unfold monom
    rw [HahnSeries.coeff_single_of_ne]
    intro hcon
    apply hne
    rw [hcon]; rfl

/-- `zwegersLHS_y`: the left-hand side of Zwegers' Lemma 10.1, `y`-version. -/
noncomputable def zwegersLHS_y : S := zFamilyY.hsum

/-- `zwegersLHS_y` is `x⁰`-supported. -/
theorem XZeroSupported_zwegersLHS_y : XZeroSupported zwegersLHS_y := by
  unfold zwegersLHS_y
  apply XZeroSupported_hsum
  rintro ⟨k, l⟩
  exact XZeroSupported_monom _ _ _

/-- `zwegersRHS_y` (cleared form): `- (Q y⁻¹) · embedQ poch_q · Θ(y;q²) · Θ(y;q)`. -/
noncomputable def zwegersRHS_y : S :=
  - monom 1 0 (-1) 1 * embedQ poch_q * thetaY_q2 * thetaY_q

/-! The `y`-version analytic inputs (mirror of the `x`-version under `x ↔ y`). -/

/-- **Monomial-times-slice lemma, `y`-version.**  `coeffXY (monom a 0 i c * F) 0 l` equals
`single a c · coeffXY F 0 (l - i)`. -/
theorem coeffXY_monom_mul_y (a i : ℤ) (c : ℚ) (F : S) (l : ℤ) :
    coeffXY (monom a 0 i c * F) 0 l = HahnSeries.single a c * coeffXY F 0 (l - i) := by
  have hneg : -expQXY a 0 i = expQXY (-a) 0 (-i) := by
    rw [neg_eq_iff_add_eq_zero, expQXY_add]
    rw [show a + -a = 0 by ring, show (0 : ℤ) + 0 = 0 by ring, show i + -i = 0 by ring]
    exact expQXY_zero
  apply HahnSeries.ext
  funext b
  rw [coeffXY_coeff, coeffQXY]
  rw [HahnSeries.coeff_single_mul, coeffXY_coeff, coeffQXY]
  show (HahnSeries.single (expQXY a 0 i) c * F).coeff (expQXY b 0 l)
      = c * F.coeff (expQXY (b - a) 0 (l - i))
  rw [HahnSeries.coeff_single_mul_S]
  rw [show expQXY b 0 l - expQXY a 0 i = expQXY (b - a) 0 (l - i) by
    rw [sub_eq_add_neg, sub_eq_add_neg, hneg, expQXY_add,
      show b + -a = b - a by ring, show (0 : ℤ) + 0 = 0 by ring, show l + -i = l - i by ring]]

/-- The `Q`-degree-`a` coefficient of the `y`-slice of `zwegersLHS_y` at `y^l`. -/
theorem coeffXY_zwegersLHS_y_coeff (l a : ℤ) :
    (coeffXY zwegersLHS_y 0 l).coeff a
      = ∑ᶠ p : ℤ × ℤ, (monom (p.1 ^ 2 + p.2 ^ 2) 0 p.2 (zW p.1 p.2)).coeff (expQXY a 0 l) := by
  rw [coeffXY_coeff, coeffQXY]
  unfold zwegersLHS_y
  rw [HahnSeries.SummableFamily.coeff_hsum]
  rfl

/-- **Bare step-3 FE for the `y`-slice of `zwegersLHS_y`** (mirror of `zwegersLHS_x_slice_fe`). -/
theorem zwegersLHS_y_slice_fe (l : ℤ) :
    coeffXY zwegersLHS_y 0 (l + 3) = - Qpow (6 * l + 9) * coeffXY zwegersLHS_y 0 l := by
  apply HahnSeries.ext
  funext a
  rw [show - Qpow (6 * l + 9) * coeffXY zwegersLHS_y 0 l
        = - (Qpow (6 * l + 9) * coeffXY zwegersLHS_y 0 l) by ring]
  rw [HahnSeries.coeff_neg]
  rw [show (Qpow (6 * l + 9) * coeffXY zwegersLHS_y 0 l).coeff a
        = (coeffXY zwegersLHS_y 0 l).coeff (a - (6 * l + 9)) by
    unfold Qpow
    rw [HahnSeries.coeff_single_mul, one_mul]]
  rw [coeffXY_zwegersLHS_y_coeff, coeffXY_zwegersLHS_y_coeff]
  rw [← finsum_neg_distrib]
  rw [← finsum_comp_equiv ((Equiv.refl ℤ).prodCongr (Equiv.addRight (3 : ℤ)))]
  apply finsum_congr
  rintro ⟨k, m⟩
  simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.coe_addRight, Prod.map_apply, id_eq]
  unfold monom
  rw [HahnSeries.coeff_single, HahnSeries.coeff_single]
  by_cases hm : m = l
  · subst hm
    have hdvd : (3 : ℤ) ∣ (m + 3) ↔ (3 : ℤ) ∣ m := by
      constructor <;> intro h <;> omega
    have hdelta : delta3 (m + 3) = delta3 m := by
      unfold delta3
      by_cases h3 : (3 : ℤ) ∣ m
      · rw [if_pos h3, if_pos (hdvd.mpr h3)]
      · rw [if_neg h3, if_neg (fun hc => h3 (hdvd.mp hc))]
    have hzW : zW k (m + 3) = - zW k m := by
      unfold zW
      rw [hdelta, show k + (m + 3) = (k + m) + 3 by ring,
        zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]
      norm_num
    have hL : (expQXY a 0 (m + 3) = expQXY (k ^ 2 + (m + 3) ^ 2) 0 (m + 3))
        ↔ a = k ^ 2 + (m + 3) ^ 2 := by
      constructor
      · intro hc; exact (expQXY_inj hc).1
      · intro hc; rw [hc]
    have hR : (expQXY (a - (6 * m + 9)) 0 m = expQXY (k ^ 2 + m ^ 2) 0 m)
        ↔ a = k ^ 2 + (m + 3) ^ 2 := by
      constructor
      · intro hc; have := (expQXY_inj hc).1; nlinarith [this]
      · intro hc; rw [show a - (6 * m + 9) = k ^ 2 + m ^ 2 by rw [hc]; ring]
    by_cases hcond : a = k ^ 2 + (m + 3) ^ 2
    · rw [if_pos (hL.mpr hcond), if_pos (hR.mpr hcond), hzW]
    · rw [if_neg (fun hc => hcond (hL.mp hc)), if_neg (fun hc => hcond (hR.mp hc)), neg_zero]
  · rw [if_neg ?_, if_neg ?_, neg_zero]
    · intro hc; exact hm (by have := (expQXY_inj hc).2.2; omega)
    · intro hc; exact hm (by have := (expQXY_inj hc).2.2; omega)

/-- The product family `Θ(y;q²)·Θ(y;q)` as a `SummableFamily`. -/
noncomputable def thetaProdY : HahnSeries.SummableFamily ExpQXY ℚ (ℤ × ℤ) :=
  HahnSeries.SummableFamily.mul (thetaFamily 6 0 0 1 (by norm_num)) (thetaFamily 3 0 0 1 (by norm_num))

theorem thetaProdY_hsum : thetaProdY.hsum = thetaY_q2 * thetaY_q := by
  unfold thetaProdY thetaY_q2 thetaY_q thetaMon
  rw [HahnSeries.SummableFamily.hsum_mul]

theorem thetaProdY_term (n2 n1 : ℤ) :
    thetaProdY (n2, n1)
      = monom (6 * Tn n2 + 3 * Tn n1) 0 (n2 + n1) ((-1) ^ (n2 + n1)) := by
  unfold thetaProdY
  show monom (thetaQDeg 6 0 n2) (0 * n2) (1 * n2) ((-1) ^ n2)
        * monom (thetaQDeg 3 0 n1) (0 * n1) (1 * n1) ((-1) ^ n1) = _
  rw [monom_mul]
  apply monom_eq_monom
  · unfold thetaQDeg; ring
  · ring
  · ring
  · rw [zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]

theorem coeffXY_thetaProdY_coeff (m a : ℤ) :
    (coeffXY (thetaY_q2 * thetaY_q) 0 m).coeff a
      = ∑ᶠ p : ℤ × ℤ,
          (monom (6 * Tn p.1 + 3 * Tn p.2) 0 (p.1 + p.2) ((-1) ^ (p.1 + p.2))).coeff (expQXY a 0 m) := by
  rw [coeffXY_coeff, coeffQXY, ← thetaProdY_hsum, HahnSeries.SummableFamily.coeff_hsum]
  apply finsum_congr
  rintro ⟨n2, n1⟩
  rw [thetaProdY_term]

/-- **Bare step-3 FE for the `y`-slice of `Θ(y;q²)·Θ(y;q)`.** -/
theorem thetaProdY_slice_fe (m : ℤ) :
    coeffXY (thetaY_q2 * thetaY_q) 0 (m + 3)
      = - Qpow (6 * m + 3) * coeffXY (thetaY_q2 * thetaY_q) 0 m := by
  apply HahnSeries.ext
  funext a
  rw [show - Qpow (6 * m + 3) * coeffXY (thetaY_q2 * thetaY_q) 0 m
        = - (Qpow (6 * m + 3) * coeffXY (thetaY_q2 * thetaY_q) 0 m) by ring]
  rw [HahnSeries.coeff_neg]
  rw [show (Qpow (6 * m + 3) * coeffXY (thetaY_q2 * thetaY_q) 0 m).coeff a
        = (coeffXY (thetaY_q2 * thetaY_q) 0 m).coeff (a - (6 * m + 3)) by
    unfold Qpow
    rw [HahnSeries.coeff_single_mul, one_mul]]
  rw [coeffXY_thetaProdY_coeff, coeffXY_thetaProdY_coeff]
  rw [← finsum_neg_distrib]
  rw [← finsum_comp_equiv ((Equiv.addRight (1 : ℤ)).prodCongr (Equiv.addRight (2 : ℤ)))]
  apply finsum_congr
  rintro ⟨n2, n1⟩
  simp only [Equiv.prodCongr_apply, Equiv.coe_addRight, Prod.map_apply]
  unfold monom
  rw [HahnSeries.coeff_single, HahnSeries.coeff_single]
  by_cases hxd : n2 + n1 = m
  · have hdeg : 6 * Tn (n2 + 1) + 3 * Tn (n1 + 2)
        = (6 * Tn n2 + 3 * Tn n1) + (6 * m + 3) := by
      rw [Tn_add_one, Tn_add_two]; rw [← hxd]; ring
    have hsign : ((-1 : ℚ)) ^ ((n2 + 1) + (n1 + 2)) = - (-1) ^ (n2 + n1) := by
      rw [show (n2 + 1) + (n1 + 2) = (n2 + n1) + 3 by ring,
        zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]
      norm_num
    have hxL : (n2 + 1) + (n1 + 2) = m + 3 := by omega
    have hL : (expQXY a 0 (m + 3)
          = expQXY (6 * Tn (n2 + 1) + 3 * Tn (n1 + 2)) 0 ((n2 + 1) + (n1 + 2)))
        ↔ a = 6 * Tn (n2 + 1) + 3 * Tn (n1 + 2) := by
      constructor
      · intro hc; exact (expQXY_inj hc).1
      · intro hc; rw [hc, hxL]
    have hR : (expQXY (a - (6 * m + 3)) 0 m = expQXY (6 * Tn n2 + 3 * Tn n1) 0 (n2 + n1))
        ↔ a = 6 * Tn (n2 + 1) + 3 * Tn (n1 + 2) := by
      constructor
      · intro hc; have h1 := (expQXY_inj hc).1; rw [hdeg]; omega
      · intro hc
        rw [show a - (6 * m + 3) = 6 * Tn n2 + 3 * Tn n1 by rw [hc, hdeg]; ring]
        rw [hxd]
    by_cases hcond : a = 6 * Tn (n2 + 1) + 3 * Tn (n1 + 2)
    · rw [if_pos (hL.mpr hcond), if_pos (hR.mpr hcond), hsign]
    · rw [if_neg (fun hc => hcond (hL.mp hc)), if_neg (fun hc => hcond (hR.mp hc)), neg_zero]
  · rw [if_neg ?_, if_neg ?_, neg_zero]
    · intro hc; exact hxd (by have := (expQXY_inj hc).2.2; omega)
    · intro hc; exact hxd (by have := (expQXY_inj hc).2.2; omega)

/-- The `y`-slice of `zwegersRHS_y` (mirror of `coeffXY_zwegersRHS_x`). -/
theorem coeffXY_zwegersRHS_y (l : ℤ) :
    coeffXY zwegersRHS_y 0 l
      = HahnSeries.single 1 (-1 : ℚ) * poch_q * coeffXY (thetaY_q2 * thetaY_q) 0 (l + 1) := by
  have hassoc : zwegersRHS_y
      = monom 1 0 (-1) (-1) * (embedQ poch_q * (thetaY_q2 * thetaY_q)) := by
    unfold zwegersRHS_y
    rw [show (- monom 1 0 (-1) 1 : S) = monom 1 0 (-1) (-1) by rw [← monom_neg_one]]
    ring
  rw [hassoc, coeffXY_monom_mul_y, coeffXY_embedQ_mul]
  rw [show l - (-1) = l + 1 by ring]
  rw [mul_assoc]

/-- Step-3 FE for the cleared LHS `y`-slice. -/
theorem zwegers_FE_LHS_y (n : ℤ) :
    coeffXY (embedQ poch_q2 * zwegersLHS_y) 0 (n + 3)
      = - Qpow (6 * n + 9) * coeffXY (embedQ poch_q2 * zwegersLHS_y) 0 n := by
  rw [coeffXY_embedQ_mul, coeffXY_embedQ_mul, zwegersLHS_y_slice_fe]
  ring

/-- Step-3 FE for the cleared RHS `y`-slice. -/
theorem zwegers_FE_RHS_y (n : ℤ) :
    coeffXY zwegersRHS_y 0 (n + 3)
      = - Qpow (6 * n + 9) * coeffXY zwegersRHS_y 0 n := by
  rw [coeffXY_zwegersRHS_y, coeffXY_zwegersRHS_y]
  rw [show (n + 3 + 1 : ℤ) = (n + 1) + 3 by ring]
  rw [thetaProdY_slice_fe]
  rw [show (6 * (n + 1) + 3 : ℤ) = 6 * n + 9 by ring]
  ring

/-- The cleared LHS lives in the `x⁰` plane (`y`-version). -/
theorem zwegers_xplane_LHS_y (i j : ℤ) (hi : i ≠ 0) (a : ℤ) :
    coeffQXY (embedQ poch_q2 * zwegersLHS_y) a i j = 0 :=
  ((XZeroSupported_embedQ poch_q2).mul XZeroSupported_zwegersLHS_y) a i j hi

/-- The cleared RHS lives in the `x⁰` plane (`y`-version). -/
theorem zwegers_xplane_RHS_y (i j : ℤ) (hi : i ≠ 0) (a : ℤ) :
    coeffQXY zwegersRHS_y a i j = 0 := by
  unfold zwegersRHS_y thetaY_q2 thetaY_q
  exact ((((XZeroSupported_monom 1 (-1) 1).neg.mul (XZeroSupported_embedQ poch_q)).mul
    (XZeroSupported_thetaMon 6 0 1 (by norm_num))).mul
    (XZeroSupported_thetaMon 3 0 1 (by norm_num))) a i j hi

/-! ### `y`-mirror slice reductions (identical to the `x`-side with the slots swapped). -/

/-- `y`-mirror of `coeffXY_thetaProdX_collapse`. -/
theorem coeffXY_thetaProdY_collapse (m a : ℤ) :
    (coeffXY (thetaY_q2 * thetaY_q) 0 m).coeff a
      = ∑ᶠ n : ℤ, (if 6 * Tn n + 3 * Tn (m - n) = a then ((-1 : ℚ) ^ m) else 0) := by
  rw [coeffXY_thetaProdY_coeff]
  have hg : ∀ p : ℤ × ℤ,
      (monom (6 * Tn p.1 + 3 * Tn p.2) 0 (p.1 + p.2) ((-1) ^ (p.1 + p.2))).coeff (expQXY a 0 m)
        = (if (6 * Tn p.1 + 3 * Tn p.2 = a ∧ p.1 + p.2 = m) then ((-1 : ℚ) ^ (p.1 + p.2)) else 0) := by
    rintro ⟨n2, n1⟩
    unfold monom
    rw [HahnSeries.coeff_single]
    by_cases hc : a = 6 * Tn n2 + 3 * Tn n1 ∧ m = n2 + n1
    · rw [if_pos (by rw [hc.1, hc.2]), if_pos ⟨hc.1.symm, hc.2.symm⟩]
    · rw [if_neg (by rintro he; exact hc ⟨(expQXY_inj he).1, (expQXY_inj he).2.2⟩)]
      rw [if_neg (by rintro ⟨h1, h2⟩; exact hc ⟨h1.symm, h2.symm⟩)]
  simp_rw [hg]
  have hfin : (Function.support
      (fun p : ℤ × ℤ => if (6 * Tn p.1 + 3 * Tn p.2 = a ∧ p.1 + p.2 = m) then ((-1 : ℚ) ^ (p.1 + p.2)) else 0)).Finite := by
    apply Set.Finite.subset (thetaProdY.finite_co_support' (expQXY a 0 m))
    rintro ⟨n2, n1⟩ hp
    simp only [Function.mem_support, ne_eq] at hp
    simp only [Set.mem_setOf_eq]
    show (thetaProdY (n2, n1)).coeff (expQXY a 0 m) ≠ 0
    rw [thetaProdY_term, hg (n2, n1)]
    exact hp
  rw [finsum_curry _ hfin]
  apply finsum_congr
  intro n
  rw [finsum_eq_single _ (m - n)]
  · simp only
    rw [show n + (m - n) = m by ring]
    by_cases hcond : 6 * Tn n + 3 * Tn (m - n) = a
    · rw [if_pos ⟨hcond, by ring⟩, if_pos hcond]
    · rw [if_neg (by rintro ⟨h1, _⟩; exact hcond h1), if_neg hcond]
  · intro s hs
    rw [if_neg]
    rintro ⟨_, h2⟩
    exact hs (by omega)

/-- `y`-mirror of `coeffXY_zwegersLHS_x_collapse`. -/
theorem coeffXY_zwegersLHS_y_collapse (l a : ℤ) :
    (coeffXY zwegersLHS_y 0 l).coeff a
      = ∑ᶠ k : ℤ, (if k ^ 2 + l ^ 2 = a then zW k l else 0) := by
  rw [coeffXY_zwegersLHS_y_coeff]
  have hg : ∀ p : ℤ × ℤ,
      (monom (p.1 ^ 2 + p.2 ^ 2) 0 p.2 (zW p.1 p.2)).coeff (expQXY a 0 l)
        = (if (p.1 ^ 2 + p.2 ^ 2 = a ∧ p.2 = l) then zW p.1 p.2 else 0) := by
    rintro ⟨k, s⟩
    unfold monom
    rw [HahnSeries.coeff_single]
    by_cases hc : a = k ^ 2 + s ^ 2 ∧ l = s
    · rw [if_pos (by rw [hc.1, hc.2]), if_pos ⟨hc.1.symm, hc.2.symm⟩]
    · rw [if_neg (by rintro he; exact hc ⟨(expQXY_inj he).1, (expQXY_inj he).2.2⟩)]
      rw [if_neg (by rintro ⟨h1, h2⟩; exact hc ⟨h1.symm, h2.symm⟩)]
  simp_rw [hg]
  have hfin : (Function.support
      (fun p : ℤ × ℤ => if (p.1 ^ 2 + p.2 ^ 2 = a ∧ p.2 = l) then zW p.1 p.2 else 0)).Finite := by
    apply Set.Finite.subset (zFamilyY.finite_co_support' (expQXY a 0 l))
    rintro ⟨k, s⟩ hp
    simp only [Function.mem_support, ne_eq] at hp
    simp only [Set.mem_setOf_eq]
    show (zFamilyY (k, s)).coeff (expQXY a 0 l) ≠ 0
    rw [show zFamilyY (k, s) = monom (k ^ 2 + s ^ 2) 0 s (zW k s) from rfl]
    rw [hg (k, s)]
    exact hp
  rw [finsum_curry _ hfin]
  apply finsum_congr
  intro k
  rw [finsum_eq_single _ l]
  · by_cases hcond : k ^ 2 + l ^ 2 = a
    · rw [if_pos ⟨hcond, rfl⟩, if_pos hcond]
    · rw [if_neg (by rintro ⟨h1, _⟩; exact hcond h1), if_neg hcond]
  · intro s hs
    rw [if_neg]
    rintro ⟨_, h2⟩
    exact hs h2

/-- `y`-mirror of `thetaProdX_slice_one`. -/
theorem thetaProdY_slice_one : coeffXY (thetaY_q2 * thetaY_q) 0 1 = - Jneg1 := by
  apply HahnSeries.ext; funext a
  rw [coeffXY_thetaProdY_collapse, HahnSeries.coeff_neg, Jneg1, JK_coeff, ← finsum_neg_distrib]
  apply finsum_congr; intro n
  rw [show 6 * Tn n + 3 * Tn (1 - n) = 9 * Tn n by rw [Tn_one_sub]; ring]
  rw [show thetaQDeg 9 0 n = 9 * Tn n by unfold thetaQDeg; ring]
  by_cases h : 9 * Tn n = a
  · rw [if_pos h, if_pos h]; norm_num
  · rw [if_neg h, if_neg h]; norm_num

/-- `y`-mirror of `thetaProdX_slice_two`. -/
theorem thetaProdY_slice_two : coeffXY (thetaY_q2 * thetaY_q) 0 2 = JnegQ6 := by
  apply HahnSeries.ext; funext a
  rw [coeffXY_thetaProdY_collapse, JnegQ6, JK_coeff]
  rw [← finsum_comp_equiv (Equiv.addRight (1 : ℤ))]
  apply finsum_congr; intro r
  simp only [Equiv.coe_addRight]
  have hdeg : 6 * Tn (r + 1) + 3 * Tn (2 - (r + 1)) = thetaQDeg 9 6 r := by
    rw [Tn_add_one, show (2 : ℤ) - (r + 1) = 1 - r by ring, Tn_one_sub]; unfold thetaQDeg; ring
  by_cases h : thetaQDeg 9 6 r = a
  · rw [if_pos (by rw [hdeg]; exact h), if_pos h]; norm_num
  · rw [if_neg (by rw [hdeg]; exact h), if_neg h]

/-- `y`-mirror of `thetaProdX_slice_three`. -/
theorem thetaProdY_slice_three :
    coeffXY (thetaY_q2 * thetaY_q) 0 3 = HahnSeries.single 3 (-1 : ℚ) * JnegQ6 := by
  apply HahnSeries.ext; funext a
  rw [coeffXY_thetaProdY_collapse]
  have hsm : (HahnSeries.single (3 : ℤ) (-1 : ℚ) * JnegQ6).coeff a = - JnegQ6.coeff (a - 3) := by
    rw [HahnSeries.coeff_single_mul]; ring
  rw [hsm, JnegQ6, JK_coeff, ← finsum_neg_distrib]
  rw [← finsum_comp_equiv (Equiv.subLeft (1 : ℤ))]
  apply finsum_congr; intro r
  simp only [Equiv.subLeft_apply]
  have hdeg : 6 * Tn (1 - r) + 3 * Tn (3 - (1 - r)) = thetaQDeg 9 6 r + 3 := by
    rw [Tn_one_sub, show (3 : ℤ) - (1 - r) = r + 2 by ring, Tn_add_two]; unfold thetaQDeg; ring
  by_cases h : thetaQDeg 9 6 r = a - 3
  · rw [if_pos (by rw [hdeg]; omega), if_pos h]; norm_num
  · rw [if_neg (by rw [hdeg]; omega), if_neg h]; norm_num

/-- `y`-mirror of `zwegersLHS_x_slice_zero`. -/
theorem zwegersLHS_y_slice_zero :
    coeffXY zwegersLHS_y 0 0 = HahnSeries.single 1 (2 : ℚ) * JQ15 := by
  apply HahnSeries.ext; funext a
  rw [coeffXY_zwegersLHS_y_collapse]
  have hsm : (HahnSeries.single (1 : ℤ) (2 : ℚ) * JQ15).coeff a = 2 * JQ15.coeff (a - 1) := by
    rw [HahnSeries.coeff_single_mul]
  rw [hsm, JQ15, JK_coeff]
  set g : ℤ → ℚ := fun k => if k ^ 2 + 0 ^ 2 = a then zW k 0 else 0 with hg
  have hgsub : Function.support g ⊆ {k : ℤ | k ^ 2 = a} := by
    intro k hk
    simp only [hg, Function.mem_support, ne_eq] at hk
    simp only [Set.mem_setOf_eq]
    by_contra h
    apply hk; rw [if_neg (by simpa using h)]
  have hsqfin : {k : ℤ | k ^ 2 = a}.Finite := by
    apply Set.Finite.subset (Set.finite_Icc (-(a^2+a+1)) (a^2+a+1))
    intro k hk; simp only [Set.mem_setOf_eq] at hk; simp only [Set.mem_Icc]
    constructor <;> nlinarith [sq_nonneg (k-1), sq_nonneg (k+1), hk, sq_nonneg k, sq_nonneg a]
  have hgfin : (Function.support g).Finite := hsqfin.subset hgsub
  have hsupp3 : Function.support g ⊆ {k : ℤ | ¬ (3 : ℤ) ∣ k} := by
    intro k hk
    simp only [hg, Function.mem_support, ne_eq] at hk
    simp only [Set.mem_setOf_eq]
    intro hd
    apply hk
    by_cases h : k ^ 2 + 0 ^ 2 = a
    · rw [if_pos h, zW_zero_off k hd]
    · rw [if_neg h]
  have hcover : {k : ℤ | ¬ (3 : ℤ) ∣ k}
      = Set.range (fun r : ℤ => 3 * r + 1) ∪ Set.range (fun r : ℤ => 3 * r + 2) := by
    ext k; simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_range]
    constructor
    · intro hd
      have h3 : k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases h3 with h | h
      · exact Or.inl ⟨k / 3, by omega⟩
      · exact Or.inr ⟨k / 3, by omega⟩
    · rintro (⟨r, rfl⟩ | ⟨r, rfl⟩) <;> omega
  have hdisj : Disjoint (Set.range (fun r : ℤ => 3 * r + 1)) (Set.range (fun r : ℤ => 3 * r + 2)) := by
    rw [Set.disjoint_left]
    rintro k ⟨r, rfl⟩ ⟨s, hs⟩; simp only [] at hs; omega
  rw [show (∑ᶠ k : ℤ, g k) = ∑ᶠ k ∈ {k : ℤ | ¬ (3 : ℤ) ∣ k}, g k by
    rw [← finsum_mem_inter_support, Set.inter_eq_right.mpr hsupp3,
        ← Set.univ_inter (Function.support g), finsum_mem_inter_support, finsum_mem_univ]]
  rw [hcover]
  rw [finsum_mem_union' hdisj
      (hgfin.subset (Set.inter_subset_right))
      (hgfin.subset (Set.inter_subset_right))]
  rw [finsum_mem_range (fun a b h => by simpa using h),
      finsum_mem_range (fun a b h => by simpa using h)]
  have hbranch1 : (∑ᶠ r : ℤ, g (3 * r + 1)) = ∑ᶠ r : ℤ, (if thetaQDeg 18 15 r = a - 1 then (-1 : ℚ) ^ r else 0) := by
    apply finsum_congr; intro r
    simp only [hg]
    rw [show (3 * r + 1) ^ 2 + 0 ^ 2 = thetaQDeg 18 15 r + 1 by rw [thetaQDeg_18_15]; ring]
    by_cases h : thetaQDeg 18 15 r = a - 1
    · rw [if_pos (by omega), if_pos h, zW_three_one]
    · rw [if_neg (by omega), if_neg h]
  have hbranch2 : (∑ᶠ r : ℤ, g (3 * r + 2)) = ∑ᶠ r : ℤ, (if thetaQDeg 18 15 r = a - 1 then (-1 : ℚ) ^ r else 0) := by
    rw [← finsum_comp_equiv (Equiv.subLeft (-1 : ℤ))]
    apply finsum_congr; intro r
    simp only [hg, Equiv.subLeft_apply]
    rw [show 3 * (-1 - r) + 2 = -(3 * r + 1) by ring]
    rw [show (-(3 * r + 1)) ^ 2 + 0 ^ 2 = thetaQDeg 18 15 r + 1 by rw [thetaQDeg_18_15]; ring]
    by_cases h : thetaQDeg 18 15 r = a - 1
    · rw [if_pos (by omega), if_pos h, zW_neg_three_one]
    · rw [if_neg (by omega), if_neg h]
  rw [hbranch1, hbranch2]; ring

/-- `y`-mirror of `zwegersLHS_x_slice_one`. -/
theorem zwegersLHS_y_slice_one :
    coeffXY zwegersLHS_y 0 1 = HahnSeries.single 1 (-1 : ℚ) * JQ9 := by
  apply HahnSeries.ext; funext a
  rw [coeffXY_zwegersLHS_y_collapse]
  have hsm : (HahnSeries.single (1 : ℤ) (-1 : ℚ) * JQ9).coeff a = - JQ9.coeff (a - 1) := by
    rw [HahnSeries.coeff_single_mul]; ring
  rw [hsm, JQ9, JK_coeff, ← finsum_neg_distrib]
  rw [finsum_multiples_three (fun k => if k ^ 2 + 1 ^ 2 = a then zW k 1 else 0)
      (fun k hk => by
        simp only
        by_cases h : k ^ 2 + 1 ^ 2 = a
        · rw [if_pos h, zW_one_off k hk]
        · rw [if_neg h])]
  apply finsum_congr; intro r
  have hz : zW (3 * r) 1 = - (-1 : ℚ) ^ r := by
    unfold zW delta3
    rw [if_pos (Dvd.intro r rfl : (3 : ℤ) ∣ 3 * r), if_neg (by decide : ¬ (3 : ℤ) ∣ 1)]
    rw [show (3 : ℤ) * r + 1 = (3 * r) + 1 by ring, zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0),
        negOne_zpow_three_mul]
    norm_num
  have hdeg : (3 * r) ^ 2 + 1 ^ 2 = thetaQDeg 18 9 r + 1 := by rw [thetaQDeg_18_9]; ring
  by_cases h : thetaQDeg 18 9 r = a - 1
  · rw [if_pos (by rw [hdeg]; omega), if_pos h, hz]
  · rw [if_neg (by rw [hdeg]; omega), if_neg h, neg_zero]

/-- `y`-mirror of `zwegersLHS_x_slice_two`. -/
theorem zwegersLHS_y_slice_two :
    coeffXY zwegersLHS_y 0 2 = HahnSeries.single 4 (1 : ℚ) * JQ9 := by
  apply HahnSeries.ext; funext a
  rw [coeffXY_zwegersLHS_y_collapse]
  have hsm : (HahnSeries.single (4 : ℤ) (1 : ℚ) * JQ9).coeff a = JQ9.coeff (a - 4) := by
    rw [HahnSeries.coeff_single_mul]; ring
  rw [hsm, JQ9, JK_coeff]
  rw [finsum_multiples_three (fun k => if k ^ 2 + 2 ^ 2 = a then zW k 2 else 0)
      (fun k hk => by
        simp only
        by_cases h : k ^ 2 + 2 ^ 2 = a
        · rw [if_pos h, zW_two_off k hk]
        · rw [if_neg h])]
  apply finsum_congr; intro r
  have hz : zW (3 * r) 2 = (-1 : ℚ) ^ r := by
    unfold zW delta3
    rw [if_pos (Dvd.intro r rfl : (3 : ℤ) ∣ 3 * r), if_neg (by decide : ¬ (3 : ℤ) ∣ 2)]
    rw [show (3 : ℤ) * r + 2 = (3 * r) + 2 by ring, zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0),
        negOne_zpow_three_mul]
    norm_num
  have hdeg : (3 * r) ^ 2 + 2 ^ 2 = thetaQDeg 18 9 r + 4 := by rw [thetaQDeg_18_9]; ring
  by_cases h : thetaQDeg 18 9 r = a - 4
  · rw [if_pos (by rw [hdeg]; omega), if_pos h, hz]
  · rw [if_neg (by rw [hdeg]; omega), if_neg h]

/-- The `y`-version analytic core of the three initial coefficient agreements, reduced via the
slicing lemmas to the two product identities `init_product_P0`/`init_product_P12`.
Numerically verified for `j = 0,1,2`. -/
theorem zwegers_init_y_core (j : ℤ) (hj : j = 0 ∨ j = 1 ∨ j = 2) :
    poch_q2 * coeffXY zwegersLHS_y 0 j
      = HahnSeries.single 1 (-1 : ℚ) * poch_q * coeffXY (thetaY_q2 * thetaY_q) 0 (j + 1) := by
  have hs12 : (HahnSeries.single (1 : ℤ) (2 : ℚ))
      = - (HahnSeries.single (1 : ℤ) (-1 : ℚ)) * HahnSeries.single (0 : ℤ) (2 : ℚ) := by
    rw [neg_mul, HahnSeries.single_mul_single]; norm_num
  have hs41 : (HahnSeries.single (4 : ℤ) (1 : ℚ))
      = HahnSeries.single (1 : ℤ) (-1 : ℚ) * HahnSeries.single (3 : ℤ) (-1 : ℚ) := by
    rw [HahnSeries.single_mul_single]; norm_num
  rcases hj with rfl | rfl | rfl
  · rw [zwegersLHS_y_slice_zero, show ((0 : ℤ) + 1) = 1 by ring, thetaProdY_slice_one]
    rw [hs12]
    rw [show HahnSeries.single (1 : ℤ) (-1 : ℚ) * poch_q * (-Jneg1)
          = - (HahnSeries.single (1 : ℤ) (-1 : ℚ) * (poch_q * Jneg1)) by ring]
    rw [init_product_P0]
    ring
  · rw [zwegersLHS_y_slice_one, show ((1 : ℤ) + 1) = 2 by ring, thetaProdY_slice_two]
    rw [show poch_q2 * (HahnSeries.single (1 : ℤ) (-1 : ℚ) * JQ9)
          = HahnSeries.single (1 : ℤ) (-1 : ℚ) * (poch_q2 * JQ9) by ring,
        ← init_product_P12]
    ring
  · rw [zwegersLHS_y_slice_two, show ((2 : ℤ) + 1) = 3 by ring, thetaProdY_slice_three]
    rw [hs41]
    rw [show poch_q2 * (HahnSeries.single (1 : ℤ) (-1 : ℚ) * HahnSeries.single (3 : ℤ) (-1 : ℚ) * JQ9)
          = HahnSeries.single (1 : ℤ) (-1 : ℚ) * HahnSeries.single (3 : ℤ) (-1 : ℚ) * (poch_q2 * JQ9) by ring,
        ← init_product_P12]
    ring

/-- The three initial `y`-coefficients agree (`y`-version).  Reduced via the slicing lemmas to
the isolated core `zwegers_init_y_core`. -/
theorem zwegers_init_y (j : ℤ) (hj : j = 0 ∨ j = 1 ∨ j = 2) :
    coeffXY (embedQ poch_q2 * zwegersLHS_y) 0 j = coeffXY zwegersRHS_y 0 j := by
  rw [coeffXY_embedQ_mul, coeffXY_zwegersRHS_y]
  exact zwegers_init_y_core j hj

/-- **Zwegers' Lemma 10.1 (`y`-version), `poch_q2`-cleared** (mirror of the `x`-version,
proved unconditionally from the `y`-analytic inputs above). -/
theorem zwegers_lemma_10_1_y :
    embedQ poch_q2 * zwegersLHS_y = zwegersRHS_y := by
  set F := embedQ poch_q2 * zwegersLHS_y with hFdef
  set G := zwegersRHS_y with hGdef
  set d : ℤ → K := fun n => coeffXY F 0 n - coeffXY G 0 n with hd
  have hdrec : ∀ n, d (n + 3) = - Qpow (6 * n + 9) * d n := by
    intro n; simp only [hd]; rw [zwegers_FE_LHS_y n, zwegers_FE_RHS_y n]; ring
  have hzeros := coeff_eq_zero_of_fe_step3 d hdrec
    (by simp only [hd]; rw [zwegers_init_y 0 (by tauto)]; ring)
    (by simp only [hd]; rw [zwegers_init_y 1 (by tauto)]; ring)
    (by simp only [hd]; rw [zwegers_init_y 2 (by tauto)]; ring)
  have hyeq : ∀ n, coeffXY F 0 n = coeffXY G 0 n := by
    intro n; have := hzeros n; simp only [hd] at this; exact sub_eq_zero.mp this
  apply ext_coeffQXY
  intro a i j
  by_cases hi : i = 0
  · subst hi
    have hF := congrArg (fun (s : K) => s.coeff a) (hyeq j)
    simpa only [coeffXY_coeff] using hF
  · rw [zwegers_xplane_LHS_y i j hi a, zwegers_xplane_RHS_y i j hi a]

/-! ## Layer F — Hickerson Lemma 10.2 via ρ-line strings

The multiplied form of Hickerson's Lemma 10.2:
`Θ(x;q) · Θ(y;q) · Rho = (q;q)∞³ · Θ(xy; q)` (in our normalisation
`thetaX_q * thetaY_q * Rho = embedQ (poch_q^3) * thetaMon 3 0 1 1`).

`Rho` is the two-variable Hahn series whose `Q^{3rs} x^r y^s` coefficient is the
ρ-line sign `ρ(r,s)` (`1` on the closed first quadrant, `-1` on the open third
quadrant, `0` elsewhere).  Its support is the union of the two nonnegative axes
(at `Q`-degree `0`) together with finite divisor fibres at each positive `Q`-degree,
which is partially well-ordered in the `q`-first lexicographic order. -/

/-- The ρ-line sign: `1` on the closed first quadrant, `-1` on the open third
quadrant, `0` otherwise. -/
def rho (r s : ℤ) : ℚ :=
  if 0 ≤ r ∧ 0 ≤ s then 1 else if r < 0 ∧ s < 0 then -1 else 0

theorem rho_eq_zero_of_mixed {r s : ℤ} (h : ¬ (0 ≤ r ∧ 0 ≤ s) ∧ ¬ (r < 0 ∧ s < 0)) :
    rho r s = 0 := by
  unfold rho; rw [if_neg h.1, if_neg h.2]

/-- On the support of `ρ`, the product `r·s` is nonnegative (closed-1st or open-3rd
quadrant), so the candidate `Q`-degree `3·r·s` is `≥ 0`. -/
theorem rho_support_nonneg_q {r s : ℤ} (h : rho r s ≠ 0) : 0 ≤ 3 * r * s := by
  unfold rho at h
  by_cases h1 : 0 ≤ r ∧ 0 ≤ s
  · have hrs : 0 ≤ r * s := mul_nonneg h1.1 h1.2
    nlinarith [hrs]
  · rw [if_neg h1] at h
    by_cases h2 : r < 0 ∧ s < 0
    · have hrs : 0 ≤ r * s := by nlinarith [h2.1, h2.2]
      nlinarith [hrs]
    · rw [if_neg h2] at h; exact absurd rfl h

/-- The `Q`-degree-`0` fibre of `ρ`: `3·r·s = 0` and `ρ r s ≠ 0` force one coordinate to be
`0` and the other nonnegative — i.e. the two nonnegative coordinate axes. -/
theorem rho_q_zero_fiber {r s : ℤ} (hq : 3 * r * s = 0) (h : rho r s ≠ 0) :
    (r = 0 ∧ 0 ≤ s) ∨ (s = 0 ∧ 0 ≤ r) := by
  have hrs : r * s = 0 := by
    have : 3 * (r * s) = 0 := by linarith [hq]
    omega
  rcases mul_eq_zero.mp hrs with hr | hs
  · left
    refine ⟨hr, ?_⟩
    unfold rho at h
    by_cases h1 : 0 ≤ r ∧ 0 ≤ s
    · exact h1.2
    · rw [if_neg h1] at h
      by_cases h2 : r < 0 ∧ s < 0
      · omega
      · rw [if_neg h2] at h; exact absurd rfl h
  · right
    refine ⟨hs, ?_⟩
    unfold rho at h
    by_cases h1 : 0 ≤ r ∧ 0 ≤ s
    · exact h1.1
    · rw [if_neg h1] at h
      by_cases h2 : r < 0 ∧ s < 0
      · omega
      · rw [if_neg h2] at h; exact absurd rfl h

/-- The `Q`-degree-`N` fibre of `ρ` for `N > 0` is finite (divisor pairs of `N/3`). -/
theorem rho_positive_q_fiber_finite {N : ℤ} (hN : 0 < N) :
    {p : ℤ × ℤ | 3 * p.1 * p.2 = N ∧ rho p.1 p.2 ≠ 0}.Finite := by
  -- both coordinates are bounded by N in absolute value (since |r|,|s| ≥ 1 and |r·s| = N/3 ≤ N).
  apply Set.Finite.subset (Set.finite_Icc ((-N, -N) : ℤ × ℤ) ((N, N) : ℤ × ℤ))
  rintro ⟨r, s⟩ ⟨hq, hne⟩
  simp only at hq hne
  have hrs_pos : 0 < r * s := by nlinarith [hN, hq]
  have hr_le : r * s ≤ N := by
    have : 3 * (r * s) = N := by linarith [hq]
    omega
  rw [Set.mem_Icc, Prod.le_def, Prod.le_def]
  -- r and s have the same sign (product positive); each has |·| ≤ |r·s| ≤ N.
  rcases (mul_pos_iff.mp hrs_pos) with ⟨hrp, hsp⟩ | ⟨hrn, hsn⟩
  · -- both positive: 1 ≤ r, 1 ≤ s ⟹ r ≤ r*s ≤ N, s ≤ r*s ≤ N.
    refine ⟨⟨by linarith [hrp, hN], by linarith [hsp, hN]⟩,
      by nlinarith [hrp, hsp, hr_le], by nlinarith [hrp, hsp, hr_le]⟩
  · -- both negative: r ≤ -1, s ≤ -1 ⟹ -r ≤ r*s ≤ N i.e. r ≥ -N, similarly s ≥ -N.
    refine ⟨⟨by nlinarith [hrn, hsn, hr_le], by nlinarith [hrn, hsn, hr_le]⟩,
      by linarith [hrn, hN], by linarith [hsn, hN]⟩

/-- The two nonnegative coordinate axes in `ExpXY = Lex (ℤ × ℤ)` are partially well-ordered. -/
theorem axes_isPWO :
    {y : ExpXY | (((ofLex y).1 = 0 ∧ 0 ≤ (ofLex y).2) ∨
        ((ofLex y).2 = 0 ∧ 0 ≤ (ofLex y).1))}.IsPWO := by
  apply Set.PartiallyWellOrderedOn.subsetProdLex
  · -- x-degree projection ⊆ Ici 0.
    have hsub : (fun (x : ℤ ×ₗ ℤ) => (ofLex x).1) ''
        {y : ExpXY | (((ofLex y).1 = 0 ∧ 0 ≤ (ofLex y).2) ∨
          ((ofLex y).2 = 0 ∧ 0 ≤ (ofLex y).1))} ⊆ Set.Ici (0 : ℤ) := by
      rintro a ⟨y, hy, rfl⟩
      simp only [Set.mem_Ici]
      rcases hy with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact le_of_eq h1.symm
      · exact h2
    refine (?_ : (Set.Ici (0 : ℤ)).IsPWO).mono hsub
    exact (bddBelow_Ici.isWF).isPWO
  · -- fibre at x-degree `a`: `Ici 0` (a = 0, PWO) or ⊆ {0} (a > 0, finite) or ∅ (a < 0).
    intro a
    by_cases ha : a = 0
    · -- a = 0: fibre = {j : 0 ≤ j} = Ici 0, which is PWO.
      apply (bddBelow_Ici (a := (0 : ℤ))).isWF.isPWO.mono
      intro j hj
      simp only [Set.mem_setOf_eq, ofLex_toLex] at hj
      rw [Set.mem_Ici]
      rcases hj with ⟨_, h2⟩ | ⟨h2, h3⟩
      · exact h2
      · omega
    · -- a ≠ 0: fibre ⊆ {0}, finite hence PWO.
      apply Set.Finite.isPWO
      apply Set.Finite.subset (Set.finite_singleton (0 : ℤ))
      intro j hj
      simp only [Set.mem_setOf_eq, ofLex_toLex] at hj
      rcases hj with ⟨h1, _⟩ | ⟨h2, _⟩
      · exact absurd h1 ha
      · exact h2

/-- The defining coefficient of `Rho`: `ρ(r,s)` at the exponent `Q^{3rs} x^r y^s`, `0` elsewhere. -/
noncomputable def rhoCoeff (z : ExpQXY) : ℚ :=
  if (ofLex z).1 = 3 * (ofLex (ofLex z).2).1 * (ofLex (ofLex z).2).2
  then rho (ofLex (ofLex z).2).1 (ofLex (ofLex z).2).2 else 0

/-- The support of `rhoCoeff` is partially well-ordered in the `q`-first lex order. -/
theorem rhoCoeff_isPWO : (Function.support rhoCoeff).IsPWO := by
  apply Set.PartiallyWellOrderedOn.subsetProdLex
  · -- q-degree projection ⊆ Ici 0 (on the support, qDeg = 3rs ≥ 0).
    have hsub : (fun (z : ℤ ×ₗ ExpXY) => (ofLex z).1) '' Function.support rhoCoeff
        ⊆ Set.Ici (0 : ℤ) := by
      rintro a ⟨z, hz, rfl⟩
      simp only [Function.mem_support, rhoCoeff] at hz
      simp only [Set.mem_Ici]
      by_cases hc : (ofLex z).1 = 3 * (ofLex (ofLex z).2).1 * (ofLex (ofLex z).2).2
      · rw [if_pos hc] at hz
        rw [hc]
        exact rho_support_nonneg_q hz
      · rw [if_neg hc] at hz; exact absurd rfl hz
    refine (?_ : (Set.Ici (0 : ℤ)).IsPWO).mono hsub
    exact (bddBelow_Ici.isWF).isPWO
  · -- fibre at q-degree N: axes (N = 0) / finite (N > 0) / empty (N < 0).
    intro N
    by_cases hN : 0 < N
    · -- N > 0: finite fibre.
      apply Set.Finite.isPWO
      apply Set.Finite.subset
        (Set.Finite.image (fun p : ℤ × ℤ => (toLex (p.1, p.2) : ExpXY))
          (rho_positive_q_fiber_finite hN))
      intro y hy
      simp only [Set.mem_setOf_eq, Function.mem_support] at hy
      -- hy : rhoCoeff (toLex (N, y)) ≠ 0.
      rw [rhoCoeff, ofLex_toLex] at hy
      by_cases hc : N = 3 * (ofLex y).1 * (ofLex y).2
      · refine ⟨((ofLex y).1, (ofLex y).2), ⟨hc.symm, ?_⟩, rfl⟩
        rw [if_pos hc] at hy
        exact hy
      · rw [if_neg hc] at hy; exact absurd rfl hy
    · -- N ≤ 0: split into N = 0 (axes) and N < 0 (empty).
      push_neg at hN
      rcases lt_or_eq_of_le hN with hlt | heq
      · -- N < 0: empty fibre.
        apply Set.Finite.isPWO
        convert Set.finite_empty
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Function.mem_support]
        rw [rhoCoeff, ofLex_toLex]
        by_cases hc : N = 3 * (ofLex y).1 * (ofLex y).2
        · rw [if_pos hc]
          intro hne
          have hge := rho_support_nonneg_q hne
          rw [← hc] at hge
          omega
        · rw [if_neg hc]; exact fun h => h rfl
      · -- N = 0: fibre ⊆ axes (PWO).
        subst heq
        apply axes_isPWO.mono
        intro y hy
        simp only [Set.mem_setOf_eq, Function.mem_support] at hy
        rw [rhoCoeff, ofLex_toLex] at hy
        by_cases hc : (0 : ℤ) = 3 * (ofLex y).1 * (ofLex y).2
        · rw [if_pos hc] at hy
          exact rho_q_zero_fiber (by linarith [hc]) hy
        · rw [if_neg hc] at hy; exact absurd rfl hy

/-- `Rho`: the two-variable Hahn series with coefficient `ρ(r,s)` at `Q^{3rs} x^r y^s`. -/
noncomputable def Rho : S where
  coeff := rhoCoeff
  isPWO_support' := rhoCoeff_isPWO

/-- The `Q^a x^i y^j` coefficient of `Rho`. -/
theorem coeffQXY_Rho (a i j : ℤ) :
    coeffQXY Rho a i j = if a = 3 * i * j then rho i j else 0 := by
  unfold coeffQXY Rho
  show rhoCoeff (expQXY a i j) = _
  rw [rhoCoeff]
  rw [qdeg_expQXY, xdeg_expQXY, ydeg_expQXY]

/-! ### String machinery: `StringSumQ` -/

/-- The ρ-line string sum `∑'_s Q^{3ds} ρ(m-s, s)` in `K = ℚ((Q))`.  The string support
`{s : ρ(m-s,s) ≠ 0}` is a finite interval, so this finsum is a genuine finite sum. -/
noncomputable def StringSumQ (m d : ℤ) : K :=
  ∑ᶠ s : ℤ, HahnSeries.single (3 * d * s) (rho (m - s) s)

/-- The string support `{s : ρ(m-s,s) ≠ 0}` is finite (a contiguous interval). -/
theorem stringSupp_finite (m : ℤ) : {s : ℤ | rho (m - s) s ≠ 0}.Finite := by
  apply Set.Finite.subset (Set.finite_Icc (min 0 (m + 1)) (max m (-1)))
  intro s hs
  simp only [Set.mem_setOf_eq] at hs
  rw [Set.mem_Icc]
  unfold rho at hs
  by_cases h1 : 0 ≤ m - s ∧ 0 ≤ s
  · constructor <;> omega
  · rw [if_neg h1] at hs
    by_cases h2 : m - s < 0 ∧ s < 0
    · constructor <;> omega
    · rw [if_neg h2] at hs; exact absurd rfl hs

/-- The support of the summand `s ↦ single (3ds) ρ(m-s,s)` is contained in the string support. -/
theorem stringSummand_support_finite (m d : ℤ) :
    (Function.support (fun s : ℤ => HahnSeries.single (3 * d * s) (rho (m - s) s))).Finite := by
  apply (stringSupp_finite m).subset
  intro s hs
  simp only [Function.mem_support] at hs
  simp only [Set.mem_setOf_eq]
  intro hc
  apply hs
  rw [hc, HahnSeries.single_eq_zero]

/-- Away from `s = m+1`, the ρ-line values at consecutive `m`s agree:
`rho (m+1-s) s = rho (m-s) s`.  (The string only changes by one term when `m → m+1`.) -/
theorem rho_agree_succ (m s : ℤ) (hs : s ≠ m + 1) : rho (m + 1 - s) s = rho (m - s) s := by
  unfold rho
  by_cases hs0 : 0 ≤ s
  · -- s ≥ 0: third-quadrant branch never fires on either side.
    rw [if_neg (show ¬(m + 1 - s < 0 ∧ s < 0) by rintro ⟨_, h⟩; omega),
        if_neg (show ¬(m - s < 0 ∧ s < 0) by rintro ⟨_, h⟩; omega)]
    by_cases h1 : 0 ≤ m + 1 - s
    · rw [if_pos (show 0 ≤ m + 1 - s ∧ 0 ≤ s from ⟨h1, hs0⟩),
          if_pos (show 0 ≤ m - s ∧ 0 ≤ s from ⟨by omega, hs0⟩)]
    · rw [if_neg (show ¬(0 ≤ m + 1 - s ∧ 0 ≤ s) by rintro ⟨h, _⟩; omega),
          if_neg (show ¬(0 ≤ m - s ∧ 0 ≤ s) by rintro ⟨h, _⟩; omega)]
  · -- s < 0: first-quadrant branch never fires on either side.
    push_neg at hs0
    rw [if_neg (show ¬(0 ≤ m + 1 - s ∧ 0 ≤ s) by rintro ⟨_, h⟩; omega),
        if_neg (show ¬(0 ≤ m - s ∧ 0 ≤ s) by rintro ⟨_, h⟩; omega)]
    by_cases h1 : m + 1 - s < 0
    · rw [if_pos (show m + 1 - s < 0 ∧ s < 0 from ⟨h1, hs0⟩),
          if_pos (show m - s < 0 ∧ s < 0 from ⟨by omega, hs0⟩)]
    · rw [if_neg (show ¬(m + 1 - s < 0 ∧ s < 0) by rintro ⟨h, _⟩; omega),
          if_neg (show ¬(m - s < 0 ∧ s < 0) by rintro ⟨h, _⟩; omega)]

/-- Away from `s = m`, the ρ-line values at `m-1` and `m` agree:
`rho (m-1-s) s = rho (m-s) s`. -/
theorem rho_agree_pred (m s : ℤ) (hs : s ≠ m) : rho (m - 1 - s) s = rho (m - s) s := by
  have := rho_agree_succ (m - 1) s (by omega)
  rw [show (m - 1) + 1 - s = m - s by ring] at this
  rw [this]

/-- A finsum of `single`s indexed by a pointwise difference that is supported at a single
index `s₀` collapses to that single term. -/
theorem finsum_single_diff (f : ℤ → ℚ) (s₀ : ℤ) (c : ℚ) (D : ℤ → ℤ)
    (hf : ∀ s, f s = if s = s₀ then c else 0) :
    (∑ᶠ s : ℤ, HahnSeries.single (D s) (f s)) = HahnSeries.single (D s₀) c := by
  rw [finsum_eq_single _ s₀ ?_]
  · rw [hf s₀, if_pos rfl]
  · intro s hs
    rw [hf s, if_neg hs, HahnSeries.single_eq_zero]

/-- **Upward recurrence** (for `m ≥ 0`):
`StringSumQ (m+1) d = StringSumQ m d + single (3d(m+1)) 1`. -/
theorem StringSumQ_succ (m d : ℤ) (hm : 0 ≤ m) :
    StringSumQ (m + 1) d = StringSumQ m d + HahnSeries.single (3 * d * (m + 1)) 1 := by
  have hdiff : StringSumQ (m + 1) d - StringSumQ m d
      = HahnSeries.single (3 * d * (m + 1)) 1 := by
    unfold StringSumQ
    rw [← finsum_sub_distrib (stringSummand_support_finite (m + 1) d)
      (stringSummand_support_finite m d)]
    have hcong : (fun s : ℤ => HahnSeries.single (3 * d * s) (rho (m + 1 - s) s)
        - HahnSeries.single (3 * d * s) (rho (m - s) s))
        = fun s : ℤ => HahnSeries.single (3 * d * s) (rho (m + 1 - s) s - rho (m - s) s) := by
      funext s; rw [HahnSeries.single_sub]
    rw [hcong]
    rw [finsum_single_diff (fun s => rho (m + 1 - s) s - rho (m - s) s) (m + 1) 1
      (fun s => 3 * d * s) ?_]
    · intro s
      simp only []
      -- rho(m+1-s,s) - rho(m-s,s) = if s = m+1 then 1 else 0  (for m ≥ 0).
      by_cases hs : s = m + 1
      · subst hs
        rw [if_pos rfl]
        -- rho(0, m+1) - rho(-1, m+1) = 1 - 0
        rw [show rho (m + 1 - (m + 1)) (m + 1) = (1 : ℚ) by
          unfold rho; rw [if_pos ⟨by omega, by omega⟩]]
        rw [show rho (m - (m + 1)) (m + 1) = (0 : ℚ) by
          unfold rho; rw [if_neg (by rintro ⟨h, _⟩; omega), if_neg (by rintro ⟨_, h⟩; omega)]]
        ring
      · rw [if_neg hs]
        rw [rho_agree_succ m s hs]
        ring
  rw [sub_eq_iff_eq_add] at hdiff
  rw [hdiff, add_comm]

/-- **Downward recurrence** (for `m ≤ 0`):
`StringSumQ (m-1) d = StringSumQ m d + single (3dm) (-1)`. -/
theorem StringSumQ_pred (m d : ℤ) (hm : m ≤ 0) :
    StringSumQ (m - 1) d = StringSumQ m d + HahnSeries.single (3 * d * m) (-1) := by
  have hdiff : StringSumQ (m - 1) d - StringSumQ m d
      = HahnSeries.single (3 * d * m) (-1) := by
    unfold StringSumQ
    rw [← finsum_sub_distrib (stringSummand_support_finite (m - 1) d)
      (stringSummand_support_finite m d)]
    have hcong : (fun s : ℤ => HahnSeries.single (3 * d * s) (rho (m - 1 - s) s)
        - HahnSeries.single (3 * d * s) (rho (m - s) s))
        = fun s : ℤ => HahnSeries.single (3 * d * s) (rho (m - 1 - s) s - rho (m - s) s) := by
      funext s; rw [HahnSeries.single_sub]
    rw [hcong]
    rw [finsum_single_diff (fun s => rho (m - 1 - s) s - rho (m - s) s) m (-1)
      (fun s => 3 * d * s) ?_]
    · intro s
      simp only []
      by_cases hs : s = m
      · subst hs
        rw [if_pos rfl]
        -- rho(-1, s) - rho(0, s) = -1  (s ≤ 0): s < 0 gives -1 - 0; s = 0 gives 0 - 1.
        have h1 : rho (s - 1 - s) s = (if s = 0 then (0 : ℚ) else -1) := by
          rw [show s - 1 - s = (-1 : ℤ) by ring]
          unfold rho
          rw [if_neg (show ¬(0 ≤ (-1 : ℤ) ∧ 0 ≤ s) by rintro ⟨h, _⟩; omega)]
          by_cases hm0 : s = 0
          · rw [if_pos hm0, if_neg (show ¬((-1 : ℤ) < 0 ∧ s < 0) by rintro ⟨_, h⟩; omega)]
          · rw [if_neg hm0, if_pos (show (-1 : ℤ) < 0 ∧ s < 0 from ⟨by omega, by omega⟩)]
        have h2 : rho (s - s) s = (if s = 0 then (1 : ℚ) else 0) := by
          rw [show s - s = (0 : ℤ) by ring]
          unfold rho
          by_cases hm0 : s = 0
          · rw [if_pos hm0, if_pos (show 0 ≤ (0 : ℤ) ∧ 0 ≤ s from ⟨by omega, by omega⟩)]
          · rw [if_neg hm0, if_neg (show ¬(0 ≤ (0 : ℤ) ∧ 0 ≤ s) by rintro ⟨_, h⟩; omega),
              if_neg (show ¬((0 : ℤ) < 0 ∧ s < 0) by rintro ⟨h, _⟩; omega)]
        rw [h1, h2]
        by_cases hm0 : s = 0 <;> simp [hm0]
      · rw [if_neg hs, rho_agree_pred m s hs]; ring
  rw [sub_eq_iff_eq_add] at hdiff
  rw [hdiff, add_comm]

/-- Base case: the ρ-string at `m = -1` is empty, so `StringSumQ (-1) d = 0`. -/
theorem StringSumQ_neg_one (d : ℤ) : StringSumQ (-1) d = 0 := by
  unfold StringSumQ
  apply finsum_eq_zero_of_forall_eq_zero
  intro s
  rw [show rho (-1 - s) s = 0 from ?_, HahnSeries.single_eq_zero]
  -- rho(-1-s, s) = 0 for all s: never both ≥ 0 (need s≥0 ⟹ -1-s ≤ -1 < 0) nor both < 0 (need s<0 ⟹ -1-s ≥ 0).
  unfold rho
  rw [if_neg (show ¬(0 ≤ -1 - s ∧ 0 ≤ s) by rintro ⟨h1, h2⟩; omega),
      if_neg (show ¬(-1 - s < 0 ∧ s < 0) by rintro ⟨h1, h2⟩; omega)]

/-- **`StringSumQ m 0 = (m+1) • 1`** (the `d = 0` ρ-string is the scalar count `m+1`).
For `m ≥ 0` it is `m+1` terms of weight `+1`; for `m ≤ -2` it is `|m|-1` terms of weight `-1`,
and `(-1)·(-m-1) = m+1` as well. -/
theorem StringSumQ_zero (m : ℤ) : StringSumQ m 0 = (m + 1 : ℚ) • (1 : K) := by
  -- prove by integer induction from the base m = -1 using the two recurrences.
  -- We phrase it as: ∀ m, StringSumQ m 0 = single 0 (m+1), and identify single 0 (c) = c • 1.
  have hsingle : ∀ c : ℚ, HahnSeries.single (0 : ℤ) c = c • (1 : K) := by
    intro c
    rw [← HahnSeries.single_zero_mul_eq_smul, mul_one]
  rw [← hsingle]
  -- Now show StringSumQ m 0 = single 0 (m+1).
  suffices h : ∀ n : ℤ, StringSumQ n 0 = HahnSeries.single (0 : ℤ) ((n : ℚ) + 1) by
    rw [h m]
  -- base computation: StringSumQ 0 0 = single 0 1 (the string at m = 0 is the single term s = 0).
  have hbase : StringSumQ 0 0 = HahnSeries.single (0 : ℤ) (1 : ℚ) := by
    unfold StringSumQ
    rw [finsum_eq_single _ 0 ?_]
    · rw [show (3 : ℤ) * 0 * 0 = 0 by ring,
        show rho (0 - 0) 0 = (1 : ℚ) by unfold rho; rw [if_pos ⟨by omega, by omega⟩]]
    · intro s hs
      rw [show rho (0 - s) s = (0 : ℚ) from ?_, HahnSeries.single_eq_zero]
      unfold rho
      rw [if_neg (show ¬(0 ≤ 0 - s ∧ 0 ≤ s) by rintro ⟨h1, h2⟩; omega),
          if_neg (show ¬(0 - s < 0 ∧ s < 0) by rintro ⟨h1, h2⟩; omega)]
  intro n
  refine Int.induction_on n ?_ ?_ ?_
  · rw [hbase]; norm_num
  · -- n = k → k+1, for k ≥ 0
    intro k ih
    have hrec := StringSumQ_succ (k : ℤ) 0 (by positivity)
    rw [show (3 : ℤ) * 0 * ((k : ℤ) + 1) = 0 by ring] at hrec
    rw [hrec, ih, ← HahnSeries.single_add]
    push_cast; ring_nf
  · -- n = -k → -(k+1), for k ≥ 0
    intro k ih
    have hrec := StringSumQ_pred (-(k : ℤ)) 0 (by simp)
    rw [show (3 : ℤ) * 0 * (-(k : ℤ)) = 0 by ring] at hrec
    rw [hrec, ih, ← HahnSeries.single_add]
    push_cast; ring_nf

/-- `Qpow a = single a 1`. -/
theorem Qpow_eq_single (a : ℤ) : Qpow a = HahnSeries.single a (1 : ℚ) := rfl

/-- `(1 - Qpow (3d)) · single c 1 = Qpow c - Qpow (3d + c)`. -/
theorem one_sub_Qpow_mul_single (d c : ℤ) :
    (1 - Qpow (3 * d)) * HahnSeries.single c (1 : ℚ) = Qpow c - Qpow (3 * d + c) := by
  rw [sub_mul, one_mul, ← Qpow_eq_single, Qpow_mul]

/-- **The geometric telescope.**  For the ρ-line string of slope `d`,
`(1 - Qpow (3d)) · StringSumQ m d = 1 - Qpow (3d(m+1))`.  (Holds for all `d`; with `d = 0`
both sides are `0`.) -/
theorem StringSumQ_mul_one_sub (m d : ℤ) :
    (1 - Qpow (3 * d)) * StringSumQ m d = 1 - Qpow (3 * d * (m + 1)) := by
  -- base: StringSumQ 0 d = single 0 1 = Qpow 0 = 1.
  have hbase : StringSumQ 0 d = (1 : K) := by
    unfold StringSumQ
    rw [finsum_eq_single _ 0 ?_]
    · rw [show (3 : ℤ) * d * 0 = 0 by ring,
        show rho (0 - 0) 0 = (1 : ℚ) by unfold rho; rw [if_pos ⟨by omega, by omega⟩]]
      rfl
    · intro s hs
      rw [show rho (0 - s) s = (0 : ℚ) from ?_, HahnSeries.single_eq_zero]
      unfold rho
      rw [if_neg (show ¬(0 ≤ 0 - s ∧ 0 ≤ s) by rintro ⟨h1, h2⟩; omega),
          if_neg (show ¬(0 - s < 0 ∧ s < 0) by rintro ⟨h1, h2⟩; omega)]
  refine Int.induction_on m ?_ ?_ ?_
  · -- m = 0
    rw [hbase, mul_one, show (3 : ℤ) * d * (0 + 1) = 3 * d by ring]
  · -- m = k → k+1, k ≥ 0
    intro k ih
    rw [StringSumQ_succ (k : ℤ) d (by positivity), mul_add, ih, one_sub_Qpow_mul_single]
    rw [show (3 : ℤ) * d * ((k : ℤ) + 1) = 3 * d * ((k : ℤ) + 1) from rfl]
    -- (1 - Qpow(3d(k+1))) + (Qpow(3d(k+1)) - Qpow(3d + 3d(k+1))) = 1 - Qpow(3d(k+1+1)).
    rw [show (3 : ℤ) * d + 3 * d * ((k : ℤ) + 1) = 3 * d * ((k : ℤ) + 1 + 1) by ring]
    abel
  · -- m = -k → -(k+1), k ≥ 0
    intro k ih
    rw [StringSumQ_pred (-(k : ℤ)) d (by simp)]
    rw [mul_add, ih]
    -- (1 - Qpow(3d(-k+1))) + (1-Qpow(3d))·single(3d(-k))(-1) = 1 - Qpow(3d(-k-1+1)) = 1 - Qpow(-3dk).
    rw [show (1 - Qpow (3 * d)) * HahnSeries.single (3 * d * (-(k : ℤ))) (-1 : ℚ)
        = - ((1 - Qpow (3 * d)) * HahnSeries.single (3 * d * (-(k : ℤ))) (1 : ℚ)) by
      rw [← mul_neg]; congr 1; rw [← HahnSeries.single_neg]]
    rw [one_sub_Qpow_mul_single]
    rw [show (3 : ℤ) * d * (-(k : ℤ)) = 3 * d * (-(k : ℤ)) from rfl]
    rw [show (3 : ℤ) * d + 3 * d * (-(k : ℤ)) = 3 * d * (-(k : ℤ) + 1) by ring]
    rw [show (3 : ℤ) * d * (-(k : ℤ) + 1) = 3 * d * (-(k : ℤ) + 1) from rfl]
    rw [show (3 : ℤ) * d * (-(k : ℤ) - 1 + 1) = 3 * d * (-(k : ℤ)) by ring]
    abel

/-! ### `Rho` as a summable family over `(r,s) : ℤ × ℤ` -/

/-- The ρ summable family `(r,s) ↦ monom (3rs) (x^r y^s) (ρ r s)`. -/
noncomputable def rhoFamily : HahnSeries.SummableFamily ExpQXY ℚ (ℤ × ℤ) where
  toFun := fun p => monom (3 * p.1 * p.2) p.1 p.2 (rho p.1 p.2)
  isPWO_iUnion_support' := by
    refine rhoCoeff_isPWO.mono (Set.iUnion_subset (fun p => ?_))
    intro g hg
    have hgeq : g = expQXY (3 * p.1 * p.2) p.1 p.2 := HahnSeries.support_single_subset hg
    -- g ∈ support of rhoCoeff: rhoCoeff g ≠ 0.
    rw [HahnSeries.mem_support] at hg
    simp only [Function.mem_support]
    rw [hgeq, rhoCoeff, qdeg_expQXY, xdeg_expQXY, ydeg_expQXY, if_pos rfl]
    -- need rho p.1 p.2 ≠ 0; from hg (monom coeff nonzero).
    unfold monom at hg
    rw [HahnSeries.coeff_single, if_pos hgeq] at hg
    exact hg
  finite_co_support' := by
    intro g
    -- only (r,s) = (xdeg g, ydeg g) can contribute (the monom is supported at one exponent).
    apply Set.Finite.subset (Set.finite_singleton
      ((ofLex (ofLex g).2).1, (ofLex (ofLex g).2).2))
    intro p hp
    simp only [Set.mem_singleton_iff] at hp ⊢
    by_contra hne
    apply hp
    unfold monom
    rw [HahnSeries.coeff_single_of_ne]
    -- expQXY (3 p1 p2) p1 p2 ≠ g, since (p1,p2) ≠ (xdeg g, ydeg g).
    intro hcon
    apply hne
    -- hcon : g = expQXY (3 p1 p2) p1 p2.  Read off x,y degrees.
    have hx : (ofLex (ofLex g).2).1 = p.1 := by rw [hcon, xdeg_expQXY]
    have hy : (ofLex (ofLex g).2).2 = p.2 := by rw [hcon, ydeg_expQXY]
    rw [hx, hy]

/-- `rhoFamily.hsum = Rho`. -/
theorem rhoFamily_hsum : rhoFamily.hsum = Rho := by
  apply HahnSeries.ext
  funext g
  rw [HahnSeries.SummableFamily.coeff_hsum]
  -- only p = (xdeg g, ydeg g) contributes.
  rw [finsum_eq_single _ ((ofLex (ofLex g).2).1, (ofLex (ofLex g).2).2) ?_]
  · -- the contributing term is `monom (3 xy) x y (rho x y)` evaluated at `g`.
    set x := (ofLex (ofLex g).2).1 with hxdef
    set y := (ofLex (ofLex g).2).2 with hydef
    show (monom (3 * x * y) x y (rho x y)).coeff g = Rho.coeff g
    show (HahnSeries.single (expQXY (3 * x * y) x y) (rho x y)).coeff g = rhoCoeff g
    rw [HahnSeries.coeff_single, rhoCoeff, ← hxdef, ← hydef]
    by_cases hc : (ofLex g).1 = 3 * x * y
    · have hgeq : g = expQXY (3 * x * y) x y := by
        conv_lhs => rw [expQXY_eta g, ← hxdef, ← hydef, hc]
      rw [if_pos hc, if_pos hgeq]
    · rw [if_neg hc, if_neg ?_]
      intro hcon
      apply hc
      rw [hcon, qdeg_expQXY]
  · -- terms at p ≠ (xdeg g, ydeg g) vanish at g.
    intro p hp
    show (monom (3 * p.1 * p.2) p.1 p.2 (rho p.1 p.2)).coeff g = 0
    unfold monom
    rw [HahnSeries.coeff_single_of_ne]
    intro hcon
    apply hp
    have hx : (ofLex (ofLex g).2).1 = p.1 := by rw [hcon, xdeg_expQXY]
    have hy : (ofLex (ofLex g).2).2 = p.2 := by rw [hcon, ydeg_expQXY]
    rw [hx, hy]

/-! ### The triple-product family and the slice extraction -/

/-- The full triple product `Θ(x;q)·Θ(y;q)·Rho` as a summable family over `(ℤ×ℤ)×(ℤ×ℤ)`. -/
noncomputable def prodFam : HahnSeries.SummableFamily ExpQXY ℚ ((ℤ × ℤ) × (ℤ × ℤ)) :=
  HahnSeries.SummableFamily.mul
    (HahnSeries.SummableFamily.mul (thetaFamily 3 0 1 0 (by norm_num))
      (thetaFamily 3 0 0 1 (by norm_num))) rhoFamily

/-- `prodFam.hsum = Θ(x;q)·Θ(y;q)·Rho`. -/
theorem prodFam_hsum : prodFam.hsum = thetaX_q * thetaY_q * Rho := by
  unfold prodFam
  rw [HahnSeries.SummableFamily.hsum_mul, HahnSeries.SummableFamily.hsum_mul, rhoFamily_hsum]
  rfl

/-- The `(k,l,r,s)`-term of `prodFam` is a single monomial. -/
theorem prodFam_term (k l r s : ℤ) :
    prodFam ((k, l), (r, s))
      = monom (3 * Tn k + 3 * Tn l + 3 * r * s) (k + r) (l + s)
          ((-1) ^ (k + l) * rho r s) := by
  unfold prodFam
  show (monom (thetaQDeg 3 0 k) (1 * k) (0 * k) ((-1) ^ k)
        * monom (thetaQDeg 3 0 l) (0 * l) (1 * l) ((-1) ^ l))
        * monom (3 * r * s) r s (rho r s) = _
  rw [monom_mul, monom_mul]
  apply monom_eq_monom
  · unfold thetaQDeg; ring
  · ring
  · ring
  · rw [zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]

/-- The `(k,l,r,s)`-term coefficient at `expQXY D a b` is the indicator of the antidiagonal. -/
theorem prodFam_term_coeff (k l r s a b D : ℤ) :
    (prodFam ((k, l), (r, s))).coeff (expQXY D a b)
      = if (3 * Tn k + 3 * Tn l + 3 * r * s = D ∧ k + r = a ∧ l + s = b)
        then (-1) ^ (k + l) * rho r s else 0 := by
  rw [prodFam_term]
  unfold monom
  rw [HahnSeries.coeff_single]
  by_cases h : (3 * Tn k + 3 * Tn l + 3 * r * s = D ∧ k + r = a ∧ l + s = b)
  · obtain ⟨hD, ha, hb⟩ := h
    rw [if_pos (show expQXY D a b
          = expQXY (3 * Tn k + 3 * Tn l + 3 * r * s) (k + r) (l + s) by rw [hD, ha, hb]),
        if_pos ⟨hD, ha, hb⟩]
  · rw [if_neg ?_, if_neg h]
    intro hcon
    apply h
    obtain ⟨hD, hx, hy⟩ := expQXY_inj hcon
    exact ⟨hD.symm, hx.symm, hy.symm⟩

/-- The co-support finiteness needed to curry the 4-index finsum. -/
theorem prodFam_coeff_finite (a b D : ℤ) :
    (Function.support (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      (prodFam p).coeff (expQXY D a b))).Finite :=
  prodFam.finite_co_support' (expQXY D a b)

/-- The K-series slice `coeffXY (Θx·Θy·Rho) a b`, coefficient at `Q`-degree `D`, collapses to a
double finsum over `(k,l)` with `r = a-k`, `s = b-l` forced by the `x,y`-degrees. -/
theorem slice_coeff_eq (a b D : ℤ) :
    (coeffXY (thetaX_q * thetaY_q * Rho) a b).coeff D
      = ∑ᶠ p : ℤ × ℤ,
          (if 3 * Tn p.1 + 3 * Tn p.2 + 3 * (a - p.1) * (b - p.2) = D
            then (-1) ^ (p.1 + p.2) * rho (a - p.1) (b - p.2) else 0) := by
  rw [coeffXY_coeff, coeffQXY, ← prodFam_hsum, HahnSeries.SummableFamily.coeff_hsum]
  -- replace the family-term coeff by the indicator.
  have hterm : (fun p : (ℤ × ℤ) × (ℤ × ℤ) => (prodFam p).coeff (expQXY D a b))
      = fun p => if (3 * Tn p.1.1 + 3 * Tn p.1.2 + 3 * p.2.1 * p.2.2 = D
          ∧ p.1.1 + p.2.1 = a ∧ p.1.2 + p.2.2 = b)
        then (-1) ^ (p.1.1 + p.1.2) * rho p.2.1 p.2.2 else 0 := by
    funext p
    obtain ⟨⟨k, l⟩, ⟨r, s⟩⟩ := p
    exact prodFam_term_coeff k l r s a b D
  rw [hterm]
  -- curry: ∑ᶠ ((k,l),(r,s)) = ∑ᶠ (k,l), ∑ᶠ (r,s).
  rw [finsum_curry _ (by
    rw [← hterm]; exact prodFam_coeff_finite a b D)]
  apply finsum_congr
  rintro ⟨k, l⟩
  -- inner sum over (r,s): only (a-k, b-l) survives the x,y-degree constraints.
  rw [finsum_eq_single _ (a - k, b - l) ?_]
  · -- value at (r,s) = (a-k, b-l): the x,y conjuncts are trivial, q-degree condition remains.
    simp only []
    by_cases hq : 3 * Tn k + 3 * Tn l + 3 * (a - k) * (b - l) = D
    · rw [if_pos ⟨hq, by ring, by ring⟩, if_pos hq]
    · rw [if_neg (by rintro ⟨h, _, _⟩; exact hq h), if_neg hq]
  · -- terms at (r,s) ≠ (a-k, b-l) vanish (x or y degree mismatch).
    rintro ⟨r, s⟩ hrs
    simp only []
    rw [if_neg ?_]
    rintro ⟨_, hx, hy⟩
    apply hrs
    have : r = a - k ∧ s = b - l := ⟨by omega, by omega⟩
    rw [this.1, this.2]

/-- The reindexing bijection mapping the new index `(t,s)` to the old `(k,l) = (t+s, b-s)`
(so that `t = k+l-b`, `s = b-l`). -/
def reindexKL (b : ℤ) : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun := fun q => (q.1 + q.2, b - q.2)
  invFun := fun p => (p.1 + p.2 - b, b - p.2)
  left_inv := by rintro ⟨t, s⟩; simp only [Prod.mk.injEq]; constructor <;> ring
  right_inv := by rintro ⟨k, l⟩; simp only [Prod.mk.injEq]; constructor <;> ring

/-- After reindexing `(k,l) ↦ (t,s) = (k+l-b, b-l)`, the slice coefficient at `D` becomes a
`(t,s)` finsum with the `q`-degree `3T b + 3T t + 3(a-b)s` and sign `(-1)^{b+t}`. -/
theorem slice_coeff_reindexed (a b D : ℤ) :
    (coeffXY (thetaX_q * thetaY_q * Rho) a b).coeff D
      = ∑ᶠ p : ℤ × ℤ,
          (if 3 * Tn b + 3 * Tn p.1 + 3 * (a - b) * p.2 = D
            then (-1) ^ (b + p.1) * rho (a - p.1 - p.2) p.2 else 0) := by
  rw [slice_coeff_eq]
  rw [← finsum_comp_equiv (reindexKL b)]
  apply finsum_congr
  rintro ⟨t, s⟩
  show (if 3 * Tn (t + s) + 3 * Tn (b - s) + 3 * (a - (t + s)) * (b - (b - s)) = D
      then (-1) ^ ((t + s) + (b - s)) * rho (a - (t + s)) (b - (b - s)) else 0)
    = (if 3 * Tn b + 3 * Tn t + 3 * (a - b) * s = D
      then (-1) ^ (b + t) * rho (a - t - s) s else 0)
  -- exponent: 3T(t+s)+3T(b-s)+3(a-t-s)·s = 3Tb+3Tt+3(a-b)s; sign (-1)^{t+b}.
  have hexp : 3 * Tn (t + s) + 3 * Tn (b - s) + 3 * (a - (t + s)) * (b - (b - s))
      = 3 * Tn b + 3 * Tn t + 3 * (a - b) * s := by
    have h1 := two_mul_Tn (t + s)
    have h2 := two_mul_Tn (b - s)
    have h3 := two_mul_Tn b
    have h4 := two_mul_Tn t
    -- multiply target by 2 and use the closed forms.
    have key : 2 * (3 * Tn (t + s) + 3 * Tn (b - s) + 3 * (a - (t + s)) * (b - (b - s)))
        = 2 * (3 * Tn b + 3 * Tn t + 3 * (a - b) * s) := by
      rw [show 2 * (3 * Tn (t + s) + 3 * Tn (b - s) + 3 * (a - (t + s)) * (b - (b - s)))
          = 3 * (2 * Tn (t + s)) + 3 * (2 * Tn (b - s)) + 6 * (a - (t + s)) * (b - (b - s)) by ring,
        h1, h2,
        show 2 * (3 * Tn b + 3 * Tn t + 3 * (a - b) * s)
          = 3 * (2 * Tn b) + 3 * (2 * Tn t) + 6 * (a - b) * s by ring, h3, h4]
      ring
    omega
  have hsign : (-1 : ℚ) ^ ((t + s) + (b - s)) = (-1) ^ (b + t) := by
    congr 1; ring
  have hrho : rho (a - (t + s)) (b - (b - s)) = rho (a - t - s) s := by
    congr 1 <;> ring
  rw [hexp, hsign, hrho]

/-! ### The slice as a single `t`-finsum, and the off-diagonal / diagonal evaluations -/

/-- Coefficient of `StringSumQ m d` at a `Q`-degree `E`. -/
theorem StringSumQ_coeff (m d E : ℤ) :
    (StringSumQ m d).coeff E = ∑ᶠ s : ℤ, (if 3 * d * s = E then rho (m - s) s else 0) := by
  unfold StringSumQ
  show (HahnSeries.coeff.addMonoidHom E) (∑ᶠ s : ℤ, HahnSeries.single (3 * d * s) (rho (m - s) s))
    = _
  rw [(HahnSeries.coeff.addMonoidHom E).map_finsum (stringSummand_support_finite m d)]
  apply finsum_congr
  intro s
  show (HahnSeries.single (3 * d * s) (rho (m - s) s)).coeff E = _
  rw [HahnSeries.coeff_single]
  by_cases h : 3 * d * s = E
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hc => h hc.symm)]

/-- The single-`t` term of the slice: `(-1)^{b+t} · Q^{3Tb+3Tt} · StringSumQ(a-t, a-b)`. -/
noncomputable def sliceTterm (a b t : ℤ) : K :=
  ((-1 : ℚ) ^ (b + t)) • (Qpow (3 * Tn b + 3 * Tn t) * StringSumQ (a - t) (a - b))

/-- Coefficient of `sliceTterm a b t` at `Q`-degree `D`. -/
theorem sliceTterm_coeff (a b t D : ℤ) :
    (sliceTterm a b t).coeff D
      = ∑ᶠ s : ℤ,
          (if 3 * Tn b + 3 * Tn t + 3 * (a - b) * s = D
            then (-1) ^ (b + t) * rho (a - t - s) s else 0) := by
  unfold sliceTterm
  rw [HahnSeries.coeff_smul, smul_eq_mul]
  -- (Qpow C * X).coeff D = X.coeff (D - C).
  rw [show (Qpow (3 * Tn b + 3 * Tn t) * StringSumQ (a - t) (a - b)).coeff D
      = (StringSumQ (a - t) (a - b)).coeff (D - (3 * Tn b + 3 * Tn t)) by
    unfold Qpow; rw [HahnSeries.coeff_single_mul, one_mul]]
  rw [StringSumQ_coeff]
  -- pull the scalar (-1)^{b+t} into the finsum.
  rw [mul_finsum' (fun s : ℤ => if 3 * (a - b) * s = D - (3 * Tn b + 3 * Tn t)
        then rho (a - t - s) s else 0) ((-1) ^ (b + t)) (by
    apply Set.Finite.subset (stringSupp_finite (a - t))
    intro s hs
    simp only [Function.mem_support] at hs
    simp only [Set.mem_setOf_eq]
    intro hc
    apply hs
    by_cases h : 3 * (a - b) * s = D - (3 * Tn b + 3 * Tn t)
    · rw [if_pos h, hc]
    · rw [if_neg h])]
  apply finsum_congr
  intro s
  by_cases h : 3 * (a - b) * s = D - (3 * Tn b + 3 * Tn t)
  · rw [if_pos h, if_pos (by omega : 3 * Tn b + 3 * Tn t + 3 * (a - b) * s = D)]
  · rw [if_neg h, if_neg (by omega : ¬ 3 * Tn b + 3 * Tn t + 3 * (a - b) * s = D), mul_zero]


/-- Each `Q`-degree in the support of `sliceTterm a b t` is `≥ 0`: writing the exponent in the
original `(k,l)` variables, it is `3·T k + 3·T l + 3·r·s` with `T k, T l ≥ 0` and `r·s ≥ 0`
(the latter because `ρ(r,s) ≠ 0`). -/
theorem sliceTterm_support_nonneg (a b t : ℤ) :
    (sliceTterm a b t).support ⊆ Set.Ici (0 : ℤ) := by
  intro E hE
  rw [HahnSeries.mem_support] at hE
  rw [Set.mem_Ici]
  by_contra hneg
  push_neg at hneg
  apply hE
  rw [sliceTterm_coeff]
  apply finsum_eq_zero_of_forall_eq_zero
  intro s
  by_cases hc : 3 * Tn b + 3 * Tn t + 3 * (a - b) * s = E
  · -- this degree is < 0; show the weight ρ vanishes (else the degree would be ≥ 0).
    rw [if_pos hc]
    by_cases hr : rho (a - t - s) s = 0
    · rw [hr, mul_zero]
    · exfalso
      -- via (k,l) = (t+s, b-s): degree = 3Tk+3Tl+3rs with rs = (a-t-s)·s ≥ 0.
      have hrs : 0 ≤ 3 * (a - t - s) * s := rho_support_nonneg_q hr
      have hTk : 0 ≤ Tn (t + s) := Tn_nonneg _
      have hTl : 0 ≤ Tn (b - s) := Tn_nonneg _
      -- 3Tb+3Tt+3(a-b)s = 3T(t+s)+3T(b-s)+3(a-t-s)s   (the reindex exponent identity, reversed).
      have hdeg : 3 * Tn b + 3 * Tn t + 3 * (a - b) * s
          = 3 * Tn (t + s) + 3 * Tn (b - s) + 3 * (a - t - s) * s := by
        have h1 := two_mul_Tn (t + s)
        have h2 := two_mul_Tn (b - s)
        have h3 := two_mul_Tn b
        have h4 := two_mul_Tn t
        have key : 2 * (3 * Tn b + 3 * Tn t + 3 * (a - b) * s)
            = 2 * (3 * Tn (t + s) + 3 * Tn (b - s) + 3 * (a - t - s) * s) := by
          rw [show 2 * (3 * Tn b + 3 * Tn t + 3 * (a - b) * s)
              = 3 * (2 * Tn b) + 3 * (2 * Tn t) + 6 * (a - b) * s by ring, h3, h4,
            show 2 * (3 * Tn (t + s) + 3 * Tn (b - s) + 3 * (a - t - s) * s)
              = 3 * (2 * Tn (t + s)) + 3 * (2 * Tn (b - s)) + 6 * (a - t - s) * s by ring, h1, h2]
          ring
        omega
      rw [hdeg] at hc
      -- E = nonneg + nonneg + nonneg ≥ 0, contradicting E < 0.
      omega
  · rw [if_neg hc]

/-- A crude bound: `Tn n ≤ E` forces `|n| ≤ E + 1`. -/
theorem abs_le_of_Tn_le {n E : ℤ} (h : Tn n ≤ E) : -(E + 1) ≤ n ∧ n ≤ E + 1 := by
  have h2 := two_mul_Tn n
  constructor <;> nlinarith [h, h2, sq_nonneg (n - 1), sq_nonneg (n + 1), Tn_nonneg n]

/-- The co-support of the `sliceTterm`-family at `E` is finite: contributing `t`s lie in a bounded
interval (from `T(t+s) ≤ E/3` and `T(b-s) ≤ E/3`, both forced by nonnegativity). -/
theorem sliceTterm_co_support_finite (a b E : ℤ) :
    {t : ℤ | (sliceTterm a b t).coeff E ≠ 0}.Finite := by
  apply Set.Finite.subset (Set.finite_Icc (-(E + 1) - (E + 1) - b) ((E + 1) + (E + 1) - b))
  intro t ht
  simp only [Set.mem_setOf_eq] at ht
  rw [sliceTterm_coeff] at ht
  rw [Set.mem_Icc]
  -- if t were outside the interval, every s-summand would vanish, making the finsum 0.
  by_contra htbound
  apply ht
  apply finsum_eq_zero_of_forall_eq_zero
  intro s
  by_cases hc : 3 * Tn b + 3 * Tn t + 3 * (a - b) * s = E
  · rw [if_pos hc]
    by_cases hr0 : rho (a - t - s) s = 0
    · rw [hr0, mul_zero]
    · -- a contributing s forces t into the interval, contradicting htbound.
      exfalso
      apply htbound
      have hrs : 0 ≤ 3 * (a - t - s) * s := rho_support_nonneg_q hr0
      have hTk : 0 ≤ Tn (t + s) := Tn_nonneg _
      have hTl : 0 ≤ Tn (b - s) := Tn_nonneg _
      have hdeg : 3 * Tn (t + s) + 3 * Tn (b - s) + 3 * (a - t - s) * s = E := by
        have h1 := two_mul_Tn (t + s)
        have h2 := two_mul_Tn (b - s)
        have h3 := two_mul_Tn b
        have h4 := two_mul_Tn t
        have key : 2 * (3 * Tn (t + s) + 3 * Tn (b - s) + 3 * (a - t - s) * s)
            = 2 * (3 * Tn b + 3 * Tn t + 3 * (a - b) * s) := by
          rw [show 2 * (3 * Tn (t + s) + 3 * Tn (b - s) + 3 * (a - t - s) * s)
              = 3 * (2 * Tn (t + s)) + 3 * (2 * Tn (b - s)) + 6 * (a - t - s) * s by ring, h1, h2,
            show 2 * (3 * Tn b + 3 * Tn t + 3 * (a - b) * s)
              = 3 * (2 * Tn b) + 3 * (2 * Tn t) + 6 * (a - b) * s by ring, h3, h4]
          ring
        have hc2 : 2 * (3 * Tn b + 3 * Tn t + 3 * (a - b) * s) = 2 * E := by rw [hc]
        linarith [key, hc2]
      have hTtsE : Tn (t + s) ≤ E := by omega
      have hTbsE : Tn (b - s) ≤ E := by omega
      obtain ⟨hts_lb, hts_ub⟩ := abs_le_of_Tn_le hTtsE
      obtain ⟨hbs_lb, hbs_ub⟩ := abs_le_of_Tn_le hTbsE
      constructor <;> omega
  · rw [if_neg hc]

/-- The `(t,s)` antidiagonal `{3Tb+3Tt+3(a-b)s = D, ρ≠0}` is finite: both `T(t+s)` and `T(b-s)`
are bounded above by `D` (nonnegativity), bounding `t+s`, `b-s`, hence `t` and `s`. -/
theorem ts_antidiagonal_finite (a b D : ℤ) :
    (Function.support (fun p : ℤ × ℤ =>
      if 3 * Tn b + 3 * Tn p.1 + 3 * (a - b) * p.2 = D
        then (-1 : ℚ) ^ (b + p.1) * rho (a - p.1 - p.2) p.2 else 0)).Finite := by
  apply Set.Finite.subset (Set.finite_Icc
    ((-(D + 1) - (D + 1) - b, b - (D + 1)) : ℤ × ℤ)
    (((D + 1) + (D + 1) - b, b + (D + 1)) : ℤ × ℤ))
  rintro ⟨t, s⟩ hts
  simp only [Function.mem_support] at hts
  by_cases hcc : 3 * Tn b + 3 * Tn t + 3 * (a - b) * s = D
  · rw [if_pos hcc] at hts
    have hr : rho (a - t - s) s ≠ 0 := fun h0 => hts (by rw [h0, mul_zero])
    have hrs : 0 ≤ 3 * (a - t - s) * s := rho_support_nonneg_q hr
    have hTk : 0 ≤ Tn (t + s) := Tn_nonneg _
    have hTl : 0 ≤ Tn (b - s) := Tn_nonneg _
    have hdeg : 3 * Tn (t + s) + 3 * Tn (b - s) + 3 * (a - t - s) * s = D := by
      have h1 := two_mul_Tn (t + s)
      have h2 := two_mul_Tn (b - s)
      have h3 := two_mul_Tn b
      have h4 := two_mul_Tn t
      have key : 2 * (3 * Tn (t + s) + 3 * Tn (b - s) + 3 * (a - t - s) * s)
          = 2 * (3 * Tn b + 3 * Tn t + 3 * (a - b) * s) := by
        rw [show 2 * (3 * Tn (t + s) + 3 * Tn (b - s) + 3 * (a - t - s) * s)
            = 3 * (2 * Tn (t + s)) + 3 * (2 * Tn (b - s)) + 6 * (a - t - s) * s by ring, h1, h2,
          show 2 * (3 * Tn b + 3 * Tn t + 3 * (a - b) * s)
            = 3 * (2 * Tn b) + 3 * (2 * Tn t) + 6 * (a - b) * s by ring, h3, h4]
        ring
      have hc2 : 2 * (3 * Tn b + 3 * Tn t + 3 * (a - b) * s) = 2 * D := by rw [hcc]
      linarith [key, hc2]
    have hTtsE : Tn (t + s) ≤ D := by omega
    have hTbsE : Tn (b - s) ≤ D := by omega
    obtain ⟨hts_lb, hts_ub⟩ := abs_le_of_Tn_le hTtsE
    obtain ⟨hbs_lb, hbs_ub⟩ := abs_le_of_Tn_le hTbsE
    rw [Set.mem_Icc, Prod.le_def, Prod.le_def]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [] <;> omega
  · rw [if_neg hcc] at hts; exact absurd rfl hts

/-- The slice summable family `t ↦ sliceTterm a b t` over `ℤ`. -/
noncomputable def sliceTFamily (a b : ℤ) : HahnSeries.SummableFamily ℤ ℚ ℤ where
  toFun := fun t => sliceTterm a b t
  isPWO_iUnion_support' := by
    refine ((bddBelow_Ici (a := (0 : ℤ))).isWF.isPWO).mono (Set.iUnion_subset (fun t => ?_))
    exact sliceTterm_support_nonneg a b t
  finite_co_support' := fun E => sliceTterm_co_support_finite a b E

/-- Coefficient of `sliceTFamily.hsum` at `D`: the `t`-finsum of `sliceTterm`-coefficients. -/
theorem sliceTFamily_hsum_coeff (a b D : ℤ) :
    (sliceTFamily a b).hsum.coeff D = ∑ᶠ t : ℤ, (sliceTterm a b t).coeff D := by
  rw [HahnSeries.SummableFamily.coeff_hsum]; rfl

/-- **The slice equals the `t`-summed family** (the design's coefficient-extraction formula,
packaged as a `K`-series identity): `coeffXY (Θx·Θy·Rho) a b = ∑'_t sliceTterm a b t`. -/
theorem coeffXY_eq_sliceTFamily_hsum (a b : ℤ) :
    coeffXY (thetaX_q * thetaY_q * Rho) a b = (sliceTFamily a b).hsum := by
  apply HahnSeries.ext
  funext D
  -- LHS coeff: slice_coeff_reindexed; RHS coeff: t-finsum of sliceTterm coeffs.
  rw [slice_coeff_reindexed a b D, sliceTFamily_hsum_coeff]
  -- RHS: ∑ᶠ t, sliceTterm coeff = ∑ᶠ t, ∑ᶠ s, (...) = ∑ᶠ (t,s) (...) = ∑ᶠ p (...).
  have hRHS : (∑ᶠ t : ℤ, (sliceTterm a b t).coeff D)
      = ∑ᶠ p : ℤ × ℤ,
          (if 3 * Tn b + 3 * Tn p.1 + 3 * (a - b) * p.2 = D
            then (-1) ^ (b + p.1) * rho (a - p.1 - p.2) p.2 else 0) := by
    rw [finsum_curry (fun p : ℤ × ℤ =>
      if 3 * Tn b + 3 * Tn p.1 + 3 * (a - b) * p.2 = D
        then (-1) ^ (b + p.1) * rho (a - p.1 - p.2) p.2 else 0) (ts_antidiagonal_finite a b D)]
    apply finsum_congr
    intro t
    rw [sliceTterm_coeff]
  exact hRHS.symm

/-! ### `theta_one_zero` shifted, and the off-diagonal vanishing -/

/-- A general `K`-theta family with `Q`-degree `thetaQDeg 3 e` (nome `Q³`, linear twist `e`). -/
noncomputable def kThetaGen (e : ℤ) (w : ℤ → ℚ) : HahnSeries.SummableFamily ℤ ℚ ℤ where
  toFun := fun t => HahnSeries.single (thetaQDeg 3 e t) (w t)
  isPWO_iUnion_support' := by
    have hb := thetaQDeg_bddBelow 3 e (by norm_num)
    refine (hb.isWF.isPWO).mono (Set.iUnion_subset (fun t => ?_))
    intro x hx
    have hxe : x = thetaQDeg 3 e t := HahnSeries.support_single_subset hx
    exact ⟨t, hxe.symm⟩
  finite_co_support' := by
    intro g
    apply Set.Finite.subset (thetaQDeg_finite_fiber 3 e (by norm_num) g)
    intro t ht
    simp only [Set.mem_setOf_eq] at ht
    by_contra hne
    apply ht
    rw [HahnSeries.coeff_single_of_ne]
    intro hcon
    exact hne hcon.symm

/-- Coefficient-anti-invariance vanishing for `kThetaGen` under the involution `t ↦ c − t`,
provided `thetaQDeg 3 e (c−t) = thetaQDeg 3 e t` and `w (c−t) = − w t`. -/
theorem kThetaGen_eq_zero_of_anti (e c : ℤ) (w : ℤ → ℚ)
    (hdeg : ∀ t, thetaQDeg 3 e (c - t) = thetaQDeg 3 e t)
    (hw : ∀ t, w (c - t) = - w t) :
    (kThetaGen e w).hsum = 0 := by
  apply HahnSeries.ext
  funext m
  rw [HahnSeries.SummableFamily.coeff_hsum, HahnSeries.coeff_zero]
  have hreindex : (∑ᶠ t, (HahnSeries.single (thetaQDeg 3 e t) (w t)).coeff m)
      = ∑ᶠ t, (HahnSeries.single (thetaQDeg 3 e (c - t)) (w (c - t))).coeff m := by
    rw [← finsum_comp_equiv (Equiv.subLeft c)]
    rfl
  have hneg : (∑ᶠ t, (HahnSeries.single (thetaQDeg 3 e (c - t)) (w (c - t))).coeff m)
      = - ∑ᶠ t, (HahnSeries.single (thetaQDeg 3 e t) (w t)).coeff m := by
    rw [← finsum_neg_distrib]
    apply finsum_congr
    intro t
    rw [hdeg t, hw t, HahnSeries.single_neg, HahnSeries.coeff_neg]
  show (∑ᶠ t, (HahnSeries.single (thetaQDeg 3 e t) (w t)).coeff m) = 0
  have := hreindex.trans hneg
  linarith [this]

/-- **`theta_one_zero` shifted**: `∑'_t (-1)^t Q^{3 T t − 3 d t} = 0` (the involution `t ↦ (1+2d)−t`
fixes the exponent `3 T t − 3 d t` and flips the sign). -/
theorem theta_one_zero_shifted (d : ℤ) :
    (kThetaGen (-3 * d) (fun t => (-1) ^ t)).hsum = 0 := by
  apply kThetaGen_eq_zero_of_anti (-3 * d) (1 + 2 * d) (fun t => (-1) ^ t)
  · intro t
    unfold thetaQDeg
    have h1 := two_mul_Tn ((1 + 2 * d) - t)
    have h2 := two_mul_Tn t
    -- double the goal and use the closed forms; the result is a polynomial identity.
    have hdouble : 2 * (3 * Tn ((1 + 2 * d) - t) + -3 * d * ((1 + 2 * d) - t))
        = 2 * (3 * Tn t + -3 * d * t) := by
      rw [show 2 * (3 * Tn ((1 + 2 * d) - t) + -3 * d * ((1 + 2 * d) - t))
          = 3 * (2 * Tn ((1 + 2 * d) - t)) + 2 * (-3 * d * ((1 + 2 * d) - t)) by ring, h1,
        show 2 * (3 * Tn t + -3 * d * t) = 3 * (2 * Tn t) + 2 * (-3 * d * t) by ring, h2]
      ring
    omega
  · intro t
    rw [show (1 + 2 * d) - t = (-t) + (1 + 2 * d) by ring]
    rw [zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0), negOne_zpow_neg t]
    rw [show (1 : ℤ) + 2 * d = 1 + 2 * d from rfl, zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]
    rw [show (2 : ℤ) * d = 2 * d from rfl]
    have h2d : ((-1 : ℚ)) ^ (2 * d) = 1 := by
      rw [zpow_mul]; norm_num
    rw [zpow_one, h2d]; ring

/-- `kThetaGen 0 (fun t => (-1)^t)).hsum = 0` (this is the unshifted `theta_one_zero`). -/
theorem theta_one_zero_gen : (kThetaGen 0 (fun t => (-1) ^ t)).hsum = 0 := by
  apply kThetaGen_eq_zero_of_anti 0 1 (fun t => (-1) ^ t)
  · intro t; unfold thetaQDeg
    have h1 := two_mul_Tn (1 - t); have h2 := two_mul_Tn t
    have : (1 - t) * (1 - t - 1) = t * (t - 1) := by ring
    omega
  · intro t; exact negOne_zpow_one_sub t

/-- **Off-diagonal telescoped term**, as a `K`-series.  For `d = a − b`,
`(1 − Q^{3d}) · sliceTterm a b t = (-1)^{b+t} · (Q^{3Tb+3Tt} − Q^{3Tb+3Tt+3d(a−t+1)})`. -/
theorem one_sub_Qpow_mul_sliceTterm (a b t : ℤ) :
    (1 - Qpow (3 * (a - b))) * sliceTterm a b t
      = ((-1 : ℚ) ^ (b + t)) • (Qpow (3 * Tn b + 3 * Tn t)
          - Qpow (3 * Tn b + 3 * Tn t + 3 * (a - b) * (a - t + 1))) := by
  unfold sliceTterm
  rw [mul_smul_comm, ← mul_assoc]
  rw [show (1 - Qpow (3 * (a - b))) * Qpow (3 * Tn b + 3 * Tn t)
      = Qpow (3 * Tn b + 3 * Tn t) * (1 - Qpow (3 * (a - b))) by ring]
  rw [mul_assoc, StringSumQ_mul_one_sub (a - t) (a - b)]
  rw [mul_sub, mul_one, Qpow_mul]

/-- Coefficient of `kThetaGen e w` at `m`, as an indicator finsum. -/
theorem kThetaGen_coeff (e : ℤ) (w : ℤ → ℚ) (m : ℤ) :
    (kThetaGen e w).hsum.coeff m = ∑ᶠ t : ℤ, (if thetaQDeg 3 e t = m then w t else 0) := by
  rw [HahnSeries.SummableFamily.coeff_hsum]
  apply finsum_congr
  intro t
  show (HahnSeries.single (thetaQDeg 3 e t) (w t)).coeff m = _
  rw [HahnSeries.coeff_single]
  by_cases h : thetaQDeg 3 e t = m
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hc => h hc.symm)]

/-- Since `kThetaGen 0 (fun t => (-1)^t)` has zero `hsum`, every fibre sum `∑ᶠ t [3Tt = m] (-1)^t`
vanishes. -/
theorem theta_fibre_zero (m : ℤ) :
    (∑ᶠ t : ℤ, (if 3 * Tn t = m then (-1 : ℚ) ^ t else 0)) = 0 := by
  have h := theta_one_zero_gen
  have hc := kThetaGen_coeff 0 (fun t => (-1) ^ t) m
  rw [h, HahnSeries.coeff_zero] at hc
  rw [show (∑ᶠ t : ℤ, (if 3 * Tn t = m then (-1 : ℚ) ^ t else 0))
      = ∑ᶠ t : ℤ, (if thetaQDeg 3 0 t = m then (-1 : ℚ) ^ t else 0) by
    apply finsum_congr; intro t; rw [show thetaQDeg 3 0 t = 3 * Tn t by unfold thetaQDeg; ring]]
  rw [← hc]

/-- The shifted fibre sum `∑ᶠ t [3Tt − 3dt = m] (-1)^t` also vanishes. -/
theorem theta_fibre_zero_shifted (d m : ℤ) :
    (∑ᶠ t : ℤ, (if 3 * Tn t - 3 * d * t = m then (-1 : ℚ) ^ t else 0)) = 0 := by
  have h := theta_one_zero_shifted d
  have hc := kThetaGen_coeff (-3 * d) (fun t => (-1) ^ t) m
  rw [h, HahnSeries.coeff_zero] at hc
  rw [show (∑ᶠ t : ℤ, (if 3 * Tn t - 3 * d * t = m then (-1 : ℚ) ^ t else 0))
      = ∑ᶠ t : ℤ, (if thetaQDeg 3 (-3 * d) t = m then (-1 : ℚ) ^ t else 0) by
    apply finsum_congr; intro t
    rw [show thetaQDeg 3 (-3 * d) t = 3 * Tn t - 3 * d * t by unfold thetaQDeg; ring]]
  rw [← hc]

/-- `1 - Qpow (3d) ≠ 0` in `K` (its constant coefficient is `1`). -/
theorem one_sub_Qpow_ne_zero (d : ℤ) (hd : d ≠ 0) : (1 : K) - Qpow (3 * d) ≠ 0 := by
  intro h
  -- evaluate at the coefficient of `Q^0`: `1 - [3d = 0] = 1 ≠ 0`.
  have hcoeff : ((1 : K) - Qpow (3 * d)).coeff 0 = 1 := by
    rw [HahnSeries.coeff_sub]
    rw [show ((1 : K)).coeff 0 = 1 by rw [HahnSeries.coeff_one]; simp]
    rw [show (Qpow (3 * d)).coeff 0 = 0 by
      unfold Qpow; rw [HahnSeries.coeff_single_of_ne]; omega]
    ring
  rw [h, HahnSeries.coeff_zero] at hcoeff
  exact one_ne_zero hcoeff.symm

/-- The smul'd family `(1−Q^{3d}) • sliceTFamily a b` has `toFun t = (1−Q^{3d})·sliceTterm a b t`. -/
theorem smul_sliceTFamily_toFun (a b t : ℤ) :
    (((1 : K) - Qpow (3 * (a - b))) • sliceTFamily a b) t
      = (1 - Qpow (3 * (a - b))) * sliceTterm a b t := by
  rfl

/-- **Off-diagonal vanishing.**  For `a ≠ b`, the slice `coeffXY (Θx·Θy·Rho) a b` is the zero
`K`-series.  (Multiply by `1−Q^{3(a−b)}`; the telescoped sum is two `theta`-sums, each `0` by
`theta_one_zero` and its shift; then cancel the nonzero factor `1−Q^{3(a−b)}`.) -/
theorem slice_off_diagonal (a b : ℤ) (hab : a ≠ b) :
    coeffXY (thetaX_q * thetaY_q * Rho) a b = 0 := by
  have hd : a - b ≠ 0 := by omega
  -- it suffices that (1 − Q^{3d})·slice = 0.
  have hzero : (1 - Qpow (3 * (a - b))) * coeffXY (thetaX_q * thetaY_q * Rho) a b = 0 := by
    rw [coeffXY_eq_sliceTFamily_hsum, ← HahnSeries.SummableFamily.hsum_smul]
    apply HahnSeries.ext
    funext E
    rw [HahnSeries.SummableFamily.coeff_hsum, HahnSeries.coeff_zero]
    -- ∑ᶠ t (telescoped term).coeff E = (theta fibre) − (shifted theta fibre) = 0.
    have hterm : ∀ t, ((((1 : K) - Qpow (3 * (a - b))) • sliceTFamily a b) t).coeff E
        = (if 3 * Tn b + 3 * Tn t = E then (-1 : ℚ) ^ (b + t) else 0)
          - (if 3 * Tn b + 3 * Tn t + 3 * (a - b) * (a - t + 1) = E
              then (-1 : ℚ) ^ (b + t) else 0) := by
      intro t
      rw [smul_sliceTFamily_toFun, one_sub_Qpow_mul_sliceTterm]
      rw [HahnSeries.coeff_smul, smul_eq_mul, HahnSeries.coeff_sub]
      rw [show (Qpow (3 * Tn b + 3 * Tn t)).coeff E
          = (if 3 * Tn b + 3 * Tn t = E then (1 : ℚ) else 0) by
        unfold Qpow; rw [HahnSeries.coeff_single]
        by_cases h : 3 * Tn b + 3 * Tn t = E
        · rw [if_pos h.symm, if_pos h]
        · rw [if_neg (fun hc => h hc.symm), if_neg h]]
      rw [show (Qpow (3 * Tn b + 3 * Tn t + 3 * (a - b) * (a - t + 1))).coeff E
          = (if 3 * Tn b + 3 * Tn t + 3 * (a - b) * (a - t + 1) = E then (1 : ℚ) else 0) by
        unfold Qpow; rw [HahnSeries.coeff_single]
        by_cases h : 3 * Tn b + 3 * Tn t + 3 * (a - b) * (a - t + 1) = E
        · rw [if_pos h.symm, if_pos h]
        · rw [if_neg (fun hc => h hc.symm), if_neg h]]
      rw [mul_sub]
      congr 1 <;> (split_ifs <;> ring)
    rw [finsum_congr hterm]
    -- split the finsum into the two theta-fibre sums.
    rw [finsum_sub_distrib ?_ ?_]
    · -- first sum: ∑ᶠ t [3Tb+3Tt=E] (-1)^{b+t} = (-1)^b · theta_fibre = 0.
      -- the shift-of-condition algebra: 3(a-b)(a-t+1) = 3(a-b)(a+1) - 3(a-b)t.
      have halg : ∀ t : ℤ, 3 * (a - b) * (a - t + 1) = 3 * (a - b) * (a + 1) - 3 * (a - b) * t := by
        intro t; ring
      have h1 : (∑ᶠ t : ℤ, (if 3 * Tn b + 3 * Tn t = E then (-1 : ℚ) ^ (b + t) else 0)) = 0 := by
        rw [show (fun t : ℤ => if 3 * Tn b + 3 * Tn t = E then (-1 : ℚ) ^ (b + t) else 0)
            = fun t : ℤ => (-1 : ℚ) ^ b * (if 3 * Tn t = E - 3 * Tn b then (-1 : ℚ) ^ t else 0) by
          funext t
          by_cases hc : 3 * Tn t = E - 3 * Tn b
          · rw [if_pos hc, if_pos (by omega), zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]
          · rw [if_neg hc, if_neg (by omega), mul_zero]]
        rw [← mul_finsum' (fun t : ℤ => if 3 * Tn t = E - 3 * Tn b then (-1 : ℚ) ^ t else 0)
          ((-1 : ℚ) ^ b) (by
          apply Set.Finite.subset (kTheta_fiber_finite (E - 3 * Tn b))
          intro t ht; simp only [Function.mem_support] at ht; simp only [Set.mem_setOf_eq]
          by_contra hcon
          rw [show thetaQDeg 3 0 t = 3 * Tn t by unfold thetaQDeg; ring] at hcon
          exact ht (by rw [if_neg (by omega : ¬ 3 * Tn t = E - 3 * Tn b)]))]
        rw [theta_fibre_zero (E - 3 * Tn b), mul_zero]
      have h2 : (∑ᶠ t : ℤ, (if 3 * Tn b + 3 * Tn t + 3 * (a - b) * (a - t + 1) = E
          then (-1 : ℚ) ^ (b + t) else 0)) = 0 := by
        rw [show (fun t : ℤ => if 3 * Tn b + 3 * Tn t + 3 * (a - b) * (a - t + 1) = E
              then (-1 : ℚ) ^ (b + t) else 0)
            = fun t : ℤ => (-1 : ℚ) ^ b *
                (if 3 * Tn t - 3 * (a - b) * t
                    = E - 3 * Tn b - 3 * (a - b) * (a + 1) then (-1 : ℚ) ^ t else 0) by
          funext t
          rw [halg t]
          by_cases hc : 3 * Tn t - 3 * (a - b) * t = E - 3 * Tn b - 3 * (a - b) * (a + 1)
          · rw [if_pos hc, if_pos (by omega), zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]
          · rw [if_neg hc, if_neg (by omega), mul_zero]]
        rw [← mul_finsum' (fun t : ℤ => if 3 * Tn t - 3 * (a - b) * t
              = E - 3 * Tn b - 3 * (a - b) * (a + 1) then (-1 : ℚ) ^ t else 0)
          ((-1 : ℚ) ^ b) (by
          apply Set.Finite.subset (thetaQDeg_finite_fiber 3 (-3 * (a - b)) (by norm_num)
            (E - 3 * Tn b - 3 * (a - b) * (a + 1)))
          intro t ht; simp only [Function.mem_support] at ht; simp only [Set.mem_setOf_eq]
          by_contra hcon
          rw [show thetaQDeg 3 (-3 * (a - b)) t = 3 * Tn t - 3 * (a - b) * t by unfold thetaQDeg; ring] at hcon
          exact ht (by rw [if_neg (by omega : ¬ 3 * Tn t - 3 * (a - b) * t = E - 3 * Tn b - 3 * (a - b) * (a + 1))]))]
        rw [theta_fibre_zero_shifted (a - b) (E - 3 * Tn b - 3 * (a - b) * (a + 1)), mul_zero]
      rw [h1, h2, sub_zero]
    · -- finiteness of the first fibre support (condition 3Tb+3Tt = E).
      apply Set.Finite.subset (kTheta_fiber_finite (E - 3 * Tn b))
      intro t ht; simp only [Function.mem_support] at ht; simp only [Set.mem_setOf_eq]
      by_contra hcon
      rw [show thetaQDeg 3 0 t = 3 * Tn t by unfold thetaQDeg; ring] at hcon
      exact ht (by rw [if_neg (by omega : ¬ 3 * Tn b + 3 * Tn t = E)])
    · -- finiteness of the shifted fibre support.
      apply Set.Finite.subset (thetaQDeg_finite_fiber 3 (-3 * (a - b)) (by norm_num)
        (E - 3 * Tn b - 3 * (a - b) * (a + 1)))
      intro t ht; simp only [Function.mem_support] at ht; simp only [Set.mem_setOf_eq]
      by_contra hcon
      rw [show thetaQDeg 3 (-3 * (a - b)) t = 3 * Tn t - 3 * (a - b) * t by unfold thetaQDeg; ring] at hcon
      have halg : 3 * (a - b) * (a - t + 1) = 3 * (a - b) * (a + 1) - 3 * (a - b) * t := by ring
      exact ht (by rw [halg, if_neg (by omega : ¬ 3 * Tn b + 3 * Tn t
        + (3 * (a - b) * (a + 1) - 3 * (a - b) * t) = E)])
  -- cancel the nonzero factor.
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h (one_sub_Qpow_ne_zero (a - b) hd)
  · exact h

/-- The Jacobi-derivative fibre sum: `∑ᶠ t [3Tt = m] (-1)^t·t = − (poch_q³).coeff m`. -/
theorem jacobi_fibre (m : ℤ) :
    (∑ᶠ t : ℤ, (if 3 * Tn t = m then (-1 : ℚ) ^ t * t else 0)) = - (poch_q ^ 3).coeff m := by
  have h := jacobi_derivative_poch_cube
  -- h : -(kTheta (fun t => (-1)^t * t)) = poch_q^3, so (poch^3).coeff m = -(kTheta ...).coeff m.
  have hc : (poch_q ^ 3).coeff m = - (kTheta (fun t => (-1) ^ t * t)).coeff m := by
    rw [← h, HahnSeries.coeff_neg]
  rw [hc, neg_neg]
  rw [kTheta_coeff_if]
  apply finsum_congr
  intro t
  rw [show thetaQDeg 3 0 t = 3 * Tn t by unfold thetaQDeg; ring]

/-- **Diagonal evaluation.**  `coeffXY (Θx·Θy·Rho) a a = poch_q³ · Q^{3·T a}·(−1)^a`. -/
theorem slice_diagonal (a : ℤ) :
    coeffXY (thetaX_q * thetaY_q * Rho) a a
      = poch_q ^ 3 * HahnSeries.single (3 * Tn a) ((-1 : ℚ) ^ a) := by
  rw [coeffXY_eq_sliceTFamily_hsum]
  apply HahnSeries.ext
  funext E
  rw [HahnSeries.SummableFamily.coeff_hsum]
  -- per-t coeff of sliceTterm a a t = (-1)^{a+t}(a-t+1)[3Ta+3Tt=E].
  have hterm : ∀ t, ((sliceTFamily a a) t).coeff E
      = (if 3 * Tn a + 3 * Tn t = E then (-1 : ℚ) ^ (a + t) * ((a - t : ℤ) + 1) else 0) := by
    intro t
    show (sliceTterm a a t).coeff E = _
    unfold sliceTterm
    rw [HahnSeries.coeff_smul, smul_eq_mul]
    rw [show (a : ℤ) - a = 0 by ring, StringSumQ_zero]
    -- Qpow(3Ta+3Tt) * ((a-t+1)•1) coeff at E.
    rw [show Qpow (3 * Tn a + 3 * Tn t) * ((((a - t : ℤ) : ℚ) + 1) • (1 : K))
        = (((a - t : ℤ) : ℚ) + 1) • Qpow (3 * Tn a + 3 * Tn t) by
      rw [mul_smul_comm, mul_one]]
    rw [HahnSeries.coeff_smul, smul_eq_mul]
    rw [show (Qpow (3 * Tn a + 3 * Tn t)).coeff E
        = (if 3 * Tn a + 3 * Tn t = E then (1 : ℚ) else 0) by
      unfold Qpow; rw [HahnSeries.coeff_single]
      by_cases h : 3 * Tn a + 3 * Tn t = E
      · rw [if_pos h.symm, if_pos h]
      · rw [if_neg (fun hc => h hc.symm), if_neg h]]
    by_cases h : 3 * Tn a + 3 * Tn t = E
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  rw [finsum_congr hterm]
  -- factor (-1)^a and the degree shift; split (a-t+1) = (a+1) - t.
  rw [show (fun t : ℤ => if 3 * Tn a + 3 * Tn t = E
        then (-1 : ℚ) ^ (a + t) * (((a - t : ℤ) : ℚ) + 1) else 0)
      = fun t : ℤ => (-1 : ℚ) ^ a *
          ((a + 1 : ℚ) * (if 3 * Tn t = E - 3 * Tn a then (-1 : ℚ) ^ t else 0)
           - (if 3 * Tn t = E - 3 * Tn a then (-1 : ℚ) ^ t * t else 0)) by
    funext t
    by_cases h : 3 * Tn t = E - 3 * Tn a
    · rw [if_pos h, if_pos h, if_pos (by omega : 3 * Tn a + 3 * Tn t = E),
        zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]
      push_cast; ring
    · rw [if_neg h, if_neg h, if_neg (by omega : ¬ 3 * Tn a + 3 * Tn t = E)]
      simp]
  -- pull out (-1)^a, split the finsum.
  rw [← mul_finsum' (fun t : ℤ => (a + 1 : ℚ) * (if 3 * Tn t = E - 3 * Tn a then (-1 : ℚ) ^ t else 0)
        - (if 3 * Tn t = E - 3 * Tn a then (-1 : ℚ) ^ t * t else 0)) ((-1 : ℚ) ^ a) (by
    -- finite support (⊆ fibre at E - 3Ta).
    apply Set.Finite.subset (kTheta_fiber_finite (E - 3 * Tn a))
    intro t ht; simp only [Function.mem_support] at ht; simp only [Set.mem_setOf_eq]
    by_contra hcon
    rw [show thetaQDeg 3 0 t = 3 * Tn t by unfold thetaQDeg; ring] at hcon
    apply ht
    rw [if_neg (by omega : ¬ 3 * Tn t = E - 3 * Tn a),
      if_neg (by omega : ¬ 3 * Tn t = E - 3 * Tn a), mul_zero, sub_zero])]
  rw [finsum_sub_distrib ?_ ?_]
  · -- first finsum = (a+1)·(theta fibre) ; second = jacobi fibre.
    rw [show (∑ᶠ t : ℤ, (a + 1 : ℚ) * (if 3 * Tn t = E - 3 * Tn a then (-1 : ℚ) ^ t else 0))
        = (a + 1 : ℚ) * ∑ᶠ t : ℤ, (if 3 * Tn t = E - 3 * Tn a then (-1 : ℚ) ^ t else 0) by
      rw [mul_finsum' (fun t : ℤ => if 3 * Tn t = E - 3 * Tn a then (-1 : ℚ) ^ t else 0)
        ((a + 1 : ℚ)) (by
        apply Set.Finite.subset (kTheta_fiber_finite (E - 3 * Tn a))
        intro t ht; simp only [Function.mem_support] at ht; simp only [Set.mem_setOf_eq]
        by_contra hcon
        rw [show thetaQDeg 3 0 t = 3 * Tn t by unfold thetaQDeg; ring] at hcon
        exact ht (by rw [if_neg (by omega : ¬ 3 * Tn t = E - 3 * Tn a)]))]]
    rw [theta_fibre_zero (E - 3 * Tn a), jacobi_fibre (E - 3 * Tn a)]
    -- RHS: (poch^3 * single(3Ta)((-1)^a)).coeff E = (poch^3).coeff(E-3Ta)·(-1)^a.
    rw [HahnSeries.coeff_mul_single]
    ring
  · -- finiteness of the (a+1)-scaled fibre.
    apply Set.Finite.subset (kTheta_fiber_finite (E - 3 * Tn a))
    intro t ht; simp only [Function.mem_support] at ht; simp only [Set.mem_setOf_eq]
    by_contra hcon
    rw [show thetaQDeg 3 0 t = 3 * Tn t by unfold thetaQDeg; ring] at hcon
    exact ht (by rw [if_neg (by omega : ¬ 3 * Tn t = E - 3 * Tn a), mul_zero])
  · apply Set.Finite.subset (kTheta_fiber_finite (E - 3 * Tn a))
    intro t ht; simp only [Function.mem_support] at ht; simp only [Set.mem_setOf_eq]
    by_contra hcon
    rw [show thetaQDeg 3 0 t = 3 * Tn t by unfold thetaQDeg; ring] at hcon
    exact ht (by rw [if_neg (by omega : ¬ 3 * Tn t = E - 3 * Tn a)])

/-! ### The RHS slice and the main Hickerson identity -/

/-- `Θ(xy;q) = thetaMon 3 0 1 1`. -/
noncomputable def thetaXY_q : S := thetaMon 3 0 1 1 (by norm_num)

/-- The `x^i y^j` slice of `Θ(xy;q)`: nonzero only on the diagonal `i = j = n`, where it is
`single (3 T n) ((-1)^n)`. -/
theorem coeffXY_thetaXY_q (i j : ℤ) :
    coeffXY thetaXY_q i j
      = if i = j then HahnSeries.single (3 * Tn i) ((-1 : ℚ) ^ i) else 0 := by
  apply HahnSeries.ext
  funext E
  rw [coeffXY_coeff, coeffQXY]
  unfold thetaXY_q
  rw [thetaMon_coeff]
  -- the n-th term coeff at expQXY E i j is nonzero only if i = n ∧ j = n.
  have hfun : (fun n => (monom (thetaQDeg 3 0 n) (1 * n) (1 * n) ((-1) ^ n)).coeff (expQXY E i j))
      = fun n => if (thetaQDeg 3 0 n = E ∧ i = n ∧ j = n) then (-1 : ℚ) ^ n else 0 := by
    funext n
    unfold monom
    rw [HahnSeries.coeff_single]
    by_cases h : thetaQDeg 3 0 n = E ∧ i = n ∧ j = n
    · obtain ⟨hE, hi, hj⟩ := h
      rw [if_pos (show expQXY E i j = expQXY (thetaQDeg 3 0 n) (1 * n) (1 * n) by
        rw [hE, hi, hj, one_mul]), if_pos ⟨hE, hi, hj⟩]
    · rw [if_neg ?_, if_neg h]
      intro hcon
      obtain ⟨hE, hi, hj⟩ := expQXY_inj hcon
      exact h ⟨hE.symm, by omega, by omega⟩
  rw [hfun]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    rw [finsum_eq_single _ i ?_]
    · rw [HahnSeries.coeff_single]
      by_cases hE : 3 * Tn i = E
      · rw [if_pos ⟨show thetaQDeg 3 0 i = E by unfold thetaQDeg; rw [← hE]; ring, rfl, rfl⟩,
          if_pos hE.symm]
      · rw [if_neg (show ¬ (thetaQDeg 3 0 i = E ∧ i = i ∧ i = i) by
          rintro ⟨hc, _, _⟩; apply hE; rw [← hc]; unfold thetaQDeg; ring),
          if_neg (fun hc => hE hc.symm)]
    · intro n hn
      rw [if_neg (by rintro ⟨_, hi, _⟩; exact hn hi.symm)]
  · rw [if_neg hij]
    apply finsum_eq_zero_of_forall_eq_zero
    intro n
    rw [if_neg (by rintro ⟨_, hi, hj⟩; exact hij (by omega))]

/-- The RHS slice: `coeffXY (embedQ poch_q³ · Θ(xy;q)) i j = poch_q³ · [i=j] single(3 T i)((-1)^i)`. -/
theorem coeffXY_rhs (i j : ℤ) :
    coeffXY (embedQ (poch_q ^ 3) * thetaXY_q) i j
      = if i = j then poch_q ^ 3 * HahnSeries.single (3 * Tn i) ((-1 : ℚ) ^ i) else 0 := by
  rw [coeffXY_embedQ_mul, coeffXY_thetaXY_q]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos hij]
  · rw [if_neg hij, if_neg hij, mul_zero]

/-- **Hickerson's Lemma 10.2 (multiplied form).**
`Θ(x;q) · Θ(y;q) · Rho = (q;q)_∞³ · Θ(xy;q)`. -/
theorem hickerson_mul :
    thetaX_q * thetaY_q * Rho = embedQ (poch_q ^ 3) * thetaXY_q := by
  apply ext_coeffQXY
  intro a i j
  -- compare the (i,j)-slices coefficientwise at Q-degree a.
  have hL : coeffQXY (thetaX_q * thetaY_q * Rho) a i j
      = (coeffXY (thetaX_q * thetaY_q * Rho) i j).coeff a := rfl
  have hR : coeffQXY (embedQ (poch_q ^ 3) * thetaXY_q) a i j
      = (coeffXY (embedQ (poch_q ^ 3) * thetaXY_q) i j).coeff a := rfl
  rw [hL, hR, coeffXY_rhs]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, slice_diagonal i]
  · rw [if_neg hij, slice_off_diagonal i j hij, HahnSeries.coeff_zero]

/-! ## Layer G1 — the substituted Hickerson identity `Θx·Θy·Rho_sub = (q;q)³·Θ(x⁻¹y⁻¹q²;q)`

`Rho_sub` is `Rho(q/x, q/y)`: the two-variable Hahn series with coefficient `ρ(r,s)` at the
exponent `Q^{3(rs+r+s)} x^{-r} y^{-s}`.  The slice extraction mirrors `Rho`'s exactly, with the
modified `Q`-exponent; the `[x^a y^b]` slice decomposes (via `u = r+s`, the `ρ`-string variable)
into `∑'_u (-1)^{a+b+u} Q^{3Ta+3Tb+3·Tplus u+3au} · StringSumQ(u, b−a)`.  Off the diagonal `a≠b`
this telescopes to `0`; on the diagonal it produces `(q;q)³` via the Jacobi-derivative identity. -/

/-- On the `Rho_sub` support, the candidate `Q`-degree `3(rs+r+s)` is `≥ -3`
(minimum at `r=s=-1`, the corner of the open third quadrant). -/
theorem rho_sub_support_ge {r s : ℤ} (h : rho r s ≠ 0) : -3 ≤ 3 * (r * s + r + s) := by
  unfold rho at h
  by_cases h1 : 0 ≤ r ∧ 0 ≤ s
  · obtain ⟨hr, hs⟩ := h1; nlinarith [mul_nonneg hr hs]
  · rw [if_neg h1] at h
    by_cases h2 : r < 0 ∧ s < 0
    · obtain ⟨hr, hs⟩ := h2
      -- r,s ≤ -1: rs+r+s = (r+1)(s+1) - 1 ≥ -1, so 3(...) ≥ -3.
      nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ -(r + 1)) (by omega : (0:ℤ) ≤ -(s + 1))]
    · rw [if_neg h2] at h; exact absurd rfl h

/-- The `Q`-degree-`N` fibre of `Rho_sub` for `N > -3` is finite. -/
theorem rho_sub_positive_q_fiber_finite {N : ℤ} (hN : -3 < N) :
    {p : ℤ × ℤ | 3 * (p.1 * p.2 + p.1 + p.2) = N ∧ rho p.1 p.2 ≠ 0}.Finite := by
  apply Set.Finite.subset (Set.finite_Icc ((-N - 4, -N - 4) : ℤ × ℤ) ((N + 4, N + 4) : ℤ × ℤ))
  rintro ⟨r, s⟩ ⟨hq, hne⟩
  simp only at hq hne
  unfold rho at hne
  rw [Set.mem_Icc, Prod.le_def, Prod.le_def]
  by_cases h1 : 0 ≤ r ∧ 0 ≤ s
  · obtain ⟨hr, hs⟩ := h1
    have hrs : 0 ≤ r * s := mul_nonneg hr hs
    -- 3(rs+r+s)=N ⟹ r+s ≤ N/3 ≤ N, with r,s ≥ 0.
    refine ⟨⟨by omega, by omega⟩, by nlinarith [hrs, hq], by nlinarith [hrs, hq]⟩
  · rw [if_neg h1] at hne
    by_cases h2 : r < 0 ∧ s < 0
    · obtain ⟨hr, hs⟩ := h2
      -- r,s ≤ -1.  If s = -1 then hq forces N = -3, contradicting hN; so s ≤ -2, similarly r ≤ -2.
      have hr2 : r ≤ -2 := by
        by_contra hcon; push_neg at hcon
        have hr1 : r = -1 := by omega
        subst hr1; omega
      have hs2 : s ≤ -2 := by
        by_contra hcon; push_neg at hcon
        have hs1 : s = -1 := by omega
        subst hs1; omega
      have hrnn : (0:ℤ) ≤ -(r + 1) := by omega
      have hsnn : (0:ℤ) ≤ -(s + 1) := by omega
      refine ⟨⟨?_, ?_⟩, by omega, by omega⟩
      · -- lower bound on r:  -(r+1) ≤ (-(r+1))·(-(s+1)) = N/3+1  (since -(s+1) ≥ 1)
        nlinarith [mul_nonneg hrnn hsnn, mul_le_mul_of_nonneg_left
          (show (1:ℤ) ≤ -(s + 1) by omega) hrnn, hq]
      · nlinarith [mul_nonneg hrnn hsnn, mul_le_mul_of_nonneg_right
          (show (1:ℤ) ≤ -(r + 1) by omega) hsnn, hq]
    · rw [if_neg h2] at hne; exact absurd rfl hne

/-- The `Q=-3` boundary fibre of `Rho_sub`, expressed in `ExpXY = Lex(ℤ×ℤ)`:
the two rays `{x=1, y≥1} ∪ {y=1, x≥1}` (the reflection `x-deg = -r ≥ 1`).  Both lie in the
positive quadrant, so the set is partially well-ordered. -/
theorem axesSub_isPWO :
    {y : ExpXY | (((ofLex y).1 = 1 ∧ 1 ≤ (ofLex y).2) ∨
        ((ofLex y).2 = 1 ∧ 1 ≤ (ofLex y).1))}.IsPWO := by
  apply Set.PartiallyWellOrderedOn.subsetProdLex
  · -- x-degree projection ⊆ Ici 1.
    have hsub : (fun (x : ℤ ×ₗ ℤ) => (ofLex x).1) ''
        {y : ExpXY | (((ofLex y).1 = 1 ∧ 1 ≤ (ofLex y).2) ∨
          ((ofLex y).2 = 1 ∧ 1 ≤ (ofLex y).1))} ⊆ Set.Ici (1 : ℤ) := by
      rintro a ⟨y, hy, rfl⟩
      simp only [Set.mem_Ici]
      rcases hy with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact le_of_eq h1.symm
      · exact h2
    refine (?_ : (Set.Ici (1 : ℤ)).IsPWO).mono hsub
    exact (bddBelow_Ici.isWF).isPWO
  · intro a
    by_cases ha : a = 1
    · -- a = 1: fibre = {j : 1 ≤ j} = Ici 1, PWO.
      apply (bddBelow_Ici (a := (1 : ℤ))).isWF.isPWO.mono
      intro j hj
      simp only [Set.mem_setOf_eq, ofLex_toLex] at hj
      rw [Set.mem_Ici]
      rcases hj with ⟨_, h2⟩ | ⟨h2, h3⟩
      · exact h2
      · omega
    · -- a ≠ 1: fibre ⊆ {1}, finite hence PWO.
      apply Set.Finite.isPWO
      apply Set.Finite.subset (Set.finite_singleton (1 : ℤ))
      intro j hj
      simp only [Set.mem_setOf_eq, ofLex_toLex] at hj
      rcases hj with ⟨h1, _⟩ | ⟨h2, _⟩
      · exact absurd h1 ha
      · exact h2

/-- The defining coefficient of `Rho_sub`: `ρ(r,s)` at the exponent `Q^{3(rs+r+s)} x^{-r} y^{-s}`.
In terms of the exponent degrees `(a,i,j)` (with `r = -i`, `s = -j`), nonzero only when
`a = 3(ij - i - j)`, where it equals `ρ(-i,-j)`. -/
noncomputable def rhoCoeffSub (z : ExpQXY) : ℚ :=
  if (ofLex z).1 = 3 * ((ofLex (ofLex z).2).1 * (ofLex (ofLex z).2).2
        - (ofLex (ofLex z).2).1 - (ofLex (ofLex z).2).2)
  then rho (-(ofLex (ofLex z).2).1) (-(ofLex (ofLex z).2).2) else 0

/-- The support of `rhoCoeffSub` is partially well-ordered in the `q`-first lex order. -/
theorem rhoCoeffSub_isPWO : (Function.support rhoCoeffSub).IsPWO := by
  apply Set.PartiallyWellOrderedOn.subsetProdLex
  · -- q-degree projection ⊆ Ici (-3).
    have hsub : (fun (z : ℤ ×ₗ ExpXY) => (ofLex z).1) '' Function.support rhoCoeffSub
        ⊆ Set.Ici (-3 : ℤ) := by
      rintro a ⟨z, hz, rfl⟩
      simp only [Function.mem_support, rhoCoeffSub] at hz
      simp only [Set.mem_Ici]
      by_cases hc : (ofLex z).1 = 3 * ((ofLex (ofLex z).2).1 * (ofLex (ofLex z).2).2
          - (ofLex (ofLex z).2).1 - (ofLex (ofLex z).2).2)
      · rw [if_pos hc] at hz
        rw [hc]
        -- rho(-i,-j) ≠ 0 ⟹ 3((-i)(-j)+(-i)+(-j)) ≥ -3, and ij-i-j = (-i)(-j)+(-i)+(-j).
        have hge := rho_sub_support_ge hz
        have heq : (ofLex (ofLex z).2).1 * (ofLex (ofLex z).2).2
            - (ofLex (ofLex z).2).1 - (ofLex (ofLex z).2).2
            = (-(ofLex (ofLex z).2).1) * (-(ofLex (ofLex z).2).2)
              + (-(ofLex (ofLex z).2).1) + (-(ofLex (ofLex z).2).2) := by ring
        rw [heq]; omega
      · rw [if_neg hc] at hz; exact absurd rfl hz
    refine (?_ : (Set.Ici (-3 : ℤ)).IsPWO).mono hsub
    exact (bddBelow_Ici.isWF).isPWO
  · intro N
    by_cases hN : -3 < N
    · -- N > -3: finite fibre.
      apply Set.Finite.isPWO
      apply Set.Finite.subset
        (Set.Finite.image (fun p : ℤ × ℤ => (toLex (-p.1, -p.2) : ExpXY))
          (rho_sub_positive_q_fiber_finite hN))
      intro y hy
      simp only [Set.mem_setOf_eq, Function.mem_support] at hy
      rw [rhoCoeffSub, ofLex_toLex] at hy
      by_cases hc : N = 3 * ((ofLex y).1 * (ofLex y).2 - (ofLex y).1 - (ofLex y).2)
      · refine ⟨(-(ofLex y).1, -(ofLex y).2), ⟨?_, ?_⟩, ?_⟩
        · -- 3(rs+r+s) = N with r=-(ofLex y).1, s=-(ofLex y).2.
          rw [show (-(ofLex y).1) * (-(ofLex y).2) + (-(ofLex y).1) + (-(ofLex y).2)
            = (ofLex y).1 * (ofLex y).2 - (ofLex y).1 - (ofLex y).2 by ring]; omega
        · rw [if_pos hc] at hy; exact hy
        · simp
      · rw [if_neg hc] at hy; exact absurd rfl hy
    · push_neg at hN
      rcases lt_or_eq_of_le hN with hlt | heq
      · -- N < -3: empty fibre.
        apply Set.Finite.isPWO
        convert Set.finite_empty
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Function.mem_support]
        rw [rhoCoeffSub, ofLex_toLex]
        by_cases hc : N = 3 * ((ofLex y).1 * (ofLex y).2 - (ofLex y).1 - (ofLex y).2)
        · rw [if_pos hc]
          intro hne
          have hge := rho_sub_support_ge hne
          rw [show (-(ofLex y).1) * (-(ofLex y).2) + (-(ofLex y).1) + (-(ofLex y).2)
            = (ofLex y).1 * (ofLex y).2 - (ofLex y).1 - (ofLex y).2 by ring] at hge
          omega
        · rw [if_neg hc]; exact fun h => h rfl
      · -- N = -3: fibre ⊆ the two boundary rays (PWO).
        subst heq
        apply axesSub_isPWO.mono
        intro y hy
        simp only [Set.mem_setOf_eq, Function.mem_support] at hy
        rw [rhoCoeffSub, ofLex_toLex] at hy
        by_cases hc : (-3 : ℤ) = 3 * ((ofLex y).1 * (ofLex y).2 - (ofLex y).1 - (ofLex y).2)
        · rw [if_pos hc] at hy
          -- ij-i-j = -1 ⟹ (i-1)(j-1)=0 ⟹ i=1 ∨ j=1; with ρ(-i,-j)≠0 ⟹ i,j≥1.
          set i := (ofLex y).1
          set j := (ofLex y).2
          have hij : i * j - i - j = -1 := by omega
          have hfac : (i - 1) * (j - 1) = 0 := by nlinarith [hij]
          -- ρ(-i,-j) ≠ 0: with the factorisation forcing i=1 or j=1, and support ⟹ i,j ≥ 1.
          unfold rho at hy
          by_cases hquad : 0 ≤ -i ∧ 0 ≤ -j
          · -- closed-1st for (-i,-j): i ≤ 0, j ≤ 0.  But then ij-i-j ≥ 0 > -1, contradiction.
            exfalso; obtain ⟨hi, hj⟩ := hquad; nlinarith [hij, mul_nonneg hi hj]
          · rw [if_neg hquad] at hy
            by_cases hquad2 : -i < 0 ∧ -j < 0
            · -- open-3rd: i ≥ 1, j ≥ 1; (i-1)(j-1)=0 ⟹ i=1 ∨ j=1.
              obtain ⟨hi, hj⟩ := hquad2
              rcases mul_eq_zero.mp hfac with h | h
              · left; exact ⟨by omega, by omega⟩
              · right; exact ⟨by omega, by omega⟩
            · rw [if_neg hquad2] at hy; exact absurd rfl hy
        · rw [if_neg hc] at hy; exact absurd rfl hy

/-- `Rho_sub = Rho(q/x,q/y)`: the two-variable Hahn series with coefficient `ρ(r,s)` at
`Q^{3(rs+r+s)} x^{-r} y^{-s}`. -/
noncomputable def Rho_sub : S where
  coeff := rhoCoeffSub
  isPWO_support' := rhoCoeffSub_isPWO

/-- The `Q^a x^i y^j` coefficient of `Rho_sub`. -/
theorem coeffQXY_Rho_sub (a i j : ℤ) :
    coeffQXY Rho_sub a i j = if a = 3 * (i * j - i - j) then rho (-i) (-j) else 0 := by
  unfold coeffQXY Rho_sub
  show rhoCoeffSub (expQXY a i j) = _
  rw [rhoCoeffSub]
  rw [qdeg_expQXY, xdeg_expQXY, ydeg_expQXY]

/-- The ρ summable family for `Rho_sub`: `(r,s) ↦ monom (3(rs+r+s)) (-r) (-s) (ρ r s)`. -/
noncomputable def rhoFamilySub : HahnSeries.SummableFamily ExpQXY ℚ (ℤ × ℤ) where
  toFun := fun p => monom (3 * (p.1 * p.2 + p.1 + p.2)) (-p.1) (-p.2) (rho p.1 p.2)
  isPWO_iUnion_support' := by
    refine rhoCoeffSub_isPWO.mono (Set.iUnion_subset (fun p => ?_))
    intro g hg
    have hgeq : g = expQXY (3 * (p.1 * p.2 + p.1 + p.2)) (-p.1) (-p.2) :=
      HahnSeries.support_single_subset hg
    rw [HahnSeries.mem_support] at hg
    simp only [Function.mem_support]
    rw [hgeq, rhoCoeffSub, qdeg_expQXY, xdeg_expQXY, ydeg_expQXY]
    rw [if_pos (by ring), neg_neg, neg_neg]
    unfold monom at hg
    rw [HahnSeries.coeff_single, if_pos hgeq] at hg
    exact hg
  finite_co_support' := by
    intro g
    apply Set.Finite.subset (Set.finite_singleton
      ((-(ofLex (ofLex g).2).1, -(ofLex (ofLex g).2).2)))
    intro p hp
    simp only [Set.mem_singleton_iff] at hp ⊢
    by_contra hne
    apply hp
    unfold monom
    rw [HahnSeries.coeff_single_of_ne]
    intro hcon
    apply hne
    have hx : (ofLex (ofLex g).2).1 = -p.1 := by rw [hcon, xdeg_expQXY]
    have hy : (ofLex (ofLex g).2).2 = -p.2 := by rw [hcon, ydeg_expQXY]
    rw [hx, hy]; simp

/-- `rhoFamilySub.hsum = Rho_sub`. -/
theorem rhoFamilySub_hsum : rhoFamilySub.hsum = Rho_sub := by
  apply HahnSeries.ext
  funext g
  rw [HahnSeries.SummableFamily.coeff_hsum]
  rw [finsum_eq_single _ (-(ofLex (ofLex g).2).1, -(ofLex (ofLex g).2).2) ?_]
  · set x := (ofLex (ofLex g).2).1 with hxdef
    set y := (ofLex (ofLex g).2).2 with hydef
    show (monom (3 * ((-x) * (-y) + (-x) + (-y))) (-(-x)) (-(-y)) (rho (-x) (-y))).coeff g
      = Rho_sub.coeff g
    rw [neg_neg, neg_neg]
    show (HahnSeries.single (expQXY (3 * ((-x) * (-y) + (-x) + (-y))) x y) (rho (-x) (-y))).coeff g
      = rhoCoeffSub g
    rw [HahnSeries.coeff_single, rhoCoeffSub, ← hxdef, ← hydef]
    by_cases hc : (ofLex g).1 = 3 * (x * y - x - y)
    · have hqeq : (3 : ℤ) * ((-x) * (-y) + (-x) + (-y)) = (ofLex g).1 := by
        rw [hc]; ring
      have hgeq : g = expQXY (3 * ((-x) * (-y) + (-x) + (-y))) x y := by
        rw [hqeq, hxdef, hydef]; exact expQXY_eta g
      rw [if_pos hgeq, if_pos hc]
    · rw [if_neg ?_, if_neg hc]
      intro hcon
      apply hc
      rw [hcon, qdeg_expQXY]
      ring
  · intro p hp
    show (monom (3 * (p.1 * p.2 + p.1 + p.2)) (-p.1) (-p.2) (rho p.1 p.2)).coeff g = 0
    unfold monom
    rw [HahnSeries.coeff_single_of_ne]
    intro hcon
    apply hp
    have hx : (ofLex (ofLex g).2).1 = -p.1 := by rw [hcon, xdeg_expQXY]
    have hy : (ofLex (ofLex g).2).2 = -p.2 := by rw [hcon, ydeg_expQXY]
    rw [hx, hy]; simp

/-! **The 10.33-pattern lemma** (FE with weight `w = x⁻¹y⁻¹q`):
`monom 3 (-1) (-1) 1 · Θ(x⁻¹y⁻¹q²;q) = - Θ(x⁻¹y⁻¹q;q)`, i.e.
`monom 3 (-1) (-1) 1 * thetaMon 3 6 (-1) (-1) = - thetaMon 3 3 (-1) (-1)`.

### The `Rho_sub` slice extraction (mirror of the `Rho` machinery, modified `Q`-exponent) -/

/-- The triple product `Θ(x;q)·Θ(y;q)·Rho_sub` as a summable family over `(ℤ×ℤ)×(ℤ×ℤ)`. -/
noncomputable def prodFamSub : HahnSeries.SummableFamily ExpQXY ℚ ((ℤ × ℤ) × (ℤ × ℤ)) :=
  HahnSeries.SummableFamily.mul
    (HahnSeries.SummableFamily.mul (thetaFamily 3 0 1 0 (by norm_num))
      (thetaFamily 3 0 0 1 (by norm_num))) rhoFamilySub

/-- `prodFamSub.hsum = Θ(x;q)·Θ(y;q)·Rho_sub`. -/
theorem prodFamSub_hsum : prodFamSub.hsum = thetaX_q * thetaY_q * Rho_sub := by
  unfold prodFamSub
  rw [HahnSeries.SummableFamily.hsum_mul, HahnSeries.SummableFamily.hsum_mul, rhoFamilySub_hsum]
  rfl

/-- The `(k,l,r,s)`-term of `prodFamSub` is a single monomial (x-degree `k-r`, y-degree `l-s`). -/
theorem prodFamSub_term (k l r s : ℤ) :
    prodFamSub ((k, l), (r, s))
      = monom (3 * Tn k + 3 * Tn l + 3 * (r * s + r + s)) (k - r) (l - s)
          ((-1) ^ (k + l) * rho r s) := by
  unfold prodFamSub
  show (monom (thetaQDeg 3 0 k) (1 * k) (0 * k) ((-1) ^ k)
        * monom (thetaQDeg 3 0 l) (0 * l) (1 * l) ((-1) ^ l))
        * monom (3 * (r * s + r + s)) (-r) (-s) (rho r s) = _
  rw [monom_mul, monom_mul]
  apply monom_eq_monom
  · unfold thetaQDeg; ring
  · ring
  · ring
  · rw [zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]

/-- The `(k,l,r,s)`-term coefficient at `expQXY D a b` is the indicator of the antidiagonal
`k - r = a ∧ l - s = b`. -/
theorem prodFamSub_term_coeff (k l r s a b D : ℤ) :
    (prodFamSub ((k, l), (r, s))).coeff (expQXY D a b)
      = if (3 * Tn k + 3 * Tn l + 3 * (r * s + r + s) = D ∧ k - r = a ∧ l - s = b)
        then (-1) ^ (k + l) * rho r s else 0 := by
  rw [prodFamSub_term]
  unfold monom
  rw [HahnSeries.coeff_single]
  by_cases h : (3 * Tn k + 3 * Tn l + 3 * (r * s + r + s) = D ∧ k - r = a ∧ l - s = b)
  · obtain ⟨hD, ha, hb⟩ := h
    rw [if_pos (show expQXY D a b
          = expQXY (3 * Tn k + 3 * Tn l + 3 * (r * s + r + s)) (k - r) (l - s) by rw [hD, ha, hb]),
        if_pos ⟨hD, ha, hb⟩]
  · rw [if_neg ?_, if_neg h]
    intro hcon
    apply h
    obtain ⟨hD, hx, hy⟩ := expQXY_inj hcon
    exact ⟨hD.symm, hx.symm, hy.symm⟩

/-- The co-support finiteness needed to curry the 4-index finsum. -/
theorem prodFamSub_coeff_finite (a b D : ℤ) :
    (Function.support (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      (prodFamSub p).coeff (expQXY D a b))).Finite :=
  prodFamSub.finite_co_support' (expQXY D a b)

/-- The `Rho_sub` slice coefficient at `Q`-degree `D` collapses to a double finsum over `(k,l)`
with `r = k-a`, `s = l-b` forced by the `x,y`-degrees. -/
theorem sliceSub_coeff_eq (a b D : ℤ) :
    (coeffXY (thetaX_q * thetaY_q * Rho_sub) a b).coeff D
      = ∑ᶠ p : ℤ × ℤ,
          (if 3 * Tn p.1 + 3 * Tn p.2 + 3 * ((p.1 - a) * (p.2 - b) + (p.1 - a) + (p.2 - b)) = D
            then (-1) ^ (p.1 + p.2) * rho (p.1 - a) (p.2 - b) else 0) := by
  rw [coeffXY_coeff, coeffQXY, ← prodFamSub_hsum, HahnSeries.SummableFamily.coeff_hsum]
  have hterm : (fun p : (ℤ × ℤ) × (ℤ × ℤ) => (prodFamSub p).coeff (expQXY D a b))
      = fun p => if (3 * Tn p.1.1 + 3 * Tn p.1.2 + 3 * (p.2.1 * p.2.2 + p.2.1 + p.2.2) = D
          ∧ p.1.1 - p.2.1 = a ∧ p.1.2 - p.2.2 = b)
        then (-1) ^ (p.1.1 + p.1.2) * rho p.2.1 p.2.2 else 0 := by
    funext p
    obtain ⟨⟨k, l⟩, ⟨r, s⟩⟩ := p
    exact prodFamSub_term_coeff k l r s a b D
  rw [hterm]
  rw [finsum_curry _ (by rw [← hterm]; exact prodFamSub_coeff_finite a b D)]
  apply finsum_congr
  rintro ⟨k, l⟩
  rw [finsum_eq_single _ (k - a, l - b) ?_]
  · simp only []
    by_cases hq : 3 * Tn k + 3 * Tn l + 3 * ((k - a) * (l - b) + (k - a) + (l - b)) = D
    · rw [if_pos ⟨hq, by ring, by ring⟩, if_pos hq]
    · rw [if_neg (by rintro ⟨h, _, _⟩; exact hq h), if_neg hq]
  · rintro ⟨r, s⟩ hrs
    simp only []
    rw [if_neg ?_]
    rintro ⟨_, hx, hy⟩
    apply hrs
    have : r = k - a ∧ s = l - b := ⟨by omega, by omega⟩
    rw [this.1, this.2]

/-- The reindexing bijection mapping `(u,s)` to `(k,l) = (u-s+a, s+b)` (so that `u = (k-a)+(l-b)`
is the ρ-string variable `r+s`, and the second component `s = l-b`). -/
def reindexKLSub (a b : ℤ) : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun := fun q => (q.1 - q.2 + a, q.2 + b)
  invFun := fun p => (p.1 - a + (p.2 - b), p.2 - b)
  left_inv := by rintro ⟨u, s⟩; simp only [Prod.mk.injEq]; constructor <;> ring
  right_inv := by rintro ⟨k, l⟩; simp only [Prod.mk.injEq]; constructor <;> ring

/-- After reindexing `(k,l) ↦ (u,s)`, the `Rho_sub` slice at `D` becomes a `(u,s)`-finsum with
`Q`-degree `3T a + 3T b + 3·Tplus u + 3 a u + 3(b−a)s` and sign `(-1)^{a+b+u}`. -/
theorem sliceSub_coeff_reindexed (a b D : ℤ) :
    (coeffXY (thetaX_q * thetaY_q * Rho_sub) a b).coeff D
      = ∑ᶠ p : ℤ × ℤ,
          (if 3 * Tn a + 3 * Tn b + 3 * Tplus p.1 + 3 * a * p.1 + 3 * (b - a) * p.2 = D
            then (-1) ^ (a + b + p.1) * rho (p.1 - p.2) p.2 else 0) := by
  rw [sliceSub_coeff_eq]
  rw [← finsum_comp_equiv (reindexKLSub a b)]
  apply finsum_congr
  rintro ⟨u, s⟩
  show (if 3 * Tn (u - s + a) + 3 * Tn (s + b)
        + 3 * (((u - s + a) - a) * ((s + b) - b) + ((u - s + a) - a) + ((s + b) - b)) = D
      then (-1) ^ ((u - s + a) + (s + b)) * rho ((u - s + a) - a) ((s + b) - b) else 0)
    = (if 3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u + 3 * (b - a) * s = D
      then (-1) ^ (a + b + u) * rho (u - s) s else 0)
  have hexp : 3 * Tn (u - s + a) + 3 * Tn (s + b)
        + 3 * (((u - s + a) - a) * ((s + b) - b) + ((u - s + a) - a) + ((s + b) - b))
      = 3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u + 3 * (b - a) * s := by
    have h1 := two_mul_Tn (u - s + a)
    have h2 := two_mul_Tn (s + b)
    have h3 := two_mul_Tn a
    have h4 := two_mul_Tn b
    have h5 := two_mul_Tplus u
    have key : 2 * (3 * Tn (u - s + a) + 3 * Tn (s + b)
          + 3 * (((u - s + a) - a) * ((s + b) - b) + ((u - s + a) - a) + ((s + b) - b)))
        = 2 * (3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u + 3 * (b - a) * s) := by
      rw [show 2 * (3 * Tn (u - s + a) + 3 * Tn (s + b)
            + 3 * (((u - s + a) - a) * ((s + b) - b) + ((u - s + a) - a) + ((s + b) - b)))
          = 3 * (2 * Tn (u - s + a)) + 3 * (2 * Tn (s + b))
            + 6 * (((u - s + a) - a) * ((s + b) - b) + ((u - s + a) - a) + ((s + b) - b)) by ring,
        h1, h2,
        show 2 * (3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u + 3 * (b - a) * s)
          = 3 * (2 * Tn a) + 3 * (2 * Tn b) + 3 * (2 * Tplus u) + 6 * a * u + 6 * (b - a) * s by ring,
        h3, h4, h5]
      ring
    omega
  have hsign : (-1 : ℚ) ^ ((u - s + a) + (s + b)) = (-1) ^ (a + b + u) := by
    congr 1; ring
  have hrho : rho ((u - s + a) - a) ((s + b) - b) = rho (u - s) s := by
    congr 1 <;> ring
  rw [hexp, hsign, hrho]

/-- The single-`u` term of the `Rho_sub` slice:
`(-1)^{a+b+u} · Q^{3Ta+3Tb+3·Tplus u+3au} · StringSumQ(u, b−a)`. -/
noncomputable def sliceSubUterm (a b u : ℤ) : K :=
  ((-1 : ℚ) ^ (a + b + u))
    • (Qpow (3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u) * StringSumQ u (b - a))

/-- Coefficient of `sliceSubUterm a b u` at `Q`-degree `D`. -/
theorem sliceSubUterm_coeff (a b u D : ℤ) :
    (sliceSubUterm a b u).coeff D
      = ∑ᶠ s : ℤ,
          (if 3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u + 3 * (b - a) * s = D
            then (-1) ^ (a + b + u) * rho (u - s) s else 0) := by
  unfold sliceSubUterm
  rw [HahnSeries.coeff_smul, smul_eq_mul]
  rw [show (Qpow (3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u) * StringSumQ u (b - a)).coeff D
      = (StringSumQ u (b - a)).coeff (D - (3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u)) by
    unfold Qpow; rw [HahnSeries.coeff_single_mul, one_mul]]
  rw [StringSumQ_coeff]
  rw [mul_finsum' (fun s : ℤ => if 3 * (b - a) * s = D - (3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u)
        then rho (u - s) s else 0) ((-1) ^ (a + b + u)) (by
    apply Set.Finite.subset (stringSupp_finite u)
    intro s hs
    simp only [Function.mem_support] at hs
    simp only [Set.mem_setOf_eq]
    intro hc
    apply hs
    by_cases h : 3 * (b - a) * s = D - (3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u)
    · rw [if_pos h, hc]
    · rw [if_neg h])]
  apply finsum_congr
  intro s
  by_cases h : 3 * (b - a) * s = D - (3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u)
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega), mul_zero]

/-- The reverse `(u,s) ↦ (k,l) = (u-s+a, s+b)` exponent identity (used in the bounds). -/
theorem sliceSub_exp_kl (a b u s : ℤ) :
    3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u + 3 * (b - a) * s
      = 3 * Tn (u - s + a) + 3 * Tn (s + b) + 3 * ((u - s) * s + (u - s) + s) := by
  have h1 := two_mul_Tn (u - s + a)
  have h2 := two_mul_Tn (s + b)
  have h3 := two_mul_Tn a
  have h4 := two_mul_Tn b
  have h5 := two_mul_Tplus u
  have key : 2 * (3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u + 3 * (b - a) * s)
      = 2 * (3 * Tn (u - s + a) + 3 * Tn (s + b) + 3 * ((u - s) * s + (u - s) + s)) := by
    rw [show 2 * (3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u + 3 * (b - a) * s)
        = 3 * (2 * Tn a) + 3 * (2 * Tn b) + 3 * (2 * Tplus u) + 6 * a * u + 6 * (b - a) * s by ring,
      h3, h4, h5,
      show 2 * (3 * Tn (u - s + a) + 3 * Tn (s + b) + 3 * ((u - s) * s + (u - s) + s))
        = 3 * (2 * Tn (u - s + a)) + 3 * (2 * Tn (s + b)) + 6 * ((u - s) * s + (u - s) + s) by ring,
      h1, h2]
    ring
  omega

/-- Each `Q`-degree in the support of `sliceSubUterm a b u` is `≥ -3`. -/
theorem sliceSubUterm_support_nonneg (a b u : ℤ) :
    (sliceSubUterm a b u).support ⊆ Set.Ici (-3 : ℤ) := by
  intro E hE
  rw [HahnSeries.mem_support] at hE
  rw [Set.mem_Ici]
  by_contra hneg
  push_neg at hneg
  apply hE
  rw [sliceSubUterm_coeff]
  apply finsum_eq_zero_of_forall_eq_zero
  intro s
  by_cases hc : 3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u + 3 * (b - a) * s = E
  · rw [if_pos hc]
    by_cases hr : rho (u - s) s = 0
    · rw [hr, mul_zero]
    · exfalso
      have hrs : 0 ≤ 3 * (u - s) * s := rho_support_nonneg_q hr
      have hTk : 0 ≤ Tn (u - s + a) := Tn_nonneg _
      have hTl : 0 ≤ Tn (s + b) := Tn_nonneg _
      rw [sliceSub_exp_kl] at hc
      -- E = 3Tk+3Tl+3((u-s)s+(u-s)+s) with the cross term ≥ -1 (since rs ≥ 0, r+s arbitrary…)
      -- but (u-s)s+(u-s)+s = (u-s)(s+1)+s; use rho support to bound below by -1.
      have hcross : -1 ≤ (u - s) * s + (u - s) + s := by
        -- on the ρ support either both ≥ 0 or both ≤ -1; in either case ≥ -1.
        unfold rho at hr
        by_cases h1 : 0 ≤ u - s ∧ 0 ≤ s
        · obtain ⟨hi, hj⟩ := h1; nlinarith [mul_nonneg hi hj]
        · rw [if_neg h1] at hr
          by_cases h2 : u - s < 0 ∧ s < 0
          · obtain ⟨hi, hj⟩ := h2
            nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ -((u - s) + 1)) (by omega : (0:ℤ) ≤ -(s + 1))]
          · rw [if_neg h2] at hr; exact absurd rfl hr
      omega
  · rw [if_neg hc]

/-- The co-support of the `sliceSubUterm`-family at `E` is finite. -/
theorem sliceSubUterm_co_support_finite (a b E : ℤ) :
    {u : ℤ | (sliceSubUterm a b u).coeff E ≠ 0}.Finite := by
  apply Set.Finite.subset (Set.finite_Icc (-(E + 4) - (E + 4) - a - b) ((E + 4) + (E + 4) - a - b))
  intro u hu
  simp only [Set.mem_setOf_eq] at hu
  rw [sliceSubUterm_coeff] at hu
  rw [Set.mem_Icc]
  by_contra hubound
  apply hu
  apply finsum_eq_zero_of_forall_eq_zero
  intro s
  by_cases hc : 3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u + 3 * (b - a) * s = E
  · rw [if_pos hc]
    by_cases hr0 : rho (u - s) s = 0
    · rw [hr0, mul_zero]
    · exfalso
      apply hubound
      have hTk : 0 ≤ Tn (u - s + a) := Tn_nonneg _
      have hTl : 0 ≤ Tn (s + b) := Tn_nonneg _
      have hcross : -1 ≤ (u - s) * s + (u - s) + s := by
        unfold rho at hr0
        by_cases h1 : 0 ≤ u - s ∧ 0 ≤ s
        · obtain ⟨hi, hj⟩ := h1; nlinarith [mul_nonneg hi hj]
        · rw [if_neg h1] at hr0
          by_cases h2 : u - s < 0 ∧ s < 0
          · obtain ⟨hi, hj⟩ := h2
            nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ -((u - s) + 1)) (by omega : (0:ℤ) ≤ -(s + 1))]
          · rw [if_neg h2] at hr0; exact absurd rfl hr0
      rw [sliceSub_exp_kl] at hc
      have hTkE : Tn (u - s + a) ≤ E + 3 := by omega
      have hTlE : Tn (s + b) ≤ E + 3 := by omega
      obtain ⟨hk_lb, hk_ub⟩ := abs_le_of_Tn_le hTkE
      obtain ⟨hl_lb, hl_ub⟩ := abs_le_of_Tn_le hTlE
      -- u = (u-s+a) + (s+b) - a - b, both bracket terms bounded.
      constructor <;> omega
  · rw [if_neg hc]

/-- The `(u,s)` antidiagonal `{3Ta+3Tb+3Tplus u+3au+3(b-a)s = D, ρ≠0}` is finite. -/
theorem us_antidiagonal_finite (a b D : ℤ) :
    (Function.support (fun p : ℤ × ℤ =>
      if 3 * Tn a + 3 * Tn b + 3 * Tplus p.1 + 3 * a * p.1 + 3 * (b - a) * p.2 = D
        then (-1 : ℚ) ^ (a + b + p.1) * rho (p.1 - p.2) p.2 else 0)).Finite := by
  apply Set.Finite.subset (Set.finite_Icc
    ((-(D + 4) - (D + 4) - a - b, -(D + 4) - b) : ℤ × ℤ)
    (((D + 4) + (D + 4) - a - b, (D + 4) - b) : ℤ × ℤ))
  rintro ⟨u, s⟩ hus
  simp only [Function.mem_support] at hus
  by_cases hcc : 3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u + 3 * (b - a) * s = D
  · rw [if_pos hcc] at hus
    have hr : rho (u - s) s ≠ 0 := fun h0 => hus (by rw [h0, mul_zero])
    have hTk : 0 ≤ Tn (u - s + a) := Tn_nonneg _
    have hTl : 0 ≤ Tn (s + b) := Tn_nonneg _
    have hcross : -1 ≤ (u - s) * s + (u - s) + s := by
      unfold rho at hr
      by_cases h1 : 0 ≤ u - s ∧ 0 ≤ s
      · obtain ⟨hi, hj⟩ := h1; nlinarith [mul_nonneg hi hj]
      · rw [if_neg h1] at hr
        by_cases h2 : u - s < 0 ∧ s < 0
        · obtain ⟨hi, hj⟩ := h2
          nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ -((u - s) + 1)) (by omega : (0:ℤ) ≤ -(s + 1))]
        · rw [if_neg h2] at hr; exact absurd rfl hr
    rw [sliceSub_exp_kl] at hcc
    have hTkE : Tn (u - s + a) ≤ D + 3 := by omega
    have hTlE : Tn (s + b) ≤ D + 3 := by omega
    obtain ⟨hk_lb, hk_ub⟩ := abs_le_of_Tn_le hTkE
    obtain ⟨hl_lb, hl_ub⟩ := abs_le_of_Tn_le hTlE
    rw [Set.mem_Icc, Prod.le_def, Prod.le_def]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [] <;> omega
  · rw [if_neg hcc] at hus; exact absurd rfl hus

/-- The slice summable family `u ↦ sliceSubUterm a b u` over `ℤ`. -/
noncomputable def sliceSubUFamily (a b : ℤ) : HahnSeries.SummableFamily ℤ ℚ ℤ where
  toFun := fun u => sliceSubUterm a b u
  isPWO_iUnion_support' := by
    refine ((bddBelow_Ici (a := (-3 : ℤ))).isWF.isPWO).mono (Set.iUnion_subset (fun u => ?_))
    exact sliceSubUterm_support_nonneg a b u
  finite_co_support' := fun E => sliceSubUterm_co_support_finite a b E

/-- Coefficient of `sliceSubUFamily.hsum` at `D`. -/
theorem sliceSubUFamily_hsum_coeff (a b D : ℤ) :
    (sliceSubUFamily a b).hsum.coeff D = ∑ᶠ u : ℤ, (sliceSubUterm a b u).coeff D := by
  rw [HahnSeries.SummableFamily.coeff_hsum]; rfl

/-- **The `Rho_sub` slice equals the `u`-summed family**:
`coeffXY (Θx·Θy·Rho_sub) a b = ∑'_u sliceSubUterm a b u`. -/
theorem coeffXY_eq_sliceSubUFamily_hsum (a b : ℤ) :
    coeffXY (thetaX_q * thetaY_q * Rho_sub) a b = (sliceSubUFamily a b).hsum := by
  apply HahnSeries.ext
  funext D
  rw [sliceSub_coeff_reindexed a b D, sliceSubUFamily_hsum_coeff]
  have hRHS : (∑ᶠ u : ℤ, (sliceSubUterm a b u).coeff D)
      = ∑ᶠ p : ℤ × ℤ,
          (if 3 * Tn a + 3 * Tn b + 3 * Tplus p.1 + 3 * a * p.1 + 3 * (b - a) * p.2 = D
            then (-1) ^ (a + b + p.1) * rho (p.1 - p.2) p.2 else 0) := by
    rw [finsum_curry (fun p : ℤ × ℤ =>
      if 3 * Tn a + 3 * Tn b + 3 * Tplus p.1 + 3 * a * p.1 + 3 * (b - a) * p.2 = D
        then (-1) ^ (a + b + p.1) * rho (p.1 - p.2) p.2 else 0) (us_antidiagonal_finite a b D)]
    apply finsum_congr
    intro u
    rw [sliceSubUterm_coeff]
  exact hRHS.symm

/-- The telescoped `Rho_sub` `u`-term: `(1−Q^{3(b−a)})·sliceSubUterm a b u
= (-1)^{a+b+u}·(Q^{C} − Q^{C+3(b−a)(u+1)})` with `C = 3Ta+3Tb+3·Tplus u+3au`. -/
theorem one_sub_Qpow_mul_sliceSubUterm (a b u : ℤ) :
    (1 - Qpow (3 * (b - a))) * sliceSubUterm a b u
      = ((-1 : ℚ) ^ (a + b + u)) • (Qpow (3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u)
          - Qpow (3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u + 3 * (b - a) * (u + 1))) := by
  unfold sliceSubUterm
  rw [mul_smul_comm, ← mul_assoc]
  rw [show (1 - Qpow (3 * (b - a))) * Qpow (3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u)
      = Qpow (3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u) * (1 - Qpow (3 * (b - a))) by ring]
  rw [mul_assoc, StringSumQ_mul_one_sub u (b - a)]
  rw [mul_sub, mul_one, Qpow_mul]

/-- The smul'd `Rho_sub` family term. -/
theorem smul_sliceSubUFamily_toFun (a b u : ℤ) :
    (((1 : K) - Qpow (3 * (b - a))) • sliceSubUFamily a b) u
      = (1 - Qpow (3 * (b - a))) * sliceSubUterm a b u := rfl

/-- **Off-diagonal vanishing for `Rho_sub`.**  For `a ≠ b`, `coeffXY (Θx·Θy·Rho_sub) a b = 0`. -/
theorem sliceSub_off_diagonal (a b : ℤ) (hab : a ≠ b) :
    coeffXY (thetaX_q * thetaY_q * Rho_sub) a b = 0 := by
  have hd : b - a ≠ 0 := by omega
  have hzero : (1 - Qpow (3 * (b - a))) * coeffXY (thetaX_q * thetaY_q * Rho_sub) a b = 0 := by
    rw [coeffXY_eq_sliceSubUFamily_hsum, ← HahnSeries.SummableFamily.hsum_smul]
    apply HahnSeries.ext
    funext E
    rw [HahnSeries.SummableFamily.coeff_hsum, HahnSeries.coeff_zero]
    have hterm : ∀ u, ((((1 : K) - Qpow (3 * (b - a))) • sliceSubUFamily a b) u).coeff E
        = (if 3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u = E then (-1 : ℚ) ^ (a + b + u) else 0)
          - (if 3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u + 3 * (b - a) * (u + 1) = E
              then (-1 : ℚ) ^ (a + b + u) else 0) := by
      intro u
      rw [smul_sliceSubUFamily_toFun, one_sub_Qpow_mul_sliceSubUterm]
      rw [HahnSeries.coeff_smul, smul_eq_mul, HahnSeries.coeff_sub]
      rw [show (Qpow (3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u)).coeff E
          = (if 3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u = E then (1 : ℚ) else 0) by
        unfold Qpow; rw [HahnSeries.coeff_single]
        by_cases h : 3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u = E
        · rw [if_pos h.symm, if_pos h]
        · rw [if_neg (fun hc => h hc.symm), if_neg h]]
      rw [show (Qpow (3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u + 3 * (b - a) * (u + 1))).coeff E
          = (if 3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u + 3 * (b - a) * (u + 1) = E
              then (1 : ℚ) else 0) by
        unfold Qpow; rw [HahnSeries.coeff_single]
        by_cases h : 3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u + 3 * (b - a) * (u + 1) = E
        · rw [if_pos h.symm, if_pos h]
        · rw [if_neg (fun hc => h hc.symm), if_neg h]]
      rw [mul_sub]
      congr 1 <;> (split_ifs <;> ring)
    rw [finsum_congr hterm]
    rw [finsum_sub_distrib ?_ ?_]
    · -- both u-theta sums vanish: exponents `3Tn u+3(a+1)u` (shifted by const) and `3Tn u+3(b+1)u`.
      have h1 : (∑ᶠ u : ℤ, (if 3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u = E
          then (-1 : ℚ) ^ (a + b + u) else 0)) = 0 := by
        rw [show (fun u : ℤ => if 3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u = E
              then (-1 : ℚ) ^ (a + b + u) else 0)
            = fun u : ℤ => (-1 : ℚ) ^ (a + b) *
                (if 3 * Tn u - 3 * (-(a + 1)) * u = E - 3 * Tn a - 3 * Tn b
                  then (-1 : ℚ) ^ u else 0) by
          funext u
          have halg : 3 * Tplus u + 3 * a * u = 3 * Tn u - 3 * (-(a + 1)) * u := by
            have hp := two_mul_Tplus u; have hn := two_mul_Tn u
            have hdiff : Tplus u = Tn u + u := Tplus_eq_Tn_add u
            rw [hdiff]; ring
          by_cases hc : 3 * Tn u - 3 * (-(a + 1)) * u = E - 3 * Tn a - 3 * Tn b
          · rw [if_pos hc, if_pos (by omega),
              zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]
          · rw [if_neg hc, if_neg (by omega), mul_zero]]
        rw [← mul_finsum' (fun u : ℤ => if 3 * Tn u - 3 * (-(a + 1)) * u = E - 3 * Tn a - 3 * Tn b
              then (-1 : ℚ) ^ u else 0) ((-1 : ℚ) ^ (a + b)) (by
          apply Set.Finite.subset (thetaQDeg_finite_fiber 3 (-3 * (-(a + 1))) (by norm_num)
            (E - 3 * Tn a - 3 * Tn b))
          intro u hu; simp only [Function.mem_support] at hu; simp only [Set.mem_setOf_eq]
          by_contra hcon
          rw [show thetaQDeg 3 (-3 * (-(a + 1))) u = 3 * Tn u - 3 * (-(a + 1)) * u by
            unfold thetaQDeg; ring] at hcon
          exact hu (by rw [if_neg (by omega)]))]
        rw [theta_fibre_zero_shifted (-(a + 1)) (E - 3 * Tn a - 3 * Tn b), mul_zero]
      have h2 : (∑ᶠ u : ℤ, (if 3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u + 3 * (b - a) * (u + 1)
          = E then (-1 : ℚ) ^ (a + b + u) else 0)) = 0 := by
        rw [show (fun u : ℤ => if 3 * Tn a + 3 * Tn b + 3 * Tplus u + 3 * a * u + 3 * (b - a) * (u + 1)
              = E then (-1 : ℚ) ^ (a + b + u) else 0)
            = fun u : ℤ => (-1 : ℚ) ^ (a + b) *
                (if 3 * Tn u - 3 * (-(b + 1)) * u
                    = E - 3 * Tn a - 3 * Tn b - 3 * (b - a) then (-1 : ℚ) ^ u else 0) by
          funext u
          have halg : 3 * Tplus u + 3 * a * u + 3 * (b - a) * (u + 1)
              = 3 * Tn u - 3 * (-(b + 1)) * u + 3 * (b - a) := by
            have hp := two_mul_Tplus u; have hn := two_mul_Tn u
            have hdiff : Tplus u = Tn u + u := Tplus_eq_Tn_add u
            rw [hdiff]; ring
          by_cases hc : 3 * Tn u - 3 * (-(b + 1)) * u = E - 3 * Tn a - 3 * Tn b - 3 * (b - a)
          · rw [if_pos hc, if_pos (by omega), zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]
          · rw [if_neg hc, if_neg (by omega), mul_zero]]
        rw [← mul_finsum' (fun u : ℤ => if 3 * Tn u - 3 * (-(b + 1)) * u
              = E - 3 * Tn a - 3 * Tn b - 3 * (b - a) then (-1 : ℚ) ^ u else 0)
          ((-1 : ℚ) ^ (a + b)) (by
          apply Set.Finite.subset (thetaQDeg_finite_fiber 3 (-3 * (-(b + 1))) (by norm_num)
            (E - 3 * Tn a - 3 * Tn b - 3 * (b - a)))
          intro u hu; simp only [Function.mem_support] at hu; simp only [Set.mem_setOf_eq]
          by_contra hcon
          rw [show thetaQDeg 3 (-3 * (-(b + 1))) u = 3 * Tn u - 3 * (-(b + 1)) * u by
            unfold thetaQDeg; ring] at hcon
          exact hu (by rw [if_neg (by omega)]))]
        rw [theta_fibre_zero_shifted (-(b + 1)) (E - 3 * Tn a - 3 * Tn b - 3 * (b - a)), mul_zero]
      rw [h1, h2, sub_zero]
    · -- finiteness of the first fibre.
      apply Set.Finite.subset (thetaQDeg_finite_fiber 3 (3 * a + 3) (by norm_num) (E - 3 * Tn a - 3 * Tn b))
      intro u hu; simp only [Function.mem_support] at hu; simp only [Set.mem_setOf_eq]
      by_contra hcon
      rw [show thetaQDeg 3 (3 * a + 3) u = 3 * Tplus u + 3 * a * u by
        unfold thetaQDeg; rw [Tplus_eq_Tn_add]; ring] at hcon
      exact hu (by rw [if_neg (by omega)])
    · -- finiteness of the second fibre.
      apply Set.Finite.subset (thetaQDeg_finite_fiber 3 (3 * b + 3) (by norm_num)
        (E - 3 * Tn a - 3 * Tn b - 3 * (b - a)))
      intro u hu; simp only [Function.mem_support] at hu; simp only [Set.mem_setOf_eq]
      by_contra hcon
      have halg : 3 * Tplus u + 3 * a * u + 3 * (b - a) * (u + 1)
          = thetaQDeg 3 (3 * b + 3) u + 3 * (b - a) := by
        unfold thetaQDeg; rw [Tplus_eq_Tn_add]; ring
      exact hu (by rw [if_neg (by omega)])
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h (by
      -- 1 - Q^{3(b-a)} ≠ 0.
      have := one_sub_Qpow_ne_zero (b - a) hd; exact this)
  · exact h

/-- **Diagonal evaluation for `Rho_sub`.**
`coeffXY (Θx·Θy·Rho_sub) a a = poch_q³ · Q^{6·T a − 3·T(a+1)} · (−1)^a`. -/
theorem sliceSub_diagonal (a : ℤ) :
    coeffXY (thetaX_q * thetaY_q * Rho_sub) a a
      = poch_q ^ 3 * HahnSeries.single (6 * Tn a - 3 * Tn (a + 1)) ((-1 : ℚ) ^ a) := by
  rw [coeffXY_eq_sliceSubUFamily_hsum]
  apply HahnSeries.ext
  funext E
  rw [HahnSeries.SummableFamily.coeff_hsum]
  -- per-u term coeff of sliceSubUterm a a u = (-1)^{u}(u+1)[6Ta+3Tplus u+3au = E].
  have hterm : ∀ u, ((sliceSubUFamily a a) u).coeff E
      = (if 6 * Tn a + 3 * Tplus u + 3 * a * u = E then (-1 : ℚ) ^ u * (((u : ℤ) : ℚ) + 1) else 0) := by
    intro u
    show (sliceSubUterm a a u).coeff E = _
    unfold sliceSubUterm
    rw [HahnSeries.coeff_smul, smul_eq_mul]
    rw [show (a : ℤ) - a = 0 by ring, StringSumQ_zero]
    rw [show Qpow (3 * Tn a + 3 * Tn a + 3 * Tplus u + 3 * a * u) * (((u : ℤ) : ℚ) + 1) • (1 : K)
        = (((u : ℤ) : ℚ) + 1) • Qpow (3 * Tn a + 3 * Tn a + 3 * Tplus u + 3 * a * u) by
      rw [mul_smul_comm, mul_one]]
    rw [HahnSeries.coeff_smul, smul_eq_mul]
    rw [show (Qpow (3 * Tn a + 3 * Tn a + 3 * Tplus u + 3 * a * u)).coeff E
        = (if 6 * Tn a + 3 * Tplus u + 3 * a * u = E then (1 : ℚ) else 0) by
      unfold Qpow; rw [HahnSeries.coeff_single]
      by_cases h : 6 * Tn a + 3 * Tplus u + 3 * a * u = E
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]]
    rw [show (a : ℤ) + a + u = 2 * a + u by ring, zpow_add₀ (by norm_num : (-1:ℚ) ≠ 0),
      show ((-1:ℚ)) ^ (2 * a) = 1 by rw [zpow_mul]; norm_num, one_mul]
    by_cases h : 6 * Tn a + 3 * Tplus u + 3 * a * u = E
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  rw [finsum_congr hterm]
  -- reindex u ↦ v = u + (a+1), so 3Tplus u + 3au = 3Tn v − 3Tn(a+1) and (u+1) = v − a.
  rw [← finsum_comp_equiv (Equiv.subRight (a + 1))]
  simp only [Equiv.subRight_apply]
  have hfeq : (fun v : ℤ => if 6 * Tn a + 3 * Tplus (v - (a + 1)) + 3 * a * (v - (a + 1)) = E
        then (-1 : ℚ) ^ (v - (a + 1)) * (((v - (a + 1) : ℤ) : ℚ) + 1) else 0)
      = fun v : ℤ => (-1 : ℚ) ^ a *
          ((a : ℚ) * (if 3 * Tn v = E - (6 * Tn a - 3 * Tn (a + 1)) then (-1 : ℚ) ^ v else 0)
           - (if 3 * Tn v = E - (6 * Tn a - 3 * Tn (a + 1))
                then (-1 : ℚ) ^ v * v else 0)) := by
    funext v
    -- exponent: 6Ta + 3Tplus(v-(a+1)) + 3a(v-(a+1)) = 3Tn v + (6Ta - 3Tn(a+1)).
    have hexp : 6 * Tn a + 3 * Tplus (v - (a + 1)) + 3 * a * (v - (a + 1))
        = 3 * Tn v + (6 * Tn a - 3 * Tn (a + 1)) := by
      have h1 := two_mul_Tplus (v - (a + 1)); have h2 := two_mul_Tn v
      have h3 := two_mul_Tn (a + 1)
      have key : 2 * (6 * Tn a + 3 * Tplus (v - (a + 1)) + 3 * a * (v - (a + 1)))
          = 2 * (3 * Tn v + (6 * Tn a - 3 * Tn (a + 1))) := by
        rw [show 2 * (6 * Tn a + 3 * Tplus (v - (a + 1)) + 3 * a * (v - (a + 1)))
            = 12 * Tn a + 3 * (2 * Tplus (v - (a + 1))) + 6 * a * (v - (a + 1)) by ring, h1,
          show 2 * (3 * Tn v + (6 * Tn a - 3 * Tn (a + 1)))
            = 3 * (2 * Tn v) + 12 * Tn a - 3 * (2 * Tn (a + 1)) by ring, h2, h3]
        ring
      omega
    by_cases h : 3 * Tn v = E - (6 * Tn a - 3 * Tn (a + 1))
    · rw [if_pos (by omega), if_pos h, if_pos h]
      -- sign (-1)^{v-(a+1)} = -(-1)^v·(-1)^a; weight (v-(a+1))+1 = v - a.
      have hsign : ((-1 : ℚ)) ^ (v - (a + 1)) = -((-1 : ℚ) ^ v * (-1) ^ a) := by
        rw [show v - (a + 1) = v + (-(a + 1)) by ring,
          zpow_add₀ (by norm_num : (-1:ℚ) ≠ 0), negOne_zpow_neg (a + 1),
          zpow_add₀ (by norm_num : (-1:ℚ) ≠ 0), zpow_one]
        ring
      rw [hsign]
      push_cast; ring
    · rw [if_neg (by omega), if_neg h, if_neg h]; ring
  rw [hfeq]
  rw [← mul_finsum' _ ((-1 : ℚ) ^ a) (by
    apply Set.Finite.subset (kTheta_fiber_finite (E - (6 * Tn a - 3 * Tn (a + 1))))
    intro v hv; simp only [Function.mem_support] at hv; simp only [Set.mem_setOf_eq]
    by_contra hcon
    rw [show thetaQDeg 3 0 v = 3 * Tn v by unfold thetaQDeg; ring] at hcon
    apply hv
    rw [if_neg (by omega), if_neg (by omega)]; ring)]
  rw [finsum_sub_distrib ?_ ?_]
  · have hpull : (∑ᶠ v : ℤ, (a : ℚ) * (if 3 * Tn v = E - (6 * Tn a - 3 * Tn (a + 1)) then (-1 : ℚ) ^ v else 0))
        = (a : ℚ) * ∑ᶠ v : ℤ, (if 3 * Tn v = E - (6 * Tn a - 3 * Tn (a + 1)) then (-1 : ℚ) ^ v else 0) := by
      have hfin1' : (Function.support (fun v : ℤ =>
            (if 3 * Tn v = E - (6 * Tn a - 3 * Tn (a + 1)) then (-1 : ℚ) ^ v else 0))).Finite := by
        apply Set.Finite.subset (kTheta_fiber_finite (E - (6 * Tn a - 3 * Tn (a + 1))))
        intro v hv; simp only [Function.mem_support] at hv; simp only [Set.mem_setOf_eq]
        by_contra hcon
        rw [show thetaQDeg 3 0 v = 3 * Tn v by unfold thetaQDeg; ring] at hcon
        exact hv (by rw [if_neg (by omega)])
      exact (mul_finsum' _ ((a : ℚ)) hfin1').symm
    rw [hpull]
    rw [theta_fibre_zero (E - (6 * Tn a - 3 * Tn (a + 1))),
      jacobi_fibre (E - (6 * Tn a - 3 * Tn (a + 1)))]
    -- RHS: (poch³ · single(6Ta-3T(a+1))((-1)^a)).coeff E = (poch³).coeff(E-(6Ta-3T(a+1)))·(-1)^a.
    rw [HahnSeries.coeff_mul_single]
    ring
  · apply Set.Finite.subset (kTheta_fiber_finite (E - (6 * Tn a - 3 * Tn (a + 1))))
    intro v hv; simp only [Function.mem_support] at hv; simp only [Set.mem_setOf_eq]
    by_contra hcon
    rw [show thetaQDeg 3 0 v = 3 * Tn v by unfold thetaQDeg; ring] at hcon
    exact hv (by rw [if_neg (by omega), mul_zero])
  · apply Set.Finite.subset (kTheta_fiber_finite (E - (6 * Tn a - 3 * Tn (a + 1))))
    intro v hv; simp only [Function.mem_support] at hv; simp only [Set.mem_setOf_eq]
    by_contra hcon
    rw [show thetaQDeg 3 0 v = 3 * Tn v by unfold thetaQDeg; ring] at hcon
    exact hv (by rw [if_neg (by omega)])

/-- The `x^i y^j` slice of `Θ(x⁻¹y⁻¹q²;q) = thetaMon 3 6 (-1) (-1)`: nonzero only on the diagonal
`i = j = -n`, where it is `single (3 T n + 6 n) ((-1)^n)` (with `n = -i`). -/
theorem coeffXY_thetaMon_36 (i j : ℤ) :
    coeffXY (thetaMon 3 6 (-1) (-1) (by norm_num)) i j
      = if i = j then HahnSeries.single (3 * Tn (-i) + 6 * (-i)) ((-1 : ℚ) ^ (-i)) else 0 := by
  apply HahnSeries.ext
  funext E
  rw [coeffXY_coeff, coeffQXY, thetaMon_coeff]
  have hfun : (fun n => (monom (thetaQDeg 3 6 n) ((-1) * n) ((-1) * n) ((-1) ^ n)).coeff (expQXY E i j))
      = fun n => if (thetaQDeg 3 6 n = E ∧ i = -n ∧ j = -n) then (-1 : ℚ) ^ n else 0 := by
    funext n
    unfold monom
    rw [HahnSeries.coeff_single]
    by_cases h : thetaQDeg 3 6 n = E ∧ i = -n ∧ j = -n
    · obtain ⟨hE, hi, hj⟩ := h
      rw [if_pos (show expQXY E i j = expQXY (thetaQDeg 3 6 n) ((-1) * n) ((-1) * n) by
        rw [hE, hi, hj]; congr 1 <;> ring), if_pos ⟨hE, hi, hj⟩]
    · rw [if_neg ?_, if_neg h]
      intro hcon
      obtain ⟨hE, hi, hj⟩ := expQXY_inj hcon
      exact h ⟨hE.symm, by omega, by omega⟩
  rw [hfun]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    rw [finsum_eq_single _ (-i) ?_]
    · rw [HahnSeries.coeff_single]
      by_cases hE : 3 * Tn (-i) + 6 * (-i) = E
      · rw [if_pos ⟨show thetaQDeg 3 6 (-i) = E by unfold thetaQDeg; omega,
          by ring, by ring⟩, if_pos hE.symm]
      · rw [if_neg (show ¬ (thetaQDeg 3 6 (-i) = E ∧ i = -(-i) ∧ i = -(-i)) by
          rintro ⟨hc, _, _⟩; apply hE; rw [← hc]; unfold thetaQDeg; ring),
          if_neg (fun hc => hE hc.symm)]
    · intro n hn
      rw [if_neg (by rintro ⟨_, hi, _⟩; exact hn (by omega))]
  · rw [if_neg hij]
    apply finsum_eq_zero_of_forall_eq_zero
    intro n
    rw [if_neg (by rintro ⟨_, hi, hj⟩; exact hij (by omega))]

/-- The RHS slice of the substituted Hickerson identity. -/
theorem coeffXY_rhs_sub (i j : ℤ) :
    coeffXY (embedQ (poch_q ^ 3) * thetaMon 3 6 (-1) (-1) (by norm_num)) i j
      = if i = j then poch_q ^ 3 * HahnSeries.single (3 * Tn (-i) + 6 * (-i)) ((-1 : ℚ) ^ (-i))
        else 0 := by
  rw [coeffXY_embedQ_mul, coeffXY_thetaMon_36]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos hij]
  · rw [if_neg hij, if_neg hij, mul_zero]

/-- **G1 — Substituted Hickerson identity.**
`Θ(x;q)·Θ(y;q)·Rho_sub = (q;q)_∞³·Θ(x⁻¹y⁻¹q²;q)`, i.e.
`thetaX_q * thetaY_q * Rho_sub = embedQ (poch_q^3) * thetaMon 3 6 (-1) (-1)`. -/
theorem hickerson_mul_sub :
    thetaX_q * thetaY_q * Rho_sub = embedQ (poch_q ^ 3) * thetaMon 3 6 (-1) (-1) (by norm_num) := by
  apply ext_coeffQXY
  intro a i j
  have hL : coeffQXY (thetaX_q * thetaY_q * Rho_sub) a i j
      = (coeffXY (thetaX_q * thetaY_q * Rho_sub) i j).coeff a := rfl
  have hR : coeffQXY (embedQ (poch_q ^ 3) * thetaMon 3 6 (-1) (-1) (by norm_num)) a i j
      = (coeffXY (embedQ (poch_q ^ 3) * thetaMon 3 6 (-1) (-1) (by norm_num)) i j).coeff a := rfl
  rw [hL, hR, coeffXY_rhs_sub]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, sliceSub_diagonal i]
    -- 6 T i − 3 T(i+1) = 3 T(-i) + 6(-i):  both equal (3i² − 9i)/2.
    rw [show 6 * Tn i - 3 * Tn (i + 1) = 3 * Tn (-i) + 6 * (-i) by
      have h1 := two_mul_Tn i; have h2 := two_mul_Tn (i + 1); have h3 := two_mul_Tn (-i)
      have he : (-i) * (-i - 1) = i * (i + 1) := by ring
      rw [he] at h3
      have hpoly : 6 * (i * (i - 1)) - 3 * ((i + 1) * (i + 1 - 1)) = 3 * (i * (i + 1)) + 12 * (-i) := by
        ring
      omega]
    rw [negOne_zpow_neg i]
  · rw [if_neg hij, sliceSub_off_diagonal i j hij, HahnSeries.coeff_zero]

/-- **The 10.33-pattern lemma** (FE with weight `w = x⁻¹y⁻¹q`):
`monom 3 (-1) (-1) 1 · Θ(x⁻¹y⁻¹q²;q) = - Θ(x⁻¹y⁻¹q;q)`, i.e.
`monom 3 (-1) (-1) 1 * thetaMon 3 6 (-1) (-1) = - thetaMon 3 3 (-1) (-1)`. -/
theorem monom_mul_thetaMon_36 :
    monom 3 (-1) (-1) 1 * thetaMon 3 6 (-1) (-1) (by norm_num)
      = - thetaMon 3 3 (-1) (-1) (by norm_num) := by
  have hfe := thetaMon_fe' 3 3 (-1) (-1) (by norm_num)
  -- hfe : thetaMon 3 3 (-1) (-1) = - monom 3 (-1) (-1) 1 * thetaMon 3 (3+3) (-1) (-1)
  rw [show (3 : ℤ) + 3 = 6 by norm_num] at hfe
  rw [hfe, neg_mul, neg_neg]

/-! ## Layer H — the triple-theta diagonal extraction for the final assembly

The final collapse needs the constant term
`CTxy (Θ(x⁻¹y⁻¹q;q) · Θ(x;q²) · Θ(y;q²))`, where
`Θ(x⁻¹y⁻¹q;q) = thetaMon 3 3 (-1) (-1)`, `Θ(x;q²) = thetaX_q2 = thetaMon 6 0 1 0`,
`Θ(y;q²) = thetaY_q2 = thetaMon 6 0 0 1`.  The `[x⁰y⁰]` projection forces the three
summation indices to coincide; the surviving Q-exponent is `15·T k + 3 k = 3·P₁₀(−k)`,
which after `k ↦ −k` becomes `3·P₁₀ n`.  -/

/-- `Θ(x⁻¹y⁻¹q;q) = thetaMon 3 3 (-1) (-1)`. -/
noncomputable def thetaXYinv_q : S := thetaMon 3 3 (-1) (-1) (by norm_num)

/-- The triple-product summable family `Θ(x⁻¹y⁻¹q;q) · Θ(x;q²) · Θ(y;q²)`, indexed by
`((k,l),m)` (the three theta indices). -/
noncomputable def tripFam : HahnSeries.SummableFamily ExpQXY ℚ ((ℤ × ℤ) × ℤ) :=
  HahnSeries.SummableFamily.mul
    (HahnSeries.SummableFamily.mul (thetaFamily 3 3 (-1) (-1) (by norm_num))
      (thetaFamily 6 0 1 0 (by norm_num))) (thetaFamily 6 0 0 1 (by norm_num))

/-- `tripFam.hsum = Θ(x⁻¹y⁻¹q;q) · Θ(x;q²) · Θ(y;q²)`. -/
theorem tripFam_hsum : tripFam.hsum = thetaXYinv_q * thetaX_q2 * thetaY_q2 := by
  unfold tripFam thetaXYinv_q thetaX_q2 thetaY_q2 thetaMon
  rw [HahnSeries.SummableFamily.hsum_mul, HahnSeries.SummableFamily.hsum_mul]

/-- The `(k,l,m)`-term of `tripFam` is a single monomial. -/
theorem tripFam_term (k l m : ℤ) :
    tripFam ((k, l), m)
      = monom (3 * Tn k + 3 * k + 6 * Tn l + 6 * Tn m) (-k + l) (-k + m)
          ((-1) ^ (k + l + m)) := by
  unfold tripFam
  show (monom (thetaQDeg 3 3 k) ((-1) * k) ((-1) * k) ((-1) ^ k)
        * monom (thetaQDeg 6 0 l) (1 * l) (0 * l) ((-1) ^ l))
        * monom (thetaQDeg 6 0 m) (0 * m) (1 * m) ((-1) ^ m) = _
  rw [monom_mul, monom_mul]
  apply monom_eq_monom
  · unfold thetaQDeg; ring
  · ring
  · ring
  · rw [zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0), zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]

/-- The `(k,l,m)`-term coefficient at `expQXY D 0 0` is the diagonal indicator `l = k ∧ m = k`. -/
theorem tripFam_term_coeff (k l m D : ℤ) :
    (tripFam ((k, l), m)).coeff (expQXY D 0 0)
      = if (3 * Tn k + 3 * k + 6 * Tn l + 6 * Tn m = D ∧ -k + l = 0 ∧ -k + m = 0)
        then (-1) ^ (k + l + m) else 0 := by
  rw [tripFam_term]
  unfold monom
  rw [HahnSeries.coeff_single]
  by_cases h : (3 * Tn k + 3 * k + 6 * Tn l + 6 * Tn m = D ∧ -k + l = 0 ∧ -k + m = 0)
  · obtain ⟨hD, hl, hm⟩ := h
    rw [if_pos (show expQXY D 0 0
          = expQXY (3 * Tn k + 3 * k + 6 * Tn l + 6 * Tn m) (-k + l) (-k + m) by
        rw [hD, hl, hm]), if_pos ⟨hD, hl, hm⟩]
  · rw [if_neg ?_, if_neg h]
    intro hcon
    apply h
    obtain ⟨hD, hl, hm⟩ := expQXY_inj hcon
    exact ⟨hD.symm, hl.symm, hm.symm⟩

/-- The `K`-summable family `n ↦ single (3·P₁₀ n) ((-1)^n)` for the RHS of the H-identity. -/
noncomputable def kP10Family : HahnSeries.SummableFamily ℤ ℚ ℤ where
  toFun := fun n => HahnSeries.single (3 * P10 n) ((-1) ^ n)
  isPWO_iUnion_support' := by
    -- 3·P₁₀ n = (15 n² + 9 n)/2 is bounded below (min at n near 0), so the support is PWO.
    refine ((bddBelow_Ici (a := (-1 : ℤ))).isWF.isPWO).mono (Set.iUnion_subset (fun n => ?_))
    intro x hx
    have hxe : x = 3 * P10 n := HahnSeries.support_single_subset hx
    rw [Set.mem_Ici, hxe]
    -- 2·(3 P₁₀ n) = 3 n(5n+3) ≥ -2 ⟹ 3 P₁₀ n ≥ -1.
    have h := two_mul_P10 n
    nlinarith [h, sq_nonneg (5 * n + 3), sq_nonneg n]
  finite_co_support' := by
    intro g
    -- the fibre {n : 3 P₁₀ n = g} is bounded: 2·(3 P₁₀ n) = 3 n(5n+3) = g·2, so |n| ≤ |g|+1.
    apply Set.Finite.subset (Set.finite_Icc (-(|g| + 1 : ℤ)) (|g| + 1))
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    have hne : (HahnSeries.single (3 * P10 n) ((-1 : ℚ) ^ n)).coeff g ≠ 0 := hn
    have hP : 3 * P10 n = g := by
      by_contra hc
      exact hne (by rw [HahnSeries.coeff_single_of_ne (fun h => hc h.symm)])
    have h := two_mul_P10 n
    have hg : |g| ≤ |g| := le_refl _
    have hgle : -|g| ≤ g ∧ g ≤ |g| := ⟨neg_abs_le g, le_abs_self g⟩
    rw [Set.mem_Icc]
    constructor <;> nlinarith [h, hP, hgle.1, hgle.2, sq_nonneg (5 * n + 3), sq_nonneg n,
      abs_nonneg g]

/-- The RHS of the H-identity as a single `K`-series. -/
noncomputable def kP10 : K := kP10Family.hsum

/-- Coefficient of `kP10` at `D`: the `n`-finsum of single-term coefficients. -/
theorem kP10_coeff (D : ℤ) :
    kP10.coeff D = ∑ᶠ n : ℤ, (HahnSeries.single (3 * P10 n) ((-1 : ℚ) ^ n)).coeff D := by
  unfold kP10 kP10Family
  rw [HahnSeries.SummableFamily.coeff_hsum]; rfl

/-- The diagonal-shift equivalence `(k,d) ↦ (k, k+d)` (its inverse is `(k,l) ↦ (k, l-k)`),
used to collapse a `(k,l)`-plane diagonal finsum to a single `k`-finsum. -/
def diagShiftEquiv : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun := fun q => (q.1, q.1 + q.2)
  invFun := fun p => (p.1, p.2 - p.1)
  left_inv := by rintro ⟨k, d⟩; simp only [add_sub_cancel_left]
  right_inv := by rintro ⟨k, l⟩; simp only [add_sub_cancel]

/-- **Triple-theta diagonal extraction (Layer H).**
`CTxy (Θ(x⁻¹y⁻¹q;q) · Θ(x;q²) · Θ(y;q²)) = ∑'_n single (3·P₁₀ n) ((-1)^n)`. -/
theorem CTxy_triple_theta :
    CTxy (thetaXYinv_q * thetaX_q2 * thetaY_q2) = kP10 := by
  apply HahnSeries.ext
  funext D
  rw [CTxy_coeff, coeffQXY, ← tripFam_hsum, HahnSeries.SummableFamily.coeff_hsum, kP10_coeff]
  -- LHS: ∑ᶠ ((k,l),m), indicator[l=k, m=k, qdeg=D] (-1)^{k+l+m}
  --     collapses (curry + single-out) to ∑ᶠ k, indicator[15Tk+3k=D] (-1)^k.
  have hLterm : (fun p : (ℤ × ℤ) × ℤ => (tripFam p).coeff (expQXY D 0 0))
      = fun p => if (3 * Tn p.1.1 + 3 * p.1.1 + 6 * Tn p.1.2 + 6 * Tn p.2 = D
          ∧ -p.1.1 + p.1.2 = 0 ∧ -p.1.1 + p.2 = 0)
        then (-1 : ℚ) ^ (p.1.1 + p.1.2 + p.2) else 0 := by
    funext p; obtain ⟨⟨k, l⟩, m⟩ := p; exact tripFam_term_coeff k l m D
  rw [hLterm]
  -- curry over ((k,l),m): ∑ᶠ (k,l), ∑ᶠ m.  Only m=k survives, then only l=k.
  rw [finsum_curry _ (by rw [← hLterm]; exact tripFam.finite_co_support' (expQXY D 0 0))]
  -- Step 1: the m-finsum singles out m = p.1 (via -p.1 + m = 0).
  have hstep1 : (fun p : ℤ × ℤ => ∑ᶠ m : ℤ,
        if (3 * Tn p.1 + 3 * p.1 + 6 * Tn p.2 + 6 * Tn m = D ∧ -p.1 + p.2 = 0 ∧ -p.1 + m = 0)
          then (-1 : ℚ) ^ (p.1 + p.2 + m) else 0)
      = fun p : ℤ × ℤ =>
        if (3 * Tn p.1 + 3 * p.1 + 6 * Tn p.2 + 6 * Tn p.1 = D ∧ p.2 = p.1)
          then (-1 : ℚ) ^ (p.1 + p.2 + p.1) else 0 := by
    funext p
    rw [finsum_eq_single _ p.1 ?_]
    · by_cases h : (3 * Tn p.1 + 3 * p.1 + 6 * Tn p.2 + 6 * Tn p.1 = D ∧ p.2 = p.1)
      · rw [if_pos ⟨h.1, by omega, by omega⟩, if_pos h]
      · rw [if_neg (fun hc => h ⟨hc.1, by omega⟩), if_neg h]
    · intro m hm
      rw [if_neg (by rintro ⟨_, _, hmk⟩; exact hm (by omega))]
  rw [hstep1]
  -- Step 2: collapse the (k,l)-plane diagonal (p.2 = p.1) to a single k-finsum via (k,d) ↦ (k,k+d).
  rw [← finsum_comp_equiv diagShiftEquiv]
  have hstep2 : (fun q : ℤ × ℤ =>
        (fun p : ℤ × ℤ => if (3 * Tn p.1 + 3 * p.1 + 6 * Tn p.2 + 6 * Tn p.1 = D ∧ p.2 = p.1)
          then (-1 : ℚ) ^ (p.1 + p.2 + p.1) else 0) (diagShiftEquiv q))
      = fun q : ℤ × ℤ => if q.2 = 0
          then (if 15 * Tn q.1 + 3 * q.1 = D then (-1 : ℚ) ^ q.1 else 0) else 0 := by
    funext q
    obtain ⟨k, d⟩ := q
    show (if (3 * Tn k + 3 * k + 6 * Tn (k + d) + 6 * Tn k = D ∧ k + d = k)
        then (-1 : ℚ) ^ (k + (k + d) + k) else 0) = _
    by_cases hd : d = 0
    · subst hd
      rw [if_pos rfl]
      by_cases h : 15 * Tn k + 3 * k = D
      · rw [if_pos ⟨by rw [show k + (0:ℤ) = k by ring]; rw [← h]; ring, by ring⟩, if_pos h,
          show k + (k + 0) + k = 2 * k + k by ring, zpow_add₀ (by norm_num : (-1:ℚ) ≠ 0),
          show ((-1:ℚ)) ^ (2 * k) = 1 by rw [zpow_mul]; norm_num, one_mul]
      · rw [if_neg (fun hc => h (by rw [← hc.1]; ring)), if_neg h]
    · rw [if_neg (by rintro ⟨_, h2⟩; exact hd (by omega)), if_neg hd]
  rw [hstep2]
  -- Step 3: curry (k,d); inner d-finsum singles out d = 0.
  have hkfin : {k : ℤ | (if 15 * Tn k + 3 * k = D then (-1 : ℚ) ^ k else 0) ≠ 0}.Finite := by
    apply Set.Finite.subset (Set.finite_Icc (-(D + 1)) ((D + 1)))
    intro k hk; simp only [Set.mem_setOf_eq] at hk; rw [Set.mem_Icc]
    by_cases hc : 15 * Tn k + 3 * k = D
    · have h2 := two_mul_Tn k
      obtain ⟨hlb, hub⟩ := abs_le_of_Tn_le (show Tn k ≤ D by nlinarith [Tn_nonneg k, hc, h2])
      constructor <;> omega
    · rw [if_neg hc] at hk; exact absurd rfl hk
  rw [finsum_curry _ (by
    apply Set.Finite.subset (Set.Finite.image (fun k : ℤ => (k, (0:ℤ))) hkfin)
    rintro ⟨k, d⟩ hkd
    rw [Function.mem_support] at hkd
    by_cases hd : d = 0
    · subst hd
      refine ⟨k, ?_, rfl⟩
      rw [Set.mem_setOf_eq]
      rw [if_pos rfl] at hkd; exact hkd
    · exact absurd (if_neg hd) hkd)]
  -- collapse each inner d-finsum to its d = 0 value, then reindex k ↦ -n.
  rw [show (∑ᶠ (k : ℤ) (d : ℤ),
        (if d = 0 then (if 15 * Tn k + 3 * k = D then (-1 : ℚ) ^ k else 0) else 0))
      = ∑ᶠ k : ℤ, (if 15 * Tn k + 3 * k = D then (-1 : ℚ) ^ k else 0) by
    apply finsum_congr; intro k
    rw [finsum_eq_single _ 0 (by intro d hd; rw [if_neg hd]), if_pos rfl]]
  -- match LHS k-finsum to RHS n-finsum via k ↦ -k.
  rw [← finsum_comp_equiv (Equiv.neg ℤ)]
  apply finsum_congr
  intro n
  simp only [Equiv.neg_apply]
  -- LHS at k = -n: indicator[15 T(-n)+3(-n)=D] (-1)^{-n}; RHS at n: single(3 P₁₀ n)((-1)^n) coeff D.
  rw [HahnSeries.coeff_single]
  have hdeg : 15 * Tn (-n) + 3 * (-n) = 3 * P10 n := by
    have h1 := two_mul_Tn (-n); have h2 := two_mul_P10 n
    have he : (-n) * (-n - 1) = n * (n + 1) := by ring
    rw [he] at h1
    -- 2·(15 Tn(-n)+3(-n)) = 15 n(n+1) - 6n = 3 n(5n+3) = 2·(3 P10 n).
    have hpoly : 15 * (n * (n + 1)) - 6 * n = 3 * (n * (5 * n + 3)) := by ring
    omega
  rw [hdeg, negOne_zpow_neg n]
  by_cases h : 3 * P10 n = D
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hc => h hc.symm)]

/-! ## Layer G3 + I — the final collapse and Chan's Eq 10.15

`ChanQuadLHS := CTxy (monom 1 0 0 1 · Rho_sub · zwegersLHS_x · zwegersLHS_y)` is Chan's Eq 10.15
LHS (constant term of `q·Rho(q/x,q/y)·Zwegers_x·Zwegers_y`).  Clearing the two `poch_q2`
denominators (one per Zwegers factor) substitutes the Zwegers RHS forms; substituting G1 and the
10.33-pattern then collapses the product to `- embedQ(poch_q^5)·Θ(x⁻¹y⁻¹q;q)·Θ(x;q²)·Θ(y;q²)`,
whose constant term is `- poch_q^5 · ∑'_n single(3 P₁₀ n)((-1)^n)` (Layer H). -/

/-- **Step-3 collapse** (the algebraic heart): substituting the Zwegers RHS forms,
`monom 1 0 0 1 · Rho_sub · zwegersRHS_x · zwegersRHS_y
= - embedQ(poch_q^5) · Θ(x⁻¹y⁻¹q;q) · Θ(x;q²) · Θ(y;q²)`. -/
theorem step3_collapse :
    monom 1 0 0 1 * Rho_sub * zwegersRHS_x * zwegersRHS_y
      = - embedQ (poch_q ^ 5) * thetaMon 3 3 (-1) (-1) (by norm_num) * thetaX_q2 * thetaY_q2 := by
  -- expand the two Zwegers RHS factors.
  rw [zwegersRHS_x, zwegersRHS_y]
  -- regroup: collect the three monomials into monom 3 (-1) (-1) 1, the two embedQ poch_q into poch²,
  -- and the four thetas; the two leading minus signs cancel.
  have hmon : monom 1 0 0 1 * (- monom 1 (-1) 0 1) * (- monom 1 0 (-1) 1)
      = monom 3 (-1) (-1) 1 := by
    rw [← monom_neg_one, ← monom_neg_one, monom_mul, monom_mul]
    apply monom_eq_monom <;> norm_num
  -- assemble: rearrange the big product (commutative ring S) into
  --   (monom 3 (-1)(-1) 1) · embedQ(poch²) · (thetaX_q2·thetaY_q2) · (Rho_sub·thetaX_q·thetaY_q).
  have hcomm : monom 1 0 0 1 * Rho_sub * (- monom 1 (-1) 0 1 * embedQ poch_q * thetaX_q2 * thetaX_q)
        * (- monom 1 0 (-1) 1 * embedQ poch_q * thetaY_q2 * thetaY_q)
      = (monom 1 0 0 1 * (- monom 1 (-1) 0 1) * (- monom 1 0 (-1) 1))
        * (embedQ poch_q * embedQ poch_q) * (thetaX_q2 * thetaY_q2)
        * (thetaX_q * thetaY_q * Rho_sub) := by ring
  rw [hcomm, hmon]
  -- substitute G1 : thetaX_q·thetaY_q·Rho_sub = embedQ(poch³)·Θ(x⁻¹y⁻¹q²;q).
  rw [hickerson_mul_sub]
  -- combine `embedQ poch_q · embedQ poch_q · embedQ (poch_q³)` into `embedQ (poch_q⁵)`, and
  -- group the monomial with Θ36 (10.33-pattern), via one commutative-ring rearrangement.
  have hpoch : embedQ poch_q * embedQ poch_q * embedQ (poch_q ^ 3) = embedQ (poch_q ^ 5) := by
    rw [← embedQ_mul, ← embedQ_mul]
    congr 1; ring
  have hrearr : monom 3 (-1) (-1) 1 * (embedQ poch_q * embedQ poch_q) * (thetaX_q2 * thetaY_q2)
        * (embedQ (poch_q ^ 3) * thetaMon 3 6 (-1) (-1) (by norm_num))
      = (embedQ poch_q * embedQ poch_q * embedQ (poch_q ^ 3))
        * (monom 3 (-1) (-1) 1 * thetaMon 3 6 (-1) (-1) (by norm_num))
        * (thetaX_q2 * thetaY_q2) := by ring
  rw [hrearr, hpoch, monom_mul_thetaMon_36]
  ring

/-- Chan's Eq 10.15 LHS as a `K`-series: the constant term of
`q · Rho(q/x,q/y) · Zwegers_x · Zwegers_y` (built from the *uncleared* Zwegers LHS sums). -/
noncomputable def ChanQuadLHS : K :=
  CTxy (monom 1 0 0 1 * Rho_sub * zwegersLHS_x * zwegersLHS_y)

/-- **Chan's Eq 10.15 (cleared form).**
`(q²;q²)_∞² · ChanQuadLHS = - (q;q)_∞⁵ · ∑'_n (-1)^n q^{(3/2)·P₁₀ n}`, where
`ChanQuadLHS = [x⁰y⁰] (q·Rho(q/x,q/y)·Zwegers_x·Zwegers_y)` is Chan's Eq 10.15 left side and the
right side `∑'_n single(3 P₁₀ n)((-1)^n)` is `∑_n (-1)^n q^{n(5n+3)/2}` in our `q = Q^3`
normalisation.  In Chan's book notation this is
`(q²;q²)_∞² · LHS = -(q;q)_∞⁵ · ∑_n (-1)^n q^{n(5n+3)/2}`.

Proof: multiply by `embedQ (poch_q2^2)` to clear the two `poch_q2` Zwegers denominators (one per
factor, via `zwegers_lemma_10_1_x/y`), apply `step3_collapse`, push the constant term through with
`CTxy_embedQ_mul`, and finish with the Layer-H triple-theta diagonal `CTxy_triple_theta`. -/
theorem chan_eq_10_15 :
    embedQ (poch_q2 ^ 2) * (monom 1 0 0 1 * Rho_sub * zwegersLHS_x * zwegersLHS_y)
      = - embedQ (poch_q ^ 5) * thetaMon 3 3 (-1) (-1) (by norm_num) * thetaX_q2 * thetaY_q2 := by
  -- distribute embedQ(poch_q2²) = embedQ poch_q2 · embedQ poch_q2 onto the two Zwegers LHS factors.
  rw [show poch_q2 ^ 2 = poch_q2 * poch_q2 by ring, embedQ_mul]
  rw [show embedQ poch_q2 * embedQ poch_q2 * (monom 1 0 0 1 * Rho_sub * zwegersLHS_x * zwegersLHS_y)
      = monom 1 0 0 1 * Rho_sub * (embedQ poch_q2 * zwegersLHS_x) * (embedQ poch_q2 * zwegersLHS_y)
      by ring]
  rw [zwegers_lemma_10_1_x, zwegers_lemma_10_1_y, step3_collapse]

/-- **Chan's Eq 10.15, constant-term (headline) form.**
`(q²;q²)_∞² · [x⁰y⁰](q·Rho(q/x,q/y)·Zwegers_x·Zwegers_y) = -(q;q)_∞⁵ · ∑_n (-1)^n q^{n(5n+3)/2}`. -/
theorem chan_eq_10_15_CTxy :
    poch_q2 ^ 2 * ChanQuadLHS = - poch_q ^ 5 * kP10 := by
  unfold ChanQuadLHS
  -- CTxy (embedQ(poch_q2²) · X) = poch_q2² · CTxy X.
  rw [← CTxy_embedQ_mul (poch_q2 ^ 2) (monom 1 0 0 1 * Rho_sub * zwegersLHS_x * zwegersLHS_y)]
  rw [chan_eq_10_15]
  -- CTxy (- embedQ(poch_q⁵) · Θ33 · ΘX2 · ΘY2) = - poch_q⁵ · CTxy(Θ33·ΘX2·ΘY2) = - poch_q⁵ · kP10.
  rw [show - embedQ (poch_q ^ 5) * thetaMon 3 3 (-1) (-1) (by norm_num) * thetaX_q2 * thetaY_q2
      = embedQ (- poch_q ^ 5) * (thetaXYinv_q * thetaX_q2 * thetaY_q2) by
    rw [map_neg]; unfold thetaXYinv_q; ring]
  rw [CTxy_embedQ_mul, CTxy_triple_theta]

/-! ## Layer I (Step 1) — the quadruple-sum decoupling of Chan's Eq 10.15 LHS

This layer transcribes ChatGPT's `chan1` Step-1 skeleton: the literal quadruple Hahn-sum form
of Chan's Eq 10.15 LHS, and the decoupling theorem identifying it with `ChanQuadLHS`.

`ChanQuadLHS = CTxy (monom 1 0 0 1 · Rho_sub · Zwegers_x · Zwegers_y)` (already defined above) is
the `[x⁰y⁰]`-coefficient of the genuine six-index product

  `q^{1/3} · Σ_{r,s} ρ(r,s) q^{rs+r+s} x^{-r} y^{-s}`
  `· Σ_{k,m} (-1)^{k+m}(δ₃k-δ₃m) q^{(k²+m²)/3} x^{m}`
  `· Σ_{l,n} (-1)^{l+n}(δ₃l-δ₃n) q^{(l²+n²)/3} y^{n}`   (in `q = Q³`).

The `[x⁰y⁰]` condition forces the antidiagonal `m = r`, `n = s`, collapsing the six-index sum to
the quadruple sum over `(k,l,r,s)` with integer `Q`-exponent

  `qExp4 = k² + l² + r² + 3rs + s² + 3r + 3s + 1`

and coefficient `ρ(r,s)·(-1)^{k+l+r+s}·(δ₃k-δ₃r)·(δ₃l-δ₃s)`.

`ChanQuadSum : K` is that quadruple sum, realised as the `hsum` of a genuine `K`-level summable
family.  The summability is the one genuinely careful point: the quadratic form `r²+3rs+s²` is
*indefinite* (discriminant `9-4 = 5 > 0`), so `qExp4` is **not** bounded below over all `(k,l,r,s)`.
However the coefficient vanishes off the `ρ`-support (`r,s ≥ 0` or `r,s ≤ -1`), and **on** that
support `qExp4 ≥ 0` with finite fibres — exactly the two-quadrant structure handled by
`rhoCoeffSub_isPWO`.  The bound is `g(r,s) := r²+3rs+s²+3r+3s+1 ≥ 0` on the support
(`= a²+3ab+b²+2a+2b ≥ 0` after `r=-1-a, s=-1-b` on the third quadrant; all terms nonneg on the
first), so `qExp4 = k²+l²+g(r,s) ≥ 0`. -/

/-- The integer `Q`-exponent of the `(k,l,r,s)` term of Chan's quadruple sum.
[OFFLINE-WRITTEN, numerics-verified to `Q^60`, build-pending] -/
def qExp4 (k l r s : ℤ) : ℤ := k ^ 2 + l ^ 2 + r ^ 2 + 3 * r * s + s ^ 2 + 3 * r + 3 * s + 1

/-- The coefficient of the `(k,l,r,s)` term of Chan's quadruple sum.
[OFFLINE-WRITTEN, numerics-verified to `Q^60`, build-pending] -/
noncomputable def quadCoeff (k l r s : ℤ) : ℚ :=
  rho r s * (-1) ^ (k + l + r + s) * (delta3 k - delta3 r) * (delta3 l - delta3 s)

/-- **Diagonal exponent identity** (`E6_diag` of the skeleton): the six-index exponent on the
antidiagonal `m=r, n=s` equals the quadruple exponent.  Pure `ring`.
[OFFLINE-WRITTEN, numerics-verified, build-pending; risk: trivial] -/
theorem qExp6_diag (k l r s : ℤ) :
    1 + 3 * (r * s + r + s) + (k ^ 2 + r ^ 2) + (l ^ 2 + s ^ 2) = qExp4 k l r s := by
  unfold qExp4; ring

/-- **Diagonal sign identity** (`sign_diag` of the skeleton): the two `(-1)`-powers from the
two Zwegers factors combine to the single quadruple sign.
[OFFLINE-WRITTEN, numerics-verified, build-pending; risk: low (`zpow_add₀`)] -/
theorem sign_diag (k l r s : ℤ) :
    ((-1 : ℚ) ^ (k + r)) * ((-1 : ℚ) ^ (l + s)) = (-1 : ℚ) ^ (k + l + r + s) := by
  rw [← zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]
  congr 1; ring

/-- **Diagonal coefficient identity** (`prodCoeff_diag` of the skeleton): the product of the
`ρ`-weight `ρ(r,s)` and the two Zwegers weights `zW k r`, `zW l s` (which is what the six-index
term contributes on the antidiagonal `m=r, n=s`) equals `quadCoeff k l r s`.
[OFFLINE-WRITTEN, numerics-verified, build-pending; risk: low] -/
theorem quadCoeff_diag (k l r s : ℤ) :
    rho r s * (zW k r * zW l s) = quadCoeff k l r s := by
  unfold quadCoeff zW
  rw [show (-1 : ℚ) ^ (k + r) * (delta3 k - delta3 r) * ((-1) ^ (l + s) * (delta3 l - delta3 s))
        = ((-1 : ℚ) ^ (k + r) * (-1) ^ (l + s)) * ((delta3 k - delta3 r) * (delta3 l - delta3 s))
      by ring]
  rw [sign_diag]
  ring

/-! ### `qExp4 ≥ 0` on the `quadCoeff` support, with finite fibres -/

/-- On the `ρ`-support, the "shifted" quadratic `g(r,s) = r²+3rs+s²+3r+3s+1` is `≥ 0`.
First quadrant (`r,s≥0`): all monomials nonnegative.  Third quadrant (`r,s≤-1`): substitute
`r=-1-a, s=-1-b` with `a,b≥0` to get `a²+3ab+b²+2a+2b ≥ 0`.
[OFFLINE-WRITTEN, numerics-verified, build-pending; risk: low (`nlinarith`)] -/
theorem g_nonneg_on_rho_support {r s : ℤ} (h : rho r s ≠ 0) :
    0 ≤ r ^ 2 + 3 * r * s + s ^ 2 + 3 * r + 3 * s + 1 := by
  unfold rho at h
  by_cases h1 : 0 ≤ r ∧ 0 ≤ s
  · obtain ⟨hr, hs⟩ := h1
    nlinarith [mul_nonneg hr hs, sq_nonneg r, sq_nonneg s, hr, hs]
  · rw [if_neg h1] at h
    by_cases h2 : r < 0 ∧ s < 0
    · obtain ⟨hr, hs⟩ := h2
      -- r ≤ -1, s ≤ -1.  Let a = -1-r ≥ 0, b = -1-s ≥ 0.  Then the form = a²+3ab+b²+2a+2b ≥ 0.
      have ha : 0 ≤ -1 - r := by omega
      have hb : 0 ≤ -1 - s := by omega
      nlinarith [mul_nonneg ha hb, sq_nonneg (-1 - r), sq_nonneg (-1 - s), ha, hb]
    · rw [if_neg h2] at h; exact absurd rfl h

/-- On the `quadCoeff` support, `qExp4 ≥ 0`.  (`quadCoeff ≠ 0 ⟹ ρ(r,s) ≠ 0`, then add `k²+l²`.)
[OFFLINE-WRITTEN, numerics-verified, build-pending; risk: low] -/
theorem qExp4_nonneg_of_quadCoeff {k l r s : ℤ} (h : quadCoeff k l r s ≠ 0) :
    0 ≤ qExp4 k l r s := by
  have hrho : rho r s ≠ 0 := by
    unfold quadCoeff at h
    intro hc; apply h; rw [hc]; ring
  have hg := g_nonneg_on_rho_support hrho
  unfold qExp4
  nlinarith [sq_nonneg k, sq_nonneg l, hg]

/-- Integer bound: `c² ≤ M` with `0 ≤ M` gives `-(M+1) ≤ c ≤ M+1` (single-variable nlinarith). -/
theorem abs_bound_of_sq_le {c M : ℤ} (h : c ^ 2 ≤ M) (hM : 0 ≤ M) :
    -(M + 1) ≤ c ∧ c ≤ M + 1 := by
  constructor
  · nlinarith [sq_nonneg (c + 1), h, hM]
  · nlinarith [sq_nonneg (c - 1), h, hM]

/-- For a fixed target `Q`-degree `D`, only finitely many `(k,l,r,s)` on the `quadCoeff` support
have `qExp4 = D`.  Each of `k², l²` is `≤ D` (the rest of `qExp4` is `≥ 0` on the support), and
`g(r,s) ≤ D` bounds `(r,s)` on the support.  We bound the whole tuple inside an `Icc` box.
[OFFLINE-WRITTEN, numerics-verified, build-pending; risk: MEDIUM (nlinarith box bounds)] -/
theorem qExp4_finite_fiber (D : ℤ) :
    {p : (ℤ × ℤ) × (ℤ × ℤ) | quadCoeff p.1.1 p.1.2 p.2.1 p.2.2 ≠ 0 ∧
        qExp4 p.1.1 p.1.2 p.2.1 p.2.2 = D}.Finite := by
  apply Set.Finite.subset (Set.finite_Icc
    (((-((D.natAbs : ℤ) + 2), -((D.natAbs : ℤ) + 2)), (-((D.natAbs : ℤ) + 2), -((D.natAbs : ℤ) + 2))) :
        (ℤ × ℤ) × (ℤ × ℤ))
    (((((D.natAbs : ℤ) + 2), ((D.natAbs : ℤ) + 2)), (((D.natAbs : ℤ) + 2), ((D.natAbs : ℤ) + 2))) :
        (ℤ × ℤ) × (ℤ × ℤ)))
  rintro ⟨⟨k, l⟩, ⟨r, s⟩⟩ ⟨hc, hD⟩
  have hrho : rho r s ≠ 0 := by
    unfold quadCoeff at hc; intro h; apply hc; rw [h]; ring
  have hg := g_nonneg_on_rho_support hrho
  -- `omega` knows `Int.natAbs`, giving both `D ≤ |D|` and `-|D| ≤ D`.
  have hNn : (D : ℤ) ≤ (D.natAbs : ℤ) := by omega
  have hNn2 : -(D.natAbs : ℤ) ≤ D := by omega
  -- From qExp4 = D and the nonneg pieces: k² ≤ D, l² ≤ D, and g(r,s) ≤ D.
  have hqe : k ^ 2 + l ^ 2 + (r ^ 2 + 3 * r * s + s ^ 2 + 3 * r + 3 * s + 1) = D := by
    have := hD; unfold qExp4 at this; linarith [this]
  have hk2 : k ^ 2 ≤ D := by nlinarith [sq_nonneg l, hg, hqe]
  have hl2 : l ^ 2 ≤ D := by nlinarith [sq_nonneg k, hg, hqe]
  have hgD : r ^ 2 + 3 * r * s + s ^ 2 + 3 * r + 3 * s + 1 ≤ D := by
    nlinarith [sq_nonneg k, sq_nonneg l, hqe]
  -- On the ρ-support, |r|, |s| are bounded by g(r,s) ≤ D ≤ |D|.
  -- First quadrant: r,s ≥ 0 and r² ≤ g, s² ≤ g (since 3rs+3r+3s+1 ≥ 0 there).
  -- Third quadrant: with a=-1-r, b=-1-s ≥ 0, a² ≤ g, b² ≤ g similarly; so |r| = a+1 ≤ g+1.
  -- On the support, r² ≤ D+1 and s² ≤ D+1.  (First quadrant: r² ≤ g ≤ D.  Third quadrant
  -- r,s ≤ -1: with a=-1-r, b=-1-s ≥ 0, g - r² = 3ab+b²+2b-1 ≥ -1, so r² ≤ g+1 ≤ D+1.)
  have hrs_bound : r ^ 2 ≤ D + 1 ∧ s ^ 2 ≤ D + 1 := by
    unfold rho at hrho
    by_cases h1 : 0 ≤ r ∧ 0 ≤ s
    · obtain ⟨hr, hs⟩ := h1
      constructor <;>
        nlinarith [mul_nonneg hr hs, hr, hs, hgD]
    · rw [if_neg h1] at hrho
      by_cases h2 : r < 0 ∧ s < 0
      · obtain ⟨hr, hs⟩ := h2
        refine ⟨?_, ?_⟩
        · nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ -1 - r) (by omega : (0:ℤ) ≤ -1 - s),
            sq_nonneg (-1 - s), hr, hs, hgD]
        · nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ -1 - r) (by omega : (0:ℤ) ≤ -1 - s),
            sq_nonneg (-1 - r), hr, hs, hgD]
      · rw [if_neg h2] at hrho; exact absurd rfl hrho
  -- Each tuple component c satisfies c² ≤ D+1 ≤ |D|+1, hence |c| ≤ |D|+1 (integer bound).
  obtain ⟨hrb, hsb⟩ := hrs_bound
  have hk2' : k ^ 2 ≤ D + 1 := by omega
  have hl2' : l ^ 2 ≤ D + 1 := by omega
  have hMnn : (0:ℤ) ≤ (D.natAbs : ℤ) + 1 := by positivity
  have hkM : k ^ 2 ≤ (D.natAbs : ℤ) + 1 := by omega
  have hlM : l ^ 2 ≤ (D.natAbs : ℤ) + 1 := by omega
  have hrM : r ^ 2 ≤ (D.natAbs : ℤ) + 1 := by omega
  have hsM : s ^ 2 ≤ (D.natAbs : ℤ) + 1 := by omega
  obtain ⟨hkL, hkU⟩ := abs_bound_of_sq_le hkM hMnn
  obtain ⟨hlL, hlU⟩ := abs_bound_of_sq_le hlM hMnn
  obtain ⟨hrL, hrU⟩ := abs_bound_of_sq_le hrM hMnn
  obtain ⟨hsL, hsU⟩ := abs_bound_of_sq_le hsM hMnn
  simp only [Set.mem_Icc, Prod.le_def]
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩ <;> dsimp only <;> omega

/-- The `K`-level summable family realising Chan's quadruple sum:
`((k,l),(r,s)) ↦ single (qExp4 k l r s) (quadCoeff k l r s)`.
[OFFLINE-WRITTEN, numerics-verified, build-pending; risk: MEDIUM (mirrors `kP10Family`/
`zFamily` but indexed by `(ℤ×ℤ)×(ℤ×ℤ)`; the PWO/finite-fibre proofs reduce to the helpers above)] -/
noncomputable def chanQuadKFamily : HahnSeries.SummableFamily ℤ ℚ ((ℤ × ℤ) × (ℤ × ℤ)) where
  toFun := fun p => HahnSeries.single (qExp4 p.1.1 p.1.2 p.2.1 p.2.2)
    (quadCoeff p.1.1 p.1.2 p.2.1 p.2.2)
  isPWO_iUnion_support' := by
    -- support ⊆ Ici 0, which is PWO; uses qExp4 ≥ 0 on the support of each term coefficient.
    refine ((bddBelow_Ici (a := (0 : ℤ))).isWF.isPWO).mono (Set.iUnion_subset (fun p => ?_))
    intro x hx
    obtain ⟨⟨k, l⟩, ⟨r, s⟩⟩ := p
    have hxe : x = qExp4 k l r s := HahnSeries.support_single_subset hx
    rw [HahnSeries.mem_support, hxe] at hx
    -- hx : single (qExp4 …) (quadCoeff …) has nonzero coeff at qExp4 …, i.e. quadCoeff … ≠ 0.
    rw [Set.mem_Ici, hxe]
    apply qExp4_nonneg_of_quadCoeff
    intro hc
    rw [hc, HahnSeries.single_eq_zero, HahnSeries.coeff_zero] at hx
    exact hx rfl
  finite_co_support' := by
    intro g
    apply Set.Finite.subset (qExp4_finite_fiber g)
    rintro ⟨⟨k, l⟩, ⟨r, s⟩⟩ hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    -- the single-term coeff at g is nonzero ⟹ quadCoeff ≠ 0 and qExp4 = g.
    rw [HahnSeries.coeff_single] at hp
    by_cases hq : g = qExp4 k l r s
    · refine ⟨?_, hq.symm⟩
      rw [if_pos hq] at hp; exact hp
    · rw [if_neg hq] at hp; exact absurd rfl hp

/-- **Chan's Eq 10.15 LHS as a genuine quadruple Hahn sum** (`ChanQuadSum` of the skeleton):
`Σ_{k,l,r,s} ρ(r,s)·(-1)^{k+l+r+s}·(δ₃k-δ₃r)·(δ₃l-δ₃s)·Q^{qExp4 k l r s}` in `K`.
[OFFLINE-WRITTEN, numerics-verified to `Q^60`, build-pending] -/
noncomputable def ChanQuadSum : K := chanQuadKFamily.hsum

/-- Coefficient of `ChanQuadSum` at `Q`-degree `D`: the quadruple finsum of single-term coeffs.
[OFFLINE-WRITTEN, numerics-verified, build-pending; risk: trivial] -/
theorem ChanQuadSum_coeff (D : ℤ) :
    ChanQuadSum.coeff D = ∑ᶠ p : (ℤ × ℤ) × (ℤ × ℤ),
      (HahnSeries.single (qExp4 p.1.1 p.1.2 p.2.1 p.2.2)
        (quadCoeff p.1.1 p.1.2 p.2.1 p.2.2)).coeff D := by
  unfold ChanQuadSum chanQuadKFamily
  rw [HahnSeries.SummableFamily.coeff_hsum]; rfl

/-! ### The six-index product family and its antidiagonal collapse

We build the inner product `Rho_sub · Zwegers_x · Zwegers_y` as a summable family over
`((ℤ×ℤ)×(ℤ×ℤ))×(ℤ×ℤ)` (indices `((r,s),(k,m)),(l,n)`), exactly mirroring `prodFamSub`. -/

/-- The six-index product family `(rhoFamilySub × zFamily) × zFamilyY` for the inner product
`Rho_sub · Zwegers_x · Zwegers_y`.
[OFFLINE-WRITTEN, build-pending; risk: low (literal `prodFamSub` pattern)] -/
noncomputable def chanProdFam :
    HahnSeries.SummableFamily ExpQXY ℚ (((ℤ × ℤ) × (ℤ × ℤ)) × (ℤ × ℤ)) :=
  HahnSeries.SummableFamily.mul
    (HahnSeries.SummableFamily.mul rhoFamilySub zFamily) zFamilyY

/-- `chanProdFam.hsum = Rho_sub · Zwegers_x · Zwegers_y`.
[OFFLINE-WRITTEN, build-pending; risk: low] -/
theorem chanProdFam_hsum : chanProdFam.hsum = Rho_sub * zwegersLHS_x * zwegersLHS_y := by
  unfold chanProdFam
  rw [HahnSeries.SummableFamily.hsum_mul, HahnSeries.SummableFamily.hsum_mul,
    rhoFamilySub_hsum]
  rfl

/-- The `(((r,s),(k,m)),(l,n))`-term of `chanProdFam` is a single monomial: `Q`-degree
`3(rs+r+s)+(k²+m²)+(l²+n²)`, `x`-degree `m-r`, `y`-degree `n-s`, coefficient `ρ(r,s)·zW k m·zW l n`.
[OFFLINE-WRITTEN, build-pending; risk: low (literal `prodFamSub_term` pattern)] -/
theorem chanProdFam_term (r s k m l n : ℤ) :
    chanProdFam (((r, s), (k, m)), (l, n))
      = monom (3 * (r * s + r + s) + (k ^ 2 + m ^ 2) + (l ^ 2 + n ^ 2)) (m - r) (n - s)
          (rho r s * (zW k m * zW l n)) := by
  unfold chanProdFam
  show (monom (3 * (r * s + r + s)) (-r) (-s) (rho r s)
        * monom (k ^ 2 + m ^ 2) m 0 (zW k m))
        * monom (l ^ 2 + n ^ 2) 0 n (zW l n) = _
  rw [monom_mul, monom_mul]
  apply monom_eq_monom <;> ring

/-- The `(((r,s),(k,m)),(l,n))`-term coefficient at `expQXY D a b` is the antidiagonal indicator
`[qExp6 = D ∧ m-r = a ∧ n-s = b]`.
[OFFLINE-WRITTEN, build-pending; risk: low (literal `prodFamSub_term_coeff` pattern)] -/
theorem chanProdFam_term_coeff (r s k m l n a b D : ℤ) :
    (chanProdFam (((r, s), (k, m)), (l, n))).coeff (expQXY D a b)
      = if (3 * (r * s + r + s) + (k ^ 2 + m ^ 2) + (l ^ 2 + n ^ 2) = D ∧ m - r = a ∧ n - s = b)
        then rho r s * (zW k m * zW l n) else 0 := by
  rw [chanProdFam_term]
  unfold monom
  rw [HahnSeries.coeff_single]
  by_cases h : (3 * (r * s + r + s) + (k ^ 2 + m ^ 2) + (l ^ 2 + n ^ 2) = D ∧ m - r = a ∧ n - s = b)
  · obtain ⟨hD, ha, hb⟩ := h
    rw [if_pos (show expQXY D a b
          = expQXY (3 * (r * s + r + s) + (k ^ 2 + m ^ 2) + (l ^ 2 + n ^ 2)) (m - r) (n - s) by
            rw [hD, ha, hb]),
        if_pos ⟨hD, ha, hb⟩]
  · rw [if_neg ?_, if_neg h]
    intro hcon
    apply h
    obtain ⟨hD, hx, hy⟩ := expQXY_inj hcon
    exact ⟨hD.symm, hx.symm, hy.symm⟩

/-! ### The constant-term (`[x⁰y⁰]`) coefficient of the six-index product

`CTxy` of the leading-monomial-times-inner-product, sliced at `Q`-degree `D`, equals the six-index
finsum with the antidiagonal indicator `m-r = 0 ∧ n-s = 0`.  We then collapse `(m,n)` against
`(r,s)` and reindex to the quadruple sum. -/

/-- The constant term of `monom 1 0 0 1 · (Rho_sub · Zx · Zy)` at `Q`-degree `D` is the six-index
finsum of `chanProdFam` term-coefficients at `expQXY (D-1) 0 0` (the `monom 1 0 0 1` shifts the
`Q`-degree down by `1` and pins `x,y` to `0`).
[OFFLINE-WRITTEN, build-pending; risk: MEDIUM (`coeffXY_monom_mul` + `coeff_hsum` chaining)] -/
theorem chanQuadLHS_coeff_eq_prodFinsum (D : ℤ) :
    (CTxy (monom 1 0 0 1 * (Rho_sub * zwegersLHS_x * zwegersLHS_y))).coeff D
      = ∑ᶠ p : ((ℤ × ℤ) × (ℤ × ℤ)) × (ℤ × ℤ),
          (chanProdFam p).coeff (expQXY (D - 1) 0 0) := by
  rw [CTxy_coeff, coeffQXY]
  -- (monom 1 0 0 1 * inner).coeff (expQXY D 0 0) = inner.coeff (expQXY (D-1) 0 0).
  rw [show (monom 1 0 0 1 * (Rho_sub * zwegersLHS_x * zwegersLHS_y)).coeff (expQXY D 0 0)
        = (Rho_sub * zwegersLHS_x * zwegersLHS_y).coeff (expQXY (D - 1) 0 0) by
    unfold monom
    rw [HahnSeries.coeff_single_mul_S, one_mul,
      show expQXY D 0 0 - expQXY 1 0 0 = expQXY (D - 1) 0 0 by
        rw [show expQXY D 0 0 - expQXY 1 0 0 = expQXY D 0 0 + (-(expQXY 1 0 0)) by ring,
          show -(expQXY 1 0 0) = expQXY (-1) 0 0 by
            rw [neg_eq_iff_add_eq_zero, expQXY_add]; norm_num,
          expQXY_add]
        congr 1 <;> ring]]
  rw [← chanProdFam_hsum, HahnSeries.SummableFamily.coeff_hsum]

/-- The index re-association equivalence `(((r,s),(k,m)),(l,n)) ↦ (((r,s),(k,l)),(m,n))`,
moving the antidiagonal pair `(m,n)` to the innermost factor.  Pure data Equiv (`rfl` on both
inverse laws).
[OFFLINE-WRITTEN, build-pending; risk: low (`rfl` field goals)] -/
def reassoc6 : (((ℤ × ℤ) × (ℤ × ℤ)) × (ℤ × ℤ)) ≃ (((ℤ × ℤ) × (ℤ × ℤ)) × (ℤ × ℤ))
    where
  toFun := fun p => (((p.1.1.1, p.1.1.2), (p.1.2.1, p.2.1)), (p.1.2.2, p.2.2))
  invFun := fun q => (((q.1.1.1, q.1.1.2), (q.1.2.1, q.2.1)), (q.1.2.2, q.2.2))
  left_inv := by rintro ⟨⟨⟨r, s⟩, ⟨k, m⟩⟩, ⟨l, n⟩⟩; rfl
  right_inv := by rintro ⟨⟨⟨r, s⟩, ⟨k, l⟩⟩, ⟨m, n⟩⟩; rfl

/-- The outer reindex `((k,l),(r,s)) ↦ ((r,s),(k,l))` matching the quadruple-sum index order to
the collapsed product index order.  Pure data Equiv.
[OFFLINE-WRITTEN, build-pending; risk: low (`rfl` field goals)] -/
def swapKLRS : ((ℤ × ℤ) × (ℤ × ℤ)) ≃ ((ℤ × ℤ) × (ℤ × ℤ))
    where
  toFun := fun p => (p.2, p.1)
  invFun := fun q => (q.2, q.1)
  left_inv := by rintro ⟨⟨k, l⟩, ⟨r, s⟩⟩; rfl
  right_inv := by rintro ⟨⟨r, s⟩, ⟨k, l⟩⟩; rfl

/-- **Step-1 decoupling** (`chan_step1_decoupling` of the skeleton): the `[x⁰y⁰]`-coefficient of
Chan's six-index product equals the quadruple Hahn sum.

The proof collapses the six-index finsum: re-associate so the antidiagonal pair `(m,n)` is the
innermost factor (`reassoc6`); curry; the inner `(m,n)`-finsum singles out `(m,n) = (r,s)` (the
`m-r=0 ∧ n-s=0` indicator); the surviving `((r,s),(k,l))`-sum is reindexed to `((k,l),(r,s))`
(`swapKLRS`) and matched termwise to the quadruple sum via the diagonal exponent identity
`qExp6_diag` and coefficient identity `quadCoeff_diag`.
[OFFLINE-WRITTEN, numerics-verified to `Q^60`, build-pending; risk: HIGH (the nested
`finsum_curry`/`finsum_eq_single` collapse — the single hardest tactic block; modelled on
`CTxy_triple_theta`)] -/
theorem chan_step1_decoupling : ChanQuadLHS = ChanQuadSum := by
  apply HahnSeries.ext
  funext D
  unfold ChanQuadLHS
  rw [show (monom 1 0 0 1 * Rho_sub * zwegersLHS_x * zwegersLHS_y : S)
        = monom 1 0 0 1 * (Rho_sub * zwegersLHS_x * zwegersLHS_y) by ring]
  rw [chanQuadLHS_coeff_eq_prodFinsum, ChanQuadSum_coeff]
  -- Rewrite each six-index term to the explicit antidiagonal indicator.
  have hterm : (fun p : ((ℤ × ℤ) × (ℤ × ℤ)) × (ℤ × ℤ) =>
        (chanProdFam p).coeff (expQXY (D - 1) 0 0))
      = fun p => if (3 * (p.1.1.1 * p.1.1.2 + p.1.1.1 + p.1.1.2)
              + (p.1.2.1 ^ 2 + p.1.2.2 ^ 2) + (p.2.1 ^ 2 + p.2.2 ^ 2) = D - 1
            ∧ p.1.2.2 - p.1.1.1 = 0 ∧ p.2.2 - p.1.1.2 = 0)
          then rho p.1.1.1 p.1.1.2 * (zW p.1.2.1 p.1.2.2 * zW p.2.1 p.2.2) else 0 := by
    funext p
    obtain ⟨⟨⟨r, s⟩, ⟨k, m⟩⟩, ⟨l, n⟩⟩ := p
    exact chanProdFam_term_coeff r s k m l n 0 0 (D - 1)
  rw [hterm]
  -- The RHS quadruple finsum: rewrite each single-term coeff to its indicator.
  have hqterm : (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
        (HahnSeries.single (qExp4 p.1.1 p.1.2 p.2.1 p.2.2)
          (quadCoeff p.1.1 p.1.2 p.2.1 p.2.2)).coeff D)
      = fun p => if qExp4 p.1.1 p.1.2 p.2.1 p.2.2 = D
          then quadCoeff p.1.1 p.1.2 p.2.1 p.2.2 else 0 := by
    funext p
    rw [HahnSeries.coeff_single]
    by_cases hq : qExp4 p.1.1 p.1.2 p.2.1 p.2.2 = D
    · rw [if_pos hq.symm, if_pos hq]
    · rw [if_neg (fun h => hq h.symm), if_neg hq]
  rw [hqterm]
  -- Abbreviation for the six-index indicator (as a function of the *re-associated* index).
  set F6 : (((ℤ × ℤ) × (ℤ × ℤ)) × (ℤ × ℤ)) → ℚ :=
    fun p => if (3 * (p.1.1.1 * p.1.1.2 + p.1.1.1 + p.1.1.2)
            + (p.1.2.1 ^ 2 + p.1.2.2 ^ 2) + (p.2.1 ^ 2 + p.2.2 ^ 2) = D - 1
          ∧ p.1.2.2 - p.1.1.1 = 0 ∧ p.2.2 - p.1.1.2 = 0)
        then rho p.1.1.1 p.1.1.2 * (zW p.1.2.1 p.1.2.2 * zW p.2.1 p.2.2) else 0 with hF6def
  -- Re-associate the six-index sum via `reassoc6`, moving `(m,n)` innermost.
  rw [← finsum_comp_equiv reassoc6]
  -- After reassoc, the index is `(((r,s),(k,l)),(m,n))`; write the composed indicator explicitly.
  have hcomp : (fun q : (((ℤ × ℤ) × (ℤ × ℤ)) × (ℤ × ℤ)) => F6 (reassoc6 q))
      = fun q => if (3 * (q.1.1.1 * q.1.1.2 + q.1.1.1 + q.1.1.2)
              + (q.1.2.1 ^ 2 + q.2.1 ^ 2) + (q.1.2.2 ^ 2 + q.2.2 ^ 2) = D - 1
            ∧ q.2.1 - q.1.1.1 = 0 ∧ q.2.2 - q.1.1.2 = 0)
          then rho q.1.1.1 q.1.1.2 * (zW q.1.2.1 q.2.1 * zW q.1.2.2 q.2.2) else 0 := by
    funext q
    obtain ⟨⟨⟨r, s⟩, ⟨k, l⟩⟩, ⟨m, n⟩⟩ := q
    rfl
  rw [hcomp]
  -- Curry `((r,s),(k,l))` (outer) from `(m,n)` (inner).  Finite support: image of the finite
  -- co-support of `chanProdFam` at `expQXY (D-1) 0 0` under the reassoc.
  have hfin : (Function.support (fun q : (((ℤ × ℤ) × (ℤ × ℤ)) × (ℤ × ℤ)) =>
        if (3 * (q.1.1.1 * q.1.1.2 + q.1.1.1 + q.1.1.2)
            + (q.1.2.1 ^ 2 + q.2.1 ^ 2) + (q.1.2.2 ^ 2 + q.2.2 ^ 2) = D - 1
          ∧ q.2.1 - q.1.1.1 = 0 ∧ q.2.2 - q.1.1.2 = 0)
        then rho q.1.1.1 q.1.1.2 * (zW q.1.2.1 q.2.1 * zW q.1.2.2 q.2.2) else 0)).Finite := by
    apply Set.Finite.subset
      (Set.Finite.image reassoc6.symm (chanProdFam.finite_co_support' (expQXY (D - 1) 0 0)))
    rintro ⟨⟨⟨r, s⟩, ⟨k, l⟩⟩, ⟨m, n⟩⟩ hq
    rw [Function.mem_support] at hq
    refine ⟨reassoc6 (((r, s), (k, l)), (m, n)), ?_, by simp⟩
    rw [Set.mem_setOf_eq]
    -- the chanProdFam term at the reassoc-image equals the indicator (nonzero).
    show (chanProdFam (((r, s), (k, m)), (l, n))).coeff (expQXY (D - 1) 0 0) ≠ 0
    rw [chanProdFam_term_coeff r s k m l n 0 0 (D - 1)]
    -- `hq` is the same indicator written with `(m,n)` innermost; the conditions are syntactically
    -- identical after destructuring, so it transfers directly.
    exact hq
  rw [finsum_curry _ hfin]
  -- Reindex the outer `((r,s),(k,l))` to `((k,l),(r,s))` (the quadruple-sum order).
  rw [← finsum_comp_equiv swapKLRS]
  apply finsum_congr
  rintro ⟨⟨k, l⟩, ⟨r, s⟩⟩
  -- inner `(m,n)`-finsum singles out `(m,n) = (r,s)`.
  show (∑ᶠ q : ℤ × ℤ, if (3 * (r * s + r + s) + (k ^ 2 + q.1 ^ 2) + (l ^ 2 + q.2 ^ 2) = D - 1
          ∧ q.1 - r = 0 ∧ q.2 - s = 0)
        then rho r s * (zW k q.1 * zW l q.2) else 0)
      = if qExp4 k l r s = D then quadCoeff k l r s else 0
  rw [finsum_eq_single _ (r, s) ?_]
  · -- at `(m,n) = (r,s)`: indicator condition reduces to `qExp4 = D`.
    show (if (3 * (r * s + r + s) + (k ^ 2 + r ^ 2) + (l ^ 2 + s ^ 2) = D - 1 ∧ r - r = 0 ∧ s - s = 0)
          then rho r s * (zW k r * zW l s) else 0)
        = if qExp4 k l r s = D then quadCoeff k l r s else 0
    rw [quadCoeff_diag k l r s]
    by_cases hD : qExp4 k l r s = D
    · rw [if_pos ⟨by rw [← qExp6_diag k l r s] at hD; linarith [hD], by ring, by ring⟩, if_pos hD]
    · rw [if_neg ?_, if_neg hD]
      rintro ⟨h1, _, _⟩
      apply hD
      rw [← qExp6_diag k l r s]; linarith [h1]
  · -- off-diagonal `(m,n) ≠ (r,s)`: the indicator's `m-r=0 ∧ n-s=0` fails.
    rintro ⟨m, n⟩ hmn
    rw [if_neg ?_]
    rintro ⟨_, hm, hn⟩
    apply hmn
    have : m = r ∧ n = s := ⟨by omega, by omega⟩
    rw [this.1, this.2]

end Ch10TwoVar
end QseriesFormalization
