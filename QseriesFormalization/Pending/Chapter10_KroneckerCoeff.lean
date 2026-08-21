import QseriesFormalization.Pending.Chapter10_PF

/-!
# Coefficientwise Kronecker partial fraction

This file formalizes the algebraic coefficient core of Appendix A.2--A.3 in
`paper/root-pair-involution/root_pair_note.tex`.  It uses exactly the signed
q-first branch inverse from `Chapter10_PF`.

The key point is the quasi-periodicity of the partial-fraction kernel.  Its
one-step proof is a coefficientwise telescope using
`denom_mul_branchInvCoeffAtPF`; the apparent boundary is `j(1;Q)` and cancels
under `k ↦ -k-1`.  Thus no residue theorem or analytic continuation enters the
formal coefficient argument.
-/

namespace QseriesFormalization.Pending.Ch10KroneckerCoeff

open QseriesFormalization.Pending.Chapter10PF
open scoped Classical

noncomputable section

/-! ## The shifted partial-fraction coefficient -/

/-- One coefficient contribution to `PF(a Q^B)` at `Q^E a^A`. -/
def shiftedPFTerm (B E A k : ℤ) : ℤ :=
  negOnePowIntPF ℤ k *
    branchInvCoeffAtPF (k + B) (E - triIntPF k) A

/-- Coefficient of `Q^E a^A` in the branch expansion of `PF(a Q^B)`. -/
def shiftedPFCoeff (B E A : ℤ) : ℤ :=
  ∑ᶠ k : ℤ, shiftedPFTerm B E A k

/-- The unshifted partial-fraction coefficient. -/
abbrev pfCoeff (E A : ℤ) : ℤ := shiftedPFCoeff 0 E A

private theorem branchInvCoeffAtPF_ne_zero_imp_eq
    {k a b : ℤ} (h : branchInvCoeffAtPF k a b ≠ 0) :
    a = k * b := by
  unfold branchInvCoeffAtPF at h
  by_cases hk : 0 ≤ k
  · simp only [hk, if_true] at h
    by_cases hb : 0 ≤ b ∧ a = k * b
    · exact hb.2
    · simp [hb] at h
  · simp only [hk, if_false] at h
    by_cases hb : b < 0 ∧ a = k * b
    · exact hb.2
    · simp [hb] at h

private theorem support_finite_of_pf_equation
    (B E A : ℤ) (f : ℤ → ℤ)
    (hf : ∀ k, f k ≠ 0 → E - triIntPF k = (k + B) * A) :
    (Function.support f).Finite := by
  classical
  by_cases hex : ∃ k₀ : ℤ, f k₀ ≠ 0
  · obtain ⟨k₀, hk₀⟩ := hex
    refine (Finset.finite_toSet ({k₀, -k₀ - 2 * A - 1} : Finset ℤ)).subset ?_
    intro k hk
    simp only [Function.mem_support] at hk
    rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    have hEq := hf k hk
    have hEq₀ := hf k₀ hk₀
    have htri := two_mul_triIntPF k
    have htri₀ := two_mul_triIntPF k₀
    have hprod : (k - k₀) * (k + k₀ + 2 * A + 1) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hprod with hleft | hright
    · left
      omega
    · right
      omega
  · have hempty : Function.support f = ∅ := by
      ext k
      simp only [Function.mem_support, Set.mem_empty_iff_false, iff_false]
      exact fun hk => hex ⟨k, hk⟩
    rw [hempty]
    exact Set.finite_empty

private theorem shiftedPFTerm_support_finite (B E A : ℤ) :
    (Function.support (shiftedPFTerm B E A)).Finite := by
  apply support_finite_of_pf_equation B E A
  intro k hk
  have hbranch := right_ne_zero_of_mul hk
  exact branchInvCoeffAtPF_ne_zero_imp_eq hbranch

private theorem shiftedPFTerm_succ_comp_support_finite (B E A : ℤ) :
    (Function.support (fun k => shiftedPFTerm B (E - B) (A - 1) (k + 1))).Finite := by
  apply support_finite_of_pf_equation (B + 1) E A
  intro k hk
  have hbranch := right_ne_zero_of_mul hk
  have hEq := branchInvCoeffAtPF_ne_zero_imp_eq hbranch
  unfold shiftedPFTerm at hEq
  have htri : triIntPF (k + 1) = triIntPF k + k + 1 := by
    have h1 := two_mul_triIntPF (k + 1)
    have h2 := two_mul_triIntPF k
    nlinarith
  rw [htri] at hEq
  nlinarith

/-- The parity sign changes under a unit shift. -/
theorem negOnePowIntPF_succ (k : ℤ) :
    negOnePowIntPF ℤ (k + 1) = -negOnePowIntPF ℤ k := by
  rw [negOnePowIntPF_add]
  norm_num [negOnePowIntPF]

/-! ## The vanishing boundary `j(1;Q)` -/

/-- The coefficient of `Q^E` in the bilateral theta series `j(1;Q)`. -/
def thetaAtOneCoeff (E : ℤ) : ℤ :=
  ∑ᶠ k : ℤ, negOnePowIntPF ℤ k * if E = triIntPF k then 1 else 0

private def triangularReflect : ℤ ≃ ℤ where
  toFun k := -k - 1
  invFun k := -k - 1
  left_inv := by intro k; ring
  right_inv := by intro k; ring

/-- Every coefficient of `j(1;Q)` cancels with its reflected partner. -/
theorem thetaAtOneCoeff_eq_zero (E : ℤ) : thetaAtOneCoeff E = 0 := by
  let f : ℤ → ℤ := fun k =>
    negOnePowIntPF ℤ k * if E = triIntPF k then 1 else 0
  have hreflect : ∀ k : ℤ, f (triangularReflect k) = -f k := by
    intro k
    dsimp [f, triangularReflect]
    rw [triIntPF_reflect, negOnePowIntPF_reflect]
    ring
  have hreindex : (∑ᶠ k : ℤ, f k) = ∑ᶠ k : ℤ, f (triangularReflect k) :=
    (finsum_comp_equiv triangularReflect).symm
  have hneg : (∑ᶠ k : ℤ, f (triangularReflect k)) = -∑ᶠ k : ℤ, f k := by
    rw [finsum_congr hreflect, finsum_neg_distrib]
  unfold thetaAtOneCoeff
  change (∑ᶠ k : ℤ, f k) = 0
  have hself : (∑ᶠ k : ℤ, f k) = -∑ᶠ k : ℤ, f k := hreindex.trans hneg
  omega

/-! ## Quasi-periodicity of the PF kernel -/

/--
One-step quasi-periodicity:
`PF(a Q^(B+1)) = -a Q^B PF(a Q^B)`, coefficient by coefficient.
-/
theorem shiftedPFCoeff_succ (B E A : ℤ) :
    shiftedPFCoeff (B + 1) E A = -shiftedPFCoeff B (E - B) (A - 1) := by
  let G : ℤ → ℤ := fun k => shiftedPFTerm B (E - B) (A - 1) k
  have hreindex : (∑ᶠ k : ℤ, G k) = ∑ᶠ k : ℤ, G (k + 1) :=
    (finsum_comp_equiv (Equiv.addRight (1 : ℤ))).symm
  unfold shiftedPFCoeff
  change (∑ᶠ k : ℤ, shiftedPFTerm (B + 1) E A k) = -∑ᶠ k : ℤ, G k
  rw [hreindex]
  have hsum :
      (∑ᶠ k : ℤ, shiftedPFTerm (B + 1) E A k) +
          (∑ᶠ k : ℤ, G (k + 1)) = 0 := by
    rw [← finsum_add_distrib
      (shiftedPFTerm_support_finite (B + 1) E A)
      (shiftedPFTerm_succ_comp_support_finite B E A)]
    have hpoint : ∀ k : ℤ,
        shiftedPFTerm (B + 1) E A k + G (k + 1) =
          negOnePowIntPF ℤ k * if E = triIntPF k ∧ A = 0 then 1 else 0 := by
      intro k
      simp only [G, shiftedPFTerm]
      have htri : triIntPF (k + 1) = triIntPF k + k + 1 := by
        have h1 := two_mul_triIntPF (k + 1)
        have h2 := two_mul_triIntPF k
        nlinarith
      rw [negOnePowIntPF_succ]
      have hq :
          E - B - triIntPF (k + 1) =
            E - triIntPF k - (k + B + 1) := by
        rw [htri]
        ring
      rw [hq]
      rw [show k + (B + 1) = k + B + 1 by ring,
        show k + 1 + B = k + B + 1 by ring]
      rw [show
        negOnePowIntPF ℤ k *
              branchInvCoeffAtPF (k + B + 1) (E - triIntPF k) A +
            -negOnePowIntPF ℤ k *
              branchInvCoeffAtPF (k + B + 1)
                (E - triIntPF k - (k + B + 1)) (A - 1) =
          negOnePowIntPF ℤ k *
            (branchInvCoeffAtPF (k + B + 1) (E - triIntPF k) A -
              branchInvCoeffAtPF (k + B + 1)
                (E - triIntPF k - (k + B + 1)) (A - 1)) by ring]
      rw [denom_mul_branchInvCoeffAtPF]
      by_cases hE : E = triIntPF k
      · simp [hE]
      · have hne : E - triIntPF k ≠ 0 := by omega
        simp [hE, hne]
    calc
      (∑ᶠ k : ℤ, (shiftedPFTerm (B + 1) E A k + G (k + 1))) =
          (∑ᶠ k : ℤ,
            negOnePowIntPF ℤ k * if E = triIntPF k ∧ A = 0 then 1 else 0) :=
            finsum_congr hpoint
      _ = if A = 0 then thetaAtOneCoeff E else 0 := by
        by_cases hA : A = 0
        · simp [hA, thetaAtOneCoeff]
        · simp [hA]
      _ = 0 := by
        by_cases hA : A = 0
        · simp [hA, thetaAtOneCoeff_eq_zero E]
        · simp [hA]
  omega

/-- Closed quasi-periodicity for every integer shift `B`. -/
theorem shiftedPFCoeff_eq_unshifted (B : ℤ) : ∀ E A : ℤ,
    shiftedPFCoeff B E A =
      negOnePowIntPF ℤ B * pfCoeff (E - triIntPF (B - 1)) (A - B) := by
  refine Int.induction_on B ?_ ?_ ?_
  · intro E A
    simp [pfCoeff, triIntPF, negOnePowIntPF]
  · intro k ih E A
    rw [shiftedPFCoeff_succ, ih (E - (k : ℤ)) (A - 1)]
    rw [negOnePowIntPF_succ]
    have htri :
        triIntPF (((k : ℤ) + 1) - 1) =
          triIntPF ((k : ℤ) - 1) + k := by
      have h1 := two_mul_triIntPF (((k : ℤ) + 1) - 1)
      have h2 := two_mul_triIntPF ((k : ℤ) - 1)
      nlinarith
    rw [htri]
    ring_nf
  · intro k ih E A
    let b : ℤ := -(k : ℤ) - 1
    have hb_succ : b + 1 = -(k : ℤ) := by dsimp [b]; ring
    have hstep := shiftedPFCoeff_succ b (E + b) (A + 1)
    have hstep' :
        shiftedPFCoeff (-(k : ℤ)) (E + b) (A + 1) =
          -shiftedPFCoeff b E A := by
      simpa [hb_succ] using hstep
    have hsolve :
        shiftedPFCoeff b E A =
          -shiftedPFCoeff (-(k : ℤ)) (E + b) (A + 1) := by
      simpa using (congrArg Neg.neg hstep').symm
    rw [ih (E + b) (A + 1)] at hsolve
    have htri : triIntPF b = triIntPF (b - 1) + b := by
      have h1 := two_mul_triIntPF b
      have h2 := two_mul_triIntPF (b - 1)
      nlinarith
    have hsign :
        negOnePowIntPF ℤ b = -negOnePowIntPF ℤ (-(k : ℤ)) := by
      have h := negOnePowIntPF_succ b
      rw [hb_succ] at h
      omega
    change shiftedPFCoeff b E A =
      -(negOnePowIntPF ℤ (-(k : ℤ)) *
        pfCoeff (E + b - triIntPF b) (A + 1 - (-(k : ℤ)))) at hsolve
    rw [htri] at hsolve
    have hEarg : E + b - (triIntPF (b - 1) + b) = E - triIntPF (b - 1) := by
      ring
    have hAarg : A + 1 - (-(k : ℤ)) = A - b := by
      dsimp [b]
      ring
    rw [hEarg, hAarg] at hsolve
    change shiftedPFCoeff b E A =
      negOnePowIntPF ℤ b * pfCoeff (E - triIntPF (b - 1)) (A - b)
    rw [hsign]
    simpa only [neg_mul] using hsolve

/-! ## Kronecker coefficient and the cleared comparison -/

/-- Coefficient of `Q^E a^A b^B` in `∑_eta b^eta/(1-aQ^eta)`. -/
def kroneckerCoeff (E A B : ℤ) : ℤ := branchInvCoeffAtPF B E A

/-- Coefficient after multiplying the Kronecker sum by `j(b;Q)`. -/
def jMulKroneckerCoeff (E A B : ℤ) : ℤ :=
  ∑ᶠ s : ℤ, negOnePowIntPF ℤ s *
    kroneckerCoeff (E - triIntPF (s - 1)) A (B - s)

private def intNegEquiv : ℤ ≃ ℤ where
  toFun s := -s
  invFun s := -s
  left_inv := by intro s; ring
  right_inv := by intro s; ring

/-- Multiplication by `j(b)` turns the Kronecker sum into `PF(aQ^B)`. -/
theorem jMulKroneckerCoeff_eq_shiftedPFCoeff (E A B : ℤ) :
    jMulKroneckerCoeff E A B = shiftedPFCoeff B E A := by
  unfold jMulKroneckerCoeff shiftedPFCoeff
  rw [show
    (∑ᶠ s : ℤ, negOnePowIntPF ℤ s *
      kroneckerCoeff (E - triIntPF (s - 1)) A (B - s)) =
      ∑ᶠ s : ℤ, negOnePowIntPF ℤ (-s) *
        kroneckerCoeff (E - triIntPF (-s - 1)) A (B - (-s)) from
    (finsum_comp_equiv intNegEquiv).symm]
  apply finsum_congr
  intro s
  unfold shiftedPFTerm kroneckerCoeff
  rw [triIntPF_reflect]
  have hsign : negOnePowIntPF ℤ (-s) = negOnePowIntPF ℤ s := by
    rw [negOnePowIntPF_eq_negOnePow, negOnePowIntPF_eq_negOnePow,
      Int.negOnePow_neg]
  rw [hsign]
  congr 2
  all_goals ring

/--
Cleared coefficientwise Kronecker identity:
`j(b;Q) * ∑_eta b^eta/(1-aQ^eta) = j(ab;Q) * PF(a)`.

The right side has coefficient
`(-1)^B Q^{C2(B)} a^B * PF(a)`, written at the target exponents.
-/
theorem kronecker_partial_fraction_cleared_coefficient
    (E A B : ℤ) :
    jMulKroneckerCoeff E A B =
      negOnePowIntPF ℤ B * pfCoeff (E - triIntPF (B - 1)) (A - B) := by
  rw [jMulKroneckerCoeff_eq_shiftedPFCoeff]
  exact shiftedPFCoeff_eq_unshifted B E A

/--
The second clearing factor is the already verified PF identity
`j(a;Q) * PF(a) = J_Q^3`.  Together with
`kronecker_partial_fraction_cleared_coefficient`, this is the fully algebraic
coefficient proof of Appendix A.2.
-/
theorem kronecker_partial_fraction_coefficientwise :
    (∀ E A B : ℤ,
      jMulKroneckerCoeff E A B =
        negOnePowIntPF ℤ B * pfCoeff (E - triIntPF (B - 1)) (A - B)) ∧
    thetaMulPFSeriesCoeffPF = qPochInfPSCubeUPowerCoeffPF := by
  constructor
  · exact kronecker_partial_fraction_cleared_coefficient
  · exact thetaMul_PF_eq_qPochInfPS_pow_three

end

end QseriesFormalization.Pending.Ch10KroneckerCoeff
