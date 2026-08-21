import QseriesFormalization.Pending.Chapter10_GeneralHahnCoeff

/-!
# Coefficient comparison with the Hickerson--Mortenson theta correction

This file formalizes Appendix A.6--A.17 of
`paper/root-pair-involution/root_pair_note.tex`.  The two finite residue
variables and the three bilateral indices in the printed HM correction are
reconstructed uniquely from a target monomial and one shell index `w`.  The
resulting branch sign and q-exponent are then identified with the wall kernel
used in `Chapter10_GeneralHahnCoeff`.

Half-integral wall coordinates are represented after multiplication by two;
this keeps every declaration integer-valued for both parities of `n`.
-/

namespace QseriesFormalization.Pending.Ch10HMComparison

open QseriesFormalization.Pending.Ch10RootPairGeneral
open QseriesFormalization.Pending.Ch10GeneralHahnCoeff
open scoped Classical

noncomputable section

/-! ## Residue representatives and the monomial constraints -/

/-- The first integer representative `rho` occurring in the HM residue interval. -/
def rhoStart (n : ℤ) : ℤ := -((n - 1) / 2)

/-- The first integer representative `sigma` occurring in the HM residue interval. -/
def sigmaStart (n : ℤ) : ℤ := n / 2 + 1

/-- The HM integer representative `rho` attached to `rStar`. -/
def hmRho (n rStar : ℤ) : ℤ := rhoStart n + rStar

/-- The HM integer representative `sigma` attached to `sStar`. -/
def hmSigma (n sStar : ℤ) : ℤ := sigmaStart n + sStar

/-- The unique first residue selected by the target exponent `R` and shell `w`. -/
def hmRStar (n p R w : ℤ) : ℤ := (R + n * w - rhoStart n) % p

/-- The corresponding Kronecker index `eta`. -/
def hmEta (n p R w : ℤ) : ℤ := (R + n * w - rhoStart n) / p

/-- The unique second residue selected by the target exponent `S` and shell `w`. -/
def hmSStar (n p S w : ℤ) : ℤ := (S - n * w - sigmaStart n) % p

/-- The corresponding Hahn inverse index `ell`. -/
def hmEll (n p S w : ℤ) : ℤ := (S - n * w - sigmaStart n) / p

/-- The remaining Jacobi index forced by `w = ell - iota - eta`. -/
def hmIota (n p R S w : ℤ) : ℤ :=
  hmEll n p S w - hmEta n p R w - w

private theorem emod_add_mul_ediv' (a p : ℤ) :
    a % p + p * (a / p) = a := by
  simpa [mul_comm] using Int.emod_add_mul_ediv a p

/-- The reconstructed first residue lies in `{0,...,p-1}`. -/
theorem hmRStar_mem (n p R w : ℤ) (hp : 0 < p) :
    hmRStar n p R w ∈ Finset.Icc (0 : ℤ) (p - 1) := by
  rw [Finset.mem_Icc]
  constructor
  · simpa [hmRStar] using
      (Int.emod_nonneg (R + n * w - rhoStart n) (ne_of_gt hp))
  · have h := Int.emod_lt_of_pos (R + n * w - rhoStart n) hp
    simpa [hmRStar] using h

/-- The reconstructed second residue lies in `{0,...,p-1}`. -/
theorem hmSStar_mem (n p S w : ℤ) (hp : 0 < p) :
    hmSStar n p S w ∈ Finset.Icc (0 : ℤ) (p - 1) := by
  rw [Finset.mem_Icc]
  constructor
  · simpa [hmSStar] using
      (Int.emod_nonneg (S - n * w - sigmaStart n) (ne_of_gt hp))
  · have h := Int.emod_lt_of_pos (S - n * w - sigmaStart n) hp
    simpa [hmSStar] using h

/-- Equation A.8 before adding the half-integral wall offset. -/
theorem hm_first_residue_equation (n p R w : ℤ) :
    R + n * w = hmRho n (hmRStar n p R w) + p * hmEta n p R w := by
  have h := emod_add_mul_ediv' (R + n * w - rhoStart n) p
  unfold hmRho hmRStar hmEta
  omega

/-- Equation A.9 before subtracting the half-integral wall offset. -/
theorem hm_second_residue_equation (n p S w : ℤ) :
    S - n * w = hmSigma n (hmSStar n p S w) + p * hmEll n p S w := by
  have h := emod_add_mul_ediv' (S - n * w - sigmaStart n) p
  unfold hmSigma hmSStar hmEll
  omega

/-- First monomial exponent in Equation A.6. -/
def hmMonomialR (n p rho iota eta ell : ℤ) : ℤ :=
  rho + n * iota + (n + p) * eta - n * ell

/-- Second monomial exponent in Equation A.6. -/
def hmMonomialS (n p sigma iota eta ell : ℤ) : ℤ :=
  sigma - n * iota - n * eta + (n + p) * ell

/-- The shell coordinate in Equation A.7. -/
def hmW (iota eta ell : ℤ) : ℤ := ell - iota - eta

/-- The canonical indices reconstruct the first monomial equation A.6. -/
theorem hmMonomialR_reconstruct (n p R S w : ℤ) :
    hmMonomialR n p (hmRho n (hmRStar n p R w))
      (hmIota n p R S w) (hmEta n p R w) (hmEll n p S w) = R := by
  have h := hm_first_residue_equation n p R w
  unfold hmMonomialR hmIota
  ring_nf at h ⊢
  omega

/-- The canonical indices reconstruct the second monomial equation A.6. -/
theorem hmMonomialS_reconstruct (n p R S w : ℤ) :
    hmMonomialS n p (hmSigma n (hmSStar n p S w))
      (hmIota n p R S w) (hmEta n p R w) (hmEll n p S w) = S := by
  have h := hm_second_residue_equation n p S w
  unfold hmMonomialS hmIota
  ring_nf at h ⊢
  omega

/-- The canonical indices reconstruct Equation A.7. -/
theorem hmW_reconstruct (n p R S w : ℤ) :
    hmW (hmIota n p R S w) (hmEta n p R w) (hmEll n p S w) = w := by
  unfold hmW hmIota
  ring

/-- Uniqueness of the first residue/index pair in Equation A.8. -/
theorem hm_first_residue_unique
    (n p R w rStar eta : ℤ) (hp : 0 < p)
    (hr0 : 0 ≤ rStar) (hrp : rStar < p)
    (h : R + n * w = hmRho n rStar + p * eta) :
    rStar = hmRStar n p R w ∧ eta = hmEta n p R w := by
  have hmod : (R + n * w - rhoStart n) % p = rStar := by
    rw [show R + n * w - rhoStart n = rStar + p * eta by
      unfold hmRho at h
      nlinarith]
    simp [Int.add_emod, Int.emod_eq_of_lt hr0 hrp]
  constructor
  · exact hmod.symm
  · have hcan := hm_first_residue_equation n p R w
    have hrs : rStar = hmRStar n p R w := hmod.symm
    have hpEq : p * eta = p * hmEta n p R w := by
      unfold hmRho at h hcan
      rw [hrs] at h
      nlinarith
    exact mul_left_cancel₀ (ne_of_gt hp) hpEq

/-- Uniqueness of the second residue/index pair in Equation A.9. -/
theorem hm_second_residue_unique
    (n p S w sStar ell : ℤ) (hp : 0 < p)
    (hs0 : 0 ≤ sStar) (hsp : sStar < p)
    (h : S - n * w = hmSigma n sStar + p * ell) :
    sStar = hmSStar n p S w ∧ ell = hmEll n p S w := by
  have hmod : (S - n * w - sigmaStart n) % p = sStar := by
    rw [show S - n * w - sigmaStart n = sStar + p * ell by
      unfold hmSigma at h
      nlinarith]
    simp [Int.add_emod, Int.emod_eq_of_lt hs0 hsp]
  constructor
  · exact hmod.symm
  · have hcan := hm_second_residue_equation n p S w
    have hss : sStar = hmSStar n p S w := hmod.symm
    have hpEq : p * ell = p * hmEll n p S w := by
      unfold hmSigma at h hcan
      rw [hss] at h
      nlinarith
    exact mul_left_cancel₀ (ne_of_gt hp) hpEq

/-! ## Branch signs, Equations A.10--A.13 -/

/-- The parity offset `2*sigmaStart-n-1` is either zero or one. -/
theorem sigmaStart_offset_bounds (n : ℤ) :
    0 ≤ 2 * sigmaStart n - n - 1 ∧ 2 * sigmaStart n - n - 1 ≤ 1 := by
  have hmod0 : 0 ≤ n % 2 := Int.emod_nonneg _ (by norm_num)
  have hmod2 : n % 2 < 2 := Int.emod_lt_of_pos _ (by norm_num)
  have hdiv := Int.emod_add_mul_ediv n 2
  unfold sigmaStart
  omega

/-- Equation A.10 in doubled wall coordinates. -/
theorem intSign_hmEll_eq_VTwice
    (n p S w : ℤ) (hp : 0 < p) :
    intSign (hmEll n p S w) = intSign (VTwice n S w) := by
  let T := S - n * w - sigmaStart n
  have hsignT : intSign (T / p) = intSign T := intSign_ediv_eq T p hp
  have hoff := sigmaStart_offset_bounds n
  have hV : VTwice n S w = 2 * T + (2 * sigmaStart n - n - 1) := by
    dsimp [T]
    unfold VTwice
    ring
  have hsignV : intSign T = intSign (VTwice n S w) := by
    unfold intSign
    by_cases hT : 0 ≤ T
    · have hV0 : 0 ≤ VTwice n S w := by rw [hV]; omega
      simp [hT, hV0]
    · have hTneg : T ≤ -1 := by omega
      have hVneg : VTwice n S w < 0 := by rw [hV]; omega
      simp [hT, not_le_of_gt hVneg]
  unfold hmEll
  exact hsignT.trans hsignV

/-- The leading q-exponent `Gamma_{rho,eta}` in Equation A.11. -/
def hmGamma (n p rho eta : ℤ) : ℤ :=
  p * genDelta n p * eta + genDelta n p * rho + genA0 n p - n * p

/-- Doubled Equation A.11, avoiding half-integral coordinates. -/
theorem two_mul_hmGamma_eq
    (n p R w rho eta : ℤ) (h : R + n * w = rho + p * eta) :
    2 * hmGamma n p rho eta =
      genDelta n p * UTwice n R w + p * (n + p) := by
  calc
    2 * hmGamma n p rho eta =
        2 * genDelta n p * (rho + p * eta) +
          2 * genA0 n p - 2 * n * p := by
            unfold hmGamma
            ring
    _ = 2 * genDelta n p * (R + n * w) +
          2 * genA0 n p - 2 * n * p := by rw [h]
    _ = genDelta n p * UTwice n R w + p * (n + p) := by
          rw [two_mul_genA0]
          simp only [genA0Twice, genDelta, UTwice]
          ring

/-- Equation A.12: `Gamma` and the first wall coordinate have the same sign. -/
theorem intSign_two_hmGamma_eq_UTwice
    (n p R w rho eta : ℤ) (hn : 0 < n) (hp : 0 < p)
    (h : R + n * w = rho + p * eta) :
    intSign (2 * hmGamma n p rho eta) = intSign (UTwice n R w) := by
  have hEq := two_mul_hmGamma_eq n p R w rho eta h
  have hDelta : 0 < genDelta n p := by
    unfold genDelta
    nlinarith
  unfold intSign
  by_cases hU : 0 ≤ UTwice n R w
  · have hG : 0 < 2 * hmGamma n p rho eta := by
      rw [hEq]
      nlinarith [mul_nonneg (le_of_lt hDelta) hU]
    simp [hU, le_of_lt hG]
  · have hUle : UTwice n R w ≤ -1 := by omega
    have hG : 2 * hmGamma n p rho eta < 0 := by
      rw [hEq]
      have hbound : genDelta n p * UTwice n R w ≤ -genDelta n p := by
        nlinarith
      have hcancel : -genDelta n p + p * (n + p) = -n * p := by
        unfold genDelta
        ring
      nlinarith
    simp [hU, not_le_of_gt hG]

/-- The HM denominator exponent never lies on a branch wall. -/
theorem two_hmGamma_ne_zero
    (n p R w rho eta : ℤ) (hn : 0 < n) (hp : 0 < p)
    (h : R + n * w = rho + p * eta) :
    2 * hmGamma n p rho eta ≠ 0 := by
  have hEq := two_mul_hmGamma_eq n p R w rho eta h
  have hDelta : 0 < genDelta n p := by
    unfold genDelta
    nlinarith
  by_cases hU : 0 ≤ UTwice n R w
  · have hG : 0 < 2 * hmGamma n p rho eta := by
      rw [hEq]
      nlinarith [mul_nonneg (le_of_lt hDelta) hU]
    exact ne_of_gt hG
  · have hUle : UTwice n R w ≤ -1 := by omega
    have hbound : genDelta n p * UTwice n R w ≤ -genDelta n p := by
      nlinarith
    have hcancel : -genDelta n p + p * (n + p) = -n * p := by
      unfold genDelta
      ring
    have hG : 2 * hmGamma n p rho eta < 0 := by
      rw [hEq]
      nlinarith
    exact ne_of_lt hG

/-- Equation A.13 for the canonical residue reconstruction. -/
theorem hm_branchCoefficient_eq_sameSign
    (n p R S w : ℤ) (hn : 0 < n) (hp : 0 < p) :
    branchCoefficient
        (2 * hmGamma n p (hmRho n (hmRStar n p R w)) (hmEta n p R w))
        (hmEll n p S w) =
      sameSignCoefficient (UTwice n R w) (VTwice n S w) := by
  have hres := hm_first_residue_equation n p R w
  have hne := two_hmGamma_ne_zero n p R w
    (hmRho n (hmRStar n p R w)) (hmEta n p R w) hn hp hres
  rw [branchCoefficient_eq_signs hne]
  rw [intSign_hmEll_eq_VTwice n p S w hp]
  rw [intSign_two_hmGamma_eq_UTwice n p R w
    (hmRho n (hmRStar n p R w)) (hmEta n p R w) hn hp hres]
  unfold sameSignCoefficient
  congr 2
  omega

/-! ## Exponent collapse, Equations A.14--A.15 -/

/-- The total q-exponent displayed in Equation A.14. -/
def hmExponent (n p rho sigma iota eta ell : ℤ) : ℤ :=
  heckeExp n p rho sigma + n * p ^ 2 * C2 iota +
    n * p * (sigma - rho - n) * iota +
    (genDelta n p * sigma - genA0 n p) * eta +
    (p * genDelta n p * eta + genDelta n p * rho + genA0 n p - n * p) * ell

private theorem hmExponent_twice_identity
    (n p rho sigma iota eta ell : ℤ) :
    heckeExpTwice n p rho sigma + n * p ^ 2 * C2Twice iota +
        2 * n * p * (sigma - rho - n) * iota +
        (2 * genDelta n p * sigma - genA0Twice n p) * eta +
        (2 * p * genDelta n p * eta + 2 * genDelta n p * rho +
          genA0Twice n p - 2 * n * p) * ell =
      heckeExpTwice n p (hmMonomialR n p rho iota eta ell)
        (hmMonomialS n p sigma iota eta ell) +
      genN n p * C2Twice (hmW iota eta ell + 1) := by
  simp only [heckeExpTwice, C2Twice, hmMonomialR, hmMonomialS, hmW,
    genN, genDelta, genA0Twice]
  ring

/-- Polynomial exponent identity A.15. -/
theorem hmExponent_eq_shell
    (n p rho sigma iota eta ell : ℤ) :
    hmExponent n p rho sigma iota eta ell =
      shellExponent n p
        (hmMonomialR n p rho iota eta ell)
        (hmMonomialS n p sigma iota eta ell)
        (hmW iota eta ell) := by
  apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by norm_num)
  calc
    2 * hmExponent n p rho sigma iota eta ell =
        heckeExpTwice n p rho sigma + n * p ^ 2 * C2Twice iota +
          2 * n * p * (sigma - rho - n) * iota +
          (2 * genDelta n p * sigma - genA0Twice n p) * eta +
          (2 * p * genDelta n p * eta + 2 * genDelta n p * rho +
            genA0Twice n p - 2 * n * p) * ell := by
            unfold hmExponent
            rw [← two_mul_heckeExp, ← two_mul_C2, ← two_mul_genA0]
            ring
    _ = heckeExpTwice n p (hmMonomialR n p rho iota eta ell)
          (hmMonomialS n p sigma iota eta ell) +
        genN n p * C2Twice (hmW iota eta ell + 1) :=
          hmExponent_twice_identity n p rho sigma iota eta ell
    _ = 2 * shellExponent n p
          (hmMonomialR n p rho iota eta ell)
          (hmMonomialS n p sigma iota eta ell)
          (hmW iota eta ell) := by
            unfold shellExponent
            rw [← two_mul_heckeExp, ← two_mul_C2]
            ring

/-- A.15 specialized to the unique indices attached to `(R,S,w)`. -/
theorem hmExponent_reconstruct (n p e R S w : ℤ) :
    (e = hmExponent n p
        (hmRho n (hmRStar n p R w))
        (hmSigma n (hmSStar n p S w))
        (hmIota n p R S w) (hmEta n p R w) (hmEll n p S w)) ↔
      e = shellExponent n p R S w := by
  rw [hmExponent_eq_shell]
  rw [hmMonomialR_reconstruct, hmMonomialS_reconstruct, hmW_reconstruct]

/-! ## The source index and its unique `w`-parametrization -/

/--
An index of the expanded HM coefficient after A.3--A.5.  The fields retain
both printed residue variables and all three bilateral indices; the two
monomial equations A.6 are part of the index type.
-/
structure HMExpandedIndex (n p R S : ℤ) where
  rStar : ℤ
  sStar : ℤ
  iota : ℤ
  eta : ℤ
  ell : ℤ
  rStar_nonneg : 0 ≤ rStar
  rStar_lt : rStar < p
  sStar_nonneg : 0 ≤ sStar
  sStar_lt : sStar < p
  monomialR : hmMonomialR n p (hmRho n rStar) iota eta ell = R
  monomialS : hmMonomialS n p (hmSigma n sStar) iota eta ell = S

private theorem HMExpandedIndex.ext_values
    {n p R S : ℤ} {x y : HMExpandedIndex n p R S}
    (hr : x.rStar = y.rStar) (hs : x.sStar = y.sStar)
    (hi : x.iota = y.iota) (he : x.eta = y.eta) (hl : x.ell = y.ell) :
    x = y := by
  cases x
  cases y
  simp_all

/-- The source shell coordinate A.7. -/
def HMExpandedIndex.shell {n p R S : ℤ} (x : HMExpandedIndex n p R S) : ℤ :=
  hmW x.iota x.eta x.ell

/-- Canonical expanded HM index reconstructed from a shell coordinate. -/
def hmExpandedIndexOfW (n p R S w : ℤ) (hp : 0 < p) :
    HMExpandedIndex n p R S where
  rStar := hmRStar n p R w
  sStar := hmSStar n p S w
  iota := hmIota n p R S w
  eta := hmEta n p R w
  ell := hmEll n p S w
  rStar_nonneg := by
    have h := hmRStar_mem n p R w hp
    rw [Finset.mem_Icc] at h
    exact h.1
  rStar_lt := by
    have h := hmRStar_mem n p R w hp
    rw [Finset.mem_Icc] at h
    have hle := h.2
    omega
  sStar_nonneg := by
    have h := hmSStar_mem n p S w hp
    rw [Finset.mem_Icc] at h
    exact h.1
  sStar_lt := by
    have h := hmSStar_mem n p S w hp
    rw [Finset.mem_Icc] at h
    have hle := h.2
    omega
  monomialR := hmMonomialR_reconstruct n p R S w
  monomialS := hmMonomialS_reconstruct n p R S w

/-- Every source index is uniquely reconstructed from its shell coordinate. -/
theorem hmExpandedIndexOfW_shell
    (n p R S : ℤ) (hp : 0 < p) (x : HMExpandedIndex n p R S) :
    hmExpandedIndexOfW n p R S x.shell hp = x := by
  have hfirst :
      R + n * x.shell = hmRho n x.rStar + p * x.eta := by
    calc
      R + n * x.shell =
          hmMonomialR n p (hmRho n x.rStar) x.iota x.eta x.ell +
            n * x.shell := by rw [x.monomialR]
      _ = hmRho n x.rStar + p * x.eta := by
        unfold HMExpandedIndex.shell hmMonomialR hmW
        ring
  have hsecond :
      S - n * x.shell = hmSigma n x.sStar + p * x.ell := by
    calc
      S - n * x.shell =
          hmMonomialS n p (hmSigma n x.sStar) x.iota x.eta x.ell -
            n * x.shell := by rw [x.monomialS]
      _ = hmSigma n x.sStar + p * x.ell := by
        unfold HMExpandedIndex.shell hmMonomialS hmW
        ring
  have hr := hm_first_residue_unique n p R x.shell x.rStar x.eta hp
    x.rStar_nonneg x.rStar_lt hfirst
  have hs := hm_second_residue_unique n p S x.shell x.sStar x.ell hp
    x.sStar_nonneg x.sStar_lt hsecond
  apply HMExpandedIndex.ext_values
  · exact hr.1.symm
  · exact hs.1.symm
  · change hmIota n p R S x.shell = x.iota
    unfold hmIota
    rw [← hr.2, ← hs.2]
    unfold HMExpandedIndex.shell hmW
    ring
  · exact hr.2.symm
  · exact hs.2.symm

/-- The five constrained source indices are equivalent to the single shell index `w`. -/
def hmExpandedIndexEquiv (n p R S : ℤ) (hp : 0 < p) :
    ℤ ≃ HMExpandedIndex n p R S where
  toFun w := hmExpandedIndexOfW n p R S w hp
  invFun x := x.shell
  left_inv := by
    intro w
    exact hmW_reconstruct n p R S w
  right_inv := hmExpandedIndexOfW_shell n p R S hp

/-! ## Coefficient comparison, Equations A.16--A.17 -/

/--
One term of the source-faithful expanded HM coefficient.  It retains the
printed residues `(rStar,sStar)` and all bilateral indices
`(iota,eta,ell)` rather than starting from the target wall kernel.
-/
def hmExpandedKernel {n p R S : ℤ}
    (e : ℤ) (x : HMExpandedIndex n p R S) : ℚ :=
  negOnePow (R + S) *
    branchCoefficient (2 * hmGamma n p (hmRho n x.rStar) x.eta) x.ell *
    (if e = hmExponent n p (hmRho n x.rStar) (hmSigma n x.sStar)
        x.iota x.eta x.ell then 1 else 0)

/--
Coefficient of `q^e x^R y^S` in the HM formula after the independently
verified Kronecker expansion A.3 and Jacobi expansion A.4.
-/
def hmExpandedCoefficient (n p e R S : ℤ) : ℚ :=
  ∑ᶠ x : HMExpandedIndex n p R S, hmExpandedKernel e x

/--
One coefficient contribution of the printed HM correction after applying the
Kronecker expansion A.3, the Jacobi expansion A.4, and the unique residue
reconstruction A.6--A.9.
-/
def hmThetaKernel (n p e R S w : ℤ) : ℚ :=
  negOnePow (R + S) *
    branchCoefficient
      (2 * hmGamma n p (hmRho n (hmRStar n p R w)) (hmEta n p R w))
      (hmEll n p S w) *
    (if e = hmExponent n p
        (hmRho n (hmRStar n p R w))
        (hmSigma n (hmSStar n p S w))
        (hmIota n p R S w) (hmEta n p R w) (hmEll n p S w)
      then 1 else 0)

/-- Coefficient of `q^e x^R y^S` in the printed HM theta correction. -/
def hmThetaCoefficient (n p e R S : ℤ) : ℚ :=
  ∑ᶠ w : ℤ, hmThetaKernel n p e R S w

/-- Canonical reconstruction preserves the expanded coefficient summand. -/
theorem hmExpandedKernel_indexOfW
    (n p e R S w : ℤ) (hp : 0 < p) :
    hmExpandedKernel e (hmExpandedIndexOfW n p R S w hp) =
      hmThetaKernel n p e R S w := rfl

/-- Equations A.6--A.9 reindex the source-faithful expanded coefficient by `w`. -/
theorem hmExpandedCoefficient_eq_hmThetaCoefficient
    (n p e R S : ℤ) (hp : 0 < p) :
    hmExpandedCoefficient n p e R S = hmThetaCoefficient n p e R S := by
  unfold hmExpandedCoefficient hmThetaCoefficient
  calc
    (∑ᶠ x : HMExpandedIndex n p R S, hmExpandedKernel e x) =
        ∑ᶠ w : ℤ,
          hmExpandedKernel e (hmExpandedIndexEquiv n p R S hp w) :=
      (finsum_comp_equiv (hmExpandedIndexEquiv n p R S hp)).symm
    _ = ∑ᶠ w : ℤ, hmThetaKernel n p e R S w := by
      apply finsum_congr
      intro w
      exact hmExpandedKernel_indexOfW n p e R S w hp

/-- Pointwise comparison of the HM kernel with the sign-wall kernel. -/
theorem hmThetaKernel_eq_thetaKernel
    (n p e R S w : ℤ) (hn : 0 < n) (hp : 0 < p) :
    hmThetaKernel n p e R S w = thetaKernel n p e R S w := by
  unfold hmThetaKernel thetaKernel shellIndicator
  rw [hm_branchCoefficient_eq_sameSign n p R S w hn hp]
  simp only [hmExponent_reconstruct n p e R S w]

/--
Proposition 2.2 / Equations A.16--A.17: the Hickerson--Mortenson printed theta
correction is coefficientwise equal to the Hahn sign-wall correction for every
positive `n,p`; no coprimality hypothesis is used.
-/
theorem hmThetaCoefficient_eq_thetaCoefficient
    (n p e R S : ℤ) (hn : 0 < n) (hp : 0 < p) :
    hmThetaCoefficient n p e R S = thetaCoefficient n p e R S := by
  unfold hmThetaCoefficient thetaCoefficient
  apply finsum_congr
  intro w
  exact hmThetaKernel_eq_thetaKernel n p e R S w hn hp

/--
Source-faithful form of Proposition 2.2: the coefficient extracted from the
expanded printed HM correction equals the Hahn sign-wall coefficient.
-/
theorem hmExpandedCoefficient_eq_thetaCoefficient
    (n p e R S : ℤ) (hn : 0 < n) (hp : 0 < p) :
    hmExpandedCoefficient n p e R S = thetaCoefficient n p e R S := by
  rw [hmExpandedCoefficient_eq_hmThetaCoefficient n p e R S hp]
  exact hmThetaCoefficient_eq_thetaCoefficient n p e R S hn hp

end

end QseriesFormalization.Pending.Ch10HMComparison
