import QseriesFormalization.Pending.Chapter10_M3_HeckeCoeffNF
import QseriesFormalization.Pending.Chapter10_M3_AppellMhat
import QseriesFormalization.Pending.Chapter10_M3_AppellRawCoeff
import QseriesFormalization.Pending.Chapter10_M3_DiagClose
import QseriesFormalization.Pending.Chapter10_M3_AppellCoeffRows

/-!
# Appell-side coefficient normal form (genuine route, NOT the circular wrapper)

`coeffQXY (PpairY·BX + PpairX·BY) e x y = ∑ᶠ u, ∑ᶠ v, FhmBYBX_uvOmegaCoeff e x y u v`,
proved INDEPENDENTLY of `cleared_identity` via the factorization `Ppair=Mhat 1` + the four-row
`coeffXY_Mhat_row_sum` + per-row coeff_hsum expansion + the Appell strip-fold (`t→l`) + the φ-maps.
This is the f_{2,3,2}→Appell content; landing it (with the proven Hecke uvOmega) closes cleared_identity
by `ext_coeffQXY` directly (no off-diag/diagonal split).
-/

namespace QseriesFormalization.Pending.Ch10M3Ghat

open QseriesFormalization.Ch10TwoVar
open QseriesFormalization.Pending.Ch10HM
open QseriesFormalization.Pending.Ch10M3Mhat
open QseriesFormalization.Pending.Ch10M3MhatFE2
open QseriesFormalization.Pending.Ch10M3HMf
open QseriesFormalization.Pending.Ch10M3OmegaKernel
open QseriesFormalization.Pending.Ch10M3DiagClose
open scoped Classical

noncomputable section

/-- Step 1 (REDUCTION, cheap): the Appell cleared side coefficient = the four-row Mhat coefficient. -/
theorem coeffQXY_Ppair_boundary_row_sum (e x y : ℤ) :
    coeffQXY (PpairY * BX + PpairX * BY) e x y =
      ∑ row : MhatRow,
        (row.lead.toMonom *
          ((mhatJThetaFamily row).hsum *
            ((mhatAppellFamilyOf mhatAppellPWO 1 row).hsum *
              (mhatDThetaFamily 1 row).hsum))).coeff (expQXY e x y) := by
  rw [Ppair_boundary_eq_Mhat_one]
  show (coeffXY (Mhat 1) x y).coeff e = _
  rw [coeffXY_Mhat_row_sum]

private theorem support_finsum_prod_left_finite {α β : Type*} {f : α × β → ℚ}
    (hf : (Function.support f).Finite) :
    (Function.support (fun a : α => ∑ᶠ b : β, f (a, b))).Finite := by
  classical
  refine Set.Finite.subset (hf.image (fun p : α × β => p.1)) ?_
  intro a ha
  simp only [Function.mem_support] at ha
  by_contra hmem
  have hzero : ∀ b : β, f (a, b) = 0 := by
    intro b
    by_contra hb
    apply hmem
    refine ⟨(a, b), ?_, rfl⟩
    simpa [Function.mem_support] using hb
  exact ha (finsum_eq_zero_of_forall_eq_zero hzero)

private theorem support_section_right_finite {α β : Type*} {f : α × β → ℚ}
    (hf : (Function.support f).Finite) (a : α) :
    (Function.support (fun b : β => f (a, b))).Finite := by
  classical
  have hinj : Function.Injective (fun b : β => (a, b)) := by
    intro b₁ b₂ h
    exact congrArg Prod.snd h
  exact hf.preimage (Set.injOn_of_injective hinj)

private theorem support_add_finite {α : Type*} {f g : α → ℚ}
    (hf : (Function.support f).Finite) (hg : (Function.support g).Finite) :
    (Function.support (fun a : α => f a + g a)).Finite := by
  classical
  refine (hf.union hg).subset ?_
  intro a ha
  rw [Function.mem_support] at ha
  simp only [Set.mem_union, Function.mem_support]
  by_cases hfz : f a = 0
  · right
    intro hgz
    exact ha (by simp [hfz, hgz])
  · left
    exact hfz

private theorem finsum₂_add_distrib {α β : Type*} {f g : α × β → ℚ}
    (hf : (Function.support f).Finite) (hg : (Function.support g).Finite) :
    (∑ᶠ a : α, ∑ᶠ b : β, (f (a, b) + g (a, b))) =
      (∑ᶠ a : α, ∑ᶠ b : β, f (a, b)) +
        (∑ᶠ a : α, ∑ᶠ b : β, g (a, b)) := by
  classical
  calc
    (∑ᶠ a : α, ∑ᶠ b : β, (f (a, b) + g (a, b))) =
        ∑ᶠ a : α, ((∑ᶠ b : β, f (a, b)) + (∑ᶠ b : β, g (a, b))) := by
      apply finsum_congr
      intro a
      rw [finsum_add_distrib
        (support_section_right_finite (f := f) hf a)
        (support_section_right_finite (f := g) hg a)]
    _ = (∑ᶠ a : α, ∑ᶠ b : β, f (a, b)) +
        (∑ᶠ a : α, ∑ᶠ b : β, g (a, b)) := by
      rw [finsum_add_distrib
        (support_finsum_prod_left_finite (f := f) hf)
        (support_finsum_prod_left_finite (f := g) hg)]

private theorem finsum₂_curry {α β : Type*} {f : α × β → ℚ}
    (hf : (Function.support f).Finite) :
    (∑ᶠ p : α × β, f p) = ∑ᶠ a : α, ∑ᶠ b : β, f (a, b) :=
  finsum_curry _ hf

def AppellSectorKernel (e a b eps eta U V : ℤ) : ℚ :=
  negOnePowIntQ (2 * a + eps + (2 * b + eta) + V) *
    (((AppellBracketEta eta a b U V : ℤ) : ℚ)) *
      (if e = heckePhi (2 * a + eps) (2 * b + eta) U V then (1 : ℚ) else 0)

def OmegaSectorKernel (e a b eps eta U V : ℤ) : ℚ :=
  negOnePowIntQ (2 * a + eps + (2 * b + eta) + V) *
    (((uvOmegaBracket a b V : ℤ) : ℚ)) *
      (if e = heckePhi (2 * a + eps) (2 * b + eta) U V then (1 : ℚ) else 0)

def PairDefectSectorKernel (e a b eps eta U V : ℤ) : ℚ :=
  negOnePowIntQ (2 * a + eps + (2 * b + eta) + V) *
    (((AppellBracketEta eta a b U V +
      AppellBracketEta eta a b (1 - U - V) V -
      2 * uvOmegaBracket a b V : ℤ) : ℚ)) *
      (if e = heckePhi (2 * a + eps) (2 * b + eta) U V then (1 : ℚ) else 0)

private def R0Kernel (e a y U V : ℤ) : ℚ :=
  negOnePowIntQ (2 * a + y + V) *
    (((sg (U + V - a - 1) (a - V) : ℤ) : ℚ)) *
    (if e = heckePhi (2 * a) y U V then (1 : ℚ) else 0)

private def R1Kernel (e x b U V : ℤ) : ℚ :=
  negOnePowIntQ (x + 2 * b + V) *
    (((sg (U - b - 1) (V + b) : ℤ) : ℚ)) *
    (if e = heckePhi x (2 * b) U V then (1 : ℚ) else 0)

private def R2Kernel (e a y U V : ℤ) : ℚ :=
  negOnePowIntQ (2 * a + 1 + y + V) *
    (((sg (U + V - a - 1) (a - V) : ℤ) : ℚ)) *
    (if e = heckePhi (2 * a + 1) y U V then (1 : ℚ) else 0)

private def R3Kernel (e x b U V : ℤ) : ℚ :=
  negOnePowIntQ (x + 2 * b + 1 + V) *
    (((sg (U - b - 2) (V + b) : ℤ) : ℚ)) *
    (if e = heckePhi x (2 * b + 1) U V then (1 : ℚ) else 0)

private theorem R0Kernel_support_finite (e a y : ℤ) :
    (Function.support (fun uv : ℤ × ℤ => R0Kernel e a y uv.1 uv.2)).Finite := by
  simpa [R0Kernel] using R0_uv_kernel_support_finite e a y

private theorem R1Kernel_support_finite (e x b : ℤ) :
    (Function.support (fun uv : ℤ × ℤ => R1Kernel e x b uv.1 uv.2)).Finite := by
  simpa [R1Kernel] using R1_uv_kernel_support_finite e x b

private theorem R2Kernel_support_finite (e a y : ℤ) :
    (Function.support (fun uv : ℤ × ℤ => R2Kernel e a y uv.1 uv.2)).Finite := by
  simpa [R2Kernel] using R2_uv_kernel_support_finite e a y

private theorem R3Kernel_support_finite (e x b : ℤ) :
    (Function.support (fun uv : ℤ × ℤ => R3Kernel e x b uv.1 uv.2)).Finite := by
  simpa [R3Kernel] using R3_uv_kernel_support_finite e x b

private theorem sg_parity_scale (a b eps eta V : ℤ)
    (heps : eps = 0 ∨ eps = 1) (heta : eta = 0 ∨ eta = 1) :
    sg (2 * a + eps - 2 * V) (2 * b + eta + 2 * V) =
      sg (a - V) (b + V) := by
  rcases heps with rfl | rfl <;> rcases heta with rfl | rfl <;>
    unfold sg <;> split_ifs <;> omega

private theorem FhmBYBX_uvOmegaCoeff_parity (e a b eps eta U V : ℤ)
    (heps : eps = 0 ∨ eps = 1) (heta : eta = 0 ∨ eta = 1) :
    FhmBYBX_uvOmegaCoeff e (2 * a + eps) (2 * b + eta) U V =
      OmegaSectorKernel e a b eps eta U V := by
  unfold FhmBYBX_uvOmegaCoeff OmegaSectorKernel heckePhi
  dsimp
  rw [sg_parity_scale a b eps eta V heps heta]
  by_cases h :
      e = FhmExp (2 * a + eps - 2 * V) (2 * b + eta + 2 * V) +
        BYExp U + BXExp (U + V)
  · simp [h, uvOmegaBracket]
  · simp [h]

def defectG (K t : ℤ) : ℚ :=
  (zsgn t + zsgn (-K - t)) / 2

private theorem defectG_support_finite (K : ℤ) :
    (Function.support (defectG K)).Finite := by
  classical
  refine ((Set.finite_Icc (-K) 0).union (Set.finite_Icc 0 (-K))).subset ?_
  intro t ht
  rw [Function.mem_support] at ht
  simp only [Set.mem_union, Set.mem_Icc]
  unfold defectG zsgn at ht
  by_cases h0 : 0 ≤ t
  · by_cases hle : t ≤ -K
    · right
      exact ⟨h0, hle⟩
    · exfalso
      apply ht
      simp [h0, hle]
  · by_cases hle : t ≤ -K
    · exfalso
      apply ht
      simp [h0, hle]
    · left
      omega

private theorem AppellBracketEta_pair_defect_wall_coords (eta a b p q : ℤ) :
    ((AppellBracketEta eta a b (UOf a q) (VOf a p q) +
      AppellBracketEta eta a b (1 - UOf a q - VOf a p q) (VOf a p q) -
      2 * uvOmegaBracket a b (VOf a p q) : ℤ) : ℚ) =
      defectG (a + b + eta + 1) p + defectG (a + b + eta + 1) q := by
  rw [AppellBracketEta_pair_defect]
  unfold defectG pCoord qCoord UOf VOf
  ring

private theorem weighted_first_prod_support_finite
    (L E C A : ℤ) (G : ℤ → ℚ) (hG : (Function.support G).Finite) (hA : A ≠ 0) :
    (Function.support (fun pq : ℤ × ℤ =>
      G pq.1 * negOnePowIntQ (pq.1 + pq.2) *
        (if E = C + A * PsiCore L pq.1 pq.2 then (1 : ℚ) else 0))).Finite := by
  classical
  have hset : (⋃ p ∈ Function.support G,
      (fun q : ℤ => (p, q)) '' {q : ℤ | E = C + A * PsiCore L p q}).Finite := by
    exact hG.biUnion fun p hp =>
      (affine_PsiCore_fixed_left_finite L E C A p hA).image (fun q : ℤ => (p, q))
  refine hset.subset ?_
  intro pq hpq
  rw [Function.mem_support] at hpq
  simp only [Set.mem_iUnion, exists_prop, Set.mem_image, Set.mem_setOf_eq]
  by_cases hGp : G pq.1 = 0
  · exfalso
    exact hpq (by simp [hGp])
  by_cases hEq : E = C + A * PsiCore L pq.1 pq.2
  · exact ⟨pq.1, by simpa [Function.mem_support] using hGp, pq.2, hEq, rfl⟩
  · exfalso
    exact hpq (by simp [hEq])

private theorem weighted_second_prod_support_finite
    (L E C A : ℤ) (G : ℤ → ℚ) (hG : (Function.support G).Finite) (hA : A ≠ 0) :
    (Function.support (fun pq : ℤ × ℤ =>
      G pq.2 * negOnePowIntQ (pq.1 + pq.2) *
        (if E = C + A * PsiCore L pq.1 pq.2 then (1 : ℚ) else 0))).Finite := by
  classical
  have hset : (⋃ q ∈ Function.support G,
      (fun p : ℤ => (p, q)) '' {p : ℤ | E = C + A * PsiCore L p q}).Finite := by
    exact hG.biUnion fun q hq =>
      (affine_PsiCore_fixed_right_finite L E C A q hA).image (fun p : ℤ => (p, q))
  refine hset.subset ?_
  intro pq hpq
  rw [Function.mem_support] at hpq
  simp only [Set.mem_iUnion, exists_prop, Set.mem_image, Set.mem_setOf_eq]
  by_cases hGq : G pq.2 = 0
  · exfalso
    exact hpq (by simp [hGq])
  by_cases hEq : E = C + A * PsiCore L pq.1 pq.2
  · exact ⟨pq.2, by simpa [Function.mem_support] using hGq, pq.1, hEq, rfl⟩
  · exfalso
    exact hpq (by simp [hEq])

private theorem qInvL_weighted_pair_prod_sum_zero_affine
    (L E C A K : ℤ) (hA : A ≠ 0) (hL : Odd L) :
    (∑ᶠ pq : ℤ × ℤ,
      (defectG K pq.1 + defectG K pq.2) *
        negOnePowIntQ (pq.1 + pq.2) *
        (if E = C + A * PsiCore L pq.1 pq.2 then (1 : ℚ) else 0)) = 0 := by
  classical
  let f₁ : ℤ × ℤ → ℚ := fun pq =>
    defectG K pq.1 * negOnePowIntQ (pq.1 + pq.2) *
      (if E = C + A * PsiCore L pq.1 pq.2 then (1 : ℚ) else 0)
  let f₂ : ℤ × ℤ → ℚ := fun pq =>
    defectG K pq.2 * negOnePowIntQ (pq.1 + pq.2) *
      (if E = C + A * PsiCore L pq.1 pq.2 then (1 : ℚ) else 0)
  have hf₁ : (Function.support f₁).Finite :=
    weighted_first_prod_support_finite L E C A (defectG K) (defectG_support_finite K) hA
  have hf₂ : (Function.support f₂).Finite :=
    weighted_second_prod_support_finite L E C A (defectG K) (defectG_support_finite K) hA
  calc
    (∑ᶠ pq : ℤ × ℤ,
      (defectG K pq.1 + defectG K pq.2) *
        negOnePowIntQ (pq.1 + pq.2) *
        (if E = C + A * PsiCore L pq.1 pq.2 then (1 : ℚ) else 0))
        = (∑ᶠ pq : ℤ × ℤ, (f₁ pq + f₂ pq)) := by
          apply finsum_congr
          intro pq
          dsimp [f₁, f₂]
          ring
    _ = (∑ᶠ pq : ℤ × ℤ, f₁ pq) + (∑ᶠ pq : ℤ × ℤ, f₂ pq) := by
          exact finsum_add_distrib hf₁ hf₂
    _ = 0 + (∑ᶠ pq : ℤ × ℤ, f₂ pq) := by
          have hzero₁ :
              (∑ᶠ pq : ℤ × ℤ, f₁ pq) = 0 := by
            rw [finsum_curry _ hf₁]
            exact qInvL_weighted_p_sum_zero_affine L E C A (defectG K) hL
          rw [hzero₁]
    _ = 0 + 0 := by
          have hzero₂ :
              (∑ᶠ pq : ℤ × ℤ, f₂ pq) = 0 := by
            exact qInvL_weighted_second_prod_sum_zero_affine L E C A (defectG K) hL
          rw [hzero₂]
    _ = 0 := by ring

private theorem sector_pair_defect_prod_sum_zero (e a b eps eta : ℤ) :
    (∑ᶠ uv : ℤ × ℤ,
      PairDefectSectorKernel e a b eps eta uv.1 uv.2) = 0 := by
  classical
  let Euv : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun pq => (UOf a pq.2, VOf a pq.1 pq.2)
      invFun := fun uv => (pCoord a uv.1 uv.2, qCoord a uv.1)
      left_inv := by
        intro pq
        rcases pq with ⟨p, q⟩
        ext <;> unfold pCoord qCoord UOf VOf <;> ring
      right_inv := by
        intro uv
        rcases uv with ⟨U, V⟩
        ext <;> unfold pCoord qCoord UOf VOf <;> ring }
  let L : ℤ := 2 * a + 4 * b + 5 + 2 * eta - 2 * eps
  let C : ℤ := PhiPQConst a b eps eta
  let K : ℤ := a + b + eta + 1
  let s0 : ℚ := negOnePowIntQ (4 * a + 2 * b + eps + eta + 1)
  have hL : Odd L := by
    dsimp [L]
    exact parity_L_odd a b eps eta
  calc
    (∑ᶠ uv : ℤ × ℤ, PairDefectSectorKernel e a b eps eta uv.1 uv.2)
        = ∑ᶠ pq : ℤ × ℤ,
            PairDefectSectorKernel e a b eps eta (Euv pq).1 (Euv pq).2 := by
          exact (finsum_comp_equiv Euv).symm
    _ = ∑ᶠ pq : ℤ × ℤ,
        s0 * ((defectG K pq.1 + defectG K pq.2) *
          negOnePowIntQ (pq.1 + pq.2) *
          (if e = C + 9 * PsiCore L pq.1 pq.2 then (1 : ℚ) else 0)) := by
          apply finsum_congr
          intro pq
          rcases pq with ⟨p, q⟩
          dsimp [Euv, L, C, K, s0]
          unfold PairDefectSectorKernel
          rw [AppellBracketEta_pair_defect_wall_coords]
          rw [heckePhi_wall_coords]
          have hsign :
              negOnePowIntQ (2 * a + eps + (2 * b + eta) + VOf a p q) =
                negOnePowIntQ (4 * a + 2 * b + eps + eta + 1) *
                  negOnePowIntQ (p + q) := by
            rw [show 2 * a + eps + (2 * b + eta) + VOf a p q =
                (4 * a + 2 * b + eps + eta + 1) + (p + q) by
                  unfold VOf
                  ring]
            rw [negOnePowIntQ_add]
          rw [hsign]
          ring
    _ = s0 * (∑ᶠ pq : ℤ × ℤ,
        (defectG K pq.1 + defectG K pq.2) *
          negOnePowIntQ (pq.1 + pq.2) *
          (if e = C + 9 * PsiCore L pq.1 pq.2 then (1 : ℚ) else 0)) := by
          rw [mul_finsum]
    _ = s0 * 0 := by
          rw [qInvL_weighted_pair_prod_sum_zero_affine L e C 9 K (by norm_num) hL]
    _ = 0 := by ring

private def uvTau : ℤ × ℤ ≃ ℤ × ℤ where
  toFun uv := (1 - uv.1 - uv.2, uv.2)
  invFun uv := (1 - uv.1 - uv.2, uv.2)
  left_inv := by
    intro uv
    rcases uv with ⟨U, V⟩
    ext <;> ring
  right_inv := by
    intro uv
    rcases uv with ⟨U, V⟩
    ext <;> ring

private theorem pair_defect_kernel_eq_appell_tau_sub (e a b eps eta U V : ℤ) :
    PairDefectSectorKernel e a b eps eta U V =
      AppellSectorKernel e a b eps eta U V +
        AppellSectorKernel e a b eps eta (1 - U - V) V -
          2 * OmegaSectorKernel e a b eps eta U V := by
  unfold PairDefectSectorKernel AppellSectorKernel OmegaSectorKernel
  rw [← heckePhi_invol (2 * a + eps) (2 * b + eta) U V]
  by_cases h : e = heckePhi (2 * a + eps) (2 * b + eta) U V
  · simp [h]
    ring_nf
  · simp [h]

private theorem sector_product_sum_eq_omega (e a b eps eta : ℤ)
    (hA : (Function.support (fun uv : ℤ × ℤ =>
      AppellSectorKernel e a b eps eta uv.1 uv.2)).Finite)
    (hO : (Function.support (fun uv : ℤ × ℤ =>
      OmegaSectorKernel e a b eps eta uv.1 uv.2)).Finite) :
    (∑ᶠ uv : ℤ × ℤ, AppellSectorKernel e a b eps eta uv.1 uv.2) =
      ∑ᶠ uv : ℤ × ℤ, OmegaSectorKernel e a b eps eta uv.1 uv.2 := by
  classical
  let A : ℤ × ℤ → ℚ := fun uv => AppellSectorKernel e a b eps eta uv.1 uv.2
  let O : ℤ × ℤ → ℚ := fun uv => OmegaSectorKernel e a b eps eta uv.1 uv.2
  let T : ℤ × ℤ ≃ ℤ × ℤ := uvTau
  have hAT : (Function.support (fun uv : ℤ × ℤ => A (T uv))).Finite :=
    hA.preimage (Set.injOn_of_injective (Equiv.injective T))
  have h2O : (Function.support (fun uv : ℤ × ℤ => (2 : ℚ) * O uv)).Finite := by
    refine hO.subset ?_
    intro uv huv
    rw [Function.mem_support] at huv ⊢
    by_contra hOzero
    apply huv
    dsimp [O] at hOzero ⊢
    simp [hOzero]
  have hAadd : (Function.support (fun uv : ℤ × ℤ => A uv + A (T uv))).Finite :=
    (hA.union hAT).subset (by
      intro uv huv
      rw [Function.mem_support] at huv
      simp only [Set.mem_union, Function.mem_support]
      by_cases hAu : A uv = 0
      · right
        intro hATzero
        exact huv (by simp [hAu, hATzero])
      · left
        exact hAu)
  have hpairzero :
      (∑ᶠ uv : ℤ × ℤ, (A uv + A (T uv) - (2 : ℚ) * O uv)) = 0 := by
    rw [← sector_pair_defect_prod_sum_zero e a b eps eta]
    apply finsum_congr
    intro uv
    rcases uv with ⟨U, V⟩
    dsimp [A, O, T, uvTau]
    exact (pair_defect_kernel_eq_appell_tau_sub e a b eps eta U V).symm
  have hdist :
      (∑ᶠ uv : ℤ × ℤ, (A uv + A (T uv) - (2 : ℚ) * O uv)) =
        (∑ᶠ uv : ℤ × ℤ, A uv) + (∑ᶠ uv : ℤ × ℤ, A (T uv)) -
          (2 : ℚ) * (∑ᶠ uv : ℤ × ℤ, O uv) := by
    rw [finsum_sub_distrib hAadd h2O]
    rw [finsum_add_distrib hA hAT]
    rw [(mul_finsum (fun uv : ℤ × ℤ => O uv) (2 : ℚ)).symm]
  have htausum : (∑ᶠ uv : ℤ × ℤ, A (T uv)) = ∑ᶠ uv : ℤ × ℤ, A uv :=
    finsum_comp_equiv T
  have hzero := hpairzero
  rw [hdist, htausum] at hzero
  linarith

private theorem sector_nested_sum_eq_omega (e a b eps eta : ℤ)
    (hA : (Function.support (fun uv : ℤ × ℤ =>
      AppellSectorKernel e a b eps eta uv.1 uv.2)).Finite)
    (hO : (Function.support (fun uv : ℤ × ℤ =>
      OmegaSectorKernel e a b eps eta uv.1 uv.2)).Finite) :
    (∑ᶠ U : ℤ, ∑ᶠ V : ℤ, AppellSectorKernel e a b eps eta U V) =
      ∑ᶠ U : ℤ, ∑ᶠ V : ℤ, OmegaSectorKernel e a b eps eta U V := by
  rw [← finsum₂_curry
    (f := fun uv : ℤ × ℤ => AppellSectorKernel e a b eps eta uv.1 uv.2) hA]
  rw [← finsum₂_curry
    (f := fun uv : ℤ × ℤ => OmegaSectorKernel e a b eps eta uv.1 uv.2) hO]
  exact sector_product_sum_eq_omega e a b eps eta hA hO

private theorem AppellSector_even_even_eq (e a b U V : ℤ) :
    AppellSectorKernel e a b 0 0 U V =
      R0Kernel e a (2 * b) U V + R1Kernel e (2 * a) b U V := by
  unfold AppellSectorKernel AppellBracketEta R0Kernel R1Kernel
  by_cases h : e = heckePhi (2 * a) (2 * b) U V
  · simp [h]
    ring_nf
  · simp [h]

private theorem AppellSector_even_odd_eq (e a b U V : ℤ) :
    AppellSectorKernel e a b 0 1 U V =
      R0Kernel e a (2 * b + 1) U V + R3Kernel e (2 * a) b U V := by
  unfold AppellSectorKernel AppellBracketEta R0Kernel R3Kernel
  by_cases h : e = heckePhi (2 * a) (2 * b + 1) U V
  · simp [h]
    ring_nf
  · simp [h]

private theorem AppellSector_odd_even_eq (e a b U V : ℤ) :
    AppellSectorKernel e a b 1 0 U V =
      R2Kernel e a (2 * b) U V + R1Kernel e (2 * a + 1) b U V := by
  unfold AppellSectorKernel AppellBracketEta R2Kernel R1Kernel
  by_cases h : e = heckePhi (2 * a + 1) (2 * b) U V
  · simp [h]
    ring_nf
  · simp [h]

private theorem AppellSector_odd_odd_eq (e a b U V : ℤ) :
    AppellSectorKernel e a b 1 1 U V =
      R2Kernel e a (2 * b + 1) U V + R3Kernel e (2 * a + 1) b U V := by
  unfold AppellSectorKernel AppellBracketEta R2Kernel R3Kernel
  by_cases h : e = heckePhi (2 * a + 1) (2 * b + 1) U V
  · simp [h]
    ring_nf
  · simp [h]

private theorem AppellSector_support_even_even (e a b : ℤ) :
    (Function.support (fun uv : ℤ × ℤ =>
      AppellSectorKernel e a b 0 0 uv.1 uv.2)).Finite := by
  have h0 := R0Kernel_support_finite e a (2 * b)
  have h1 := R1Kernel_support_finite e (2 * a) b
  have hEq :
      (fun uv : ℤ × ℤ => AppellSectorKernel e a b 0 0 uv.1 uv.2) =
        fun uv : ℤ × ℤ => R0Kernel e a (2 * b) uv.1 uv.2 +
          R1Kernel e (2 * a) b uv.1 uv.2 := by
    funext uv
    rcases uv with ⟨U, V⟩
    exact AppellSector_even_even_eq e a b U V
  rw [hEq]
  exact support_add_finite h0 h1

private theorem AppellSector_support_even_odd (e a b : ℤ) :
    (Function.support (fun uv : ℤ × ℤ =>
      AppellSectorKernel e a b 0 1 uv.1 uv.2)).Finite := by
  have h0 := R0Kernel_support_finite e a (2 * b + 1)
  have h3 := R3Kernel_support_finite e (2 * a) b
  have hEq :
      (fun uv : ℤ × ℤ => AppellSectorKernel e a b 0 1 uv.1 uv.2) =
        fun uv : ℤ × ℤ => R0Kernel e a (2 * b + 1) uv.1 uv.2 +
          R3Kernel e (2 * a) b uv.1 uv.2 := by
    funext uv
    rcases uv with ⟨U, V⟩
    exact AppellSector_even_odd_eq e a b U V
  rw [hEq]
  exact support_add_finite h0 h3

private theorem AppellSector_support_odd_even (e a b : ℤ) :
    (Function.support (fun uv : ℤ × ℤ =>
      AppellSectorKernel e a b 1 0 uv.1 uv.2)).Finite := by
  have h2 := R2Kernel_support_finite e a (2 * b)
  have h1 := R1Kernel_support_finite e (2 * a + 1) b
  have hEq :
      (fun uv : ℤ × ℤ => AppellSectorKernel e a b 1 0 uv.1 uv.2) =
        fun uv : ℤ × ℤ => R2Kernel e a (2 * b) uv.1 uv.2 +
          R1Kernel e (2 * a + 1) b uv.1 uv.2 := by
    funext uv
    rcases uv with ⟨U, V⟩
    exact AppellSector_odd_even_eq e a b U V
  rw [hEq]
  exact support_add_finite h2 h1

private theorem AppellSector_support_odd_odd (e a b : ℤ) :
    (Function.support (fun uv : ℤ × ℤ =>
      AppellSectorKernel e a b 1 1 uv.1 uv.2)).Finite := by
  have h2 := R2Kernel_support_finite e a (2 * b + 1)
  have h3 := R3Kernel_support_finite e (2 * a + 1) b
  have hEq :
      (fun uv : ℤ × ℤ => AppellSectorKernel e a b 1 1 uv.1 uv.2) =
        fun uv : ℤ × ℤ => R2Kernel e a (2 * b + 1) uv.1 uv.2 +
          R3Kernel e (2 * a + 1) b uv.1 uv.2 := by
    funext uv
    rcases uv with ⟨U, V⟩
    exact AppellSector_odd_odd_eq e a b U V
  rw [hEq]
  exact support_add_finite h2 h3

private theorem OmegaSector_support (e a b eps eta : ℤ)
    (heps : eps = 0 ∨ eps = 1) (heta : eta = 0 ∨ eta = 1) :
    (Function.support (fun uv : ℤ × ℤ =>
      OmegaSectorKernel e a b eps eta uv.1 uv.2)).Finite := by
  have hraw := FhmBYBX_uvOmegaCoeff_support_finite e (2 * a + eps) (2 * b + eta)
  have hEq :
      (fun uv : ℤ × ℤ => OmegaSectorKernel e a b eps eta uv.1 uv.2) =
        fun uv : ℤ × ℤ =>
          FhmBYBX_uvOmegaCoeff e (2 * a + eps) (2 * b + eta) uv.1 uv.2 := by
    funext uv
    rcases uv with ⟨U, V⟩
    exact (FhmBYBX_uvOmegaCoeff_parity e a b eps eta U V heps heta).symm
  rw [hEq]
  exact hraw

private theorem R0_R1_rows_eq_uvOmega_even_even (e a b : ℤ) :
    rowRawSum MhatRow.R0 e (2 * a) (2 * b) +
      rowRawSum MhatRow.R1 e (2 * a) (2 * b) =
      ∑ᶠ u : ℤ, ∑ᶠ v : ℤ,
        FhmBYBX_uvOmegaCoeff e (2 * a) (2 * b) u v := by
  classical
  have h0 := R0Kernel_support_finite e a (2 * b)
  have h1 := R1Kernel_support_finite e (2 * a) b
  have hA := AppellSector_support_even_even e a b
  have hO := OmegaSector_support e a b 0 0 (Or.inl rfl) (Or.inl rfl)
  rw [R0_row_uv_sum, R1_row_uv_sum]
  change (∑ᶠ U : ℤ, ∑ᶠ V : ℤ, R0Kernel e a (2 * b) U V) +
      (∑ᶠ U : ℤ, ∑ᶠ V : ℤ, R1Kernel e (2 * a) b U V) = _
  rw [← finsum₂_add_distrib h0 h1]
  calc
    (∑ᶠ U : ℤ, ∑ᶠ V : ℤ,
      (R0Kernel e a (2 * b) U V + R1Kernel e (2 * a) b U V))
        = ∑ᶠ U : ℤ, ∑ᶠ V : ℤ, AppellSectorKernel e a b 0 0 U V := by
          apply finsum_congr
          intro U
          apply finsum_congr
          intro V
          exact (AppellSector_even_even_eq e a b U V).symm
    _ = ∑ᶠ U : ℤ, ∑ᶠ V : ℤ, OmegaSectorKernel e a b 0 0 U V :=
          sector_nested_sum_eq_omega e a b 0 0 hA hO
    _ = ∑ᶠ u : ℤ, ∑ᶠ v : ℤ,
          FhmBYBX_uvOmegaCoeff e (2 * a) (2 * b) u v := by
          apply finsum_congr
          intro U
          apply finsum_congr
          intro V
          simpa using
            (FhmBYBX_uvOmegaCoeff_parity e a b 0 0 U V (Or.inl rfl) (Or.inl rfl)).symm

private theorem R0_R3_rows_eq_uvOmega_even_odd (e a b : ℤ) :
    rowRawSum MhatRow.R0 e (2 * a) (2 * b + 1) +
      rowRawSum MhatRow.R3 e (2 * a) (2 * b + 1) =
      ∑ᶠ u : ℤ, ∑ᶠ v : ℤ,
        FhmBYBX_uvOmegaCoeff e (2 * a) (2 * b + 1) u v := by
  classical
  have h0 := R0Kernel_support_finite e a (2 * b + 1)
  have h3 := R3Kernel_support_finite e (2 * a) b
  have hA := AppellSector_support_even_odd e a b
  have hO := OmegaSector_support e a b 0 1 (Or.inl rfl) (Or.inr rfl)
  rw [R0_row_uv_sum, R3_row_uv_sum]
  change (∑ᶠ U : ℤ, ∑ᶠ V : ℤ, R0Kernel e a (2 * b + 1) U V) +
      (∑ᶠ U : ℤ, ∑ᶠ V : ℤ, R3Kernel e (2 * a) b U V) = _
  rw [← finsum₂_add_distrib h0 h3]
  calc
    (∑ᶠ U : ℤ, ∑ᶠ V : ℤ,
      (R0Kernel e a (2 * b + 1) U V + R3Kernel e (2 * a) b U V))
        = ∑ᶠ U : ℤ, ∑ᶠ V : ℤ, AppellSectorKernel e a b 0 1 U V := by
          apply finsum_congr
          intro U
          apply finsum_congr
          intro V
          exact (AppellSector_even_odd_eq e a b U V).symm
    _ = ∑ᶠ U : ℤ, ∑ᶠ V : ℤ, OmegaSectorKernel e a b 0 1 U V :=
          sector_nested_sum_eq_omega e a b 0 1 hA hO
    _ = ∑ᶠ u : ℤ, ∑ᶠ v : ℤ,
          FhmBYBX_uvOmegaCoeff e (2 * a) (2 * b + 1) u v := by
          apply finsum_congr
          intro U
          apply finsum_congr
          intro V
          simpa using
            (FhmBYBX_uvOmegaCoeff_parity e a b 0 1 U V (Or.inl rfl) (Or.inr rfl)).symm

private theorem R2_R1_rows_eq_uvOmega_odd_even (e a b : ℤ) :
    rowRawSum MhatRow.R2 e (2 * a + 1) (2 * b) +
      rowRawSum MhatRow.R1 e (2 * a + 1) (2 * b) =
      ∑ᶠ u : ℤ, ∑ᶠ v : ℤ,
        FhmBYBX_uvOmegaCoeff e (2 * a + 1) (2 * b) u v := by
  classical
  have h2 := R2Kernel_support_finite e a (2 * b)
  have h1 := R1Kernel_support_finite e (2 * a + 1) b
  have hA := AppellSector_support_odd_even e a b
  have hO := OmegaSector_support e a b 1 0 (Or.inr rfl) (Or.inl rfl)
  rw [R2_row_uv_sum, R1_row_uv_sum]
  change (∑ᶠ U : ℤ, ∑ᶠ V : ℤ, R2Kernel e a (2 * b) U V) +
      (∑ᶠ U : ℤ, ∑ᶠ V : ℤ, R1Kernel e (2 * a + 1) b U V) = _
  rw [← finsum₂_add_distrib h2 h1]
  calc
    (∑ᶠ U : ℤ, ∑ᶠ V : ℤ,
      (R2Kernel e a (2 * b) U V + R1Kernel e (2 * a + 1) b U V))
        = ∑ᶠ U : ℤ, ∑ᶠ V : ℤ, AppellSectorKernel e a b 1 0 U V := by
          apply finsum_congr
          intro U
          apply finsum_congr
          intro V
          exact (AppellSector_odd_even_eq e a b U V).symm
    _ = ∑ᶠ U : ℤ, ∑ᶠ V : ℤ, OmegaSectorKernel e a b 1 0 U V :=
          sector_nested_sum_eq_omega e a b 1 0 hA hO
    _ = ∑ᶠ u : ℤ, ∑ᶠ v : ℤ,
          FhmBYBX_uvOmegaCoeff e (2 * a + 1) (2 * b) u v := by
          apply finsum_congr
          intro U
          apply finsum_congr
          intro V
          simpa using
            (FhmBYBX_uvOmegaCoeff_parity e a b 1 0 U V (Or.inr rfl) (Or.inl rfl)).symm

private theorem R2_R3_rows_eq_uvOmega_odd_odd (e a b : ℤ) :
    rowRawSum MhatRow.R2 e (2 * a + 1) (2 * b + 1) +
      rowRawSum MhatRow.R3 e (2 * a + 1) (2 * b + 1) =
      ∑ᶠ u : ℤ, ∑ᶠ v : ℤ,
        FhmBYBX_uvOmegaCoeff e (2 * a + 1) (2 * b + 1) u v := by
  classical
  have h2 := R2Kernel_support_finite e a (2 * b + 1)
  have h3 := R3Kernel_support_finite e (2 * a + 1) b
  have hA := AppellSector_support_odd_odd e a b
  have hO := OmegaSector_support e a b 1 1 (Or.inr rfl) (Or.inr rfl)
  rw [R2_row_uv_sum, R3_row_uv_sum]
  change (∑ᶠ U : ℤ, ∑ᶠ V : ℤ, R2Kernel e a (2 * b + 1) U V) +
      (∑ᶠ U : ℤ, ∑ᶠ V : ℤ, R3Kernel e (2 * a + 1) b U V) = _
  rw [← finsum₂_add_distrib h2 h3]
  calc
    (∑ᶠ U : ℤ, ∑ᶠ V : ℤ,
      (R2Kernel e a (2 * b + 1) U V + R3Kernel e (2 * a + 1) b U V))
        = ∑ᶠ U : ℤ, ∑ᶠ V : ℤ, AppellSectorKernel e a b 1 1 U V := by
          apply finsum_congr
          intro U
          apply finsum_congr
          intro V
          exact (AppellSector_odd_odd_eq e a b U V).symm
    _ = ∑ᶠ U : ℤ, ∑ᶠ V : ℤ, OmegaSectorKernel e a b 1 1 U V :=
          sector_nested_sum_eq_omega e a b 1 1 hA hO
    _ = ∑ᶠ u : ℤ, ∑ᶠ v : ℤ,
          FhmBYBX_uvOmegaCoeff e (2 * a + 1) (2 * b + 1) u v := by
          apply finsum_congr
          intro U
          apply finsum_congr
          intro V
          simpa using
            (FhmBYBX_uvOmegaCoeff_parity e a b 1 1 U V (Or.inr rfl) (Or.inr rfl)).symm

private theorem row_coeff_sum_eq_rowRawSum (e x y : ℤ) :
    (∑ row : MhatRow,
      (row.lead.toMonom *
        ((mhatJThetaFamily row).hsum *
          ((mhatAppellFamilyOf mhatAppellPWO 1 row).hsum *
            (mhatDThetaFamily 1 row).hsum))).coeff (expQXY e x y)) =
      ∑ row : MhatRow, rowRawSum row e x y := by
  apply Finset.sum_congr rfl
  intro row _
  rw [coeff_Mhat_row_rawTerm]
  rfl

/-- Appell 4-row coefficient sum matches the Hecke uvOmega normal form. -/
theorem coeffQXY_Ppair_boundary_uvOmega (e x y : ℤ) :
    coeffQXY (PpairY * BX + PpairX * BY) e x y =
      ∑ᶠ u : ℤ, ∑ᶠ v : ℤ, FhmBYBX_uvOmegaCoeff e x y u v := by
  rw [coeffQXY_Ppair_boundary_row_sum]
  rw [row_coeff_sum_eq_rowRawSum]
  rcases Int.even_or_odd x with ⟨a, hx⟩ | ⟨a, hx⟩
  · rcases Int.even_or_odd y with ⟨b, hy⟩ | ⟨b, hy⟩
    · rw [hx, hy]
      rw [show a + a = 2 * a by ring, show b + b = 2 * b by ring]
      rw [show (∑ row : MhatRow, rowRawSum row e (2 * a) (2 * b)) =
          rowRawSum MhatRow.R0 e (2 * a) (2 * b) +
            rowRawSum MhatRow.R1 e (2 * a) (2 * b) by
        unfold rowRawSum
        exact Mhat_row_sum_even_even e (2 * a) (2 * b)
          ⟨a, by ring⟩ ⟨b, by ring⟩]
      exact R0_R1_rows_eq_uvOmega_even_even e a b
    · rw [hx, hy]
      rw [show a + a = 2 * a by ring]
      have hyOdd : ¬ Even (2 * b + 1) := by
        intro h
        rcases h with ⟨k, hk⟩
        omega
      rw [show (∑ row : MhatRow, rowRawSum row e (2 * a) (2 * b + 1)) =
          rowRawSum MhatRow.R0 e (2 * a) (2 * b + 1) +
            rowRawSum MhatRow.R3 e (2 * a) (2 * b + 1) by
        unfold rowRawSum
        exact Mhat_row_sum_even_odd e (2 * a) (2 * b + 1)
          ⟨a, by ring⟩ hyOdd]
      exact R0_R3_rows_eq_uvOmega_even_odd e a b
  · rcases Int.even_or_odd y with ⟨b, hy⟩ | ⟨b, hy⟩
    · rw [hx, hy]
      rw [show b + b = 2 * b by ring]
      have hxOdd : ¬ Even (2 * a + 1) := by
        intro h
        rcases h with ⟨k, hk⟩
        omega
      rw [show (∑ row : MhatRow, rowRawSum row e (2 * a + 1) (2 * b)) =
          rowRawSum MhatRow.R2 e (2 * a + 1) (2 * b) +
            rowRawSum MhatRow.R1 e (2 * a + 1) (2 * b) by
        unfold rowRawSum
        exact Mhat_row_sum_odd_even e (2 * a + 1) (2 * b)
          hxOdd ⟨b, by ring⟩]
      exact R2_R1_rows_eq_uvOmega_odd_even e a b
    · rw [hx, hy]
      have hxOdd : ¬ Even (2 * a + 1) := by
        intro h
        rcases h with ⟨k, hk⟩
        omega
      have hyOdd : ¬ Even (2 * b + 1) := by
        intro h
        rcases h with ⟨k, hk⟩
        omega
      rw [show (∑ row : MhatRow, rowRawSum row e (2 * a + 1) (2 * b + 1)) =
          rowRawSum MhatRow.R2 e (2 * a + 1) (2 * b + 1) +
            rowRawSum MhatRow.R3 e (2 * a + 1) (2 * b + 1) by
        unfold rowRawSum
        exact Mhat_row_sum_odd_odd e (2 * a + 1) (2 * b + 1)
          hxOdd hyOdd]
      exact R2_R3_rows_eq_uvOmega_odd_odd e a b

/-- The cleared identity: both sides land on the same `uvOmega` coefficient. -/
theorem cleared_identity_uvOmega :
    Fhm * BY * BX = PpairY * BX + PpairX * BY := by
  apply ext_coeffQXY
  intro e x y
  rw [coeffQXY_Fhm_BY_BX_uvOmega, coeffQXY_Ppair_boundary_uvOmega]

/-- `Fhm = Ghat 1` from the cleared identity. -/
theorem Fhm_eq_Ghat_via_uvOmega : Fhm = Ghat 1 :=
  Fhm_eq_Ghat_of_cleared cleared_identity_uvOmega

end

end QseriesFormalization.Pending.Ch10M3Ghat
