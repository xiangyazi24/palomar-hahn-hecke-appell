import QseriesFormalization.Pending.Chapter10_M3_HeckeCoeffNF
import QseriesFormalization.Pending.Chapter10_M3_AppellRawCoeff
import QseriesFormalization.Pending.Chapter10_M3_DiagClose

/-!
# Appell-side row coefficient normal forms

This file pins each surviving `Mhat` row coefficient to the common `(U,V)`
Hecke fiber coordinates.  The cancellation and final assembly live downstream.
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

private abbrev RawIdx := (ℤ × (ℤ × ℤ)) × ℤ
private abbrev SignedIdx := ((ℤ × ℤ) × ℤ) × ℤ

private theorem support_uv_of_signed_zero_finite
    {F : SignedIdx → ℚ} {K : ℤ × ℤ → ℚ}
    (hF : (Function.support F).Finite)
    (hK : ∀ U V : ℤ, K (U, V) ≠ 0 → F (((U, V), 0), 0) ≠ 0) :
    (Function.support K).Finite := by
  classical
  refine Set.Finite.subset (hF.image (fun idx : SignedIdx => idx.1.1)) ?_
  intro uv huv
  rw [Function.mem_support] at huv
  refine ⟨((uv, 0), 0), ?_, rfl⟩
  rw [Function.mem_support]
  exact hK uv.1 uv.2 huv

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

private theorem finsum_signed_curry {f : SignedIdx → ℚ}
    (hf : (Function.support f).Finite) :
    (∑ᶠ idx : SignedIdx, f idx) =
      ∑ᶠ u : ℤ, ∑ᶠ v : ℤ, ∑ᶠ dk : ℤ, ∑ᶠ dm : ℤ,
        f (((u, v), dk), dm) := by
  classical
  rw [finsum_curry _ hf]
  let g : (ℤ × ℤ) × ℤ → ℚ := fun x => ∑ᶠ dm : ℤ, f (x, dm)
  change (∑ᶠ x : (ℤ × ℤ) × ℤ, g x) = _
  have hg : (Function.support g).Finite :=
    support_finsum_prod_left_finite (f := f) hf
  rw [finsum_curry _ hg]
  let h : ℤ × ℤ → ℚ := fun uv => ∑ᶠ dk : ℤ, g (uv, dk)
  change (∑ᶠ uv : ℤ × ℤ, h uv) = _
  have hh : (Function.support h).Finite :=
    support_finsum_prod_left_finite (f := g) hg
  rw [finsum_curry _ hh]

private def signedRawEquiv (baseK baseM threshold : ℤ) : SignedIdx ≃ RawIdx where
  toFun idx :=
    let u := idx.1.1.1
    let v := idx.1.1.2
    let dk := idx.1.2
    let dm := idx.2
    (((baseK + v + dk, (u, if threshold ≤ u then v else -v)), u + baseM + dm))
  invFun idx :=
    let k := idx.1.1
    let u := idx.1.2.1
    let t := idx.1.2.2
    let m := idx.2
    let v := if threshold ≤ u then t else -t
    (((u, v), k - (baseK + v)), m - (u + baseM))
  left_inv := by
    intro idx
    rcases idx with ⟨⟨⟨u, v⟩, dk⟩, dm⟩
    by_cases h : threshold ≤ u <;> simp [h]
  right_inv := by
    intro idx
    rcases idx with ⟨⟨k, r, t⟩, m⟩
    by_cases h : threshold ≤ r <;> simp [h]

private def uvEquivR02 (a : ℤ) : SignedIdx ≃ SignedIdx where
  toFun idx :=
    let U := idx.1.1.1
    let V := idx.1.1.2
    let dk := idx.1.2
    let dm := idx.2
    (((U + V - a, a - V), dk), dm)
  invFun idx :=
    let r := idx.1.1.1
    let l := idx.1.1.2
    let dk := idx.1.2
    let dm := idx.2
    (((r + l, a - l), dk), dm)
  left_inv := by
    intro idx
    rcases idx with ⟨⟨⟨U, V⟩, dk⟩, dm⟩
    simp
  right_inv := by
    intro idx
    rcases idx with ⟨⟨⟨r, l⟩, dk⟩, dm⟩
    simp

private def uvEquivR13 (b : ℤ) : SignedIdx ≃ SignedIdx where
  toFun idx :=
    let U := idx.1.1.1
    let V := idx.1.1.2
    let dk := idx.1.2
    let dm := idx.2
    (((U - b, V + b), dk), dm)
  invFun idx :=
    let r := idx.1.1.1
    let l := idx.1.1.2
    let dk := idx.1.2
    let dm := idx.2
    (((r + b, l - b), dk), dm)
  left_inv := by
    intro idx
    rcases idx with ⟨⟨⟨U, V⟩, dk⟩, dm⟩
    simp
  right_inv := by
    intro idx
    rcases idx with ⟨⟨⟨r, l⟩, dk⟩, dm⟩
    simp

private theorem R0_signed_term_coeff (e a y r l : ℤ) :
    (mhatRawTerm 1 MhatRow.R0 (2 * a + y + l) r (if 1 ≤ r then l else -l) (r + a)).coeff
        (expQXY e (2 * a) y) =
      negOnePowIntQ (2 * a + y + (a - l)) *
        (((sg (r - 1) l : ℤ) : ℚ)) *
        (if e = heckePhi (2 * a) y (r + l) (a - l) then (1 : ℚ) else 0) := by
  rw [mhatRawTerm_coeff, R0_signed_rawExp, R0_signed_rawCoeff]
  by_cases hE : e = heckePhi (2 * a) y (r + l) (a - l)
  · rw [if_pos ⟨hE, rfl, rfl⟩, if_pos hE]
    ring
  · rw [if_neg (by intro h; exact hE h.1), if_neg hE]
    ring

private theorem R1_signed_term_coeff (e x b r l : ℤ) :
    (mhatRawTerm 1 MhatRow.R1 (x + 2 * b + l) r (if 1 ≤ r then l else -l) (r + b)).coeff
        (expQXY e x (2 * b)) =
      negOnePowIntQ (x + 2 * b + (l - b)) *
        (((sg (r - 1) l : ℤ) : ℚ)) *
        (if e = heckePhi x (2 * b) (r + b) (l - b) then (1 : ℚ) else 0) := by
  rw [mhatRawTerm_coeff, R1_signed_rawExp, R1_signed_rawCoeff]
  by_cases hE : e = heckePhi x (2 * b) (r + b) (l - b)
  · rw [if_pos ⟨hE, rfl, rfl⟩, if_pos hE]
    ring
  · rw [if_neg (by intro h; exact hE h.1), if_neg hE]
    ring

private theorem R2_signed_term_coeff (e a y r l : ℤ) :
    (mhatRawTerm 1 MhatRow.R2 (2 * a + 1 + y + l) r (if 1 ≤ r then l else -l) (r + a)).coeff
        (expQXY e (2 * a + 1) y) =
      negOnePowIntQ (2 * a + 1 + y + (a - l)) *
        (((sg (r - 1) l : ℤ) : ℚ)) *
        (if e = heckePhi (2 * a + 1) y (r + l) (a - l) then (1 : ℚ) else 0) := by
  rw [mhatRawTerm_coeff, R2_signed_rawExp, R2_signed_rawCoeff]
  by_cases hE : e = heckePhi (2 * a + 1) y (r + l) (a - l)
  · rw [if_pos ⟨hE, rfl, rfl⟩, if_pos hE]
    ring
  · rw [if_neg (by intro h; exact hE h.1), if_neg hE]
    ring

private theorem R3_signed_term_coeff (e x b r l : ℤ) :
    (mhatRawTerm 1 MhatRow.R3 (x + 2 * b + 1 + l) r (if 2 ≤ r then l else -l) (r + b)).coeff
        (expQXY e x (2 * b + 1)) =
      negOnePowIntQ (x + 2 * b + 1 + (l - b)) *
        (((sg (r - 2) l : ℤ) : ℚ)) *
        (if e = heckePhi x (2 * b + 1) (r + b) (l - b) then (1 : ℚ) else 0) := by
  rw [mhatRawTerm_coeff, R3_signed_rawExp, R3_signed_rawCoeff]
  by_cases hE : e = heckePhi x (2 * b + 1) (r + b) (l - b)
  · rw [if_pos ⟨hE, rfl, rfl⟩, if_pos hE]
    ring
  · rw [if_neg (by intro h; exact hE h.1), if_neg hE]
    ring

def rowRawSum (row : MhatRow) (e x y : ℤ) : ℚ :=
  ∑ᶠ idx : RawIdx,
    (mhatRawTerm 1 row idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff (expQXY e x y)

private theorem R0_uv_dm_coeff_zero (e a y U V dk dm : ℤ) (hdm : dm ≠ 0) :
    (mhatRawTerm 1 MhatRow.R0 (2 * a + y + (a - V) + dk) (U + V - a)
        (if 1 ≤ U + V - a then a - V else -(a - V)) (U + V - a + a + dm)).coeff
        (expQXY e (2 * a) y) = 0 := by
  rw [mhatRawTerm_coeff]
  rw [if_neg]
  intro h
  rcases h with ⟨_, hx, _⟩
  rw [rawExp_R0_cX] at hx
  omega

private theorem R0_uv_dk_coeff_zero (e a y U V dk : ℤ) (hdk : dk ≠ 0) :
    (mhatRawTerm 1 MhatRow.R0 (2 * a + y + (a - V) + dk) (U + V - a)
        (if 1 ≤ U + V - a then a - V else -(a - V)) (U + V - a + a)).coeff
        (expQXY e (2 * a) y) = 0 := by
  rw [mhatRawTerm_coeff]
  rw [if_neg]
  intro h
  rcases h with ⟨_, _, hy⟩
  rw [rawExp_R0_cY] at hy
  by_cases hr : 1 ≤ U + V - a
  · have hp : (mhatDenomExp 1 MhatRow.R0 (U + V - a)).lexPositive :=
      (R0_lexPositive_iff (U + V - a)).2 hr
    simp [hp, hr] at hy
    omega
  · have hp : ¬ (mhatDenomExp 1 MhatRow.R0 (U + V - a)).lexPositive :=
      mt (R0_lexPositive_iff (U + V - a)).1 hr
    simp [hp, hr] at hy
    omega

theorem R0_row_uv_sum (e a y : ℤ) :
    rowRawSum MhatRow.R0 e (2 * a) y =
      ∑ᶠ U : ℤ, ∑ᶠ V : ℤ,
        negOnePowIntQ (2 * a + y + V) *
          (((sg (U + V - a - 1) (a - V) : ℤ) : ℚ)) *
          (if e = heckePhi (2 * a) y U V then (1 : ℚ) else 0) := by
  classical
  let E : SignedIdx ≃ RawIdx := (uvEquivR02 a).trans (signedRawEquiv (2 * a + y) a 1)
  have hfraw : (Function.support (fun idx : RawIdx =>
      (mhatRawTerm 1 MhatRow.R0 idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
        (expQXY e (2 * a) y))).Finite :=
    mhatRawTerm_coeff_support_finite MhatRow.R0 e (2 * a) y
  have hfsigned : (Function.support (fun idx : SignedIdx =>
      (mhatRawTerm 1 MhatRow.R0 (E idx).1.1 (E idx).1.2.1 (E idx).1.2.2 (E idx).2).coeff
        (expQXY e (2 * a) y))).Finite :=
    hfraw.preimage (Set.injOn_of_injective (Equiv.injective E))
  calc
    rowRawSum MhatRow.R0 e (2 * a) y
        = ∑ᶠ idx : RawIdx,
            (mhatRawTerm 1 MhatRow.R0 idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
              (expQXY e (2 * a) y) := rfl
    _ = ∑ᶠ idx : SignedIdx,
            (mhatRawTerm 1 MhatRow.R0 (E idx).1.1 (E idx).1.2.1 (E idx).1.2.2 (E idx).2).coeff
              (expQXY e (2 * a) y) := (finsum_comp_equiv E).symm
    _ = ∑ᶠ U : ℤ, ∑ᶠ V : ℤ, ∑ᶠ dk : ℤ, ∑ᶠ dm : ℤ,
            (mhatRawTerm 1 MhatRow.R0 (E (((U, V), dk), dm)).1.1
              (E (((U, V), dk), dm)).1.2.1
              (E (((U, V), dk), dm)).1.2.2
              (E (((U, V), dk), dm)).2).coeff (expQXY e (2 * a) y) := by
          exact finsum_signed_curry hfsigned
    _ = ∑ᶠ U : ℤ, ∑ᶠ V : ℤ,
        negOnePowIntQ (2 * a + y + V) *
          (((sg (U + V - a - 1) (a - V) : ℤ) : ℚ)) *
          (if e = heckePhi (2 * a) y U V then (1 : ℚ) else 0) := by
          apply finsum_congr
          intro U
          apply finsum_congr
          intro V
          dsimp [E, uvEquivR02, signedRawEquiv]
          change (∑ᶠ dk : ℤ, ∑ᶠ dm : ℤ,
              (mhatRawTerm 1 MhatRow.R0 (2 * a + y + (a - V) + dk) (U + V - a)
                (if 1 ≤ U + V - a then a - V else -(a - V)) (U + V - a + a + dm)).coeff
                (expQXY e (2 * a) y)) =
            negOnePowIntQ (2 * a + y + V) *
              (((sg (U + V - a - 1) (a - V) : ℤ) : ℚ)) *
              (if e = heckePhi (2 * a) y U V then (1 : ℚ) else 0)
          calc
            (∑ᶠ dk : ℤ, ∑ᶠ dm : ℤ,
              (mhatRawTerm 1 MhatRow.R0 (2 * a + y + (a - V) + dk) (U + V - a)
                (if 1 ≤ U + V - a then a - V else -(a - V)) (U + V - a + a + dm)).coeff
                (expQXY e (2 * a) y))
                = ∑ᶠ dk : ℤ,
                    (mhatRawTerm 1 MhatRow.R0 (2 * a + y + (a - V) + dk) (U + V - a)
                      (if 1 ≤ U + V - a then a - V else -(a - V)) (U + V - a + a)).coeff
                      (expQXY e (2 * a) y) := by
                    apply finsum_congr
                    intro dk
                    rw [finsum_eq_single _ 0]
                    · ring
                    · intro dm hdm
                      exact R0_uv_dm_coeff_zero e a y U V dk dm hdm
            _ = (mhatRawTerm 1 MhatRow.R0 (2 * a + y + (a - V)) (U + V - a)
                      (if 1 ≤ U + V - a then a - V else -(a - V)) (U + V - a + a)).coeff
                      (expQXY e (2 * a) y) := by
                    rw [finsum_eq_single _ 0]
                    · ring
                    · intro dk hdk
                      exact R0_uv_dk_coeff_zero e a y U V dk hdk
            _ = negOnePowIntQ (2 * a + y + V) *
              (((sg (U + V - a - 1) (a - V) : ℤ) : ℚ)) *
              (if e = heckePhi (2 * a) y U V then (1 : ℚ) else 0) := by
                    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
                      R0_signed_term_coeff e a y (U + V - a) (a - V)

theorem R0_uv_kernel_support_finite (e a y : ℤ) :
    (Function.support (fun uv : ℤ × ℤ =>
      negOnePowIntQ (2 * a + y + uv.2) *
        (((sg (uv.1 + uv.2 - a - 1) (a - uv.2) : ℤ) : ℚ)) *
        (if e = heckePhi (2 * a) y uv.1 uv.2 then (1 : ℚ) else 0))).Finite := by
  classical
  let E : SignedIdx ≃ RawIdx := (uvEquivR02 a).trans (signedRawEquiv (2 * a + y) a 1)
  have hfraw : (Function.support (fun idx : RawIdx =>
      (mhatRawTerm 1 MhatRow.R0 idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
        (expQXY e (2 * a) y))).Finite :=
    mhatRawTerm_coeff_support_finite MhatRow.R0 e (2 * a) y
  have hfsigned : (Function.support (fun idx : SignedIdx =>
      (mhatRawTerm 1 MhatRow.R0 (E idx).1.1 (E idx).1.2.1 (E idx).1.2.2 (E idx).2).coeff
        (expQXY e (2 * a) y))).Finite :=
    hfraw.preimage (Set.injOn_of_injective (Equiv.injective E))
  refine support_uv_of_signed_zero_finite
    (F := fun idx : SignedIdx =>
      (mhatRawTerm 1 MhatRow.R0 (E idx).1.1 (E idx).1.2.1 (E idx).1.2.2 (E idx).2).coeff
        (expQXY e (2 * a) y))
    (K := fun uv : ℤ × ℤ =>
      negOnePowIntQ (2 * a + y + uv.2) *
        (((sg (uv.1 + uv.2 - a - 1) (a - uv.2) : ℤ) : ℚ)) *
        (if e = heckePhi (2 * a) y uv.1 uv.2 then (1 : ℚ) else 0))
    hfsigned ?_
  intro U V hK
  dsimp [E, uvEquivR02, signedRawEquiv]
  have hbase :
      (mhatRawTerm 1 MhatRow.R0 (2 * a + y + (a - V)) (U + V - a)
          (if 1 ≤ U + V - a then a - V else -(a - V)) (U + V - a + a)).coeff
          (expQXY e (2 * a) y) ≠ 0 := by
    rw [R0_signed_term_coeff]
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hK
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hbase

private theorem R1_uv_dm_coeff_zero (e x b U V dk dm : ℤ) (hdm : dm ≠ 0) :
    (mhatRawTerm 1 MhatRow.R1 (x + 2 * b + (V + b) + dk) (U - b)
        (if 1 ≤ U - b then V + b else -(V + b)) (U - b + b + dm)).coeff
        (expQXY e x (2 * b)) = 0 := by
  rw [mhatRawTerm_coeff]
  rw [if_neg]
  intro h
  rcases h with ⟨_, _, hy⟩
  rw [rawExp_R1_cY] at hy
  omega

private theorem R1_uv_dk_coeff_zero (e x b U V dk : ℤ) (hdk : dk ≠ 0) :
    (mhatRawTerm 1 MhatRow.R1 (x + 2 * b + (V + b) + dk) (U - b)
        (if 1 ≤ U - b then V + b else -(V + b)) (U - b + b)).coeff
        (expQXY e x (2 * b)) = 0 := by
  rw [mhatRawTerm_coeff]
  rw [if_neg]
  intro h
  rcases h with ⟨_, hx, _⟩
  have hraw := R1_signed_rawExp (x + dk) b (U - b) (V + b)
  have hk : x + dk + 2 * b + (V + b) = x + 2 * b + (V + b) + dk := by ring
  rw [hk] at hraw
  rw [hraw] at hx
  simp at hx
  omega

theorem R1_row_uv_sum (e x b : ℤ) :
    rowRawSum MhatRow.R1 e x (2 * b) =
      ∑ᶠ U : ℤ, ∑ᶠ V : ℤ,
        negOnePowIntQ (x + 2 * b + V) *
          (((sg (U - b - 1) (V + b) : ℤ) : ℚ)) *
          (if e = heckePhi x (2 * b) U V then (1 : ℚ) else 0) := by
  classical
  let E : SignedIdx ≃ RawIdx := (uvEquivR13 b).trans (signedRawEquiv (x + 2 * b) b 1)
  have hfraw : (Function.support (fun idx : RawIdx =>
      (mhatRawTerm 1 MhatRow.R1 idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
        (expQXY e x (2 * b)))).Finite :=
    mhatRawTerm_coeff_support_finite MhatRow.R1 e x (2 * b)
  have hfsigned : (Function.support (fun idx : SignedIdx =>
      (mhatRawTerm 1 MhatRow.R1 (E idx).1.1 (E idx).1.2.1 (E idx).1.2.2 (E idx).2).coeff
        (expQXY e x (2 * b)))).Finite :=
    hfraw.preimage (Set.injOn_of_injective (Equiv.injective E))
  calc
    rowRawSum MhatRow.R1 e x (2 * b)
        = ∑ᶠ idx : RawIdx,
            (mhatRawTerm 1 MhatRow.R1 idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
              (expQXY e x (2 * b)) := rfl
    _ = ∑ᶠ idx : SignedIdx,
            (mhatRawTerm 1 MhatRow.R1 (E idx).1.1 (E idx).1.2.1 (E idx).1.2.2 (E idx).2).coeff
              (expQXY e x (2 * b)) := (finsum_comp_equiv E).symm
    _ = ∑ᶠ U : ℤ, ∑ᶠ V : ℤ, ∑ᶠ dk : ℤ, ∑ᶠ dm : ℤ,
            (mhatRawTerm 1 MhatRow.R1 (E (((U, V), dk), dm)).1.1
              (E (((U, V), dk), dm)).1.2.1
              (E (((U, V), dk), dm)).1.2.2
              (E (((U, V), dk), dm)).2).coeff (expQXY e x (2 * b)) := by
          exact finsum_signed_curry hfsigned
    _ = ∑ᶠ U : ℤ, ∑ᶠ V : ℤ,
        negOnePowIntQ (x + 2 * b + V) *
          (((sg (U - b - 1) (V + b) : ℤ) : ℚ)) *
          (if e = heckePhi x (2 * b) U V then (1 : ℚ) else 0) := by
          apply finsum_congr
          intro U
          apply finsum_congr
          intro V
          dsimp [E, uvEquivR13, signedRawEquiv]
          change (∑ᶠ dk : ℤ, ∑ᶠ dm : ℤ,
              (mhatRawTerm 1 MhatRow.R1 (x + 2 * b + (V + b) + dk) (U - b)
                (if 1 ≤ U - b then V + b else -(V + b)) (U - b + b + dm)).coeff
                (expQXY e x (2 * b))) =
            negOnePowIntQ (x + 2 * b + V) *
              (((sg (U - b - 1) (V + b) : ℤ) : ℚ)) *
              (if e = heckePhi x (2 * b) U V then (1 : ℚ) else 0)
          calc
            (∑ᶠ dk : ℤ, ∑ᶠ dm : ℤ,
              (mhatRawTerm 1 MhatRow.R1 (x + 2 * b + (V + b) + dk) (U - b)
                (if 1 ≤ U - b then V + b else -(V + b)) (U - b + b + dm)).coeff
                (expQXY e x (2 * b)))
                = ∑ᶠ dk : ℤ,
                    (mhatRawTerm 1 MhatRow.R1 (x + 2 * b + (V + b) + dk) (U - b)
                      (if 1 ≤ U - b then V + b else -(V + b)) (U - b + b)).coeff
                      (expQXY e x (2 * b)) := by
                    apply finsum_congr
                    intro dk
                    rw [finsum_eq_single _ 0]
                    · ring
                    · intro dm hdm
                      exact R1_uv_dm_coeff_zero e x b U V dk dm hdm
            _ = (mhatRawTerm 1 MhatRow.R1 (x + 2 * b + (V + b)) (U - b)
                      (if 1 ≤ U - b then V + b else -(V + b)) (U - b + b)).coeff
                      (expQXY e x (2 * b)) := by
                    rw [finsum_eq_single _ 0]
                    · ring
                    · intro dk hdk
                      exact R1_uv_dk_coeff_zero e x b U V dk hdk
            _ = negOnePowIntQ (x + 2 * b + V) *
              (((sg (U - b - 1) (V + b) : ℤ) : ℚ)) *
              (if e = heckePhi x (2 * b) U V then (1 : ℚ) else 0) := by
                    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
                      R1_signed_term_coeff e x b (U - b) (V + b)

theorem R1_uv_kernel_support_finite (e x b : ℤ) :
    (Function.support (fun uv : ℤ × ℤ =>
      negOnePowIntQ (x + 2 * b + uv.2) *
        (((sg (uv.1 - b - 1) (uv.2 + b) : ℤ) : ℚ)) *
        (if e = heckePhi x (2 * b) uv.1 uv.2 then (1 : ℚ) else 0))).Finite := by
  classical
  let E : SignedIdx ≃ RawIdx := (uvEquivR13 b).trans (signedRawEquiv (x + 2 * b) b 1)
  have hfraw : (Function.support (fun idx : RawIdx =>
      (mhatRawTerm 1 MhatRow.R1 idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
        (expQXY e x (2 * b)))).Finite :=
    mhatRawTerm_coeff_support_finite MhatRow.R1 e x (2 * b)
  have hfsigned : (Function.support (fun idx : SignedIdx =>
      (mhatRawTerm 1 MhatRow.R1 (E idx).1.1 (E idx).1.2.1 (E idx).1.2.2 (E idx).2).coeff
        (expQXY e x (2 * b)))).Finite :=
    hfraw.preimage (Set.injOn_of_injective (Equiv.injective E))
  refine support_uv_of_signed_zero_finite
    (F := fun idx : SignedIdx =>
      (mhatRawTerm 1 MhatRow.R1 (E idx).1.1 (E idx).1.2.1 (E idx).1.2.2 (E idx).2).coeff
        (expQXY e x (2 * b)))
    (K := fun uv : ℤ × ℤ =>
      negOnePowIntQ (x + 2 * b + uv.2) *
        (((sg (uv.1 - b - 1) (uv.2 + b) : ℤ) : ℚ)) *
        (if e = heckePhi x (2 * b) uv.1 uv.2 then (1 : ℚ) else 0))
    hfsigned ?_
  intro U V hK
  dsimp [E, uvEquivR13, signedRawEquiv]
  have hbase :
      (mhatRawTerm 1 MhatRow.R1 (x + 2 * b + (V + b)) (U - b)
          (if 1 ≤ U - b then V + b else -(V + b)) (U - b + b)).coeff
          (expQXY e x (2 * b)) ≠ 0 := by
    rw [R1_signed_term_coeff]
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hK
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hbase

private theorem R2_uv_dm_coeff_zero (e a y U V dk dm : ℤ) (hdm : dm ≠ 0) :
    (mhatRawTerm 1 MhatRow.R2 (2 * a + 1 + y + (a - V) + dk) (U + V - a)
        (if 1 ≤ U + V - a then a - V else -(a - V)) (U + V - a + a + dm)).coeff
        (expQXY e (2 * a + 1) y) = 0 := by
  rw [mhatRawTerm_coeff]
  rw [if_neg]
  intro h
  rcases h with ⟨_, hx, _⟩
  rw [rawExp_R2_cX] at hx
  omega

private theorem R2_uv_dk_coeff_zero (e a y U V dk : ℤ) (hdk : dk ≠ 0) :
    (mhatRawTerm 1 MhatRow.R2 (2 * a + 1 + y + (a - V) + dk) (U + V - a)
        (if 1 ≤ U + V - a then a - V else -(a - V)) (U + V - a + a)).coeff
        (expQXY e (2 * a + 1) y) = 0 := by
  rw [mhatRawTerm_coeff]
  rw [if_neg]
  intro h
  rcases h with ⟨_, _, hy⟩
  have hraw := R2_signed_rawExp a (y + dk) (U + V - a) (a - V)
  have hk : 2 * a + 1 + (y + dk) + (a - V) = 2 * a + 1 + y + (a - V) + dk := by ring
  rw [hk] at hraw
  rw [hraw] at hy
  simp at hy
  omega

theorem R2_row_uv_sum (e a y : ℤ) :
    rowRawSum MhatRow.R2 e (2 * a + 1) y =
      ∑ᶠ U : ℤ, ∑ᶠ V : ℤ,
        negOnePowIntQ (2 * a + 1 + y + V) *
          (((sg (U + V - a - 1) (a - V) : ℤ) : ℚ)) *
          (if e = heckePhi (2 * a + 1) y U V then (1 : ℚ) else 0) := by
  classical
  let E : SignedIdx ≃ RawIdx := (uvEquivR02 a).trans (signedRawEquiv (2 * a + 1 + y) a 1)
  have hfraw : (Function.support (fun idx : RawIdx =>
      (mhatRawTerm 1 MhatRow.R2 idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
        (expQXY e (2 * a + 1) y))).Finite :=
    mhatRawTerm_coeff_support_finite MhatRow.R2 e (2 * a + 1) y
  have hfsigned : (Function.support (fun idx : SignedIdx =>
      (mhatRawTerm 1 MhatRow.R2 (E idx).1.1 (E idx).1.2.1 (E idx).1.2.2 (E idx).2).coeff
        (expQXY e (2 * a + 1) y))).Finite :=
    hfraw.preimage (Set.injOn_of_injective (Equiv.injective E))
  calc
    rowRawSum MhatRow.R2 e (2 * a + 1) y
        = ∑ᶠ idx : RawIdx,
            (mhatRawTerm 1 MhatRow.R2 idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
              (expQXY e (2 * a + 1) y) := rfl
    _ = ∑ᶠ idx : SignedIdx,
            (mhatRawTerm 1 MhatRow.R2 (E idx).1.1 (E idx).1.2.1 (E idx).1.2.2 (E idx).2).coeff
              (expQXY e (2 * a + 1) y) := (finsum_comp_equiv E).symm
    _ = ∑ᶠ U : ℤ, ∑ᶠ V : ℤ, ∑ᶠ dk : ℤ, ∑ᶠ dm : ℤ,
            (mhatRawTerm 1 MhatRow.R2 (E (((U, V), dk), dm)).1.1
              (E (((U, V), dk), dm)).1.2.1
              (E (((U, V), dk), dm)).1.2.2
              (E (((U, V), dk), dm)).2).coeff (expQXY e (2 * a + 1) y) := by
          exact finsum_signed_curry hfsigned
    _ = ∑ᶠ U : ℤ, ∑ᶠ V : ℤ,
        negOnePowIntQ (2 * a + 1 + y + V) *
          (((sg (U + V - a - 1) (a - V) : ℤ) : ℚ)) *
          (if e = heckePhi (2 * a + 1) y U V then (1 : ℚ) else 0) := by
          apply finsum_congr
          intro U
          apply finsum_congr
          intro V
          dsimp [E, uvEquivR02, signedRawEquiv]
          change (∑ᶠ dk : ℤ, ∑ᶠ dm : ℤ,
              (mhatRawTerm 1 MhatRow.R2 (2 * a + 1 + y + (a - V) + dk) (U + V - a)
                (if 1 ≤ U + V - a then a - V else -(a - V)) (U + V - a + a + dm)).coeff
                (expQXY e (2 * a + 1) y)) =
            negOnePowIntQ (2 * a + 1 + y + V) *
              (((sg (U + V - a - 1) (a - V) : ℤ) : ℚ)) *
              (if e = heckePhi (2 * a + 1) y U V then (1 : ℚ) else 0)
          calc
            (∑ᶠ dk : ℤ, ∑ᶠ dm : ℤ,
              (mhatRawTerm 1 MhatRow.R2 (2 * a + 1 + y + (a - V) + dk) (U + V - a)
                (if 1 ≤ U + V - a then a - V else -(a - V)) (U + V - a + a + dm)).coeff
                (expQXY e (2 * a + 1) y))
                = ∑ᶠ dk : ℤ,
                    (mhatRawTerm 1 MhatRow.R2 (2 * a + 1 + y + (a - V) + dk) (U + V - a)
                      (if 1 ≤ U + V - a then a - V else -(a - V)) (U + V - a + a)).coeff
                      (expQXY e (2 * a + 1) y) := by
                    apply finsum_congr
                    intro dk
                    rw [finsum_eq_single _ 0]
                    · ring
                    · intro dm hdm
                      exact R2_uv_dm_coeff_zero e a y U V dk dm hdm
            _ = (mhatRawTerm 1 MhatRow.R2 (2 * a + 1 + y + (a - V)) (U + V - a)
                      (if 1 ≤ U + V - a then a - V else -(a - V)) (U + V - a + a)).coeff
                      (expQXY e (2 * a + 1) y) := by
                    rw [finsum_eq_single _ 0]
                    · ring
                    · intro dk hdk
                      exact R2_uv_dk_coeff_zero e a y U V dk hdk
            _ = negOnePowIntQ (2 * a + 1 + y + V) *
              (((sg (U + V - a - 1) (a - V) : ℤ) : ℚ)) *
              (if e = heckePhi (2 * a + 1) y U V then (1 : ℚ) else 0) := by
                    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
                      R2_signed_term_coeff e a y (U + V - a) (a - V)

theorem R2_uv_kernel_support_finite (e a y : ℤ) :
    (Function.support (fun uv : ℤ × ℤ =>
      negOnePowIntQ (2 * a + 1 + y + uv.2) *
        (((sg (uv.1 + uv.2 - a - 1) (a - uv.2) : ℤ) : ℚ)) *
        (if e = heckePhi (2 * a + 1) y uv.1 uv.2 then (1 : ℚ) else 0))).Finite := by
  classical
  let E : SignedIdx ≃ RawIdx := (uvEquivR02 a).trans (signedRawEquiv (2 * a + 1 + y) a 1)
  have hfraw : (Function.support (fun idx : RawIdx =>
      (mhatRawTerm 1 MhatRow.R2 idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
        (expQXY e (2 * a + 1) y))).Finite :=
    mhatRawTerm_coeff_support_finite MhatRow.R2 e (2 * a + 1) y
  have hfsigned : (Function.support (fun idx : SignedIdx =>
      (mhatRawTerm 1 MhatRow.R2 (E idx).1.1 (E idx).1.2.1 (E idx).1.2.2 (E idx).2).coeff
        (expQXY e (2 * a + 1) y))).Finite :=
    hfraw.preimage (Set.injOn_of_injective (Equiv.injective E))
  refine support_uv_of_signed_zero_finite
    (F := fun idx : SignedIdx =>
      (mhatRawTerm 1 MhatRow.R2 (E idx).1.1 (E idx).1.2.1 (E idx).1.2.2 (E idx).2).coeff
        (expQXY e (2 * a + 1) y))
    (K := fun uv : ℤ × ℤ =>
      negOnePowIntQ (2 * a + 1 + y + uv.2) *
        (((sg (uv.1 + uv.2 - a - 1) (a - uv.2) : ℤ) : ℚ)) *
        (if e = heckePhi (2 * a + 1) y uv.1 uv.2 then (1 : ℚ) else 0))
    hfsigned ?_
  intro U V hK
  dsimp [E, uvEquivR02, signedRawEquiv]
  have hbase :
      (mhatRawTerm 1 MhatRow.R2 (2 * a + 1 + y + (a - V)) (U + V - a)
          (if 1 ≤ U + V - a then a - V else -(a - V)) (U + V - a + a)).coeff
          (expQXY e (2 * a + 1) y) ≠ 0 := by
    rw [R2_signed_term_coeff]
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hK
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hbase

private theorem R3_uv_dm_coeff_zero (e x b U V dk dm : ℤ) (hdm : dm ≠ 0) :
    (mhatRawTerm 1 MhatRow.R3 (x + 2 * b + 1 + (V + b) + dk) (U - b)
        (if 2 ≤ U - b then V + b else -(V + b)) (U - b + b + dm)).coeff
        (expQXY e x (2 * b + 1)) = 0 := by
  rw [mhatRawTerm_coeff]
  rw [if_neg]
  intro h
  rcases h with ⟨_, _, hy⟩
  rw [rawExp_R3_cY] at hy
  omega

private theorem R3_uv_dk_coeff_zero (e x b U V dk : ℤ) (hdk : dk ≠ 0) :
    (mhatRawTerm 1 MhatRow.R3 (x + 2 * b + 1 + (V + b) + dk) (U - b)
        (if 2 ≤ U - b then V + b else -(V + b)) (U - b + b)).coeff
        (expQXY e x (2 * b + 1)) = 0 := by
  rw [mhatRawTerm_coeff]
  rw [if_neg]
  intro h
  rcases h with ⟨_, hx, _⟩
  have hraw := R3_signed_rawExp (x + dk) b (U - b) (V + b)
  have hk : x + dk + 2 * b + 1 + (V + b) = x + 2 * b + 1 + (V + b) + dk := by ring
  rw [hk] at hraw
  rw [hraw] at hx
  simp at hx
  omega

theorem R3_row_uv_sum (e x b : ℤ) :
    rowRawSum MhatRow.R3 e x (2 * b + 1) =
      ∑ᶠ U : ℤ, ∑ᶠ V : ℤ,
        negOnePowIntQ (x + 2 * b + 1 + V) *
          (((sg (U - b - 2) (V + b) : ℤ) : ℚ)) *
          (if e = heckePhi x (2 * b + 1) U V then (1 : ℚ) else 0) := by
  classical
  let E : SignedIdx ≃ RawIdx := (uvEquivR13 b).trans (signedRawEquiv (x + 2 * b + 1) b 2)
  have hfraw : (Function.support (fun idx : RawIdx =>
      (mhatRawTerm 1 MhatRow.R3 idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
        (expQXY e x (2 * b + 1)))).Finite :=
    mhatRawTerm_coeff_support_finite MhatRow.R3 e x (2 * b + 1)
  have hfsigned : (Function.support (fun idx : SignedIdx =>
      (mhatRawTerm 1 MhatRow.R3 (E idx).1.1 (E idx).1.2.1 (E idx).1.2.2 (E idx).2).coeff
        (expQXY e x (2 * b + 1)))).Finite :=
    hfraw.preimage (Set.injOn_of_injective (Equiv.injective E))
  calc
    rowRawSum MhatRow.R3 e x (2 * b + 1)
        = ∑ᶠ idx : RawIdx,
            (mhatRawTerm 1 MhatRow.R3 idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
              (expQXY e x (2 * b + 1)) := rfl
    _ = ∑ᶠ idx : SignedIdx,
            (mhatRawTerm 1 MhatRow.R3 (E idx).1.1 (E idx).1.2.1 (E idx).1.2.2 (E idx).2).coeff
              (expQXY e x (2 * b + 1)) := (finsum_comp_equiv E).symm
    _ = ∑ᶠ U : ℤ, ∑ᶠ V : ℤ, ∑ᶠ dk : ℤ, ∑ᶠ dm : ℤ,
            (mhatRawTerm 1 MhatRow.R3 (E (((U, V), dk), dm)).1.1
              (E (((U, V), dk), dm)).1.2.1
              (E (((U, V), dk), dm)).1.2.2
              (E (((U, V), dk), dm)).2).coeff (expQXY e x (2 * b + 1)) := by
          exact finsum_signed_curry hfsigned
    _ = ∑ᶠ U : ℤ, ∑ᶠ V : ℤ,
        negOnePowIntQ (x + 2 * b + 1 + V) *
          (((sg (U - b - 2) (V + b) : ℤ) : ℚ)) *
          (if e = heckePhi x (2 * b + 1) U V then (1 : ℚ) else 0) := by
          apply finsum_congr
          intro U
          apply finsum_congr
          intro V
          dsimp [E, uvEquivR13, signedRawEquiv]
          change (∑ᶠ dk : ℤ, ∑ᶠ dm : ℤ,
              (mhatRawTerm 1 MhatRow.R3 (x + 2 * b + 1 + (V + b) + dk) (U - b)
                (if 2 ≤ U - b then V + b else -(V + b)) (U - b + b + dm)).coeff
                (expQXY e x (2 * b + 1))) =
            negOnePowIntQ (x + 2 * b + 1 + V) *
              (((sg (U - b - 2) (V + b) : ℤ) : ℚ)) *
              (if e = heckePhi x (2 * b + 1) U V then (1 : ℚ) else 0)
          calc
            (∑ᶠ dk : ℤ, ∑ᶠ dm : ℤ,
              (mhatRawTerm 1 MhatRow.R3 (x + 2 * b + 1 + (V + b) + dk) (U - b)
                (if 2 ≤ U - b then V + b else -(V + b)) (U - b + b + dm)).coeff
                (expQXY e x (2 * b + 1)))
                = ∑ᶠ dk : ℤ,
                    (mhatRawTerm 1 MhatRow.R3 (x + 2 * b + 1 + (V + b) + dk) (U - b)
                      (if 2 ≤ U - b then V + b else -(V + b)) (U - b + b)).coeff
                      (expQXY e x (2 * b + 1)) := by
                    apply finsum_congr
                    intro dk
                    rw [finsum_eq_single _ 0]
                    · ring
                    · intro dm hdm
                      exact R3_uv_dm_coeff_zero e x b U V dk dm hdm
            _ = (mhatRawTerm 1 MhatRow.R3 (x + 2 * b + 1 + (V + b)) (U - b)
                      (if 2 ≤ U - b then V + b else -(V + b)) (U - b + b)).coeff
                      (expQXY e x (2 * b + 1)) := by
                    rw [finsum_eq_single _ 0]
                    · ring
                    · intro dk hdk
                      exact R3_uv_dk_coeff_zero e x b U V dk hdk
            _ = negOnePowIntQ (x + 2 * b + 1 + V) *
              (((sg (U - b - 2) (V + b) : ℤ) : ℚ)) *
              (if e = heckePhi x (2 * b + 1) U V then (1 : ℚ) else 0) := by
                    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
                      R3_signed_term_coeff e x b (U - b) (V + b)

theorem R3_uv_kernel_support_finite (e x b : ℤ) :
    (Function.support (fun uv : ℤ × ℤ =>
      negOnePowIntQ (x + 2 * b + 1 + uv.2) *
        (((sg (uv.1 - b - 2) (uv.2 + b) : ℤ) : ℚ)) *
        (if e = heckePhi x (2 * b + 1) uv.1 uv.2 then (1 : ℚ) else 0))).Finite := by
  classical
  let E : SignedIdx ≃ RawIdx := (uvEquivR13 b).trans (signedRawEquiv (x + 2 * b + 1) b 2)
  have hfraw : (Function.support (fun idx : RawIdx =>
      (mhatRawTerm 1 MhatRow.R3 idx.1.1 idx.1.2.1 idx.1.2.2 idx.2).coeff
        (expQXY e x (2 * b + 1)))).Finite :=
    mhatRawTerm_coeff_support_finite MhatRow.R3 e x (2 * b + 1)
  have hfsigned : (Function.support (fun idx : SignedIdx =>
      (mhatRawTerm 1 MhatRow.R3 (E idx).1.1 (E idx).1.2.1 (E idx).1.2.2 (E idx).2).coeff
        (expQXY e x (2 * b + 1)))).Finite :=
    hfraw.preimage (Set.injOn_of_injective (Equiv.injective E))
  refine support_uv_of_signed_zero_finite
    (F := fun idx : SignedIdx =>
      (mhatRawTerm 1 MhatRow.R3 (E idx).1.1 (E idx).1.2.1 (E idx).1.2.2 (E idx).2).coeff
        (expQXY e x (2 * b + 1)))
    (K := fun uv : ℤ × ℤ =>
      negOnePowIntQ (x + 2 * b + 1 + uv.2) *
        (((sg (uv.1 - b - 2) (uv.2 + b) : ℤ) : ℚ)) *
        (if e = heckePhi x (2 * b + 1) uv.1 uv.2 then (1 : ℚ) else 0))
    hfsigned ?_
  intro U V hK
  dsimp [E, uvEquivR13, signedRawEquiv]
  have hbase :
      (mhatRawTerm 1 MhatRow.R3 (x + 2 * b + 1 + (V + b)) (U - b)
          (if 2 ≤ U - b then V + b else -(V + b)) (U - b + b)).coeff
          (expQXY e x (2 * b + 1)) ≠ 0 := by
    rw [R3_signed_term_coeff]
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hK
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hbase

end

end QseriesFormalization.Pending.Ch10M3Ghat
