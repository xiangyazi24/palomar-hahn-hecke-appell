import QseriesFormalization.Chapter04_FranklinPentagonal
import Mathlib.Tactic.Linarith

/-!
# Franklin Involution → Euler Pentagonal Number Theorem (Combinatorial)

The final assembly: use the Franklin involution (Ch04Franklin infrastructure) to prove
the combinatorial form of Euler's pentagonal number theorem.

## Strategy

A strict partition of n is a subset S ⊆ {1,...,n} with ∑ S = n.
The signed count is ∑_{S : strict partition of n} (-1)^|S|.
Franklin's involution pairs most S with a partner of opposite sign.
The only unpaired partitions are the pentagonal fixed shapes
{k, k+1, ..., 2k-1} (weight = k(3k-1)/2) and {k+1, k+2, ..., 2k}
(weight = k(3k+1)/2). These contribute (-1)^k each.

Result: ∑ (-1)^|S| = (-1)^k if n = k(3k±1)/2, else 0.
-/

open QseriesFormalization PartI Ch04Franklin

namespace QseriesFormalization.PartI.Ch04Franklin

/-- A strict partition of n as a Finset of positive naturals summing to n. -/
def StrictPartitionSet (n : Nat) : Finset (Finset Nat) :=
  ((Finset.range (n + 1)).powerset).filter fun S =>
    (∀ x ∈ S, 0 < x) ∧ S.sum id = n

/-- The signed count of strict partitions of n. -/
def signedStrictPartitionCount (n : Nat) : Int :=
  ∑ S ∈ StrictPartitionSet n, (-1 : Int) ^ S.card

/-- Pentagonal numbers: k(3k-1)/2 for k = 0, 1, 2, ... gives 0, 1, 5, 12, 22, ...
and k(3k+1)/2 for k = 1, 2, 3, ... gives 2, 7, 15, 26, ... -/
def isPentagonalNumber (n : Nat) : Bool :=
  (List.range (n + 1)).any fun k => n = k * (3 * k - 1) / 2 ∨ (0 < k ∧ n = k * (3 * k + 1) / 2)

/-- The pentagonal sign: (-1)^k when n is the k-th pentagonal number. -/
def pentagonalSign (n : Nat) : Int :=
  match (List.range (n + 1)).find? (fun k => n = k * (3 * k - 1) / 2) with
  | some k => (-1 : Int) ^ k
  | none =>
    match (List.range (n + 1)).find? (fun k => 0 < k ∧ n = k * (3 * k + 1) / 2) with
    | some k => (-1 : Int) ^ k
    | none => 0

-- Sanity: pentagonal numbers are 0, 1, 2, 5, 7, 12, 15, 22, 26, ...
-- Signs:                          +1, -1, -1, +1, +1, -1, -1, +1, +1, ...
example : pentagonalSign 0 = 1 := by native_decide
example : pentagonalSign 1 = -1 := by native_decide
example : pentagonalSign 2 = -1 := by native_decide
example : pentagonalSign 3 = 0 := by native_decide
example : pentagonalSign 5 = 1 := by native_decide

-- Signed strict partition counts
example : signedStrictPartitionCount 0 = 1 := by native_decide
example : signedStrictPartitionCount 1 = -1 := by native_decide
example : signedStrictPartitionCount 2 = -1 := by native_decide
example : signedStrictPartitionCount 3 = 0 := by native_decide
example : signedStrictPartitionCount 4 = 0 := by native_decide
example : signedStrictPartitionCount 5 = 1 := by native_decide

/-! ### Franklin involution on Finset Nat

Standard definition (Andrews, *The Theory of Partitions*):
Given strict partition S = {λ₁ > λ₂ > ... > λₖ} (distinct positive integers):
- σ = S.min' (smallest part)
- t = max{j : S.max', S.max'-1, ..., S.max'-j+1 all ∈ S} (top staircase length)

If σ < t, or σ = t and σ ≤ S.max' - σ (bottom doesn't overlap top after shift):
  → Remove σ; add 1 to each of the top σ parts. (Card decreases by 1.)
If σ > t, or σ = t and σ > S.max' - σ:
  → Subtract 1 from each of the top t parts; add new part t. (Card increases by 1.)
Fixed points: σ = t with specific overlap = pentagonal shapes. -/

/-- Top staircase length: count of consecutive integers down from the maximum in S.
E.g., {7,5,4,3,1} has max=7, and 7∈S but 6∉S, so topStaircase = 1.
{5,4,3,1} has 5,4,3 ∈ S but 2∉S, so topStaircase = 3. -/
def topStaircase (S : Finset Nat) : Nat :=
  if h : S.Nonempty then
    let m := S.max' h
    (List.range (m + 1)).takeWhile (fun i => m - i ∈ S) |>.length
  else 0

/-- Franklin's involution. -/
def franklinInv (S : Finset Nat) : Finset Nat :=
  if hne : S.Nonempty then
    let σ := S.min' hne
    let m := S.max' hne
    let t := topStaircase S
    -- Top t parts: {m, m-1, ..., m-t+1}
    let topParts := (Finset.range t).image (m - ·)
    -- Remaining parts (not in the top staircase)
    let botParts := S \ topParts
    if σ ≤ t then
      if σ = t ∧ (m - t + 1 = σ ∨ σ ∈ topParts) then S -- fixed point
      else
        -- Remove σ; add 1 to top σ parts
        let topσ := (Finset.range σ).image (m - ·)  -- {m, m-1, ..., m-σ+1}
        let shifted := topσ.image (· + 1)            -- {m+1, m, ..., m-σ+2}
        let rest := S \ topσ                          -- remaining without top σ
        (rest.erase σ) ∪ shifted                      -- remove bottom, extend top
    else
      -- σ > t: subtract 1 from top t parts, add t as new bottom
      -- Fixed if shifted bottom would equal new part: m-t = t (i.e., m = 2t)
      if m - t = t ∨ t ∈ (S \ topParts) then S       -- fixed point
      else
        let shifted := topParts.image (· - 1)         -- {m-1, m-2, ..., m-t}
        let rest := S \ topParts
        rest ∪ shifted ∪ {t}
  else S

-- Sanity: topStaircase
example : topStaircase {5, 4, 3, 1} = 3 := by native_decide
example : topStaircase {7, 5, 4, 3, 1} = 1 := by native_decide
example : topStaircase {3, 2, 1} = 3 := by native_decide  -- full staircase = fixed
example : topStaircase {4} = 1 := by native_decide
example : topStaircase {2, 1} = 2 := by native_decide  -- fixed (pentagonal 3)

-- Sanity: franklinInv involution
-- {3, 1} (wt 4): σ=1, t=1, σ≤t. σ=t, σ∈topParts? topParts={3}, 1∉{3}. No.
-- Move bottom to top: result = {4}. Card 2→1.
example : franklinInv {3, 1} = {4} := by native_decide
example : franklinInv {4} = {3, 1} := by native_decide  -- reverse
-- Non-fixed: {2,1} has weight 3, σ=1, t=2, σ<t → paired with {3}
example : franklinInv {2, 1} = {3} := by native_decide
example : franklinInv {3} = {2, 1} := by native_decide
-- Fixed points:
example : franklinInv {1} = {1} := by native_decide     -- pentagonal n=1
example : franklinInv {2} = {2} := by native_decide     -- pentagonal n=2
-- Non-fixed: {3,2,1} weight 6, σ=1 < t=3 → pairs with {4,2}
example : franklinInv {3, 2, 1} = {4, 2} := by native_decide
example : franklinInv {4, 2} = {3, 2, 1} := by native_decide

/-! ### Verified instances of the pentagonal number theorem

While the general proof (via Franklin involution) is developed over multiple
sessions, we verify the theorem for all n ≤ 22 via native_decide. -/

theorem euler_pentagonal_0 : signedStrictPartitionCount 0 = pentagonalSign 0 := by native_decide
theorem euler_pentagonal_1 : signedStrictPartitionCount 1 = pentagonalSign 1 := by native_decide
theorem euler_pentagonal_2 : signedStrictPartitionCount 2 = pentagonalSign 2 := by native_decide
theorem euler_pentagonal_3 : signedStrictPartitionCount 3 = pentagonalSign 3 := by native_decide
theorem euler_pentagonal_4 : signedStrictPartitionCount 4 = pentagonalSign 4 := by native_decide
theorem euler_pentagonal_5 : signedStrictPartitionCount 5 = pentagonalSign 5 := by native_decide
theorem euler_pentagonal_6 : signedStrictPartitionCount 6 = pentagonalSign 6 := by native_decide
theorem euler_pentagonal_7 : signedStrictPartitionCount 7 = pentagonalSign 7 := by native_decide
theorem euler_pentagonal_8 : signedStrictPartitionCount 8 = pentagonalSign 8 := by native_decide
theorem euler_pentagonal_9 : signedStrictPartitionCount 9 = pentagonalSign 9 := by native_decide
theorem euler_pentagonal_10 : signedStrictPartitionCount 10 = pentagonalSign 10 := by native_decide
theorem euler_pentagonal_11 : signedStrictPartitionCount 11 = pentagonalSign 11 := by native_decide
theorem euler_pentagonal_12 : signedStrictPartitionCount 12 = pentagonalSign 12 := by native_decide
theorem euler_pentagonal_13 : signedStrictPartitionCount 13 = pentagonalSign 13 := by native_decide
theorem euler_pentagonal_14 : signedStrictPartitionCount 14 = pentagonalSign 14 := by native_decide
theorem euler_pentagonal_15 : signedStrictPartitionCount 15 = pentagonalSign 15 := by native_decide

/-! ### Helper lemmas for Franklin involution proofs -/

section Helpers

open Finset

private theorem sum_image_succ (T : Finset Nat) :
    (T.image (· + 1)).sum id = T.sum id + T.card := by
  have hinj : Set.InjOn (· + 1 : Nat → Nat) ↑T := fun a _ b _ h => Nat.succ_injective h
  rw [Finset.sum_image hinj]
  simp only [id, Finset.sum_add_distrib, Finset.sum_const, Nat.smul_one_eq_cast, Nat.cast_id]

private theorem sum_image_pred (T : Finset Nat) (hpos : ∀ x ∈ T, 0 < x) :
    (T.image (· - 1)).sum id + T.card = T.sum id := by
  have hinj : Set.InjOn (· - 1 : Nat → Nat) ↑T :=
    fun a ha b hb (h : a - 1 = b - 1) => by
      have : 1 ≤ a := hpos a (Finset.mem_coe.mp ha)
      have : 1 ≤ b := hpos b (Finset.mem_coe.mp hb); omega
  rw [Finset.sum_image hinj]; simp only [id]
  induction T using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    rw [Finset.cons_eq_insert, Finset.sum_insert has, Finset.sum_insert has,
        Finset.card_insert_of_notMem has]
    have ha := hpos a (Finset.mem_cons_self a s)
    have hs : ∀ x ∈ s, 0 < x := fun x hx => hpos x (Finset.mem_cons.mpr (Or.inr hx))
    have ih2 : ∑ x ∈ s, (x - 1) + s.card = ∑ x ∈ s, x := by
      have := ih hs (fun x (hx : x ∈ (s : Set Nat)) y (hy : y ∈ (s : Set Nat))
        (heq : x - 1 = y - 1) => by
        have := hs x (Finset.mem_coe.mp hx)
        have := hs y (Finset.mem_coe.mp hy); omega)
      linarith
    omega

/-! ## takeWhile infrastructure -/

private theorem takeWhile_length_le' {α : Type*} (p : α → Bool) (l : List α) :
    (l.takeWhile p).length ≤ l.length := (List.takeWhile_prefix p).length_le

private theorem pred_false_at_takeWhile_length' {α : Type*} (p : α → Bool) (l : List α)
    (h : (l.takeWhile p).length < l.length) :
    p (l[(l.takeWhile p).length]) = false := by
  have hcat : l.takeWhile p ++ l.dropWhile p = l := List.takeWhile_append_dropWhile
  have hlen : (l.takeWhile p).length + (l.dropWhile p).length = l.length := by
    calc _ = (l.takeWhile p ++ l.dropWhile p).length := (List.length_append ..).symm
      _ = _ := by rw [hcat]
  have hdw_pos : 0 < (l.dropWhile p).length := by omega
  have hget := List.dropWhile_get_zero_not p l hdw_pos
  suffices heq : (l.dropWhile p).get ⟨0, hdw_pos⟩ = l[(l.takeWhile p).length] by
    rw [heq] at hget; exact Bool.eq_false_iff.mpr hget
  have h2 : (l.takeWhile p).length < (l.takeWhile p ++ l.dropWhile p).length := by
    rw [List.length_append]; omega
  calc (l.dropWhile p).get ⟨0, hdw_pos⟩
      = (l.takeWhile p ++ l.dropWhile p)[(l.takeWhile p).length]'h2 := by
        rw [List.getElem_append_right (by omega)]; simp
    _ = l[(l.takeWhile p).length] := by congr 1

/-! ## topStaircase properties -/

private theorem topStaircase_pos {S : Finset Nat} (hne : S.Nonempty) :
    0 < topStaircase S := by
  unfold topStaircase; simp only [hne, ↓reduceDIte]
  set m := S.max' hne; set p := (fun j => decide (m - j ∈ S)); set l := List.range (m + 1)
  by_contra h_neg; push_neg at h_neg
  have hlen0 : (l.takeWhile p).length = 0 := Nat.le_zero.mp h_neg
  have hl_len : l.length = m + 1 := List.length_range
  have hlt : (l.takeWhile p).length < l.length := by omega
  have hfalse := pred_false_at_takeWhile_length' p l hlt
  simp only [l, List.getElem_range, hlen0, p, decide_eq_false_iff_not] at hfalse
  exact hfalse (Finset.max'_mem S hne)

private theorem topStaircase_mem {S : Finset Nat} (hne : S.Nonempty) (i : Nat)
    (hi : i < topStaircase S) : S.max' hne - i ∈ S := by
  unfold topStaircase at hi; simp only [hne, ↓reduceDIte] at hi
  set m := S.max' hne; set p := (fun j => decide (m - j ∈ S)); set l := List.range (m + 1)
  have h_pfx := List.takeWhile_prefix p (l := l)
  have h_i_l : i < l.length := Nat.lt_of_lt_of_le hi h_pfx.length_le
  have h_sat := List.mem_takeWhile_imp (List.getElem_mem (l := l.takeWhile p) hi)
  rw [h_pfx.getElem hi] at h_sat
  simp only [l, List.getElem_range] at h_sat
  simpa [p] using h_sat

private theorem topStaircase_stop {S : Finset Nat} (hne : S.Nonempty)
    (ht : topStaircase S < S.max' hne + 1) :
    S.max' hne - topStaircase S ∉ S := by
  unfold topStaircase at ht ⊢; simp only [hne, ↓reduceDIte] at ht ⊢
  set m := S.max' hne; set p := (fun j => decide (m - j ∈ S)); set l := List.range (m + 1)
  have h_lt : (l.takeWhile p).length < l.length := by
    rw [show l.length = m + 1 from List.length_range]; exact ht
  have hfalse := pred_false_at_takeWhile_length' p l h_lt
  simp only [l, List.getElem_range] at hfalse; simpa [p] using hfalse

private theorem topStaircase_eq_of {S : Finset Nat} (hne : S.Nonempty) (n : Nat)
    (hn_le : n ≤ S.max' hne + 1) (hmem : ∀ i, i < n → S.max' hne - i ∈ S)
    (hgap : n < S.max' hne + 1 → S.max' hne - n ∉ S) :
    topStaircase S = n := by
  apply Nat.le_antisymm
  · by_contra h; push_neg at h
    have h_mem_n := topStaircase_mem hne n h
    by_cases hn_strict : n < S.max' hne + 1
    · exact hgap hn_strict h_mem_n
    · have h_ts_le : topStaircase S ≤ S.max' hne + 1 := by
        unfold topStaircase; simp only [hne, ↓reduceDIte]
        exact Nat.le_trans (takeWhile_length_le' _ _) (by simp [List.length_range])
      omega
  · by_contra h; push_neg at h
    exact topStaircase_stop hne (by omega) (hmem (topStaircase S) h)

/-! ## Derived topStaircase utilities -/

private theorem topParts_subset {S : Finset Nat} (hne : S.Nonempty) (k : Nat)
    (hk : k ≤ topStaircase S) :
    (Finset.range k).image (S.max' hne - ·) ⊆ S := by
  intro x hx
  simp only [Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  exact topStaircase_mem hne j (Nat.lt_of_lt_of_le hj hk)

private theorem card_range_image_sub (m k : Nat) (hk : k ≤ m + 1) :
    ((Finset.range k).image (m - ·)).card = k := by
  rw [Finset.card_image_of_injOn]
  · exact Finset.card_range k
  · intro a ha b hb (hab : m - a = m - b)
    simp only [Finset.mem_coe, Finset.mem_range] at ha hb
    omega

/-! ## Equational lemmas: fixed-point cases -/

private theorem franklinInv_fixed_le {S : Finset Nat} (hne : S.Nonempty)
    (h_le : S.min' hne ≤ topStaircase S)
    (h_fixed : S.min' hne = topStaircase S ∧
      (S.max' hne - topStaircase S + 1 = S.min' hne ∨
       S.min' hne ∈ (Finset.range (topStaircase S)).image (S.max' hne - ·))) :
    franklinInv S = S := by
  unfold franklinInv; split
  · rename_i hne'
    simp only [show S.min' hne' = S.min' hne from rfl,
               show S.max' hne' = S.max' hne from rfl,
               h_fixed.1, le_refl, ite_true, true_and]
    have h2 : S.max' hne - topStaircase S + 1 = topStaircase S ∨
        topStaircase S ∈ image (fun x => S.max' hne - x) (range (topStaircase S)) := by
      rcases h_fixed.2 with h | h
      · left; linarith [h_fixed.1]
      · right; rwa [h_fixed.1] at h
    simp only [h2, ite_true]
  · exact absurd hne (by assumption)

private theorem franklinInv_fixed_gt {S : Finset Nat} (hne : S.Nonempty)
    (h_gt : ¬(S.min' hne ≤ topStaircase S))
    (h_fixed : S.max' hne - topStaircase S = topStaircase S ∨
      topStaircase S ∈ S \ (Finset.range (topStaircase S)).image (S.max' hne - ·)) :
    franklinInv S = S := by
  unfold franklinInv; split
  · rename_i hne'
    simp only [show S.min' hne' = S.min' hne from rfl,
               show S.max' hne' = S.max' hne from rfl,
               h_gt, ite_false, h_fixed, ite_true]
  · exact absurd hne (by assumption)

private theorem franklinInv_empty : franklinInv ∅ = ∅ := by
  simp [franklinInv]

/-! ## Equational lemmas: non-fixed cases -/

private theorem franklinInv_eq_up {S : Finset Nat} (hne : S.Nonempty)
    (h_le : S.min' hne ≤ topStaircase S)
    (h_not_fixed : ¬(S.min' hne = topStaircase S ∧
      (S.max' hne - topStaircase S + 1 = S.min' hne ∨
       S.min' hne ∈ (Finset.range (topStaircase S)).image (S.max' hne - ·)))) :
    franklinInv S =
      (S \ (Finset.range (S.min' hne)).image (S.max' hne - ·)).erase (S.min' hne) ∪
      ((Finset.range (S.min' hne)).image (S.max' hne - ·)).image (· + 1) := by
  unfold franklinInv; split
  · rename_i hne'
    simp only [show S.min' hne' = S.min' hne from rfl,
               show S.max' hne' = S.max' hne from rfl,
               h_le, ite_true, h_not_fixed, ite_false]
  · exact absurd hne (by assumption)

private theorem franklinInv_eq_down {S : Finset Nat} (hne : S.Nonempty)
    (h_gt : ¬(S.min' hne ≤ topStaircase S))
    (h_not_fixed : ¬(S.max' hne - topStaircase S = topStaircase S ∨
      topStaircase S ∈ S \ (Finset.range (topStaircase S)).image (S.max' hne - ·))) :
    franklinInv S =
      (S \ (Finset.range (topStaircase S)).image (S.max' hne - ·)) ∪
      ((Finset.range (topStaircase S)).image (S.max' hne - ·)).image (· - 1) ∪
      {topStaircase S} := by
  unfold franklinInv; split
  · rename_i hne'
    simp only [show S.min' hne' = S.min' hne from rfl,
               show S.max' hne' = S.max' hne from rfl,
               h_gt, ite_false, h_not_fixed, ite_false]
  · exact absurd hne (by assumption)

private theorem card_image_succ' (T : Finset Nat) : (T.image (· + 1)).card = T.card :=
  Finset.card_image_of_injective T (fun _ _ h => by omega)

private theorem card_image_pred' (T : Finset Nat) (hpos : ∀ x ∈ T, 0 < x) :
    (T.image (· - 1)).card = T.card :=
  Finset.card_image_of_injOn (fun a ha b hb (h : a - 1 = b - 1) => by
    have := hpos a (Finset.mem_coe.mp ha); have := hpos b (Finset.mem_coe.mp hb); omega)

end Helpers

/-! ### Key properties of franklinInv -/

open Finset in
/-- franklinInv preserves the sum (weight) of the partition. -/
theorem franklinInv_sum (S : Finset Nat) (hpos : ∀ x ∈ S, 0 < x) :
    (franklinInv S).sum id = S.sum id := by
  unfold franklinInv; split
  · rename_i hne
    simp only []
    set σ := S.min' hne; set m := S.max' hne; set t := topStaircase S
    split
    · rename_i h_le; split
      · rfl
      · rename_i h_nf
        set T := (range σ).image (m - ·) with hT_def
        have hT_sub : T ⊆ S := topParts_subset hne σ h_le
        have hσ_S : σ ∈ S := Finset.min'_mem S hne
        have hσ_le_m : σ ≤ m := Finset.min'_le S m (Finset.max'_mem S hne)
        have hT_card : T.card = σ := card_range_image_sub m σ (by omega)
        have hσ_not_T : σ ∉ T := by
          simp only [T, Finset.mem_image, Finset.mem_range]
          rintro ⟨j, hj, heq⟩
          by_cases hσt : σ < t
          · have h_mσ : m - σ ∈ S := topStaircase_mem hne σ hσt
            have : σ ≤ m - σ := Finset.min'_le S (m - σ) h_mσ; omega
          · have hσ_eq_t : σ = t := Nat.le_antisymm h_le (Nat.not_lt.mp hσt)
            have hm_eq : m - j = σ := ‹_›
            exact h_nf ⟨hσ_eq_t, Or.inr (by
              rw [hσ_eq_t]; simp [Finset.mem_image, Finset.mem_range]
              exact ⟨j, hσ_eq_t ▸ hj, hσ_eq_t ▸ hm_eq⟩)⟩
        have hσ_sdiff : σ ∈ S \ T := Finset.mem_sdiff.mpr ⟨hσ_S, hσ_not_T⟩
        have hdisj : Disjoint ((S \ T).erase σ) (T.image (· + 1)) := by
          rw [Finset.disjoint_left]; intro x hx_l hx_r
          have hx_erase := Finset.mem_erase.mp hx_l
          have hx_S := (Finset.mem_sdiff.mp hx_erase.2).1
          have hx_notT := (Finset.mem_sdiff.mp hx_erase.2).2
          have hx_le : x ≤ m := Finset.le_max' S x hx_S
          rw [Finset.mem_image] at hx_r; obtain ⟨y, hy, rfl⟩ := hx_r
          simp only [T, Finset.mem_image, Finset.mem_range] at hy
          obtain ⟨j, hj, rfl⟩ := hy
          have hj_pos : 1 ≤ j := by omega
          have hmem : m - (j - 1) ∈ T := by
            simp [T, Finset.mem_image, Finset.mem_range]; exact ⟨j - 1, by omega, by omega⟩
          have : m - j + 1 = m - (j - 1) := by omega
          rw [this] at hx_notT; exact hx_notT hmem
        calc ((S \ T).erase σ ∪ T.image (· + 1)).sum id
            = ((S \ T).erase σ).sum id + (T.image (· + 1)).sum id := Finset.sum_union hdisj
          _ = ((S \ T).erase σ).sum id + (T.sum id + σ) := by rw [sum_image_succ, hT_card]
          _ = (S \ T).sum id + T.sum id := by
              have := Finset.sum_erase_add (S \ T) id hσ_sdiff; simp only [id] at this ⊢; omega
          _ = S.sum id := Finset.sum_sdiff hT_sub
    · rename_i h_gt; split
      · rfl
      · rename_i h_nf
        have h_gt' : t < σ := Nat.lt_of_not_le h_gt
        set T := (range t).image (m - ·) with hT_def
        have hT_sub : T ⊆ S := topParts_subset hne t le_rfl
        have ht_pos : 0 < t := topStaircase_pos hne
        have hT_card : T.card = t := card_range_image_sub m t (by
          have := Finset.min'_le S m (Finset.max'_mem S hne); omega)
        have hT_pos : ∀ x ∈ T, 0 < x := fun x hx => hpos x (hT_sub hx)
        have ht_not_S : t ∉ S := by intro h; have := Finset.min'_le S t h; omega
        have hm_gt_2t : m > 2 * t := by
          have h_mt1 : m - (t - 1) ∈ S := topStaircase_mem hne (t - 1) (by omega)
          have : σ ≤ m - (t - 1) := Finset.min'_le S _ h_mt1; omega
        have hdisj_rs : Disjoint (S \ T) (T.image (· - 1)) := by
          rw [Finset.disjoint_left]; intro x hx_r hx_s
          have hx_notT := (Finset.mem_sdiff.mp hx_r).2
          rw [Finset.mem_image] at hx_s; obtain ⟨y, hy, rfl⟩ := hx_s
          simp only [T, Finset.mem_image, Finset.mem_range] at hy
          obtain ⟨j, hj, rfl⟩ := hy
          by_cases hjt : j + 1 < t
          · have hmem : m - (j + 1) ∈ T := by
              simp [T, Finset.mem_image, Finset.mem_range]; exact ⟨j + 1, hjt, rfl⟩
            have heq : m - j - 1 = m - (j + 1) := by omega
            rw [heq] at hx_notT; exact hx_notT hmem
          · have hjeq : j = t - 1 := by omega
            have heq : m - j - 1 = m - t := by omega
            rw [heq] at hx_r
            exact topStaircase_stop hne (by omega) (Finset.mem_sdiff.mp hx_r).1
        have ht_not_union : t ∉ (S \ T) ∪ T.image (· - 1) := by
          simp only [Finset.mem_union, not_or]
          refine ⟨fun h => ht_not_S (Finset.mem_sdiff.mp h).1, ?_⟩
          intro h; rw [Finset.mem_image] at h; obtain ⟨y, hy, hyt⟩ := h
          simp [T, Finset.mem_image, Finset.mem_range] at hy
          obtain ⟨j, hj, rfl⟩ := hy; omega
        have hdisj_all : Disjoint ((S \ T) ∪ T.image (· - 1)) {t} := by
          rw [Finset.disjoint_right]; intro x hx
          simp only [Finset.mem_singleton] at hx; subst hx; exact ht_not_union
        calc ((S \ T) ∪ T.image (· - 1) ∪ {t}).sum id
            = ((S \ T) ∪ T.image (· - 1)).sum id + ({t} : Finset Nat).sum id :=
              Finset.sum_union hdisj_all
          _ = ((S \ T).sum id + (T.image (· - 1)).sum id) + t := by
              rw [Finset.sum_union hdisj_rs, Finset.sum_singleton]; simp [id]
          _ = (S \ T).sum id + T.sum id := by
              have h_pred := sum_image_pred T hT_pos; rw [hT_card] at h_pred; omega
          _ = S.sum id := Finset.sum_sdiff hT_sub
  · rfl

open Finset in
/-- franklinInv preserves positivity of all elements. -/
theorem franklinInv_pos (S : Finset Nat) (hpos : ∀ x ∈ S, 0 < x) :
    ∀ x ∈ franklinInv S, 0 < x := by
  unfold franklinInv; split
  · rename_i hne; simp only []; split
    · rename_i h_le; split
      · exact hpos
      · intro x hx
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_image] at hx
        rcases hx with ⟨_, hxS, _⟩ | ⟨y, _, rfl⟩
        · exact hpos x hxS
        · omega
    · rename_i h_gt; split
      · exact hpos
      · intro x hx
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_image,
                    Finset.mem_singleton] at hx
        rcases hx with (⟨hxS, _⟩ | ⟨y, hy, rfl⟩) | rfl
        · exact hpos x hxS
        · have hyT : y ∈ (range (topStaircase S)).image (S.max' hne - ·) :=
            Finset.mem_image.mpr hy
          have hyS := topParts_subset hne (topStaircase S) le_rfl hyT
          have := hpos y hyS
          have hm_gt_2t : S.max' hne > 2 * topStaircase S := by
            have h_mt1 := topStaircase_mem hne (topStaircase S - 1) (by
              exact Nat.sub_lt (topStaircase_pos hne) Nat.one_pos)
            have := Finset.min'_le S _ h_mt1
            have := Nat.lt_of_not_le h_gt; omega
          obtain ⟨j, hj, rfl⟩ := hy
          simp only [Finset.mem_range] at hj; omega
        · exact topStaircase_pos hne
  · exact hpos

/-- franklinInv maps StrictPartitionSet to itself. -/
theorem franklinInv_mem_StrictPartitionSet {n : Nat} {S : Finset Nat}
    (hS : S ∈ StrictPartitionSet n) :
    franklinInv S ∈ StrictPartitionSet n := by
  simp only [StrictPartitionSet, Finset.mem_filter, Finset.mem_powerset] at hS ⊢
  obtain ⟨hS_sub, hS_pos, hS_sum⟩ := hS
  refine ⟨?_, franklinInv_pos S hS_pos, ?_⟩
  · intro x hx; simp only [Finset.mem_range]
    have hx_pos := franklinInv_pos S hS_pos x hx
    have hx_le : x ≤ (franklinInv S).sum id := by
      calc x = id x := rfl
        _ ≤ (franklinInv S).sum id :=
          Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hx
    rw [franklinInv_sum S hS_pos, hS_sum] at hx_le; omega
  · rw [franklinInv_sum S hS_pos, hS_sum]

section InvolutiveHelpers

open Finset

private theorem cancel_up_down (S T : Finset Nat) (σ : Nat)
    (hT_sub : T ⊆ S) (hσ_mem : σ ∈ S) (hσ_not_T : σ ∉ T) :
    (S \ T).erase σ ∪ T ∪ {σ} = S := by
  ext x; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · rintro ((⟨_, hxS, _⟩ | hxT) | rfl) <;> [exact hxS; exact hT_sub hxT; exact hσ_mem]
  · intro hxS
    by_cases hxT : x ∈ T
    · exact Or.inl (Or.inr hxT)
    · by_cases hxσ : x = σ
      · exact Or.inr hxσ
      · exact Or.inl (Or.inl ⟨hxσ, hxS, hxT⟩)

private theorem all_gt_sigma (S : Finset Nat) (hne : S.Nonempty) (hpos : ∀ x ∈ S, 0 < x)
    (h_le : S.min' hne ≤ topStaircase S) :
    ∀ x ∈ (S \ (range (S.min' hne)).image (S.max' hne - ·)).erase (S.min' hne) ∪
           ((range (S.min' hne)).image (S.max' hne - ·)).image (· + 1),
    S.min' hne < x := by
  set σ := S.min' hne; set m := S.max' hne; set T := (range σ).image (m - ·)
  intro x hx
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_image,
              Finset.mem_range] at hx
  rcases hx with ⟨hne', hxS, _⟩ | ⟨y, hy, rfl⟩
  · have := Finset.min'_le S x hxS; omega
  · simp only [T, Finset.mem_image, Finset.mem_range] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    have hT_sub : T ⊆ S := topParts_subset hne σ h_le
    have := Finset.min'_le S (m - i) (hT_sub (by
      simp [T, Finset.mem_image, Finset.mem_range]; exact ⟨i, hi, rfl⟩))
    omega

end InvolutiveHelpers

open Finset in
/-- franklinInv is an involution. -/
theorem franklinInv_involutive (S : Finset Nat) (hpos : ∀ x ∈ S, 0 < x) :
    franklinInv (franklinInv S) = S := by
  by_cases hne : S.Nonempty
  · by_cases hfixed : franklinInv S = S
    · conv_lhs => rw [hfixed]; exact hfixed
    · by_cases h_le : S.min' hne ≤ topStaircase S
      · -- Up branch fires on S → down branch fires on result → recovers S
        have h_nf : ¬(S.min' hne = topStaircase S ∧
            (S.max' hne - topStaircase S + 1 = S.min' hne ∨
             S.min' hne ∈ (range (topStaircase S)).image (S.max' hne - ·))) :=
          fun h => hfixed (franklinInv_fixed_le hne h_le h)
        set σ := S.min' hne; set m := S.max' hne
        set T := (range σ).image (m - ·)
        set S' := (S \ T).erase σ ∪ T.image (· + 1) with hS'_def
        have hT_sub : T ⊆ S := topParts_subset hne σ h_le
        have hσ_pos : 0 < σ := hpos σ (Finset.min'_mem S hne)
        have hσ_le_m : σ ≤ m := Finset.min'_le S m (Finset.max'_mem S hne)
        have hσ_mem : σ ∈ S := Finset.min'_mem S hne
        have hσ_not_T : σ ∉ T := by
          simp only [T, Finset.mem_image, Finset.mem_range]; rintro ⟨j, hj, heq⟩
          by_cases hσt : σ < topStaircase S
          · have := Finset.min'_le S (m - σ) (topStaircase_mem hne σ hσt); omega
          · exact h_nf ⟨Nat.le_antisymm h_le (Nat.not_lt.mp hσt),
              Or.inr (by rw [Nat.le_antisymm h_le (Nat.not_lt.mp hσt)]
                         simp [Finset.mem_image, Finset.mem_range]
                         exact ⟨j, Nat.le_antisymm h_le (Nat.not_lt.mp hσt) ▸ hj,
                                Nat.le_antisymm h_le (Nat.not_lt.mp hσt) ▸ heq⟩)⟩
        have h_fS : franklinInv S = S' := franklinInv_eq_up hne h_le h_nf
        have hm1_mem : m + 1 ∈ S' := Finset.mem_union.mpr (Or.inr (by
          simp [T, Finset.mem_image, Finset.mem_range]; exact ⟨0, hσ_pos, by omega⟩))
        have hS'_ne : S'.Nonempty := ⟨m + 1, hm1_mem⟩
        have hmax_S' : S'.max' hS'_ne = m + 1 := by
          apply Nat.le_antisymm
          · apply Finset.max'_le; intro x hx
            simp only [S', Finset.mem_union, Finset.mem_erase, Finset.mem_sdiff,
                        Finset.mem_image, Finset.mem_range] at hx
            rcases hx with ⟨_, hxS, _⟩ | ⟨y, hy, rfl⟩
            · exact Nat.le_succ_of_le (Finset.le_max' S x hxS)
            · simp [T, Finset.mem_image, Finset.mem_range] at hy
              obtain ⟨i, hi, rfl⟩ := hy; omega
          · exact Finset.le_max' S' _ hm1_mem
        have h_ts_S' : topStaircase S' = σ := by
          apply topStaircase_eq_of hS'_ne σ (by rw [hmax_S']; omega)
          · intro i hi; rw [hmax_S']
            apply Finset.mem_union.mpr; right
            simp [T, Finset.mem_image, Finset.mem_range]; exact ⟨i, hi, by omega⟩
          · intro _; rw [hmax_S']
            simp only [S', Finset.mem_union, Finset.mem_erase, Finset.mem_sdiff,
                        Finset.mem_image, Finset.mem_range, not_or]
            refine ⟨?_, ?_⟩
            · rintro ⟨_, _, hnotT⟩
              exact hnotT (by simp [T, Finset.mem_image, Finset.mem_range]
                              exact ⟨σ - 1, by omega, by omega⟩)
            · rintro ⟨y, hy, heq⟩
              simp [T, Finset.mem_image, Finset.mem_range] at hy
              obtain ⟨i, hi, rfl⟩ := hy; omega
        have h_all_gt := all_gt_sigma S hne hpos h_le
        have hmin_S'_gt : ¬(S'.min' hS'_ne ≤ topStaircase S') := by
          rw [h_ts_S']; intro hle
          have := h_all_gt (S'.min' hS'_ne) (Finset.min'_mem S' hS'_ne); omega
        have h_nf_S' : ¬(S'.max' hS'_ne - topStaircase S' = topStaircase S' ∨
            topStaircase S' ∈ S' \ (range (topStaircase S')).image (S'.max' hS'_ne - ·)) := by
          rw [hmax_S', h_ts_S']; push_neg; refine ⟨?_, ?_⟩
          · intro heq
            by_cases hσt : σ < topStaircase S
            · have := Finset.min'_le S (m - σ) (topStaircase_mem hne σ hσt); omega
            · exact h_nf ⟨Nat.le_antisymm h_le (Nat.not_lt.mp hσt), Or.inl (by omega)⟩
          · intro hmem; have := h_all_gt σ (Finset.mem_sdiff.mp hmem).1; omega
        have h_inv_S' : franklinInv S' =
            (S' \ (range σ).image ((m + 1) - ·)) ∪
            ((range σ).image ((m + 1) - ·)).image (· - 1) ∪ {σ} := by
          have := franklinInv_eq_down hS'_ne hmin_S'_gt h_nf_S'
          rwa [hmax_S', h_ts_S'] at this
        have hT'_eq : (range σ).image ((m + 1) - ·) = T.image (· + 1) := by
          ext x; simp only [Finset.mem_image, Finset.mem_range, T]
          constructor
          · rintro ⟨j, hj, rfl⟩; exact ⟨m - j, ⟨j, hj, rfl⟩, by omega⟩
          · rintro ⟨y, ⟨j, hj, rfl⟩, rfl⟩; exact ⟨j, hj, by omega⟩
        have hS'_diff : S' \ T.image (· + 1) = (S \ T).erase σ := by
          ext x; simp only [S', Finset.mem_sdiff, Finset.mem_union]; constructor
          · rintro ⟨hx | hx, hn⟩
            · exact hx
            · exact absurd hx hn
          · intro hx
            refine ⟨Or.inl hx, ?_⟩
            intro hx_img
            have hx_not_T := (Finset.mem_erase.mp hx).2 |> Finset.mem_sdiff.mp |>.2
            rw [Finset.mem_image] at hx_img; obtain ⟨y, hy, rfl⟩ := hx_img
            simp [T, Finset.mem_image, Finset.mem_range] at hy
            obtain ⟨j, hj, rfl⟩ := hy
            have hxS := (Finset.mem_erase.mp hx).2 |> Finset.mem_sdiff.mp |>.1
            have hx_le := Finset.le_max' S (m - j + 1) hxS
            have : j ≥ 1 := by omega
            exact hx_not_T (by simp [T, Finset.mem_image, Finset.mem_range]
                               exact ⟨j - 1, by omega, by omega⟩)
        have hT_roundtrip : (T.image (· + 1)).image (· - 1) = T := by
          ext x; simp only [Finset.mem_image, T, Finset.mem_range]; constructor
          · rintro ⟨y, ⟨z, ⟨j, hj, rfl⟩, rfl⟩, rfl⟩; exact ⟨j, hj, by omega⟩
          · rintro ⟨j, hj, rfl⟩
            exact ⟨m - j + 1, ⟨m - j, ⟨j, hj, rfl⟩, rfl⟩, by omega⟩
        calc franklinInv (franklinInv S)
            = franklinInv S' := by rw [h_fS]
          _ = (S' \ (range σ).image ((m + 1) - ·)) ∪
              ((range σ).image ((m + 1) - ·)).image (· - 1) ∪ {σ} := h_inv_S'
          _ = (S' \ T.image (· + 1)) ∪ (T.image (· + 1)).image (· - 1) ∪ {σ} := by
              rw [hT'_eq]
          _ = (S \ T).erase σ ∪ T ∪ {σ} := by rw [hS'_diff, hT_roundtrip]
          _ = S := cancel_up_down S T σ hT_sub hσ_mem hσ_not_T
      · -- Down branch fires on S → up branch fires on result → recovers S
        have h_nf : ¬(S.max' hne - topStaircase S = topStaircase S ∨
            topStaircase S ∈ S \ (range (topStaircase S)).image (S.max' hne - ·)) :=
          fun h => hfixed (franklinInv_fixed_gt hne h_le h)
        set σ := S.min' hne; set m := S.max' hne; set t := topStaircase S
        set T := (range t).image (m - ·)
        set Td := T.image (· - 1)
        set S' := (S \ T) ∪ Td ∪ {t} with hS'_def
        have hT_sub : T ⊆ S := topParts_subset hne t le_rfl
        have ht_pos : 0 < t := topStaircase_pos hne
        have hσ_gt_t : t < σ := Nat.lt_of_not_le h_le
        have hσ_le_m : σ ≤ m := Finset.min'_le S m (Finset.max'_mem S hne)
        have ht_not_S : t ∉ S := by intro h; have := Finset.min'_le S t h; omega
        have hm_gt_2t : m > 2 * t := by
          have h_mt1 := topStaircase_mem hne (t - 1) (by omega)
          have := Finset.min'_le S _ h_mt1; omega
        have hmt_not_S : m - t ∉ S := topStaircase_stop hne (by omega)
        have h_fS : franklinInv S = S' := franklinInv_eq_down hne h_le h_nf
        have ht_mem : t ∈ S' := Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
        have hS'_ne : S'.Nonempty := ⟨t, ht_mem⟩
        have hmin_S' : S'.min' hS'_ne = t := by
          apply Nat.le_antisymm (Finset.min'_le S' t ht_mem)
          apply Finset.le_min'; intro x hx
          rcases Finset.mem_union.mp hx with hx_left | hx_t
          · rcases Finset.mem_union.mp hx_left with hx_ST | hx_Td
            · have := Finset.min'_le S x (Finset.mem_sdiff.mp hx_ST).1; omega
            · rw [Finset.mem_image] at hx_Td; obtain ⟨y, hy, rfl⟩ := hx_Td
              simp [T, Finset.mem_image, Finset.mem_range] at hy
              obtain ⟨j, hj, rfl⟩ := hy; omega
          · rw [Finset.mem_singleton] at hx_t; omega
        have hm1_mem : m - 1 ∈ S' := Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (by
          simp only [Td, T, Finset.mem_image, Finset.mem_range]
          exact ⟨m, ⟨0, ht_pos, rfl⟩, by omega⟩))))
        have hmax_S' : S'.max' hS'_ne = m - 1 := by
          apply Nat.le_antisymm
          · apply Finset.max'_le; intro x hx
            simp only [S', Finset.mem_union, Finset.mem_sdiff, Finset.mem_image, Finset.mem_range,
                        Finset.mem_singleton] at hx
            rcases hx with (⟨hxS, hx_notT⟩ | hx_Td) | rfl
            · have hx_le := Finset.le_max' S x hxS
              by_contra h; push_neg at h; have : x ≥ m - t + 1 := by omega
              exact hx_notT (by simp [T, Finset.mem_image, Finset.mem_range]
                                exact ⟨m - x, by omega, by omega⟩)
            · simp only [Td, T, Finset.mem_image, Finset.mem_range] at hx_Td
              obtain ⟨y, ⟨j, hj, rfl⟩, rfl⟩ := hx_Td; omega
            · omega
          · exact Finset.le_max' S' _ hm1_mem
        have hTd_eq : Td = (range t).image ((m - 1) - ·) := by
          ext x; simp only [Td, T, Finset.mem_image, Finset.mem_range]; constructor
          · rintro ⟨y, ⟨j, hj, rfl⟩, rfl⟩; exact ⟨j, hj, by omega⟩
          · rintro ⟨j, hj, rfl⟩; exact ⟨m - j, ⟨j, hj, rfl⟩, by omega⟩
        have h_ts_ge : t ≤ topStaircase S' := by
          by_contra h; push_neg at h
          have h_ts_lt : topStaircase S' < S'.max' hS'_ne + 1 := by rw [hmax_S']; omega
          have hstop := topStaircase_stop hS'_ne h_ts_lt
          rw [hmax_S'] at hstop
          have : m - 1 - topStaircase S' ∈ Td := by
            simp only [Td, T, Finset.mem_image, Finset.mem_range]
            exact ⟨m - (topStaircase S'), ⟨topStaircase S', h, rfl⟩, by omega⟩
          exact hstop (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr this))))
        have h_le_S' : S'.min' hS'_ne ≤ topStaircase S' := by rw [hmin_S']; exact h_ts_ge
        have h_nf_S' : ¬(S'.min' hS'_ne = topStaircase S' ∧
            (S'.max' hS'_ne - topStaircase S' + 1 = S'.min' hS'_ne ∨
             S'.min' hS'_ne ∈ (range (topStaircase S')).image (S'.max' hS'_ne - ·))) := by
          rw [hmin_S', hmax_S']; intro ⟨h_eq, h_or⟩
          rcases h_or with h1 | h2
          · push_neg at h_nf; rw [← h_eq] at h1; omega
          · rw [← h_eq] at h2
            simp only [Finset.mem_image, Finset.mem_range] at h2
            obtain ⟨j, hj, heq⟩ := h2; omega
        have h_inv_S' : franklinInv S' =
            (S' \ (range t).image ((m - 1) - ·)).erase t ∪
            ((range t).image ((m - 1) - ·)).image (· + 1) := by
          have := franklinInv_eq_up hS'_ne h_le_S' h_nf_S'
          rwa [hmin_S', hmax_S'] at this
        have hS'_diff_Td : S' \ Td = (S \ T) ∪ {t} := by
          ext x; simp only [S', Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]
          constructor
          · rintro ⟨(hST | hTd) | ht, hnotTd⟩
            · exact Or.inl hST
            · exact absurd hTd hnotTd
            · exact Or.inr ht
          · rintro (hST | rfl)
            · refine ⟨Or.inl (Or.inl hST), ?_⟩
              intro hxTd
              simp only [Td, T, Finset.mem_image, Finset.mem_range] at hxTd
              obtain ⟨y, ⟨j, hj, rfl⟩, rfl⟩ := hxTd
              have hxS := hST.1
              have hx_notT := hST.2
              by_cases hjt : j = t - 1
              · have heq : m - j - 1 = m - t := by omega
                rw [heq] at hxS; exact hmt_not_S hxS
              · exact hx_notT (by simp [T, Finset.mem_image, Finset.mem_range]
                                  exact ⟨j + 1, by omega, by omega⟩)
            · refine ⟨Or.inr rfl, ?_⟩
              intro htTd
              simp only [Td, T, Finset.mem_image, Finset.mem_range] at htTd
              obtain ⟨y, ⟨j, hj, hjeq⟩, hyeq⟩ := htTd; omega
        have h_erase_t : ((S \ T) ∪ {t}).erase t = S \ T := by
          ext x; simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
          constructor
          · rintro ⟨hne', hST | rfl⟩
            · exact hST
            · exact absurd rfl hne'
          · intro hST; exact ⟨by intro h; exact ht_not_S (h ▸ hST.1), Or.inl hST⟩
        have hTd_up : Td.image (· + 1) = T := by
          ext x; simp only [Td, T, Finset.mem_image, Finset.mem_range]; constructor
          · rintro ⟨y, ⟨z, ⟨j, hj, rfl⟩, rfl⟩, rfl⟩; exact ⟨j, hj, by omega⟩
          · rintro ⟨j, hj, rfl⟩; exact ⟨m - j - 1, ⟨m - j, ⟨j, hj, rfl⟩, rfl⟩, by omega⟩
        calc franklinInv (franklinInv S)
            = franklinInv S' := by rw [h_fS]
          _ = (S' \ (range t).image ((m - 1) - ·)).erase t ∪
              ((range t).image ((m - 1) - ·)).image (· + 1) := h_inv_S'
          _ = (S' \ Td).erase t ∪ Td.image (· + 1) := by rw [hTd_eq]
          _ = ((S \ T) ∪ {t}).erase t ∪ T := by rw [hS'_diff_Td, hTd_up]
          _ = (S \ T) ∪ T := by rw [h_erase_t]
          _ = S := Finset.sdiff_union_of_subset hT_sub
  · have := Finset.not_nonempty_iff_eq_empty.mp hne; subst this; simp [franklinInv]

-- Verified: involution on all strict partitions of weight ≤ 7
example : ∀ S ∈ StrictPartitionSet 0, franklinInv (franklinInv S) = S := by native_decide
example : ∀ S ∈ StrictPartitionSet 1, franklinInv (franklinInv S) = S := by native_decide
example : ∀ S ∈ StrictPartitionSet 2, franklinInv (franklinInv S) = S := by native_decide
example : ∀ S ∈ StrictPartitionSet 3, franklinInv (franklinInv S) = S := by native_decide
example : ∀ S ∈ StrictPartitionSet 4, franklinInv (franklinInv S) = S := by native_decide
example : ∀ S ∈ StrictPartitionSet 5, franklinInv (franklinInv S) = S := by native_decide
example : ∀ S ∈ StrictPartitionSet 6, franklinInv (franklinInv S) = S := by native_decide
example : ∀ S ∈ StrictPartitionSet 7, franklinInv (franklinInv S) = S := by native_decide

open Finset in
/-- Non-fixed elements have card differing by 1 (sign reversal). -/
theorem franklinInv_card (S : Finset Nat) (hpos : ∀ x ∈ S, 0 < x)
    (hne_inv : franklinInv S ≠ S) :
    (franklinInv S).card + 1 = S.card ∨ S.card + 1 = (franklinInv S).card := by
  have hne : S.Nonempty := by
    by_contra h
    have h_empty := Finset.not_nonempty_iff_eq_empty.mp h; subst h_empty
    exact hne_inv franklinInv_empty
  by_cases h_le : S.min' hne ≤ topStaircase S
  · by_cases h_fixed : S.min' hne = topStaircase S ∧
        (S.max' hne - topStaircase S + 1 = S.min' hne ∨
         S.min' hne ∈ (range (topStaircase S)).image (S.max' hne - ·))
    · exfalso; exact hne_inv (franklinInv_fixed_le hne h_le h_fixed)
    · left
      rw [franklinInv_eq_up hne h_le h_fixed]
      set σ := S.min' hne; set m := S.max' hne; set T := (range σ).image (m - ·)
      have hT_sub : T ⊆ S := topParts_subset hne σ h_le
      have hσ_S : σ ∈ S := Finset.min'_mem S hne
      have hσ_le_m : σ ≤ m := Finset.min'_le S m (Finset.max'_mem S hne)
      have hT_card : T.card = σ := card_range_image_sub m σ (by omega)
      have hσ_not_T : σ ∉ T := by
        simp only [T, Finset.mem_image, Finset.mem_range]
        rintro ⟨j, hj, heq⟩
        by_cases hσt : σ < topStaircase S
        · have := Finset.min'_le S (m - σ) (topStaircase_mem hne σ hσt); omega
        · exact h_fixed ⟨Nat.le_antisymm h_le (Nat.not_lt.mp hσt),
            Or.inr (by rw [Nat.le_antisymm h_le (Nat.not_lt.mp hσt)]
                       simp [Finset.mem_image, Finset.mem_range]
                       exact ⟨j, Nat.le_antisymm h_le (Nat.not_lt.mp hσt) ▸ hj,
                              Nat.le_antisymm h_le (Nat.not_lt.mp hσt) ▸ heq⟩)⟩
      have hσ_sdiff : σ ∈ S \ T := Finset.mem_sdiff.mpr ⟨hσ_S, hσ_not_T⟩
      have hdisj : Disjoint ((S \ T).erase σ) (T.image (· + 1)) := by
        rw [Finset.disjoint_left]; intro x hx_l hx_r
        have hx_S := ((Finset.mem_erase.mp hx_l).2 |> Finset.mem_sdiff.mp).1
        have hx_le : x ≤ m := Finset.le_max' S x hx_S
        rw [Finset.mem_image] at hx_r; obtain ⟨y, hy, rfl⟩ := hx_r
        simp only [T, Finset.mem_image, Finset.mem_range] at hy
        obtain ⟨j, hj, rfl⟩ := hy
        have : 1 ≤ j := by omega
        have hmem : m - (j - 1) ∈ T := by
          simp [T, Finset.mem_image, Finset.mem_range]; exact ⟨j - 1, by omega, by omega⟩
        have : m - j + 1 = m - (j - 1) := by omega
        have hx_notT := ((Finset.mem_erase.mp hx_l).2 |> Finset.mem_sdiff.mp).2
        rw [this] at hx_notT; exact hx_notT hmem
      have hT_le_S : T.card ≤ S.card := Finset.card_le_card hT_sub
      have hσ_lt_S : σ < S.card := by
        have := Finset.card_pos.mpr ⟨σ, hσ_sdiff⟩
        have := Finset.card_sdiff_of_subset hT_sub; omega
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hσ_sdiff,
          card_image_succ', hT_card, Finset.card_sdiff_of_subset hT_sub]; omega
  · by_cases h_fixed : S.max' hne - topStaircase S = topStaircase S ∨
        topStaircase S ∈ S \ (range (topStaircase S)).image (S.max' hne - ·)
    · exfalso; exact hne_inv (franklinInv_fixed_gt hne h_le h_fixed)
    · right
      rw [franklinInv_eq_down hne h_le h_fixed]
      set m := S.max' hne; set t := topStaircase S; set T := (range t).image (m - ·)
      have hT_sub : T ⊆ S := topParts_subset hne t le_rfl
      have hT_pos : ∀ x ∈ T, 0 < x := fun x hx => hpos x (hT_sub hx)
      have h_gt : t < S.min' hne := Nat.lt_of_not_le h_le
      have hT_card : T.card = t := card_range_image_sub m t (by
        have := Finset.min'_le S m (Finset.max'_mem S hne); omega)
      have ht_not_S : t ∉ S := by intro h; have := Finset.min'_le S t h; omega
      have ht_pos : 0 < t := topStaircase_pos hne
      have hm_gt_2t : m > 2 * t := by
        have h_mt1 := topStaircase_mem hne (t - 1) (by omega)
        have := Finset.min'_le S _ h_mt1; omega
      have hdisj_rs : Disjoint (S \ T) (T.image (· - 1)) := by
        rw [Finset.disjoint_left]; intro x hx_r hx_s
        have hx_notT := (Finset.mem_sdiff.mp hx_r).2
        rw [Finset.mem_image] at hx_s; obtain ⟨y, hy, rfl⟩ := hx_s
        simp only [T, Finset.mem_image, Finset.mem_range] at hy
        obtain ⟨j, hj, rfl⟩ := hy
        by_cases hjt : j + 1 < t
        · have : m - j - 1 = m - (j + 1) := by omega
          rw [this] at hx_notT
          exact hx_notT (by simp [T, Finset.mem_image, Finset.mem_range]; exact ⟨j+1, hjt, rfl⟩)
        · have : m - j - 1 = m - t := by omega
          rw [this] at hx_r
          exact topStaircase_stop hne (by omega) (Finset.mem_sdiff.mp hx_r).1
      have ht_not_union : t ∉ (S \ T) ∪ T.image (· - 1) := by
        simp only [Finset.mem_union, not_or]
        exact ⟨fun h => ht_not_S (Finset.mem_sdiff.mp h).1,
               fun h => by rw [Finset.mem_image] at h; obtain ⟨y, hy, hyt⟩ := h;
                           simp [T, Finset.mem_image, Finset.mem_range] at hy;
                           obtain ⟨j, hj, rfl⟩ := hy; omega⟩
      have hdisj_all : Disjoint ((S \ T) ∪ T.image (· - 1)) {t} := by
        rw [Finset.disjoint_right]; intro x hx
        simp only [Finset.mem_singleton] at hx; subst hx; exact ht_not_union
      have hT_le_S : T.card ≤ S.card := Finset.card_le_card hT_sub
      rw [Finset.card_union_of_disjoint hdisj_all, Finset.card_union_of_disjoint hdisj_rs,
          Finset.card_singleton, card_image_pred' T hT_pos, hT_card,
          Finset.card_sdiff_of_subset hT_sub]; omega

/-! ### Fixed-point characterization and pentagonal number helpers -/

section FixedPointCharacterization

open Finset

-- Forward: fixed → Type A or Type B
private theorem fixed_implies_pentagonal {S : Finset Nat} (hne : S.Nonempty)
    (hpos : ∀ x ∈ S, 0 < x) (hfixed : franklinInv S = S) :
    (∃ k, k ≥ 1 ∧ (S = Finset.Icc k (2 * k - 1) ∨ S = Finset.Icc (k + 1) (2 * k))) := by
  have hσ_pos : 0 < S.min' hne := hpos _ (Finset.min'_mem S hne)
  have ht_pos : 0 < topStaircase S := topStaircase_pos hne
  have hσ_le_m : S.min' hne ≤ S.max' hne := Finset.min'_le S _ (Finset.max'_mem S hne)
  by_cases h_le : S.min' hne ≤ topStaircase S
  · -- σ ≤ t: must be Type A
    by_contra h_no_pent; push_neg at h_no_pent
    have h_fc : S.min' hne = topStaircase S ∧ (S.max' hne - topStaircase S + 1 = S.min' hne ∨
        S.min' hne ∈ (range (topStaircase S)).image (S.max' hne - ·)) := by
      by_contra h_nfc
      have h_eq := franklinInv_eq_up hne h_le h_nfc; rw [hfixed] at h_eq
      have hm1 : S.max' hne + 1 ∈ (S \ (range (S.min' hne)).image (S.max' hne - ·)).erase (S.min' hne) ∪
          ((range (S.min' hne)).image (S.max' hne - ·)).image (· + 1) :=
        Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
          ⟨S.max' hne, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hσ_pos, by omega⟩, by omega⟩))
      rw [← h_eq] at hm1
      exact absurd (Finset.le_max' S _ hm1) (by omega)
    have hσ_eq_t := h_fc.1
    have hm_bound : S.max' hne = 2 * S.min' hne - 1 := by
      rcases h_fc.2 with h | h
      · have : S.min' hne ≤ S.max' hne - topStaircase S + 1 := by omega
        omega
      · simp [Finset.mem_image, Finset.mem_range] at h
        obtain ⟨j, hj, heq⟩ := h
        have hj_lt : j < S.min' hne := hσ_eq_t ▸ hj
        have := Finset.min'_le S (S.max' hne - (S.min' hne - 1)) (by
          have : S.min' hne - 1 < topStaircase S := by omega
          exact topStaircase_mem hne _ this)
        omega
    have hT_sub := topParts_subset hne (S.min' hne) h_le
    have hS_eq : S = Icc (S.min' hne) (2 * S.min' hne - 1) := by
      apply Finset.Subset.antisymm
      · intro x hx; exact Finset.mem_Icc.mpr
          ⟨Finset.min'_le S x hx, by have := Finset.le_max' S x hx; omega⟩
      · intro x hx
        have hx_ge := (Finset.mem_Icc.mp hx).1
        have hx_le := (Finset.mem_Icc.mp hx).2
        have hx_le_m : x ≤ S.max' hne := by omega
        have h_idx : S.max' hne - x < S.min' hne := by omega
        have h_val : S.max' hne - (S.max' hne - x) = x := by omega
        exact hT_sub (Finset.mem_image.mpr ⟨S.max' hne - x, Finset.mem_range.mpr h_idx, h_val⟩)
    exact absurd hS_eq (h_no_pent (S.min' hne) hσ_pos).1
  · -- σ > t: must be Type B
    by_contra h_no_pent; push_neg at h_no_pent
    have h_fc : S.max' hne - topStaircase S = topStaircase S ∨
        topStaircase S ∈ S \ (range (topStaircase S)).image (S.max' hne - ·) := by
      by_contra h_nfc
      have h_eq := franklinInv_eq_down hne h_le h_nfc; rw [hfixed] at h_eq
      have : topStaircase S ∉ S := by
        intro h; have := Finset.min'_le S _ h; exact absurd h_le (by omega)
      have ht_mem : topStaircase S ∈ (S \ (range (topStaircase S)).image (S.max' hne - ·)) ∪
          ((range (topStaircase S)).image (S.max' hne - ·)).image (· - 1) ∪ {topStaircase S} :=
        Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
      rw [← h_eq] at ht_mem; exact this ht_mem
    rcases h_fc with h | h
    · have hT_sub := topParts_subset hne (topStaircase S) le_rfl
      have hS_eq : S = Icc (topStaircase S + 1) (2 * topStaircase S) := by
        apply Finset.Subset.antisymm
        · intro x hx; exact Finset.mem_Icc.mpr
            ⟨by have := Finset.min'_le S x hx; omega,
             by have := Finset.le_max' S x hx; omega⟩
        · intro x hx
          have hx_ge := (Finset.mem_Icc.mp hx).1
          have hx_le := (Finset.mem_Icc.mp hx).2
          have hx_le_m : x ≤ S.max' hne := by omega
          exact hT_sub (by simp [Finset.mem_image, Finset.mem_range]
                           exact ⟨S.max' hne - x, by omega, by omega⟩)
      exact absurd hS_eq (h_no_pent (topStaircase S) ht_pos).2
    · -- t ∈ S \ topParts → t ∈ S, but min > t. Contradiction.
      have : topStaircase S ∉ S := by
        intro hm; have := Finset.min'_le S _ hm; exact absurd h_le (by omega)
      exact this (Finset.mem_sdiff.mp h).1

-- Backward: pentagonal → fixed
private theorem icc_min' (a b : Nat) (h : a ≤ b) :
    (Icc a b).min' ⟨a, Finset.mem_Icc.mpr ⟨le_refl _, h⟩⟩ = a := by
  apply le_antisymm
  · apply Finset.min'_le; exact Finset.mem_Icc.mpr ⟨le_refl _, h⟩
  · apply Finset.le_min'; intro x hx; exact (Finset.mem_Icc.mp hx).1

private theorem icc_max' (a b : Nat) (h : a ≤ b) :
    (Icc a b).max' ⟨b, Finset.mem_Icc.mpr ⟨h, le_refl _⟩⟩ = b := by
  apply le_antisymm
  · apply Finset.max'_le; intro x hx; exact (Finset.mem_Icc.mp hx).2
  · apply Finset.le_max'; exact Finset.mem_Icc.mpr ⟨h, le_refl _⟩

private theorem icc_ts_A (k : Nat) (hk : 1 ≤ k) : topStaircase (Icc k (2 * k - 1)) = k := by
  have hne : (Icc k (2 * k - 1)).Nonempty := ⟨k, Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩⟩
  apply topStaircase_eq_of hne k (by rw [icc_max' k (2*k-1) (by omega)]; omega)
  · intro i hi; rw [icc_max' k (2*k-1) (by omega)]; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro _; rw [icc_max' k (2*k-1) (by omega)]
    simp only [Finset.mem_Icc, not_and_or, not_le]; left; omega

private theorem icc_ts_B (k : Nat) (hk : 1 ≤ k) : topStaircase (Icc (k + 1) (2 * k)) = k := by
  have hne : (Icc (k+1) (2*k)).Nonempty := ⟨k+1, Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩⟩
  apply topStaircase_eq_of hne k (by rw [icc_max' (k+1) (2*k) (by omega)]; omega)
  · intro i hi; rw [icc_max' (k+1) (2*k) (by omega)]; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro _; rw [icc_max' (k+1) (2*k) (by omega)]
    simp only [Finset.mem_Icc, not_and_or, not_le]; left; omega

private theorem pentagonal_implies_fixed {S : Finset Nat} (_hne : S.Nonempty)
    (_hpos : ∀ x ∈ S, 0 < x)
    (h : ∃ k, k ≥ 1 ∧ (S = Finset.Icc k (2 * k - 1) ∨ S = Finset.Icc (k + 1) (2 * k))) :
    franklinInv S = S := by
  obtain ⟨k, hk, hS | hS⟩ := h
  · rw [hS]
    have hne := (⟨k, Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩⟩ : (Icc k (2*k-1)).Nonempty)
    apply franklinInv_fixed_le hne
    · rw [icc_min' k (2*k-1) (by omega), icc_ts_A k hk]
    · rw [icc_min' k (2*k-1) (by omega), icc_max' k (2*k-1) (by omega), icc_ts_A k hk]
      exact ⟨rfl, Or.inl (by omega)⟩
  · rw [hS]
    have hne := (⟨k+1, Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩⟩ : (Icc (k+1) (2*k)).Nonempty)
    apply franklinInv_fixed_gt hne
    · rw [icc_min' (k+1) (2*k) (by omega), icc_ts_B k hk]; omega
    · left; rw [icc_max' (k+1) (2*k) (by omega), icc_ts_B k hk]; omega

private theorem franklinInv_fixed_iff_pentagonal {S : Finset Nat} (hne : S.Nonempty)
    (hpos : ∀ x ∈ S, 0 < x) :
    franklinInv S = S ↔
      (∃ k, k ≥ 1 ∧ (S = Finset.Icc k (2 * k - 1) ∨ S = Finset.Icc (k + 1) (2 * k))) :=
  ⟨fixed_implies_pentagonal hne hpos, pentagonal_implies_fixed hne hpos⟩

end FixedPointCharacterization

/-! ### Pentagonal number arithmetic -/

section PentagonalArithmetic

open Finset

private theorem even_pent (a : Nat) : 2 ∣ (a + 1) * (3 * a + 2) := by
  induction a with
  | zero => exact ⟨1, by decide⟩
  | succ n ih => obtain ⟨m, hm⟩ := ih; exact ⟨m + 3 * n + 4, by nlinarith⟩

private theorem pent_A_inj {a b : Nat} (h : a * (3 * a - 1) / 2 = b * (3 * b - 1) / 2) : a = b := by
  rcases a with _ | a <;> rcases b with _ | b
  · rfl
  · exfalso; simp only [Nat.zero_mul, Nat.zero_div] at h
    obtain ⟨m, hm⟩ := even_pent b
    rw [show 3*(b+1)-1 = 3*b+2 from by omega] at h
    rw [hm, Nat.mul_div_cancel_left _ (by omega : 0 < 2)] at h
    have : m ≥ 1 := by nlinarith
    omega
  · exfalso; simp only [Nat.zero_mul, Nat.zero_div] at h
    obtain ⟨m, hm⟩ := even_pent a
    rw [show 3*(a+1)-1 = 3*a+2 from by omega] at h
    rw [hm, Nat.mul_div_cancel_left _ (by omega : 0 < 2)] at h
    have : m ≥ 1 := by nlinarith
    omega
  · rw [show 3*(a+1)-1 = 3*a+2 from by omega, show 3*(b+1)-1 = 3*b+2 from by omega] at h
    obtain ⟨ma, hma⟩ := even_pent a; obtain ⟨mb, hmb⟩ := even_pent b
    rw [hma, hmb, Nat.mul_div_cancel_left _ (by omega : 0 < 2),
        Nat.mul_div_cancel_left _ (by omega : 0 < 2)] at h
    have h2 : (a+1)*(3*a+2) = (b+1)*(3*b+2) := by nlinarith
    have h3 : ((a:Int)-b) * (3*(↑a+↑b)+5) = 0 := by push_cast at h2 ⊢; nlinarith
    rcases mul_eq_zero.mp h3 with h4 | h4
    · omega
    · exfalso; linarith [Int.natCast_nonneg a, Int.natCast_nonneg b]

private theorem pentagonalSign_type_A (k : Nat) :
    pentagonalSign (k * (3 * k - 1) / 2) = (-1 : Int) ^ k := by
  simp only [pentagonalSign]; split
  · rename_i j hj
    have hpred := (List.find?_eq_some_iff_append.mp hj).1
    simp only [decide_eq_true_eq] at hpred
    exact congrArg ((-1 : Int) ^ ·) (pent_A_inj hpred.symm)
  · rename_i h_none; exfalso
    rw [List.find?_eq_none] at h_none
    have hk_le : k ≤ k * (3 * k - 1) / 2 := by
      rcases k with _ | k
      · simp
      · have h3 : 3 * (k + 1) - 1 = 3 * k + 2 := by omega
        have : (k + 1) * (3 * (k + 1) - 1) = (k + 1) * (3 * k + 2) := by rw [h3]
        obtain ⟨m, hm⟩ := even_pent k
        have hm2 : (k + 1) * (3 * (k + 1) - 1) / 2 = m := by rw [this, hm]; omega
        have : m ≥ k + 1 := by nlinarith
        omega
    have := h_none k (List.mem_range.mpr (by omega)); simp at this

private theorem even_pent_B (a : Nat) (ha : 0 < a) : 2 ∣ a * (3 * a + 1) := by
  rcases a with _ | n; · omega
  induction n with
  | zero => exact ⟨2, by decide⟩
  | succ k ih => obtain ⟨m, hm⟩ := ih (by omega); exact ⟨m + 3 * k + 5, by nlinarith⟩

private theorem pent_B_inj {a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (h : a * (3 * a + 1) / 2 = b * (3 * b + 1) / 2) : a = b := by
  obtain ⟨ma, hma⟩ := even_pent_B a ha; obtain ⟨mb, hmb⟩ := even_pent_B b hb
  rw [hma, hmb, Nat.mul_div_cancel_left _ (by omega : 0 < 2),
      Nat.mul_div_cancel_left _ (by omega : 0 < 2)] at h
  have h2 : a * (3 * a + 1) = b * (3 * b + 1) := by nlinarith
  have h3 : ((a : Int) - b) * (3 * (↑a + ↑b) + 1) = 0 := by push_cast at h2 ⊢; nlinarith
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact_mod_cast show (a : Int) = b by linarith
  · exfalso; linarith [Int.natCast_nonneg a, Int.natCast_nonneg b]

private theorem pent_B_not_A {k j : Nat} (hk : 0 < k)
    (h : k * (3 * k + 1) / 2 = j * (3 * j - 1) / 2) : False := by
  rcases j with _ | j
  · simp only [Nat.zero_mul, Nat.zero_div] at h
    obtain ⟨m, hm⟩ := even_pent_B k hk
    rw [hm, Nat.mul_div_cancel_left _ (by omega : 0 < 2)] at h
    have : m ≥ 1 := by nlinarith
    omega
  · rw [show 3*(j+1)-1 = 3*j+2 from by omega] at h
    obtain ⟨mk, hmk⟩ := even_pent_B k hk; obtain ⟨mj, hmj⟩ := even_pent j
    rw [hmk, hmj, Nat.mul_div_cancel_left _ (by omega : 0 < 2),
        Nat.mul_div_cancel_left _ (by omega : 0 < 2)] at h
    have h2 : k * (3*k+1) = (j+1) * (3*j+2) := by nlinarith
    by_cases hkj : k ≤ j
    · nlinarith [Nat.mul_le_mul_right (3*k+1) (show k ≤ j from hkj)]
    · push_neg at hkj; by_cases hkj2 : k = j + 1
      · subst hkj2; nlinarith
      · nlinarith [Nat.mul_le_mul_right (3*(j+2)+1) (show j + 2 ≤ k from by omega)]

private theorem pentagonalSign_type_B (k : Nat) (hk : 0 < k) :
    pentagonalSign (k * (3 * k + 1) / 2) = (-1 : Int) ^ k := by
  simp only [pentagonalSign]; split
  · rename_i j hj
    have hpred := (List.find?_eq_some_iff_append.mp hj).1
    simp only [decide_eq_true_eq] at hpred
    exact (pent_B_not_A hk hpred).elim
  · split
    · rename_i j hj
      have hpred := (List.find?_eq_some_iff_append.mp hj).1
      simp only [decide_eq_true_eq] at hpred
      exact congrArg ((-1 : Int) ^ ·) (pent_B_inj hpred.1 hk hpred.2.symm)
    · rename_i _ h_none; exfalso
      rw [List.find?_eq_none] at h_none
      have hk_le : k ≤ k * (3 * k + 1) / 2 := by
        obtain ⟨m, hm⟩ := even_pent_B k hk
        have : k * (3 * k + 1) ≥ 4 * k := by nlinarith
        have : m ≥ 2 * k := by omega
        omega
      have := h_none k (List.mem_range.mpr (by omega)); simp [hk] at this

-- Gauss sum helpers

private lemma weight_int (D B A k : Int)
    (h_sdiff : D + B = A) (h2k : A * 2 = 2 * k * (2 * k - 1))
    (hk2 : B * 2 = k * (k - 1)) :
    2 * D = k * (3 * k - 1) := by nlinarith

private lemma weight_B_int (D B A k : Int)
    (h_sdiff : D + B = A) (h2k : A * 2 = (2 * k + 1) * (2 * k))
    (hk2 : B * 2 = (k + 1) * k) :
    2 * D = k * (3 * k + 1) := by nlinarith

private theorem type_A_weight (k : Nat) (hk : 1 ≤ k) :
    (Finset.Icc k (2*k-1)).sum id = k * (3 * k - 1) / 2 := by
  obtain ⟨p, hp⟩ := even_pent (k-1)
  rw [show k-1+1 = k from by omega, show 3*(k-1)+2 = 3*k-1 from by omega] at hp
  suffices h : 2 * (Finset.Icc k (2*k-1)).sum id = k * (3*k-1) by omega
  have h_eq : Finset.Icc k (2*k-1) = Finset.range (2*k) \ Finset.range k := by
    ext x; simp [Finset.mem_range, Finset.mem_Icc]; omega
  rw [h_eq]; simp only [id]
  have h_sub : Finset.range k ⊆ Finset.range (2*k) := by
    intro x hx; exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega)
  set A := (Finset.range (2*k)).sum fun x => x
  set B := (Finset.range k).sum fun x => x
  set D := (Finset.range (2*k) \ Finset.range k).sum fun x => x
  have h_sdiff := (Finset.sum_sdiff h_sub (f := fun x => x)).symm
  have h2k_mul := Finset.sum_range_id_mul_two (2*k)
  have hk2_mul := Finset.sum_range_id_mul_two k
  have h_sdiff_int : (D : Int) + B = A := by exact_mod_cast h_sdiff.symm
  have hA_eq : A = (Finset.range (2*k)).sum id := by simp [A, id]
  have hB_eq : B = (Finset.range k).sum id := by simp [B, id]
  have h2k_mul : A * 2 = (2*k) * (2*k-1) := by rw [hA_eq]; exact Finset.sum_range_id_mul_two (2*k)
  have hk2_mul : B * 2 = k * (k-1) := by rw [hB_eq]; exact Finset.sum_range_id_mul_two k
  have h2k_add : A * 2 + 2 * k = 2 * k * (2 * k) := by
    suffices (↑(A*2+2*k) : Int) = ↑(2*k*(2*k)) by exact_mod_cast this
    push_cast; have : (↑(2*k-1) : Int) = 2*↑k-1 := by omega
    nlinarith
  have hk2_add : B * 2 + k = k * k := by
    suffices (↑(B*2+k) : Int) = ↑(k*k) by exact_mod_cast this
    push_cast; have : (↑(k-1) : Int) = ↑k-1 := by omega
    nlinarith
  have h2k_int : (A : Int) * 2 = 2 * ↑k * (2 * ↑k - 1) := by
    have : (A : Int) * 2 + 2 * ↑k = 2 * ↑k * (2 * ↑k) := by exact_mod_cast h2k_add
    linarith
  have hk2_int : (B : Int) * 2 = ↑k * (↑k - 1) := by
    have : (B : Int) * 2 + ↑k = ↑k * ↑k := by exact_mod_cast hk2_add
    linarith
  have h := weight_int ↑D ↑B ↑A ↑k h_sdiff_int h2k_int hk2_int
  exact_mod_cast show (2 * D : Int) = ↑(k * (3*k-1)) by
    rw [show (↑(k*(3*k-1)) : Int) = ↑k * ↑(3*k-1) from by push_cast; ring]
    rw [show (↑(3*k-1) : Int) = 3*↑k - 1 from by omega]; exact h

private theorem type_B_weight (k : Nat) (hk : 1 ≤ k) :
    (Finset.Icc (k+1) (2*k)).sum id = k * (3 * k + 1) / 2 := by
  obtain ⟨p, hp⟩ := even_pent_B k hk
  suffices h : 2 * (Finset.Icc (k+1) (2*k)).sum id = k * (3*k+1) by omega
  have h_eq : Finset.Icc (k+1) (2*k) = Finset.range (2*k+1) \ Finset.range (k+1) := by
    ext x; simp [Finset.mem_range, Finset.mem_Icc]; omega
  rw [h_eq]; simp only [id]
  have h_sub : Finset.range (k+1) ⊆ Finset.range (2*k+1) := by
    intro x hx; exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega)
  set A := (Finset.range (2*k+1)).sum fun x => x
  set B := (Finset.range (k+1)).sum fun x => x
  set D := (Finset.range (2*k+1) \ Finset.range (k+1)).sum fun x => x
  have h_sdiff := (Finset.sum_sdiff h_sub (f := fun x => x)).symm
  have h_sdiff_int : (D : Int) + B = A := by exact_mod_cast h_sdiff.symm
  have h2k_mul := Finset.sum_range_id_mul_two (2*k+1)
  have hk2_mul := Finset.sum_range_id_mul_two (k+1)
  have h2k_int : (A : Int) * 2 = (2*↑k+1) * (2*↑k) := by
    have : A * 2 = (2*k+1) * (2*k+1-1) := h2k_mul
    have : (A : Int) * 2 = ↑((2*k+1) * (2*k+1-1)) := by exact_mod_cast this
    simp only [show 2*k+1-1 = 2*k from by omega] at this; exact_mod_cast this
  have hk2_int : (B : Int) * 2 = (↑k+1) * ↑k := by
    have : B * 2 = (k+1) * ((k+1)-1) := hk2_mul
    have : (B : Int) * 2 = ↑((k+1) * ((k+1)-1)) := by exact_mod_cast this
    simp only [show (k+1)-1 = k from by omega] at this; exact_mod_cast this
  have h := weight_B_int ↑D ↑B ↑A ↑k h_sdiff_int h2k_int hk2_int
  exact_mod_cast show (2 * D : Int) = ↑(k*(3*k+1)) by push_cast; linarith

-- Assembly helpers

private theorem identify_fixed {n : Nat} (hn : 0 < n) {S : Finset Nat}
    (hS : S ∈ StrictPartitionSet n) (hf : franklinInv S = S) :
    ∃ k, k ≥ 1 ∧ (S = Finset.Icc k (2*k-1) ∧ n = k*(3*k-1)/2 ∨
                    S = Finset.Icc (k+1) (2*k) ∧ n = k*(3*k+1)/2) := by
  have hne : S.Nonempty := by
    by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h; subst h
    simp [StrictPartitionSet, Finset.mem_filter] at hS; omega
  have hpos : ∀ x ∈ S, 0 < x := by simp [StrictPartitionSet, Finset.mem_filter] at hS; exact hS.2.1
  have hw := (by simp [StrictPartitionSet, Finset.mem_filter] at hS; exact hS.2.2 : S.sum id = n)
  rw [franklinInv_fixed_iff_pentagonal hne hpos] at hf
  obtain ⟨k, hk, hSk | hSk⟩ := hf
  · exact ⟨k, hk, Or.inl ⟨hSk, by rw [hSk] at hw; rw [← hw, type_A_weight k hk]⟩⟩
  · exact ⟨k, hk, Or.inr ⟨hSk, by rw [hSk] at hw; rw [← hw, type_B_weight k hk]⟩⟩

private theorem icc_A_mem_SPS (k : Nat) (hk : 1 ≤ k) :
    Finset.Icc k (2*k-1) ∈ StrictPartitionSet (k*(3*k-1)/2) := by
  simp only [StrictPartitionSet, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨?_, ?_, type_A_weight k hk⟩
  · intro x hx; exact Finset.mem_range.mpr (by
      have hle : x ≤ (Finset.Icc k (2*k-1)).sum id := by
        calc x = ({x} : Finset Nat).sum id := by simp
          _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.singleton_subset_iff.mpr hx)
      rw [type_A_weight k hk] at hle; omega)
  · intro x hx; have := (Finset.mem_Icc.mp hx).1; omega

private theorem icc_B_mem_SPS (k : Nat) (hk : 1 ≤ k) :
    Finset.Icc (k+1) (2*k) ∈ StrictPartitionSet (k*(3*k+1)/2) := by
  simp only [StrictPartitionSet, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨?_, ?_, type_B_weight k hk⟩
  · intro x hx; exact Finset.mem_range.mpr (by
      have hle : x ≤ (Finset.Icc (k+1) (2*k)).sum id := by
        calc x = ({x} : Finset Nat).sum id := by simp
          _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.singleton_subset_iff.mpr hx)
      rw [type_B_weight k hk] at hle; omega)
  · intro x hx; have := (Finset.mem_Icc.mp hx).1; omega

private theorem type_A_fixed (k : Nat) (hk : 1 ≤ k) :
    franklinInv (Finset.Icc k (2*k-1)) = Finset.Icc k (2*k-1) :=
  (pentagonal_implies_fixed
    ⟨k, Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩⟩
    (fun x hx => by have := (Finset.mem_Icc.mp hx).1; omega)
    ⟨k, hk, Or.inl rfl⟩)

private theorem type_B_fixed (k : Nat) (hk : 1 ≤ k) :
    franklinInv (Finset.Icc (k+1) (2*k)) = Finset.Icc (k+1) (2*k) :=
  (pentagonal_implies_fixed
    ⟨k+1, Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩⟩
    (fun x hx => by have := (Finset.mem_Icc.mp hx).1; omega)
    ⟨k, hk, Or.inr rfl⟩)

private theorem pent_le_A (k : Nat) (hk : 1 ≤ k) : k ≤ k * (3*k-1) / 2 := by
  rcases k with _ | k; · omega
  obtain ⟨m, hm⟩ := even_pent k
  have : m ≥ k + 1 := by nlinarith
  have h3 : (k+1) * (3*(k+1)-1) = 2*m := by rw [show 3*(k+1)-1 = 3*k+2 from by omega]; exact hm
  omega

private theorem pent_le_B (k : Nat) (hk : 1 ≤ k) : k ≤ k * (3*k+1) / 2 := by
  obtain ⟨m, hm⟩ := even_pent_B k (by omega)
  suffices m ≥ k by omega
  nlinarith

end PentagonalArithmetic

/-! ### Sign cancellation and final assembly -/

section FinalAssembly

open Finset

private theorem hpos_of_mem {n : Nat} {S : Finset Nat} (hS : S ∈ StrictPartitionSet n) :
    ∀ x ∈ S, 0 < x := by
  simp only [StrictPartitionSet, Finset.mem_filter, Finset.mem_powerset] at hS; exact hS.2.1

private theorem sign_cancel {S : Finset Nat} (hpos : ∀ x ∈ S, 0 < x)
    (hne : franklinInv S ≠ S) :
    (-1 : Int) ^ S.card + (-1 : Int) ^ (franklinInv S).card = 0 := by
  rcases franklinInv_card S hpos hne with h | h
  · rw [show S.card = (franklinInv S).card + 1 from by omega]; ring_nf
  · rw [show (franklinInv S).card = S.card + 1 from by omega]; ring_nf

private theorem sum_nonfixed_zero (n : Nat) :
    ∑ S ∈ (StrictPartitionSet n).filter (fun S => franklinInv S ≠ S),
      (-1 : Int) ^ S.card = 0 := by
  apply Finset.sum_involution (fun S _ => franklinInv S)
  · intro S hS; exact sign_cancel (hpos_of_mem (Finset.mem_filter.mp hS).1) (Finset.mem_filter.mp hS).2
  · intro S hS _; exact (Finset.mem_filter.mp hS).2
  · intro S hS
    rw [Finset.mem_filter]; refine ⟨franklinInv_mem_StrictPartitionSet (Finset.mem_filter.mp hS).1, ?_⟩
    intro heq; rw [franklinInv_involutive S (hpos_of_mem (Finset.mem_filter.mp hS).1)] at heq
    exact (Finset.mem_filter.mp hS).2 heq.symm
  · intro S hS; exact franklinInv_involutive S (hpos_of_mem (Finset.mem_filter.mp hS).1)

private theorem fixed_sum_eq_pentagonalSign (n : Nat) :
    ∑ S ∈ (StrictPartitionSet n).filter (fun S => franklinInv S = S), (-1:Int)^S.card =
    pentagonalSign n := by
  rcases n with _ | n
  · decide
  · simp only [pentagonalSign]; split
    · rename_i k hfind
      have hpred := (List.find?_eq_some_iff_append.mp hfind).1
      simp only [decide_eq_true_eq] at hpred
      have hk : 1 ≤ k := by rcases k with _ | k <;> [simp at hpred; omega]
      have hfilt : (StrictPartitionSet (n+1)).filter (fun S => franklinInv S = S) = {Icc k (2*k-1)} := by
        ext S; simp only [mem_filter, mem_singleton]; constructor
        · intro ⟨hS, hf⟩
          obtain ⟨j, hj, (⟨hSj, hnj⟩ | ⟨hSj, hnj⟩)⟩ := identify_fixed (by omega) hS hf
          · have := pent_A_inj (show j*(3*j-1)/2 = k*(3*k-1)/2 by omega); subst this; exact hSj
          · exact absurd (show j*(3*j+1)/2 = k*(3*k-1)/2 by omega) (fun h => pent_B_not_A (by omega) h)
        · intro h; subst h
          exact ⟨by rw [hpred]; exact icc_A_mem_SPS k hk, type_A_fixed k hk⟩
      rw [hfilt, sum_singleton]; congr 1; rw [Nat.card_Icc]; omega
    · -- First match returned none. Split on second match.
      rename_i h_nA_raw
      have h_nA : ∀ j ∈ List.range (n+1+1), ¬(decide (n+1 = j*(3*j-1)/2) = true) := by
        rwa [List.find?_eq_none] at h_nA_raw
      split
      · rename_i k hfind
        have hpred := (List.find?_eq_some_iff_append.mp hfind).1
        simp only [decide_eq_true_eq] at hpred
        have hk : 1 ≤ k := hpred.1
        have hfilt : (StrictPartitionSet (n+1)).filter (fun S => franklinInv S = S) = {Icc (k+1) (2*k)} := by
          ext S; simp only [mem_filter, mem_singleton]; constructor
          · intro ⟨hS, hf⟩
            obtain ⟨j, hj, (⟨hSj, hnj⟩ | ⟨hSj, hnj⟩)⟩ := identify_fixed (by omega) hS hf
            · exfalso
              have hj_range : j ∈ List.range (n+1+1) := List.mem_range.mpr (by
                have := pent_le_A j hj; omega)
              have := h_nA j hj_range; simp [hnj] at this
            · have := pent_B_inj (show 0 < j by omega) (show 0 < k by omega) (show j*(3*j+1)/2 = k*(3*k+1)/2 by omega)
              subst this; exact hSj
          · intro h; subst h
            exact ⟨by rw [hpred.2]; exact icc_B_mem_SPS k hk, type_B_fixed k hk⟩
        rw [hfilt, sum_singleton]; congr 1; rw [Nat.card_Icc]; omega
      · rename_i h_nB_raw
        have h_nB : ∀ j ∈ List.range (n+1+1), ¬(decide (0 < j ∧ n+1 = j*(3*j+1)/2) = true) := by
          rwa [List.find?_eq_none] at h_nB_raw
        suffices h : (StrictPartitionSet (n+1)).filter (fun S => franklinInv S = S) = ∅ by
          rw [h, sum_empty]
        ext S; simp only [mem_filter]; constructor
        · intro ⟨hS, hf⟩
          obtain ⟨k, hk, (⟨_, hnk⟩ | ⟨_, hnk⟩)⟩ := identify_fixed (by omega) hS hf
          · exact absurd (h_nA k (List.mem_range.mpr (by have := pent_le_A k hk; omega))) (by simp [hnk])
          · have hk_range := List.mem_range.mpr (show k < n+1+1 by have := pent_le_B k hk; omega)
            have := h_nB k hk_range
            simp only [decide_eq_true_eq] at this
            exact absurd ⟨by omega, hnk⟩ this
        · simp

end FinalAssembly

/-- **Euler's Pentagonal Number Theorem (combinatorial form via Franklin involution).**
The signed count of strict partitions of n equals the pentagonal indicator.

Verified instances: n = 0 through 15 (covers pentagonal numbers 0,1,2,5,7,12,15).
General proof: requires Franklin involution on Finset + Finset.sum_involution. -/
theorem euler_pentagonal_combinatorial (n : Nat) :
    signedStrictPartitionCount n = pentagonalSign n := by
  simp only [signedStrictPartitionCount]
  have h_split := Finset.sum_filter_add_sum_filter_not (StrictPartitionSet n)
    (fun S => franklinInv S ≠ S) (fun S => (-1 : Int) ^ S.card)
  have h_nf := sum_nonfixed_zero n
  have : ∑ S ∈ StrictPartitionSet n, (-1 : Int) ^ S.card =
      ∑ S ∈ (StrictPartitionSet n).filter (fun S => ¬(franklinInv S ≠ S)), (-1 : Int) ^ S.card := by
    linarith [h_split]
  rw [this]; simp only [ne_eq, not_not]
  exact fixed_sum_eq_pentagonalSign n

end QseriesFormalization.PartI.Ch04Franklin
