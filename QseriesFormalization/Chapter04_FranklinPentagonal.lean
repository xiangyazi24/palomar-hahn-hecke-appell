import QseriesFormalization.Basic

/-!
# Chapter 5 — Boson-Fermion correspondence (Chan §5) — **partial setup only**

⚠️  **AUX CHAPTER — chapter-main result OPEN; file also contains Ch4-style
combinatorial material (strict partitions, Franklin involution)**.

Per `PLAYBOOK_AUDIT.md` (2026-05-22):

What's here:
- (lines ~7-39) Setup for Chan §5: `AdmissibleState`, `charge`, `energy`,
  `vacuum` — Borcherd's fermion-sea configurations.  These are the
  building blocks for Chan's third proof of JTP via fermionic vs bosonic
  evaluation of the partition function `Z(q,z)`.
- (lines ~41 onward) Strict-partition infrastructure used by Franklin's
  involution (`Chapter05_Franklin.lean`), which is Chan §4's combinatorial
  proof of Euler's pentagonal number theorem (NOT §5 content).

What is **not** here:
- Chan Theorem 5 (effectively Eq 5.2 = Eq 5.4 ⇒ JTP) — the fermionic
  evaluation `Z(q,z) = ∏ (1+zq^{n-1/2})(1+z^{-1}q^{n-1/2})`, the bosonic
  evaluation `Z(q,z) = (1/(q;q)_∞) · ∑_{n∈ℤ} z^n q^{n²/2}`, and the
  derivation that equating them gives JTP.  These are the chapter's
  actual main content and are NOT formalized.

So this file is a mix of "Ch5 setup definitions" and "Ch4 Franklin
infrastructure".  The Franklin work is solid.

**Update (2026-05-24)**: Chan §5's *main theorem* — the **Jacobi Triple
Product** — IS proved in the repository and re-exported as
`Pending.Ch05JTP.jacobi_triple_product` (= `Ch02.jacobiTripleProduct`).  The
*result* of §5 is thus available; only §5's specific *proof method*
(Boson–Fermion / fermionic Fock space, eqs 5.2 = 5.4) is not formalized — the
repo instead proves JTP via the Chan §3 finite-JTP limit.
-/

namespace QseriesFormalization
namespace PartI
namespace Ch04Franklin

/-- An admissible "fermion sea" configuration, modelled as the finset
of levels (offset from ℤ+1/2 to ℤ for Lean simplicity) that DIFFER
from the vacuum state. Vacuum has all i ≤ -1 occupied; an admissible
state has finitely many levels added (i ≥ 0 occupied) or removed
(i ≤ -1 vacated). -/
structure AdmissibleState where
  /-- Levels added (i ≥ 0 occupied beyond vacuum). -/
  added : Finset Nat
  /-- Levels removed (i ≤ -1 vacated below vacuum, encoded as Nat for the
  reflection k = -1 - i ≥ 0). -/
  removed : Finset Nat

/-- Two admissible states are equal iff their added/removed finsets match. -/
@[ext] theorem AdmissibleState.ext {S T : AdmissibleState}
    (h_added : S.added = T.added) (h_removed : S.removed = T.removed) :
    S = T := by
  cases S; cases T; simp_all

/-- The vacuum state: nothing added, nothing removed. -/
def vacuum : AdmissibleState := ⟨∅, ∅⟩

/-- Charge `Q(S) := added.card - removed.card`. -/
def charge (S : AdmissibleState) : Int :=
  (S.added.card : Int) - S.removed.card

theorem charge_eq_zero_iff (S : AdmissibleState) :
    charge S = 0 ↔ S.added.card = S.removed.card := by
  unfold charge; omega

/-- Energy `H(S) := ∑_{i ∈ added} (i + 1) + ∑_{k ∈ removed} (k + 1)`.
(Using offset `+1` so that the lowest added level i=0 contributes 1, etc.) -/
def energy (S : AdmissibleState) : Nat :=
  S.added.sum (· + 1) + S.removed.sum (· + 1)

/-- A partition has distinct parts when its list representation has no repeated
row lengths. -/
def HasDistinctParts (lam : List Nat) : Prop :=
  lam.Nodup

/-- All parts of a list-partition are positive. This excludes trailing zero
rows when using list representations. -/
def PositiveParts (lam : List Nat) : Prop :=
  ∀ n ∈ lam, 0 < n

/-- Strict partitions are weakly decreasing, positive, and have distinct
parts. These are the finite objects underlying Franklin's involution. -/
def IsStrictPartition (lam : List Nat) : Prop :=
  IsPartition lam ∧ PositiveParts lam ∧ HasDistinctParts lam

/-- The empty partition is strict. -/
theorem IsStrictPartition_nil :
    IsStrictPartition [] := by
  simp [IsStrictPartition, IsPartition, PositiveParts, HasDistinctParts]

/-- A one-part list is strict exactly when that part is positive. -/
theorem IsStrictPartition_singleton {n : Nat} :
    IsStrictPartition [n] ↔ 0 < n := by
  simp [IsStrictPartition, IsPartition, PositiveParts, HasDistinctParts]

/-- The first part of a nonempty strict partition is positive. -/
theorem IsStrictPartition.head_pos {n : Nat} {lam : List Nat}
    (h : IsStrictPartition (n :: lam)) :
    0 < n := by
  exact h.2.1 n (by simp)

/-- The tail of a nonempty strict partition is strict. -/
theorem IsStrictPartition.tail {n : Nat} {lam : List Nat}
    (h : IsStrictPartition (n :: lam)) :
    IsStrictPartition lam := by
  rcases h with ⟨hpart, hpos, hnodup⟩
  exact ⟨hpart.tail, (fun m hm => hpos m (by simp [hm])),
    List.Nodup.of_cons hnodup⟩

/-- A new positive first part that is strictly larger than every old part can
be prepended to a strict partition. -/
theorem IsStrictPartition.cons_of_forall_lt {n : Nat} {lam : List Nat}
    (hstrict : IsStrictPartition lam) (hn : 0 < n)
    (hgt : ∀ m, m ∈ lam → m < n) :
    IsStrictPartition (n :: lam) := by
  rcases hstrict with ⟨hpart, hpos, hnodup⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold IsPartition at hpart ⊢
    exact List.Pairwise.cons (fun m hm => Nat.le_of_lt (hgt m hm)) hpart
  · intro m hm
    simp at hm
    rcases hm with hmn | hmem
    · subst m
      exact hn
    · exact hpos m hmem
  · unfold HasDistinctParts at hnodup ⊢
    exact List.Nodup.cons (fun hnmem => (Nat.lt_irrefl n) (hgt n hnmem)) hnodup

/-- In a strict partition, every tail part is strictly below the first part. -/
theorem IsStrictPartition.tail_lt_head {n : Nat} {lam : List Nat}
    (h : IsStrictPartition (n :: lam)) {m : Nat} (hm : m ∈ lam) :
    m < n := by
  rcases h with ⟨hpart, _hpos, hnodup⟩
  have hle : m ≤ n := by
    exact hpart.rel_head (by simp [hm])
  have hne : m ≠ n := by
    intro hmn
    subst m
    exact (List.nodup_cons.mp hnodup).1 hm
  exact Nat.lt_of_le_of_ne hle hne

/-- The head of a nonempty strict partition does not occur again in the tail. -/
theorem IsStrictPartition.head_not_mem_tail {n : Nat} {lam : List Nat}
    (h : IsStrictPartition (n :: lam)) :
    n ∉ lam := by
  intro hnmem
  exact (Nat.lt_irrefl n) (IsStrictPartition.tail_lt_head h hnmem)

/-- A cons list is strict exactly when the tail is strict, the new part is
positive, and every old part is strictly smaller than the new head. -/
theorem IsStrictPartition_cons_iff {n : Nat} {lam : List Nat} :
    IsStrictPartition (n :: lam) ↔
      IsStrictPartition lam ∧ 0 < n ∧ ∀ m, m ∈ lam → m < n := by
  constructor
  · intro h
    exact ⟨IsStrictPartition.tail h, IsStrictPartition.head_pos h,
      fun m hm => IsStrictPartition.tail_lt_head h hm⟩
  · rintro ⟨hstrict, hn, hgt⟩
    exact IsStrictPartition.cons_of_forall_lt hstrict hn hgt

/-- Appending two strict partitions gives a strict partition when every part
of the right partition is strictly below every part of the left partition. -/
theorem IsStrictPartition_append_of_forall_gt {lam mu : List Nat}
    (hlam : IsStrictPartition lam) (hmu : IsStrictPartition mu)
    (hgt : ∀ a, a ∈ lam → ∀ b, b ∈ mu → b < a) :
    IsStrictPartition (lam ++ mu) := by
  induction lam with
  | nil =>
      simpa using hmu
  | cons n tail ih =>
      have htail : IsStrictPartition tail := IsStrictPartition.tail hlam
      have happ : IsStrictPartition (tail ++ mu) := by
        apply ih htail
        intro a ha b hb
        exact hgt a (by simp [ha]) b hb
      apply IsStrictPartition.cons_of_forall_lt happ (IsStrictPartition.head_pos hlam)
      intro m hm
      simp at hm
      rcases hm with htail_mem | hmu_mem
      · exact IsStrictPartition.tail_lt_head hlam htail_mem
      · exact hgt n (by simp) m hmu_mem

/-- If an appended list is a strict partition, then its left segment is strict. -/
theorem IsStrictPartition_left_of_append {lam mu : List Nat}
    (h : IsStrictPartition (lam ++ mu)) :
    IsStrictPartition lam := by
  induction lam with
  | nil =>
      exact IsStrictPartition_nil
  | cons n tail ih =>
      rw [List.cons_append] at h
      have htail_append : IsStrictPartition (tail ++ mu) := IsStrictPartition.tail h
      have htail : IsStrictPartition tail := ih htail_append
      apply IsStrictPartition.cons_of_forall_lt htail (IsStrictPartition.head_pos h)
      intro m hm
      have hm_append : m ∈ tail ++ mu := by simp [hm]
      exact IsStrictPartition.tail_lt_head h hm_append

/-- If an appended list is a strict partition, then its right segment is strict. -/
theorem IsStrictPartition_right_of_append {lam mu : List Nat}
    (h : IsStrictPartition (lam ++ mu)) :
    IsStrictPartition mu := by
  induction lam with
  | nil =>
      simpa using h
  | cons _ tail ih =>
      rw [List.cons_append] at h
      exact ih (IsStrictPartition.tail h)

/-- If an appended list is strict, every right-segment part is strictly below
every left-segment part. -/
theorem IsStrictPartition_append_forall_gt {lam mu : List Nat}
    (h : IsStrictPartition (lam ++ mu)) :
    ∀ a, a ∈ lam → ∀ b, b ∈ mu → b < a := by
  induction lam with
  | nil =>
      intro a ha
      simp at ha
  | cons n tail ih =>
      rw [List.cons_append] at h
      intro a ha b hb
      simp at ha
      rcases ha with rfl | htail
      · exact IsStrictPartition.tail_lt_head h (by simp [hb])
      · exact ih (IsStrictPartition.tail h) a htail b hb

/-- A concatenation is a strict partition exactly when each segment is strict
and every right-segment part is strictly below every left-segment part. -/
theorem IsStrictPartition_append_iff {lam mu : List Nat} :
    IsStrictPartition (lam ++ mu) ↔
      IsStrictPartition lam ∧ IsStrictPartition mu ∧
        ∀ a, a ∈ lam → ∀ b, b ∈ mu → b < a := by
  constructor
  · intro h
    exact ⟨IsStrictPartition_left_of_append h, IsStrictPartition_right_of_append h,
      IsStrictPartition_append_forall_gt h⟩
  · rintro ⟨hlam, hmu, hgt⟩
    exact IsStrictPartition_append_of_forall_gt hlam hmu hgt

/-- Dropping the last displayed row preserves strictness. The empty case is
trivial; in the nonempty case recover the list as
`dropLast ++ [getLast]` and take the strict left segment. -/
theorem IsStrictPartition_dropLast {lam : List Nat}
    (hstrict : IsStrictPartition lam) :
    IsStrictPartition lam.dropLast := by
  by_cases hne : lam = []
  · subst lam
    exact IsStrictPartition_nil
  · have hrec : lam.dropLast ++ [lam.getLast hne] = lam :=
      List.dropLast_append_getLast hne
    have hstrict' : IsStrictPartition (lam.dropLast ++ [lam.getLast hne]) := by
      simpa [hrec] using hstrict
    exact IsStrictPartition_left_of_append hstrict'

/-- Prepending a first part adds exactly that part to the partition weight. -/
theorem partitionWeight_cons_part (n : Nat) (lam : List Nat) :
    partitionWeight (n :: lam) = n + partitionWeight lam := by
  rfl

/-- Removing the first part subtracts its contribution from the weight. -/
theorem partitionWeight_cons_sub_head (n : Nat) (lam : List Nat) :
    partitionWeight (n :: lam) - n = partitionWeight lam := by
  simp [partitionWeight]

/-- Tail weight plus the first part recovers the total weight. -/
theorem partitionWeight_tail_add_head (n : Nat) (lam : List Nat) :
    partitionWeight lam + n = partitionWeight (n :: lam) := by
  simp [partitionWeight, Nat.add_comm]

/-- Appending list partitions adds their weights. This Ch04Franklin wrapper keeps the
weight accounting close to the Franklin-involution infrastructure. -/
theorem partitionWeight_append_parts (lam mu : List Nat) :
    partitionWeight (lam ++ mu) = partitionWeight lam + partitionWeight mu := by
  exact partitionWeight_append lam mu

/-- `[3,2,1]` is a strict partition. -/
theorem IsStrictPartition_three_two_one :
    IsStrictPartition [3, 2, 1] := by
  norm_num [IsStrictPartition, IsPartition, PositiveParts, HasDistinctParts]

/-- A repeated positive part is not strict. -/
theorem not_IsStrictPartition_two_two :
    ¬ IsStrictPartition [2, 2] := by
  intro h
  have hn : HasDistinctParts [2, 2] := h.2.2
  norm_num [HasDistinctParts] at hn

/-- Number of parts in the list model. -/
def numberOfParts (lam : List Nat) : Nat :=
  lam.length

/-- The empty partition has no parts. -/
theorem numberOfParts_nil :
    numberOfParts [] = 0 := by
  rfl

/-- Prepending a larger first part increases the number of parts by one. -/
theorem numberOfParts_cons (n : Nat) (lam : List Nat) :
    numberOfParts (n :: lam) = numberOfParts lam + 1 := by
  simp [numberOfParts]

/-- Appending list partitions adds their numbers of parts. -/
theorem numberOfParts_append (lam mu : List Nat) :
    numberOfParts (lam ++ mu) = numberOfParts lam + numberOfParts mu := by
  simp [numberOfParts]

/-- A nonempty list loses exactly one part when the last displayed row is
dropped. -/
theorem numberOfParts_dropLast_of_ne_nil {lam : List Nat} (_hne : lam ≠ []) :
    numberOfParts lam.dropLast = numberOfParts lam - 1 := by
  simp [numberOfParts]

/-- A nonempty list has `#(dropLast) + 1 = #list`. -/
theorem numberOfParts_dropLast_add_one_of_ne_nil {lam : List Nat} (hne : lam ≠ []) :
    numberOfParts lam.dropLast + 1 = numberOfParts lam := by
  rw [numberOfParts_dropLast_of_ne_nil hne]
  have hpos : 0 < numberOfParts lam := by
    simpa [numberOfParts, List.length_pos_iff] using hne
  omega

/-- The `getD` last-part convention agrees with `List.getLast` on nonempty
lists. -/
theorem lastPart_eq_getLast {lam : List Nat} (hne : lam ≠ []) :
    lam.getD (numberOfParts lam - 1) 0 = lam.getLast hne := by
  have hpos : 0 < lam.length := by
    simpa [List.length_pos_iff] using hne
  rw [List.getLast_eq_getElem, List.getD_eq_getElem]
  · congr
  · simpa [numberOfParts] using Nat.sub_lt hpos Nat.zero_lt_one

/-- Reading before `dropLast.length` agrees with reading the original list. -/
theorem dropLast_getD_of_lt {lam : List Nat} {r : Nat}
    (hr : r < lam.dropLast.length) :
    lam.dropLast.getD r 0 = lam.getD r 0 := by
  have hne : lam ≠ [] := by
    intro hnil
    subst lam
    simp at hr
  have hrec : lam.dropLast ++ [lam.getLast hne] = lam :=
    List.dropLast_append_getLast hne
  have happ :
      (lam.dropLast ++ [lam.getLast hne]).getD r 0 = lam.dropLast.getD r 0 :=
    List.getD_append _ _ _ _ hr
  rw [hrec] at happ
  exact happ.symm

/-- Removing the first part subtracts one from the number of parts. -/
theorem numberOfParts_cons_sub_one (n : Nat) (lam : List Nat) :
    numberOfParts (n :: lam) - 1 = numberOfParts lam := by
  simp [numberOfParts]

/-- Tail part count plus one recovers the number of parts of a cons list. -/
theorem numberOfParts_tail_add_one (n : Nat) (lam : List Nat) :
    numberOfParts lam + 1 = numberOfParts (n :: lam) := by
  rw [numberOfParts_cons]

/-- Reading an existing list entry with `getD` returns an actual member of
the list. -/
theorem getD_mem_of_lt (lam : List Nat) {r d : Nat} (hr : r < lam.length) :
    lam.getD r d ∈ lam := by
  rw [List.getD_eq_getElem (l := lam) (d := d) hr]
  exact List.getElem_mem _

/-- Parity of the number of parts, used as the sign-reversing datum for
Franklin's involution. -/
def partParity (lam : List Nat) : Nat :=
  numberOfParts lam % 2

/-- The empty partition has even part parity. -/
theorem partParity_nil :
    partParity [] = 0 := by
  rfl

/-- Prepending one part toggles the number-of-parts parity, in mod-2 form. -/
theorem partParity_cons (n : Nat) (lam : List Nat) :
    partParity (n :: lam) = (partParity lam + 1) % 2 := by
  unfold partParity numberOfParts
  change (lam.length + 1) % 2 = (lam.length % 2 + 1) % 2
  rw [Nat.add_mod]

/-- Removing a first part toggles the number-of-parts parity back. -/
theorem partParity_tail_cons (n : Nat) (lam : List Nat) :
    partParity lam = (partParity (n :: lam) + 1) % 2 := by
  unfold partParity numberOfParts
  change lam.length % 2 = ((lam.length + 1) % 2 + 1) % 2
  omega

/-- Prepending two parts preserves the number-of-parts parity. -/
theorem partParity_cons_cons (m n : Nat) (lam : List Nat) :
    partParity (m :: n :: lam) = partParity lam := by
  unfold partParity numberOfParts
  change (lam.length + 2) % 2 = lam.length % 2
  omega

/-- Appending list partitions adds their part parities modulo two. -/
theorem partParity_append (lam mu : List Nat) :
    partParity (lam ++ mu) = (partParity lam + partParity mu) % 2 := by
  unfold partParity numberOfParts
  simp only [List.length_append]
  rw [Nat.add_mod]

/-- If a partition has even part parity, prepending one part makes it odd. -/
theorem partParity_cons_of_zero {n : Nat} {lam : List Nat}
    (h : partParity lam = 0) :
    partParity (n :: lam) = 1 := by
  rw [partParity_cons, h]

/-- If a partition has odd part parity, prepending one part makes it even. -/
theorem partParity_cons_of_one {n : Nat} {lam : List Nat}
    (h : partParity lam = 1) :
    partParity (n :: lam) = 0 := by
  rw [partParity_cons, h]

/-- If a nonempty partition has even part parity, its tail has odd parity. -/
theorem partParity_tail_of_cons_zero {n : Nat} {lam : List Nat}
    (h : partParity (n :: lam) = 0) :
    partParity lam = 1 := by
  rw [partParity_tail_cons, h]

/-- If a nonempty partition has odd part parity, its tail has even parity. -/
theorem partParity_tail_of_cons_one {n : Nat} {lam : List Nat}
    (h : partParity (n :: lam) = 1) :
    partParity lam = 0 := by
  rw [partParity_tail_cons, h]

/-- The part parity is always either even (`0`) or odd (`1`). -/
theorem partParity_eq_zero_or_one (lam : List Nat) :
    partParity lam = 0 ∨ partParity lam = 1 := by
  unfold partParity
  have hlt : numberOfParts lam % 2 < 2 := Nat.mod_lt _ (by decide : 0 < 2)
  omega

/-- The sign attached to a strict partition in Franklin's sign-reversing
involution: even number of parts contributes `+1`, odd contributes `-1`. -/
def partSign (lam : List Nat) : Int :=
  if partParity lam = 0 then 1 else -1

/-- The empty partition has Franklin sign `+1`. -/
theorem partSign_nil :
    partSign [] = 1 := by
  rfl

theorem partSign_of_partParity_zero {lam : List Nat}
    (h : partParity lam = 0) :
    partSign lam = 1 := by
  simp [partSign, h]

theorem partSign_of_partParity_one {lam : List Nat}
    (h : partParity lam = 1) :
    partSign lam = -1 := by
  simp [partSign, h]

/-- Franklin's partition sign is always either `+1` or `-1`. -/
theorem partSign_eq_one_or_neg_one (lam : List Nat) :
    partSign lam = 1 ∨ partSign lam = -1 := by
  rcases partParity_eq_zero_or_one lam with h | h
  · exact Or.inl (partSign_of_partParity_zero h)
  · exact Or.inr (partSign_of_partParity_one h)

/-- Franklin's partition sign is never zero. -/
theorem partSign_ne_zero (lam : List Nat) :
    partSign lam ≠ 0 := by
  rcases partSign_eq_one_or_neg_one lam with h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num

/-- Franklin's partition sign squares to one. -/
theorem partSign_mul_self (lam : List Nat) :
    partSign lam * partSign lam = 1 := by
  rcases partSign_eq_one_or_neg_one lam with h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num

/-- Adding one part reverses Franklin's parity sign. -/
theorem partSign_cons (n : Nat) (lam : List Nat) :
    partSign (n :: lam) = - partSign lam := by
  unfold partSign
  rcases partParity_eq_zero_or_one lam with h | h
  · have hc : partParity (n :: lam) = 1 := partParity_cons_of_zero h
    simp [h, hc]
  · have hc : partParity (n :: lam) = 0 := partParity_cons_of_one h
    simp [h, hc]

/-- Removing the first part also reverses Franklin's parity sign. -/
theorem partSign_tail_cons (n : Nat) (lam : List Nat) :
    partSign lam = - partSign (n :: lam) := by
  rw [partSign_cons]
  omega

/-- Removing the first part of a nonempty list has the expected weight and
Franklin-sign behavior: the weight loses the head and the sign is reversed. -/
theorem tail_weight_sign_of_cons (n : Nat) (lam : List Nat) :
    partitionWeight (n :: lam) - n = partitionWeight lam ∧
      partSign lam = - partSign (n :: lam) :=
  ⟨partitionWeight_cons_sub_head n lam, partSign_tail_cons n lam⟩

/-- The named operation that removes the first row of a list partition. It is
separated out so Franklin-style moves can refer to the operation rather than
destructing the list every time. -/
def removeFirstPart : List Nat → List Nat
  | [] => []
  | _ :: tail => tail

/-- The first row length of a list partition, defaulting to zero on the empty
partition. -/
def firstPart : List Nat → Nat
  | [] => 0
  | head :: _ => head

@[simp] theorem removeFirstPart_nil :
    removeFirstPart [] = [] := rfl

@[simp] theorem removeFirstPart_cons (n : Nat) (lam : List Nat) :
    removeFirstPart (n :: lam) = lam := rfl

@[simp] theorem firstPart_nil :
    firstPart [] = 0 := rfl

@[simp] theorem firstPart_cons (n : Nat) (lam : List Nat) :
    firstPart (n :: lam) = n := rfl

/-- Removing the first row of a nonempty strict partition leaves a strict
partition. -/
theorem IsStrictPartition_removeFirstPart_cons {n : Nat} {lam : List Nat}
    (h : IsStrictPartition (n :: lam)) :
    IsStrictPartition (removeFirstPart (n :: lam)) := by
  simpa using IsStrictPartition.tail h

/-- The first row of a nonempty strict partition is positive, stated with the
named `firstPart` operation. -/
theorem firstPart_pos_of_IsStrictPartition_cons {n : Nat} {lam : List Nat}
    (h : IsStrictPartition (n :: lam)) :
    0 < firstPart (n :: lam) := by
  simpa using IsStrictPartition.head_pos h

/-- The named first part of any nonempty strict partition is positive. -/
theorem firstPart_pos_of_IsStrictPartition_of_ne_nil {lam : List Nat}
    (hstrict : IsStrictPartition lam) (hne : lam ≠ []) :
    0 < firstPart lam := by
  cases lam with
  | nil => exact False.elim (hne rfl)
  | cons n tail =>
      exact firstPart_pos_of_IsStrictPartition_cons hstrict

/-- Removing the first row of any strict partition leaves a strict partition.
For the empty partition this is the empty partition again. -/
theorem IsStrictPartition_removeFirstPart {lam : List Nat}
    (h : IsStrictPartition lam) :
    IsStrictPartition (removeFirstPart lam) := by
  cases lam with
  | nil =>
      simpa using IsStrictPartition_nil
  | cons n tail =>
      exact IsStrictPartition_removeFirstPart_cons h

/-- Removing the first row of a nonempty list decreases the number of parts
by one. -/
theorem numberOfParts_removeFirstPart_cons (n : Nat) (lam : List Nat) :
    numberOfParts (removeFirstPart (n :: lam)) + 1 = numberOfParts (n :: lam) := by
  rw [removeFirstPart_cons, numberOfParts_tail_add_one]

/-- Removing the first row of a nonempty list toggles the part-count parity. -/
theorem partParity_removeFirstPart_cons (n : Nat) (lam : List Nat) :
    partParity (removeFirstPart (n :: lam)) =
      (partParity (n :: lam) + 1) % 2 := by
  rw [removeFirstPart_cons]
  exact partParity_tail_cons n lam

/-- Removing the first row of a nonempty list reverses Franklin's
part-count sign. -/
theorem partSign_removeFirstPart_cons (n : Nat) (lam : List Nat) :
    partSign (removeFirstPart (n :: lam)) = - partSign (n :: lam) := by
  rw [removeFirstPart_cons]
  exact partSign_tail_cons n lam

/-- Removing the first row of a nonempty list has the same weight and
Franklin-sign behavior as taking the tail. -/
theorem removeFirstPart_weight_sign_cons (n : Nat) (lam : List Nat) :
    partitionWeight (n :: lam) - n = partitionWeight (removeFirstPart (n :: lam)) ∧
      partSign (removeFirstPart (n :: lam)) = - partSign (n :: lam) := by
  simpa using tail_weight_sign_of_cons n lam

/-- The named operation that prepends a row to a list partition. -/
def prependPart (n : Nat) (lam : List Nat) : List Nat := n :: lam

@[simp] theorem prependPart_eq_cons (n : Nat) (lam : List Nat) :
    prependPart n lam = n :: lam := rfl

@[simp] theorem firstPart_prependPart (n : Nat) (lam : List Nat) :
    firstPart (prependPart n lam) = n := rfl

@[simp] theorem removeFirstPart_prependPart (n : Nat) (lam : List Nat) :
    removeFirstPart (prependPart n lam) = lam := rfl

@[simp] theorem prependPart_removeFirstPart_cons (n : Nat) (lam : List Nat) :
    prependPart n (removeFirstPart (n :: lam)) = n :: lam := rfl

/-- A nonempty list partition is recovered from its named first part and named
tail operation. -/
@[simp] theorem prependPart_firstPart_removeFirstPart_cons (n : Nat) (lam : List Nat) :
    prependPart (firstPart (n :: lam)) (removeFirstPart (n :: lam)) = n :: lam := rfl

/-- Any nonempty list partition is recovered from its named first part and
named tail operation. -/
theorem prependPart_firstPart_removeFirstPart_of_ne_nil (lam : List Nat)
    (hne : lam ≠ []) :
    prependPart (firstPart lam) (removeFirstPart lam) = lam := by
  cases lam with
  | nil => exact False.elim (hne rfl)
  | cons n tail => rfl

/-- In a nonempty strict partition, every part left after removing the first
row is strictly below the named first part. -/
theorem removeFirstPart_lt_firstPart_of_IsStrictPartition_cons {n : Nat} {lam : List Nat}
    (h : IsStrictPartition (n :: lam)) {m : Nat}
    (hm : m ∈ removeFirstPart (n :: lam)) :
    m < firstPart (n :: lam) := by
  simpa using IsStrictPartition.tail_lt_head h hm

/-- In any strict partition, every part left after removing the first row is
strictly below the named first part. The empty case is vacuous. -/
theorem removeFirstPart_lt_firstPart_of_IsStrictPartition {lam : List Nat}
    (h : IsStrictPartition lam) {m : Nat} (hm : m ∈ removeFirstPart lam) :
    m < firstPart lam := by
  cases lam with
  | nil =>
      simp [removeFirstPart] at hm
  | cons n tail =>
      exact removeFirstPart_lt_firstPart_of_IsStrictPartition_cons h hm

/-- Weight decomposition through the named first-part and tail operations. -/
theorem partitionWeight_firstPart_add_removeFirstPart_cons (n : Nat) (lam : List Nat) :
    partitionWeight (n :: lam) =
      firstPart (n :: lam) + partitionWeight (removeFirstPart (n :: lam)) := by
  rfl

/-- Part-count decomposition through the named first-part and tail operations. -/
theorem numberOfParts_removeFirstPart_add_one_cons (n : Nat) (lam : List Nat) :
    numberOfParts (n :: lam) = numberOfParts (removeFirstPart (n :: lam)) + 1 := by
  rfl

/-- Franklin sign decomposition through the named tail operation. -/
theorem partSign_cons_eq_neg_removeFirstPart (n : Nat) (lam : List Nat) :
    partSign (n :: lam) = - partSign (removeFirstPart (n :: lam)) := by
  rw [removeFirstPart_cons, partSign_cons]

/-- Prepending a positive part larger than every old part preserves strictness. -/
theorem IsStrictPartition_prependPart_of_forall_lt {n : Nat} {lam : List Nat}
    (hstrict : IsStrictPartition lam) (hn : 0 < n)
    (hgt : ∀ m, m ∈ lam → m < n) :
    IsStrictPartition (prependPart n lam) := by
  exact IsStrictPartition.cons_of_forall_lt hstrict hn hgt

/-- Prepending one row increases the number of parts by one. -/
theorem numberOfParts_prependPart (n : Nat) (lam : List Nat) :
    numberOfParts (prependPart n lam) = numberOfParts lam + 1 := by
  exact numberOfParts_cons n lam

/-- Prepending one row toggles the part-count parity. -/
theorem partParity_prependPart (n : Nat) (lam : List Nat) :
    partParity (prependPart n lam) = (partParity lam + 1) % 2 := by
  exact partParity_cons n lam

/-- Prepending one row reverses Franklin's part-count sign. -/
theorem partSign_prependPart (n : Nat) (lam : List Nat) :
    partSign (prependPart n lam) = - partSign lam := by
  exact partSign_cons n lam

/-- Prepending one row has the expected weight and Franklin-sign behavior. -/
theorem prependPart_weight_sign (n : Nat) (lam : List Nat) :
    partitionWeight (prependPart n lam) = n + partitionWeight lam ∧
      partSign (prependPart n lam) = - partSign lam :=
  ⟨partitionWeight_cons_part n lam, partSign_cons n lam⟩

/-- Prepending a new large head to a strict partition has the expected
structural, weight, and Franklin-sign behavior. -/
theorem cons_strict_weight_sign_of_forall_lt {n : Nat} {lam : List Nat}
    (hstrict : IsStrictPartition lam) (hn : 0 < n)
    (hgt : ∀ m, m ∈ lam → m < n) :
    IsStrictPartition (n :: lam) ∧
      partitionWeight (n :: lam) = n + partitionWeight lam ∧
      partSign (n :: lam) = - partSign lam :=
  ⟨IsStrictPartition.cons_of_forall_lt hstrict hn hgt,
    partitionWeight_cons_part n lam, partSign_cons n lam⟩

/-- Named `prependPart` version of the strictness, weight, and sign package. -/
theorem prependPart_strict_weight_sign_of_forall_lt {n : Nat} {lam : List Nat}
    (hstrict : IsStrictPartition lam) (hn : 0 < n)
    (hgt : ∀ m, m ∈ lam → m < n) :
    IsStrictPartition (prependPart n lam) ∧
      partitionWeight (prependPart n lam) = n + partitionWeight lam ∧
      partSign (prependPart n lam) = - partSign lam := by
  simpa using cons_strict_weight_sign_of_forall_lt hstrict hn hgt

/-- Prepending two parts preserves Franklin's parity sign. -/
theorem partSign_cons_cons (m n : Nat) (lam : List Nat) :
    partSign (m :: n :: lam) = partSign lam := by
  rw [partSign_cons, partSign_cons]
  omega

/-- Appending two list partitions multiplies their Franklin parity signs. -/
theorem partSign_append (lam mu : List Nat) :
    partSign (lam ++ mu) = partSign lam * partSign mu := by
  have happ := partParity_append lam mu
  rcases partParity_eq_zero_or_one lam with hlam | hlam
  · rcases partParity_eq_zero_or_one mu with hmu | hmu
    · have h : partParity (lam ++ mu) = 0 := by simp [happ, hlam, hmu]
      simp [partSign, h, hlam, hmu]
    · have h : partParity (lam ++ mu) = 1 := by simp [happ, hlam, hmu]
      simp [partSign, h, hlam, hmu]
  · rcases partParity_eq_zero_or_one mu with hmu | hmu
    · have h : partParity (lam ++ mu) = 1 := by simp [happ, hlam, hmu]
      simp [partSign, h, hlam, hmu]
    · have h : partParity (lam ++ mu) = 0 := by simp [happ, hlam, hmu]
      simp [partSign, h, hlam, hmu]

theorem numberOfParts_three_two_one :
    numberOfParts [3, 2, 1] = 3 := by
  rfl

theorem partParity_three_two_one :
    partParity [3, 2, 1] = 1 := by
  rfl

/-- The staircase partition `[n, n-1, ..., 1]`. Its Ferrers diagram is a
triangular staircase, one of the basic shapes in Franklin's involution. -/
def staircasePartition : Nat → List Nat
  | 0 => []
  | Nat.succ n => Nat.succ n :: staircasePartition n

@[simp] theorem staircasePartition_zero :
    staircasePartition 0 = [] := rfl

@[simp] theorem staircasePartition_succ (n : Nat) :
    staircasePartition (Nat.succ n) = Nat.succ n :: staircasePartition n := rfl

theorem staircasePartition_three :
    staircasePartition 3 = [3, 2, 1] := by
  rfl

/-- The staircase partition of height `n` has `n` parts. -/
theorem numberOfParts_staircasePartition (n : Nat) :
    numberOfParts (staircasePartition n) = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [numberOfParts]
      simpa [numberOfParts] using ih

/-- The staircase partition of height `n` has list length `n`. -/
theorem staircasePartition_length (n : Nat) :
    (staircasePartition n).length = n := by
  simpa [numberOfParts] using numberOfParts_staircasePartition n

/-- The `r`-th displayed part of the height-`n` staircase is `n-r`. -/
theorem staircasePartition_getD_of_lt {n r : Nat} (hr : r < n) :
    (staircasePartition n).getD r 0 = n - r := by
  induction n generalizing r with
  | zero =>
      omega
  | succ n ih =>
      cases r with
      | zero =>
          simp [staircasePartition]
      | succ r =>
          have hrn : r < n := by omega
          rw [show (staircasePartition (n + 1)).getD (r + 1) 0 =
              (staircasePartition n).getD r 0 by rfl]
          rw [ih hrn]
          omega

/-- The staircase partition has parity determined by its height. -/
theorem partParity_staircasePartition (n : Nat) :
    partParity (staircasePartition n) = n % 2 := by
  unfold partParity
  rw [numberOfParts_staircasePartition]

/-- The staircase partition has Franklin sign determined by its height. -/
theorem partSign_staircasePartition (n : Nat) :
    partSign (staircasePartition n) = if n % 2 = 0 then 1 else -1 := by
  simp [partSign, partParity_staircasePartition]

/-- The weight of the staircase partition is the triangular number. -/
theorem partitionWeight_staircasePartition (n : Nat) :
    partitionWeight (staircasePartition n) = triangular n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [ih, triangular_succ]
      omega

/-- Every part of the height-`n` staircase is at most `n`. -/
theorem mem_staircasePartition_le {m n : Nat}
    (hmem : m ∈ staircasePartition n) : m ≤ n := by
  induction n with
  | zero =>
      simp at hmem
  | succ n ih =>
      simp [staircasePartition] at hmem
      rcases hmem with h | h
      · omega
      · exact Nat.le_trans (ih h) (Nat.le_succ n)

/-- Every part of a staircase partition is positive. -/
theorem PositiveParts_staircasePartition (n : Nat) :
    PositiveParts (staircasePartition n) := by
  intro m hmem
  induction n with
  | zero =>
      simp at hmem
  | succ n ih =>
      simp [staircasePartition] at hmem
      rcases hmem with h | h
      · omega
      · exact ih h

/-- The staircase partition has no repeated parts. -/
theorem HasDistinctParts_staircasePartition (n : Nat) :
    HasDistinctParts (staircasePartition n) := by
  induction n with
  | zero =>
      simp [HasDistinctParts]
  | succ n ih =>
      simp [HasDistinctParts, staircasePartition]
      constructor
      · intro hmem
        have hle := mem_staircasePartition_le hmem
        omega
      · exact ih

/-- The staircase partition is weakly decreasing. -/
theorem IsPartition_staircasePartition (n : Nat) :
    IsPartition (staircasePartition n) := by
  induction n with
  | zero =>
      simp [IsPartition]
  | succ n ih =>
      simp [IsPartition, staircasePartition]
      constructor
      · intro m hmem
        exact Nat.le_trans (mem_staircasePartition_le hmem) (Nat.le_succ n)
      · exact ih

/-- Staircase partitions are strict partitions. -/
theorem IsStrictPartition_staircasePartition (n : Nat) :
    IsStrictPartition (staircasePartition n) := by
  exact ⟨IsPartition_staircasePartition n, PositiveParts_staircasePartition n,
    HasDistinctParts_staircasePartition n⟩

/-- Add a fixed offset to every part. This preserves the relative shape and is
useful for shifted staircase/Ferrers manipulations. -/
def shiftParts (d : Nat) (lam : List Nat) : List Nat :=
  lam.map (fun n => n + d)

theorem shiftParts_nil (d : Nat) :
    shiftParts d [] = [] := by
  rfl

theorem shiftParts_three_two_one_one :
    shiftParts 1 [3, 2, 1] = [4, 3, 2] := by
  rfl

/-- Shifting all parts preserves the number of parts. -/
theorem numberOfParts_shiftParts (d : Nat) (lam : List Nat) :
    numberOfParts (shiftParts d lam) = numberOfParts lam := by
  simp [numberOfParts, shiftParts]

/-- Reading a shifted part below the list length adds the shift offset to the
original part. -/
theorem shiftParts_getD_of_lt {d : Nat} {lam : List Nat} {r : Nat}
    (hr : r < lam.length) :
    (shiftParts d lam).getD r 0 = lam.getD r 0 + d := by
  induction lam generalizing r with
  | nil =>
      simp at hr
  | cons n tail ih =>
      cases r with
      | zero =>
          simp [shiftParts]
      | succ r =>
          have hrt : r < tail.length := by simpa using hr
          simpa [shiftParts] using ih hrt

/-- Shifting all parts preserves the parity of the number of parts. -/
theorem partParity_shiftParts (d : Nat) (lam : List Nat) :
    partParity (shiftParts d lam) = partParity lam := by
  unfold partParity
  rw [numberOfParts_shiftParts]

/-- Shifting all parts preserves Franklin's parity sign. -/
theorem partSign_shiftParts (d : Nat) (lam : List Nat) :
    partSign (shiftParts d lam) = partSign lam := by
  simp [partSign, partParity_shiftParts]

/-- Shifting all parts by `d` adds `d` times the number of parts to the
partition weight. -/
theorem partitionWeight_shiftParts (d : Nat) (lam : List Nat) :
    partitionWeight (shiftParts d lam) =
      partitionWeight lam + d * numberOfParts lam := by
  induction lam with
  | nil =>
      simp [shiftParts, numberOfParts]
  | cons a t ih =>
      simp [shiftParts, partitionWeight, numberOfParts]
      change a + d + partitionWeight (shiftParts d t) =
        a + partitionWeight t + d * (t.length + 1)
      rw [ih]
      simp [numberOfParts]
      rw [Nat.mul_add, Nat.mul_one]
      omega

/-- Shifting positive parts keeps them positive. -/
theorem PositiveParts_shiftParts {d : Nat} {lam : List Nat}
    (h : PositiveParts lam) :
    PositiveParts (shiftParts d lam) := by
  intro m hm
  rcases List.mem_map.mp hm with ⟨n, hn, rfl⟩
  exact Nat.lt_add_right d (h n hn)

/-- Shifting by a fixed offset preserves distinct parts. -/
theorem HasDistinctParts_shiftParts {d : Nat} {lam : List Nat}
    (h : HasDistinctParts lam) :
    HasDistinctParts (shiftParts d lam) := by
  unfold HasDistinctParts shiftParts
  exact h.map (fun _ _ hxy => by omega)

/-- Shifting all parts preserves the weakly decreasing partition order. -/
theorem IsPartition_shiftParts {d : Nat} {lam : List Nat}
    (h : IsPartition lam) :
    IsPartition (shiftParts d lam) := by
  induction lam with
  | nil =>
      simp [IsPartition, shiftParts]
  | cons a t ih =>
      simp [IsPartition, shiftParts] at h ⊢
      constructor
      · intro m hm
        have hnle : m ≤ a := h.1 m hm
        omega
      · exact ih h.2

/-- Shifting all parts of a strict partition gives another strict partition. -/
theorem IsStrictPartition_shiftParts {d : Nat} {lam : List Nat}
    (h : IsStrictPartition lam) :
    IsStrictPartition (shiftParts d lam) :=
  ⟨IsPartition_shiftParts h.1, PositiveParts_shiftParts h.2.1,
    HasDistinctParts_shiftParts h.2.2⟩

/-- Applying two uniform shifts is the same as applying their sum. -/
theorem shiftParts_shiftParts (a b : Nat) (lam : List Nat) :
    shiftParts a (shiftParts b lam) = shiftParts (b + a) lam := by
  induction lam with
  | nil =>
      rfl
  | cons n tail =>
      simp [shiftParts]
      omega

/-- Subtract one from every displayed part. This is the row-shortening half
of Franklin's sign-reversing move away from the pentagonal fixed shapes. -/
def decrementParts (lam : List Nat) : List Nat :=
  lam.map (fun n => n - 1)

theorem decrementParts_nil :
    decrementParts [] = [] := by
  rfl

theorem decrementParts_cons (n : Nat) (lam : List Nat) :
    decrementParts (n :: lam) = (n - 1) :: decrementParts lam := by
  rfl

/-- Row-shortening preserves the number of displayed parts. -/
theorem numberOfParts_decrementParts (lam : List Nat) :
    numberOfParts (decrementParts lam) = numberOfParts lam := by
  simp [numberOfParts, decrementParts]

/-- Row-shortening preserves Franklin's parity sign. -/
theorem partSign_decrementParts (lam : List Nat) :
    partSign (decrementParts lam) = partSign lam := by
  simp [partSign, partParity, numberOfParts_decrementParts]

/-- If all parts are positive, shortening every row by one loses exactly one
cell from each displayed part. -/
theorem partitionWeight_decrementParts_add_numberOfParts {lam : List Nat}
    (hpos : PositiveParts lam) :
    partitionWeight (decrementParts lam) + numberOfParts lam = partitionWeight lam := by
  induction lam with
  | nil =>
      simp [decrementParts, numberOfParts, partitionWeight]
  | cons n tail ih =>
      have hn : 0 < n := hpos n (by simp)
      have htail : PositiveParts tail := by
        intro m hm
        exact hpos m (by simp [hm])
      have ih_tail := ih htail
      simp [decrementParts, partitionWeight, numberOfParts] at ih_tail ⊢
      omega

/-- Weakly decreasing row order is preserved when every part is shortened by
one. -/
theorem IsPartition_decrementParts {lam : List Nat}
    (hpart : IsPartition lam) :
    IsPartition (decrementParts lam) := by
  unfold IsPartition at hpart ⊢
  unfold decrementParts
  exact List.Pairwise.map (fun n => n - 1)
    (fun _a _b hle => Nat.sub_le_sub_right hle 1) hpart

/-- Positivity survives row-shortening when every original part is at least
two. -/
theorem PositiveParts_decrementParts_of_one_lt {lam : List Nat}
    (hgt : ∀ n, n ∈ lam → 1 < n) :
    PositiveParts (decrementParts lam) := by
  intro m hm
  unfold decrementParts at hm
  rcases List.mem_map.mp hm with ⟨n, hn, rfl⟩
  exact Nat.sub_pos_of_lt (hgt n hn)

/-- Distinctness survives row-shortening on positive parts. -/
theorem HasDistinctParts_decrementParts {lam : List Nat}
    (hpos : PositiveParts lam) (hnodup : HasDistinctParts lam) :
    HasDistinctParts (decrementParts lam) := by
  unfold HasDistinctParts at hnodup ⊢
  unfold decrementParts
  exact hnodup.map_on (fun x hx y hy hxy => by
    have hxpos : 0 < x := hpos x hx
    have hypos : 0 < y := hpos y hy
    omega)

/-- Row-shortening preserves strictness when no part is shortened to zero. -/
theorem IsStrictPartition_decrementParts_of_one_lt {lam : List Nat}
    (hstrict : IsStrictPartition lam) (hgt : ∀ n, n ∈ lam → 1 < n) :
    IsStrictPartition (decrementParts lam) :=
  ⟨IsPartition_decrementParts hstrict.1,
    PositiveParts_decrementParts_of_one_lt hgt,
    HasDistinctParts_decrementParts hstrict.2.1 hstrict.2.2⟩

/-- Franklin's row-shortening move: shorten every existing row by one and
append a new row whose size is the old number of parts. This is the case used
when the smallest part is strictly larger than `numberOfParts lam + 1`. -/
def franklinDownMove (lam : List Nat) : List Nat :=
  decrementParts lam ++ [numberOfParts lam]

/-- Shape condition for the Franklin down branch: the partition is nonempty
and every row is long enough that shortening all rows and appending a new last
row is the active branch. -/
def IsFranklinDownBranchInput (lam : List Nat) : Prop :=
  0 < numberOfParts lam ∧
    ∀ n, n ∈ lam → numberOfParts lam + 1 < n

/-- Shape condition for the Franklin up branch: the list has the explicit form
`mu ++ [#mu]` with a strict preceding segment. -/
def IsFranklinUpBranchInput (lam : List Nat) : Prop :=
  ∃ mu : List Nat, IsStrictPartition mu ∧ lam = mu ++ [numberOfParts mu]

/-- Last-part criterion for the explicit Franklin up-branch shape. -/
theorem IsFranklinUpBranchInput.lastPart_eq_pred {lam : List Nat}
    (hup : IsFranklinUpBranchInput lam) :
    lam.getD (numberOfParts lam - 1) 0 = numberOfParts lam - 1 := by
  rcases hup with ⟨mu, _hmu, rfl⟩
  simp [numberOfParts]

/-- A strict nonempty partition whose last row has size `#parts - 1` is in
the explicit Franklin up branch. -/
theorem IsFranklinUpBranchInput_of_strict_lastPart_eq_pred {lam : List Nat}
    (hstrict : IsStrictPartition lam) (hne : lam ≠ [])
    (hlast : lam.getD (numberOfParts lam - 1) 0 = numberOfParts lam - 1) :
    IsFranklinUpBranchInput lam := by
  refine ⟨lam.dropLast, IsStrictPartition_dropLast hstrict, ?_⟩
  have hlast_get :
      lam.getLast hne = numberOfParts lam.dropLast := by
    rw [← lastPart_eq_getLast hne, hlast, numberOfParts_dropLast_of_ne_nil hne]
  calc
    lam = lam.dropLast ++ [lam.getLast hne] := by
      exact (List.dropLast_append_getLast hne).symm
    _ = lam.dropLast ++ [numberOfParts lam.dropLast] := by
      rw [hlast_get]

/-- For strict nonempty partitions, the explicit Franklin up-branch predicate
is exactly the last-part equality `last = #parts - 1`. -/
theorem IsFranklinUpBranchInput_iff_lastPart_eq_pred_of_strict {lam : List Nat}
    (hstrict : IsStrictPartition lam) (hne : lam ≠ []) :
    IsFranklinUpBranchInput lam ↔
      lam.getD (numberOfParts lam - 1) 0 = numberOfParts lam - 1 := by
  constructor
  · exact IsFranklinUpBranchInput.lastPart_eq_pred
  · exact IsFranklinUpBranchInput_of_strict_lastPart_eq_pred hstrict hne

/-- Down-branch inputs force the last part to exceed `#parts + 1`. -/
theorem IsFranklinDownBranchInput.lastPart_gt_numberOfParts_add_one
    {lam : List Nat} (hdown : IsFranklinDownBranchInput lam) :
    numberOfParts lam + 1 < lam.getD (numberOfParts lam - 1) 0 := by
  have hlen : numberOfParts lam - 1 < lam.length := by
    have hpos : 0 < lam.length := by
      simpa [numberOfParts] using hdown.1
    simpa [numberOfParts] using Nat.sub_lt hpos Nat.zero_lt_one
  exact hdown.2 (lam.getD (numberOfParts lam - 1) 0)
    (getD_mem_of_lt lam (d := 0) hlen)

/-- If the last part of a strict nonempty partition exceeds `#parts + 1`,
then every part does, so the partition is in the down branch. -/
theorem IsFranklinDownBranchInput_of_strict_lastPart_gt_numberOfParts_add_one
    {lam : List Nat} (hstrict : IsStrictPartition lam) (hne : lam ≠ [])
    (hlast : numberOfParts lam + 1 < lam.getD (numberOfParts lam - 1) 0) :
    IsFranklinDownBranchInput lam := by
  constructor
  · simpa [numberOfParts, List.length_pos_iff] using hne
  · intro n hn
    have hlast_le : lam.getD (numberOfParts lam - 1) 0 ≤ n := by
      have hgl : lam.getLast hne ≤ n := by
        simpa [IsPartition] using hstrict.1.rel_getLast hn
      rwa [lastPart_eq_getLast hne]
    exact Nat.lt_of_lt_of_le hlast hlast_le

/-- For strict nonempty partitions, the down-branch predicate is exactly the
last-part inequality `#parts + 1 < last`. -/
theorem IsFranklinDownBranchInput_iff_lastPart_gt_numberOfParts_add_one_of_strict
    {lam : List Nat} (hstrict : IsStrictPartition lam) (hne : lam ≠ []) :
    IsFranklinDownBranchInput lam ↔
      numberOfParts lam + 1 < lam.getD (numberOfParts lam - 1) 0 := by
  constructor
  · exact IsFranklinDownBranchInput.lastPart_gt_numberOfParts_add_one
  · exact IsFranklinDownBranchInput_of_strict_lastPart_gt_numberOfParts_add_one hstrict hne

/-- The down move adds one displayed part. -/
theorem numberOfParts_franklinDownMove (lam : List Nat) :
    numberOfParts (franklinDownMove lam) = numberOfParts lam + 1 := by
  simp [franklinDownMove, numberOfParts, decrementParts]

/-- The down move reverses Franklin's sign. -/
theorem partSign_franklinDownMove (lam : List Nat) :
    partSign (franklinDownMove lam) = - partSign lam := by
  rw [franklinDownMove, partSign_append, partSign_decrementParts]
  have hsingle : partSign [numberOfParts lam] = -1 := by
    simp [partSign, partParity, numberOfParts]
  rw [hsingle]
  rcases partSign_eq_one_or_neg_one lam with h | h <;> rw [h] <;> norm_num

/-- The down move preserves weight on positive-parts lists: one cell is
removed from each old row and exactly that many cells are appended as the new
row. -/
theorem partitionWeight_franklinDownMove {lam : List Nat}
    (hpos : PositiveParts lam) :
    partitionWeight (franklinDownMove lam) = partitionWeight lam := by
  rw [franklinDownMove, partitionWeight_append]
  simp [partitionWeight]
  exact partitionWeight_decrementParts_add_numberOfParts hpos

/-- Under the non-fixed Franklin inequality, the down move preserves
strictness. The hypothesis says every old row remains strictly longer than
the new appended row after shortening. -/
theorem IsStrictPartition_franklinDownMove {lam : List Nat}
    (hstrict : IsStrictPartition lam) (hlen : 0 < numberOfParts lam)
    (hgt : ∀ n, n ∈ lam → numberOfParts lam + 1 < n) :
    IsStrictPartition (franklinDownMove lam) := by
  unfold franklinDownMove
  apply IsStrictPartition_append_of_forall_gt
  · apply IsStrictPartition_decrementParts_of_one_lt hstrict
    intro n hn
    have hnlarge := hgt n hn
    omega
  · exact (IsStrictPartition_singleton).2 hlen
  · intro a ha b hb
    unfold decrementParts at ha
    rcases List.mem_map.mp ha with ⟨n, hn, rfl⟩
    simp at hb
    subst b
    have hnlarge := hgt n hn
    omega

/-- Package the down branch of Franklin's move: away from the pentagonal fixed
case, it preserves weight, reverses sign, and stays in strict partitions. -/
theorem franklinDownMove_strict_weight_sign {lam : List Nat}
    (hstrict : IsStrictPartition lam) (hlen : 0 < numberOfParts lam)
    (hgt : ∀ n, n ∈ lam → numberOfParts lam + 1 < n) :
    IsStrictPartition (franklinDownMove lam) ∧
      partitionWeight (franklinDownMove lam) = partitionWeight lam ∧
      partSign (franklinDownMove lam) = - partSign lam :=
  ⟨IsStrictPartition_franklinDownMove hstrict hlen hgt,
    partitionWeight_franklinDownMove hstrict.2.1,
    partSign_franklinDownMove lam⟩

/-- Under the Franklin down-branch inequality, the shortened old rows form a
strict partition. This is the preceding segment in the paired up-branch input
shape. -/
theorem IsStrictPartition_decrementParts_of_franklinDownMove_hgt {lam : List Nat}
    (hstrict : IsStrictPartition lam)
    (hgt : ∀ n, n ∈ lam → numberOfParts lam + 1 < n) :
    IsStrictPartition (decrementParts lam) := by
  apply IsStrictPartition_decrementParts_of_one_lt hstrict
  intro n hn
  have hnlarge := hgt n hn
  omega

/-- The down branch output is explicitly an up-branch input:
`decrementParts lam ++ [#(decrementParts lam)]`. -/
theorem franklinDownMove_eq_append_numberOfParts_decrementParts (lam : List Nat) :
    franklinDownMove lam =
      decrementParts lam ++ [numberOfParts (decrementParts lam)] := by
  rw [franklinDownMove, numberOfParts_decrementParts]

/-- Existence form of the previous theorem: every down-branch output has the
explicit up-branch input shape. -/
theorem franklinDownMove_eq_append_numberOfParts_exists (lam : List Nat) :
    ∃ mu : List Nat, franklinDownMove lam = mu ++ [numberOfParts mu] :=
  ⟨decrementParts lam, franklinDownMove_eq_append_numberOfParts_decrementParts lam⟩

/-- Under the Franklin down-branch hypotheses, the preceding segment in the
resulting up-branch input shape is strict. -/
theorem franklinDownMove_eq_append_numberOfParts_strict_exists {lam : List Nat}
    (hstrict : IsStrictPartition lam)
    (hgt : ∀ n, n ∈ lam → numberOfParts lam + 1 < n) :
    ∃ mu : List Nat,
      IsStrictPartition mu ∧ franklinDownMove lam = mu ++ [numberOfParts mu] :=
  ⟨decrementParts lam,
    IsStrictPartition_decrementParts_of_franklinDownMove_hgt hstrict hgt,
    franklinDownMove_eq_append_numberOfParts_decrementParts lam⟩

/-- Predicate form: a strict down-branch input is sent by the down move to an
up-branch input. -/
theorem IsFranklinUpBranchInput_franklinDownMove {lam : List Nat}
    (hstrict : IsStrictPartition lam) (hdown : IsFranklinDownBranchInput lam) :
    IsFranklinUpBranchInput (franklinDownMove lam) := by
  rcases hdown with ⟨_hlen, hgt⟩
  exact franklinDownMove_eq_append_numberOfParts_strict_exists hstrict hgt

/-- Predicate form of the down branch package. -/
theorem franklinDownMove_strict_weight_sign_of_branch_input {lam : List Nat}
    (hstrict : IsStrictPartition lam) (hdown : IsFranklinDownBranchInput lam) :
    IsStrictPartition (franklinDownMove lam) ∧
      partitionWeight (franklinDownMove lam) = partitionWeight lam ∧
      partSign (franklinDownMove lam) = - partSign lam :=
  franklinDownMove_strict_weight_sign hstrict hdown.1 hdown.2

/-- The inverse-shaped Franklin branch: remove the last displayed row and
lengthen every remaining row by one. This is the branch paired with
`franklinDownMove` away from fixed pentagonal shapes. -/
def franklinUpMove (lam : List Nat) : List Nat :=
  shiftParts 1 lam.dropLast

/-- Incrementing after decrementing positive parts recovers the original
partition list. -/
theorem shiftParts_one_decrementParts_eq_of_positive {lam : List Nat}
    (hpos : PositiveParts lam) :
    shiftParts 1 (decrementParts lam) = lam := by
  induction lam with
  | nil =>
      rfl
  | cons n tail ih =>
      have hn : 0 < n := hpos n (by simp)
      have htail : PositiveParts tail := by
        intro m hm
        exact hpos m (by simp [hm])
      simp [shiftParts, decrementParts]
      constructor
      · omega
      · simpa [shiftParts, decrementParts] using ih htail

/-- Shortening after lengthening every row by one recovers the original list. -/
theorem decrementParts_shiftParts_one_eq (lam : List Nat) :
    decrementParts (shiftParts 1 lam) = lam := by
  induction lam with
  | nil =>
      rfl
  | cons n tail ih =>
      change (n + 1 - 1) :: decrementParts (shiftParts 1 tail) = n :: tail
      rw [Nat.add_sub_cancel, ih]

/-- Shortening a list shifted by a positive offset removes one unit of that
offset. -/
theorem decrementParts_shiftParts_succ (d : Nat) (lam : List Nat) :
    decrementParts (shiftParts (d + 1) lam) = shiftParts d lam := by
  induction lam with
  | nil =>
      rfl
  | cons n tail =>
      simp [decrementParts, shiftParts]

/-- The up branch is a left inverse to the down branch on positive-parts
lists. This records the core inverse calculation needed for Franklin's
sign-reversing involution. -/
theorem franklinUpMove_franklinDownMove_of_positive {lam : List Nat}
    (hpos : PositiveParts lam) :
    franklinUpMove (franklinDownMove lam) = lam := by
  unfold franklinUpMove franklinDownMove
  rw [List.dropLast_concat]
  exact shiftParts_one_decrementParts_eq_of_positive hpos

/-- A down-branch step lands in the up-branch input region, and the up move
immediately returns to the original partition. -/
theorem franklinDownMove_branch_transition_and_inverse {lam : List Nat}
    (hstrict : IsStrictPartition lam) (hdown : IsFranklinDownBranchInput lam) :
    IsFranklinUpBranchInput (franklinDownMove lam) ∧
      franklinUpMove (franklinDownMove lam) = lam :=
  ⟨IsFranklinUpBranchInput_franklinDownMove hstrict hdown,
    franklinUpMove_franklinDownMove_of_positive hstrict.2.1⟩

/-- On an explicitly displayed last row, the up branch drops that last row
and lengthens every preceding row. -/
theorem franklinUpMove_append_singleton (mu : List Nat) (n : Nat) :
    franklinUpMove (mu ++ [n]) = shiftParts 1 mu := by
  unfold franklinUpMove
  rw [List.dropLast_concat]

/-- The down branch is the inverse of the up branch on the explicit
last-row shape `mu ++ [#mu]`. -/
theorem franklinDownMove_franklinUpMove_append_numberOfParts (mu : List Nat) :
    franklinDownMove (franklinUpMove (mu ++ [numberOfParts mu])) =
      mu ++ [numberOfParts mu] := by
  rw [franklinUpMove_append_singleton]
  unfold franklinDownMove
  rw [decrementParts_shiftParts_one_eq, numberOfParts_shiftParts]

/-- The up branch on an explicitly displayed last row has as many parts as
the preceding segment. -/
theorem numberOfParts_franklinUpMove_append_singleton (mu : List Nat) (n : Nat) :
    numberOfParts (franklinUpMove (mu ++ [n])) = numberOfParts mu := by
  rw [franklinUpMove_append_singleton, numberOfParts_shiftParts]

/-- On a nonempty list, the up move has one fewer displayed part. -/
theorem numberOfParts_franklinUpMove_of_ne_nil {lam : List Nat} (hne : lam ≠ []) :
    numberOfParts (franklinUpMove lam) = numberOfParts lam - 1 := by
  rw [franklinUpMove, numberOfParts_shiftParts,
    numberOfParts_dropLast_of_ne_nil hne]

/-- The up move preserves consecutive row differences equal to one. -/
theorem successive_getD_franklinUpMove_of_successive {lam : List Nat}
    (hsucc : ∀ r, r + 1 < numberOfParts lam →
      lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    ∀ r, r + 1 < numberOfParts (franklinUpMove lam) →
      (franklinUpMove lam).getD (r + 1) 0 + 1 =
        (franklinUpMove lam).getD r 0 := by
  intro r hr
  have htargetLen : numberOfParts (franklinUpMove lam) = lam.dropLast.length := by
    rw [franklinUpMove, numberOfParts_shiftParts, numberOfParts]
  have hrDropSucc : r + 1 < lam.dropLast.length := by
    simpa [htargetLen] using hr
  have hrDrop : r < lam.dropLast.length := by omega
  have hsuccLam : r + 1 < numberOfParts lam := by
    have hdropLen : lam.dropLast.length = lam.length - 1 := by
      simp
    simp [numberOfParts]
    omega
  rw [franklinUpMove]
  rw [shiftParts_getD_of_lt (d := 1) (lam := lam.dropLast) hrDropSucc,
    shiftParts_getD_of_lt (d := 1) (lam := lam.dropLast) hrDrop,
    dropLast_getD_of_lt hrDropSucc, dropLast_getD_of_lt hrDrop]
  have h := hsucc r hsuccLam
  omega

/-- A strict explicit up-branch input is sent by the up move to a down-branch
input. The strictness of the whole input supplies the inequality between the
preceding rows and the removed last row. -/
theorem IsFranklinDownBranchInput_franklinUpMove {lam : List Nat}
    (hstrict : IsStrictPartition lam) (hup : IsFranklinUpBranchInput lam) :
    IsFranklinDownBranchInput (franklinUpMove lam) := by
  rcases hup with ⟨mu, _hmu, hshape⟩
  rw [hshape] at hstrict ⊢
  rw [franklinUpMove_append_singleton]
  constructor
  · have hsingle : IsStrictPartition [numberOfParts mu] :=
      IsStrictPartition_right_of_append (lam := mu) hstrict
    simpa [numberOfParts_shiftParts] using (IsStrictPartition_singleton).1 hsingle
  · intro n hn
    rw [numberOfParts_shiftParts]
    unfold shiftParts at hn
    rcases List.mem_map.mp hn with ⟨m, hm, rfl⟩
    have hgt :=
      IsStrictPartition_append_forall_gt hstrict m hm (numberOfParts mu) (by simp)
    omega

/-- The up branch reverses Franklin's sign on any list with an explicitly
displayed last row. -/
theorem partSign_franklinUpMove_append_singleton (mu : List Nat) (n : Nat) :
    partSign (franklinUpMove (mu ++ [n])) = - partSign (mu ++ [n]) := by
  rw [franklinUpMove_append_singleton, partSign_shiftParts, partSign_append]
  have hsingle : partSign [n] = -1 := by
    simp [partSign, partParity, numberOfParts]
  rw [hsingle]
  rcases partSign_eq_one_or_neg_one mu with h | h <;> rw [h] <;> norm_num

/-- If the last row has size equal to the number of preceding rows, the up
branch preserves partition weight: the removed last row is redistributed by
adding one cell to each previous row. -/
theorem partitionWeight_franklinUpMove_append_numberOfParts (mu : List Nat) :
    partitionWeight (franklinUpMove (mu ++ [numberOfParts mu])) =
      partitionWeight (mu ++ [numberOfParts mu]) := by
  rw [franklinUpMove_append_singleton, partitionWeight_shiftParts, partitionWeight_append]
  simp [partitionWeight, numberOfParts]

/-- The up branch preserves strictness on an explicitly displayed last-row
shape as soon as the preceding segment is strict. -/
theorem IsStrictPartition_franklinUpMove_append_singleton {mu : List Nat} {n : Nat}
    (hstrict : IsStrictPartition mu) :
    IsStrictPartition (franklinUpMove (mu ++ [n])) := by
  rw [franklinUpMove_append_singleton]
  exact IsStrictPartition_shiftParts hstrict

/-- Package the up branch on the complementary Franklin shape: when the last
row has size equal to the number of previous rows, the move preserves weight,
reverses sign, and outputs a strict partition. -/
theorem franklinUpMove_append_numberOfParts_strict_weight_sign {mu : List Nat}
    (hstrict : IsStrictPartition mu) :
    IsStrictPartition (franklinUpMove (mu ++ [numberOfParts mu])) ∧
      partitionWeight (franklinUpMove (mu ++ [numberOfParts mu])) =
        partitionWeight (mu ++ [numberOfParts mu]) ∧
      partSign (franklinUpMove (mu ++ [numberOfParts mu])) =
        - partSign (mu ++ [numberOfParts mu]) :=
  ⟨IsStrictPartition_franklinUpMove_append_singleton hstrict,
    partitionWeight_franklinUpMove_append_numberOfParts mu,
    partSign_franklinUpMove_append_singleton mu (numberOfParts mu)⟩

/-- Predicate form of the up branch package. -/
theorem franklinUpMove_strict_weight_sign_of_branch_input {lam : List Nat}
    (hup : IsFranklinUpBranchInput lam) :
    IsStrictPartition (franklinUpMove lam) ∧
      partitionWeight (franklinUpMove lam) = partitionWeight lam ∧
      partSign (franklinUpMove lam) = - partSign lam := by
  rcases hup with ⟨mu, hmu, hshape⟩
  rw [hshape]
  exact franklinUpMove_append_numberOfParts_strict_weight_sign hmu

/-- An up-branch step lands in the down-branch input region, and the down move
immediately returns to the original partition. -/
theorem franklinUpMove_branch_transition_and_inverse {lam : List Nat}
    (hstrict : IsStrictPartition lam) (hup : IsFranklinUpBranchInput lam) :
    IsFranklinDownBranchInput (franklinUpMove lam) ∧
      franklinDownMove (franklinUpMove lam) = lam := by
  rcases hup with ⟨mu, hmu, hshape⟩
  constructor
  · exact IsFranklinDownBranchInput_franklinUpMove hstrict ⟨mu, hmu, hshape⟩
  · rw [hshape]
    exact franklinDownMove_franklinUpMove_append_numberOfParts mu

/-- The Franklin down and up branch input regions are disjoint. -/
theorem not_IsFranklinDownBranchInput_of_IsFranklinUpBranchInput {lam : List Nat}
    (hup : IsFranklinUpBranchInput lam) :
    ¬ IsFranklinDownBranchInput lam := by
  intro hdown
  rcases hup with ⟨mu, _hmu, hshape⟩
  have hmem : numberOfParts mu ∈ lam := by
    rw [hshape]
    simp
  have hbad := hdown.2 (numberOfParts mu) hmem
  rw [hshape] at hbad
  simp [numberOfParts] at hbad
  omega

/-- Symmetric form of branch disjointness. -/
theorem not_IsFranklinUpBranchInput_of_IsFranklinDownBranchInput {lam : List Nat}
    (hdown : IsFranklinDownBranchInput lam) :
    ¬ IsFranklinUpBranchInput lam := by
  intro hup
  exact not_IsFranklinDownBranchInput_of_IsFranklinUpBranchInput hup hdown

/-- Relation form of Franklin's non-fixed move. This avoids choosing a
decidable branch and records only the two active branch transitions. -/
def IsFranklinMovePair (lam mu : List Nat) : Prop :=
  (IsFranklinDownBranchInput lam ∧ mu = franklinDownMove lam) ∨
    (IsFranklinUpBranchInput lam ∧ mu = franklinUpMove lam)

/-- A down-branch input is related to its down move. -/
theorem IsFranklinMovePair_franklinDownMove {lam : List Nat}
    (hdown : IsFranklinDownBranchInput lam) :
    IsFranklinMovePair lam (franklinDownMove lam) :=
  Or.inl ⟨hdown, rfl⟩

/-- An up-branch input is related to its up move. -/
theorem IsFranklinMovePair_franklinUpMove {lam : List Nat}
    (hup : IsFranklinUpBranchInput lam) :
    IsFranklinMovePair lam (franklinUpMove lam) :=
  Or.inr ⟨hup, rfl⟩

/-- A source admits a relation-form Franklin move exactly when it lies in one
of the two active branch-input regions. -/
theorem exists_IsFranklinMovePair_iff (lam : List Nat) :
    (∃ mu : List Nat, IsFranklinMovePair lam mu) ↔
      IsFranklinDownBranchInput lam ∨ IsFranklinUpBranchInput lam := by
  constructor
  · rintro ⟨mu, hpair⟩
    rcases hpair with ⟨hdown, _⟩ | ⟨hup, _⟩
    · exact Or.inl hdown
    · exact Or.inr hup
  · intro hbranch
    rcases hbranch with hdown | hup
    · exact ⟨franklinDownMove lam, IsFranklinMovePair_franklinDownMove hdown⟩
    · exact ⟨franklinUpMove lam, IsFranklinMovePair_franklinUpMove hup⟩

/-- For strict nonempty partitions, the relation-form Franklin move exists
exactly at the two last-row boundaries handled by the current branch relation:
the down region `#parts + 1 < last`, or the up boundary `last = #parts - 1`. -/
theorem exists_IsFranklinMovePair_iff_lastPart_boundary_of_strict
    {lam : List Nat} (hstrict : IsStrictPartition lam) (hne : lam ≠ []) :
    (∃ mu : List Nat, IsFranklinMovePair lam mu) ↔
      numberOfParts lam + 1 < lam.getD (numberOfParts lam - 1) 0 ∨
        lam.getD (numberOfParts lam - 1) 0 = numberOfParts lam - 1 := by
  rw [exists_IsFranklinMovePair_iff,
    IsFranklinDownBranchInput_iff_lastPart_gt_numberOfParts_add_one_of_strict
      hstrict hne,
    IsFranklinUpBranchInput_iff_lastPart_eq_pred_of_strict hstrict hne]

/-- Complement form of the previous theorem: for strict nonempty partitions,
the current relation has no edge exactly when neither handled last-row
boundary holds. -/
theorem not_exists_IsFranklinMovePair_iff_not_lastPart_boundary_of_strict
    {lam : List Nat} (hstrict : IsStrictPartition lam) (hne : lam ≠ []) :
    (¬ ∃ mu : List Nat, IsFranklinMovePair lam mu) ↔
      ¬ numberOfParts lam + 1 < lam.getD (numberOfParts lam - 1) 0 ∧
        lam.getD (numberOfParts lam - 1) 0 ≠ numberOfParts lam - 1 := by
  rw [exists_IsFranklinMovePair_iff_lastPart_boundary_of_strict hstrict hne]
  constructor
  · intro hno
    exact ⟨fun hdown => hno (Or.inl hdown),
      fun hup => hno (Or.inr hup)⟩
  · rintro ⟨hnotDown, hnotUp⟩ (hdown | hup)
    · exact hnotDown hdown
    · exact hnotUp hup

/-- Exact target classification for relation-form Franklin moves from strict
nonempty partitions in terms of the last displayed row. -/
theorem IsFranklinMovePair_iff_lastPart_boundary_of_strict
    {lam mu : List Nat} (hstrict : IsStrictPartition lam) (hne : lam ≠ []) :
    IsFranklinMovePair lam mu ↔
      (numberOfParts lam + 1 < lam.getD (numberOfParts lam - 1) 0 ∧
          mu = franklinDownMove lam) ∨
        (lam.getD (numberOfParts lam - 1) 0 = numberOfParts lam - 1 ∧
          mu = franklinUpMove lam) := by
  constructor
  · intro hpair
    rcases hpair with ⟨hdown, hmu⟩ | ⟨hup, hmu⟩
    · exact Or.inl
        ⟨(IsFranklinDownBranchInput_iff_lastPart_gt_numberOfParts_add_one_of_strict
          hstrict hne).1 hdown, hmu⟩
    · exact Or.inr
        ⟨(IsFranklinUpBranchInput_iff_lastPart_eq_pred_of_strict
          hstrict hne).1 hup, hmu⟩
  · rintro (⟨hdown, rfl⟩ | ⟨hup, rfl⟩)
    · exact Or.inl
        ⟨(IsFranklinDownBranchInput_iff_lastPart_gt_numberOfParts_add_one_of_strict
          hstrict hne).2 hdown, rfl⟩
    · exact Or.inr
        ⟨(IsFranklinUpBranchInput_iff_lastPart_eq_pred_of_strict
          hstrict hne).2 hup, rfl⟩

/-- Exhaustive last-row split for strict nonempty sources with respect to the
current relation-form Franklin move. The two active cases are `last = # - 1`
and `# + 1 < last`; the low residual and middle boundary cases have no
relation edge. -/
theorem IsFranklinMovePair_lastPart_cases_of_strict
    {lam : List Nat} (hstrict : IsStrictPartition lam) (hne : lam ≠ []) :
    (lam.getD (numberOfParts lam - 1) 0 < numberOfParts lam - 1 ∧
        ¬ ∃ mu : List Nat, IsFranklinMovePair lam mu) ∨
      (lam.getD (numberOfParts lam - 1) 0 = numberOfParts lam - 1 ∧
        IsFranklinMovePair lam (franklinUpMove lam)) ∨
      (((lam.getD (numberOfParts lam - 1) 0 = numberOfParts lam) ∨
          lam.getD (numberOfParts lam - 1) 0 = numberOfParts lam + 1) ∧
        ¬ ∃ mu : List Nat, IsFranklinMovePair lam mu) ∨
      (numberOfParts lam + 1 < lam.getD (numberOfParts lam - 1) 0 ∧
        IsFranklinMovePair lam (franklinDownMove lam)) := by
  let last := lam.getD (numberOfParts lam - 1) 0
  by_cases hlow : last < numberOfParts lam - 1
  · left
    constructor
    · simpa [last] using hlow
    · rw [not_exists_IsFranklinMovePair_iff_not_lastPart_boundary_of_strict hstrict hne]
      constructor <;> omega
  · right
    by_cases hup : last = numberOfParts lam - 1
    · left
      constructor
      · simpa [last] using hup
      · exact IsFranklinMovePair_franklinUpMove
          ((IsFranklinUpBranchInput_iff_lastPart_eq_pred_of_strict hstrict hne).2
            (by simpa [last] using hup))
    · right
      by_cases hmid0 : last = numberOfParts lam
      · left
        constructor
        · exact Or.inl (by simpa [last] using hmid0)
        · rw [not_exists_IsFranklinMovePair_iff_not_lastPart_boundary_of_strict hstrict hne]
          constructor <;> omega
      · by_cases hmid1 : last = numberOfParts lam + 1
        · left
          constructor
          · exact Or.inr (by simpa [last] using hmid1)
          · rw [not_exists_IsFranklinMovePair_iff_not_lastPart_boundary_of_strict hstrict hne]
            constructor <;> omega
        · right
          have hdown : numberOfParts lam + 1 < last := by omega
          constructor
          · simpa [last] using hdown
          · exact IsFranklinMovePair_franklinDownMove
              ((IsFranklinDownBranchInput_iff_lastPart_gt_numberOfParts_add_one_of_strict
                hstrict hne).2 (by simpa [last] using hdown))

/-- The relation form is single-valued from a fixed source: the down and up
branch input regions are disjoint, and each branch has a fixed target. -/
theorem IsFranklinMovePair.eq_of_left {lam mu nu : List Nat}
    (hmu : IsFranklinMovePair lam mu) (hnu : IsFranklinMovePair lam nu) :
    mu = nu := by
  rcases hmu with ⟨hdown, rfl⟩ | ⟨hup, rfl⟩
  · rcases hnu with ⟨_hdown', rfl⟩ | ⟨hup', _hnu⟩
    · rfl
    · exact False.elim (not_IsFranklinDownBranchInput_of_IsFranklinUpBranchInput hup' hdown)
  · rcases hnu with ⟨hdown', _hnu⟩ | ⟨_hup', rfl⟩
    · exact False.elim (not_IsFranklinUpBranchInput_of_IsFranklinDownBranchInput hdown' hup)
    · rfl

/-- On strict branch inputs, the relation form of Franklin's move is symmetric:
the target lies in the opposite branch and moves back to the source. -/
theorem IsFranklinMovePair.symm_of_strict {lam mu : List Nat}
    (hstrict : IsStrictPartition lam) (hpair : IsFranklinMovePair lam mu) :
    IsFranklinMovePair mu lam := by
  rcases hpair with ⟨hdown, rfl⟩ | ⟨hup, rfl⟩
  · have hpack := franklinDownMove_branch_transition_and_inverse hstrict hdown
    exact Or.inr ⟨hpack.1, hpack.2.symm⟩
  · have hpack := franklinUpMove_branch_transition_and_inverse hstrict hup
    exact Or.inl ⟨hpack.1, hpack.2.symm⟩

/-- On strict endpoints, the relation form of Franklin's move is symmetric
as an iff. -/
theorem IsFranklinMovePair_comm_iff_of_strict {lam mu : List Nat}
    (hlam : IsStrictPartition lam) (hmu : IsStrictPartition mu) :
    IsFranklinMovePair lam mu ↔ IsFranklinMovePair mu lam := by
  constructor
  · exact IsFranklinMovePair.symm_of_strict hlam
  · exact IsFranklinMovePair.symm_of_strict hmu

/-- Right-uniqueness on strict sources: two strict branch inputs paired with
the same target must be equal. -/
theorem IsFranklinMovePair.eq_of_right_of_strict {lam mu nu : List Nat}
    (hlam : IsStrictPartition lam) (hmu : IsStrictPartition mu)
    (hpair_lam : IsFranklinMovePair lam nu) (hpair_mu : IsFranklinMovePair mu nu) :
    lam = mu := by
  exact IsFranklinMovePair.eq_of_left
    (IsFranklinMovePair.symm_of_strict hlam hpair_lam)
    (IsFranklinMovePair.symm_of_strict hmu hpair_mu)

/-- On strict branch inputs, the relation form of Franklin's move preserves
weight, reverses sign, and outputs a strict partition. -/
theorem IsFranklinMovePair.strict_weight_sign {lam mu : List Nat}
    (hstrict : IsStrictPartition lam) (hpair : IsFranklinMovePair lam mu) :
    IsStrictPartition mu ∧
      partitionWeight mu = partitionWeight lam ∧
      partSign mu = - partSign lam := by
  rcases hpair with ⟨hdown, rfl⟩ | ⟨hup, rfl⟩
  · exact franklinDownMove_strict_weight_sign_of_branch_input hstrict hdown
  · exact franklinUpMove_strict_weight_sign_of_branch_input hup

/-- A strict partition cannot be paired with itself by Franklin's
sign-reversing move relation. -/
theorem IsFranklinMovePair.not_self_of_strict {lam : List Nat}
    (hstrict : IsStrictPartition lam) :
    ¬ IsFranklinMovePair lam lam := by
  intro hpair
  have hsign := (IsFranklinMovePair.strict_weight_sign hstrict hpair).2.2
  rcases partSign_eq_one_or_neg_one lam with h | h <;> rw [h] at hsign <;> norm_num at hsign

/-- Equivalent inequality form of the no-fixed-point property. -/
theorem IsFranklinMovePair.ne_of_strict {lam mu : List Nat}
    (hstrict : IsStrictPartition lam) (hpair : IsFranklinMovePair lam mu) :
    mu ≠ lam := by
  intro hmu
  subst mu
  exact IsFranklinMovePair.not_self_of_strict hstrict hpair

/-- Consolidated relation-form Franklin package: from a strict source and one
move-pair edge, the target is strict, points back to the source, preserves
weight, reverses sign, and is not the source. -/
theorem IsFranklinMovePair.involution_package {lam mu : List Nat}
    (hstrict : IsStrictPartition lam) (hpair : IsFranklinMovePair lam mu) :
    IsStrictPartition mu ∧
      IsFranklinMovePair mu lam ∧
      partitionWeight mu = partitionWeight lam ∧
      partSign mu = - partSign lam ∧
      mu ≠ lam := by
  have hpack := IsFranklinMovePair.strict_weight_sign hstrict hpair
  exact ⟨hpack.1, IsFranklinMovePair.symm_of_strict hstrict hpair,
    hpack.2.1, hpack.2.2, IsFranklinMovePair.ne_of_strict hstrict hpair⟩

/-- Cancellation form of sign reversal for a relation-form Franklin pair. -/
theorem IsFranklinMovePair.partSign_add_eq_zero {lam mu : List Nat}
    (hstrict : IsStrictPartition lam) (hpair : IsFranklinMovePair lam mu) :
    partSign lam + partSign mu = 0 := by
  have hsign := (IsFranklinMovePair.strict_weight_sign hstrict hpair).2.2
  rw [hsign]
  omega

/-- Symmetric cancellation form of sign reversal for a relation-form Franklin
pair. -/
theorem IsFranklinMovePair.partSign_add_eq_zero' {lam mu : List Nat}
    (hstrict : IsStrictPartition lam) (hpair : IsFranklinMovePair lam mu) :
    partSign mu + partSign lam = 0 := by
  rw [Int.add_comm]
  exact IsFranklinMovePair.partSign_add_eq_zero hstrict hpair

/-- A list displayed in the explicit up-branch input shape has last part equal
to one less than its total number of parts. -/
theorem append_numberOfParts_lastPart (mu : List Nat) :
    (mu ++ [numberOfParts mu]).getD
        (numberOfParts (mu ++ [numberOfParts mu]) - 1) 0 =
      numberOfParts (mu ++ [numberOfParts mu]) - 1 := by
  simp [numberOfParts]

/-- A shifted staircase has parts `[n+d, n-1+d, ..., 1+d]`.  These shapes are
the fixed pentagonal configurations in Franklin's involution. -/
def shiftedStaircasePartition (d n : Nat) : List Nat :=
  shiftParts d (staircasePartition n)

theorem shiftedStaircasePartition_zero (d : Nat) :
    shiftedStaircasePartition d 0 = [] := by
  rfl

theorem shiftedStaircasePartition_one (d : Nat) :
    shiftedStaircasePartition d 1 = [1 + d] := by
  rfl

theorem shiftedStaircasePartition_three_one :
    shiftedStaircasePartition 1 3 = [4, 3, 2] := by
  rfl

theorem numberOfParts_shiftedStaircasePartition (d n : Nat) :
    numberOfParts (shiftedStaircasePartition d n) = n := by
  rw [shiftedStaircasePartition, numberOfParts_shiftParts,
    numberOfParts_staircasePartition]

/-- The `r`-th displayed part of a shifted staircase is `n - r + d`. -/
theorem shiftedStaircasePartition_getD_of_lt {d n r : Nat} (hr : r < n) :
    (shiftedStaircasePartition d n).getD r 0 = n - r + d := by
  rw [shiftedStaircasePartition, shiftParts_getD_of_lt]
  · rw [staircasePartition_getD_of_lt hr]
  · simpa [staircasePartition_length] using hr

theorem shiftedStaircasePartition_lastPart (d n : Nat) (hn : 0 < n) :
    (shiftedStaircasePartition d n).getD (n - 1) 0 = 1 + d := by
  rw [shiftedStaircasePartition_getD_of_lt (by omega)]
  omega

theorem shiftedStaircasePartition_succ_append (d n : Nat) :
    shiftedStaircasePartition d (n + 1) =
      shiftedStaircasePartition (d + 1) n ++ [1 + d] := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [shiftedStaircasePartition, shiftParts, staircasePartition] at ih ⊢
      rw [ih]
      simp [Nat.add_comm, Nat.add_left_comm]

/-- Uniformly shifting a shifted staircase only changes its offset. -/
theorem shiftParts_shiftedStaircasePartition (a d n : Nat) :
    shiftParts a (shiftedStaircasePartition d n) =
      shiftedStaircasePartition (d + a) n := by
  rw [shiftedStaircasePartition, shiftedStaircasePartition,
    shiftParts_shiftParts]

/-- Shortening every part of a shifted staircase with positive offset lowers
the offset by one. -/
theorem decrementParts_shiftedStaircasePartition_succ_offset (d n : Nat) :
    decrementParts (shiftedStaircasePartition (d + 1) n) =
      shiftedStaircasePartition d n := by
  rw [shiftedStaircasePartition, shiftedStaircasePartition,
    decrementParts_shiftParts_succ]

/-- The up move removes the last row of a nonempty shifted staircase and
raises the remaining offset by two. -/
theorem franklinUpMove_shiftedStaircasePartition_succ (d n : Nat) :
    franklinUpMove (shiftedStaircasePartition d (n + 1)) =
      shiftedStaircasePartition (d + 2) n := by
  rw [shiftedStaircasePartition_succ_append, franklinUpMove_append_singleton,
    shiftParts_shiftedStaircasePartition]

/-- Positive-height form of the explicit up-move formula. -/
theorem franklinUpMove_shiftedStaircasePartition_of_pos_height
    {d k : Nat} (hk : 0 < k) :
    franklinUpMove (shiftedStaircasePartition d k) =
      shiftedStaircasePartition (d + 2) (k - 1) := by
  have hkdecomp : k = (k - 1) + 1 := by omega
  rw [hkdecomp, franklinUpMove_shiftedStaircasePartition_succ]
  congr

/-- The down move on a shifted staircase with positive offset shortens the
offset and appends the old height as the new last row. -/
theorem franklinDownMove_shiftedStaircasePartition_succ_offset (d n : Nat) :
    franklinDownMove (shiftedStaircasePartition (d + 1) n) =
      shiftedStaircasePartition d n ++ [n] := by
  rw [franklinDownMove, decrementParts_shiftedStaircasePartition_succ_offset,
    numberOfParts_shiftedStaircasePartition]

/-- Positive-offset form of the explicit down-move formula. -/
theorem franklinDownMove_shiftedStaircasePartition_of_pos_offset
    {d k : Nat} (hd : 0 < d) :
    franklinDownMove (shiftedStaircasePartition d k) =
      shiftedStaircasePartition (d - 1) k ++ [k] := by
  have hddecomp : d = (d - 1) + 1 := by omega
  rw [hddecomp, franklinDownMove_shiftedStaircasePartition_succ_offset]
  congr

/-- For a positive-height shifted staircase, Franklin's down-branch inequality
holds exactly when the offset is strictly larger than the height. -/
theorem franklinDownMove_hgt_shiftedStaircasePartition_iff
    {d k : Nat} (hk : 0 < k) :
    (∀ n, n ∈ shiftedStaircasePartition d k →
      numberOfParts (shiftedStaircasePartition d k) + 1 < n) ↔
      k < d := by
  constructor
  · intro hgt
    have hlen : k - 1 < (shiftedStaircasePartition d k).length := by
      simpa [numberOfParts] using
        (show k - 1 < numberOfParts (shiftedStaircasePartition d k) by
          rw [numberOfParts_shiftedStaircasePartition]
          omega)
    have hmem := getD_mem_of_lt (shiftedStaircasePartition d k) (d := 0) hlen
    have hlast : 1 + d ∈ shiftedStaircasePartition d k := by
      rwa [shiftedStaircasePartition_lastPart d k hk] at hmem
    have hbad := hgt (1 + d) hlast
    rw [numberOfParts_shiftedStaircasePartition] at hbad
    omega
  · intro hkd n hn
    unfold shiftedStaircasePartition shiftParts at hn
    rcases List.mem_map.mp hn with ⟨m, hm, rfl⟩
    have hmpos := PositiveParts_staircasePartition k m hm
    rw [numberOfParts_shiftedStaircasePartition]
    omega

theorem not_franklinDownMove_hgt_shiftedStaircasePartition_iff
    {d k : Nat} (hk : 0 < k) :
    ¬ (∀ n, n ∈ shiftedStaircasePartition d k →
      numberOfParts (shiftedStaircasePartition d k) + 1 < n) ↔
      d ≤ k := by
  rw [franklinDownMove_hgt_shiftedStaircasePartition_iff hk]
  omega

/-- Extensional recognition of shifted staircases from their displayed row
formula. -/
theorem eq_shiftedStaircasePartition_of_getD {lam : List Nat} {d n : Nat}
    (hlen : numberOfParts lam = n)
    (hget : ∀ r, r < n → lam.getD r 0 = n - r + d) :
    lam = shiftedStaircasePartition d n := by
  apply List.ext_getElem
  · have hshift : (shiftedStaircasePartition d n).length = n := by
      simpa [numberOfParts] using numberOfParts_shiftedStaircasePartition d n
    simpa [numberOfParts, hshift] using hlen
  · intro r hlam hshift
    have hshift_len : (shiftedStaircasePartition d n).length = n := by
      simpa [numberOfParts] using numberOfParts_shiftedStaircasePartition d n
    have hrn : r < n := by omega
    rw [← List.getD_eq_getElem (l := lam) (d := 0) hlam,
      ← List.getD_eq_getElem (l := shiftedStaircasePartition d n) (d := 0) hshift,
      hget r hrn, shiftedStaircasePartition_getD_of_lt hrn]

/-- A shifted staircase has parity determined by its height. -/
theorem partParity_shiftedStaircasePartition (d n : Nat) :
    partParity (shiftedStaircasePartition d n) = n % 2 := by
  rw [shiftedStaircasePartition, partParity_shiftParts,
    partParity_staircasePartition]

/-- A shifted staircase has Franklin sign determined by its height. -/
theorem partSign_shiftedStaircasePartition (d n : Nat) :
    partSign (shiftedStaircasePartition d n) = if n % 2 = 0 then 1 else -1 := by
  rw [shiftedStaircasePartition, partSign_shiftParts,
    partSign_staircasePartition]

theorem partitionWeight_shiftedStaircasePartition (d n : Nat) :
    partitionWeight (shiftedStaircasePartition d n) = triangular n + d * n := by
  rw [shiftedStaircasePartition, partitionWeight_shiftParts,
    partitionWeight_staircasePartition, numberOfParts_staircasePartition]

theorem IsStrictPartition_shiftedStaircasePartition (d n : Nat) :
    IsStrictPartition (shiftedStaircasePartition d n) := by
  exact IsStrictPartition_shiftParts (IsStrictPartition_staircasePartition n)

/-- The lower pentagonal staircase of height `k`, with weight
`k(3k-1)/2`. -/
def lowerPentagonalPartition (k : Nat) : List Nat :=
  shiftedStaircasePartition (k - 1) k

/-- The upper pentagonal staircase of height `k`, with weight
`k(3k+1)/2`. -/
def upperPentagonalPartition (k : Nat) : List Nat :=
  shiftedStaircasePartition k k

/-- The positive-side companion to `pentagonalNumber k = k(3k-1)/2`, written
in the triangular-plus-square form used by the shifted staircase weight. -/
def upperPentagonalNumber (k : Nat) : Nat :=
  triangular k + k * k

/-- The two fixed-shape families in Franklin's involution: lower and upper
pentagonal shifted staircases. The height is required positive so the empty
partition is not classified as a pentagonal fixed shape here. -/
def IsPentagonalFixedShape (lam : List Nat) : Prop :=
  ∃ k, 0 < k ∧ (lam = lowerPentagonalPartition k ∨ lam = upperPentagonalPartition k)

theorem IsPentagonalFixedShape_lower (k : Nat) (hk : 0 < k) :
    IsPentagonalFixedShape (lowerPentagonalPartition k) :=
  ⟨k, hk, Or.inl rfl⟩

theorem IsPentagonalFixedShape_upper (k : Nat) (hk : 0 < k) :
    IsPentagonalFixedShape (upperPentagonalPartition k) :=
  ⟨k, hk, Or.inr rfl⟩

theorem eq_lowerPentagonalPartition_of_getD {lam : List Nat} {k : Nat}
    (hlen : numberOfParts lam = k)
    (hget : ∀ r, r < k → lam.getD r 0 = k - r + (k - 1)) :
    lam = lowerPentagonalPartition k := by
  rw [lowerPentagonalPartition]
  exact eq_shiftedStaircasePartition_of_getD hlen hget

theorem eq_upperPentagonalPartition_of_getD {lam : List Nat} {k : Nat}
    (hlen : numberOfParts lam = k)
    (hget : ∀ r, r < k → lam.getD r 0 = k - r + k) :
    lam = upperPentagonalPartition k := by
  rw [upperPentagonalPartition]
  exact eq_shiftedStaircasePartition_of_getD hlen hget

theorem eq_lowerPentagonalPartition_of_firstPart_and_successive {lam : List Nat} {k : Nat}
    (hlen : numberOfParts lam = k)
    (hfirst : lam.getD 0 0 = 2 * k - 1)
    (hsucc : ∀ r, r + 1 < k → lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    lam = lowerPentagonalPartition k := by
  apply eq_lowerPentagonalPartition_of_getD hlen
  intro r hr
  have hrow : lam.getD r 0 = lam.getD 0 0 - r := by
    induction r with
    | zero =>
        simp
    | succ r ih =>
        have hr' : r < k := by omega
        have hsucc' := hsucc r hr
        rw [ih hr'] at hsucc'
        omega
  rw [hrow, hfirst]
  omega

theorem eq_upperPentagonalPartition_of_firstPart_and_successive {lam : List Nat} {k : Nat}
    (hlen : numberOfParts lam = k)
    (hfirst : lam.getD 0 0 = 2 * k)
    (hsucc : ∀ r, r + 1 < k → lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    lam = upperPentagonalPartition k := by
  apply eq_upperPentagonalPartition_of_getD hlen
  intro r hr
  have hrow : lam.getD r 0 = lam.getD 0 0 - r := by
    induction r with
    | zero =>
        simp
    | succ r ih =>
        have hr' : r < k := by omega
        have hsucc' := hsucc r hr
        rw [ih hr'] at hsucc'
        omega
  rw [hrow, hfirst]
  omega

/-- Along a finite run of adjacent rows differing by one, the row at the
start equals the row at the end plus the number of steps. -/
theorem getD_eq_last_add_of_successive_from {lam : List Nat} {s k : Nat} (hk : 0 < k)
    (hsucc : ∀ r, s ≤ r → r + 1 < s + k →
      lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    lam.getD s 0 = lam.getD (s + k - 1) 0 + (k - 1) := by
  induction k generalizing s with
  | zero =>
      omega
  | succ k ih =>
      cases k with
      | zero =>
          simp
      | succ k =>
          have hfirst := hsucc s (by omega) (by omega)
          have htail : lam.getD (s + 1) 0 =
              lam.getD (s + (k + 1 + 1) - 1) 0 + k := by
            have ih' := ih (s := s + 1) (by omega) (fun r hsr hr => by
              exact hsucc r (by omega) (by omega))
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih'
          rw [htail] at hfirst
          omega

theorem getD_zero_eq_last_add_of_successive {lam : List Nat} {k : Nat} (hk : 0 < k)
    (hsucc : ∀ r, r + 1 < k → lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    lam.getD 0 0 = lam.getD (k - 1) 0 + (k - 1) := by
  simpa using getD_eq_last_add_of_successive_from (lam := lam) (s := 0) hk
    (fun r _ hr => hsucc r (by simpa using hr))

theorem eq_lowerPentagonalPartition_of_lastPart_and_successive {lam : List Nat} {k : Nat}
    (hk : 0 < k) (hlen : numberOfParts lam = k)
    (hlast : lam.getD (k - 1) 0 = k)
    (hsucc : ∀ r, r + 1 < k → lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    lam = lowerPentagonalPartition k := by
  apply eq_lowerPentagonalPartition_of_firstPart_and_successive hlen
  · have h0 := getD_zero_eq_last_add_of_successive hk hsucc
    rw [hlast] at h0
    rw [h0]
    omega
  · exact hsucc

theorem eq_upperPentagonalPartition_of_lastPart_and_successive {lam : List Nat} {k : Nat}
    (hk : 0 < k) (hlen : numberOfParts lam = k)
    (hlast : lam.getD (k - 1) 0 = k + 1)
    (hsucc : ∀ r, r + 1 < k → lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    lam = upperPentagonalPartition k := by
  apply eq_upperPentagonalPartition_of_firstPart_and_successive hlen
  · have h0 := getD_zero_eq_last_add_of_successive hk hsucc
    rw [hlast] at h0
    rw [h0]
    omega
  · exact hsucc

theorem IsPentagonalFixedShape_of_lastPart_eq_numberOfParts_or_add_one_and_successive
    {lam : List Nat} {k : Nat} (hk : 0 < k) (hlen : numberOfParts lam = k)
    (hlast :
      lam.getD (k - 1) 0 = k ∨ lam.getD (k - 1) 0 = k + 1)
    (hsucc : ∀ r, r + 1 < k → lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    IsPentagonalFixedShape lam := by
  rcases hlast with hlast | hlast
  · exact ⟨k, hk,
      Or.inl (eq_lowerPentagonalPartition_of_lastPart_and_successive
        hk hlen hlast hsucc)⟩
  · exact ⟨k, hk,
      Or.inr (eq_upperPentagonalPartition_of_lastPart_and_successive
        hk hlen hlast hsucc)⟩

theorem IsPentagonalFixedShape_of_lastPart_eq_numberOfParts_or_add_one
    {lam : List Nat} (hlen : 0 < numberOfParts lam)
    (hlast :
      lam.getD (numberOfParts lam - 1) 0 = numberOfParts lam ∨
        lam.getD (numberOfParts lam - 1) 0 = numberOfParts lam + 1)
    (hsucc : ∀ r, r + 1 < numberOfParts lam →
      lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    IsPentagonalFixedShape lam :=
  IsPentagonalFixedShape_of_lastPart_eq_numberOfParts_or_add_one_and_successive
    hlen rfl hlast hsucc

theorem lowerPentagonalPartition_three :
    lowerPentagonalPartition 3 = [5, 4, 3] := by
  rfl

theorem upperPentagonalPartition_three :
    upperPentagonalPartition 3 = [6, 5, 4] := by
  rfl

/-- The `r`-th displayed part of the lower pentagonal staircase. -/
theorem lowerPentagonalPartition_getD_of_lt {k r : Nat} (hr : r < k) :
    (lowerPentagonalPartition k).getD r 0 = k - r + (k - 1) := by
  rw [lowerPentagonalPartition, shiftedStaircasePartition_getD_of_lt hr]

/-- The `r`-th displayed part of the upper pentagonal staircase. -/
theorem upperPentagonalPartition_getD_of_lt {k r : Nat} (hr : r < k) :
    (upperPentagonalPartition k).getD r 0 = k - r + k := by
  rw [upperPentagonalPartition, shiftedStaircasePartition_getD_of_lt hr]

/-- The last displayed part of the lower pentagonal fixed shape is `k`. -/
theorem lowerPentagonalPartition_lastPart (k : Nat) (hk : 0 < k) :
    (lowerPentagonalPartition k).getD (k - 1) 0 = k := by
  rw [lowerPentagonalPartition_getD_of_lt (by omega)]
  omega

/-- The last displayed part of the upper pentagonal fixed shape is `k + 1`. -/
theorem upperPentagonalPartition_lastPart (k : Nat) (hk : 0 < k) :
    (upperPentagonalPartition k).getD (k - 1) 0 = k + 1 := by
  rw [upperPentagonalPartition_getD_of_lt (by omega)]
  omega

/-- The first row of the lower pentagonal fixed shape has length `2k - 1`. -/
theorem lowerPentagonalPartition_firstPart (k : Nat) (hk : 0 < k) :
    (lowerPentagonalPartition k).getD 0 0 = 2 * k - 1 := by
  rw [lowerPentagonalPartition_getD_of_lt (by omega)]
  omega

/-- The first row of the upper pentagonal fixed shape has length `2k`. -/
theorem upperPentagonalPartition_firstPart (k : Nat) (hk : 0 < k) :
    (upperPentagonalPartition k).getD 0 0 = 2 * k := by
  rw [upperPentagonalPartition_getD_of_lt (by omega)]
  omega

/-- Consecutive rows of the lower pentagonal fixed shape differ by one. -/
theorem lowerPentagonalPartition_successive_getD (k r : Nat) (hr : r + 1 < k) :
    (lowerPentagonalPartition k).getD (r + 1) 0 + 1 =
      (lowerPentagonalPartition k).getD r 0 := by
  rw [lowerPentagonalPartition_getD_of_lt hr,
    lowerPentagonalPartition_getD_of_lt (by omega)]
  omega

/-- Consecutive rows of the upper pentagonal fixed shape differ by one. -/
theorem upperPentagonalPartition_successive_getD (k r : Nat) (hr : r + 1 < k) :
    (upperPentagonalPartition k).getD (r + 1) 0 + 1 =
      (upperPentagonalPartition k).getD r 0 := by
  rw [upperPentagonalPartition_getD_of_lt hr,
    upperPentagonalPartition_getD_of_lt (by omega)]
  omega

theorem triangular_add_pred_mul_eq_pentagonalNumber (k : Nat) :
    triangular k + (k - 1) * k = pentagonalNumber k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      cases k with
      | zero =>
          simp [triangular_succ, pentagonalNumber]
      | succ j =>
          rw [triangular_succ, pentagonalNumber_succ, ← ih]
          simp [Nat.succ_eq_add_one]
          nlinarith

theorem partitionWeight_lowerPentagonalPartition (k : Nat) :
    partitionWeight (lowerPentagonalPartition k) = pentagonalNumber k := by
  rw [lowerPentagonalPartition, partitionWeight_shiftedStaircasePartition]
  exact triangular_add_pred_mul_eq_pentagonalNumber k

theorem partitionWeight_upperPentagonalPartition (k : Nat) :
    partitionWeight (upperPentagonalPartition k) = upperPentagonalNumber k := by
  rw [upperPentagonalPartition, partitionWeight_shiftedStaircasePartition,
    upperPentagonalNumber]

/-- The lower pentagonal fixed shape has `k` parts. -/
theorem numberOfParts_lowerPentagonalPartition (k : Nat) :
    numberOfParts (lowerPentagonalPartition k) = k := by
  rw [lowerPentagonalPartition, numberOfParts_shiftedStaircasePartition]

/-- The upper pentagonal fixed shape has `k` parts. -/
theorem numberOfParts_upperPentagonalPartition (k : Nat) :
    numberOfParts (upperPentagonalPartition k) = k := by
  rw [upperPentagonalPartition, numberOfParts_shiftedStaircasePartition]

theorem lowerPentagonalPartition_lastPart_mem (k : Nat) (hk : 0 < k) :
    k ∈ lowerPentagonalPartition k := by
  have hlen : k - 1 < (lowerPentagonalPartition k).length := by
    simpa [numberOfParts] using
      (show k - 1 < numberOfParts (lowerPentagonalPartition k) by
        rw [numberOfParts_lowerPentagonalPartition]
        omega)
  have hmem := getD_mem_of_lt (lowerPentagonalPartition k) (d := 0) hlen
  rwa [lowerPentagonalPartition_lastPart k hk] at hmem

theorem upperPentagonalPartition_lastPart_mem (k : Nat) (hk : 0 < k) :
    k + 1 ∈ upperPentagonalPartition k := by
  have hlen : k - 1 < (upperPentagonalPartition k).length := by
    simpa [numberOfParts] using
      (show k - 1 < numberOfParts (upperPentagonalPartition k) by
        rw [numberOfParts_upperPentagonalPartition]
        omega)
  have hmem := getD_mem_of_lt (upperPentagonalPartition k) (d := 0) hlen
  rwa [upperPentagonalPartition_lastPart k hk] at hmem

theorem lowerPentagonalPartition_lastPart_eq_numberOfParts (k : Nat) (hk : 0 < k) :
    (lowerPentagonalPartition k).getD (numberOfParts (lowerPentagonalPartition k) - 1) 0 =
      numberOfParts (lowerPentagonalPartition k) := by
  rw [numberOfParts_lowerPentagonalPartition, lowerPentagonalPartition_lastPart k hk]

theorem upperPentagonalPartition_lastPart_eq_numberOfParts_add_one (k : Nat) (hk : 0 < k) :
    (upperPentagonalPartition k).getD (numberOfParts (upperPentagonalPartition k) - 1) 0 =
      numberOfParts (upperPentagonalPartition k) + 1 := by
  rw [numberOfParts_upperPentagonalPartition, upperPentagonalPartition_lastPart k hk]

theorem not_franklinDownMove_hgt_lowerPentagonalPartition (k : Nat) (hk : 0 < k) :
    ¬ (∀ n, n ∈ lowerPentagonalPartition k →
      numberOfParts (lowerPentagonalPartition k) + 1 < n) := by
  intro hgt
  have hbad := hgt k (lowerPentagonalPartition_lastPart_mem k hk)
  rw [numberOfParts_lowerPentagonalPartition] at hbad
  omega

theorem not_franklinDownMove_hgt_upperPentagonalPartition (k : Nat) (hk : 0 < k) :
    ¬ (∀ n, n ∈ upperPentagonalPartition k →
      numberOfParts (upperPentagonalPartition k) + 1 < n) := by
  intro hgt
  have hbad := hgt (k + 1) (upperPentagonalPartition_lastPart_mem k hk)
  rw [numberOfParts_upperPentagonalPartition] at hbad
  omega

theorem not_lowerPentagonalPartition_eq_append_numberOfParts (k : Nat) (hk : 0 < k) :
    ¬ ∃ mu : List Nat, lowerPentagonalPartition k = mu ++ [numberOfParts mu] := by
  rintro ⟨mu, hmu⟩
  have hshape := append_numberOfParts_lastPart mu
  rw [← hmu] at hshape
  have hfixed := lowerPentagonalPartition_lastPart_eq_numberOfParts k hk
  rw [hfixed] at hshape
  rw [numberOfParts_lowerPentagonalPartition] at hshape
  omega

theorem not_upperPentagonalPartition_eq_append_numberOfParts (k : Nat) (hk : 0 < k) :
    ¬ ∃ mu : List Nat, upperPentagonalPartition k = mu ++ [numberOfParts mu] := by
  rintro ⟨mu, hmu⟩
  have hshape := append_numberOfParts_lastPart mu
  rw [← hmu] at hshape
  have hfixed := upperPentagonalPartition_lastPart_eq_numberOfParts_add_one k hk
  rw [hfixed] at hshape
  rw [numberOfParts_upperPentagonalPartition] at hshape
  omega

theorem not_franklinDownMove_hgt_of_IsPentagonalFixedShape {lam : List Nat}
    (hfixed : IsPentagonalFixedShape lam) :
    ¬ (∀ n, n ∈ lam → numberOfParts lam + 1 < n) := by
  rcases hfixed with ⟨k, hk, hlow | hup⟩
  · rw [hlow]
    exact not_franklinDownMove_hgt_lowerPentagonalPartition k hk
  · rw [hup]
    exact not_franklinDownMove_hgt_upperPentagonalPartition k hk

theorem not_eq_append_numberOfParts_of_IsPentagonalFixedShape {lam : List Nat}
    (hfixed : IsPentagonalFixedShape lam) :
    ¬ ∃ mu : List Nat, lam = mu ++ [numberOfParts mu] := by
  rcases hfixed with ⟨k, hk, hlow | hup⟩
  · rw [hlow]
    exact not_lowerPentagonalPartition_eq_append_numberOfParts k hk
  · rw [hup]
    exact not_upperPentagonalPartition_eq_append_numberOfParts k hk

/-- A pentagonal fixed shape is not in the down-branch input region. -/
theorem not_IsFranklinDownBranchInput_of_IsPentagonalFixedShape {lam : List Nat}
    (hfixed : IsPentagonalFixedShape lam) :
    ¬ IsFranklinDownBranchInput lam := by
  intro hdown
  exact not_franklinDownMove_hgt_of_IsPentagonalFixedShape hfixed hdown.2

/-- A pentagonal fixed shape is not in the up-branch input region. -/
theorem not_IsFranklinUpBranchInput_of_IsPentagonalFixedShape {lam : List Nat}
    (hfixed : IsPentagonalFixedShape lam) :
    ¬ IsFranklinUpBranchInput lam := by
  intro hup
  rcases hup with ⟨mu, _hmu, hshape⟩
  exact not_eq_append_numberOfParts_of_IsPentagonalFixedShape hfixed ⟨mu, hshape⟩

/-- Pentagonal fixed shapes are outside the relation-form Franklin move domain. -/
theorem not_IsFranklinMovePair_of_IsPentagonalFixedShape_left {lam mu : List Nat}
    (hfixed : IsPentagonalFixedShape lam) :
    ¬ IsFranklinMovePair lam mu := by
  intro hpair
  rcases hpair with ⟨hdown, _⟩ | ⟨hup, _⟩
  · exact not_IsFranklinDownBranchInput_of_IsPentagonalFixedShape hfixed hdown
  · exact not_IsFranklinUpBranchInput_of_IsPentagonalFixedShape hfixed hup

/-- Existential form: pentagonal fixed shapes admit no relation-form Franklin
move. -/
theorem not_exists_IsFranklinMovePair_of_IsPentagonalFixedShape_left
    {lam : List Nat} (hfixed : IsPentagonalFixedShape lam) :
    ¬ ∃ mu : List Nat, IsFranklinMovePair lam mu := by
  rintro ⟨mu, hpair⟩
  exact not_IsFranklinMovePair_of_IsPentagonalFixedShape_left hfixed hpair

/-- Middle last-row boundary plus consecutive row differences gives a
pentagonal fixed shape, hence no relation-form Franklin move. -/
theorem not_IsFranklinMovePair_of_middle_lastPart_and_successive
    {lam mu : List Nat} (hlen : 0 < numberOfParts lam)
    (hlast :
      lam.getD (numberOfParts lam - 1) 0 = numberOfParts lam ∨
        lam.getD (numberOfParts lam - 1) 0 = numberOfParts lam + 1)
    (hsucc : ∀ r, r + 1 < numberOfParts lam →
      lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    ¬ IsFranklinMovePair lam mu := by
  exact not_IsFranklinMovePair_of_IsPentagonalFixedShape_left
    (IsPentagonalFixedShape_of_lastPart_eq_numberOfParts_or_add_one
      hlen hlast hsucc)

/-- Existential no-edge form of
`not_IsFranklinMovePair_of_middle_lastPart_and_successive`. -/
theorem not_exists_IsFranklinMovePair_of_middle_lastPart_and_successive
    {lam : List Nat} (hlen : 0 < numberOfParts lam)
    (hlast :
      lam.getD (numberOfParts lam - 1) 0 = numberOfParts lam ∨
        lam.getD (numberOfParts lam - 1) 0 = numberOfParts lam + 1)
    (hsucc : ∀ r, r + 1 < numberOfParts lam →
      lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    ¬ ∃ mu : List Nat, IsFranklinMovePair lam mu := by
  rintro ⟨mu, hpair⟩
  exact not_IsFranklinMovePair_of_middle_lastPart_and_successive
    hlen hlast hsucc hpair

/-- For strict nonempty sources with consecutive row differences equal to one,
the last-row split becomes the expected Franklin split: low residual no-edge,
up move, pentagonal fixed no-edge, or down move. -/
theorem IsFranklinMovePair_successive_lastPart_cases_of_strict
    {lam : List Nat} (hstrict : IsStrictPartition lam) (hne : lam ≠ [])
    (hsucc : ∀ r, r + 1 < numberOfParts lam →
      lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    (lam.getD (numberOfParts lam - 1) 0 < numberOfParts lam - 1 ∧
        ¬ ∃ mu : List Nat, IsFranklinMovePair lam mu) ∨
      (lam.getD (numberOfParts lam - 1) 0 = numberOfParts lam - 1 ∧
        IsFranklinMovePair lam (franklinUpMove lam)) ∨
      (IsPentagonalFixedShape lam ∧
        ¬ ∃ mu : List Nat, IsFranklinMovePair lam mu) ∨
      (numberOfParts lam + 1 < lam.getD (numberOfParts lam - 1) 0 ∧
        IsFranklinMovePair lam (franklinDownMove lam)) := by
  rcases IsFranklinMovePair_lastPart_cases_of_strict hstrict hne with
    hlow | hup | hmid | hdown
  · exact Or.inl hlow
  · exact Or.inr (Or.inl hup)
  · refine Or.inr (Or.inr (Or.inl ?_))
    have hlen : 0 < numberOfParts lam := by
      simpa [numberOfParts, List.length_pos_iff] using hne
    exact ⟨IsPentagonalFixedShape_of_lastPart_eq_numberOfParts_or_add_one
      hlen hmid.1 hsucc, hmid.2⟩
  · exact Or.inr (Or.inr (Or.inr hdown))

/-- Under the same consecutive-difference hypothesis, no relation-form
Franklin edge exists exactly in the low residual case or at a pentagonal fixed
shape. -/
theorem not_exists_IsFranklinMovePair_iff_low_or_fixed_of_successive_of_strict
    {lam : List Nat} (hstrict : IsStrictPartition lam) (hne : lam ≠ [])
    (hsucc : ∀ r, r + 1 < numberOfParts lam →
      lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    (¬ ∃ mu : List Nat, IsFranklinMovePair lam mu) ↔
      lam.getD (numberOfParts lam - 1) 0 < numberOfParts lam - 1 ∨
        IsPentagonalFixedShape lam := by
  constructor
  · intro hno
    rcases IsFranklinMovePair_successive_lastPart_cases_of_strict
        hstrict hne hsucc with hlow | hup | hfixed | hdown
    · exact Or.inl hlow.1
    · exact False.elim (hno ⟨franklinUpMove lam, hup.2⟩)
    · exact Or.inr hfixed.1
    · exact False.elim (hno ⟨franklinDownMove lam, hdown.2⟩)
  · intro hcase
    rcases hcase with hlow | hfixed
    · rw [not_exists_IsFranklinMovePair_iff_not_lastPart_boundary_of_strict hstrict hne]
      constructor <;> omega
    · exact not_exists_IsFranklinMovePair_of_IsPentagonalFixedShape_left hfixed

/-- Complementary domain form under consecutive row differences: a
relation-form Franklin edge exists exactly when the source is neither low
residual nor a pentagonal fixed shape. -/
theorem exists_IsFranklinMovePair_iff_not_low_not_fixed_of_successive_of_strict
    {lam : List Nat} (hstrict : IsStrictPartition lam) (hne : lam ≠ [])
    (hsucc : ∀ r, r + 1 < numberOfParts lam →
      lam.getD (r + 1) 0 + 1 = lam.getD r 0) :
    (∃ mu : List Nat, IsFranklinMovePair lam mu) ↔
      ¬ lam.getD (numberOfParts lam - 1) 0 < numberOfParts lam - 1 ∧
        ¬ IsPentagonalFixedShape lam := by
  constructor
  · rintro ⟨mu, hpair⟩
    constructor
    · intro hlow
      have hno :=
        (not_exists_IsFranklinMovePair_iff_low_or_fixed_of_successive_of_strict
          hstrict hne hsucc).2 (Or.inl hlow)
      exact hno ⟨mu, hpair⟩
    · intro hfixed
      exact not_IsFranklinMovePair_of_IsPentagonalFixedShape_left hfixed hpair
  · rintro ⟨hnotLow, hnotFixed⟩
    rcases IsFranklinMovePair_successive_lastPart_cases_of_strict
        hstrict hne hsucc with hlow | hup | hfixed | hdown
    · exact False.elim (hnotLow hlow.1)
    · exact ⟨franklinUpMove lam, hup.2⟩
    · exact False.elim (hnotFixed hfixed.1)
    · exact ⟨franklinDownMove lam, hdown.2⟩

/-- Active-domain uniqueness under consecutive row differences: once a strict
nonempty source is neither low residual nor pentagonal fixed, it has a unique
relation-form Franklin target. -/
theorem exists_unique_IsFranklinMovePair_of_not_low_not_fixed_of_successive_of_strict
    {lam : List Nat} (hstrict : IsStrictPartition lam) (hne : lam ≠ [])
    (hsucc : ∀ r, r + 1 < numberOfParts lam →
      lam.getD (r + 1) 0 + 1 = lam.getD r 0)
    (hnotLow : ¬ lam.getD (numberOfParts lam - 1) 0 < numberOfParts lam - 1)
    (hnotFixed : ¬ IsPentagonalFixedShape lam) :
    ∃! mu : List Nat, IsFranklinMovePair lam mu := by
  have hexists :
      ∃ mu : List Nat, IsFranklinMovePair lam mu :=
    (exists_IsFranklinMovePair_iff_not_low_not_fixed_of_successive_of_strict
      hstrict hne hsucc).2 ⟨hnotLow, hnotFixed⟩
  rcases hexists with ⟨mu, hmu⟩
  refine ⟨mu, hmu, ?_⟩
  intro nu hnu
  exact (IsFranklinMovePair.eq_of_left hmu hnu).symm

/-- Active-domain package under consecutive row differences: the unique target
exists and immediately satisfies the usual Franklin involution properties. -/
theorem exists_IsFranklinMovePair_involution_package_of_not_low_not_fixed_of_successive_of_strict
    {lam : List Nat} (hstrict : IsStrictPartition lam) (hne : lam ≠ [])
    (hsucc : ∀ r, r + 1 < numberOfParts lam →
      lam.getD (r + 1) 0 + 1 = lam.getD r 0)
    (hnotLow : ¬ lam.getD (numberOfParts lam - 1) 0 < numberOfParts lam - 1)
    (hnotFixed : ¬ IsPentagonalFixedShape lam) :
    ∃ mu : List Nat,
      IsFranklinMovePair lam mu ∧
        IsStrictPartition mu ∧
        IsFranklinMovePair mu lam ∧
        partitionWeight mu = partitionWeight lam ∧
        partSign mu = - partSign lam ∧
        mu ≠ lam := by
  have hexists :
      ∃ mu : List Nat, IsFranklinMovePair lam mu :=
    (exists_IsFranklinMovePair_iff_not_low_not_fixed_of_successive_of_strict
      hstrict hne hsucc).2 ⟨hnotLow, hnotFixed⟩
  rcases hexists with ⟨mu, hpair⟩
  have hpack := IsFranklinMovePair.involution_package hstrict hpair
  exact ⟨mu, hpair, hpack.1, hpack.2.1, hpack.2.2.1, hpack.2.2.2.1,
    hpack.2.2.2.2⟩

/-- Exact target case split in the consecutive-difference active domain. This
is the branch-level form needed before turning the relation into an explicit
Franklin map. -/
theorem IsFranklinMovePair_active_target_cases_of_not_low_not_fixed_of_successive_of_strict
    {lam mu : List Nat} (hstrict : IsStrictPartition lam) (hne : lam ≠ [])
    (hsucc : ∀ r, r + 1 < numberOfParts lam →
      lam.getD (r + 1) 0 + 1 = lam.getD r 0)
    (hnotLow : ¬ lam.getD (numberOfParts lam - 1) 0 < numberOfParts lam - 1)
    (hnotFixed : ¬ IsPentagonalFixedShape lam)
    (hpair : IsFranklinMovePair lam mu) :
    (lam.getD (numberOfParts lam - 1) 0 = numberOfParts lam - 1 ∧
        mu = franklinUpMove lam) ∨
      (numberOfParts lam + 1 < lam.getD (numberOfParts lam - 1) 0 ∧
        mu = franklinDownMove lam) := by
  rcases IsFranklinMovePair_successive_lastPart_cases_of_strict
      hstrict hne hsucc with hlow | hup | hfixed | hdown
  · exact False.elim (hnotLow hlow.1)
  · exact Or.inl ⟨hup.1, IsFranklinMovePair.eq_of_left hpair hup.2⟩
  · exact False.elim (hnotFixed hfixed.1)
  · exact Or.inr ⟨hdown.1, IsFranklinMovePair.eq_of_left hpair hdown.2⟩

/-- A strict Franklin move cannot land in a pentagonal fixed shape. -/
theorem not_IsPentagonalFixedShape_right_of_IsFranklinMovePair
    {lam mu : List Nat} (hstrict : IsStrictPartition lam)
    (hpair : IsFranklinMovePair lam mu) :
    ¬ IsPentagonalFixedShape mu := by
  intro hfixed
  exact not_IsFranklinMovePair_of_IsPentagonalFixedShape_left hfixed
    (IsFranklinMovePair.symm_of_strict hstrict hpair)

/-- Both pentagonal fixed shapes have sign parity determined by `k`. -/
theorem partParity_lowerPentagonalPartition (k : Nat) :
    partParity (lowerPentagonalPartition k) = k % 2 := by
  unfold partParity
  rw [numberOfParts_lowerPentagonalPartition]

/-- Both pentagonal fixed shapes have sign parity determined by `k`. -/
theorem partParity_upperPentagonalPartition (k : Nat) :
    partParity (upperPentagonalPartition k) = k % 2 := by
  unfold partParity
  rw [numberOfParts_upperPentagonalPartition]

/-- The lower pentagonal fixed shape has the sign prescribed by its height. -/
theorem partSign_lowerPentagonalPartition (k : Nat) :
    partSign (lowerPentagonalPartition k) = if k % 2 = 0 then 1 else -1 := by
  simp [partSign, partParity_lowerPentagonalPartition]

/-- The upper pentagonal fixed shape has the sign prescribed by its height. -/
theorem partSign_upperPentagonalPartition (k : Nat) :
    partSign (upperPentagonalPartition k) = if k % 2 = 0 then 1 else -1 := by
  simp [partSign, partParity_upperPentagonalPartition]

/-- The two pentagonal fixed shapes of the same height contribute with the
same Franklin sign. -/
theorem partSign_lowerPentagonalPartition_eq_upper (k : Nat) :
    partSign (lowerPentagonalPartition k) = partSign (upperPentagonalPartition k) := by
  simp [partSign, partParity_lowerPentagonalPartition, partParity_upperPentagonalPartition]

theorem two_mul_upperPentagonalNumber (k : Nat) :
    2 * upperPentagonalNumber k = k * (3 * k + 1) := by
  rw [upperPentagonalNumber, Nat.mul_add, two_mul_triangular]
  nlinarith

theorem IsStrictPartition_lowerPentagonalPartition (k : Nat) :
    IsStrictPartition (lowerPentagonalPartition k) := by
  exact IsStrictPartition_shiftedStaircasePartition (k - 1) k

theorem IsStrictPartition_upperPentagonalPartition (k : Nat) :
    IsStrictPartition (upperPentagonalPartition k) := by
  exact IsStrictPartition_shiftedStaircasePartition k k

theorem IsStrictPartition_of_IsPentagonalFixedShape {lam : List Nat}
    (hfixed : IsPentagonalFixedShape lam) :
    IsStrictPartition lam := by
  rcases hfixed with ⟨k, _hk, hlow | hup⟩
  · rw [hlow]
    exact IsStrictPartition_lowerPentagonalPartition k
  · rw [hup]
    exact IsStrictPartition_upperPentagonalPartition k

theorem numberOfParts_pos_of_IsPentagonalFixedShape {lam : List Nat}
    (hfixed : IsPentagonalFixedShape lam) :
    0 < numberOfParts lam := by
  rcases hfixed with ⟨k, hk, hlow | hup⟩
  · rw [hlow, numberOfParts_lowerPentagonalPartition]
    exact hk
  · rw [hup, numberOfParts_upperPentagonalPartition]
    exact hk

theorem lastPart_eq_numberOfParts_or_add_one_of_IsPentagonalFixedShape {lam : List Nat}
    (hfixed : IsPentagonalFixedShape lam) :
    lam.getD (numberOfParts lam - 1) 0 = numberOfParts lam ∨
      lam.getD (numberOfParts lam - 1) 0 = numberOfParts lam + 1 := by
  rcases hfixed with ⟨k, hk, hlow | hup⟩
  · left
    rw [hlow]
    exact lowerPentagonalPartition_lastPart_eq_numberOfParts k hk
  · right
    rw [hup]
    exact upperPentagonalPartition_lastPart_eq_numberOfParts_add_one k hk

theorem successive_getD_of_IsPentagonalFixedShape {lam : List Nat}
    (hfixed : IsPentagonalFixedShape lam) :
    ∀ r, r + 1 < numberOfParts lam →
      lam.getD (r + 1) 0 + 1 = lam.getD r 0 := by
  rcases hfixed with ⟨k, _hk, hlow | hup⟩
  · intro r hr
    have hrk : r + 1 < k := by
      simpa [hlow, numberOfParts_lowerPentagonalPartition] using hr
    rw [hlow]
    exact lowerPentagonalPartition_successive_getD k r hrk
  · intro r hr
    have hrk : r + 1 < k := by
      simpa [hup, numberOfParts_upperPentagonalPartition] using hr
    rw [hup]
    exact upperPentagonalPartition_successive_getD k r hrk

theorem IsPentagonalFixedShape_iff_lastPart_boundary_and_successive
    {lam : List Nat} (hlen : 0 < numberOfParts lam) :
    IsPentagonalFixedShape lam ↔
      (lam.getD (numberOfParts lam - 1) 0 = numberOfParts lam ∨
          lam.getD (numberOfParts lam - 1) 0 = numberOfParts lam + 1) ∧
        ∀ r, r + 1 < numberOfParts lam →
          lam.getD (r + 1) 0 + 1 = lam.getD r 0 := by
  constructor
  · intro hfixed
    exact ⟨lastPart_eq_numberOfParts_or_add_one_of_IsPentagonalFixedShape hfixed,
      successive_getD_of_IsPentagonalFixedShape hfixed⟩
  · rintro ⟨hlast, hsucc⟩
    exact IsPentagonalFixedShape_of_lastPart_eq_numberOfParts_or_add_one
      hlen hlast hsucc

theorem IsPentagonalFixedShape_shiftedStaircasePartition_iff
    {d k : Nat} (hk : 0 < k) :
    IsPentagonalFixedShape (shiftedStaircasePartition d k) ↔
      d = k - 1 ∨ d = k := by
  constructor
  · intro hfixed
    have hlast :=
      lastPart_eq_numberOfParts_or_add_one_of_IsPentagonalFixedShape hfixed
    rw [numberOfParts_shiftedStaircasePartition,
      shiftedStaircasePartition_lastPart d k hk] at hlast
    omega
  · intro hd
    rcases hd with hd | hd
    · subst d
      simpa [lowerPentagonalPartition] using IsPentagonalFixedShape_lower k hk
    · subst d
      simpa [upperPentagonalPartition] using IsPentagonalFixedShape_upper k hk

/-- Negated form of the shifted-staircase fixed-shape classification. -/
theorem not_IsPentagonalFixedShape_shiftedStaircasePartition_iff
    {d k : Nat} (hk : 0 < k) :
    ¬ IsPentagonalFixedShape (shiftedStaircasePartition d k) ↔
      d ≠ k - 1 ∧ d ≠ k := by
  rw [IsPentagonalFixedShape_shiftedStaircasePartition_iff hk]
  constructor
  · intro h
    exact ⟨fun hd => h (Or.inl hd), fun hd => h (Or.inr hd)⟩
  · rintro ⟨hlow, hup⟩ h
    exact h.elim hlow hup

theorem shiftedStaircasePartition_eq_append_numberOfParts_iff
    {d k : Nat} (hk : 0 < k) :
    (∃ mu : List Nat,
      shiftedStaircasePartition d k = mu ++ [numberOfParts mu]) ↔
      d + 2 = k := by
  constructor
  · rintro ⟨mu, hmu⟩
    have hshape := append_numberOfParts_lastPart mu
    rw [← hmu] at hshape
    rw [numberOfParts_shiftedStaircasePartition,
      shiftedStaircasePartition_lastPart d k hk] at hshape
    omega
  · intro hd
    refine ⟨shiftedStaircasePartition (d + 1) (k - 1), ?_⟩
    have hkdecomp : k = (k - 1) + 1 := by omega
    rw [hkdecomp, shiftedStaircasePartition_succ_append,
      numberOfParts_shiftedStaircasePartition]
    congr
    omega

/-- Predicate form: a positive-height shifted staircase is in the up-branch
input region exactly in the low-offset boundary case `d + 2 = k`. -/
theorem IsFranklinUpBranchInput_shiftedStaircasePartition_iff
    {d k : Nat} (hk : 0 < k) :
    IsFranklinUpBranchInput (shiftedStaircasePartition d k) ↔
      d + 2 = k := by
  constructor
  · rintro ⟨mu, _hmu, hshape⟩
    exact (shiftedStaircasePartition_eq_append_numberOfParts_iff hk).1 ⟨mu, hshape⟩
  · intro hd
    refine ⟨shiftedStaircasePartition (d + 1) (k - 1),
      IsStrictPartition_shiftedStaircasePartition (d + 1) (k - 1), ?_⟩
    have hkdecomp : k = (k - 1) + 1 := by omega
    rw [hkdecomp, shiftedStaircasePartition_succ_append,
      numberOfParts_shiftedStaircasePartition]
    congr
    omega

/-- Predicate form: a positive-height shifted staircase is in the down-branch
input region exactly when its offset is larger than the height. -/
theorem IsFranklinDownBranchInput_shiftedStaircasePartition_iff
    {d k : Nat} (hk : 0 < k) :
    IsFranklinDownBranchInput (shiftedStaircasePartition d k) ↔ k < d := by
  constructor
  · intro hdown
    exact (franklinDownMove_hgt_shiftedStaircasePartition_iff hk).1 hdown.2
  · intro hkd
    exact ⟨by simpa [numberOfParts_shiftedStaircasePartition] using hk,
      (franklinDownMove_hgt_shiftedStaircasePartition_iff hk).2 hkd⟩

/-- A positive-height shifted staircase admits a relation-form Franklin move
exactly in the up-boundary or down-boundary offset regions. -/
theorem exists_IsFranklinMovePair_shiftedStaircasePartition_iff
    {d k : Nat} (hk : 0 < k) :
    (∃ mu : List Nat, IsFranklinMovePair (shiftedStaircasePartition d k) mu) ↔
      d + 2 = k ∨ k < d := by
  rw [exists_IsFranklinMovePair_iff,
    IsFranklinDownBranchInput_shiftedStaircasePartition_iff hk,
    IsFranklinUpBranchInput_shiftedStaircasePartition_iff hk]
  constructor
  · intro h
    rcases h with hdown | hup
    · exact Or.inr hdown
    · exact Or.inl hup
  · intro h
    rcases h with hup | hdown
    · exact Or.inr hup
    · exact Or.inl hdown

/-- A positive-height shifted staircase admits no relation-form Franklin move
exactly when it is pentagonal-fixed or in the low residual offset region. -/
theorem not_exists_IsFranklinMovePair_shiftedStaircasePartition_iff
    {d k : Nat} (hk : 0 < k) :
    (¬ ∃ mu : List Nat, IsFranklinMovePair (shiftedStaircasePartition d k) mu) ↔
      IsPentagonalFixedShape (shiftedStaircasePartition d k) ∨ d + 2 < k := by
  rw [exists_IsFranklinMovePair_shiftedStaircasePartition_iff hk]
  constructor
  · intro hno
    by_cases hlow : d + 2 < k
    · exact Or.inr hlow
    · left
      rw [IsPentagonalFixedShape_shiftedStaircasePartition_iff hk]
      have hnotUp : d + 2 ≠ k := fun hup => hno (Or.inl hup)
      have hnotDown : ¬ k < d := fun hdown => hno (Or.inr hdown)
      omega
  · intro hnod hmove
    rcases hnod with hfixed | hlow
    · rw [IsPentagonalFixedShape_shiftedStaircasePartition_iff hk] at hfixed
      rcases hmove with hup | hdown <;> omega
    · rcases hmove with hup | hdown <;> omega

/-- Exact target classification for relation-form Franklin moves from a
positive-height shifted staircase. -/
theorem IsFranklinMovePair_shiftedStaircasePartition_iff
    {d k : Nat} (hk : 0 < k) {mu : List Nat} :
    IsFranklinMovePair (shiftedStaircasePartition d k) mu ↔
      (d + 2 = k ∧ mu = franklinUpMove (shiftedStaircasePartition d k)) ∨
        (k < d ∧ mu = franklinDownMove (shiftedStaircasePartition d k)) := by
  constructor
  · intro hpair
    rcases hpair with ⟨hdown, hmu⟩ | ⟨hup, hmu⟩
    · exact Or.inr
        ⟨(IsFranklinDownBranchInput_shiftedStaircasePartition_iff hk).1 hdown, hmu⟩
    · exact Or.inl
        ⟨(IsFranklinUpBranchInput_shiftedStaircasePartition_iff hk).1 hup, hmu⟩
  · rintro (⟨hup, rfl⟩ | ⟨hdown, rfl⟩)
    · exact Or.inr
        ⟨(IsFranklinUpBranchInput_shiftedStaircasePartition_iff hk).2 hup, rfl⟩
    · exact Or.inl
        ⟨(IsFranklinDownBranchInput_shiftedStaircasePartition_iff hk).2 hdown, rfl⟩

/-- Last-part form of the low residual shifted-staircase region. -/
theorem shiftedStaircasePartition_lastPart_low_residual_iff
    {d k : Nat} (hk : 0 < k) :
    (shiftedStaircasePartition d k).getD
        (numberOfParts (shiftedStaircasePartition d k) - 1) 0 <
      numberOfParts (shiftedStaircasePartition d k) - 1 ↔
      d + 2 < k := by
  rw [numberOfParts_shiftedStaircasePartition,
    shiftedStaircasePartition_lastPart d k hk]
  omega

/-- Last-part form of the shifted-staircase up-input boundary. -/
theorem shiftedStaircasePartition_lastPart_up_boundary_iff
    {d k : Nat} (hk : 0 < k) :
    (shiftedStaircasePartition d k).getD
        (numberOfParts (shiftedStaircasePartition d k) - 1) 0 =
      numberOfParts (shiftedStaircasePartition d k) - 1 ↔
      IsFranklinUpBranchInput (shiftedStaircasePartition d k) := by
  rw [IsFranklinUpBranchInput_shiftedStaircasePartition_iff hk,
    numberOfParts_shiftedStaircasePartition,
    shiftedStaircasePartition_lastPart d k hk]
  omega

/-- Last-part form of the shifted-staircase pentagonal fixed shapes. -/
theorem shiftedStaircasePartition_lastPart_fixed_boundary_iff
    {d k : Nat} (hk : 0 < k) :
    ((shiftedStaircasePartition d k).getD
          (numberOfParts (shiftedStaircasePartition d k) - 1) 0 =
        numberOfParts (shiftedStaircasePartition d k) ∨
      (shiftedStaircasePartition d k).getD
          (numberOfParts (shiftedStaircasePartition d k) - 1) 0 =
        numberOfParts (shiftedStaircasePartition d k) + 1) ↔
      IsPentagonalFixedShape (shiftedStaircasePartition d k) := by
  rw [IsPentagonalFixedShape_shiftedStaircasePartition_iff hk,
    numberOfParts_shiftedStaircasePartition,
    shiftedStaircasePartition_lastPart d k hk]
  omega

/-- Last-part form of the shifted-staircase down-input boundary. -/
theorem shiftedStaircasePartition_lastPart_down_boundary_iff
    {d k : Nat} (hk : 0 < k) :
    numberOfParts (shiftedStaircasePartition d k) + 1 <
        (shiftedStaircasePartition d k).getD
          (numberOfParts (shiftedStaircasePartition d k) - 1) 0 ↔
      IsFranklinDownBranchInput (shiftedStaircasePartition d k) := by
  rw [IsFranklinDownBranchInput_shiftedStaircasePartition_iff hk,
    numberOfParts_shiftedStaircasePartition,
    shiftedStaircasePartition_lastPart d k hk]
  omega

/-- On the shifted-staircase up boundary, the explicit up move lands in the
down-branch input region. -/
theorem IsFranklinDownBranchInput_franklinUpMove_shiftedStaircasePartition
    {d k : Nat} (hk : 0 < k) (hup : d + 2 = k) :
    IsFranklinDownBranchInput
      (franklinUpMove (shiftedStaircasePartition d k)) := by
  rw [franklinUpMove_shiftedStaircasePartition_of_pos_height hk]
  apply (IsFranklinDownBranchInput_shiftedStaircasePartition_iff (d := d + 2)
    (k := k - 1) (by omega)).2
  omega

/-- On the shifted-staircase down boundary, the explicit down move lands in
the up-branch input region. -/
theorem IsFranklinUpBranchInput_franklinDownMove_shiftedStaircasePartition
    {d k : Nat} (hk : 0 < k) (hdown : k < d) :
    IsFranklinUpBranchInput
      (franklinDownMove (shiftedStaircasePartition d k)) := by
  have hd : 0 < d := by omega
  rw [franklinDownMove_shiftedStaircasePartition_of_pos_offset hd]
  refine ⟨shiftedStaircasePartition (d - 1) k,
    IsStrictPartition_shiftedStaircasePartition (d - 1) k, ?_⟩
  rw [numberOfParts_shiftedStaircasePartition]

/-- On the shifted-staircase up boundary, the down move inverts the explicit
up move. -/
theorem franklinDownMove_franklinUpMove_shiftedStaircasePartition
    {d k : Nat} (hk : 0 < k) (hup : d + 2 = k) :
    franklinDownMove (franklinUpMove (shiftedStaircasePartition d k)) =
      shiftedStaircasePartition d k := by
  have hupInput :
      IsFranklinUpBranchInput (shiftedStaircasePartition d k) :=
    (IsFranklinUpBranchInput_shiftedStaircasePartition_iff hk).2 hup
  exact (franklinUpMove_branch_transition_and_inverse
    (IsStrictPartition_shiftedStaircasePartition d k) hupInput).2

/-- On the shifted-staircase down boundary, the up move inverts the explicit
down move. -/
theorem franklinUpMove_franklinDownMove_shiftedStaircasePartition
    {d k : Nat} (hk : 0 < k) (hdown : k < d) :
    franklinUpMove (franklinDownMove (shiftedStaircasePartition d k)) =
      shiftedStaircasePartition d k := by
  have hdownInput :
      IsFranklinDownBranchInput (shiftedStaircasePartition d k) :=
    (IsFranklinDownBranchInput_shiftedStaircasePartition_iff hk).2 hdown
  exact (franklinDownMove_branch_transition_and_inverse
    (IsStrictPartition_shiftedStaircasePartition d k) hdownInput).2

/-- On the shifted-staircase up boundary, the up move preserves weight,
reverses sign, and stays strict. -/
theorem franklinUpMove_shiftedStaircasePartition_strict_weight_sign
    {d k : Nat} (hk : 0 < k) (hup : d + 2 = k) :
    IsStrictPartition (franklinUpMove (shiftedStaircasePartition d k)) ∧
      partitionWeight (franklinUpMove (shiftedStaircasePartition d k)) =
        partitionWeight (shiftedStaircasePartition d k) ∧
      partSign (franklinUpMove (shiftedStaircasePartition d k)) =
        - partSign (shiftedStaircasePartition d k) := by
  exact franklinUpMove_strict_weight_sign_of_branch_input
    ((IsFranklinUpBranchInput_shiftedStaircasePartition_iff hk).2 hup)

/-- On the shifted-staircase down boundary, the down move preserves weight,
reverses sign, and stays strict. -/
theorem franklinDownMove_shiftedStaircasePartition_strict_weight_sign
    {d k : Nat} (hk : 0 < k) (hdown : k < d) :
    IsStrictPartition (franklinDownMove (shiftedStaircasePartition d k)) ∧
      partitionWeight (franklinDownMove (shiftedStaircasePartition d k)) =
        partitionWeight (shiftedStaircasePartition d k) ∧
      partSign (franklinDownMove (shiftedStaircasePartition d k)) =
        - partSign (shiftedStaircasePartition d k) := by
  exact franklinDownMove_strict_weight_sign_of_branch_input
    (IsStrictPartition_shiftedStaircasePartition d k)
    ((IsFranklinDownBranchInput_shiftedStaircasePartition_iff hk).2 hdown)

/-- Full shifted-staircase package for the up boundary: strictness, weight,
sign reversal, transition to the down-input region, and inverse. -/
theorem franklinUpMove_shiftedStaircasePartition_branch_package
    {d k : Nat} (hk : 0 < k) (hup : d + 2 = k) :
    IsStrictPartition (franklinUpMove (shiftedStaircasePartition d k)) ∧
      partitionWeight (franklinUpMove (shiftedStaircasePartition d k)) =
        partitionWeight (shiftedStaircasePartition d k) ∧
      partSign (franklinUpMove (shiftedStaircasePartition d k)) =
        - partSign (shiftedStaircasePartition d k) ∧
      IsFranklinDownBranchInput
        (franklinUpMove (shiftedStaircasePartition d k)) ∧
      franklinDownMove (franklinUpMove (shiftedStaircasePartition d k)) =
        shiftedStaircasePartition d k := by
  have hpack := franklinUpMove_shiftedStaircasePartition_strict_weight_sign hk hup
  exact ⟨hpack.1, hpack.2.1, hpack.2.2,
    IsFranklinDownBranchInput_franklinUpMove_shiftedStaircasePartition hk hup,
    franklinDownMove_franklinUpMove_shiftedStaircasePartition hk hup⟩

/-- Full shifted-staircase package for the down boundary: strictness, weight,
sign reversal, transition to the up-input region, and inverse. -/
theorem franklinDownMove_shiftedStaircasePartition_branch_package
    {d k : Nat} (hk : 0 < k) (hdown : k < d) :
    IsStrictPartition (franklinDownMove (shiftedStaircasePartition d k)) ∧
      partitionWeight (franklinDownMove (shiftedStaircasePartition d k)) =
        partitionWeight (shiftedStaircasePartition d k) ∧
      partSign (franklinDownMove (shiftedStaircasePartition d k)) =
        - partSign (shiftedStaircasePartition d k) ∧
      IsFranklinUpBranchInput
        (franklinDownMove (shiftedStaircasePartition d k)) ∧
      franklinUpMove (franklinDownMove (shiftedStaircasePartition d k)) =
        shiftedStaircasePartition d k := by
  have hpack := franklinDownMove_shiftedStaircasePartition_strict_weight_sign hk hdown
  exact ⟨hpack.1, hpack.2.1, hpack.2.2,
    IsFranklinUpBranchInput_franklinDownMove_shiftedStaircasePartition hk hdown,
    franklinUpMove_franklinDownMove_shiftedStaircasePartition hk hdown⟩

/-- A shifted staircase whose offset is too small is in none of the three
boundary cases isolated so far: it is not pentagonal-fixed, not an explicit
up-branch input, and not in the down-branch inequality. -/
theorem shiftedStaircasePartition_low_offset_no_boundary
    {d k : Nat} (hk : 0 < k) (hdk : d + 2 < k) :
    ¬ IsPentagonalFixedShape (shiftedStaircasePartition d k) ∧
      ¬ (∃ mu : List Nat,
        shiftedStaircasePartition d k = mu ++ [numberOfParts mu]) ∧
      ¬ (∀ n, n ∈ shiftedStaircasePartition d k →
        numberOfParts (shiftedStaircasePartition d k) + 1 < n) := by
  constructor
  · rw [not_IsPentagonalFixedShape_shiftedStaircasePartition_iff hk]
    constructor <;> omega
  · constructor
    · rw [shiftedStaircasePartition_eq_append_numberOfParts_iff hk]
      omega
    · rw [not_franklinDownMove_hgt_shiftedStaircasePartition_iff hk]
      omega

/-- Predicate version of the low-offset residual case: a positive-height
shifted staircase with `d + 2 < k` is neither fixed nor in either Franklin
branch-input region. -/
theorem shiftedStaircasePartition_low_offset_no_branch_inputs
    {d k : Nat} (hk : 0 < k) (hdk : d + 2 < k) :
    ¬ IsPentagonalFixedShape (shiftedStaircasePartition d k) ∧
      ¬ IsFranklinUpBranchInput (shiftedStaircasePartition d k) ∧
      ¬ IsFranklinDownBranchInput (shiftedStaircasePartition d k) := by
  constructor
  · rw [not_IsPentagonalFixedShape_shiftedStaircasePartition_iff hk]
    constructor <;> omega
  · constructor
    · rw [IsFranklinUpBranchInput_shiftedStaircasePartition_iff hk]
      omega
    · rw [IsFranklinDownBranchInput_shiftedStaircasePartition_iff hk]
      omega

/-- The residual shifted-staircase region is exactly the low-offset region:
outside the fixed shapes and both Franklin branch-input predicates iff
`d + 2 < k`. -/
theorem shiftedStaircasePartition_residual_branch_inputs_iff
    {d k : Nat} (hk : 0 < k) :
    (¬ IsPentagonalFixedShape (shiftedStaircasePartition d k) ∧
        ¬ IsFranklinUpBranchInput (shiftedStaircasePartition d k) ∧
        ¬ IsFranklinDownBranchInput (shiftedStaircasePartition d k)) ↔
      d + 2 < k := by
  constructor
  · rintro ⟨hfixed, hup, hdown⟩
    rw [not_IsPentagonalFixedShape_shiftedStaircasePartition_iff hk] at hfixed
    rw [IsFranklinUpBranchInput_shiftedStaircasePartition_iff hk] at hup
    rw [IsFranklinDownBranchInput_shiftedStaircasePartition_iff hk] at hdown
    omega
  · intro hlow
    exact shiftedStaircasePartition_low_offset_no_branch_inputs hk hlow

/-- Exhaustive offset split for positive-height shifted staircases, in the
language of the current Franklin boundary infrastructure. -/
theorem shiftedStaircasePartition_offset_cases {d k : Nat} (hk : 0 < k) :
    (d + 2 < k ∧
        ¬ IsPentagonalFixedShape (shiftedStaircasePartition d k) ∧
        ¬ (∃ mu : List Nat,
          shiftedStaircasePartition d k = mu ++ [numberOfParts mu]) ∧
        ¬ (∀ n, n ∈ shiftedStaircasePartition d k →
          numberOfParts (shiftedStaircasePartition d k) + 1 < n)) ∨
      (∃ mu : List Nat,
        shiftedStaircasePartition d k = mu ++ [numberOfParts mu]) ∨
      IsPentagonalFixedShape (shiftedStaircasePartition d k) ∨
      (∀ n, n ∈ shiftedStaircasePartition d k →
        numberOfParts (shiftedStaircasePartition d k) + 1 < n) := by
  by_cases hlow : d + 2 < k
  · left
    exact ⟨hlow, shiftedStaircasePartition_low_offset_no_boundary hk hlow⟩
  · right
    by_cases hup : d + 2 = k
    · left
      exact (shiftedStaircasePartition_eq_append_numberOfParts_iff hk).2 hup
    · right
      have hgt : k < d + 2 := by omega
      by_cases hdk : d ≤ k
      · left
        rw [IsPentagonalFixedShape_shiftedStaircasePartition_iff hk]
        omega
      · right
        rw [franklinDownMove_hgt_shiftedStaircasePartition_iff hk]
        omega

/-- Predicate-form exhaustive split for positive-height shifted staircases:
low residual, up branch input, fixed pentagonal shape, or down branch input. -/
theorem shiftedStaircasePartition_branch_input_cases {d k : Nat} (hk : 0 < k) :
    (d + 2 < k ∧
        ¬ IsPentagonalFixedShape (shiftedStaircasePartition d k) ∧
        ¬ IsFranklinUpBranchInput (shiftedStaircasePartition d k) ∧
        ¬ IsFranklinDownBranchInput (shiftedStaircasePartition d k)) ∨
      IsFranklinUpBranchInput (shiftedStaircasePartition d k) ∨
      IsPentagonalFixedShape (shiftedStaircasePartition d k) ∨
      IsFranklinDownBranchInput (shiftedStaircasePartition d k) := by
  by_cases hlow : d + 2 < k
  · left
    exact ⟨hlow, shiftedStaircasePartition_low_offset_no_branch_inputs hk hlow⟩
  · right
    by_cases hup : d + 2 = k
    · left
      rw [IsFranklinUpBranchInput_shiftedStaircasePartition_iff hk]
      exact hup
    · right
      have hgt : k < d + 2 := by omega
      by_cases hdk : d ≤ k
      · left
        rw [IsPentagonalFixedShape_shiftedStaircasePartition_iff hk]
        omega
      · right
        rw [IsFranklinDownBranchInput_shiftedStaircasePartition_iff hk]
        omega

/-- Away from the low residual offset region, a positive-height shifted
staircase lies in exactly one of the three active boundary classes isolated
so far: up branch input, fixed pentagonal shape, or down branch input. -/
theorem shiftedStaircasePartition_up_or_fixed_or_down_of_not_low_offset
    {d k : Nat} (hk : 0 < k) (hlow : ¬ (d + 2 < k)) :
    IsFranklinUpBranchInput (shiftedStaircasePartition d k) ∨
      IsPentagonalFixedShape (shiftedStaircasePartition d k) ∨
      IsFranklinDownBranchInput (shiftedStaircasePartition d k) := by
  rcases shiftedStaircasePartition_branch_input_cases hk with hres | hboundary
  · exact False.elim (hlow hres.1)
  · exact hboundary

/-- Complement form of the shifted-staircase predicate classification. -/
theorem shiftedStaircasePartition_up_or_fixed_or_down_iff_not_low_offset
    {d k : Nat} (hk : 0 < k) :
    (IsFranklinUpBranchInput (shiftedStaircasePartition d k) ∨
        IsPentagonalFixedShape (shiftedStaircasePartition d k) ∨
        IsFranklinDownBranchInput (shiftedStaircasePartition d k)) ↔
      ¬ (d + 2 < k) := by
  constructor
  · intro hboundary hlow
    have hres := shiftedStaircasePartition_low_offset_no_branch_inputs hk hlow
    rcases hboundary with hup | hfixed | hdown
    · exact hres.2.1 hup
    · exact hres.1 hfixed
    · exact hres.2.2 hdown
  · exact shiftedStaircasePartition_up_or_fixed_or_down_of_not_low_offset hk

/-- A cell in the Ferrers diagram of a list-based partition. Rows and columns
are zero-indexed. -/
def FerrersCell (lam : List Nat) (r c : Nat) : Prop :=
  r < lam.length ∧ c < lam.getD r 0

/-- The empty partition has no Ferrers cells. -/
theorem FerrersCell_nil (r c : Nat) :
    FerrersCell [] r c ↔ False := by
  simp [FerrersCell]

/-- A Ferrers cell lies in an existing row. -/
theorem FerrersCell_row_bound {lam : List Nat} {r c : Nat}
    (h : FerrersCell lam r c) : r < lam.length := h.1

/-- A Ferrers cell lies before the row length. -/
theorem FerrersCell_col_bound {lam : List Nat} {r c : Nat}
    (h : FerrersCell lam r c) : c < lam.getD r 0 := h.2

/-- Row lengths of a list partition are antitone in the row index. -/
theorem IsPartition.getD_antitone {lam : List Nat} (hpart : IsPartition lam)
    {s r : Nat} (hsr : s ≤ r) (hr : r < lam.length) :
    lam.getD r 0 ≤ lam.getD s 0 := by
  have hs : s < lam.length := Nat.lt_of_le_of_lt hsr hr
  simpa [List.getD_eq_getElem?_getD, hs, hr] using
    hpart.rel_get_of_le (a := ⟨s, hs⟩) (b := ⟨r, hr⟩) hsr

/-- Ferrers columns of a partition are upward closed: if row `r` contains a
cell in column `c`, every earlier row `s ≤ r` contains that cell too. -/
theorem FerrersCell_of_le_row {lam : List Nat} (hpart : IsPartition lam)
    {s r c : Nat} (hsr : s ≤ r) (hcell : FerrersCell lam r c) :
    FerrersCell lam s c := by
  refine ⟨Nat.lt_of_le_of_lt hsr hcell.1, ?_⟩
  exact Nat.lt_of_lt_of_le hcell.2 (IsPartition.getD_antitone hpart hsr hcell.1)

/-- The finite set of column indices occupied in row `r` of a Ferrers diagram. -/
def FerrersRowCells (lam : List Nat) (r : Nat) : Finset Nat :=
  if r < lam.length then Finset.range (lam.getD r 0) else ∅

/-- Membership in the row-cell finset is exactly the Ferrers-cell predicate
with the row fixed. -/
theorem mem_FerrersRowCells_iff {lam : List Nat} {r c : Nat} :
    c ∈ FerrersRowCells lam r ↔ FerrersCell lam r c := by
  by_cases hr : r < lam.length
  · simp [FerrersRowCells, FerrersCell, hr]
  · simp [FerrersRowCells, FerrersCell, hr]

/-- The number of cells in an existing Ferrers row is its row length. -/
theorem FerrersRowCells_card_of_lt {lam : List Nat} {r : Nat}
    (hr : r < lam.length) :
    (FerrersRowCells lam r).card = lam.getD r 0 := by
  simp [FerrersRowCells, hr]

/-- A non-existing row has no Ferrers cells. -/
theorem FerrersRowCells_card_of_not_lt {lam : List Nat} {r : Nat}
    (hr : ¬ r < lam.length) :
    (FerrersRowCells lam r).card = 0 := by
  simp [FerrersRowCells, hr]

/-- The finite set of row indices occupied in column `c` of a Ferrers diagram. -/
def FerrersColumnCells (lam : List Nat) (c : Nat) : Finset Nat :=
  (Finset.range lam.length).filter (fun r => c < lam.getD r 0)

/-- Membership in the column-cell finset is exactly the Ferrers-cell predicate
with the column fixed. -/
theorem mem_FerrersColumnCells_iff {lam : List Nat} {r c : Nat} :
    r ∈ FerrersColumnCells lam c ↔ FerrersCell lam r c := by
  simp [FerrersColumnCells, FerrersCell]

/-- Membership in a Ferrers column is upward closed for a partition. -/
theorem FerrersColumnCells_mem_of_le_row {lam : List Nat} (hpart : IsPartition lam)
    {s r c : Nat} (hsr : s ≤ r) (hr : r ∈ FerrersColumnCells lam c) :
    s ∈ FerrersColumnCells lam c := by
  rw [mem_FerrersColumnCells_iff] at hr ⊢
  exact FerrersCell_of_le_row hpart hsr hr

/-- Earlier Ferrers columns contain every row that later columns contain. -/
theorem FerrersColumnCells_subset_of_le_col (lam : List Nat) {c d : Nat}
    (hcd : c ≤ d) :
    FerrersColumnCells lam d ⊆ FerrersColumnCells lam c := by
  intro r hr
  rw [mem_FerrersColumnCells_iff] at hr ⊢
  exact ⟨hr.1, Nat.lt_of_le_of_lt hcd hr.2⟩

/-- Ferrers column heights are weakly decreasing as the column index increases. -/
theorem FerrersColumnCells_card_antitone (lam : List Nat) {c d : Nat}
    (hcd : c ≤ d) :
    (FerrersColumnCells lam d).card ≤ (FerrersColumnCells lam c).card := by
  exact Finset.card_le_card (FerrersColumnCells_subset_of_le_col lam hcd)

/-- In a partition Ferrers diagram, every column is an initial segment of row
indices. Its row set is exactly `range` of its height. -/
theorem FerrersColumnCells_eq_range_card {lam : List Nat} (hpart : IsPartition lam)
    (c : Nat) :
    FerrersColumnCells lam c = Finset.range (FerrersColumnCells lam c).card := by
  ext r
  constructor
  · intro hr
    rw [Finset.mem_range]
    by_contra hnot
    have hsubset : Finset.range (r + 1) ⊆ FerrersColumnCells lam c := by
      intro s hs
      rw [Finset.mem_range] at hs
      exact FerrersColumnCells_mem_of_le_row hpart (Nat.le_of_lt_succ hs) hr
    have hle : r + 1 ≤ (FerrersColumnCells lam c).card := by
      simpa using Finset.card_le_card hsubset
    omega
  · intro hr
    rw [Finset.mem_range] at hr
    by_contra hnot
    have hsubset : FerrersColumnCells lam c ⊆ Finset.range r := by
      intro s hs
      rw [Finset.mem_range]
      by_contra hsr
      have hrs : r ≤ s := Nat.le_of_not_gt hsr
      exact hnot (FerrersColumnCells_mem_of_le_row hpart hrs hs)
    have hle : (FerrersColumnCells lam c).card ≤ r := by
      simpa using Finset.card_le_card hsubset
    omega

/-- The finite set of all cells in a Ferrers diagram. -/
def FerrersDiagramCells (lam : List Nat) : Finset (Nat × Nat) :=
  (Finset.range lam.length).biUnion
    (fun r => (FerrersRowCells lam r).image (fun c => (r, c)))

/-- Membership in the full Ferrers cell finset is exactly the cell predicate. -/
theorem mem_FerrersDiagramCells_iff {lam : List Nat} {r c : Nat} :
    (r, c) ∈ FerrersDiagramCells lam ↔ FerrersCell lam r c := by
  by_cases hr : r < lam.length
  · simp [FerrersDiagramCells, FerrersRowCells, FerrersCell, hr]
  · simp [FerrersDiagramCells, FerrersRowCells, FerrersCell, hr]

/-- Cells grouped by columns up to a bounding width `N`. This is the column
view of the same Ferrers diagram, useful for conjugation-style arguments. -/
def FerrersDiagramCellsByColumnsUpTo (lam : List Nat) (N : Nat) : Finset (Nat × Nat) :=
  (Finset.range N).biUnion
    (fun c => (FerrersColumnCells lam c).image (fun r => (r, c)))

/-- Membership in the column-grouped Ferrers diagram with an explicit column
bound. -/
theorem mem_FerrersDiagramCellsByColumnsUpTo_iff {lam : List Nat} {N r c : Nat} :
    (r, c) ∈ FerrersDiagramCellsByColumnsUpTo lam N ↔ FerrersCell lam r c ∧ c < N := by
  constructor
  · intro h
    unfold FerrersDiagramCellsByColumnsUpTo at h
    rw [Finset.mem_biUnion] at h
    rcases h with ⟨d, hdN, hd⟩
    rcases Finset.mem_image.mp hd with ⟨r', hr', hpair⟩
    have hrc : r = r' ∧ c = d := Prod.ext_iff.mp hpair.symm
    rcases hrc with ⟨rfl, rfl⟩
    rw [mem_FerrersColumnCells_iff] at hr'
    exact ⟨hr', by simpa using hdN⟩
  · rintro ⟨hcell, hcN⟩
    unfold FerrersDiagramCellsByColumnsUpTo
    rw [Finset.mem_biUnion]
    refine ⟨c, by simpa using hcN, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨r, by rwa [mem_FerrersColumnCells_iff], rfl⟩

/-- If `N` bounds all row lengths, grouping cells by columns recovers the full
Ferrers diagram. -/
theorem FerrersDiagramCellsByColumnsUpTo_eq_of_bound (lam : List Nat) (N : Nat)
    (hbound : ∀ r : Nat, r < lam.length → lam.getD r 0 ≤ N) :
    FerrersDiagramCellsByColumnsUpTo lam N = FerrersDiagramCells lam := by
  ext p
  rcases p with ⟨r, c⟩
  rw [mem_FerrersDiagramCellsByColumnsUpTo_iff, mem_FerrersDiagramCells_iff]
  constructor
  · exact fun h => h.1
  · intro hcell
    exact ⟨hcell, Nat.lt_of_lt_of_le hcell.2 (hbound r hcell.1)⟩

/-- The column-grouped Ferrers diagram has cardinality equal to the sum of
column heights. -/
theorem FerrersDiagramCellsByColumnsUpTo_card (lam : List Nat) (N : Nat) :
    (FerrersDiagramCellsByColumnsUpTo lam N).card =
      (Finset.range N).sum (fun c => (FerrersColumnCells lam c).card) := by
  unfold FerrersDiagramCellsByColumnsUpTo
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro _c _hc
    rw [Finset.card_image_of_injective]
    intro a b h
    exact congrArg Prod.fst h
  · intro c _hc d _hd hcd
    unfold Function.onFun
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨_r, _hr, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨_s, _hs, hy_eq⟩
    rw [← hxy] at hy_eq
    exact hcd (Prod.ext_iff.mp hy_eq).2.symm

/-- A bounded column-sum version of the Ferrers cell count formula. -/
theorem FerrersDiagramCells_card_eq_sum_column_cards_of_bound (lam : List Nat) (N : Nat)
    (hbound : ∀ r : Nat, r < lam.length → lam.getD r 0 ≤ N) :
    (FerrersDiagramCells lam).card =
      (Finset.range N).sum (fun c => (FerrersColumnCells lam c).card) := by
  rw [← FerrersDiagramCellsByColumnsUpTo_eq_of_bound lam N hbound]
  exact FerrersDiagramCellsByColumnsUpTo_card lam N

/-- Column heights of a Ferrers diagram, truncated at width `N`. -/
def FerrersColumnHeightsUpTo (lam : List Nat) (N : Nat) : List Nat :=
  (List.range N).map (fun c => (FerrersColumnCells lam c).card)

/-- The truncated column-height list has the requested width. -/
theorem FerrersColumnHeightsUpTo_length (lam : List Nat) (N : Nat) :
    (FerrersColumnHeightsUpTo lam N).length = N := by
  simp [FerrersColumnHeightsUpTo]

/-- Reading a displayed column height below the truncation width gives the
cardinality of that Ferrers column. -/
theorem FerrersColumnHeightsUpTo_getD_of_lt (lam : List Nat) {c N : Nat}
    (hc : c < N) :
    (FerrersColumnHeightsUpTo lam N).getD c 0 = (FerrersColumnCells lam c).card := by
  unfold FerrersColumnHeightsUpTo
  rw [List.getD_eq_getElem?_getD]
  simp [hc]

/-- Reading a displayed column height past the truncation width gives the
default value zero. -/
theorem FerrersColumnHeightsUpTo_getD_of_ge (lam : List Nat) {c N : Nat}
    (hN : N ≤ c) :
    (FerrersColumnHeightsUpTo lam N).getD c 0 = 0 := by
  unfold FerrersColumnHeightsUpTo
  rw [List.getD_eq_getElem?_getD]
  simp [Nat.not_lt.mpr hN]

/-- The truncated column-height list is a partition: column heights weakly
decrease from left to right. -/
theorem IsPartition_FerrersColumnHeightsUpTo (lam : List Nat) (N : Nat) :
    IsPartition (FerrersColumnHeightsUpTo lam N) := by
  unfold FerrersColumnHeightsUpTo IsPartition
  exact List.Pairwise.map (fun c => (FerrersColumnCells lam c).card)
    (fun _c _d hcd => FerrersColumnCells_card_antitone lam (Nat.le_of_lt hcd))
    List.pairwise_lt_range

/-- Ferrers cells of the truncated column-height partition are transposed
cells of the original Ferrers diagram, within the displayed width. -/
theorem FerrersCell_FerrersColumnHeightsUpTo_iff {lam : List Nat}
    (hpart : IsPartition lam) {N r c : Nat} :
    FerrersCell (FerrersColumnHeightsUpTo lam N) c r ↔ c < N ∧ FerrersCell lam r c := by
  rw [FerrersCell]
  constructor
  · intro h
    have hcN : c < N := by
      simpa [FerrersColumnHeightsUpTo_length] using h.1
    have hget := FerrersColumnHeightsUpTo_getD_of_lt lam hcN
    rw [hget] at h
    have hrmem : r ∈ FerrersColumnCells lam c := by
      rw [FerrersColumnCells_eq_range_card hpart c, Finset.mem_range]
      exact h.2
    rw [mem_FerrersColumnCells_iff] at hrmem
    exact ⟨hcN, hrmem⟩
  · rintro ⟨hcN, hcell⟩
    refine ⟨?_, ?_⟩
    · simpa [FerrersColumnHeightsUpTo_length] using hcN
    · have hrmem : r ∈ FerrersColumnCells lam c := by
        rwa [mem_FerrersColumnCells_iff]
      have hrcol : r < (FerrersColumnCells lam c).card := by
        rwa [FerrersColumnCells_eq_range_card hpart c, Finset.mem_range] at hrmem
      have hget := FerrersColumnHeightsUpTo_getD_of_lt lam hcN
      rw [hget]
      exact hrcol

/-- Membership in the Ferrers diagram of the truncated column-height partition
is membership in the transposed original diagram, within the displayed width. -/
theorem mem_FerrersDiagramCells_FerrersColumnHeightsUpTo_iff {lam : List Nat}
    (hpart : IsPartition lam) {N r c : Nat} :
    (c, r) ∈ FerrersDiagramCells (FerrersColumnHeightsUpTo lam N) ↔
      (r, c) ∈ FerrersDiagramCells lam ∧ c < N := by
  rw [mem_FerrersDiagramCells_iff, mem_FerrersDiagramCells_iff,
    FerrersCell_FerrersColumnHeightsUpTo_iff hpart]
  tauto

/-- If the displayed width bounds the original row lengths, the truncated
column-height partition has exactly the transposed Ferrers cells. -/
theorem FerrersCell_FerrersColumnHeightsUpTo_iff_of_bound {lam : List Nat}
    (hpart : IsPartition lam) {N r c : Nat}
    (hbound : ∀ s : Nat, s < lam.length → lam.getD s 0 ≤ N) :
    FerrersCell (FerrersColumnHeightsUpTo lam N) c r ↔ FerrersCell lam r c := by
  rw [FerrersCell_FerrersColumnHeightsUpTo_iff hpart]
  constructor
  · exact fun h => h.2
  · intro hcell
    exact ⟨Nat.lt_of_lt_of_le hcell.2 (hbound r hcell.1), hcell⟩

/-- Under a width bound, the Ferrers diagram of the column-height partition is
the transpose of the original Ferrers diagram. -/
theorem mem_FerrersDiagramCells_FerrersColumnHeightsUpTo_iff_of_bound {lam : List Nat}
    (hpart : IsPartition lam) {N r c : Nat}
    (hbound : ∀ s : Nat, s < lam.length → lam.getD s 0 ≤ N) :
    (c, r) ∈ FerrersDiagramCells (FerrersColumnHeightsUpTo lam N) ↔
      (r, c) ∈ FerrersDiagramCells lam := by
  rw [mem_FerrersDiagramCells_iff, mem_FerrersDiagramCells_iff,
    FerrersCell_FerrersColumnHeightsUpTo_iff_of_bound hpart hbound]

/-- The Ferrers conjugate partition: the list of column heights of `lam`,
displayed up to the first row length. -/
def FerrersConjugatePartition (lam : List Nat) : List Nat :=
  FerrersColumnHeightsUpTo lam (lam.getD 0 0)

/-- The conjugate partition has length equal to the first row length of the
original list. -/
theorem FerrersConjugatePartition_length (lam : List Nat) :
    (FerrersConjugatePartition lam).length = lam.getD 0 0 := by
  unfold FerrersConjugatePartition
  exact FerrersColumnHeightsUpTo_length lam (lam.getD 0 0)

/-- Reading a conjugate part below the first row length gives the corresponding
Ferrers column height. -/
theorem FerrersConjugatePartition_getD_of_lt (lam : List Nat) {c : Nat}
    (hc : c < lam.getD 0 0) :
    (FerrersConjugatePartition lam).getD c 0 = (FerrersColumnCells lam c).card := by
  unfold FerrersConjugatePartition
  exact FerrersColumnHeightsUpTo_getD_of_lt lam hc

/-- Reading a conjugate part past the first row length gives the default value
zero. -/
theorem FerrersConjugatePartition_getD_of_ge (lam : List Nat) {c : Nat}
    (hc : lam.getD 0 0 ≤ c) :
    (FerrersConjugatePartition lam).getD c 0 = 0 := by
  unfold FerrersConjugatePartition
  exact FerrersColumnHeightsUpTo_getD_of_ge lam hc

/-- If all displayed row lengths are positive, the zeroth Ferrers column
contains exactly every row. -/
theorem FerrersColumnCells_zero_eq_range_length_of_positive {lam : List Nat}
    (hpos : PositiveParts lam) :
    FerrersColumnCells lam 0 = Finset.range lam.length := by
  ext r
  rw [mem_FerrersColumnCells_iff, Finset.mem_range]
  constructor
  · intro h
    exact h.1
  · intro hr
    refine ⟨hr, ?_⟩
    have hmem : lam.getD r 0 ∈ lam := by
      rw [List.getD_eq_getElem (l := lam) (d := 0) hr]
      exact List.getElem_mem _
    exact hpos (lam.getD r 0) hmem

/-- For a positive-parts list, the first part of the conjugate is the number
of displayed rows. -/
theorem FerrersConjugatePartition_getD_zero_eq_length_of_positive {lam : List Nat}
    (hpos : PositiveParts lam) :
    (FerrersConjugatePartition lam).getD 0 0 = lam.length := by
  cases lam with
  | nil =>
      rfl
  | cons n tail =>
      have hn : 0 < n := hpos n (by simp)
      rw [FerrersConjugatePartition_getD_of_lt (lam := n :: tail) hn,
        FerrersColumnCells_zero_eq_range_length_of_positive hpos]
      simp

/-- The empty partition is self-conjugate. -/
theorem FerrersConjugatePartition_nil :
    FerrersConjugatePartition [] = [] := by
  rfl

/-- The staircase `[3,2,1]` is self-conjugate. -/
theorem FerrersConjugatePartition_three_two_one :
    FerrersConjugatePartition [3, 2, 1] = [3, 2, 1] := by
  decide

/-- The Ferrers conjugate of `[4,2]` is `[2,2,1,1]`. -/
theorem FerrersConjugatePartition_four_two :
    FerrersConjugatePartition [4, 2] = [2, 2, 1, 1] := by
  decide

/-- The Ferrers conjugate of `[2,2,1,1]` is `[4,2]`. -/
theorem FerrersConjugatePartition_two_two_one_one :
    FerrersConjugatePartition [2, 2, 1, 1] = [4, 2] := by
  decide

/-- The `c`-th column of the height-`n` staircase has exactly `n-c` cells. -/
theorem FerrersColumnCells_staircasePartition_eq_range_sub (n c : Nat) :
    FerrersColumnCells (staircasePartition n) c = Finset.range (n - c) := by
  ext r
  rw [mem_FerrersColumnCells_iff, Finset.mem_range]
  constructor
  · intro h
    rw [FerrersCell, staircasePartition_length] at h
    rw [staircasePartition_getD_of_lt h.1] at h
    omega
  · intro hr
    rw [FerrersCell, staircasePartition_length]
    have hrn : r < n := by omega
    refine ⟨hrn, ?_⟩
    rw [staircasePartition_getD_of_lt hrn]
    omega

/-- Staircase Ferrers diagrams are self-conjugate. -/
theorem FerrersConjugatePartition_staircasePartition (n : Nat) :
    FerrersConjugatePartition (staircasePartition n) = staircasePartition n := by
  apply List.ext_getElem
  · cases n with
    | zero =>
        rfl
    | succ n =>
        rw [FerrersConjugatePartition_length,
          staircasePartition_getD_of_lt (n := n + 1) (r := 0) (by omega),
          staircasePartition_length]
        omega
  · intro r hconj hstair
    have hrfirst : r < (staircasePartition n).getD 0 0 := by
      simpa [FerrersConjugatePartition_length] using hconj
    have hstair_n : r < n := by
      simpa [staircasePartition_length] using hstair
    rw [← List.getD_eq_getElem (l := FerrersConjugatePartition (staircasePartition n))
        (d := 0) hconj,
      ← List.getD_eq_getElem (l := staircasePartition n) (d := 0) hstair,
      FerrersConjugatePartition_getD_of_lt (lam := staircasePartition n) hrfirst,
      FerrersColumnCells_staircasePartition_eq_range_sub,
      staircasePartition_getD_of_lt hstair_n]
    simp

/-- In a partition, every row length is bounded by the first row length. -/
theorem IsPartition.getD_le_first {lam : List Nat} (hpart : IsPartition lam)
    {r : Nat} (hr : r < lam.length) :
    lam.getD r 0 ≤ lam.getD 0 0 := by
  exact IsPartition.getD_antitone hpart (Nat.zero_le r) hr

/-- The Ferrers conjugate list is a partition. -/
theorem IsPartition_FerrersConjugatePartition (lam : List Nat) :
    IsPartition (FerrersConjugatePartition lam) := by
  unfold FerrersConjugatePartition
  exact IsPartition_FerrersColumnHeightsUpTo lam (lam.getD 0 0)

/-- Every displayed part of the Ferrers conjugate partition is positive. -/
theorem PositiveParts_FerrersConjugatePartition (lam : List Nat) :
    PositiveParts (FerrersConjugatePartition lam) := by
  intro n hn
  unfold FerrersConjugatePartition FerrersColumnHeightsUpTo at hn
  rcases List.mem_map.mp hn with ⟨c, hcRange, rfl⟩
  rw [List.mem_range] at hcRange
  have hlen : 0 < lam.length := by
    by_contra hnot
    have hle : lam.length ≤ 0 := Nat.le_of_not_gt hnot
    have hzero : lam.length = 0 := Nat.eq_zero_of_le_zero hle
    have hget : lam.getD 0 0 = 0 := by
      cases lam <;> simp at hzero ⊢
    omega
  have hmem : 0 ∈ FerrersColumnCells lam c := by
    rw [mem_FerrersColumnCells_iff]
    exact ⟨hlen, by simpa using hcRange⟩
  exact Finset.card_pos.mpr ⟨0, hmem⟩

/-- Cells of the Ferrers conjugate partition are transposed original cells. -/
theorem FerrersCell_FerrersConjugatePartition_iff {lam : List Nat}
    (hpart : IsPartition lam) {r c : Nat} :
    FerrersCell (FerrersConjugatePartition lam) c r ↔ FerrersCell lam r c := by
  unfold FerrersConjugatePartition
  apply FerrersCell_FerrersColumnHeightsUpTo_iff_of_bound hpart
  intro s hs
  exact IsPartition.getD_le_first hpart hs

/-- The Ferrers diagram of the conjugate partition is the transpose of the
original Ferrers diagram. -/
theorem mem_FerrersDiagramCells_FerrersConjugatePartition_iff {lam : List Nat}
    (hpart : IsPartition lam) {r c : Nat} :
    (c, r) ∈ FerrersDiagramCells (FerrersConjugatePartition lam) ↔
      (r, c) ∈ FerrersDiagramCells lam := by
  unfold FerrersConjugatePartition
  apply mem_FerrersDiagramCells_FerrersColumnHeightsUpTo_iff_of_bound hpart
  intro s hs
  exact IsPartition.getD_le_first hpart hs

/-- Double Ferrers conjugation returns the original Ferrers-cell membership
relation. This avoids committing to list equality in the presence of possible
trailing zero rows. -/
theorem FerrersCell_FerrersConjugatePartition_conjugate_iff {lam : List Nat}
    (hpart : IsPartition lam) {r c : Nat} :
    FerrersCell (FerrersConjugatePartition (FerrersConjugatePartition lam)) r c ↔
      FerrersCell lam r c := by
  rw [FerrersCell_FerrersConjugatePartition_iff (IsPartition_FerrersConjugatePartition lam)]
  rw [FerrersCell_FerrersConjugatePartition_iff hpart]

/-- Double Ferrers conjugation has the same list length when the original
partition has no trailing zero rows. -/
theorem FerrersConjugatePartition_conjugate_length {lam : List Nat}
    (hpos : PositiveParts lam) :
    (FerrersConjugatePartition (FerrersConjugatePartition lam)).length = lam.length := by
  rw [FerrersConjugatePartition_length,
    FerrersConjugatePartition_getD_zero_eq_length_of_positive hpos]

/-- Double Ferrers conjugation returns the original list for partitions whose
displayed rows are all positive. -/
theorem FerrersConjugatePartition_conjugate_eq {lam : List Nat}
    (hpart : IsPartition lam) (hpos : PositiveParts lam) :
    FerrersConjugatePartition (FerrersConjugatePartition lam) = lam := by
  apply List.ext_getElem
  · exact FerrersConjugatePartition_conjugate_length hpos
  · intro r hdouble hlam
    have hrow :
        FerrersRowCells (FerrersConjugatePartition (FerrersConjugatePartition lam)) r =
          FerrersRowCells lam r := by
      ext c
      rw [mem_FerrersRowCells_iff, mem_FerrersRowCells_iff,
        FerrersCell_FerrersConjugatePartition_conjugate_iff hpart]
    have hcard := congrArg Finset.card hrow
    rw [FerrersRowCells_card_of_lt hdouble, FerrersRowCells_card_of_lt hlam] at hcard
    rw [← List.getD_eq_getElem (l := FerrersConjugatePartition
      (FerrersConjugatePartition lam)) (d := 0) hdouble,
      ← List.getD_eq_getElem (l := lam) (d := 0) hlam]
    exact hcard

/-- Double Ferrers conjugation returns the original Ferrers-diagram membership
relation. -/
theorem mem_FerrersDiagramCells_FerrersConjugatePartition_conjugate_iff
    {lam : List Nat} (hpart : IsPartition lam) {r c : Nat} :
    (r, c) ∈ FerrersDiagramCells (FerrersConjugatePartition (FerrersConjugatePartition lam)) ↔
      (r, c) ∈ FerrersDiagramCells lam := by
  rw [mem_FerrersDiagramCells_FerrersConjugatePartition_iff
    (IsPartition_FerrersConjugatePartition lam)]
  rw [mem_FerrersDiagramCells_FerrersConjugatePartition_iff hpart]

/-- The weight of the truncated column-height list is the sum of its column
heights. -/
theorem partitionWeight_FerrersColumnHeightsUpTo (lam : List Nat) (N : Nat) :
    partitionWeight (FerrersColumnHeightsUpTo lam N) =
      (Finset.range N).sum (fun c => (FerrersColumnCells lam c).card) := by
  induction N with
  | zero =>
      simp [FerrersColumnHeightsUpTo]
  | succ N ih =>
      rw [show FerrersColumnHeightsUpTo lam (N + 1) =
          FerrersColumnHeightsUpTo lam N ++ [(FerrersColumnCells lam N).card] by
        unfold FerrersColumnHeightsUpTo
        rw [List.range_succ]
        simp]
      rw [partitionWeight_append]
      simp [partitionWeight, ih, Finset.sum_range_succ]

/-- The empty Ferrers diagram has no cells. -/
theorem FerrersDiagramCells_nil :
    FerrersDiagramCells [] = ∅ := by
  simp [FerrersDiagramCells]

/-- Summing the displayed row lengths of a list partition gives its weight.
This `get?` version is convenient for induction on lists. -/
theorem partitionWeight_eq_sum_getElem_getD (lam : List Nat) :
    (Finset.range lam.length).sum (fun r => (lam[r]?).getD 0) = partitionWeight lam := by
  induction lam with
  | nil =>
      simp [partitionWeight]
  | cons a t ih =>
      rw [show (a :: t).length = t.length + 1 by rfl]
      rw [Finset.sum_range_succ']
      simp
      rw [ih]
      omega

/-- Summing the row lengths by numeric index gives the partition weight. -/
theorem partitionWeight_eq_sum_getD (lam : List Nat) :
    (Finset.range lam.length).sum (fun r => lam.getD r 0) = partitionWeight lam := by
  rw [← partitionWeight_eq_sum_getElem_getD lam]
  apply Finset.sum_congr rfl
  intro r _hr
  simp [List.getD_eq_getElem?_getD]

/-- The number of Ferrers diagram cells is the partition weight. -/
theorem FerrersDiagramCells_card (lam : List Nat) :
    (FerrersDiagramCells lam).card = partitionWeight lam := by
  rw [show (FerrersDiagramCells lam).card =
      (Finset.range lam.length).sum (fun r => (FerrersRowCells lam r).card) by
    unfold FerrersDiagramCells
    rw [Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro _r _hr
      rw [Finset.card_image_of_injective]
      intro a b h
      exact congrArg Prod.snd h
    · intro r _hr s _hs hrs
      unfold Function.onFun
      rw [Finset.disjoint_iff_ne]
      intro x hx y hy hxy
      rcases Finset.mem_image.mp hx with ⟨_cx, _hcx, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨_cy, _hcy, hy_eq⟩
      rw [← hxy] at hy_eq
      exact hrs (Prod.ext_iff.mp hy_eq).1.symm]
  rw [show (Finset.range lam.length).sum (fun r => (FerrersRowCells lam r).card) =
      (Finset.range lam.length).sum (fun r => lam.getD r 0) by
    apply Finset.sum_congr rfl
    intro r hr
    exact FerrersRowCells_card_of_lt (by simpa using hr)]
  exact partitionWeight_eq_sum_getD lam

/-- If the truncation width bounds every row, the column-height list preserves
the weight of the Ferrers diagram. -/
theorem partitionWeight_FerrersColumnHeightsUpTo_eq_of_bound (lam : List Nat) (N : Nat)
    (hbound : ∀ r : Nat, r < lam.length → lam.getD r 0 ≤ N) :
    partitionWeight (FerrersColumnHeightsUpTo lam N) = partitionWeight lam := by
  rw [partitionWeight_FerrersColumnHeightsUpTo]
  rw [← FerrersDiagramCells_card_eq_sum_column_cards_of_bound lam N hbound]
  exact FerrersDiagramCells_card lam

/-- Ferrers conjugation preserves weight for partitions. -/
theorem partitionWeight_FerrersConjugatePartition {lam : List Nat}
    (hpart : IsPartition lam) :
    partitionWeight (FerrersConjugatePartition lam) = partitionWeight lam := by
  unfold FerrersConjugatePartition
  apply partitionWeight_FerrersColumnHeightsUpTo_eq_of_bound
  intro r hr
  exact IsPartition.getD_le_first hpart hr

/-- Ferrers conjugation preserves the number of cells in the Ferrers diagram. -/
theorem FerrersDiagramCells_card_FerrersConjugatePartition {lam : List Nat}
    (hpart : IsPartition lam) :
    (FerrersDiagramCells (FerrersConjugatePartition lam)).card =
      (FerrersDiagramCells lam).card := by
  rw [FerrersDiagramCells_card, FerrersDiagramCells_card,
    partitionWeight_FerrersConjugatePartition hpart]

/-- Double Ferrers conjugation preserves partition weight. -/
theorem partitionWeight_FerrersConjugatePartition_conjugate {lam : List Nat}
    (hpart : IsPartition lam) :
    partitionWeight (FerrersConjugatePartition (FerrersConjugatePartition lam)) =
      partitionWeight lam := by
  rw [partitionWeight_FerrersConjugatePartition (IsPartition_FerrersConjugatePartition lam),
    partitionWeight_FerrersConjugatePartition hpart]

/-- Ferrers cells of a one-row partition. -/
theorem FerrersCell_singleton {n r c : Nat} :
    FerrersCell [n] r c ↔ r = 0 ∧ c < n := by
  constructor
  · intro h
    rcases h with ⟨hr, hc⟩
    cases r with
    | zero =>
        exact ⟨rfl, by simpa [FerrersCell] using hc⟩
    | succ r =>
        have : False := by
          simp at hr
        exact False.elim this
  · rintro ⟨rfl, hc⟩
    exact ⟨by simp, by simpa [FerrersCell] using hc⟩

/-- The top-left cell exists in the partition `[3, 2, 1]`. -/
theorem FerrersCell_three_two_one_zero_zero :
    FerrersCell [3, 2, 1] 0 0 := by
  exact ⟨by norm_num, by norm_num [FerrersCell]⟩

/-- The cell in row 1, column 1 exists in the partition `[3, 2, 1]`. -/
theorem FerrersCell_three_two_one_one_one :
    FerrersCell [3, 2, 1] 1 1 := by
  exact ⟨by norm_num, by norm_num [FerrersCell]⟩

/-- The rows of `[3,2,1]` have lengths `3`, `2`, and `1`. -/
theorem FerrersRowCells_three_two_one_cards :
    (FerrersRowCells [3, 2, 1] 0).card = 3 ∧
    (FerrersRowCells [3, 2, 1] 1).card = 2 ∧
    (FerrersRowCells [3, 2, 1] 2).card = 1 := by
  norm_num [FerrersRowCells]

/-- Column membership checks for the Ferrers diagram `[3,2,1]`. -/
theorem FerrersColumnCells_three_two_one_members :
    0 ∈ FerrersColumnCells [3, 2, 1] 0 ∧
    1 ∈ FerrersColumnCells [3, 2, 1] 0 ∧
    2 ∈ FerrersColumnCells [3, 2, 1] 0 ∧
    0 ∈ FerrersColumnCells [3, 2, 1] 1 ∧
    1 ∈ FerrersColumnCells [3, 2, 1] 1 ∧
    2 ∉ FerrersColumnCells [3, 2, 1] 1 ∧
    0 ∈ FerrersColumnCells [3, 2, 1] 2 ∧
    1 ∉ FerrersColumnCells [3, 2, 1] 2 := by
  norm_num [FerrersColumnCells]

/-- Concrete full-diagram membership for `[3,2,1]`. -/
theorem FerrersDiagramCells_three_two_one_members :
    (0, 0) ∈ FerrersDiagramCells [3, 2, 1] ∧
    (0, 2) ∈ FerrersDiagramCells [3, 2, 1] ∧
    (1, 1) ∈ FerrersDiagramCells [3, 2, 1] ∧
    (2, 0) ∈ FerrersDiagramCells [3, 2, 1] ∧
    (2, 1) ∉ FerrersDiagramCells [3, 2, 1] ∧
    (3, 0) ∉ FerrersDiagramCells [3, 2, 1] := by
  norm_num [FerrersDiagramCells, FerrersRowCells]

/-- Row 2 of `[3, 2, 1]` has only one cell. -/
theorem not_FerrersCell_three_two_one_two_one :
    ¬ FerrersCell [3, 2, 1] 2 1 := by
  intro h
  have hc := h.2
  norm_num [FerrersCell] at hc

/-- Vacuum has charge 0 and energy 0. -/
@[simp] theorem charge_vacuum : charge vacuum = 0 := by simp [charge, vacuum]
@[simp] theorem energy_vacuum : energy vacuum = 0 := by simp [energy, vacuum]

/-- Adding a single empty level k (i ≥ 0 occupied) gives charge +1. -/
theorem charge_add_single (k : Nat) :
    charge ⟨{k}, ∅⟩ = 1 := by
  simp [charge]

/-- Removing a single level vacates: charge -1. -/
theorem charge_remove_single (k : Nat) :
    charge ⟨∅, {k}⟩ = -1 := by
  simp [charge]

/-- Energy of single added level k = k+1. -/
theorem energy_add_single (k : Nat) :
    energy ⟨{k}, ∅⟩ = k + 1 := by
  simp [energy]

/-- Energy of single removed level k = k+1. -/
theorem energy_remove_single (k : Nat) :
    energy ⟨∅, {k}⟩ = k + 1 := by
  simp [energy]

/-- A charge-0 state with one particle added at level k and one hole at level j
has energy (k+1) + (j+1). -/
theorem energy_one_one (k j : Nat) :
    energy ⟨{k}, {j}⟩ = (k + 1) + (j + 1) := by
  simp [energy]

/-- A charge-0 state with one add and one remove has charge 0. -/
theorem charge_one_one (k j : Nat) :
    charge ⟨{k}, {j}⟩ = 0 := by
  simp [charge]

/-- Energy is always nonneg (trivially, since it's Nat). -/
theorem energy_nonneg (S : AdmissibleState) : 0 ≤ energy S := Nat.zero_le _

/-- The minimum nonzero energy for a charge-0 state is 2 (add level 0, remove level 0). -/
theorem energy_min_charge_zero :
    energy ⟨{0}, {0}⟩ = 2 := by
  simp [energy]

/-- Two-particle state: adding levels 0 and 1 gives charge 2 and energy 3. -/
theorem charge_two_particles :
    charge ⟨{0, 1}, ∅⟩ = 2 := by
  simp [charge]

theorem energy_two_particles :
    energy ⟨{0, 1}, ∅⟩ = 3 := by
  simp [energy]

/-- Charge of vacuum-like state (empty added, empty removed) = 0. -/
theorem charge_empty : charge ⟨∅, ∅⟩ = 0 := by simp [charge]

/-- Energy of vacuum-like state = 0. -/
theorem energy_empty : energy ⟨∅, ∅⟩ = 0 := by simp [energy]

/-- Charge of a state with both added and removed levels equals the difference. -/
theorem charge_pair (a r : Nat) :
    charge ⟨{a}, {r}⟩ = 0 := by
  simp [charge]

/-- Energy of a balanced pair: one added level k₁ and one removed level k₂. -/
theorem energy_pair (k₁ k₂ : Nat) :
    energy ⟨{k₁}, {k₂}⟩ = k₁ + 1 + (k₂ + 1) := by
  simp [energy]

/-- Energy of two added levels (disjoint). -/
theorem energy_add_two (a b : Nat) (hab : a ≠ b) :
    energy ⟨{a, b}, ∅⟩ = a + 1 + (b + 1) := by
  simp [energy, Finset.sum_pair hab]

/-- Charge of two added levels is 2. -/
theorem charge_add_two (a b : Nat) (hab : a ≠ b) :
    charge ⟨{a, b}, ∅⟩ = 2 := by
  simp [charge, Finset.card_pair hab]

/-- Three particles added at levels 0, 1, 2: charge = 3, energy = 6. -/
theorem charge_three_particles :
    charge ⟨{0, 1, 2}, ∅⟩ = 3 := by
  simp [charge]

theorem energy_three_particles :
    energy ⟨{0, 1, 2}, ∅⟩ = 6 := by
  simp [energy]

/-- A balanced two-pair state: add 0,1 and remove 0,1. Charge = 0, energy = 6. -/
theorem charge_balanced_two (hab : (0 : Nat) ≠ 1) :
    charge ⟨{0, 1}, {0, 1}⟩ = 0 := by
  simp [charge, Finset.card_pair hab]

theorem energy_balanced_two (hab : (0 : Nat) ≠ 1) :
    energy ⟨{0, 1}, {0, 1}⟩ = 6 := by
  simp [energy, Finset.sum_pair hab]

/-- Four particles added at levels 0, 1, 2, 3: charge = 4, energy = 10. -/
theorem charge_four_particles :
    charge ⟨{0, 1, 2, 3}, ∅⟩ = 4 := by
  simp [charge]

theorem energy_four_particles :
    energy ⟨{0, 1, 2, 3}, ∅⟩ = 10 := by
  simp [energy]

/-- Five particles added at levels 0, 1, 2, 3, 4: charge = 5, energy = 15. -/
theorem charge_five_particles :
    charge ⟨{0, 1, 2, 3, 4}, ∅⟩ = 5 := by
  simp [charge]

theorem energy_five_particles :
    energy ⟨{0, 1, 2, 3, 4}, ∅⟩ = 15 := by
  simp [energy]

/-- Six particles added at levels 0, 1, 2, 3, 4, 5: charge = 6, energy = 21. -/
theorem charge_six_particles :
    charge ⟨{0, 1, 2, 3, 4, 5}, ∅⟩ = 6 := by
  simp [charge]

theorem energy_six_particles :
    energy ⟨{0, 1, 2, 3, 4, 5}, ∅⟩ = 21 := by
  simp [energy]

end Ch04Franklin
end PartI
end QseriesFormalization
