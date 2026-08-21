import QseriesFormalization.Chapter19
import QseriesFormalization.Chapter04
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Characterisation of `jacobiTripleSign`

Two clean closed forms for `jacobiTripleSign` (defined in `Chapter19.lean`
via `List.find?` on triangular indices):

* `jacobiTripleSign_triangular`: `jacobiTripleSign (k*(k+1)/2) = (-1)^k * (2k+1)`.
* `jacobiTripleSign_of_not_triangular`: `jacobiTripleSign n = 0` when no
  `k ≤ n` satisfies `n = k*(k+1)/2`.

These will be needed by both attack routes on the cube convolution
identity (Sylvester combinatorial proof in `Pending/Sylvester_TripleSum`
and the analytic-formal Taylor bridge in `Pending/JacobiCubeAnalyticToFormal`).
Stating them in the main build (rather than inside a Pending file)
keeps the headline target portable.
-/

namespace QseriesFormalization
namespace PartIV
namespace Ch19

/-- `n * (n + 1)` is divisible by 2. -/
theorem two_dvd_mul_succ (n : ℕ) : 2 ∣ n * (n + 1) := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨m, hm⟩ := he
    exact ⟨m * (n + 1), by rw [hm]; ring⟩
  · obtain ⟨m, hm⟩ := ho
    refine ⟨n * (m + 1), ?_⟩
    rw [hm]; ring

/-- `2 * T_n = n * (n + 1)`. -/
theorem two_mul_triangular (n : ℕ) :
    2 * (n * (n + 1) / 2) = n * (n + 1) := by
  rw [Nat.mul_div_cancel' (two_dvd_mul_succ n)]

/-- Triangular numbers strictly increase on ℕ. -/
theorem triangular_strictMono :
    StrictMono (fun k : ℕ => k * (k + 1) / 2) := by
  intro a b hab
  show a * (a + 1) / 2 < b * (b + 1) / 2
  have h1 : a * (a + 1) < b * (b + 1) := by nlinarith
  have ha := two_mul_triangular a
  have hb := two_mul_triangular b
  omega

/-- `k ≤ T_k = k*(k+1)/2`. -/
theorem k_le_triangular (k : ℕ) :
    k ≤ k * (k + 1) / 2 := by
  rcases k with _ | k
  · simp
  · have h1 : 2 * (k + 1) ≤ (k + 1) * (k + 1 + 1) := by nlinarith
    have h2 := two_mul_triangular (k + 1)
    omega

/-- **Closed form (triangular case).**  `jacobiTripleSign` at the
triangular index `k*(k+1)/2` returns `(-1)^k · (2k+1)`. -/
theorem jacobiTripleSign_triangular (k : ℕ) :
    jacobiTripleSign (k * (k + 1) / 2) = (-1 : ℤ) ^ k * (2 * k + 1) := by
  set n := k * (k + 1) / 2 with hn_def
  unfold jacobiTripleSign
  have hk_le : k ≤ n := k_le_triangular k
  have hfind :
      (List.range (n + 1)).find? (fun k' => n = k' * (k' + 1) / 2) = some k := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨?_, k, ?_, ?_, ?_⟩
    · show decide (n = k * (k + 1) / 2) = true
      rw [hn_def]; simp
    · simp [List.length_range]; exact hk_le
    · rw [List.getElem_range]
    · intro j hj
      have hj_lt : j < n + 1 := by omega
      rw [List.getElem_range]
      show (!decide (n = j * (j + 1) / 2)) = true
      rw [Bool.not_eq_true', decide_eq_false_iff_not]
      intro heq
      have hjk : j * (j + 1) / 2 < k * (k + 1) / 2 := triangular_strictMono hj
      omega
  rw [hfind]

/-- **Closed form (non-triangular case).**  `jacobiTripleSign n = 0`
when no `k ≤ n` satisfies `n = k*(k+1)/2`. -/
theorem jacobiTripleSign_of_not_triangular (n : ℕ)
    (hno : ∀ k ≤ n, n ≠ k * (k + 1) / 2) :
    jacobiTripleSign n = 0 := by
  unfold jacobiTripleSign
  have hfind :
      (List.range (n + 1)).find? (fun k' => n = k' * (k' + 1) / 2) = none := by
    rw [List.find?_eq_none]
    intro k' hk'
    simp at hk'
    intro hpred
    have hk_eq : n = k' * (k' + 1) / 2 := of_decide_eq_true hpred
    exact hno k' (by omega) hk_eq
  rw [hfind]

/-- `|jacobiTripleSign n|` is bounded by `2n + 1`. -/
theorem natAbs_jacobiTripleSign_le (n : ℕ) :
    (jacobiTripleSign n).natAbs ≤ 2 * n + 1 := by
  by_cases htri : ∃ k ≤ n, n = k * (k + 1) / 2
  · obtain ⟨k, _hkle, hk_eq⟩ := htri
    rw [hk_eq, jacobiTripleSign_triangular k]
    have h_natAbs : ((-1 : ℤ) ^ k * (2 * k + 1)).natAbs = 2 * k + 1 := by
      rw [Int.natAbs_mul, Int.natAbs_pow]
      simp
      omega
    rw [h_natAbs]
    have hk_le := k_le_triangular k
    omega
  · push_neg at htri
    rw [jacobiTripleSign_of_not_triangular n htri]
    simp

/-- The complex norm of `jacobiTripleSign n` cast to `ℂ` equals its
`natAbs` as a real. -/
theorem norm_jacobiTripleSign_cast (n : ℕ) :
    ‖((jacobiTripleSign n : ℤ) : ℂ)‖ = ((jacobiTripleSign n).natAbs : ℝ) := by
  rw [Complex.norm_intCast, Nat.cast_natAbs]
  push_cast
  rfl

/-- **Summability of the `jacobiTripleSign` power series** for `‖q‖ < 1`.

The coefficient norms grow at most linearly (`|jacobiTripleSign n| ≤ 2n + 1`),
so the series `∑ jacobiTripleSign n · q^n` is absolutely summable on
the unit disc.  This is the key analytic ingredient for identifying the
formal series `jacobiThetaPS ℂ` with the analytic function
`gAnalytic q = ∑' n, (-1)^n (2n+1) q^{T_n}`. -/
theorem summable_jacobiTripleSign_mul_pow (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => ((jacobiTripleSign n : ℤ) : ℂ) * q ^ n) := by
  apply Summable.of_norm_bounded
    (g := fun n : ℕ => ((2 * n + 1 : ℕ) : ℝ) * ‖q‖ ^ n)
  · have hnorm : ‖(‖q‖ : ℝ)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hq
    have h1 : Summable (fun n : ℕ => (n : ℝ) * ‖q‖ ^ n) := by
      have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
      simpa using this
    have h2 : Summable (fun n : ℕ => ‖q‖ ^ n) :=
      summable_geometric_of_norm_lt_one hnorm
    have hsum := (h1.mul_left 2).add h2
    convert hsum using 1
    ext n
    push_cast
    ring
  · intro n
    rw [norm_mul, norm_jacobiTripleSign_cast, norm_pow]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast natAbs_jacobiTripleSign_le n)
      (pow_nonneg (norm_nonneg _) _)

/-- **The headline reindex (Taylor ↔ triangular indexing)**.

  `∑' k, jacobiTripleSign k · q^k = ∑' n, (-1)^n (2n+1) q^{n*(n+1)/2}`

valid on all of `ℂ` (Mathlib's `∑'` convention sets the value to 0 for
non-summable series, so we don't need a convergence hypothesis here).

Both forms describe the same series: the LHS is the canonical formal-PS
expansion (`jacobiThetaPS ℂ` as a Taylor series), the RHS is the
"sparse" form indexed by triangular indices (matching Ch04's analytic
`jacobiIdentity_pochhammer` RHS).

This is the analytic-bridge Step 4 in
`Pending/JacobiCubeAnalyticToFormal.lean`: the RHS Taylor extraction
step, now closed unconditionally. -/
theorem tsum_jacobiTripleSign_eq_jacobi_series (q : ℂ) :
    ∑' k : ℕ, ((jacobiTripleSign k : ℤ) : ℂ) * q ^ k =
      ∑' n : ℕ, ((-1) ^ n * (2 * (n : ℂ) + 1) * q ^ (n * (n + 1) / 2)) := by
  symm
  have h_inj : Function.Injective (fun n : ℕ => n * (n + 1) / 2) :=
    triangular_strictMono.injective
  have h_supp : Function.support
      (fun k : ℕ => ((jacobiTripleSign k : ℤ) : ℂ) * q ^ k) ⊆
      Set.range (fun n : ℕ => n * (n + 1) / 2) := by
    intro k hk
    simp only [Function.mem_support, ne_eq] at hk
    by_contra h_not_range
    apply hk
    have h_zero : jacobiTripleSign k = 0 := by
      apply jacobiTripleSign_of_not_triangular
      intro k' _hkle hk_eq
      apply h_not_range
      exact ⟨k', hk_eq.symm⟩
    rw [h_zero]; simp
  have h_reindex := h_inj.tsum_eq
    (f := fun k : ℕ => ((jacobiTripleSign k : ℤ) : ℂ) * q ^ k) h_supp
  rw [← h_reindex]
  congr 1
  ext n
  show (-1 : ℂ) ^ n * (2 * (n : ℂ) + 1) * q ^ (n * (n + 1) / 2) =
       ((jacobiTripleSign (n * (n + 1) / 2) : ℤ) : ℂ) * q ^ (n * (n + 1) / 2)
  rw [jacobiTripleSign_triangular n]
  push_cast
  ring

/-- **The cube identity at coefficient `0`** —
`((qPochInfPS ℂ)^3).coeff 0 = jacobiTripleSign 0`.

A concrete instance of the headline B2 identity, proved directly from
the polynomial-truncation bridge.  The full headline (∀ n) reduces to
generalising this argument; the structure of the proof is the same. -/
theorem coeff_zero_qPochInfPS_pow_three_eq_jacobiTripleSign :
    ((qPochInfPS ℂ)^3).coeff 0 = ((jacobiTripleSign 0 : ℤ) : ℂ) := by
  rw [coeff_qPochInfPS_pow_eq_coeff_finite_product_pow ℂ 3 0 1 Nat.zero_lt_one]
  simp [PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_pow, map_sub, map_one, jacobiTripleSign]

/-- **`((qPochInfPS ℤ)^3).coeff n` expands to the cube convolution** of
`pentagonalSign` values via the formal-multiplication rule. -/
theorem coeff_qPochInfPS_pow_three_int_eq_cubeConvolution (n : ℕ) :
    ((qPochInfPS ℤ)^3).coeff n =
      ∑ pq ∈ Finset.antidiagonal n,
        (∑ ab ∈ Finset.antidiagonal pq.1,
          (QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ab.1 : ℤ) *
          (QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ab.2 : ℤ)) *
        (QseriesFormalization.PartI.Ch04Franklin.pentagonalSign pq.2 : ℤ) := by
  rw [show (qPochInfPS ℤ) ^ 3 = qPochInfPS ℤ * qPochInfPS ℤ * qPochInfPS ℤ from by ring]
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro pq _
  rw [PowerSeries.coeff_mul]
  rw [coeff_qPochInfPS_int_eq_pentagonalSign]
  congr 1
  apply Finset.sum_congr rfl
  intro ab _
  rw [coeff_qPochInfPS_int_eq_pentagonalSign, coeff_qPochInfPS_int_eq_pentagonalSign]

/-! ### Analogous lemmas for `pentagonalSign` (parallels jacobiTripleSign).

For the analytic→formal bridge on the LHS of the cube identity, we also
need bounds and summability for `(pentagonalSign n : ℂ) * q^n`. -/

open QseriesFormalization.PartI.Ch04Franklin (pentagonalSign)

/-- `|pentagonalSign n| ≤ 1` — `pentagonalSign` is `(-1)^k` or `0`. -/
theorem natAbs_pentagonalSign_le_one (n : ℕ) :
    (pentagonalSign n).natAbs ≤ 1 := by
  unfold pentagonalSign
  split
  · simp [Int.natAbs_pow]
  · split
    · simp [Int.natAbs_pow]
    · simp

/-- Pentagonal sign is in `{-1, 0, 1}`. -/
theorem pentagonalSign_mem (n : ℕ) :
    pentagonalSign n = -1 ∨ pentagonalSign n = 0 ∨ pentagonalSign n = 1 := by
  unfold pentagonalSign
  split
  · rename_i k _
    rcases Nat.even_or_odd k with he | ho
    · right; right; exact he.neg_one_pow
    · left; exact ho.neg_one_pow
  · split
    · rename_i k _
      rcases Nat.even_or_odd k with he | ho
      · right; right; exact he.neg_one_pow
      · left; exact ho.neg_one_pow
    · right; left; rfl

/-- `‖((pentagonalSign n : ℤ) : ℂ)‖ ≤ 1`. -/
theorem norm_pentagonalSign_cast_le (n : ℕ) :
    ‖((pentagonalSign n : ℤ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  rcases pentagonalSign_mem n with h | h | h <;> rw [h] <;> simp

/-- Summability of `(pentagonalSign n : ℂ) * q^n` for `‖q‖ < 1`.

Bound: `|σ(n) · q^n| ≤ 1 · ‖q‖^n`, with geometric series summable. -/
theorem summable_pentagonalSign_mul_pow (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => ((pentagonalSign n : ℤ) : ℂ) * q^n) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => ‖q‖^n)
  · have hnorm : ‖(‖q‖ : ℝ)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hq
    exact summable_geometric_of_norm_lt_one hnorm
  · intro n
    rw [norm_mul, norm_pow]
    calc ‖((pentagonalSign n : ℤ) : ℂ)‖ * ‖q‖^n
        ≤ 1 * ‖q‖^n := by
          apply mul_le_mul_of_nonneg_right (norm_pentagonalSign_cast_le n)
          exact pow_nonneg (norm_nonneg _) _
      _ = ‖q‖^n := one_mul _

/-! ### Pentagonal index function and its injectivity.

For the analytic Euler pentagonal identity in `ℕ`-indexed form, we use
the map `j ↦ j*(3j+1)/2 : ℤ → ℕ` which sends integers to pentagonal
numbers (both `+` and `-` branches).  The map is injective.

This is the bridge from Ch04's bilateral `ℤ`-indexed analytic identity
to the `ℕ`-indexed formal-Taylor form needed for the cube argument. -/

/-- The pentagonal index function `ℤ → ℕ`: `j ↦ j*(3j+1)/2` (as Nat). -/
noncomputable def pentagonalIndex (j : ℤ) : ℕ := (j * (3 * j + 1) / 2).toNat

example : pentagonalIndex 0 = 0 := by decide
example : pentagonalIndex 1 = 2 := by decide
example : pentagonalIndex (-1) = 1 := by decide
example : pentagonalIndex 2 = 7 := by decide
example : pentagonalIndex (-2) = 5 := by decide

/-- `j * (3 * j + 1)` is non-negative for any integer `j`. -/
theorem int_j_three_j_plus_one_nonneg (j : ℤ) : 0 ≤ j * (3 * j + 1) := by
  by_cases hj : 0 ≤ j
  · have h1 : 0 ≤ 3 * j + 1 := by linarith
    exact mul_nonneg hj h1
  · push_neg at hj
    have h1 : 3 * j + 1 ≤ -2 := by linarith
    nlinarith

/-- `j * (3 * j + 1)` is divisible by 2. -/
theorem int_two_dvd_j_three_j_plus_one (j : ℤ) : (2 : ℤ) ∣ j * (3 * j + 1) := by
  rcases Int.even_or_odd j with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨m * (3 * j + 1), by rw [hm]; ring⟩
  · refine ⟨j * (3 * m + 2), ?_⟩
    rw [hm]; ring

/-- The pentagonal index function is injective on `ℤ`.

Proof: from `pentagonalIndex j1 = pentagonalIndex j2`, multiply through
to get `j1*(3*j1+1) = j2*(3*j2+1)`, factor as `(j1-j2)(3(j1+j2)+1) = 0`,
and observe `3(j1+j2)+1 = 0` has no integer solution (omega). -/
theorem pentagonalIndex_injective : Function.Injective pentagonalIndex := by
  intro j1 j2 h
  unfold pentagonalIndex at h
  have h1_nn : 0 ≤ j1 * (3 * j1 + 1) / 2 :=
    Int.ediv_nonneg (int_j_three_j_plus_one_nonneg j1) (by norm_num)
  have h2_nn : 0 ≤ j2 * (3 * j2 + 1) / 2 :=
    Int.ediv_nonneg (int_j_three_j_plus_one_nonneg j2) (by norm_num)
  have h_eq : j1 * (3 * j1 + 1) / 2 = j2 * (3 * j2 + 1) / 2 := by
    have hcast : ((j1 * (3 * j1 + 1) / 2 : ℤ).toNat : ℤ) =
        ((j2 * (3 * j2 + 1) / 2 : ℤ).toNat : ℤ) := by
      rw [h]
    rw [Int.toNat_of_nonneg h1_nn, Int.toNat_of_nonneg h2_nn] at hcast
    exact hcast
  have hd1 := int_two_dvd_j_three_j_plus_one j1
  have hd2 := int_two_dvd_j_three_j_plus_one j2
  have h_full : j1 * (3 * j1 + 1) = j2 * (3 * j2 + 1) := by
    have h2mul := congrArg (fun x => 2 * x) h_eq
    simp only at h2mul
    rw [show (2 : ℤ) * (j1 * (3 * j1 + 1) / 2) = j1 * (3 * j1 + 1) by
        rw [mul_comm, Int.ediv_mul_cancel hd1]] at h2mul
    rw [show (2 : ℤ) * (j2 * (3 * j2 + 1) / 2) = j2 * (3 * j2 + 1) by
        rw [mul_comm, Int.ediv_mul_cancel hd2]] at h2mul
    exact h2mul
  have h_factor : (j1 - j2) * (3 * (j1 + j2) + 1) = 0 := by linarith
  rcases mul_eq_zero.mp h_factor with h_diff | h_sum
  · linarith
  · omega

/-- `(pentagonalIndex j : ℤ) = j * (3*j+1) / 2` (lifting `.toNat`). -/
theorem pentagonalIndex_cast (j : ℤ) :
    (pentagonalIndex j : ℤ) = j * (3 * j + 1) / 2 := by
  unfold pentagonalIndex
  rw [Int.toNat_of_nonneg]
  exact Int.ediv_nonneg (int_j_three_j_plus_one_nonneg j) (by norm_num)

/-- For `j < 0`, the pentagonal index has the "negative" form `(-j)*(3*(-j)-1)/2`. -/
theorem pentagonalIndex_neg_form (j : ℤ) :
    (pentagonalIndex j : ℤ) = (-j) * (3 * (-j) - 1) / 2 := by
  rw [pentagonalIndex_cast]
  congr 1
  ring

/-- For `j ≥ 0`, the pentagonal index equals `j.toNat * (3 * j.toNat + 1) / 2`
as a Nat (the "+ pentagonal" form). -/
theorem pentagonalIndex_of_nonneg (j : ℤ) (hj : 0 ≤ j) :
    pentagonalIndex j = j.toNat * (3 * j.toNat + 1) / 2 := by
  unfold pentagonalIndex
  have hj_eq : j = j.toNat := (Int.toNat_of_nonneg hj).symm
  conv_lhs => rw [hj_eq]
  push_cast
  rfl

/-- For `j < 0`, the pentagonal index equals `(-j).toNat * (3 * (-j).toNat - 1) / 2`
as a Nat (the "- pentagonal" form). -/
theorem pentagonalIndex_of_neg (j : ℤ) (hj : j < 0) :
    pentagonalIndex j = (-j).toNat * (3 * (-j).toNat - 1) / 2 := by
  unfold pentagonalIndex
  have hneg_pos : 0 ≤ -j := by linarith
  have hneg_eq : -j = (-j).toNat := (Int.toNat_of_nonneg hneg_pos).symm
  have h_id : j * (3 * j + 1) = (-j) * (3 * (-j) - 1) := by ring
  rw [h_id]
  conv_lhs => rw [hneg_eq]
  have hm_pos : 1 ≤ (-j).toNat := by
    have h1 : 1 ≤ -j := by linarith
    have : ((1 : ℕ) : ℤ) ≤ -j := by exact_mod_cast h1
    omega
  have h3m1 : (3 * (-j).toNat - 1 : ℤ) = (3 * (-j).toNat - 1 : ℕ) := by
    push_cast
    omega
  rw [h3m1]
  rfl

/-- "Plus pentagonal" `k(3k+1)/2` is strictly increasing in `k : ℕ`. -/
theorem plus_pentagonal_strict_mono :
    StrictMono (fun k : ℕ => k * (3 * k + 1) / 2) := by
  intro a b hab
  show a * (3*a+1)/2 < b * (3*b+1)/2
  have h1 : a * (3*a+1) < b * (3*b+1) := by nlinarith
  have hda : 2 ∣ a * (3 * a + 1) := by
    rcases Nat.even_or_odd a with he | ho
    · obtain ⟨m, hm⟩ := he
      exact ⟨m * (3 * a + 1), by rw [hm]; ring⟩
    · obtain ⟨m, hm⟩ := ho
      refine ⟨a * (3 * m + 2), ?_⟩
      rw [hm]; ring
  have hdb : 2 ∣ b * (3 * b + 1) := by
    rcases Nat.even_or_odd b with he | ho
    · obtain ⟨m, hm⟩ := he
      exact ⟨m * (3 * b + 1), by rw [hm]; ring⟩
    · obtain ⟨m, hm⟩ := ho
      refine ⟨b * (3 * m + 2), ?_⟩
      rw [hm]; ring
  have ha : 2 * (a * (3 * a + 1) / 2) = a * (3 * a + 1) :=
    Nat.mul_div_cancel' hda
  have hb : 2 * (b * (3 * b + 1) / 2) = b * (3 * b + 1) :=
    Nat.mul_div_cancel' hdb
  omega

/-- "Minus pentagonal" `k(3k-1)/2` strictly increases for `1 ≤ a < b`. -/
private theorem minus_pentagonal_strict_mono_pos {a b : ℕ}
    (ha : 1 ≤ a) (hab : a < b) :
    a * (3*a-1)/2 < b * (3*b-1)/2 := by
  have hb_pos : 1 ≤ b := by omega
  have h3am1_pos : 1 ≤ 3 * a - 1 := by omega
  have h3bm1_pos : 1 ≤ 3 * b - 1 := by omega
  have h_lt : a * (3 * a - 1) < b * (3 * b - 1) := by
    have h1 : 3 * a - 1 ≤ 3 * b - 1 := by omega
    have h2 : a * (3 * a - 1) ≤ a * (3 * b - 1) := Nat.mul_le_mul_left a h1
    have h3 : a * (3 * b - 1) < b * (3 * b - 1) := by
      have hpos : (3 * b - 1) > 0 := by omega
      exact (Nat.mul_lt_mul_right hpos).mpr hab
    omega
  have hda : 2 ∣ a * (3 * a - 1) := by
    rcases Nat.even_or_odd a with he | ho
    · obtain ⟨m, hm⟩ := he
      exact ⟨m * (3 * a - 1), by rw [hm]; ring⟩
    · obtain ⟨m, hm⟩ := ho
      refine ⟨a * (3 * m + 1), ?_⟩
      rw [hm]
      rw [show 3 * (2 * m + 1) - 1 = 6 * m + 2 by omega]
      ring
  have hdb : 2 ∣ b * (3 * b - 1) := by
    rcases Nat.even_or_odd b with he | ho
    · obtain ⟨m, hm⟩ := he
      exact ⟨m * (3 * b - 1), by rw [hm]; ring⟩
    · obtain ⟨m, hm⟩ := ho
      refine ⟨b * (3 * m + 1), ?_⟩
      rw [hm]
      rw [show 3 * (2 * m + 1) - 1 = 6 * m + 2 by omega]
      ring
  have h_eq_a : 2 * (a * (3 * a - 1) / 2) = a * (3 * a - 1) := Nat.mul_div_cancel' hda
  have h_eq_b : 2 * (b * (3 * b - 1) / 2) = b * (3 * b - 1) := Nat.mul_div_cancel' hdb
  omega

/-- "Minus pentagonal" `k(3k-1)/2` is strictly increasing in `k : ℕ`. -/
theorem minus_pentagonal_strict_mono :
    StrictMono (fun k : ℕ => k * (3 * k - 1) / 2) := by
  intro a b hab
  show a * (3*a-1)/2 < b * (3*b-1)/2
  rcases Nat.eq_zero_or_pos a with h | h
  · subst h
    simp
    have : 1 ≤ b := hab
    by_cases hb1 : b = 1
    · rw [hb1]
    · have hb2 : 1 < b := by omega
      have h_inc := minus_pentagonal_strict_mono_pos
        (show (1 : ℕ) ≤ 1 from le_refl _) hb2
      omega
  · exact minus_pentagonal_strict_mono_pos h hab

/-- **No `k ∈ ℕ` satisfies "minus pentagonal at k" = "plus pentagonal at j > 0"**.

The algebraic fact: if `k(3k-1)/2 = j(3j+1)/2` with `j > 0`, then
`(k+j)(3(k-j) - 1) = 0`, which forces either `k+j = 0` (impossible for
positive `j`) or `3(k-j) = 1` (no integer solution).

Used to show `pentagonalSign`'s first `find?` branch returns `none` when
the index is a strict "+ pentagonal" number. -/
theorem no_minus_pentagonal_eq_plus_pentagonal (j : ℕ) (hj : 0 < j) :
    ∀ k : ℕ, k * (3 * k - 1) / 2 ≠ j * (3 * j + 1) / 2 := by
  intro k heq
  have hdk : 2 ∣ k * (3 * k - 1) := by
    rcases Nat.even_or_odd k with he | ho
    · obtain ⟨m, hm⟩ := he
      exact ⟨m * (3 * k - 1), by rw [hm]; ring⟩
    · obtain ⟨m, hm⟩ := ho
      refine ⟨k * (3 * m + 1), ?_⟩
      rw [hm]
      rw [show 3 * (2 * m + 1) - 1 = 6 * m + 2 by omega]
      ring
  have hdj : 2 ∣ j * (3 * j + 1) := by
    rcases Nat.even_or_odd j with he | ho
    · obtain ⟨m, hm⟩ := he
      exact ⟨m * (3 * j + 1), by rw [hm]; ring⟩
    · obtain ⟨m, hm⟩ := ho
      refine ⟨j * (3 * m + 2), ?_⟩
      rw [hm]; ring
  have h_eq_full : k * (3 * k - 1) = j * (3 * j + 1) := by
    have := congrArg (fun x => 2 * x) heq
    simp only at this
    rw [show 2 * (k * (3 * k - 1) / 2) = k * (3 * k - 1) by
      rw [mul_comm]; exact Nat.div_mul_cancel hdk] at this
    rw [show 2 * (j * (3 * j + 1) / 2) = j * (3 * j + 1) by
      rw [mul_comm]; exact Nat.div_mul_cancel hdj] at this
    exact this
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp at h_eq_full
    omega
  · have hk1 : 1 ≤ k := hk
    have h_int_eq : (k : ℤ) * (3 * k - 1) = j * (3 * j + 1) := by
      have h_cast_full : ((k * (3 * k - 1) : ℕ) : ℤ) = ((j * (3 * j + 1) : ℕ) : ℤ) := by
        exact_mod_cast h_eq_full
      have h_3km1 : ((3 * k - 1 : ℕ) : ℤ) = 3 * (k : ℤ) - 1 := by push_cast; omega
      have h_lhs : ((k * (3 * k - 1) : ℕ) : ℤ) = (k : ℤ) * (3 * k - 1) := by
        push_cast
        rw [h_3km1]
      have h_rhs : ((j * (3 * j + 1) : ℕ) : ℤ) = (j : ℤ) * (3 * j + 1) := by
        push_cast; ring
      linarith [h_cast_full, h_lhs.symm, h_rhs.symm]
    have h_factor : ((k : ℤ) + j) * (3 * ((k : ℤ) - j) - 1) = 0 := by
      have : (k : ℤ) * (3 * k - 1) - (j : ℤ) * (3 * j + 1) = 0 := by
        rw [h_int_eq]; ring
      nlinarith [this]
    rcases mul_eq_zero.mp h_factor with h_sum | h_diff
    · have hk_pos : (k : ℤ) ≥ 1 := by exact_mod_cast hk1
      have hj_pos : (j : ℤ) ≥ 1 := by exact_mod_cast hj
      omega
    · omega

/-- **`pentagonalSign` at "+ pentagonal" indices**: for `j ≥ 1`,
`σ(j*(3j+1)/2) = (-1)^j`.  First find? returns none (by
`no_minus_pentagonal_eq_plus_pentagonal`); second find? finds j as the
smallest match (by `plus_pentagonal_strict_mono`). -/
theorem pentagonalSign_plus_pentagonal (j : ℕ) (hj : 0 < j) :
    pentagonalSign (j * (3 * j + 1) / 2) = (-1 : ℤ)^j := by
  set n := j * (3 * j + 1) / 2 with hn
  unfold pentagonalSign
  have h_first : (List.range (n + 1)).find? (fun k => n = k * (3 * k - 1) / 2) = none := by
    rw [List.find?_eq_none]
    intro k' _ hpred
    have heq : n = k' * (3 * k' - 1) / 2 := of_decide_eq_true hpred
    exact no_minus_pentagonal_eq_plus_pentagonal j hj k' heq.symm
  rw [h_first]
  have hj_le : j ≤ n := by
    rw [hn]
    have h1 : 2 * j ≤ j * (3 * j + 1) := by nlinarith
    have h2 : 2 ∣ j * (3 * j + 1) := by
      rcases Nat.even_or_odd j with he | ho
      · obtain ⟨m, hm⟩ := he
        exact ⟨m * (3 * j + 1), by rw [hm]; ring⟩
      · obtain ⟨m, hm⟩ := ho
        refine ⟨j * (3 * m + 2), ?_⟩
        rw [hm]; ring
    have h_eq : 2 * (j * (3 * j + 1) / 2) = j * (3 * j + 1) := Nat.mul_div_cancel' h2
    omega
  have h_second : (List.range (n + 1)).find?
      (fun k => 0 < k ∧ n = k * (3 * k + 1) / 2) = some j := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨?_, j, ?_, ?_, ?_⟩
    · show decide (0 < j ∧ n = j * (3 * j + 1) / 2) = true
      simp [hj, hn]
    · simp [List.length_range]; omega
    · rw [List.getElem_range]
    · intro k' hk'
      have hk'_lt : k' < n + 1 := by omega
      rw [List.getElem_range]
      show (!decide (0 < k' ∧ n = k' * (3 * k' + 1) / 2)) = true
      rw [Bool.not_eq_true', decide_eq_false_iff_not]
      intro ⟨hk'_pos, heq⟩
      have h_mono : k' * (3 * k' + 1) / 2 < j * (3 * j + 1) / 2 :=
        plus_pentagonal_strict_mono hk'
      rw [hn] at heq
      omega
  rw [h_second]

/-- **`pentagonalSign` at "- pentagonal" indices**: for `m ≥ 1`,
`σ(m*(3m-1)/2) = (-1)^m`.  First find? returns some m (smallest by
`minus_pentagonal_strict_mono`). -/
theorem pentagonalSign_minus_pentagonal (m : ℕ) (hm : 1 ≤ m) :
    pentagonalSign (m * (3 * m - 1) / 2) = (-1 : ℤ)^m := by
  set n := m * (3 * m - 1) / 2 with hn
  unfold pentagonalSign
  have hm_le : m ≤ n := by
    rw [hn]
    have h1 : 2 * m ≤ m * (3 * m - 1) := by
      have h_ge2 : 3 * m - 1 ≥ 2 := by omega
      have : m * 2 ≤ m * (3 * m - 1) := Nat.mul_le_mul_left m h_ge2
      omega
    have h2 : 2 ∣ m * (3 * m - 1) := by
      rcases Nat.even_or_odd m with he | ho
      · obtain ⟨l, hl⟩ := he
        exact ⟨l * (3 * m - 1), by rw [hl]; ring⟩
      · obtain ⟨l, hl⟩ := ho
        refine ⟨m * (3 * l + 1), ?_⟩
        rw [hl]
        rw [show 3 * (2 * l + 1) - 1 = 6 * l + 2 by omega]
        ring
    have h_eq : 2 * (m * (3 * m - 1) / 2) = m * (3 * m - 1) := Nat.mul_div_cancel' h2
    omega
  have h_first : (List.range (n + 1)).find?
      (fun k => n = k * (3 * k - 1) / 2) = some m := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨?_, m, ?_, ?_, ?_⟩
    · show decide (n = m * (3 * m - 1) / 2) = true
      simp [hn]
    · simp [List.length_range]; omega
    · rw [List.getElem_range]
    · intro k' hk'
      have hk'_lt : k' < n + 1 := by omega
      rw [List.getElem_range]
      show (!decide (n = k' * (3 * k' - 1) / 2)) = true
      rw [Bool.not_eq_true', decide_eq_false_iff_not]
      intro heq
      have h_mono : k' * (3 * k' - 1) / 2 < m * (3 * m - 1) / 2 :=
        minus_pentagonal_strict_mono hk'
      rw [hn] at heq
      omega
  rw [h_first]

/-- For `j ≥ 0`, `j.toNat = j.natAbs`. -/
theorem toNat_eq_natAbs_of_nonneg (j : ℤ) (hj : 0 ≤ j) :
    j.toNat = j.natAbs := by
  have h_eq : (j.toNat : ℤ) = (j.natAbs : ℤ) := by
    rw [Int.toNat_of_nonneg hj, Int.natAbs_of_nonneg hj]
  exact_mod_cast h_eq

/-- For `j ≤ 0`, `(-j).toNat = j.natAbs`. -/
theorem neg_toNat_eq_natAbs_of_nonpos (j : ℤ) (hj : j ≤ 0) :
    (-j).toNat = j.natAbs := by
  have h_nn : 0 ≤ -j := by linarith
  rw [Int.natAbs_neg j |>.symm]
  exact toNat_eq_natAbs_of_nonneg (-j) h_nn

/-- **Main identity**: `pentagonalSign (pentagonalIndex j) = (-1)^j.natAbs`.

This is the bridge needed to convert Ch04's ℤ-indexed Euler pentagonal
into ℕ-indexed σ-form: `∑' j : ℤ, (-1)^j q^(pentagonalIndex j) =
∑' n : ℕ, σ(n) q^n` (the latter exists if we extend σ to be 0 outside
the range of pentagonalIndex). -/
theorem pentagonalSign_pentagonalIndex_eq (j : ℤ) :
    pentagonalSign (pentagonalIndex j) = (-1 : ℤ)^j.natAbs := by
  rcases lt_trichotomy j 0 with hj_neg | hj_zero | hj_pos
  · rw [pentagonalIndex_of_neg j hj_neg]
    have h_pos : 1 ≤ (-j).toNat := by
      have h1 : 1 ≤ -j := by linarith
      have : ((1 : ℕ) : ℤ) ≤ -j := by exact_mod_cast h1
      omega
    rw [pentagonalSign_minus_pentagonal (-j).toNat h_pos]
    congr 1
    exact neg_toNat_eq_natAbs_of_nonpos j (le_of_lt hj_neg)
  · subst hj_zero
    decide
  · rw [pentagonalIndex_of_nonneg j (le_of_lt hj_pos)]
    have h_pos : 0 < j.toNat := by
      rw [toNat_eq_natAbs_of_nonneg j (le_of_lt hj_pos)]
      have : (0 : ℤ) < j := hj_pos
      omega
    rw [pentagonalSign_plus_pentagonal j.toNat h_pos]
    congr 1
    exact toNat_eq_natAbs_of_nonneg j (le_of_lt hj_pos)

/-- **Verification: for `|j| ≤ 10`** (kept for documentation). -/
theorem pentagonalSign_pentagonalIndex_eq_le_ten (j : ℤ) (hj : -10 ≤ j ∧ j ≤ 10) :
    pentagonalSign (pentagonalIndex j) = (-1)^j.natAbs :=
  pentagonalSign_pentagonalIndex_eq j

/-- `(-1 : ℂ)^j = (-1)^j.natAbs` — zpow ↔ npow bridge for `±1`. -/
theorem neg_one_zpow_complex_eq_npow_natAbs (j : ℤ) :
    (-1 : ℂ)^j = (-1)^j.natAbs := by
  by_cases hev : Even j
  · rw [hev.neg_one_zpow]
    have : Even j.natAbs := by exact_mod_cast Int.natAbs_even.mpr hev
    rw [this.neg_one_pow]
  · have hodd : Odd j := Int.not_even_iff_odd.mp hev
    have h_int : (-1 : ℂ)^j = -1 := by
      rw [neg_one_zpow_eq_ite]
      simp [hev]
    rw [h_int]
    have : Odd j.natAbs := by exact_mod_cast Int.natAbs_odd.mpr hodd
    rw [this.neg_one_pow]

/-- `pentagonalIndex (-k) = k * (3*k - 1) / 2` for `k : ℕ`. -/
theorem pentagonalIndex_neg_natCast (k : ℕ) :
    pentagonalIndex (-(k : ℤ)) = k * (3 * k - 1) / 2 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; decide
  · have hkz : (-(k : ℤ)) < 0 := by
      have h1 : (1 : ℤ) ≤ k := by exact_mod_cast hk
      linarith
    rw [pentagonalIndex_of_neg _ hkz]
    have : -(-(k : ℤ)) = k := by ring
    rw [this, Int.toNat_natCast]

/-- `pentagonalIndex (k : ℤ) = k * (3*k + 1) / 2` for `k : ℕ`. -/
theorem pentagonalIndex_natCast (k : ℕ) :
    pentagonalIndex (k : ℤ) = k * (3 * k + 1) / 2 := by
  rw [pentagonalIndex_of_nonneg _ (Int.natCast_nonneg k)]
  rw [Int.toNat_natCast]

/-- **Support of `pentagonalSign` ⊆ range `pentagonalIndex`**: if `σ(n) ≠ 0`,
then `n` is a pentagonal number (in the image of `pentagonalIndex : ℤ → ℕ`). -/
theorem pentagonalSign_ne_zero_imp_mem_range (n : ℕ) (hn : pentagonalSign n ≠ 0) :
    n ∈ Set.range pentagonalIndex := by
  unfold pentagonalSign at hn
  generalize h_find1 : (List.range (n + 1)).find?
      (fun k => n = k * (3 * k - 1) / 2) = res1
  cases res1 with
  | some k =>
    rw [h_find1] at hn
    have h_pred := List.find?_some h_find1
    simp at h_pred
    refine ⟨-(k : ℤ), ?_⟩
    rw [pentagonalIndex_neg_natCast]
    exact h_pred.symm
  | none =>
    rw [h_find1] at hn
    generalize h_find2 : (List.range (n + 1)).find?
        (fun k => 0 < k ∧ n = k * (3 * k + 1) / 2) = res2
    cases res2 with
    | some k =>
      rw [h_find2] at hn
      have h_pred := List.find?_some h_find2
      simp at h_pred
      obtain ⟨_, h_eq⟩ := h_pred
      refine ⟨(k : ℤ), ?_⟩
      rw [pentagonalIndex_natCast]
      exact h_eq.symm
    | none =>
      rw [h_find2] at hn
      simp at hn

/-- **Analytic Euler pentagonal in ℕ-indexed σ-form**:
`eulerPentagonalInfiniteProduct q = ∑' n : ℕ, σ(n) · q^n` for `‖q‖ < 1`.

The bridge from Ch04's ℤ-indexed bilateral form to the formal-Taylor
ℕ-form via:
  - Function.Injective.tsum_eq (with pentagonalIndex_injective).
  - Support confinement (pentagonalSign_ne_zero_imp_mem_range).
  - Pointwise matching (pentagonalSign_pentagonalIndex_eq +
    neg_one_zpow_complex_eq_npow_natAbs). -/
theorem eulerPentagonalInfiniteProduct_eq_tsum_pentagonalSign
    (q : ℂ) (hqnorm : ‖q‖ < 1) :
    QseriesFormalization.PartI.Ch04.eulerPentagonalInfiniteProduct q =
      ∑' n : ℕ, ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign n : ℤ) : ℂ) * q^n := by
  rw [QseriesFormalization.PartI.Ch04.eulerPentagonalInfiniteProduct_eq_tsum' q hqnorm]
  symm
  have h_inj : Function.Injective pentagonalIndex := pentagonalIndex_injective
  have h_supp : Function.support
      (fun n : ℕ => ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign n : ℤ) : ℂ) * q^n) ⊆
      Set.range pentagonalIndex := by
    intro n hn
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hn
    obtain ⟨hsig, _⟩ := hn
    have h_sig_ne : QseriesFormalization.PartI.Ch04Franklin.pentagonalSign n ≠ 0 := by
      intro h; apply hsig
      rw [h]; simp
    exact pentagonalSign_ne_zero_imp_mem_range n h_sig_ne
  have h_reindex := h_inj.tsum_eq
    (f := fun n : ℕ =>
      ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign n : ℤ) : ℂ) * q^n) h_supp
  rw [← h_reindex]
  congr 1
  ext j
  show ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign (pentagonalIndex j) : ℤ) : ℂ)
        * q^(pentagonalIndex j) =
       (-1 : ℂ)^j * q^(j * (3 * j + 1) / 2)
  rw [pentagonalSign_pentagonalIndex_eq j]
  have h_qpow : q^(pentagonalIndex j) = q^(j * (3 * j + 1) / 2) := by
    rw [show (j * (3 * j + 1) / 2 : ℤ) = ((pentagonalIndex j : ℕ) : ℤ) from
      (pentagonalIndex_cast j).symm]
    rw [zpow_natCast]
  rw [h_qpow]
  have h_cast : (((-1 : ℤ)^j.natAbs : ℤ) : ℂ) = (-1 : ℂ)^j := by
    push_cast
    rw [← neg_one_zpow_complex_eq_npow_natAbs]
  rw [h_cast]

/-! ### Cube identity via tsum_mul_tsum (analytic side). -/

open QseriesFormalization.PartI.Ch04 (eulerPentagonalInfiniteProduct)

/-- Norm-summability of `(σ(n) : ℂ) * q^n` for `‖q‖ < 1`. -/
theorem summable_norm_pentagonalSign_mul_pow (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ =>
      ‖((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign n : ℤ) : ℂ) * q^n‖) :=
  (summable_pentagonalSign_mul_pow q hq).norm

/-- The convolution sequence `n ↦ ∑_{a+b=n} σ(a) q^a · σ(b) q^b`. -/
noncomputable def sigmaQConv (q : ℂ) (n : ℕ) : ℂ :=
  ∑ ab ∈ Finset.antidiagonal n,
    ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ab.1 : ℤ) : ℂ) * q^ab.1 *
    (((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ab.2 : ℤ) : ℂ) * q^ab.2)

theorem summable_norm_sigmaQConv (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => ‖sigmaQConv q n‖) := by
  have h := summable_norm_sum_mul_antidiagonal_of_summable_norm
    (summable_norm_pentagonalSign_mul_pow q hq)
    (summable_norm_pentagonalSign_mul_pow q hq)
  exact h

theorem summable_sigmaQConv (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => sigmaQConv q n) :=
  (summable_norm_sigmaQConv q hq).of_norm

/-- `(eulerPentagonalInfiniteProduct q)^2 = ∑' n, sigmaQConv q n`. -/
theorem eulerPentagonalInfiniteProduct_sq_eq_tsum_sigmaQConv
    (q : ℂ) (hqnorm : ‖q‖ < 1) :
    (eulerPentagonalInfiniteProduct q)^2 = ∑' n : ℕ, sigmaQConv q n := by
  rw [sq, eulerPentagonalInfiniteProduct_eq_tsum_pentagonalSign q hqnorm]
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (summable_norm_pentagonalSign_mul_pow q hqnorm)
    (summable_norm_pentagonalSign_mul_pow q hqnorm)]
  rfl

/-- `(eulerPentagonalInfiniteProduct q)^3 = ∑' n, ∑_{m+k=n} sigmaQConv q m · σ(k) q^k`.
The Cauchy product of `(epp q)^2 = ∑ sigmaQConv` with `epp q = ∑ σ q^k`. -/
theorem eulerPentagonalInfiniteProduct_cube_eq_tsum
    (q : ℂ) (hqnorm : ‖q‖ < 1) :
    (eulerPentagonalInfiniteProduct q)^3 =
      ∑' n : ℕ, ∑ mk ∈ Finset.antidiagonal n,
        sigmaQConv q mk.1 *
        (((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign mk.2 : ℤ) : ℂ) * q^mk.2) := by
  rw [show (eulerPentagonalInfiniteProduct q)^3 =
      (eulerPentagonalInfiniteProduct q)^2 * eulerPentagonalInfiniteProduct q from by ring]
  rw [eulerPentagonalInfiniteProduct_sq_eq_tsum_sigmaQConv q hqnorm]
  rw [eulerPentagonalInfiniteProduct_eq_tsum_pentagonalSign q hqnorm]
  exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (summable_norm_sigmaQConv q hqnorm)
    (summable_norm_pentagonalSign_mul_pow q hqnorm)

/-- The Nat-level cube convolution: `∑_{(p,q'):p+q'=n} (∑_{(a,b):a+b=p} σ(a)·σ(b)) · σ(q')`.
Mirror of `Pending/Sylvester_TripleSum.cubeConvolution`. -/
noncomputable def cubeConvolution (n : ℕ) : ℤ :=
  ∑ pq ∈ Finset.antidiagonal n,
    (∑ ab ∈ Finset.antidiagonal pq.1,
      (QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ab.1 : ℤ) *
      (QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ab.2 : ℤ)) *
    (QseriesFormalization.PartI.Ch04Franklin.pentagonalSign pq.2 : ℤ)

/-- `sigmaQConv q m = q^m · ∑_{a+b=m} σ(a)·σ(b)`: extract the `q^m` factor. -/
theorem sigmaQConv_eq_qpow_mul (q : ℂ) (m : ℕ) :
    sigmaQConv q m = q^m *
      (∑ ab ∈ Finset.antidiagonal m,
        ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ab.1 : ℤ) : ℂ) *
        ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ab.2 : ℤ) : ℂ)) := by
  unfold sigmaQConv
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  rw [Finset.mem_antidiagonal] at hab
  have h_pow : q^ab.1 * q^ab.2 = q^m := by
    rw [← pow_add, hab]
  calc ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ab.1 : ℤ) : ℂ) * q^ab.1 *
        (((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ab.2 : ℤ) : ℂ) * q^ab.2)
      = ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ab.1 : ℤ) : ℂ) *
        ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ab.2 : ℤ) : ℂ) *
        (q^ab.1 * q^ab.2) := by ring
    _ = ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ab.1 : ℤ) : ℂ) *
        ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ab.2 : ℤ) : ℂ) * q^m := by
        rw [h_pow]
    _ = q^m * (((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ab.1 : ℤ) : ℂ) *
        ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ab.2 : ℤ) : ℂ)) := by ring

/-- The double-antidiagonal sum collapses: `q^n · cubeConvolution n`. -/
theorem double_antidiagonal_eq_qpow_mul_cube (q : ℂ) (n : ℕ) :
    (∑ mk ∈ Finset.antidiagonal n,
      sigmaQConv q mk.1 *
      (((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign mk.2 : ℤ) : ℂ) * q^mk.2))
    = q^n * ((cubeConvolution n : ℤ) : ℂ) := by
  unfold cubeConvolution
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mk hmk
  rw [Finset.mem_antidiagonal] at hmk
  rw [sigmaQConv_eq_qpow_mul]
  have h_pow : q^mk.1 * q^mk.2 = q^n := by
    rw [← pow_add, hmk]
  calc q^mk.1 * (∑ ab ∈ Finset.antidiagonal mk.1,
          ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ab.1 : ℤ) : ℂ) *
          ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ab.2 : ℤ) : ℂ)) *
        (((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign mk.2 : ℤ) : ℂ) * q^mk.2)
      = (q^mk.1 * q^mk.2) *
        ((∑ ab ∈ Finset.antidiagonal mk.1,
          ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ab.1 : ℤ) : ℂ) *
          ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ab.2 : ℤ) : ℂ)) *
        ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign mk.2 : ℤ) : ℂ)) := by ring
    _ = q^n * ((∑ ab ∈ Finset.antidiagonal mk.1,
          ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ab.1 : ℤ) : ℂ) *
          ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign ab.2 : ℤ) : ℂ)) *
        ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign mk.2 : ℤ) : ℂ)) := by rw [h_pow]

/-- **(epp q)^3 = ∑' n, q^n · cubeConvolution n** for ‖q‖ < 1.

Combines `eulerPentagonalInfiniteProduct_cube_eq_tsum` with the inner
simplification `double_antidiagonal_eq_qpow_mul_cube`. -/
theorem eulerPentagonalInfiniteProduct_cube_eq_tsum_qpow_cubeConvolution
    (q : ℂ) (hqnorm : ‖q‖ < 1) :
    (eulerPentagonalInfiniteProduct q)^3 =
      ∑' n : ℕ, q^n * ((cubeConvolution n : ℤ) : ℂ) := by
  rw [eulerPentagonalInfiniteProduct_cube_eq_tsum q hqnorm]
  apply tsum_congr
  intro n
  exact double_antidiagonal_eq_qpow_mul_cube q n

/-- **Analytic-formal bridge for `qPochInfPS ℂ`**: the analytic
`eulerPentagonalInfiniteProduct q` is the analytic evaluation of the
formal power series `qPochInfPS ℂ` at `q`, for `‖q‖ < 1`. -/
theorem eulerPentagonalInfiniteProduct_eq_tsum_qPochInfPS_coeff
    (q : ℂ) (hqnorm : ‖q‖ < 1) :
    eulerPentagonalInfiniteProduct q =
      ∑' n : ℕ, (qPochInfPS ℂ).coeff n * q^n := by
  rw [eulerPentagonalInfiniteProduct_eq_tsum_pentagonalSign q hqnorm]
  apply tsum_congr
  intro n
  rw [coeff_qPochInfPS_eq_pentagonalSign]

/-- Norm-summability of `q^n · (cubeConvolution n : ℂ)` for `‖q‖ < 1`. -/
theorem summable_norm_qpow_cubeConvolution (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => ‖q^n * ((cubeConvolution n : ℤ) : ℂ)‖) := by
  have h_summable := summable_norm_sum_mul_antidiagonal_of_summable_norm
    (summable_norm_sigmaQConv q hq)
    (summable_norm_pentagonalSign_mul_pow q hq)
  apply h_summable.congr
  intro n
  congr 1
  exact double_antidiagonal_eq_qpow_mul_cube q n

/-- Summability (plain): `Summable (fun n => q^n · cubeConvolution n)` for `‖q‖ < 1`. -/
theorem summable_qpow_cubeConvolution (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => q^n * ((cubeConvolution n : ℤ) : ℂ)) :=
  (summable_norm_qpow_cubeConvolution q hq).of_norm

end Ch19
end PartIV
end QseriesFormalization
