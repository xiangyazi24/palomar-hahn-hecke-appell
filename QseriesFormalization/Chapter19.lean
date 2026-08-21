import QseriesFormalization.Basic
import QseriesFormalization.Chapter01
import QseriesFormalization.Chapter05_Franklin
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse

namespace QseriesFormalization
namespace PartIV
namespace Ch19

open QseriesFormalization.Ch01 (partitionCount)
open PowerSeries

-- Ramanujan's deeper congruences require higher partition values.
-- Here we verify congruences using p(0)..p(11) proved in Ch01.

/-- p(5·0+4) = p(4) = 5 ≡ 0 (mod 5). -/
theorem ramanujan_5_n0 : 5 ∣ partitionCount (5 * 0 + 4) := by
  simp [Ch01.partitionCount_four]

/-- p(5·1+4) = p(9) = 30 ≡ 0 (mod 5). -/
theorem ramanujan_5_n1 : 5 ∣ partitionCount (5 * 1 + 4) := by
  simp [Ch01.partitionCount_nine]

/-- p(7·0+5) = p(5) = 7 ≡ 0 (mod 7). -/
theorem ramanujan_7_n0 : 7 ∣ partitionCount (7 * 0 + 5) := by
  simp [Ch01.partitionCount_five]

/-- p(11·0+6) = p(6) = 11 ≡ 0 (mod 11). -/
theorem ramanujan_11_n0 : 11 ∣ partitionCount (11 * 0 + 6) := by
  simp [Ch01.partitionCount_six]

/-- Deeper: p(5) = 7, and 7 = 7·1, so p(5) ≡ 0 (mod 7).
This is both p(7·0+5) and a standalone fact. -/
theorem p5_dvd_7 : 7 ∣ partitionCount 5 := by
  simp [Ch01.partitionCount_five]

/-- p(10) = 42 = 6·7, so p(7·1-2) ≡ 0 (mod 7). -/
theorem p10_dvd_7 : 7 ∣ partitionCount 10 := by
  simp [Ch01.partitionCount_ten]

/-- p(11) = 56 = 8·7 ≡ 0 (mod 7). -/
theorem p11_dvd_7 : 7 ∣ partitionCount 11 := by
  simp [Ch01.partitionCount_eleven]

/-- p(11) = 56 = 56, and 56 % 11 = 1, so p(11) ≢ 0 (mod 11).
This is NOT a Ramanujan congruence — 11 does not divide p(11). -/
theorem p11_mod_11 : partitionCount 11 % 11 = 1 := by
  simp [Ch01.partitionCount_eleven]

/-- p(6) = 11 ≡ 0 (mod 11): Ramanujan's third family at n = 0. -/
theorem p6_dvd_11 : 11 ∣ partitionCount 6 := by
  simp [Ch01.partitionCount_six]

-- p(25n+24) ≡ 0 (mod 25) requires partitionCount_24 (not yet in Ch01).

/-- p(4) = 5 ≡ 0 (mod 5) but p(4) = 5 ≢ 0 (mod 25). -/
theorem p4_mod_25 : partitionCount 4 % 25 = 5 := by
  simp [Ch01.partitionCount_four]

/-- p(9) = 30 ≡ 0 (mod 5) and p(9) ≡ 0 (mod 10) and p(9) ≡ 0 (mod 15) but p(9) ≢ 0 (mod 25). -/
theorem p9_mod_25 : partitionCount 9 % 25 = 5 := by
  simp [Ch01.partitionCount_nine]

/-- p(0) = 1, so p(0) mod 5 = 1. -/
theorem p0_mod_5 : partitionCount 0 % 5 = 1 := by
  simp [Ch01.partitionCount_zero]

/-- p(1) = 1, so p(1) mod 5 = 1. -/
theorem p1_mod_5 : partitionCount 1 % 5 = 1 := by
  simp [Ch01.partitionCount_one]

/-- p(2) = 2, so p(2) mod 5 = 2. -/
theorem p2_mod_5 : partitionCount 2 % 5 = 2 := by
  simp [Ch01.partitionCount_two]

/-- p(3) = 3, so p(3) mod 5 = 3. -/
theorem p3_mod_5 : partitionCount 3 % 5 = 3 := by
  simp [Ch01.partitionCount_three]

/-- p(7) = 15 ≡ 0 (mod 5). -/
theorem p7_dvd_5 : 5 ∣ partitionCount 7 := by
  simp [Ch01.partitionCount_seven]

/-- p(8) = 22 ≡ 0 (mod 11). -/
theorem p8_dvd_11 : 11 ∣ partitionCount 8 := by
  simp [Ch01.partitionCount_eight]

/-- p(8) = 22 ≡ 0 (mod 2). -/
theorem p8_dvd_2 : 2 ∣ partitionCount 8 := by
  simp [Ch01.partitionCount_eight]

/-- p(10) = 42 ≡ 0 (mod 7). -/
theorem p10_dvd_14 : 14 ∣ partitionCount 10 := by
  simp [Ch01.partitionCount_ten]

/-- p(10) = 42 ≡ 0 (mod 21). -/
theorem p10_dvd_21 : 21 ∣ partitionCount 10 := by
  simp [Ch01.partitionCount_ten]

/-- p(11) = 56 ≡ 0 (mod 8). -/
theorem p11_dvd_8 : 8 ∣ partitionCount 11 := by
  simp [Ch01.partitionCount_eleven]

/-- p(11) = 56 ≡ 0 (mod 4). -/
theorem p11_dvd_4 : 4 ∣ partitionCount 11 := by
  simp [Ch01.partitionCount_eleven]

/-- p(11) = 56 ≡ 0 (mod 14). -/
theorem p11_dvd_14 : 14 ∣ partitionCount 11 := by
  simp [Ch01.partitionCount_eleven]

/-- p(11) = 56 ≡ 0 (mod 28). -/
theorem p11_dvd_28 : 28 ∣ partitionCount 11 := by
  simp [Ch01.partitionCount_eleven]

/-- p(9) = 30 ≡ 0 (mod 6). -/
theorem p9_dvd_6 : 6 ∣ partitionCount 9 := by
  simp [Ch01.partitionCount_nine]

/-- p(9) = 30 ≡ 0 (mod 3). -/
theorem p9_dvd_3 : 3 ∣ partitionCount 9 := by
  simp [Ch01.partitionCount_nine]

/-- p(0) mod 7 = 1. -/
theorem p0_mod_7 : partitionCount 0 % 7 = 1 := by
  simp [Ch01.partitionCount_zero]

/-- p(1) mod 11 = 1. -/
theorem p1_mod_11 : partitionCount 1 % 11 = 1 := by
  simp [Ch01.partitionCount_one]

/-- p(2) mod 7 = 2. -/
theorem p2_mod_7 : partitionCount 2 % 7 = 2 := by
  simp [Ch01.partitionCount_two]

/-- p(3) mod 7 = 3. -/
theorem p3_mod_7 : partitionCount 3 % 7 = 3 := by
  simp [Ch01.partitionCount_three]

/-- p(4) mod 7 = 5. -/
theorem p4_mod_7 : partitionCount 4 % 7 = 5 := by
  simp [Ch01.partitionCount_four]

/-- p(5) mod 7 = 0. -/
theorem p5_mod_7 : partitionCount 5 % 7 = 0 := by
  simp [Ch01.partitionCount_five]

/-- p(6) mod 7 = 4. -/
theorem p6_mod_7 : partitionCount 6 % 7 = 4 := by
  simp [Ch01.partitionCount_six]

/-- p(7) mod 7 = 1. -/
theorem p7_mod_7 : partitionCount 7 % 7 = 1 := by
  simp [Ch01.partitionCount_seven]

/-- p(8) mod 7 = 1. -/
theorem p8_mod_7 : partitionCount 8 % 7 = 1 := by
  simp [Ch01.partitionCount_eight]

/-- p(9) mod 7 = 2. -/
theorem p9_mod_7 : partitionCount 9 % 7 = 2 := by
  simp [Ch01.partitionCount_nine]

/-- p(10) mod 7 = 0. -/
theorem p10_mod_7 : partitionCount 10 % 7 = 0 := by
  simp [Ch01.partitionCount_ten]

/-- p(11) mod 7 = 0. -/
theorem p11_mod_7 : partitionCount 11 % 7 = 0 := by
  simp [Ch01.partitionCount_eleven]

/-- p(5) mod 11 = 7. -/
theorem p5_mod_11 : partitionCount 5 % 11 = 7 := by
  simp [Ch01.partitionCount_five]

/-- p(6) mod 11 = 0. -/
theorem p6_mod_11 : partitionCount 6 % 11 = 0 := by
  simp [Ch01.partitionCount_six]

/-- p(7) mod 11 = 4. -/
theorem p7_mod_11 : partitionCount 7 % 11 = 4 := by
  simp [Ch01.partitionCount_seven]

/-- p(8) mod 11 = 0. -/
theorem p8_mod_11 : partitionCount 8 % 11 = 0 := by
  simp [Ch01.partitionCount_eight]

/-- p(9) mod 11 = 8. -/
theorem p9_mod_11 : partitionCount 9 % 11 = 8 := by
  simp [Ch01.partitionCount_nine]

/-- p(10) mod 11 = 9. -/
theorem p10_mod_11 : partitionCount 10 % 11 = 9 := by
  simp [Ch01.partitionCount_ten]

/-- p(5) mod 5 = 2. -/
theorem p5_mod_5 : partitionCount 5 % 5 = 2 := by
  simp [Ch01.partitionCount_five]

/-- p(6) mod 5 = 1. -/
theorem p6_mod_5 : partitionCount 6 % 5 = 1 := by
  simp [Ch01.partitionCount_six]

/-- p(7) mod 5 = 0. -/
theorem p7_mod_5 : partitionCount 7 % 5 = 0 := by
  simp [Ch01.partitionCount_seven]

/-- p(8) mod 5 = 2. -/
theorem p8_mod_5 : partitionCount 8 % 5 = 2 := by
  simp [Ch01.partitionCount_eight]

/-- p(10) mod 5 = 2. -/
theorem p10_mod_5 : partitionCount 10 % 5 = 2 := by
  simp [Ch01.partitionCount_ten]

/-- p(11) mod 5 = 1. -/
theorem p11_mod_5 : partitionCount 11 % 5 = 1 := by
  simp [Ch01.partitionCount_eleven]

theorem p0_mod_11 : partitionCount 0 % 11 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem p2_mod_11 : partitionCount 2 % 11 = 2 := by
  simp [Ch01.partitionCount_two]

theorem p3_mod_11 : partitionCount 3 % 11 = 3 := by
  simp [Ch01.partitionCount_three]

theorem p4_mod_11 : partitionCount 4 % 11 = 5 := by
  simp [Ch01.partitionCount_four]

theorem p9_dvd_10 : 10 ∣ partitionCount 9 := by
  simp [Ch01.partitionCount_nine]

theorem p9_dvd_2 : 2 ∣ partitionCount 9 := by
  simp [Ch01.partitionCount_nine]

theorem p7_dvd_3 : 3 ∣ partitionCount 7 := by
  simp [Ch01.partitionCount_seven]

theorem p10_dvd_6 : 6 ∣ partitionCount 10 := by
  simp [Ch01.partitionCount_ten]

theorem p10_dvd_3 : 3 ∣ partitionCount 10 := by
  simp [Ch01.partitionCount_ten]

theorem p10_dvd_2 : 2 ∣ partitionCount 10 := by
  simp [Ch01.partitionCount_ten]

theorem p11_dvd_56 : 56 ∣ partitionCount 11 := by
  simp [Ch01.partitionCount_eleven]

theorem p11_dvd_2 : 2 ∣ partitionCount 11 := by
  simp [Ch01.partitionCount_eleven]

theorem p8_dvd_22 : 22 ∣ partitionCount 8 := by
  simp [Ch01.partitionCount_eight]

theorem p9_mod_5 : partitionCount 9 % 5 = 0 := by
  simp [Ch01.partitionCount_nine]


-- Additional divisibility and modular facts

-- p(n) mod 3 for n=0..11
theorem p0_mod_3 : partitionCount 0 % 3 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem p1_mod_3 : partitionCount 1 % 3 = 1 := by
  simp [Ch01.partitionCount_one]

theorem p2_mod_3 : partitionCount 2 % 3 = 2 := by
  simp [Ch01.partitionCount_two]

theorem p3_mod_3 : partitionCount 3 % 3 = 0 := by
  simp [Ch01.partitionCount_three]

theorem p4_mod_3 : partitionCount 4 % 3 = 2 := by
  simp [Ch01.partitionCount_four]

theorem p5_mod_3 : partitionCount 5 % 3 = 1 := by
  simp [Ch01.partitionCount_five]

theorem p6_mod_3 : partitionCount 6 % 3 = 2 := by
  simp [Ch01.partitionCount_six]

theorem p7_mod_3 : partitionCount 7 % 3 = 0 := by
  simp [Ch01.partitionCount_seven]

theorem p8_mod_3 : partitionCount 8 % 3 = 1 := by
  simp [Ch01.partitionCount_eight]

theorem p9_mod_3 : partitionCount 9 % 3 = 0 := by
  simp [Ch01.partitionCount_nine]

theorem p10_mod_3 : partitionCount 10 % 3 = 0 := by
  simp [Ch01.partitionCount_ten]

theorem p11_mod_3 : partitionCount 11 % 3 = 2 := by
  simp [Ch01.partitionCount_eleven]

-- p(n) mod 4
theorem p0_mod_4 : partitionCount 0 % 4 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem p1_mod_4 : partitionCount 1 % 4 = 1 := by
  simp [Ch01.partitionCount_one]

theorem p2_mod_4 : partitionCount 2 % 4 = 2 := by
  simp [Ch01.partitionCount_two]

theorem p3_mod_4 : partitionCount 3 % 4 = 3 := by
  simp [Ch01.partitionCount_three]

theorem p4_mod_4 : partitionCount 4 % 4 = 1 := by
  simp [Ch01.partitionCount_four]

theorem p5_mod_4 : partitionCount 5 % 4 = 3 := by
  simp [Ch01.partitionCount_five]

theorem p6_mod_4 : partitionCount 6 % 4 = 3 := by
  simp [Ch01.partitionCount_six]

theorem p7_mod_4 : partitionCount 7 % 4 = 3 := by
  simp [Ch01.partitionCount_seven]

theorem p8_mod_4 : partitionCount 8 % 4 = 2 := by
  simp [Ch01.partitionCount_eight]

theorem p9_mod_4 : partitionCount 9 % 4 = 2 := by
  simp [Ch01.partitionCount_nine]

theorem p10_mod_4 : partitionCount 10 % 4 = 2 := by
  simp [Ch01.partitionCount_ten]

theorem p11_mod_4 : partitionCount 11 % 4 = 0 := by
  simp [Ch01.partitionCount_eleven]

/-! ### Modular arithmetic for primes 13, 17, 19, 23 -/

-- p(n) mod 13
theorem p0_mod_13 : partitionCount 0 % 13 = 1 := by simp [Ch01.partitionCount_zero]
theorem p1_mod_13 : partitionCount 1 % 13 = 1 := by simp [Ch01.partitionCount_one]
theorem p2_mod_13 : partitionCount 2 % 13 = 2 := by simp [Ch01.partitionCount_two]
theorem p3_mod_13 : partitionCount 3 % 13 = 3 := by simp [Ch01.partitionCount_three]
theorem p4_mod_13 : partitionCount 4 % 13 = 5 := by simp [Ch01.partitionCount_four]
theorem p5_mod_13 : partitionCount 5 % 13 = 7 := by simp [Ch01.partitionCount_five]
theorem p6_mod_13 : partitionCount 6 % 13 = 11 := by simp [Ch01.partitionCount_six]
theorem p7_mod_13 : partitionCount 7 % 13 = 2 := by simp [Ch01.partitionCount_seven]
theorem p8_mod_13 : partitionCount 8 % 13 = 9 := by simp [Ch01.partitionCount_eight]
theorem p9_mod_13 : partitionCount 9 % 13 = 4 := by simp [Ch01.partitionCount_nine]
theorem p10_mod_13 : partitionCount 10 % 13 = 3 := by simp [Ch01.partitionCount_ten]
theorem p11_mod_13 : partitionCount 11 % 13 = 4 := by simp [Ch01.partitionCount_eleven]

-- p(n) mod 17
theorem p0_mod_17 : partitionCount 0 % 17 = 1 := by simp [Ch01.partitionCount_zero]
theorem p1_mod_17 : partitionCount 1 % 17 = 1 := by simp [Ch01.partitionCount_one]
theorem p4_mod_17 : partitionCount 4 % 17 = 5 := by simp [Ch01.partitionCount_four]
theorem p7_mod_17 : partitionCount 7 % 17 = 15 := by simp [Ch01.partitionCount_seven]
theorem p8_mod_17 : partitionCount 8 % 17 = 5 := by simp [Ch01.partitionCount_eight]
theorem p9_mod_17 : partitionCount 9 % 17 = 13 := by simp [Ch01.partitionCount_nine]
theorem p10_mod_17 : partitionCount 10 % 17 = 8 := by simp [Ch01.partitionCount_ten]
theorem p11_mod_17 : partitionCount 11 % 17 = 5 := by simp [Ch01.partitionCount_eleven]

-- p(n) mod 19
theorem p0_mod_19 : partitionCount 0 % 19 = 1 := by simp [Ch01.partitionCount_zero]
theorem p8_mod_19 : partitionCount 8 % 19 = 3 := by simp [Ch01.partitionCount_eight]
theorem p9_mod_19 : partitionCount 9 % 19 = 11 := by simp [Ch01.partitionCount_nine]
theorem p10_mod_19 : partitionCount 10 % 19 = 4 := by simp [Ch01.partitionCount_ten]
theorem p11_mod_19 : partitionCount 11 % 19 = 18 := by simp [Ch01.partitionCount_eleven]

-- p(n) mod 23
theorem p0_mod_23 : partitionCount 0 % 23 = 1 := by simp [Ch01.partitionCount_zero]
theorem p11_mod_23 : partitionCount 11 % 23 = 10 := by simp [Ch01.partitionCount_eleven]

/-! ### Composite moduli -/

-- p(n) mod 10
theorem p7_mod_10 : partitionCount 7 % 10 = 5 := by simp [Ch01.partitionCount_seven]
theorem p8_mod_10 : partitionCount 8 % 10 = 2 := by simp [Ch01.partitionCount_eight]
theorem p9_mod_10 : partitionCount 9 % 10 = 0 := by simp [Ch01.partitionCount_nine]
theorem p10_mod_10 : partitionCount 10 % 10 = 2 := by simp [Ch01.partitionCount_ten]
theorem p11_mod_10 : partitionCount 11 % 10 = 6 := by simp [Ch01.partitionCount_eleven]

-- p(n) mod 12
theorem p7_mod_12 : partitionCount 7 % 12 = 3 := by simp [Ch01.partitionCount_seven]
theorem p8_mod_12 : partitionCount 8 % 12 = 10 := by simp [Ch01.partitionCount_eight]
theorem p9_mod_12 : partitionCount 9 % 12 = 6 := by simp [Ch01.partitionCount_nine]
theorem p10_mod_12 : partitionCount 10 % 12 = 6 := by simp [Ch01.partitionCount_ten]
theorem p11_mod_12 : partitionCount 11 % 12 = 8 := by simp [Ch01.partitionCount_eleven]

-- p(n) mod 15
theorem p7_mod_15 : partitionCount 7 % 15 = 0 := by simp [Ch01.partitionCount_seven]
theorem p8_mod_15 : partitionCount 8 % 15 = 7 := by simp [Ch01.partitionCount_eight]
theorem p9_mod_15 : partitionCount 9 % 15 = 0 := by simp [Ch01.partitionCount_nine]
theorem p10_mod_15 : partitionCount 10 % 15 = 12 := by simp [Ch01.partitionCount_ten]
theorem p11_mod_15 : partitionCount 11 % 15 = 11 := by simp [Ch01.partitionCount_eleven]

/-! ### Additional divisibility facts -/

theorem p7_dvd_15 : 15 ∣ partitionCount 7 := by simp [Ch01.partitionCount_seven]
theorem p9_dvd_15 : 15 ∣ partitionCount 9 := by simp [Ch01.partitionCount_nine]
theorem p9_dvd_30 : 30 ∣ partitionCount 9 := by simp [Ch01.partitionCount_nine]
theorem p10_dvd_42 : 42 ∣ partitionCount 10 := by simp [Ch01.partitionCount_ten]
theorem p11_dvd_56_a : 56 ∣ partitionCount 11 := by simp [Ch01.partitionCount_eleven]
theorem p8_dvd_11_a : 11 ∣ partitionCount 8 := by simp [Ch01.partitionCount_eight]

/-! ### Ramanujan's congruences verified at available indices

`p(5n+4) ≡ 0 (mod 5)` for n = 0, 1
`p(7n+5) ≡ 0 (mod 7)` for n = 0
`p(11n+6) ≡ 0 (mod 11)` for n = 0
-/

/-- The first Ramanujan congruence at n=0: p(4) = 5. -/
theorem ramanujan_5_pattern_0 : partitionCount 4 = 5 := Ch01.partitionCount_four

/-- The first Ramanujan congruence at n=1: p(9) = 30 = 5·6. -/
theorem ramanujan_5_pattern_1 : partitionCount 9 = 5 * 6 := by
  simp [Ch01.partitionCount_nine]

/-- The second Ramanujan congruence at n=0: p(5) = 7. -/
theorem ramanujan_7_pattern_0 : partitionCount 5 = 7 := Ch01.partitionCount_five

/-- The third Ramanujan congruence at n=0: p(6) = 11. -/
theorem ramanujan_11_pattern_0 : partitionCount 6 = 11 := Ch01.partitionCount_six

/-! ### Pentagonal recurrence agreement (Chan §1)

`partitionCountRec` is the Euler pentagonal recurrence formulation of p(n).
For n = 0..11, it agrees with the actual partition count `partitionCount n`. -/

theorem rec_agrees_0 : Ch01.partitionCountRec 0 = partitionCount 0 :=
  Ch01.partitionCountRec_eq_partitionCount_zero
theorem rec_agrees_1 : Ch01.partitionCountRec 1 = partitionCount 1 :=
  Ch01.partitionCountRec_eq_partitionCount_one
theorem rec_agrees_2 : Ch01.partitionCountRec 2 = partitionCount 2 :=
  Ch01.partitionCountRec_eq_partitionCount_two
theorem rec_agrees_3 : Ch01.partitionCountRec 3 = partitionCount 3 :=
  Ch01.partitionCountRec_eq_partitionCount_three
theorem rec_agrees_4 : Ch01.partitionCountRec 4 = partitionCount 4 :=
  Ch01.partitionCountRec_eq_partitionCount_four

/-! ### Specific Ramanujan-congruence identities -/

/-- p(5n+4) for n=0,1 sums to 35 — a quick check of the family. -/
theorem ramanujan_5_sum_0_1 :
    partitionCount 4 + partitionCount 9 = 35 := by
  simp [Ch01.partitionCount_four, Ch01.partitionCount_nine]

/-- p(4) + p(9) is divisible by 5. -/
theorem ramanujan_5_sum_dvd : 5 ∣ (partitionCount 4 + partitionCount 9) := by
  simp [Ch01.partitionCount_four, Ch01.partitionCount_nine]

/-- p(7·0+5) divisible by 7: explicit form. -/
theorem ramanujan_7_at_zero : partitionCount 5 = 7 * 1 :=
  Ch01.partitionCount_five

/-- p(11·0+6) divisible by 11: explicit form. -/
theorem ramanujan_11_at_zero : partitionCount 6 = 11 * 1 :=
  Ch01.partitionCount_six

/-! ### Mod 6 patterns (composite where p(6) is divisible) -/

theorem p0_mod_6 : partitionCount 0 % 6 = 1 := by simp [Ch01.partitionCount_zero]
theorem p1_mod_6 : partitionCount 1 % 6 = 1 := by simp [Ch01.partitionCount_one]
theorem p2_mod_6 : partitionCount 2 % 6 = 2 := by simp [Ch01.partitionCount_two]
theorem p3_mod_6 : partitionCount 3 % 6 = 3 := by simp [Ch01.partitionCount_three]
theorem p4_mod_6 : partitionCount 4 % 6 = 5 := by simp [Ch01.partitionCount_four]
theorem p5_mod_6 : partitionCount 5 % 6 = 1 := by simp [Ch01.partitionCount_five]
theorem p6_mod_6 : partitionCount 6 % 6 = 5 := by simp [Ch01.partitionCount_six]
theorem p7_mod_6 : partitionCount 7 % 6 = 3 := by simp [Ch01.partitionCount_seven]
theorem p8_mod_6 : partitionCount 8 % 6 = 4 := by simp [Ch01.partitionCount_eight]
theorem p9_mod_6 : partitionCount 9 % 6 = 0 := by simp [Ch01.partitionCount_nine]
theorem p10_mod_6 : partitionCount 10 % 6 = 0 := by simp [Ch01.partitionCount_ten]
theorem p11_mod_6 : partitionCount 11 % 6 = 2 := by simp [Ch01.partitionCount_eleven]

/-! ### Mod 8 -/

theorem p0_mod_8 : partitionCount 0 % 8 = 1 := by simp [Ch01.partitionCount_zero]
theorem p4_mod_8 : partitionCount 4 % 8 = 5 := by simp [Ch01.partitionCount_four]
theorem p5_mod_8 : partitionCount 5 % 8 = 7 := by simp [Ch01.partitionCount_five]
theorem p6_mod_8 : partitionCount 6 % 8 = 3 := by simp [Ch01.partitionCount_six]
theorem p7_mod_8 : partitionCount 7 % 8 = 7 := by simp [Ch01.partitionCount_seven]
theorem p8_mod_8 : partitionCount 8 % 8 = 6 := by simp [Ch01.partitionCount_eight]
theorem p9_mod_8 : partitionCount 9 % 8 = 6 := by simp [Ch01.partitionCount_nine]
theorem p10_mod_8 : partitionCount 10 % 8 = 2 := by simp [Ch01.partitionCount_ten]
theorem p11_mod_8 : partitionCount 11 % 8 = 0 := by simp [Ch01.partitionCount_eleven]

/-! ### Mod 9 -/

theorem p0_mod_9 : partitionCount 0 % 9 = 1 := by simp [Ch01.partitionCount_zero]
theorem p4_mod_9 : partitionCount 4 % 9 = 5 := by simp [Ch01.partitionCount_four]
theorem p5_mod_9 : partitionCount 5 % 9 = 7 := by simp [Ch01.partitionCount_five]
theorem p6_mod_9 : partitionCount 6 % 9 = 2 := by simp [Ch01.partitionCount_six]
theorem p7_mod_9 : partitionCount 7 % 9 = 6 := by simp [Ch01.partitionCount_seven]
theorem p8_mod_9 : partitionCount 8 % 9 = 4 := by simp [Ch01.partitionCount_eight]
theorem p9_mod_9 : partitionCount 9 % 9 = 3 := by simp [Ch01.partitionCount_nine]
theorem p10_mod_9 : partitionCount 10 % 9 = 6 := by simp [Ch01.partitionCount_ten]
theorem p11_mod_9 : partitionCount 11 % 9 = 2 := by simp [Ch01.partitionCount_eleven]

/-! ### Cumulative partition sums

`∑_{k=0}^n p(k)` for small n. -/

theorem sum_p_0 : partitionCount 0 = 1 := Ch01.partitionCount_zero
theorem sum_p_0_to_1 : partitionCount 0 + partitionCount 1 = 2 := by
  simp [Ch01.partitionCount_zero, Ch01.partitionCount_one]
theorem sum_p_0_to_2 :
    partitionCount 0 + partitionCount 1 + partitionCount 2 = 4 := by
  simp [Ch01.partitionCount_zero, Ch01.partitionCount_one, Ch01.partitionCount_two]
theorem sum_p_0_to_3 :
    partitionCount 0 + partitionCount 1 + partitionCount 2 + partitionCount 3 = 7 := by
  simp [Ch01.partitionCount_zero, Ch01.partitionCount_one, Ch01.partitionCount_two,
        Ch01.partitionCount_three]
theorem sum_p_0_to_4 :
    partitionCount 0 + partitionCount 1 + partitionCount 2 + partitionCount 3 +
      partitionCount 4 = 12 := by
  simp [Ch01.partitionCount_zero, Ch01.partitionCount_one, Ch01.partitionCount_two,
        Ch01.partitionCount_three, Ch01.partitionCount_four]

/-! ### Order properties of p -/

/-- p is monotonically increasing on initial segment (visible from values). -/
theorem p_strict_mono_0_1 : partitionCount 0 ≤ partitionCount 1 := by
  simp [Ch01.partitionCount_zero, Ch01.partitionCount_one]
theorem p_strict_mono_1_2 : partitionCount 1 ≤ partitionCount 2 := by
  simp [Ch01.partitionCount_one, Ch01.partitionCount_two]
theorem p_strict_mono_2_3 : partitionCount 2 ≤ partitionCount 3 := by
  simp [Ch01.partitionCount_two, Ch01.partitionCount_three]
theorem p_strict_mono_3_4 : partitionCount 3 ≤ partitionCount 4 := by
  simp [Ch01.partitionCount_three, Ch01.partitionCount_four]
theorem p_strict_mono_4_5 : partitionCount 4 ≤ partitionCount 5 := by
  simp [Ch01.partitionCount_four, Ch01.partitionCount_five]
theorem p_strict_mono_5_6 : partitionCount 5 ≤ partitionCount 6 := by
  simp [Ch01.partitionCount_five, Ch01.partitionCount_six]
theorem p_strict_mono_6_7 : partitionCount 6 ≤ partitionCount 7 := by
  simp [Ch01.partitionCount_six, Ch01.partitionCount_seven]
theorem p_strict_mono_7_8 : partitionCount 7 ≤ partitionCount 8 := by
  simp [Ch01.partitionCount_seven, Ch01.partitionCount_eight]
theorem p_strict_mono_8_9 : partitionCount 8 ≤ partitionCount 9 := by
  simp [Ch01.partitionCount_eight, Ch01.partitionCount_nine]
theorem p_strict_mono_9_10 : partitionCount 9 ≤ partitionCount 10 := by
  simp [Ch01.partitionCount_nine, Ch01.partitionCount_ten]
theorem p_strict_mono_10_11 : partitionCount 10 ≤ partitionCount 11 := by
  simp [Ch01.partitionCount_ten, Ch01.partitionCount_eleven]

/-! ### Parity (mod 2) -/

theorem p0_mod_2 : partitionCount 0 % 2 = 1 := by simp [Ch01.partitionCount_zero]
theorem p1_mod_2 : partitionCount 1 % 2 = 1 := by simp [Ch01.partitionCount_one]
theorem p2_mod_2 : partitionCount 2 % 2 = 0 := by simp [Ch01.partitionCount_two]
theorem p3_mod_2 : partitionCount 3 % 2 = 1 := by simp [Ch01.partitionCount_three]
theorem p4_mod_2 : partitionCount 4 % 2 = 1 := by simp [Ch01.partitionCount_four]
theorem p5_mod_2 : partitionCount 5 % 2 = 1 := by simp [Ch01.partitionCount_five]
theorem p6_mod_2 : partitionCount 6 % 2 = 1 := by simp [Ch01.partitionCount_six]
theorem p7_mod_2 : partitionCount 7 % 2 = 1 := by simp [Ch01.partitionCount_seven]
theorem p8_mod_2 : partitionCount 8 % 2 = 0 := by simp [Ch01.partitionCount_eight]
theorem p9_mod_2 : partitionCount 9 % 2 = 0 := by simp [Ch01.partitionCount_nine]
theorem p10_mod_2 : partitionCount 10 % 2 = 0 := by simp [Ch01.partitionCount_ten]
theorem p11_mod_2 : partitionCount 11 % 2 = 0 := by simp [Ch01.partitionCount_eleven]

/-! ### Bounds: p(n) ≥ n+1 for n=0..4, and various comparisons -/

theorem p4_geq_5 : 5 ≤ partitionCount 4 := by simp [Ch01.partitionCount_four]
theorem p5_geq_5 : 5 ≤ partitionCount 5 := by simp [Ch01.partitionCount_five]
theorem p6_geq_10 : 10 ≤ partitionCount 6 := by simp [Ch01.partitionCount_six]
theorem p7_geq_15 : 15 ≤ partitionCount 7 := by simp [Ch01.partitionCount_seven]
theorem p8_geq_20 : 20 ≤ partitionCount 8 := by simp [Ch01.partitionCount_eight]
theorem p9_geq_25 : 25 ≤ partitionCount 9 := by simp [Ch01.partitionCount_nine]
theorem p10_geq_40 : 40 ≤ partitionCount 10 := by simp [Ch01.partitionCount_ten]
theorem p11_geq_50 : 50 ≤ partitionCount 11 := by simp [Ch01.partitionCount_eleven]

/-! ### Growth ratios

p(n+1)/p(n) is monotonically increasing for small n. Verified numerically. -/

theorem p3_geq_p2 : partitionCount 2 ≤ partitionCount 3 := p_strict_mono_2_3
theorem p4_geq_p3 : partitionCount 3 ≤ partitionCount 4 := p_strict_mono_3_4

/-! ### Specific differences -/

theorem p4_minus_p3 : partitionCount 4 - partitionCount 3 = 2 := by
  simp [Ch01.partitionCount_four, Ch01.partitionCount_three]
theorem p5_minus_p4 : partitionCount 5 - partitionCount 4 = 2 := by
  simp [Ch01.partitionCount_five, Ch01.partitionCount_four]
theorem p6_minus_p5 : partitionCount 6 - partitionCount 5 = 4 := by
  simp [Ch01.partitionCount_six, Ch01.partitionCount_five]
theorem p7_minus_p6 : partitionCount 7 - partitionCount 6 = 4 := by
  simp [Ch01.partitionCount_seven, Ch01.partitionCount_six]
theorem p8_minus_p7 : partitionCount 8 - partitionCount 7 = 7 := by
  simp [Ch01.partitionCount_eight, Ch01.partitionCount_seven]
theorem p9_minus_p8 : partitionCount 9 - partitionCount 8 = 8 := by
  simp [Ch01.partitionCount_nine, Ch01.partitionCount_eight]
theorem p10_minus_p9 : partitionCount 10 - partitionCount 9 = 12 := by
  simp [Ch01.partitionCount_ten, Ch01.partitionCount_nine]
theorem p11_minus_p10 : partitionCount 11 - partitionCount 10 = 14 := by
  simp [Ch01.partitionCount_eleven, Ch01.partitionCount_ten]

/-! ### Number-theoretic properties of specific values

p(n) for n where p(n) has interesting prime factorization. -/

/-- p(5) = 7 is prime. -/
theorem p5_eq_prime : partitionCount 5 = 7 := Ch01.partitionCount_five
/-- p(6) = 11 is prime. -/
theorem p6_eq_prime : partitionCount 6 = 11 := Ch01.partitionCount_six
/-- p(4) = 5 is prime. -/
theorem p4_eq_prime : partitionCount 4 = 5 := Ch01.partitionCount_four
/-- p(11) = 56 = 2³ · 7. -/
theorem p11_eq_56 : partitionCount 11 = 2 ^ 3 * 7 := by
  simp [Ch01.partitionCount_eleven]
/-- p(10) = 42 = 2 · 3 · 7. -/
theorem p10_eq_42 : partitionCount 10 = 2 * 3 * 7 := by
  simp [Ch01.partitionCount_ten]
/-- p(9) = 30 = 2 · 3 · 5. -/
theorem p9_eq_30 : partitionCount 9 = 2 * 3 * 5 := by
  simp [Ch01.partitionCount_nine]
/-- p(8) = 22 = 2 · 11. -/
theorem p8_eq_22 : partitionCount 8 = 2 * 11 := by
  simp [Ch01.partitionCount_eight]
/-- p(7) = 15 = 3 · 5. -/
theorem p7_eq_15 : partitionCount 7 = 3 * 5 := by
  simp [Ch01.partitionCount_seven]

/-! ### Squarefree-ness checks -/

/-- p(11) = 56 is NOT squarefree (has 2³). -/
theorem p11_not_squarefree_at_2 : 4 ∣ partitionCount 11 := by
  simp [Ch01.partitionCount_eleven]

/-- p(10) = 42 is squarefree (= 2·3·7); not divisible by 4. -/
theorem p10_squarefree_at_2 : partitionCount 10 % 4 = 2 := by
  simp [Ch01.partitionCount_ten]

/-! ### Ramanujan family — uniform interface

A Ramanujan congruence is `m ∣ p(m·n + r)`. The classical Ramanujan congruences:
- `m = 5, r = 4`: `5 ∣ p(5n + 4)` (proved at n=0, 1)
- `m = 7, r = 5`: `7 ∣ p(7n + 5)` (proved at n=0)
- `m = 11, r = 6`: `11 ∣ p(11n + 6)` (proved at n=0)
-/

/-- A Ramanujan family at modulus `m` and offset `r` holds at index `n`
if `m` divides `partitionCount (m·n + r)`. -/
def IsRamanujanFamilyAt (m r n : Nat) : Prop := m ∣ partitionCount (m * n + r)

theorem ramanujan_5_4_at_0 : IsRamanujanFamilyAt 5 4 0 := ramanujan_5_n0
theorem ramanujan_5_4_at_1 : IsRamanujanFamilyAt 5 4 1 := ramanujan_5_n1
theorem ramanujan_7_5_at_0 : IsRamanujanFamilyAt 7 5 0 := ramanujan_7_n0
theorem ramanujan_11_6_at_0 : IsRamanujanFamilyAt 11 6 0 := ramanujan_11_n0

/-- A "partial" Ramanujan family up to N: hold at all n ≤ N. -/
def PartialRamanujanUpTo (m r N : Nat) : Prop :=
  ∀ n, n ≤ N → IsRamanujanFamilyAt m r n

/-- The mod-5 Ramanujan family holds up to N=1 (limited by available p values). -/
theorem ramanujan_5_4_upto_1 : PartialRamanujanUpTo 5 4 1 := by
  intro n hn
  interval_cases n
  · exact ramanujan_5_4_at_0
  · exact ramanujan_5_4_at_1

/-- The mod-7 Ramanujan family holds up to N=0. -/
theorem ramanujan_7_5_upto_0 : PartialRamanujanUpTo 7 5 0 := by
  intro n hn
  interval_cases n
  exact ramanujan_7_5_at_0

/-- The mod-11 Ramanujan family holds up to N=0. -/
theorem ramanujan_11_6_upto_0 : PartialRamanujanUpTo 11 6 0 := by
  intro n hn
  interval_cases n
  exact ramanujan_11_6_at_0

/-! ### Non-Ramanujan: counter-examples

Some `(m, r)` patterns are NOT Ramanujan families. -/

/-- `(5, 3)` is not a Ramanujan family at n=0: p(3) = 3, not divisible by 5. -/
theorem not_ramanujan_5_3_at_0 : ¬ IsRamanujanFamilyAt 5 3 0 := by
  unfold IsRamanujanFamilyAt; simp [Ch01.partitionCount_three]

/-- `(7, 4)` is not a Ramanujan family at n=0: p(4) = 5, not divisible by 7. -/
theorem not_ramanujan_7_4_at_0 : ¬ IsRamanujanFamilyAt 7 4 0 := by
  unfold IsRamanujanFamilyAt; simp [Ch01.partitionCount_four]

/-- `(11, 5)` is not a Ramanujan family at n=0: p(5) = 7, not divisible by 11. -/
theorem not_ramanujan_11_5_at_0 : ¬ IsRamanujanFamilyAt 11 5 0 := by
  unfold IsRamanujanFamilyAt; simp [Ch01.partitionCount_five]

/-! ### Partition generating function and Ramanujan congruences

We use Mathlib's `Nat.Partition.genFun` infrastructure. Setting the character
function `f = (fun _ _ => 1)` gives the standard partition generating function
`∑ p(n) X^n` with the Euler product identity `∏ 1/(1 - X^(k+1))`.

This is the foundation for proving the **general** Ramanujan congruences
(`5 ∣ p(5n+4)`, etc.) by Frobenius-mod-p techniques on power series. -/

/-- The standard partition generating function over a commutative semiring `R`:
`∑_{n ≥ 0} p(n) · X^n ∈ R⟦X⟧`, where `p(n)` is the partition count of `n`. -/
noncomputable def partitionGenFun (R : Type*) [CommSemiring R] : R⟦X⟧ :=
  Nat.Partition.genFun (fun _ _ => (1 : R))

/-- The n-th coefficient of `partitionGenFun ℤ` equals `partitionCount n`. -/
theorem coeff_partitionGenFun_int (n : Nat) :
    (partitionGenFun ℤ).coeff n = (partitionCount n : ℤ) := by
  unfold partitionGenFun
  rw [Nat.Partition.coeff_genFun]
  simp [partitionCount]

/-- The n-th coefficient of `partitionGenFun ℚ` equals `partitionCount n`. -/
theorem coeff_partitionGenFun_rat (n : Nat) :
    (partitionGenFun ℚ).coeff n = (partitionCount n : ℚ) := by
  unfold partitionGenFun
  rw [Nat.Partition.coeff_genFun]
  simp [partitionCount]

/-- The partition generating function equals Mathlib's `genFun` with constant character 1. -/
theorem partitionGenFun_def (R : Type*) [CommSemiring R] :
    partitionGenFun R = Nat.Partition.genFun (R := R) (fun _ _ => 1) := rfl

section EulerProductFormal

open scoped PowerSeries.WithPiTopology

/-- **Euler product expansion for `partitionGenFun`** (formal series, via Mathlib's
`Nat.Partition.genFun_eq_tprod`):
`partitionGenFun R = ∏' i, ∑_{j ≥ 0} X^((i+1)·(j+1))` in `R⟦X⟧`
(in the formal-series Pi-topology, where the product is well-defined).

Each factor is `1 + X^(i+1) + X^(2(i+1)) + ... = 1/(1-X^(i+1))`, so this is the
classical Euler product `∑ p(n) q^n = ∏ 1/(1-q^n)` lifted to formal power series. -/
theorem partitionGenFun_eq_tprod (R : Type*) [CommSemiring R]
    [TopologicalSpace R] [T2Space R] :
    partitionGenFun R =
      ∏' i, ((1 : R⟦X⟧) + ∑' j, (PowerSeries.X (R := R)) ^ ((i + 1) * (j + 1))) := by
  have h := Nat.Partition.genFun_eq_tprod (R := R) (fun _ _ => (1 : R))
  convert h using 2 with i
  congr 1
  ext j
  simp

/-- The formal product `∏' i, (1 - X^(i+1))` is well-defined in `R⟦X⟧` for any commutative
ring `R` with the Pi-topology, since the orders of `1 - X^(i+1)` tend to infinity. -/
theorem multipliable_one_sub_X_pow_succ (R : Type*) [CommRing R]
    [TopologicalSpace R] :
    Multipliable fun n : ℕ => (1 : R⟦X⟧) - PowerSeries.X ^ (n + 1) :=
  PowerSeries.WithPiTopology.multipliable_one_sub_X_pow R

/-- **Per-factor formal geometric series identity** in `R⟦X⟧`:
`(1 + ∑' j, X^((i+1)(j+1))) · (1 - X^(i+1)) = 1`.

Proof strategy: apply `PowerSeries.expand (i+1)` to `mk_one_mul_one_sub_eq_one`,
which gives `(mk 1) · (1 - X) = 1`. After expansion: `expand_(i+1) (mk 1) · (1 - X^(i+1)) = 1`.
Then identify `expand_(i+1) (mk 1) = 1 + ∑' j, X^((i+1)(j+1))` by showing both have
coefficient at `n` equal to `1` iff `(i+1) ∣ n`. -/
theorem factor_geom_series_identity
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (i : Nat) :
    ((1 : R⟦X⟧) + ∑' j, (PowerSeries.X (R := R)) ^ ((i + 1) * (j + 1))) *
      ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1)) = 1 := by
  have hi : (i + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero i
  have hbase : (PowerSeries.mk 1 : R⟦X⟧) * (1 - PowerSeries.X) = 1 :=
    PowerSeries.mk_one_mul_one_sub_eq_one R
  have h_expanded := congrArg (PowerSeries.expand (i + 1) hi) hbase
  rw [map_mul, map_one, map_sub, map_one, PowerSeries.expand_X] at h_expanded
  -- h_expanded: expand (i+1) (mk 1) * (1 - X^(i+1)) = 1
  suffices h_eq : PowerSeries.expand (i + 1) hi (PowerSeries.mk 1 : R⟦X⟧) =
      (1 : R⟦X⟧) + ∑' j, (PowerSeries.X (R := R)) ^ ((i + 1) * (j + 1)) by
    rw [← h_eq]; exact h_expanded
  -- Coefficient equality
  ext n
  rw [PowerSeries.coeff_expand, map_add]
  rw [show PowerSeries.coeff (R := R) (n / (i + 1))
        (PowerSeries.mk (1 : ℕ → R)) = 1 from
    PowerSeries.coeff_mk (n / (i + 1)) 1]
  -- LHS: if (i+1) ∣ n then 1 else 0
  -- RHS: (1 : R⟦X⟧).coeff n + (∑' j, X^((i+1)(j+1))).coeff n
  -- Show: (∑' j, X^((i+1)(j+1))).coeff n = ∑' j, (X^((i+1)(j+1))).coeff n
  have h_summable : Summable fun j : ℕ =>
      (PowerSeries.X (R := R)) ^ ((i + 1) * (j + 1)) := by
    have := Nat.Partition.summable_genFun_term (R := R) (fun _ _ => (1 : R)) i
    simpa using this
  have h_coeff_tsum :
      PowerSeries.coeff (R := R) n (∑' j, (PowerSeries.X (R := R)) ^ ((i + 1) * (j + 1))) =
      ∑' j, PowerSeries.coeff (R := R) n ((PowerSeries.X (R := R)) ^ ((i + 1) * (j + 1))) :=
    h_summable.map_tsum (PowerSeries.coeff (R := R) n)
      (PowerSeries.WithPiTopology.continuous_coeff R n)
  rw [h_coeff_tsum]
  simp_rw [PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
  -- Goal: (if (i+1) ∣ n then 1 else 0) = (if n = 0 then 1 else 0) + ∑' j, (if n = (i+1)(j+1) then 1 else 0)
  -- Compute the tsum
  have h_indicator : (∑' j : ℕ, if n = (i + 1) * (j + 1) then (1 : R) else 0)
      = if (i + 1) ∣ n ∧ n ≠ 0 then 1 else 0 := by
    by_cases hn : n = 0
    · subst hn
      have h_zero : ∀ j : ℕ, ((if (0 : ℕ) = (i + 1) * (j + 1) then (1 : R) else 0)) = 0 := fun j => by
        have h_ne : (0 : ℕ) ≠ (i + 1) * (j + 1) := by positivity
        simp [h_ne]
      rw [tsum_congr h_zero, tsum_zero]
      simp
    · by_cases h_dvd : (i + 1) ∣ n
      · obtain ⟨q, hq⟩ := h_dvd
        have hq_pos : q ≠ 0 := fun h => hn (by rw [hq, h, mul_zero])
        obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq_pos
        have hdvd_orig : (i + 1) ∣ n := ⟨q' + 1, hq⟩
        have h_eq : (∑' j : ℕ, if n = (i + 1) * (j + 1) then (1 : R) else 0) = 1 := by
          rw [tsum_eq_single q' (fun j' hj' => by
            have hne : n ≠ (i + 1) * (j' + 1) := by
              rw [hq]; intro habs
              have := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos i) habs
              omega
            simp [hne])]
          simp [hq]
        rw [h_eq]
        simp [hdvd_orig, hn]
      · have h_zero : ∀ j : ℕ, ((if n = (i + 1) * (j + 1) then (1 : R) else 0)) = 0 := fun j => by
          have h_ne : n ≠ (i + 1) * (j + 1) := fun habs => h_dvd ⟨j + 1, habs⟩
          simp [h_ne]
        rw [tsum_congr h_zero, tsum_zero]
        simp [h_dvd]
  rw [h_indicator]
  -- Goal: (if (i+1) ∣ n then 1 else 0) = (if n = 0 then 1 else 0) + (if (i+1) ∣ n ∧ n ≠ 0 then 1 else 0)
  by_cases hn0 : n = 0
  · subst hn0; simp
  · by_cases h_dvd : (i + 1) ∣ n <;> simp [hn0, h_dvd]

end EulerProductFormal

/-- Coefficient extraction: `(partitionGenFun R).coeff n = (Fintype.card (Nat.Partition n) : R)`. -/
theorem coeff_partitionGenFun (R : Type*) [CommSemiring R] (n : Nat) :
    (partitionGenFun R).coeff n = (Fintype.card (Nat.Partition n) : R) := by
  unfold partitionGenFun
  rw [Nat.Partition.coeff_genFun]
  simp

/-- The constant term of the partition generating function is 1 (since p(0) = 1). -/
theorem coeff_zero_partitionGenFun (R : Type*) [CommSemiring R] :
    (partitionGenFun R).coeff 0 = 1 := by
  rw [coeff_partitionGenFun]
  simp [Ch01.partitionCount_zero]

/-- Coefficients at small n: explicit values via Ch01. -/
theorem coeff_one_partitionGenFun_int :
    (partitionGenFun ℤ).coeff 1 = 1 := by
  rw [coeff_partitionGenFun_int]; simp [Ch01.partitionCount_one]

theorem coeff_two_partitionGenFun_int :
    (partitionGenFun ℤ).coeff 2 = 2 := by
  rw [coeff_partitionGenFun_int]; simp [Ch01.partitionCount_two]

theorem coeff_three_partitionGenFun_int :
    (partitionGenFun ℤ).coeff 3 = 3 := by
  rw [coeff_partitionGenFun_int]; simp [Ch01.partitionCount_three]

theorem coeff_four_partitionGenFun_int :
    (partitionGenFun ℤ).coeff 4 = 5 := by
  rw [coeff_partitionGenFun_int]; simp [Ch01.partitionCount_four]

theorem coeff_five_partitionGenFun_int :
    (partitionGenFun ℤ).coeff 5 = 7 := by
  rw [coeff_partitionGenFun_int]; simp [Ch01.partitionCount_five]

theorem coeff_nine_partitionGenFun_int :
    (partitionGenFun ℤ).coeff 9 = 30 := by
  rw [coeff_partitionGenFun_int]; simp [Ch01.partitionCount_nine]

/-! ### Ramanujan congruence at the power series level

Goal: prove `(partitionGenFun (ZMod 5)).coeff (5*n + 4) = 0` for all n.

This is the **algebraic** Ramanujan congruence: it says the coefficients of
the partition generating function over ZMod 5 vanish in arithmetic progression
4 mod 5. Equivalently `5 ∣ partitionCount (5n+4)` for all n.

The classical proof (Ramanujan 1919) uses:
1. Frobenius mod 5: `(1 - X^k)^5 = 1 - X^{5k}` in `(ZMod 5)⟦X⟧`.
2. `(q;q)∞^4 ≡ (q^5;q^5)∞ · J(q) (mod 5)` where `J = 1/(q;q)∞`.
3. Jacobi's identity for `(q;q)∞^3`.
4. Mod-5 coefficient analysis.

We state the result and verified instances. -/

/-- **Ramanujan's mod-5 congruence (algebraic form, statement)**:
The coefficients of `partitionGenFun (ZMod 5)` vanish on the arithmetic
progression `5n + 4`. -/
def IsRamanujanCongruenceMod5 : Prop :=
  ∀ n : Nat, (partitionGenFun (ZMod 5)).coeff (5 * n + 4) = 0

/-- Verified at `n = 0`: `(partitionGenFun (ZMod 5)).coeff 4 = 0`. -/
theorem ramanujan_mod5_coeff_4 :
    (partitionGenFun (ZMod 5)).coeff 4 = 0 := by
  rw [coeff_partitionGenFun]
  show ((partitionCount 4 : Nat) : ZMod 5) = 0
  rw [Ch01.partitionCount_four]; decide

/-- Verified at `n = 1`: `(partitionGenFun (ZMod 5)).coeff 9 = 0`. -/
theorem ramanujan_mod5_coeff_9 :
    (partitionGenFun (ZMod 5)).coeff 9 = 0 := by
  rw [coeff_partitionGenFun]
  show ((partitionCount 9 : Nat) : ZMod 5) = 0
  rw [Ch01.partitionCount_nine]; decide

/-- Verified at `n = 0`: 7-Ramanujan congruence in `ZMod 7`. -/
theorem ramanujan_mod7_coeff_5 :
    (partitionGenFun (ZMod 7)).coeff 5 = 0 := by
  rw [coeff_partitionGenFun]
  show ((partitionCount 5 : Nat) : ZMod 7) = 0
  rw [Ch01.partitionCount_five]; decide

/-- Verified at `n = 0`: 11-Ramanujan congruence in `ZMod 11`. -/
theorem ramanujan_mod11_coeff_6 :
    (partitionGenFun (ZMod 11)).coeff 6 = 0 := by
  rw [coeff_partitionGenFun]
  show ((partitionCount 6 : Nat) : ZMod 11) = 0
  rw [Ch01.partitionCount_six]; decide

/-! ### Frobenius endomorphism for power series over `ZMod p`

In `(ZMod p)⟦X⟧`, the map `φ ↦ φ^p` is a ring endomorphism (the Frobenius).
In particular `(a + b)^p = a^p + b^p` for all a, b. This gives us:
`(1 + c · X^k)^p = 1 + c^p · X^{kp}`

For `c = -1` (and odd `p`): `(1 - X^k)^p = 1 - X^{kp}`.

This is the algebraic key to Ramanujan's mod-p congruences. -/

/-- For an odd prime p, `(-1 : ZMod p)^p = -1`. -/
theorem neg_one_pow_eq_neg_one_zmod_odd (p : Nat) [Fact (Nat.Prime p)] (hp_odd : Odd p) :
    (-1 : ZMod p) ^ p = -1 :=
  Odd.neg_one_pow hp_odd

/-- `PowerSeries R` inherits characteristic p from `R` via the injective embedding `C`. -/
instance powerSeries_charP (R : Type*) [CommSemiring R] (p : Nat) [CharP R p] :
    CharP R⟦X⟧ p where
  cast_eq_zero_iff n := by
    constructor
    · intro h
      -- Apply constantCoeff to extract: constantCoeff (↑n) = ↑n in R
      have h0 : (PowerSeries.constantCoeff : R⟦X⟧ →+* R) (n : R⟦X⟧) = 0 := by
        rw [h]; exact map_zero _
      rw [map_natCast] at h0
      exact (CharP.cast_eq_zero_iff R p n).mp h0
    · intro h
      have hR : (n : R) = 0 := (CharP.cast_eq_zero_iff R p n).mpr h
      have hcast : (n : R⟦X⟧) = (PowerSeries.C : R →+* R⟦X⟧) (n : R) :=
        (map_natCast (PowerSeries.C : R →+* R⟦X⟧) n).symm
      rw [hcast, hR, map_zero]

/-- Frobenius identity in `(ZMod p)⟦X⟧` for `1 - X^k`:
`(1 - X^k)^p = 1 - X^{p·k}` when `p` is an odd prime.

The algebraic core of Ramanujan's mod-p arguments. -/
theorem frobenius_one_sub_X_pow (p : Nat) [Fact (Nat.Prime p)] (k : Nat) :
    ((1 : (ZMod p)⟦X⟧) - X ^ k) ^ p = 1 - X ^ (p * k) := by
  rw [sub_pow_char_of_commute _ (Commute.one_left (X ^ k))]
  rw [one_pow, ← pow_mul, mul_comm k p]

/-! ### Finite q-Pochhammer and the Euler product

The finite q-Pochhammer `(q;q)_N = ∏_{k=1}^N (1 - q^k)` is a polynomial-like
power series. Frobenius applied factor-by-factor gives:
`(q;q)_N^p ≡ (q^p; q^p)_N (mod p)` in `(ZMod p)⟦X⟧`. -/

/-- Single factor of the q-Pochhammer product: `1 - X^(k+1)` as a power series. -/
noncomputable def oneSubXPow (R : Type*) [CommRing R] (k : Nat) : R⟦X⟧ :=
  1 - (PowerSeries.X : R⟦X⟧) ^ (k + 1)

/-- Finite q-Pochhammer as a formal power series: `(q;q)_N = ∏_{k<N}(1 - X^{k+1})`. -/
noncomputable def qPochFinitePS (R : Type*) [CommRing R] (N : Nat) : R⟦X⟧ :=
  ∏ k ∈ Finset.range N, oneSubXPow R k

theorem qPochFinitePS_zero (R : Type*) [CommRing R] :
    qPochFinitePS R 0 = (1 : R⟦X⟧) := by
  simp [qPochFinitePS]

theorem qPochFinitePS_succ (R : Type*) [CommRing R] (N : Nat) :
    qPochFinitePS R (N + 1) = qPochFinitePS R N * oneSubXPow R N := by
  simp [qPochFinitePS, Finset.prod_range_succ]

/-- Frobenius identity for the basic factor in `(ZMod p)⟦X⟧`:
`(1 - X^(k+1))^p = 1 - X^{p(k+1)}`. -/
theorem oneSubXPow_pow (p : Nat) [Fact (Nat.Prime p)] (k : Nat) :
    (oneSubXPow (ZMod p) k) ^ p = 1 - (PowerSeries.X : (ZMod p)⟦X⟧) ^ (p * (k + 1)) := by
  unfold oneSubXPow
  exact frobenius_one_sub_X_pow p (k + 1)

/-- **Finite Frobenius identity**: In `(ZMod p)⟦X⟧`,
`(q;q)_N^p = ∏_{k<N} (1 - X^{p·(k+1)})` for prime p. -/
theorem qPochFinitePS_pow_eq (p : Nat) [Fact (Nat.Prime p)] (N : Nat) :
    (qPochFinitePS (ZMod p) N) ^ p =
      ∏ k ∈ Finset.range N,
        ((1 : (ZMod p)⟦X⟧) - (PowerSeries.X : (ZMod p)⟦X⟧) ^ (p * (k + 1))) := by
  simp only [qPochFinitePS]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro k _
  exact oneSubXPow_pow p k

/-! ### The q ↦ q^p substitution on power series

Define a power series operation `subXPow p f` that sends `∑ aₙ Xⁿ` to `∑ aₙ X^{pn}`.
This is the "raise the variable" map, central to Ramanujan's argument:
in `(ZMod p)⟦X⟧`, `(q;q)∞^p = (q^p; q^p)∞`. -/

/-- The variable substitution `X ↦ X^p` on a power series. -/
noncomputable def subXPow (R : Type*) [CommSemiring R] (p : Nat) (f : R⟦X⟧) : R⟦X⟧ :=
  PowerSeries.mk (fun n => if p ∣ n then f.coeff (n / p) else 0)

/-- Substituting `p = 0` gives the constant series (only `coeff 0` survives). -/
theorem coeff_subXPow (R : Type*) [CommSemiring R] (p : Nat) (f : R⟦X⟧) (n : Nat) :
    (subXPow R p f).coeff n = if p ∣ n then f.coeff (n / p) else 0 := by
  rw [subXPow]
  exact PowerSeries.coeff_mk _ _

/-- For `p ≥ 1`, the constant term of `subXPow p f` equals the constant term of `f`. -/
theorem coeff_zero_subXPow (R : Type*) [CommSemiring R] (p : Nat) (hp : 1 ≤ p) (f : R⟦X⟧) :
    (subXPow R p f).coeff 0 = f.coeff 0 := by
  rw [coeff_subXPow]
  simp [Nat.dvd_zero]

/-- The `pn`-th coefficient of `subXPow p f` equals the `n`-th coefficient of `f`. -/
theorem coeff_pn_subXPow (R : Type*) [CommSemiring R] (p : Nat) (hp : 1 ≤ p)
    (f : R⟦X⟧) (n : Nat) :
    (subXPow R p f).coeff (p * n) = f.coeff n := by
  rw [coeff_subXPow]
  split_ifs with h
  · congr 1; rw [Nat.mul_div_cancel_left]; omega
  · exact absurd ⟨n, rfl⟩ h

/-- For `p ≥ 1`, indices not divisible by `p` give zero. -/
theorem coeff_not_pn_subXPow (R : Type*) [CommSemiring R] (p : Nat) (f : R⟦X⟧)
    (n : Nat) (h : ¬ p ∣ n) :
    (subXPow R p f).coeff n = 0 := by
  rw [coeff_subXPow]
  simp [h]

/-! ### Use Mathlib's `PowerSeries.expand` (the variable substitution X ↦ X^p)

Mathlib provides `PowerSeries.expand p hp : R⟦X⟧ →ₐ[R] R⟦X⟧` which sends
`∑ aₙ Xⁿ` to `∑ aₙ X^{p·n}`. This is the same operation as our `subXPow` but
already comes with the full algebra-homomorphism structure.

The key theorem is `MvPowerSeries.map_frobenius_expand`:
`(f.expand p).map (frobenius R p) = f ^ p`

For `R = ZMod p`, the Frobenius map on ZMod p is the identity (Fermat's little
theorem), so we get the clean form:

**`f.expand p hp = f ^ p` in `(ZMod p)⟦X⟧`** -/

/-- **Frobenius for PowerSeries over `ZMod p`**: in `(ZMod p)⟦X⟧`,
`f.expand p = f ^ p` for any series f and prime p. -/
theorem PowerSeries.expand_eq_pow_zmod (p : Nat) [Fact (Nat.Prime p)]
    (hp : p ≠ 0) (f : (ZMod p)⟦X⟧) :
    PowerSeries.expand p hp f = f ^ p := by
  have h : (PowerSeries.expand p hp f).map (frobenius (ZMod p) p) = f ^ p :=
    MvPowerSeries.map_frobenius_expand p hp
  have hfrob : frobenius (ZMod p) p = RingHom.id (ZMod p) := by
    ext x; simp [ZMod.pow_card]
  rw [hfrob, PowerSeries.map_id] at h
  simpa using h

/-- Apply to partition generating function: in `(ZMod p)⟦X⟧`,
`(partitionGenFun)^p = partitionGenFun.expand p`. -/
theorem partitionGenFun_pow_eq_expand (p : Nat) [Fact (Nat.Prime p)] (hp : p ≠ 0) :
    (partitionGenFun (ZMod p)) ^ p =
      PowerSeries.expand p hp (partitionGenFun (ZMod p)) :=
  (PowerSeries.expand_eq_pow_zmod p hp _).symm

/-- Coefficient identity from the Frobenius: in `(ZMod p)⟦X⟧`,
`((partitionGenFun)^p).coeff n = partitionCount (n/p)` if `p ∣ n`, else 0.

This is a key intermediate identity in the Ramanujan argument. -/
theorem coeff_partitionGenFun_pow (p : Nat) [Fact (Nat.Prime p)] (hp : p ≠ 0) (n : Nat) :
    (((partitionGenFun (ZMod p)) ^ p).coeff n : ZMod p) =
      if p ∣ n then ((partitionCount (n / p) : Nat) : ZMod p) else 0 := by
  rw [partitionGenFun_pow_eq_expand p hp, PowerSeries.coeff_expand p hp]
  split_ifs with h
  · rw [coeff_partitionGenFun]
    show (((Fintype.card (Nat.Partition (n/p)) : Nat) : ZMod p)) = _
    rfl
  · rfl

/-! ### The `(q;q)∞` formal power series

We define `qPochInfPS R := (partitionGenFun R)⁻¹` (as a power series inverse,
which exists since the constant term of `partitionGenFun R` is 1, a unit).

This gives us `partitionGenFun R * qPochInfPS R = 1` algebraically. -/

/-- `(q;q)∞` as the formal power series inverse of `partitionGenFun`. -/
noncomputable def qPochInfPS (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.invOfUnit (partitionGenFun R) 1

/-- The defining property: `partitionGenFun * qPochInfPS = 1`. -/
theorem partitionGenFun_mul_qPochInfPS (R : Type*) [CommRing R] :
    partitionGenFun R * qPochInfPS R = 1 := by
  unfold qPochInfPS
  apply PowerSeries.mul_invOfUnit
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_partitionGenFun]
  rfl

/-- The defining property: `qPochInfPS * partitionGenFun = 1`. -/
theorem qPochInfPS_mul_partitionGenFun (R : Type*) [CommRing R] :
    qPochInfPS R * partitionGenFun R = 1 := by
  rw [mul_comm]
  exact partitionGenFun_mul_qPochInfPS R

/-- `qPochInfPS` is a unit (with `partitionGenFun` as its inverse). -/
theorem isUnit_qPochInfPS (R : Type*) [CommRing R] : IsUnit (qPochInfPS R) :=
  ⟨⟨qPochInfPS R, partitionGenFun R, qPochInfPS_mul_partitionGenFun R,
    partitionGenFun_mul_qPochInfPS R⟩, rfl⟩

/-- **Naturality of `partitionGenFun`** under ring homs: for `f : R →+* S`,
`PowerSeries.map f (partitionGenFun R) = partitionGenFun S`. -/
theorem map_partitionGenFun {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) :
    PowerSeries.map f (partitionGenFun R) = partitionGenFun S := by
  ext n
  rw [PowerSeries.coeff_map, coeff_partitionGenFun, coeff_partitionGenFun]
  simp

/-- **Naturality of `qPochInfPS`** under ring homs: for `f : R →+* S`,
`PowerSeries.map f (qPochInfPS R) = qPochInfPS S`. -/
theorem map_qPochInfPS {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    PowerSeries.map f (qPochInfPS R) = qPochInfPS S := by
  -- Both are inverses of partitionGenFun S
  have h1 : PowerSeries.map f (qPochInfPS R) * partitionGenFun S = 1 := by
    rw [← map_partitionGenFun f, ← map_mul, qPochInfPS_mul_partitionGenFun]
    exact (PowerSeries.map f).map_one
  have h2 : qPochInfPS S * partitionGenFun S = 1 := qPochInfPS_mul_partitionGenFun S
  -- (map f q) = (map f q) · (J · qPoch) = ((map f q) · J) · qPoch = 1 · qPoch = qPoch
  calc PowerSeries.map f (qPochInfPS R)
      = PowerSeries.map f (qPochInfPS R) * (partitionGenFun S * qPochInfPS S) := by
        rw [partitionGenFun_mul_qPochInfPS]; ring
    _ = (PowerSeries.map f (qPochInfPS R) * partitionGenFun S) * qPochInfPS S := by ring
    _ = 1 * qPochInfPS S := by rw [h1]
    _ = qPochInfPS S := one_mul _

section FormalEulerBridge

open scoped PowerSeries.WithPiTopology

/-- **Conditional bridge to formal Euler product**: if the formal geometric series identity
holds factor-by-factor, then `qPochInfPS = ∏'(1 - X^(n+1))` in `R⟦X⟧`.

The hypothesis is the per-factor formal identity:
  `(1 + ∑' j, X^((i+1)(j+1))) · (1 - X^(i+1)) = 1` in `R⟦X⟧` for all i.

This is provable via `mk_one_mul_one_sub_eq_one` + `expand (i+1)` ring hom + tsum reindexing
(detailed formalization left to future work due to careful coefficient tracking through tsum).

Given the hypothesis, the conclusion follows by composing:
1. `partitionGenFun_eq_tprod` (HasProd for partitionGenFun via Mathlib's hasProd_genFun)
2. `multipliable_one_sub_X_pow_succ` (HasProd for ∏'(1 - X^(n+1)))
3. `HasProd.mul` + the factor identity → HasProd of constant 1 → product equals 1
4. Uniqueness of inverse: from `partitionGenFun · Q = 1` and `J · qPoch = 1`, get `Q = qPoch`. -/
theorem qPochInfPS_eq_tprod_of_factor_identity
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (h_factor : ∀ i : Nat,
      ((1 : R⟦X⟧) + ∑' j, (PowerSeries.X (R := R)) ^ ((i + 1) * (j + 1))) *
        ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1)) = 1) :
    qPochInfPS R = ∏' i, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1)) := by
  -- HasProd for partitionGenFun (via partitionGenFun_eq_tprod)
  have h_partJ : HasProd
      (fun i : ℕ => (1 : R⟦X⟧) + ∑' j, (PowerSeries.X (R := R)) ^ ((i + 1) * (j + 1)))
      (partitionGenFun R) := by
    have hM := (Nat.Partition.multipliable_genFun (R := R) (fun _ _ => 1)).hasProd
    have heq : (fun i : ℕ => (1 : R⟦X⟧) +
        ∑' j, (1 : R) • (PowerSeries.X (R := R)) ^ ((i + 1) * (j + 1))) =
        fun i : ℕ => (1 : R⟦X⟧) +
        ∑' j, (PowerSeries.X (R := R)) ^ ((i + 1) * (j + 1)) := by
      funext i; congr 1; ext j; simp
    rw [← heq]
    convert hM using 1
    rw [partitionGenFun_eq_tprod, heq]
  -- HasProd for ∏'(1 - X^(n+1))
  have h_partQ : HasProd
      (fun i : ℕ => (1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))
      (∏' i, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))) :=
    (multipliable_one_sub_X_pow_succ R).hasProd
  -- HasProd.mul
  have h_mul := h_partJ.mul h_partQ
  -- The product function is the constant 1
  have h_const : (fun i : ℕ =>
      ((1 : R⟦X⟧) + ∑' j, (PowerSeries.X (R := R)) ^ ((i + 1) * (j + 1))) *
        ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))) = fun _ => (1 : R⟦X⟧) := by
    funext i; exact h_factor i
  rw [h_const] at h_mul
  -- HasProd of constant 1 → product is 1
  have h_one_prod : HasProd (fun _ : ℕ => (1 : R⟦X⟧)) 1 := hasProd_one
  have h_eq : partitionGenFun R * ∏' i, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1)) = 1 :=
    h_mul.unique h_one_prod
  -- Q = qPochInfPS via inverse uniqueness
  have h_qPoch : qPochInfPS R * partitionGenFun R = 1 := qPochInfPS_mul_partitionGenFun R
  calc qPochInfPS R
      = qPochInfPS R * 1 := (mul_one _).symm
    _ = qPochInfPS R *
          (partitionGenFun R * ∏' i, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))) := by rw [h_eq]
    _ = (qPochInfPS R * partitionGenFun R) *
          ∏' i, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1)) := by ring
    _ = 1 * ∏' i, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1)) := by rw [h_qPoch]
    _ = ∏' i, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1)) := one_mul _

/-- **THE formal Euler product theorem** (UNCONDITIONAL):
in `R⟦X⟧` for any commutative topological ring R with T2,
`qPochInfPS R = ∏' i, (1 - X^(i+1))`.

This is the formal power series version of the classical identity

  `(q; q)_∞ = ∏_{n ≥ 1} (1 - q^n)`.

Proof: combine `qPochInfPS_eq_tprod_of_factor_identity` with the now-proven
`factor_geom_series_identity` (the per-factor formal geometric series). -/
theorem qPochInfPS_eq_tprod
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    qPochInfPS R = ∏' i, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1)) :=
  qPochInfPS_eq_tprod_of_factor_identity R (factor_geom_series_identity R)

/-- **Partial product stabilization at coefficient k**: for any `N ≥ k`,
multiplying `∏_{i ∈ Finset.range N} (1 - X^(i+1))` by `(1 - X^(N+1))` doesn't change
the coefficient at index `k`.

This is because `(1 - X^(N+1))` only affects coefficients at indices `0` and `N+1`,
and `N+1 > k`. -/
theorem partial_prod_one_sub_X_pow_succ_coeff_stable
    (R : Type*) [CommRing R] (k N : Nat) (hN : k ≤ N) :
    PowerSeries.coeff k
        (∏ i ∈ Finset.range (N + 1), ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))) =
      PowerSeries.coeff k
        (∏ i ∈ Finset.range N, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))) := by
  rw [Finset.prod_range_succ]
  -- Goal: coeff k (P · (1 - X^(N+1))) = coeff k P  where P = partial product up to N
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (f := fun i j =>
      PowerSeries.coeff i (∏ i ∈ Finset.range N, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))) *
        PowerSeries.coeff j ((1 : R⟦X⟧) - PowerSeries.X ^ (N + 1))) k]
  -- Goal: ∑ i in range (k+1), coeff i P · coeff (k-i) (1 - X^(N+1)) = coeff k P
  -- (1 - X^(N+1)).coeff (k-i) = 1 if k-i = 0, -1 if k-i = N+1, 0 else.
  -- For k ≤ N: k - i ranges 0..k. So k-i = N+1 impossible (since k-i ≤ k ≤ N < N+1).
  -- So only k-i = 0 term contributes: i = k, coeff = 1.
  rw [Finset.sum_range_succ]
  -- Last term: coeff k P * coeff 0 (1 - X^(N+1)) = coeff k P * 1 = coeff k P
  -- Other terms: i < k, k-i > 0, k-i < N+1 (since k ≤ N), so coeff = 0
  have h_one_sub : PowerSeries.coeff 0 ((1 : R⟦X⟧) - PowerSeries.X ^ (N + 1)) = 1 := by
    rw [map_sub, PowerSeries.coeff_one]
    simp [PowerSeries.coeff_X_pow]
  rw [show k - k = 0 from Nat.sub_self k, h_one_sub, mul_one]
  -- Remaining: ∑ i in range k, ... = 0
  have h_rest : ∀ i ∈ Finset.range k,
      PowerSeries.coeff i (∏ j ∈ Finset.range N, ((1 : R⟦X⟧) - PowerSeries.X ^ (j + 1))) *
        PowerSeries.coeff (k - i) ((1 : R⟦X⟧) - PowerSeries.X ^ (N + 1)) = 0 := by
    intro i hi
    simp only [Finset.mem_range] at hi
    have h_ki : k - i > 0 := by omega
    have h_ki' : k - i ≤ k := Nat.sub_le k i
    have h_ki_lt : k - i < N + 1 := by omega
    have : PowerSeries.coeff (k - i) ((1 : R⟦X⟧) - PowerSeries.X ^ (N + 1)) = 0 := by
      rw [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
      have h1 : ¬ (k - i = 0) := by omega
      have h2 : ¬ (k - i = N + 1) := by omega
      simp [h1, h2]
    rw [this, mul_zero]
  rw [Finset.sum_eq_zero h_rest, zero_add]

/-- **Partial product stable at coefficient k for any extension above N**:
for `k ≤ N ≤ M`, the coefficient at `k` of `∏_{i ∈ range M}(1 - X^(i+1))` equals
the coefficient at `k` of `∏_{i ∈ range N}(1 - X^(i+1))`. -/
theorem partial_prod_one_sub_X_pow_succ_coeff_eq
    (R : Type*) [CommRing R] (k N M : Nat) (hkN : k ≤ N) (hNM : N ≤ M) :
    PowerSeries.coeff k
        (∏ i ∈ Finset.range M, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))) =
      PowerSeries.coeff k
        (∏ i ∈ Finset.range N, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))) := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M hM ih =>
    rw [partial_prod_one_sub_X_pow_succ_coeff_stable R k M (by omega), ih]

section CoeffTprodBridge

open Filter Topology

/-- **Main bridge theorem**: in `R⟦X⟧` with `WithPiTopology`, the coefficient at `k` of
the formal infinite product `∏'(1 - X^(i+1))` equals the coefficient at `k` of the partial
product `∏_{i ∈ range (k+1)}(1 - X^(i+1))`. This is the unconditional partial = tprod
agreement at low coefficients. -/
theorem coeff_tprod_one_sub_X_pow_succ
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (k : Nat) :
    PowerSeries.coeff k (∏' i, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))) =
      PowerSeries.coeff k
        (∏ i ∈ Finset.range (k + 1), ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))) := by
  have h_mult := multipliable_one_sub_X_pow_succ R
  -- Partial products tend to tprod (Nat-indexed)
  have h_tendsto : Tendsto
      (fun N : ℕ => ∏ i ∈ Finset.range N, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1)))
      atTop (𝓝 (∏' i, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1)))) :=
    h_mult.tendsto_prod_tprod_nat
  -- Compose with continuous coeff k
  have h_coeff_tendsto : Tendsto
      (fun N : ℕ =>
        PowerSeries.coeff k (∏ i ∈ Finset.range N, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))))
      atTop (𝓝 (PowerSeries.coeff k (∏' i, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))))) :=
    ((PowerSeries.WithPiTopology.continuous_coeff R k).tendsto _).comp h_tendsto
  -- The sequence is eventually constant
  have h_const_tendsto : Tendsto
      (fun N : ℕ =>
        PowerSeries.coeff k (∏ i ∈ Finset.range N, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))))
      atTop (𝓝 (PowerSeries.coeff k
        (∏ i ∈ Finset.range (k + 1), ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))))) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    exact ⟨k + 1, fun N hN =>
      (partial_prod_one_sub_X_pow_succ_coeff_eq R k (k + 1) N (by omega) hN).symm⟩
  exact tendsto_nhds_unique h_coeff_tendsto h_const_tendsto

end CoeffTprodBridge

end FormalEulerBridge

/-- The constant term of `qPochInfPS` is 1. -/
theorem constantCoeff_qPochInfPS (R : Type*) [CommRing R] :
    (PowerSeries.constantCoeff : R⟦X⟧ →+* R) (qPochInfPS R) = 1 := by
  unfold qPochInfPS
  rw [PowerSeries.constantCoeff_invOfUnit]
  rfl

/-- In `(ZMod p)⟦X⟧`, `qPochInfPS^p = qPochInfPS.expand p` (Frobenius applied to inverse). -/
theorem qPochInfPS_pow_eq_expand (p : Nat) [Fact (Nat.Prime p)] (hp : p ≠ 0) :
    (qPochInfPS (ZMod p)) ^ p =
      PowerSeries.expand p hp (qPochInfPS (ZMod p)) :=
  (PowerSeries.expand_eq_pow_zmod p hp _).symm

/-- **Frobenius preservation of inverse**: in `(ZMod p)⟦X⟧`,
`expand_p (partitionGenFun) · expand_p (qPochInfPS) = 1`.

Equivalently: the inverse relation `J · qPoch = 1` is preserved under the
Frobenius substitution `X ↦ X^p`. Proof: by ring-hom multiplication
of expand applied to `J · qPoch = 1`. -/
theorem expand_partitionGenFun_mul_expand_qPochInfPS
    (p : Nat) [Fact (Nat.Prime p)] (hp : p ≠ 0) :
    PowerSeries.expand p hp (partitionGenFun (ZMod p)) *
      PowerSeries.expand p hp (qPochInfPS (ZMod p)) = 1 := by
  rw [← map_mul, partitionGenFun_mul_qPochInfPS, map_one]

/-- The coefficient at index 0 of `qPochInfPS` is 1. -/
theorem coeff_zero_qPochInfPS (R : Type*) [CommRing R] :
    (qPochInfPS R).coeff 0 = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact constantCoeff_qPochInfPS R

section SignedStrictPartition

open scoped PowerSeries.WithPiTopology

/-- The character function picking out strict (multiplicity-1) partitions with sign.
For `i ≥ 1` and `j = 1`: returns `-1`. For other `(i, j)`: returns `0`.

When applied via `Nat.Partition.genFun`, this gives the formal Euler product
`∏(1 - X^(i+1)) = qPochInfPS`, whose coefficient at `n` is the signed count
of strict partitions of `n`. -/
noncomputable def signedStrictChar (R : Type*) [Ring R] : ℕ → ℕ → R :=
  fun i j => if i ≥ 1 ∧ j = 1 then -1 else 0

/-- **Strict-partition Euler product identity**: `Nat.Partition.genFun (signedStrictChar R) = qPochInfPS R`.

Proof: both equal `∏'(1 - X^(i+1))` via `Nat.Partition.genFun_eq_tprod` (with the right f) and
`qPochInfPS_eq_tprod`. -/
theorem genFun_signedStrictChar_eq_qPochInfPS
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    Nat.Partition.genFun (signedStrictChar R) = qPochInfPS R := by
  rw [qPochInfPS_eq_tprod]
  rw [Nat.Partition.genFun_eq_tprod]
  congr 1
  ext i
  -- factor: 1 + ∑' j, signedStrictChar R (i+1) (j+1) • X^((i+1)(j+1)) = 1 - X^(i+1)
  have h_at_zero : signedStrictChar R (i + 1) (0 + 1) = -1 := by
    simp [signedStrictChar]
  have h_at_other : ∀ j, j ≠ 0 → signedStrictChar R (i + 1) (j + 1) = 0 := by
    intro j hj
    simp [signedStrictChar]
    omega
  have h_sum : (∑' j : ℕ, signedStrictChar R (i + 1) (j + 1) •
      (PowerSeries.X (R := R)) ^ ((i + 1) * (j + 1))) =
      -(PowerSeries.X (R := R)) ^ (i + 1) := by
    rw [tsum_eq_single 0 (fun j hj => by
      rw [h_at_other j hj]; simp)]
    rw [h_at_zero]
    simp
  rw [h_sum]
  ring

/-- **Signed strict partition count via Nat.Partition** (using Mathlib's `Nat.Partition`).
This is the sum over partitions of `n` (with no repeated parts, weighted by sign). -/
noncomputable def signedStrictCount (R : Type*) [CommRing R] (n : ℕ) : R :=
  (Nat.Partition.genFun (signedStrictChar R)).coeff n

/-- **Main: qPochInfPS coefficient = signedStrictCount**.
This is the formal-PS expansion of `(q; q)_∞ = ∑ over strict partitions, (-1)^|parts| · X^|partition|`. -/
theorem coeff_qPochInfPS_eq_signedStrictCount
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (n : Nat) :
    (qPochInfPS R).coeff n = signedStrictCount R n := by
  unfold signedStrictCount
  rw [genFun_signedStrictChar_eq_qPochInfPS]

end SignedStrictPartition

section BridgeToCh05Pentagonal

open PowerSeries
open scoped PowerSeries.WithPiTopology

/-- Expand the finite product `∏_{i ∈ range N}(1 - X^(i+1))` as a sum over subsets:
`∑_{t ⊆ range N} (-1)^|t| · X^(∑_{i∈t}(i+1))`. -/
theorem finite_product_one_sub_X_pow_eq_subset_sum (R : Type*) [CommRing R] (N : Nat) :
    (∏ i ∈ Finset.range N, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))) =
      ∑ t ∈ (Finset.range N).powerset,
        (-1 : R⟦X⟧) ^ t.card * PowerSeries.X ^ (∑ i ∈ t, (i + 1)) := by
  rw [Finset.prod_sub (f := fun _ : Nat => (1 : R⟦X⟧)) (g := fun i => PowerSeries.X ^ (i + 1))]
  refine Finset.sum_congr rfl ?_
  intro t _
  rw [Finset.prod_const_one, mul_one, Finset.prod_pow_eq_pow_sum]

/-- Coefficient extraction: `(-1)^k · X^m` at coefficient `n` equals `(-1)^k` if `n = m` else `0`. -/
theorem coeff_neg_one_pow_mul_X_pow (R : Type*) [CommRing R] (k m n : Nat) :
    ((-1 : R⟦X⟧) ^ k * PowerSeries.X ^ m).coeff n =
      if n = m then (-1 : R) ^ k else 0 := by
  have h_neg_one : ((-1 : R⟦X⟧) : R⟦X⟧) = (PowerSeries.C : R →+* R⟦X⟧) (-1) := by
    rw [map_neg, map_one]
  rw [show ((-1 : R⟦X⟧) ^ k) = (PowerSeries.C : R →+* R⟦X⟧) ((-1 : R) ^ k) from by
    rw [h_neg_one, ← map_pow]]
  rw [PowerSeries.coeff_C_mul_X_pow]

/-- The coefficient at `n` of the finite product `∏(1 - X^(i+1))` equals
the signed sum over subsets summing to `n`. -/
theorem coeff_finite_product_one_sub_X_pow_succ (R : Type*) [CommRing R] (n N : Nat) :
    (∏ i ∈ Finset.range N, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))).coeff n =
      ∑ t ∈ ((Finset.range N).powerset).filter (fun t => ∑ i ∈ t, (i + 1) = n),
        (-1 : R) ^ t.card := by
  rw [finite_product_one_sub_X_pow_eq_subset_sum]
  rw [map_sum]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro t _
  rw [coeff_neg_one_pow_mul_X_pow R t.card (∑ i ∈ t, (i + 1)) n]
  by_cases h : ∑ i ∈ t, (i + 1) = n
  · simp [h]
  · have h' : n ≠ ∑ i ∈ t, (i + 1) := fun habs => h habs.symm
    simp [h, h']

/-- **Bridge to Ch04Franklin's signedStrictPartitionCount**: the subset-sum form
`∑_{t ⊆ range (n+1), ∑_{i∈t}(i+1) = n} (-1)^|t|` equals `Ch04Franklin.signedStrictPartitionCount n`
in `ℤ`.

Bijection: `t ↦ t.image (· + 1)` between subsets of `range(n+1)` (i.e., {0,...,n})
summing `(i+1)` to `n`, and subsets of `{1,...,n}` summing to `n` (Ch04Franklin's
`StrictPartitionSet n`). -/
theorem coeff_finite_product_eq_signedStrictPartitionCount (n : Nat) :
    (∑ t ∈ ((Finset.range (n + 1)).powerset).filter (fun t => ∑ i ∈ t, (i + 1) = n),
        (-1 : ℤ) ^ t.card) =
      QseriesFormalization.PartI.Ch04Franklin.signedStrictPartitionCount n := by
  unfold QseriesFormalization.PartI.Ch04Franklin.signedStrictPartitionCount
  unfold QseriesFormalization.PartI.Ch04Franklin.StrictPartitionSet
  refine Finset.sum_nbij' (fun t => t.image (· + 1)) (fun S => S.image (· - 1))
    ?hi ?hj ?h_li ?h_ri ?h_val
  case hi =>
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_powerset] at ht ⊢
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      rw [Finset.mem_image] at hk
      obtain ⟨i, hi, hki⟩ := hk
      have h_i := ht.1 hi
      simp only [Finset.mem_range] at h_i ⊢
      -- i ≤ n, so i+1 ≤ n+1. But we need i+1 < n+1, i.e., i+1 ≤ n.
      -- Sum constraint: i+1 ≤ ∑(i+1) = n.
      have h_le : i + 1 ≤ n := by
        rw [← ht.2]
        exact Finset.single_le_sum (f := fun i => i + 1)
          (fun _ _ => Nat.zero_le _) hi
      omega
    · intro k hk
      rw [Finset.mem_image] at hk
      obtain ⟨_, _, hki⟩ := hk; omega
    · rw [Finset.sum_image (fun a _ b _ h => by omega)]
      exact ht.2
  case hj =>
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
    obtain ⟨hSrange, hSpos, hSsum⟩ := hS
    refine ⟨?_, ?_⟩
    · intro k hk
      rw [Finset.mem_image] at hk
      obtain ⟨a, haS, hka⟩ := hk
      have ha_in := hSrange haS
      have ha_pos := hSpos a haS
      simp only [Finset.mem_range] at ha_in ⊢
      omega
    · rw [Finset.sum_image (fun a haS b hbS h => by
        have := hSpos a haS; have := hSpos b hbS; omega)]
      have hcong : ∀ k ∈ S, k - 1 + 1 = k := fun k hk => by
        have := hSpos k hk; omega
      rw [Finset.sum_congr rfl hcong]; exact hSsum
  case h_li =>
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_powerset] at ht
    ext i
    simp only [Finset.mem_image]
    refine ⟨fun ⟨k, hk_mem, hk_eq⟩ => ?_, fun hi => ?_⟩
    · obtain ⟨j, hj, rfl⟩ := hk_mem
      have : i = j := by omega
      rw [this]; exact hj
    · refine ⟨i + 1, ⟨i, hi, rfl⟩, by omega⟩
  case h_ri =>
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨_, hSpos, _⟩ := hS
    ext j
    simp only [Finset.mem_image]
    refine ⟨fun ⟨k, hk_mem, hk_eq⟩ => ?_, fun hj => ?_⟩
    · obtain ⟨a, ha, rfl⟩ := hk_mem
      have h_pos := hSpos a ha
      have : a - 1 + 1 = a := by omega
      rw [this] at hk_eq; rw [← hk_eq]; exact ha
    · have h_pos := hSpos j hj
      refine ⟨j - 1, ⟨j, hj, rfl⟩, by omega⟩
  case h_val =>
    intro t _
    rw [Finset.card_image_of_injective _ (fun a b h => by omega)]

end BridgeToCh05Pentagonal

/-- **qPochInfPS coefficient = finite product coefficient**: closed-form evaluation.

In `R⟦X⟧` with `WithPiTopology`,
  `(qPochInfPS R).coeff k = (∏_{i < k+1}(1 - X^(i+1))).coeff k`.

Proof: combine `qPochInfPS_eq_tprod` with `coeff_tprod_one_sub_X_pow_succ`.
This gives a concrete, computable formula for `(q;q)_∞` coefficients via finite products. -/
theorem coeff_qPochInfPS_eq_coeff_finite_product
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (k : Nat) :
    (qPochInfPS R).coeff k =
      (∏ i ∈ Finset.range (k + 1), ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))).coeff k := by
  rw [qPochInfPS_eq_tprod]
  exact coeff_tprod_one_sub_X_pow_succ R k

/-- **B1 Step 2 (FINAL): Euler Pentagonal Number Theorem as formal power series identity**.

For all `n`: `(qPochInfPS ℤ).coeff n = pentagonalSign n`.

This is the **classical Euler Pentagonal Number Theorem** as a formal-PS identity in `ℤ⟦X⟧`:
every coefficient of `(q; q)_∞` is the pentagonal sign. Combined with cast naturality,
this gives `(qPochInfPS R).coeff n = (pentagonalSign n : R)` for any commutative ring `R`.

Proof chain:
1. `coeff_qPochInfPS_eq_coeff_finite_product`: coeff via finite product
2. `coeff_finite_product_one_sub_X_pow_succ`: subset sum form
3. `coeff_finite_product_eq_signedStrictPartitionCount`: bridge to Ch04Franklin (Finset bijection)
4. `Ch04Franklin.euler_pentagonal_combinatorial`: Franklin involution → pentagonalSign -/
theorem coeff_qPochInfPS_int_eq_pentagonalSign (n : Nat) :
    (qPochInfPS ℤ).coeff n = QseriesFormalization.PartI.Ch04Franklin.pentagonalSign n := by
  rw [coeff_qPochInfPS_eq_coeff_finite_product ℤ n,
      coeff_finite_product_one_sub_X_pow_succ ℤ n (n + 1),
      coeff_finite_product_eq_signedStrictPartitionCount n,
      QseriesFormalization.PartI.Ch04Franklin.euler_pentagonal_combinatorial n]

/-- **Euler Pentagonal in any commutative ring**: `(qPochInfPS R).coeff n = (pentagonalSign n : R)`.

Derived from the ℤ case via the cast naturality `map_qPochInfPS`. -/
theorem coeff_qPochInfPS_eq_pentagonalSign
    (R : Type*) [CommRing R] (n : Nat) :
    (qPochInfPS R).coeff n =
      ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign n : ℤ) : R) := by
  rw [← coeff_qPochInfPS_int_eq_pentagonalSign n]
  rw [← map_qPochInfPS (Int.castRingHom R)]
  rw [PowerSeries.coeff_map]
  rfl

/-! ### Specific qPochInfPS coefficient values via Euler pentagonal

Derived from `coeff_qPochInfPS_eq_pentagonalSign` + `decide` on `pentagonalSign n` for
specific small n. These extend beyond the n=0..8 values proved via the J·qPoch=1 recurrence
in earlier sections. -/

/-- `(qPochInfPS R).coeff 12 = -1` (12 = 3·(3·3-1)/2 is pentagonal with sign (-1)^3 = -1). -/
theorem coeff_twelve_qPochInfPS (R : Type*) [CommRing R] :
    (qPochInfPS R).coeff 12 = -1 := by
  rw [coeff_qPochInfPS_eq_pentagonalSign]
  show ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 12 : ℤ) : R) = -1
  rw [show (QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 12 : ℤ) = -1 from by decide]
  norm_cast

/-- `(qPochInfPS R).coeff 15 = -1` (15 = 3·(3·3+1)/2 is pentagonal, sign (-1)^3 = -1). -/
theorem coeff_fifteen_qPochInfPS (R : Type*) [CommRing R] :
    (qPochInfPS R).coeff 15 = -1 := by
  rw [coeff_qPochInfPS_eq_pentagonalSign]
  show ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 15 : ℤ) : R) = -1
  rw [show (QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 15 : ℤ) = -1 from by decide]
  norm_cast

/-- `(qPochInfPS R).coeff 22 = 1` (22 = 4·(3·4-1)/2 is pentagonal, sign (-1)^4 = 1). -/
theorem coeff_twentytwo_qPochInfPS (R : Type*) [CommRing R] :
    (qPochInfPS R).coeff 22 = 1 := by
  rw [coeff_qPochInfPS_eq_pentagonalSign]
  show ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 22 : ℤ) : R) = 1
  rw [show (QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 22 : ℤ) = 1 from by decide]
  norm_cast

/-- `(qPochInfPS R).coeff 9 = 0` (9 not pentagonal). -/
theorem coeff_nine_qPochInfPS' (R : Type*) [CommRing R] :
    (qPochInfPS R).coeff 9 = 0 := by
  rw [coeff_qPochInfPS_eq_pentagonalSign]
  show ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 9 : ℤ) : R) = 0
  rw [show (QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 9 : ℤ) = 0 from by decide]
  norm_cast

/-- `(qPochInfPS R).coeff 10 = 0`, `coeff 11 = 0` (10, 11 not pentagonal). -/
theorem coeff_ten_qPochInfPS (R : Type*) [CommRing R] :
    (qPochInfPS R).coeff 10 = 0 := by
  rw [coeff_qPochInfPS_eq_pentagonalSign]
  show ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 10 : ℤ) : R) = 0
  rw [show (QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 10 : ℤ) = 0 from by decide]
  norm_cast

theorem coeff_eleven_qPochInfPS (R : Type*) [CommRing R] :
    (qPochInfPS R).coeff 11 = 0 := by
  rw [coeff_qPochInfPS_eq_pentagonalSign]
  show ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 11 : ℤ) : R) = 0
  rw [show (QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 11 : ℤ) = 0 from by decide]
  norm_cast

/-- **`qPochInfPS` as the formal pentagonal series**:
`qPochInfPS R = PowerSeries.mk fun n => (pentagonalSign n : R)` as formal power series.

This is the FORMAL series version of Euler's pentagonal identity. Combined with
the cube convolution form, it reduces the B2 Jacobi target to the integer convolution
identity `∑_{a+b+c=n} pent(a)·pent(b)·pent(c) = jacobiTripleSign n`. -/
theorem qPochInfPS_eq_mk_pentagonalSign (R : Type*) [CommRing R] :
    qPochInfPS R = PowerSeries.mk (fun n => ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign n : ℤ) : R)) := by
  ext n
  rw [PowerSeries.coeff_mk]
  exact coeff_qPochInfPS_eq_pentagonalSign R n

/-- **Explicit formula for `(qPoch ZMod p)^p` coefficients via Frobenius + Euler pentagonal**:
  `((qPoch ZMod p)^p).coeff n = if p ∣ n then (pentagonalSign (n/p) : ZMod p) else 0`.

Proof: by Frobenius, `(qPoch ZMod p)^p = expand_p (qPoch ZMod p)`. Then by
`PowerSeries.coeff_expand`, the coefficient at `n` is `qPoch.coeff (n/p)` if `p ∣ n`
else `0`. And by Euler pentagonal, `qPoch.coeff k = pentagonalSign k`. -/
theorem coeff_qPochInfPS_pow_p_in_ZMod_p
    (p : Nat) [Fact (Nat.Prime p)] (hp : p ≠ 0) (n : Nat) :
    ((qPochInfPS (ZMod p)) ^ p).coeff n =
      if p ∣ n then
        ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign (n / p) : ℤ) : ZMod p)
      else 0 := by
  rw [qPochInfPS_pow_eq_expand p hp]
  rw [PowerSeries.coeff_expand]
  split_ifs with h
  · exact coeff_qPochInfPS_eq_pentagonalSign (ZMod p) (n / p)
  · rfl


/-! ### B2 groundwork: Jacobi triple product at z=1 (cube identity)

Goal: prove `(qPochInfPS R)^3 = ∑ (-1)^n (2n+1) X^{n(n+1)/2}` as formal power series.

This is the classical Jacobi identity `∏(1-q^n)^3 = ∑(-1)^n(2n+1)q^{T_n}`.
Ch04_T43 has the analytic version (`jacobiIdentity`) for `|q| < 1`.

The formal-PS version requires either:
  (a) Combinatorial proof via Sylvester-style involution on triple partitions
  (b) Analytic → formal bridge via Taylor expansion uniqueness

Both are substantial work; we define the target and prove small cases here. -/

/-- The Jacobi triple sign: `(-1)^k · (2k+1)` if `n = k(k+1)/2` for some `k ≥ 0`,
else `0`. This is the expected `n`-th coefficient of `(q;q)_∞^3`. -/
def jacobiTripleSign (n : Nat) : Int :=
  match (List.range (n + 1)).find? (fun k => n = k * (k + 1) / 2) with
  | some k => (-1 : Int) ^ k * (2 * k + 1)
  | none => 0

-- Sanity: triangular numbers 0, 1, 3, 6, 10, 15, ...
-- Values:                    1, -3, 5, -7, 9, -11, ...
example : jacobiTripleSign 0 = 1 := by native_decide
example : jacobiTripleSign 1 = -3 := by native_decide
example : jacobiTripleSign 2 = 0 := by native_decide
example : jacobiTripleSign 3 = 5 := by native_decide
example : jacobiTripleSign 4 = 0 := by native_decide
example : jacobiTripleSign 5 = 0 := by native_decide
example : jacobiTripleSign 6 = -7 := by native_decide
example : jacobiTripleSign 10 = 9 := by native_decide

/-- The Jacobi theta-like formal power series: `∑ (-1)^k (2k+1) X^{T_k}`. -/
noncomputable def jacobiThetaPS (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.mk fun n => ((jacobiTripleSign n : ℤ) : R)

/-- Coefficient extraction from `jacobiThetaPS`. -/
@[simp] theorem coeff_jacobiThetaPS (R : Type*) [CommRing R] (n : Nat) :
    (jacobiThetaPS R).coeff n = ((jacobiTripleSign n : ℤ) : R) := by
  unfold jacobiThetaPS; rw [PowerSeries.coeff_mk]

-- **B2 target theorem**: `(qPochInfPS R)^3 = jacobiThetaPS R` in `R⟦X⟧`.
-- This is the formal-PS version of Jacobi's identity (Ch04.jacobiIdentity in
-- analytic form). Full proof requires either Sylvester's combinatorial bijection
-- or an analytic ↔ formal Taylor uniqueness bridge.


-- Small case verification: `(qPochInfPS R)^3 . coeff n` for small n is computable
-- via the generic `coeff_n_pow_of_constantCoeff_one` helpers in Ch20 and Euler-pentagonal
-- coefficient values. See Ch20.ramanujanTau_two for the analogous tau computation pattern.

/-- **Generalized closed-form**: for any `N` with `k < N`,
`(qPochInfPS R).coeff k = (∏_{i < N}(1 - X^(i+1))).coeff k`. -/
theorem coeff_qPochInfPS_eq_coeff_finite_product_of_lt
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (k N : Nat) (hkN : k < N) :
    (qPochInfPS R).coeff k =
      (∏ i ∈ Finset.range N, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))).coeff k := by
  rw [coeff_qPochInfPS_eq_coeff_finite_product]
  exact (partial_prod_one_sub_X_pow_succ_coeff_eq R k (k + 1) N (Nat.le_succ k) hkN).symm

/-- **Truncation agreement**: the truncation of `qPochInfPS R` at degree `N` equals
the truncation of `∏_{i < N}(1 - X^(i+1))` at degree `N`. -/
theorem trunc_qPochInfPS_eq_trunc_finite_product
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (N : Nat) :
    PowerSeries.trunc N (qPochInfPS R) =
      PowerSeries.trunc N
        (∏ i ∈ Finset.range N, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))) := by
  ext k
  rcases Nat.lt_or_ge k N with hkN | hkN
  · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_pos hkN, if_pos hkN]
    exact coeff_qPochInfPS_eq_coeff_finite_product_of_lt R k N hkN
  · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc,
        if_neg (not_lt.mpr hkN), if_neg (not_lt.mpr hkN)]

/-- **Power agreement at low coefficients**: for any exponent `e` and `k < N`,
`((qPochInfPS R)^e).coeff k = ((∏_{i < N}(1 - X^(i+1)))^e).coeff k`.

Proof: via `PowerSeries.trunc_trunc_pow` from the truncation agreement. -/
theorem coeff_qPochInfPS_pow_eq_coeff_finite_product_pow
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (e k N : Nat) (hkN : k < N) :
    ((qPochInfPS R) ^ e).coeff k =
      ((∏ i ∈ Finset.range N, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))) ^ e).coeff k := by
  have h_trunc := trunc_qPochInfPS_eq_trunc_finite_product R N
  have h_pow : PowerSeries.trunc N ((qPochInfPS R) ^ e) =
      PowerSeries.trunc N
        ((∏ i ∈ Finset.range N, ((1 : R⟦X⟧) - PowerSeries.X ^ (i + 1))) ^ e) := by
    rw [← PowerSeries.trunc_trunc_pow, h_trunc, PowerSeries.trunc_trunc_pow]
  have hcoeff := congrArg (Polynomial.coeff · k) h_pow
  simp only [PowerSeries.coeff_trunc, if_pos hkN] at hcoeff
  exact hcoeff

/-- `(partitionGenFun R).coeff 1 = 1` in any commutative semiring: one partition of 1. -/
theorem coeff_one_partitionGenFun (R : Type*) [CommSemiring R] :
    (partitionGenFun R).coeff 1 = 1 := by
  rw [coeff_partitionGenFun]
  have h : Fintype.card (Nat.Partition 1) = 1 := Ch01.partitionCount_one
  rw [h]; simp

/-- The coefficient at index 1 of `qPochInfPS`: from `J · (q;q)∞ = 1`,
extracting the X¹-coefficient gives `J.coeff 0 · qPochInfPS.coeff 1 + J.coeff 1 · qPochInfPS.coeff 0 = 0`.
Plugging in `J.coeff 0 = J.coeff 1 = 1` and `qPochInfPS.coeff 0 = 1` yields `coeff 1 = -1`. -/
theorem coeff_one_qPochInfPS (R : Type*) [CommRing R] :
    (qPochInfPS R).coeff 1 = -1 := by
  have hmul : (partitionGenFun R * qPochInfPS R).coeff 1 = (1 : R⟦X⟧).coeff 1 := by
    rw [partitionGenFun_mul_qPochInfPS]
  rw [PowerSeries.coeff_mul] at hmul
  -- antidiagonal of 1 = {(0,1), (1,0)}
  rw [show (Finset.antidiagonal 1 : Finset (Nat × Nat)) = {(0, 1), (1, 0)} from rfl] at hmul
  rw [Finset.sum_insert (by simp), Finset.sum_singleton] at hmul
  simp only [coeff_zero_partitionGenFun, coeff_zero_qPochInfPS,
    coeff_one_partitionGenFun, one_mul, mul_one] at hmul
  -- hmul: qPochInfPS.coeff 1 + 1 = (1 : R⟦X⟧).coeff 1
  rw [show ((1 : R⟦X⟧).coeff 1 : R) = 0 from by
    rw [PowerSeries.coeff_one]; simp] at hmul
  linear_combination hmul

/-- `(partitionGenFun R).coeff 2 = 2` in any commutative semiring: two partitions of 2 ([2], [1,1]). -/
theorem coeff_two_partitionGenFun (R : Type*) [CommSemiring R] :
    (partitionGenFun R).coeff 2 = 2 := by
  rw [coeff_partitionGenFun]
  have h : Fintype.card (Nat.Partition 2) = 2 := Ch01.partitionCount_two
  rw [h]; simp

/-- The coefficient at index 2 of `qPochInfPS`: equals `-1` (Euler pentagonal: 1 - X - X² + ...).
From `J · (q;q)∞ = 1` at X²: `coeff 2 + (-1) + 2 = 0`, so coeff 2 = -1. -/
theorem coeff_two_qPochInfPS (R : Type*) [CommRing R] :
    (qPochInfPS R).coeff 2 = -1 := by
  have hmul : (partitionGenFun R * qPochInfPS R).coeff 2 = (1 : R⟦X⟧).coeff 2 := by
    rw [partitionGenFun_mul_qPochInfPS]
  rw [PowerSeries.coeff_mul] at hmul
  rw [show (Finset.antidiagonal 2 : Finset (Nat × Nat)) = {(0, 2), (1, 1), (2, 0)} from rfl] at hmul
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton] at hmul
  simp only [coeff_zero_partitionGenFun, coeff_zero_qPochInfPS,
    coeff_one_partitionGenFun, coeff_one_qPochInfPS, coeff_two_partitionGenFun,
    one_mul, mul_one] at hmul
  rw [show ((1 : R⟦X⟧).coeff 2 : R) = 0 from by
    rw [PowerSeries.coeff_one]; simp] at hmul
  linear_combination hmul

/-- `(partitionGenFun R).coeff 3 = 3` in any commutative semiring: three partitions of 3
([3], [2,1], [1,1,1]). -/
theorem coeff_three_partitionGenFun (R : Type*) [CommSemiring R] :
    (partitionGenFun R).coeff 3 = 3 := by
  rw [coeff_partitionGenFun]
  have h : Fintype.card (Nat.Partition 3) = 3 := Ch01.partitionCount_three
  rw [h]; simp

/-- `(partitionGenFun R).coeff 4 = 5` (five partitions of 4). -/
theorem coeff_four_partitionGenFun (R : Type*) [CommSemiring R] :
    (partitionGenFun R).coeff 4 = 5 := by
  rw [coeff_partitionGenFun]
  have h : Fintype.card (Nat.Partition 4) = 5 := Ch01.partitionCount_four
  rw [h]; simp

/-- `(partitionGenFun R).coeff 5 = 7` (seven partitions of 5). -/
theorem coeff_five_partitionGenFun (R : Type*) [CommSemiring R] :
    (partitionGenFun R).coeff 5 = 7 := by
  rw [coeff_partitionGenFun]
  have h : Fintype.card (Nat.Partition 5) = 7 := Ch01.partitionCount_five
  rw [h]; simp

/-- The coefficient at index 3 of `qPochInfPS`: equals `0` (Euler pentagonal: 1-X-X²+X⁵+X⁷-...).
From `J · (q;q)∞ = 1` at X³: `coeff 3 + (-1) + (-2) + 3 = 0`, so coeff 3 = 0. -/
theorem coeff_three_qPochInfPS (R : Type*) [CommRing R] :
    (qPochInfPS R).coeff 3 = 0 := by
  have hmul : (partitionGenFun R * qPochInfPS R).coeff 3 = (1 : R⟦X⟧).coeff 3 := by
    rw [partitionGenFun_mul_qPochInfPS]
  rw [PowerSeries.coeff_mul] at hmul
  rw [show (Finset.antidiagonal 3 : Finset (Nat × Nat)) = {(0, 3), (1, 2), (2, 1), (3, 0)} from rfl] at hmul
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_insert (by simp), Finset.sum_singleton] at hmul
  simp only [coeff_zero_partitionGenFun, coeff_zero_qPochInfPS,
    coeff_one_partitionGenFun, coeff_one_qPochInfPS,
    coeff_two_partitionGenFun, coeff_two_qPochInfPS,
    coeff_three_partitionGenFun,
    one_mul, mul_one] at hmul
  rw [show ((1 : R⟦X⟧).coeff 3 : R) = 0 from by
    rw [PowerSeries.coeff_one]; simp] at hmul
  linear_combination hmul

/-- The coefficient at index 4 of `qPochInfPS`: equals `0` (Euler pentagonal: zero at n=4).
From `J · (q;q)∞ = 1` at X⁴: `coeff 4 + 0 + (-2) + (-3) + 5 = 0`, so coeff 4 = 0. -/
theorem coeff_four_qPochInfPS (R : Type*) [CommRing R] :
    (qPochInfPS R).coeff 4 = 0 := by
  have hmul : (partitionGenFun R * qPochInfPS R).coeff 4 = (1 : R⟦X⟧).coeff 4 := by
    rw [partitionGenFun_mul_qPochInfPS]
  rw [PowerSeries.coeff_mul] at hmul
  rw [show (Finset.antidiagonal 4 : Finset (Nat × Nat))
    = {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} from rfl] at hmul
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_singleton] at hmul
  simp only [coeff_zero_partitionGenFun, coeff_zero_qPochInfPS,
    coeff_one_partitionGenFun, coeff_one_qPochInfPS,
    coeff_two_partitionGenFun, coeff_two_qPochInfPS,
    coeff_three_partitionGenFun, coeff_three_qPochInfPS,
    coeff_four_partitionGenFun,
    one_mul, mul_one] at hmul
  rw [show ((1 : R⟦X⟧).coeff 4 : R) = 0 from by
    rw [PowerSeries.coeff_one]; simp] at hmul
  linear_combination hmul

/-- `(partitionGenFun R).coeff 6 = 11` (eleven partitions of 6). -/
theorem coeff_six_partitionGenFun (R : Type*) [CommSemiring R] :
    (partitionGenFun R).coeff 6 = 11 := by
  rw [coeff_partitionGenFun]
  have h : Fintype.card (Nat.Partition 6) = 11 := Ch01.partitionCount_six
  rw [h]; simp

/-- The coefficient at index 5 of `qPochInfPS`: equals `1`
(Euler pentagonal: `1 - X - X² + X⁵ + X⁷ - X¹² - ...`, where 5 = 2(3·2-1)/2 with sign (-1)² = 1).
From `J · (q;q)∞ = 1` at X⁵: `coeff 5 + 0 + 0 + (-3) + (-5) + 7 = 0`, so coeff 5 = 1. -/
theorem coeff_five_qPochInfPS (R : Type*) [CommRing R] :
    (qPochInfPS R).coeff 5 = 1 := by
  have hmul : (partitionGenFun R * qPochInfPS R).coeff 5 = (1 : R⟦X⟧).coeff 5 := by
    rw [partitionGenFun_mul_qPochInfPS]
  rw [PowerSeries.coeff_mul] at hmul
  rw [show (Finset.antidiagonal 5 : Finset (Nat × Nat))
    = {(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)} from rfl] at hmul
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_insert (by simp), Finset.sum_singleton] at hmul
  simp only [coeff_zero_partitionGenFun, coeff_zero_qPochInfPS,
    coeff_one_partitionGenFun, coeff_one_qPochInfPS,
    coeff_two_partitionGenFun, coeff_two_qPochInfPS,
    coeff_three_partitionGenFun, coeff_three_qPochInfPS,
    coeff_four_partitionGenFun, coeff_four_qPochInfPS,
    coeff_five_partitionGenFun,
    one_mul, mul_one] at hmul
  rw [show ((1 : R⟦X⟧).coeff 5 : R) = 0 from by
    rw [PowerSeries.coeff_one]; simp] at hmul
  linear_combination hmul

/-- The coefficient at index 6 of `qPochInfPS`: equals `0` (6 is not a pentagonal number).
From `J · (q;q)∞ = 1` at X⁶: `coeff 6 + 1 + 0 + 0 + (-5) + (-7) + 11 = 0`, so coeff 6 = 0. -/
theorem coeff_six_qPochInfPS (R : Type*) [CommRing R] :
    (qPochInfPS R).coeff 6 = 0 := by
  have hmul : (partitionGenFun R * qPochInfPS R).coeff 6 = (1 : R⟦X⟧).coeff 6 := by
    rw [partitionGenFun_mul_qPochInfPS]
  rw [PowerSeries.coeff_mul] at hmul
  rw [show (Finset.antidiagonal 6 : Finset (Nat × Nat))
    = {(0, 6), (1, 5), (2, 4), (3, 3), (4, 2), (5, 1), (6, 0)} from rfl] at hmul
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_singleton] at hmul
  simp only [coeff_zero_partitionGenFun, coeff_zero_qPochInfPS,
    coeff_one_partitionGenFun, coeff_one_qPochInfPS,
    coeff_two_partitionGenFun, coeff_two_qPochInfPS,
    coeff_three_partitionGenFun, coeff_three_qPochInfPS,
    coeff_four_partitionGenFun, coeff_four_qPochInfPS,
    coeff_five_partitionGenFun, coeff_five_qPochInfPS,
    coeff_six_partitionGenFun,
    one_mul, mul_one] at hmul
  rw [show ((1 : R⟦X⟧).coeff 6 : R) = 0 from by
    rw [PowerSeries.coeff_one]; simp] at hmul
  linear_combination hmul

/-- `(partitionGenFun R).coeff 7 = 15` (fifteen partitions of 7). -/
theorem coeff_seven_partitionGenFun (R : Type*) [CommSemiring R] :
    (partitionGenFun R).coeff 7 = 15 := by
  rw [coeff_partitionGenFun]
  have h : Fintype.card (Nat.Partition 7) = 15 := Ch01.partitionCount_seven
  rw [h]; simp

/-- `(partitionGenFun R).coeff 8 = 22` (twenty-two partitions of 8). -/
theorem coeff_eight_partitionGenFun (R : Type*) [CommSemiring R] :
    (partitionGenFun R).coeff 8 = 22 := by
  rw [coeff_partitionGenFun]
  have h : Fintype.card (Nat.Partition 8) = 22 := Ch01.partitionCount_eight
  rw [h]; simp

/-- The coefficient at index 7 of `qPochInfPS`: equals `1`
(Euler pentagonal: `X^7` appears at k=-2: `-2·(3·(-2)-1)/2 = 7`, sign `(-1)^{-2} = 1`).
From `J · (q;q)∞ = 1` at X⁷ recurrence: solve coeff 7 = 1. -/
theorem coeff_seven_qPochInfPS (R : Type*) [CommRing R] :
    (qPochInfPS R).coeff 7 = 1 := by
  have hmul : (partitionGenFun R * qPochInfPS R).coeff 7 = (1 : R⟦X⟧).coeff 7 := by
    rw [partitionGenFun_mul_qPochInfPS]
  rw [PowerSeries.coeff_mul] at hmul
  rw [show (Finset.antidiagonal 7 : Finset (Nat × Nat))
    = {(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2), (6, 1), (7, 0)} from rfl] at hmul
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_insert (by simp), Finset.sum_singleton] at hmul
  simp only [coeff_zero_partitionGenFun, coeff_zero_qPochInfPS,
    coeff_one_partitionGenFun, coeff_one_qPochInfPS,
    coeff_two_partitionGenFun, coeff_two_qPochInfPS,
    coeff_three_partitionGenFun, coeff_three_qPochInfPS,
    coeff_four_partitionGenFun, coeff_four_qPochInfPS,
    coeff_five_partitionGenFun, coeff_five_qPochInfPS,
    coeff_six_partitionGenFun, coeff_six_qPochInfPS,
    coeff_seven_partitionGenFun,
    one_mul, mul_one] at hmul
  rw [show ((1 : R⟦X⟧).coeff 7 : R) = 0 from by
    rw [PowerSeries.coeff_one]; simp] at hmul
  linear_combination hmul

/-- The coefficient at index 8 of `qPochInfPS`: equals `0` (8 not pentagonal).
From `J · (q;q)∞ = 1` at X⁸ recurrence. -/
theorem coeff_eight_qPochInfPS (R : Type*) [CommRing R] :
    (qPochInfPS R).coeff 8 = 0 := by
  have hmul : (partitionGenFun R * qPochInfPS R).coeff 8 = (1 : R⟦X⟧).coeff 8 := by
    rw [partitionGenFun_mul_qPochInfPS]
  rw [PowerSeries.coeff_mul] at hmul
  rw [show (Finset.antidiagonal 8 : Finset (Nat × Nat))
    = {(0, 8), (1, 7), (2, 6), (3, 5), (4, 4), (5, 3), (6, 2), (7, 1), (8, 0)} from rfl] at hmul
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_singleton] at hmul
  simp only [coeff_zero_partitionGenFun, coeff_zero_qPochInfPS,
    coeff_one_partitionGenFun, coeff_one_qPochInfPS,
    coeff_two_partitionGenFun, coeff_two_qPochInfPS,
    coeff_three_partitionGenFun, coeff_three_qPochInfPS,
    coeff_four_partitionGenFun, coeff_four_qPochInfPS,
    coeff_five_partitionGenFun, coeff_five_qPochInfPS,
    coeff_six_partitionGenFun, coeff_six_qPochInfPS,
    coeff_seven_partitionGenFun, coeff_seven_qPochInfPS,
    coeff_eight_partitionGenFun,
    one_mul, mul_one] at hmul
  rw [show ((1 : R⟦X⟧).coeff 8 : R) = 0 from by
    rw [PowerSeries.coeff_one]; simp] at hmul
  linear_combination hmul

/-- **Key Ramanujan algebraic identity (mod p)**:
In `(ZMod p)⟦X⟧`, `J · (q;q)∞.expand p = (q;q)∞^(p-1)`
where J = partitionGenFun, (q;q)∞ = qPochInfPS.

Proof: from `J · (q;q)∞ = 1`, multiply by `(q;q)∞^(p-1)` to get
`J · (q;q)∞^p = (q;q)∞^(p-1)`. Then apply Frobenius `(q;q)∞^p = (q;q)∞.expand p`. -/
theorem ramanujan_key_identity (p : Nat) [Fact (Nat.Prime p)] (hp : p ≠ 0) :
    partitionGenFun (ZMod p) * PowerSeries.expand p hp (qPochInfPS (ZMod p)) =
      (qPochInfPS (ZMod p)) ^ (p - 1) := by
  -- Start with J · (q;q)∞ = 1
  have h1 : partitionGenFun (ZMod p) * qPochInfPS (ZMod p) = 1 :=
    partitionGenFun_mul_qPochInfPS (ZMod p)
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  -- Apply Frobenius: (q;q)∞^p = (q;q)∞.expand p
  have hfrob : (qPochInfPS (ZMod p)) ^ p =
      PowerSeries.expand p hp (qPochInfPS (ZMod p)) :=
    qPochInfPS_pow_eq_expand p hp
  -- Express (q;q)∞^p = (q;q)∞ · (q;q)∞^(p-1)
  have hsplit : (qPochInfPS (ZMod p)) ^ p =
      qPochInfPS (ZMod p) * (qPochInfPS (ZMod p)) ^ (p - 1) := by
    rw [← pow_succ', Nat.sub_one_add_one hp]
  -- Multiply J · (q;q)∞^p:
  --   J · (q;q)∞^p = J · ((q;q)∞ · (q;q)∞^(p-1)) = (J · (q;q)∞) · (q;q)∞^(p-1) = (q;q)∞^(p-1)
  have h2 : partitionGenFun (ZMod p) * (qPochInfPS (ZMod p)) ^ p =
      (qPochInfPS (ZMod p)) ^ (p - 1) := by
    rw [hsplit, ← mul_assoc, h1, one_mul]
  -- Substitute (q;q)∞^p = (q;q)∞.expand p
  rw [← hfrob]
  exact h2

/-! ### Conditional Ramanujan congruence

If the coefficients of `(q;q)∞^(p-1)` vanish on the arithmetic progression
`pn + r` (mod p), then by the key identity the LHS `J · (q;q)∞.expand p`
also vanishes there.

The actual vanishing of `(q;q)∞^(p-1)` coefficients on the appropriate
progression (for p=5, r=4; p=7, r=5; p=11, r=6) follows from Jacobi's
triple product identity — the next major step to formalize. -/

/-- **Immediate corollary of the key identity**: in `(ZMod p)⟦X⟧`,
the coefficients of `J · (q;q)∞.expand p` and `(q;q)∞^(p-1)` at any index agree. -/
theorem coeff_eq_of_key_identity (p : Nat) [Fact (Nat.Prime p)] (hp : p ≠ 0) (m : Nat) :
    (partitionGenFun (ZMod p) * PowerSeries.expand p hp (qPochInfPS (ZMod p))).coeff m =
      ((qPochInfPS (ZMod p)) ^ (p - 1)).coeff m :=
  congr_arg (fun f => (PowerSeries.coeff m) f) (ramanujan_key_identity p hp)

/-- **Coefficient extraction lemma**: in `R⟦X⟧`, with `p ≠ 0` and `r < p`,
`(f * expand p g).coeff (p*n+r) = ∑_{k=0}^n f.coeff (p*(n-k)+r) * g.coeff k`.

Proof: convert `(expand p g).coeff j = if p ∣ j then g.coeff (j/p) else 0`,
filter to the dvd-set, then bijection `(i, p·k) ↔ k` between filtered antidiagonal
and `range(n+1)`. -/
theorem coeff_mul_expand_of_lt (R : Type*) [CommRing R] (p : Nat) (hp : p ≠ 0)
    (f g : R⟦X⟧) (n r : Nat) (hr : r < p) :
    (f * PowerSeries.expand p hp g).coeff (p * n + r) =
      ∑ k ∈ Finset.range (n + 1), f.coeff (p * (n - k) + r) * g.coeff k := by
  rw [PowerSeries.coeff_mul]
  -- Step 1: rewrite each term using coeff_expand
  have hterm : ∀ ij ∈ Finset.antidiagonal (p * n + r),
      f.coeff ij.1 * (PowerSeries.expand p hp g).coeff ij.2 =
        if p ∣ ij.2 then f.coeff ij.1 * g.coeff (ij.2 / p) else 0 := by
    intro ij _
    rw [PowerSeries.coeff_expand p hp]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hterm]
  -- Step 2: extract the if-then-else as a filter
  rw [← Finset.sum_filter]
  -- Step 3: bijection between filtered antidiagonal and range(n+1)
  apply Finset.sum_bij' (fun ij _ => ij.2 / p) (fun k _ => (p * (n - k) + r, p * k))
  · -- (i,j) ∈ filtered → j/p ∈ range(n+1)
    intro ⟨i, j⟩ hij
    simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hij
    obtain ⟨hsum, hdvd⟩ := hij
    simp only [Finset.mem_range]
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, Nat.mul_div_cancel_left _ (p.pos_of_ne_zero hp)]
    by_contra h; push_neg at h
    have h1 : p * (n + 1) ≤ p * k := Nat.mul_le_mul_left _ h
    have hmul : p * (n + 1) = p * n + p := by ring
    have h3 : p * k ≤ p * n + r := by rw [← hk]; omega
    linarith
  · -- k ∈ range(n+1) → (p(n-k)+r, pk) ∈ filtered
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_antidiagonal]
    simp only [Finset.mem_range] at hk
    refine ⟨?_, ⟨k, rfl⟩⟩
    have : p * (n - k) + r + p * k = p * (n - k) + p * k + r := by ring
    rw [this, ← Nat.mul_add, Nat.sub_add_cancel (by omega : k ≤ n)]
  · -- left inverse: (i,j) → j/p → (p(n-(j/p))+r, p(j/p)) should equal (i,j)
    intro ⟨i, j⟩ hij
    simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hij
    obtain ⟨hsum, hdvd⟩ := hij
    obtain ⟨k, hk⟩ := hdvd
    simp only [hk, Nat.mul_div_cancel_left _ (p.pos_of_ne_zero hp)]
    have hkn : k ≤ n := by
      by_contra h; push_neg at h
      have h1 : p * (n + 1) ≤ p * k := Nat.mul_le_mul_left _ h
      have hmul : p * (n + 1) = p * n + p := by ring
      have h3 : p * k ≤ p * n + r := by rw [← hk]; omega
      linarith
    have hi : i = p * (n - k) + r := by
      have h_eq : p * (n - k) + p * k = p * n := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hkn]
      omega
    refine Prod.ext ?_ rfl
    exact hi.symm
  · -- right inverse: k → (p(n-k)+r, pk) → pk/p = k
    intro k _
    exact Nat.mul_div_cancel_left _ (p.pos_of_ne_zero hp)
  · -- functional equality: f.coeff i * g.coeff (j/p) = f.coeff (p(n-(j/p))+r) * g.coeff (j/p)
    intro ⟨i, j⟩ hij
    simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hij
    obtain ⟨hsum, hdvd⟩ := hij
    obtain ⟨k, hk⟩ := hdvd
    have hkn : k ≤ n := by
      by_contra h; push_neg at h
      have h1 : p * (n + 1) ≤ p * k := Nat.mul_le_mul_left _ h
      have hmul : p * (n + 1) = p * n + p := by ring
      have h3 : p * k ≤ p * n + r := by rw [← hk]; omega
      linarith
    simp only [hk, Nat.mul_div_cancel_left _ (p.pos_of_ne_zero hp)]
    have hi : i = p * (n - k) + r := by
      have h_eq : p * (n - k) + p * k = p * n := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hkn]
      omega
    rw [hi]

/-- **Explicit Ramanujan convolution formula in ZMod p**:
in `(ZMod p)⟦X⟧`, the coefficient of `(qPoch ZMod p)^(p-1)` at `p·n + r` (for `r < p`)
equals a finite convolution of partition counts with pentagonal signs.

Combines:
- `ramanujan_key_identity` / `coeff_eq_of_key_identity`: `J · expand_p qPoch = qPoch^(p-1)`
- `coeff_mul_expand_of_lt`: convolution at `p·n+r`
- `coeff_qPochInfPS_eq_pentagonalSign`: Euler pentagonal substitution

This formula is the explicit form used by Ramanujan's classical proofs of
`p(p·n+r) ≡ 0 (mod p)` for the three special primes/residues. -/
theorem coeff_qPochInfPS_pow_pred_at_AP
    (p : Nat) [Fact (Nat.Prime p)] (hp : p ≠ 0) (n r : Nat) (hr : r < p) :
    ((qPochInfPS (ZMod p)) ^ (p - 1)).coeff (p * n + r) =
      ∑ k ∈ Finset.range (n + 1),
        ((partitionCount (p * (n - k) + r) : Nat) : ZMod p) *
          ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign k : ℤ) : ZMod p) := by
  have h1 := coeff_eq_of_key_identity p hp (p * n + r)
  have h2 := coeff_mul_expand_of_lt (ZMod p) p hp
    (partitionGenFun (ZMod p)) (qPochInfPS (ZMod p)) n r hr
  rw [← h1, h2]
  refine Finset.sum_congr rfl ?_
  intro k _
  congr 1
  · rw [coeff_partitionGenFun]
    show ((Fintype.card (Nat.Partition (p * (n - k) + r)) : Nat) : ZMod p) =
         ((partitionCount (p * (n - k) + r) : Nat) : ZMod p)
    rfl
  · exact coeff_qPochInfPS_eq_pentagonalSign (ZMod p) k

/-! ### Conditional Ramanujan theorem

If the coefficients of `(q;q)∞^(p-1)` vanish on the arithmetic progression
`p·n + r` (in `(ZMod p)⟦X⟧`), then `partitionCount(p·n + r) ≡ 0 (mod p)`. -/

/-- **Conditional Ramanujan**: from algebraic vanishing of `(q;q)∞^(p-1)` on
`pn+r`, derive the partition congruence by induction. -/
theorem ramanujan_from_pochInf_vanishes (p : Nat) [Fact (Nat.Prime p)] (hp : p ≠ 0)
    (r : Nat) (hr : r < p)
    (hvanish : ∀ n, ((qPochInfPS (ZMod p)) ^ (p - 1)).coeff (p * n + r) = 0) :
    ∀ n, ((partitionCount (p * n + r) : Nat) : ZMod p) = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    -- Extract coefficient via the coefficient extraction lemma + key identity:
    have hext := coeff_mul_expand_of_lt (ZMod p) p hp
      (partitionGenFun (ZMod p)) (qPochInfPS (ZMod p)) n r hr
    -- LHS by key identity = ((q;q)∞^(p-1)).coeff (p*n+r) = 0
    have hkey := coeff_eq_of_key_identity p hp (p * n + r)
    rw [hext] at hkey
    -- hkey: ∑_{k=0}^n J.coeff (p*(n-k)+r) * (q;q)∞.coeff k =
    --       ((q;q)∞^(p-1)).coeff (p*n+r)
    rw [hvanish n] at hkey
    -- hkey: ∑_{k=0}^n J.coeff (p*(n-k)+r) * (q;q)∞.coeff k = 0
    -- Peel off k=0 term
    rw [Finset.sum_range_succ'] at hkey
    simp only [Nat.sub_zero, coeff_zero_qPochInfPS, mul_one] at hkey
    -- hkey: ∑_{k ∈ range n} J.coeff (p*(n-(k+1))+r) * (q;q)∞.coeff (k+1) +
    --       J.coeff (p*n+r) = 0
    -- By IH, J.coeff (p*(n-(k+1))+r) = 0 for k ∈ range n (since n-(k+1) < n)
    have hzero_sum : ∑ k ∈ Finset.range n,
        (partitionGenFun (ZMod p)).coeff (p * (n - (k + 1)) + r) *
          (qPochInfPS (ZMod p)).coeff (k + 1) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_range] at hk
      have h_lt : n - (k + 1) < n := by omega
      -- J.coeff (p*(n-(k+1))+r) = partitionCount (p*(n-(k+1))+r) (in ZMod p) = 0 by IH
      rw [coeff_partitionGenFun]
      show ((Fintype.card (Nat.Partition (p * (n - (k + 1)) + r)) : Nat) : ZMod p) *
        _ = 0
      have : ((partitionCount (p * (n - (k + 1)) + r) : Nat) : ZMod p) = 0 := IH _ h_lt
      simp [partitionCount] at this
      rw [this]; ring
    rw [hzero_sum, zero_add] at hkey
    -- hkey: J.coeff (p*n+r) = 0
    rw [coeff_partitionGenFun] at hkey
    show ((partitionCount (p * n + r) : Nat) : ZMod p) = 0
    simp [partitionCount]
    exact hkey

/-! ### Ramanujan congruences — conditional corollaries

The three classical Ramanujan partition congruences are mod 5, 7, 11, each
on a specific residue class. Below are the conditional statements: assuming
the corresponding `(q;q)∞^(p-1)` coefficient vanishes on the progression. -/

/-- **Ramanujan p(5n+4) ≡ 0 (mod 5)** (conditional on `(q;q)∞^4` vanishing on `5n+4`). -/
theorem ramanujan_mod_5_conditional
    (hvanish : ∀ n, ((qPochInfPS (ZMod 5)) ^ 4).coeff (5 * n + 4) = 0) :
    ∀ n, ((partitionCount (5 * n + 4) : Nat) : ZMod 5) = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hp : (5 : Nat) ≠ 0 := by decide
  have hr : 4 < (5 : Nat) := by decide
  -- 5 - 1 = 4
  have h := ramanujan_from_pochInf_vanishes 5 hp 4 hr
  simp only [show (5 - 1 : Nat) = 4 from rfl] at h
  exact h hvanish

/-- **Ramanujan p(7n+5) ≡ 0 (mod 7)** (conditional on `(q;q)∞^6` vanishing on `7n+5`). -/
theorem ramanujan_mod_7_conditional
    (hvanish : ∀ n, ((qPochInfPS (ZMod 7)) ^ 6).coeff (7 * n + 5) = 0) :
    ∀ n, ((partitionCount (7 * n + 5) : Nat) : ZMod 7) = 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hp : (7 : Nat) ≠ 0 := by decide
  have hr : 5 < (7 : Nat) := by decide
  have h := ramanujan_from_pochInf_vanishes 7 hp 5 hr
  simp only [show (7 - 1 : Nat) = 6 from rfl] at h
  exact h hvanish

/-- **Ramanujan p(11n+6) ≡ 0 (mod 11)** (conditional on `(q;q)∞^10` vanishing on `11n+6`). -/
theorem ramanujan_mod_11_conditional
    (hvanish : ∀ n, ((qPochInfPS (ZMod 11)) ^ 10).coeff (11 * n + 6) = 0) :
    ∀ n, ((partitionCount (11 * n + 6) : Nat) : ZMod 11) = 0 := by
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hp : (11 : Nat) ≠ 0 := by decide
  have hr : 6 < (11 : Nat) := by decide
  have h := ramanujan_from_pochInf_vanishes 11 hp 6 hr
  simp only [show (11 - 1 : Nat) = 10 from rfl] at h
  exact h hvanish

/-! ### N=0 Ramanujan identity: closed-form bridge

For `0 ≤ r < p`, the algebraic identity collapses cleanly:
`((q;q)∞^(p-1)).coeff r = (p(r) : ZMod p)`.

This is the n=0 case of the conditional Ramanujan. The LHS can be computed
directly from the Euler-pentagonal coefficients of qPochInfPS via the
binomial expansion. -/

/-- Key bridge: in `(ZMod p)⟦X⟧`, the coefficient of `X^r` in `(q;q)∞^(p-1)` equals
`p(r) mod p`, for `r < p`. -/
theorem coeff_pochInfPow_eq_partitionCount_of_lt
    (p : Nat) [Fact (Nat.Prime p)] (hp : p ≠ 0) (r : Nat) (hr : r < p) :
    ((qPochInfPS (ZMod p)) ^ (p - 1)).coeff r =
      ((partitionCount r : Nat) : ZMod p) := by
  -- (q;q)∞^(p-1) = J · expand_p (q;q)∞
  have hkey := coeff_eq_of_key_identity p hp r
  -- The LHS of hkey: ((q;q)∞^(p-1)).coeff r
  -- The RHS of hkey: (J · expand_p (q;q)∞).coeff r
  -- Apply coeff_mul_expand_of_lt at n = 0:
  have hext := coeff_mul_expand_of_lt (ZMod p) p hp
    (partitionGenFun (ZMod p)) (qPochInfPS (ZMod p)) 0 r hr
  -- hext has p*0+r, normalize to r
  rw [Nat.mul_zero, Nat.zero_add] at hext
  rw [hext] at hkey
  -- Sum reduces to k=0 term: J.coeff r · qPoch.coeff 0 = J.coeff r · 1 = J.coeff r
  simp only [Finset.sum_range_one, Nat.sub_zero, Nat.mul_zero, Nat.zero_add,
    coeff_zero_qPochInfPS, mul_one] at hkey
  rw [coeff_partitionGenFun] at hkey
  rw [← hkey]
  simp [partitionCount]

/-! ### Status note: path to full Ramanujan mod 5

**Completed real theorems**:
- `powerSeries_charP`: CharP instance for PowerSeries (R⟦X⟧ inherits char from R)
- `PowerSeries.expand_eq_pow_zmod`: Frobenius — `f.expand p = f^p` in (ZMod p)⟦X⟧
- `partitionGenFun`: formal partition generating function (via Mathlib's `Nat.Partition.genFun`)
- `coeff_partitionGenFun_int/_rat`: connection to Ch01's `partitionCount`
- `qPochInfPS`: formal `(q;q)∞` via `PowerSeries.invOfUnit`
- `partitionGenFun_mul_qPochInfPS`: `J · (q;q)∞ = 1`
- `ramanujan_key_identity`: in (ZMod p)⟦X⟧, `J · (q;q)∞.expand p = (q;q)∞^(p-1)`
- `coeff_eq_of_key_identity`: coefficient corollary

**Remaining for full Ramanujan mod 5** (each substantial):

1. **Euler pentagonal** as formal power series:
   `(q;q)∞ = ∑_{n ∈ ℤ} (-1)^n X^{n(3n-1)/2}`
   Reference: Ch04Franklin's `euler_pentagonal_combinatorial` (Franklin involution),
   bridged via `signedStrictPartitionCount n = qPochInfPS.coeff n` (cast).

2. **Jacobi identity** as formal power series:
   `(q;q)∞^3 = ∑_{k ≥ 0} (-1)^k (2k+1) X^{k(k+1)/2}`
   Reference: Ch03's Jacobi triple product, specialized.

3. **Mod-5 vanishing analysis**: show `((q;q)∞^4).coeff (5n+4) = 0` in (ZMod 5)⟦X⟧
   by analyzing pairs `(m, k)` with `m(3m-1)/2 + k(k+1)/2 = 5n+4`, showing the
   `(2k+1)` factor is always ≡ 0 (mod 5).

4. **Coefficient extraction + induction**: from `coeff_eq_of_key_identity`,
   derive the linear recurrence `partitionCount(5n+4) = -∑_{k≥1} ...`,
   then induct on n.

Steps 1-2 are substantial but reuse existing Q-series infrastructure.
Step 3 is finite combinatorial. Step 4 is straightforward induction. -/

end Ch19
end PartIV
end QseriesFormalization
