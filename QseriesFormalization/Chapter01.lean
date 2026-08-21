import QseriesFormalization.Basic
import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# Chapter 1: Introduction

(Hei-Chi Chan, *An Invitation to q-Series*, Ch 1.)

Most of the introductory material—partitions, triangular numbers,
the q-Pochhammer symbol—lives in `QseriesFormalization.Basic`.
This file collects any chapter-specific lemmas that are too lightweight
to belong in `Basic.lean` but that the introduction relies on.

Currently empty; populated as we work through Chapter 1.
-/

namespace QseriesFormalization
namespace Ch01

/-- The partition function `p(n)` (Chan Def 1.1, Eq 1.8). -/
def partitionCount (n : Nat) : Nat := Fintype.card (Nat.Partition n)

/-- The generalized pentagonal number `k(3k-1)/2`. -/
def pentagonalLower (k : Nat) : Nat := k * (3 * k - 1) / 2

/-- The generalized pentagonal number `k(3k+1)/2`. -/
def pentagonalUpper (k : Nat) : Nat := k * (3 * k + 1) / 2

/-- One Euler pentagonal recurrence step, evaluated from a table of earlier values. -/
private def partitionCountRecFrom (values : List Nat) (n : Nat) : Nat :=
  let term (j : Nat) : Int :=
    let k := j + 1
    let subtotal : Nat :=
      (if pentagonalLower k ≤ n then values.getD (n - pentagonalLower k) 0 else 0) +
      (if pentagonalUpper k ≤ n then values.getD (n - pentagonalUpper k) 0 else 0)
    if k % 2 = 1 then (subtotal : Int) else -((subtotal : Int))
  Int.toNat ((Finset.range n).sum term)

/-- Table of values produced by Euler's pentagonal recurrence through index `n`. -/
private def partitionCountRecTable : Nat → List Nat
  | 0 => [1]
  | Nat.succ n =>
      let previous := partitionCountRecTable n
      previous ++ [partitionCountRecFrom previous (n + 1)]

/-- Pentagonal recurrence value at `n`, computed from the finite table of earlier values. -/
def partitionCountRec (n : Nat) : Nat :=
  (partitionCountRecTable n).getD n 0

private def partitionOfParts (n : Nat) (parts : Multiset Nat)
    (parts_pos : ∀ {i}, i ∈ parts → 0 < i) (parts_sum : parts.sum = n) :
    Nat.Partition n where
  parts := parts
  parts_pos := parts_pos
  parts_sum := parts_sum


private def partitionOfPartsChecked (n : Nat) (parts : Multiset Nat) : Nat.Partition n :=
  if h : (∀ {i}, i ∈ parts → 0 < i) ∧ parts.sum = n then
    partitionOfParts n parts h.1 h.2
  else
    Nat.Partition.indiscrete n

private def partitionTwo : Nat.Partition 2 :=
  partitionOfParts 2 {2} (by simp) (by norm_num)

private def partitionOneOne : Nat.Partition 2 :=
  partitionOfParts 2 {1, 1} (by simp) (by norm_num)

private def partitionThree : Nat.Partition 3 :=
  partitionOfParts 3 {3} (by simp) (by norm_num)

private def partitionTwoOne : Nat.Partition 3 :=
  partitionOfParts 3 {1, 2} (by simp) (by norm_num)

private def partitionOneOneOne : Nat.Partition 3 :=
  partitionOfParts 3 {1, 1, 1} (by simp) (by norm_num)

private def partitionFour : Nat.Partition 4 :=
  partitionOfParts 4 {4} (by simp) (by norm_num)

private def partitionThreeOne : Nat.Partition 4 :=
  partitionOfParts 4 {1, 3} (by simp) (by norm_num)

private def partitionTwoTwo : Nat.Partition 4 :=
  partitionOfParts 4 {2, 2} (by simp) (by norm_num)

private def partitionTwoOneOne : Nat.Partition 4 :=
  partitionOfParts 4 {1, 1, 2} (by simp) (by norm_num)

private def partitionOneOneOneOne : Nat.Partition 4 :=
  partitionOfParts 4 {1, 1, 1, 1} (by simp) (by norm_num)

private def partitionFive : Nat.Partition 5 :=
  partitionOfParts 5 {5} (by simp) (by norm_num)

private def partitionFourOne : Nat.Partition 5 :=
  partitionOfParts 5 {1, 4} (by simp) (by norm_num)

private def partitionThreeTwo : Nat.Partition 5 :=
  partitionOfParts 5 {2, 3} (by simp) (by norm_num)

private def partitionThreeOneOne : Nat.Partition 5 :=
  partitionOfParts 5 {1, 1, 3} (by simp) (by norm_num)

private def partitionTwoTwoOne : Nat.Partition 5 :=
  partitionOfParts 5 {1, 2, 2} (by simp) (by norm_num)

private def partitionTwoOneOneOne : Nat.Partition 5 :=
  partitionOfParts 5 {1, 1, 1, 2} (by simp) (by norm_num)

private def partitionOneOneOneOneOne : Nat.Partition 5 :=
  partitionOfParts 5 {1, 1, 1, 1, 1} (by simp) (by norm_num)

private def partitionSix : Nat.Partition 6 :=
  partitionOfParts 6 {6} (by simp) (by norm_num)

private def partitionFiveOne : Nat.Partition 6 :=
  partitionOfParts 6 {1, 5} (by simp) (by norm_num)

private def partitionFourTwo : Nat.Partition 6 :=
  partitionOfParts 6 {2, 4} (by simp) (by norm_num)

private def partitionFourOneOne : Nat.Partition 6 :=
  partitionOfParts 6 {1, 1, 4} (by simp) (by norm_num)

private def partitionThreeThree : Nat.Partition 6 :=
  partitionOfParts 6 {3, 3} (by simp) (by norm_num)

private def partitionThreeTwoOne : Nat.Partition 6 :=
  partitionOfParts 6 {1, 2, 3} (by simp) (by norm_num)

private def partitionThreeOneOneOne : Nat.Partition 6 :=
  partitionOfParts 6 {1, 1, 1, 3} (by simp) (by norm_num)

private def partitionTwoTwoTwo : Nat.Partition 6 :=
  partitionOfParts 6 {2, 2, 2} (by simp) (by norm_num)

private def partitionTwoTwoOneOne : Nat.Partition 6 :=
  partitionOfParts 6 {1, 1, 2, 2} (by simp) (by norm_num)

private def partitionTwoOneOneOneOne : Nat.Partition 6 :=
  partitionOfParts 6 {1, 1, 1, 1, 2} (by simp) (by norm_num)

private def partitionOneOneOneOneOneOne : Nat.Partition 6 :=
  partitionOfParts 6 {1, 1, 1, 1, 1, 1} (by simp) (by norm_num)

private def partitionSeven : Nat.Partition 7 :=
  partitionOfParts 7 {7} (by simp) (by norm_num)

private def partitionSixOne : Nat.Partition 7 :=
  partitionOfParts 7 {1, 6} (by simp) (by norm_num)

private def partitionFiveTwo : Nat.Partition 7 :=
  partitionOfParts 7 {2, 5} (by simp) (by norm_num)

private def partitionFiveOneOne : Nat.Partition 7 :=
  partitionOfParts 7 {1, 1, 5} (by simp) (by norm_num)

private def partitionFourThree : Nat.Partition 7 :=
  partitionOfParts 7 {3, 4} (by simp) (by norm_num)

private def partitionFourTwoOne : Nat.Partition 7 :=
  partitionOfParts 7 {1, 2, 4} (by simp) (by norm_num)

private def partitionFourOneOneOne : Nat.Partition 7 :=
  partitionOfParts 7 {1, 1, 1, 4} (by simp) (by norm_num)

private def partitionThreeThreeOne : Nat.Partition 7 :=
  partitionOfParts 7 {1, 3, 3} (by simp) (by norm_num)

private def partitionThreeTwoTwo : Nat.Partition 7 :=
  partitionOfParts 7 {2, 2, 3} (by simp) (by norm_num)

private def partitionThreeTwoOneOne : Nat.Partition 7 :=
  partitionOfParts 7 {1, 1, 2, 3} (by simp) (by norm_num)

private def partitionThreeOneOneOneOne : Nat.Partition 7 :=
  partitionOfParts 7 {1, 1, 1, 1, 3} (by simp) (by norm_num)

private def partitionTwoTwoTwoOne : Nat.Partition 7 :=
  partitionOfParts 7 {1, 2, 2, 2} (by simp) (by norm_num)

private def partitionTwoTwoOneOneOne : Nat.Partition 7 :=
  partitionOfParts 7 {1, 1, 1, 2, 2} (by simp) (by norm_num)

private def partitionTwoOneOneOneOneOne : Nat.Partition 7 :=
  partitionOfParts 7 {1, 1, 1, 1, 1, 2} (by simp) (by norm_num)

private def partitionOneOneOneOneOneOneOne : Nat.Partition 7 :=
  partitionOfParts 7 {1, 1, 1, 1, 1, 1, 1} (by simp) (by norm_num)

private def partitionEight : Nat.Partition 8 :=
  partitionOfParts 8 {8} (by simp) (by norm_num)

private def partitionSevenOne : Nat.Partition 8 :=
  partitionOfParts 8 {1, 7} (by simp) (by norm_num)

private def partitionSixTwo : Nat.Partition 8 :=
  partitionOfParts 8 {2, 6} (by simp) (by norm_num)

private def partitionSixOneOne : Nat.Partition 8 :=
  partitionOfParts 8 {1, 1, 6} (by simp) (by norm_num)

private def partitionFiveThree : Nat.Partition 8 :=
  partitionOfParts 8 {3, 5} (by simp) (by norm_num)

private def partitionFiveTwoOne : Nat.Partition 8 :=
  partitionOfParts 8 {1, 2, 5} (by simp) (by norm_num)

private def partitionFiveOneOneOne : Nat.Partition 8 :=
  partitionOfParts 8 {1, 1, 1, 5} (by simp) (by norm_num)

private def partitionFourFour : Nat.Partition 8 :=
  partitionOfParts 8 {4, 4} (by simp) (by norm_num)

private def partitionFourThreeOne : Nat.Partition 8 :=
  partitionOfParts 8 {1, 3, 4} (by simp) (by norm_num)

private def partitionFourTwoTwo : Nat.Partition 8 :=
  partitionOfParts 8 {2, 2, 4} (by simp) (by norm_num)

private def partitionFourTwoOneOne : Nat.Partition 8 :=
  partitionOfParts 8 {1, 1, 2, 4} (by simp) (by norm_num)

private def partitionFourOneOneOneOne : Nat.Partition 8 :=
  partitionOfParts 8 {1, 1, 1, 1, 4} (by simp) (by norm_num)

private def partitionThreeThreeTwo : Nat.Partition 8 :=
  partitionOfParts 8 {2, 3, 3} (by simp) (by norm_num)

private def partitionThreeThreeOneOne : Nat.Partition 8 :=
  partitionOfParts 8 {1, 1, 3, 3} (by simp) (by norm_num)

private def partitionThreeTwoTwoOne : Nat.Partition 8 :=
  partitionOfParts 8 {1, 2, 2, 3} (by simp) (by norm_num)

private def partitionThreeTwoOneOneOne : Nat.Partition 8 :=
  partitionOfParts 8 {1, 1, 1, 2, 3} (by simp) (by norm_num)

private def partitionThreeOneOneOneOneOne : Nat.Partition 8 :=
  partitionOfParts 8 {1, 1, 1, 1, 1, 3} (by simp) (by norm_num)

private def partitionTwoTwoTwoTwo : Nat.Partition 8 :=
  partitionOfParts 8 {2, 2, 2, 2} (by simp) (by norm_num)

private def partitionTwoTwoTwoOneOne : Nat.Partition 8 :=
  partitionOfParts 8 {1, 1, 2, 2, 2} (by simp) (by norm_num)

private def partitionTwoTwoOneOneOneOne : Nat.Partition 8 :=
  partitionOfParts 8 {1, 1, 1, 1, 2, 2} (by simp) (by norm_num)

private def partitionTwoOneOneOneOneOneOne : Nat.Partition 8 :=
  partitionOfParts 8 {1, 1, 1, 1, 1, 1, 2} (by simp) (by norm_num)

private def partitionOneOneOneOneOneOneOneOne : Nat.Partition 8 :=
  partitionOfParts 8 {1, 1, 1, 1, 1, 1, 1, 1} (by simp) (by norm_num)

private def partitionNine : Nat.Partition 9 :=
  partitionOfParts 9 {9} (by simp) (by norm_num)

private def partitionEightOne : Nat.Partition 9 :=
  partitionOfParts 9 {1, 8} (by simp) (by norm_num)

private def partitionSevenTwo : Nat.Partition 9 :=
  partitionOfParts 9 {2, 7} (by simp) (by norm_num)

private def partitionSevenOneOne : Nat.Partition 9 :=
  partitionOfParts 9 {1, 1, 7} (by simp) (by norm_num)

private def partitionSixThree : Nat.Partition 9 :=
  partitionOfParts 9 {3, 6} (by simp) (by norm_num)

private def partitionSixTwoOne : Nat.Partition 9 :=
  partitionOfParts 9 {1, 2, 6} (by simp) (by norm_num)

private def partitionSixOneOneOne : Nat.Partition 9 :=
  partitionOfParts 9 {1, 1, 1, 6} (by simp) (by norm_num)

private def partitionFiveFour : Nat.Partition 9 :=
  partitionOfParts 9 {4, 5} (by simp) (by norm_num)

private def partitionFiveThreeOne : Nat.Partition 9 :=
  partitionOfParts 9 {1, 3, 5} (by simp) (by norm_num)

private def partitionFiveTwoTwo : Nat.Partition 9 :=
  partitionOfParts 9 {2, 2, 5} (by simp) (by norm_num)

private def partitionFiveTwoOneOne : Nat.Partition 9 :=
  partitionOfParts 9 {1, 1, 2, 5} (by simp) (by norm_num)

private def partitionFiveOneOneOneOne : Nat.Partition 9 :=
  partitionOfParts 9 {1, 1, 1, 1, 5} (by simp) (by norm_num)

private def partitionFourFourOne : Nat.Partition 9 :=
  partitionOfParts 9 {1, 4, 4} (by simp) (by norm_num)

private def partitionFourThreeTwo : Nat.Partition 9 :=
  partitionOfParts 9 {2, 3, 4} (by simp) (by norm_num)

private def partitionFourThreeOneOne : Nat.Partition 9 :=
  partitionOfParts 9 {1, 1, 3, 4} (by simp) (by norm_num)

private def partitionFourTwoTwoOne : Nat.Partition 9 :=
  partitionOfParts 9 {1, 2, 2, 4} (by simp) (by norm_num)

private def partitionFourTwoOneOneOne : Nat.Partition 9 :=
  partitionOfParts 9 {1, 1, 1, 2, 4} (by simp) (by norm_num)

private def partitionFourOneOneOneOneOne : Nat.Partition 9 :=
  partitionOfParts 9 {1, 1, 1, 1, 1, 4} (by simp) (by norm_num)

private def partitionThreeThreeThree : Nat.Partition 9 :=
  partitionOfParts 9 {3, 3, 3} (by simp) (by norm_num)

private def partitionThreeThreeTwoOne : Nat.Partition 9 :=
  partitionOfParts 9 {1, 2, 3, 3} (by simp) (by norm_num)

private def partitionThreeThreeOneOneOne : Nat.Partition 9 :=
  partitionOfParts 9 {1, 1, 1, 3, 3} (by simp) (by norm_num)

private def partitionThreeTwoTwoTwo : Nat.Partition 9 :=
  partitionOfParts 9 {2, 2, 2, 3} (by simp) (by norm_num)

private def partitionThreeTwoTwoOneOne : Nat.Partition 9 :=
  partitionOfParts 9 {1, 1, 2, 2, 3} (by simp) (by norm_num)

private def partitionThreeTwoOneOneOneOne : Nat.Partition 9 :=
  partitionOfParts 9 {1, 1, 1, 1, 2, 3} (by simp) (by norm_num)

private def partitionThreeOneOneOneOneOneOne : Nat.Partition 9 :=
  partitionOfParts 9 {1, 1, 1, 1, 1, 1, 3} (by simp) (by norm_num)

private def partitionTwoTwoTwoTwoOne : Nat.Partition 9 :=
  partitionOfParts 9 {1, 2, 2, 2, 2} (by simp) (by norm_num)

private def partitionTwoTwoTwoOneOneOne : Nat.Partition 9 :=
  partitionOfParts 9 {1, 1, 1, 2, 2, 2} (by simp) (by norm_num)

private def partitionTwoTwoOneOneOneOneOne : Nat.Partition 9 :=
  partitionOfParts 9 {1, 1, 1, 1, 1, 2, 2} (by simp) (by norm_num)

private def partitionTwoOneOneOneOneOneOneOne : Nat.Partition 9 :=
  partitionOfParts 9 {1, 1, 1, 1, 1, 1, 1, 2} (by simp) (by norm_num)

private def partitionOneOneOneOneOneOneOneOneOne : Nat.Partition 9 :=
  partitionOfParts 9 {1, 1, 1, 1, 1, 1, 1, 1, 1} (by simp) (by norm_num)

private def partitionTen : Nat.Partition 10 :=
  partitionOfParts 10 {10} (by simp) (by norm_num)

private def partitionNineOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 9} (by simp) (by norm_num)

private def partitionEightTwo : Nat.Partition 10 :=
  partitionOfParts 10 {2, 8} (by simp) (by norm_num)

private def partitionEightOneOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 1, 8} (by simp) (by norm_num)

private def partitionSevenThree : Nat.Partition 10 :=
  partitionOfParts 10 {3, 7} (by simp) (by norm_num)

private def partitionSevenTwoOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 2, 7} (by simp) (by norm_num)

private def partitionSevenOneOneOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 1, 1, 7} (by simp) (by norm_num)

private def partitionSixFour : Nat.Partition 10 :=
  partitionOfParts 10 {4, 6} (by simp) (by norm_num)

private def partitionSixThreeOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 3, 6} (by simp) (by norm_num)

private def partitionSixTwoTwo : Nat.Partition 10 :=
  partitionOfParts 10 {2, 2, 6} (by simp) (by norm_num)

private def partitionSixTwoOneOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 1, 2, 6} (by simp) (by norm_num)

private def partitionSixOneOneOneOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 1, 1, 1, 6} (by simp) (by norm_num)

private def partitionFiveFive : Nat.Partition 10 :=
  partitionOfParts 10 {5, 5} (by simp) (by norm_num)

private def partitionFiveFourOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 4, 5} (by simp) (by norm_num)

private def partitionFiveThreeTwo : Nat.Partition 10 :=
  partitionOfParts 10 {2, 3, 5} (by simp) (by norm_num)

private def partitionFiveThreeOneOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 1, 3, 5} (by simp) (by norm_num)

private def partitionFiveTwoTwoOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 2, 2, 5} (by simp) (by norm_num)

private def partitionFiveTwoOneOneOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 1, 1, 2, 5} (by simp) (by norm_num)

private def partitionFiveOneOneOneOneOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 1, 1, 1, 1, 5} (by simp) (by norm_num)

private def partitionFourFourTwo : Nat.Partition 10 :=
  partitionOfParts 10 {2, 4, 4} (by simp) (by norm_num)

private def partitionFourFourOneOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 1, 4, 4} (by simp) (by norm_num)

private def partitionFourThreeThree : Nat.Partition 10 :=
  partitionOfParts 10 {3, 3, 4} (by simp) (by norm_num)

private def partitionFourThreeTwoOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 2, 3, 4} (by simp) (by norm_num)

private def partitionFourThreeOneOneOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 1, 1, 3, 4} (by simp) (by norm_num)

private def partitionFourTwoTwoTwo : Nat.Partition 10 :=
  partitionOfParts 10 {2, 2, 2, 4} (by simp) (by norm_num)

private def partitionFourTwoTwoOneOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 1, 2, 2, 4} (by simp) (by norm_num)

private def partitionFourTwoOneOneOneOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 1, 1, 1, 2, 4} (by simp) (by norm_num)

private def partitionFourOneOneOneOneOneOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 1, 1, 1, 1, 1, 4} (by simp) (by norm_num)

private def partitionThreeThreeThreeOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 3, 3, 3} (by simp) (by norm_num)

private def partitionThreeThreeTwoTwo : Nat.Partition 10 :=
  partitionOfParts 10 {2, 2, 3, 3} (by simp) (by norm_num)

private def partitionThreeThreeTwoOneOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 1, 2, 3, 3} (by simp) (by norm_num)

private def partitionThreeThreeOneOneOneOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 1, 1, 1, 3, 3} (by simp) (by norm_num)

private def partitionThreeTwoTwoTwoOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 2, 2, 2, 3} (by simp) (by norm_num)

private def partitionThreeTwoTwoOneOneOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 1, 1, 2, 2, 3} (by simp) (by norm_num)

private def partitionThreeTwoOneOneOneOneOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 1, 1, 1, 1, 2, 3} (by simp) (by norm_num)

private def partitionThreeOneOneOneOneOneOneOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 1, 1, 1, 1, 1, 1, 3} (by simp) (by norm_num)

private def partitionTwoTwoTwoTwoTwo : Nat.Partition 10 :=
  partitionOfParts 10 {2, 2, 2, 2, 2} (by simp) (by norm_num)

private def partitionTwoTwoTwoTwoOneOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 1, 2, 2, 2, 2} (by simp) (by norm_num)

private def partitionTwoTwoTwoOneOneOneOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 1, 1, 1, 2, 2, 2} (by simp) (by norm_num)

private def partitionTwoTwoOneOneOneOneOneOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 1, 1, 1, 1, 1, 2, 2} (by simp) (by norm_num)

private def partitionTwoOneOneOneOneOneOneOneOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 1, 1, 1, 1, 1, 1, 1, 2} (by simp) (by norm_num)

private def partitionOneOneOneOneOneOneOneOneOneOne : Nat.Partition 10 :=
  partitionOfParts 10 {1, 1, 1, 1, 1, 1, 1, 1, 1, 1} (by simp) (by norm_num)

private lemma partition_parts_card_le {n : Nat} (p : Nat.Partition n) :
    p.parts.card ≤ n := by
  simpa [p.parts_sum] using
    (Multiset.card_nsmul_le_sum (s := p.parts) (a := 1)
      (by intro i hi; exact p.parts_pos hi))

private lemma Multiset.card_eq_five {α : Type*} {s : Multiset α} :
    s.card = 5 ↔ ∃ a b c d e, s = {a, b, c, d, e} :=
  ⟨Quot.inductionOn s fun l h => by
      cases l with
      | nil => simp at h
      | cons a l =>
        cases l with
        | nil => simp at h
        | cons b l =>
          cases l with
          | nil => simp at h
          | cons c l =>
            cases l with
            | nil => simp at h
            | cons d l =>
              cases l with
              | nil => simp at h
              | cons e l =>
                cases l with
                | nil =>
                  exact ⟨a, b, c, d, e, rfl⟩
                | cons f l => simp at h,
    fun ⟨_a, _b, _c, _d, _e, h⟩ => h.symm ▸ rfl⟩

private lemma Multiset.card_eq_six {α : Type*} {s : Multiset α} :
    s.card = 6 ↔ ∃ a b c d e f, s = {a, b, c, d, e, f} :=
  ⟨Quot.inductionOn s fun l h => by
      cases l with
      | nil => simp at h
      | cons a l =>
        cases l with
        | nil => simp at h
        | cons b l =>
          cases l with
          | nil => simp at h
          | cons c l =>
            cases l with
            | nil => simp at h
            | cons d l =>
              cases l with
              | nil => simp at h
              | cons e l =>
                cases l with
                | nil => simp at h
                | cons f l =>
                  cases l with
                  | nil =>
                    exact ⟨a, b, c, d, e, f, rfl⟩
                  | cons g l => simp at h,
    fun ⟨_a, _b, _c, _d, _e, _f, h⟩ => h.symm ▸ rfl⟩

private lemma Multiset.card_eq_seven {α : Type*} {s : Multiset α} :
    s.card = 7 ↔ ∃ a b c d e f g, s = {a, b, c, d, e, f, g} :=
  ⟨Quot.inductionOn s fun l hcard => by
      cases l with
      | nil => simp at hcard
      | cons a l =>
        cases l with
        | nil => simp at hcard
        | cons b l =>
          cases l with
          | nil => simp at hcard
          | cons c l =>
            cases l with
            | nil => simp at hcard
            | cons d l =>
              cases l with
              | nil => simp at hcard
              | cons e l =>
                cases l with
                | nil => simp at hcard
                | cons f l =>
                  cases l with
                  | nil => simp at hcard
                  | cons g l =>
                    cases l with
                    | nil =>
                      exact ⟨a, b, c, d, e, f, g, rfl⟩
                    | cons h l => simp at hcard,
    fun ⟨_a, _b, _c, _d, _e, _f, _g, h⟩ => h.symm ▸ rfl⟩

private lemma Multiset.card_eq_eight {α : Type*} {s : Multiset α} :
    s.card = 8 ↔ ∃ a b c d e f g h, s = {a, b, c, d, e, f, g, h} :=
  ⟨Quot.inductionOn s fun l hcard => by
      cases l with
      | nil => simp at hcard
      | cons a l =>
        cases l with
        | nil => simp at hcard
        | cons b l =>
          cases l with
          | nil => simp at hcard
          | cons c l =>
            cases l with
            | nil => simp at hcard
            | cons d l =>
              cases l with
              | nil => simp at hcard
              | cons e l =>
                cases l with
                | nil => simp at hcard
                | cons f l =>
                  cases l with
                  | nil => simp at hcard
                  | cons g l =>
                    cases l with
                    | nil => simp at hcard
                    | cons h l =>
                      cases l with
                      | nil =>
                        exact ⟨a, b, c, d, e, f, g, h, rfl⟩
                      | cons i l => simp at hcard,
    fun ⟨_a, _b, _c, _d, _e, _f, _g, _h, h⟩ => h.symm ▸ rfl⟩

private lemma Multiset.card_eq_nine {α : Type*} {s : Multiset α} :
    s.card = 9 ↔ ∃ a b c d e f g h i, s = {a, b, c, d, e, f, g, h, i} :=
  ⟨Quot.inductionOn s fun l hcard => by
      cases l with
      | nil => simp at hcard
      | cons a l =>
        cases l with
        | nil => simp at hcard
        | cons b l =>
          cases l with
          | nil => simp at hcard
          | cons c l =>
            cases l with
            | nil => simp at hcard
            | cons d l =>
              cases l with
              | nil => simp at hcard
              | cons e l =>
                cases l with
                | nil => simp at hcard
                | cons f l =>
                  cases l with
                  | nil => simp at hcard
                  | cons g l =>
                    cases l with
                    | nil => simp at hcard
                    | cons h l =>
                      cases l with
                      | nil => simp at hcard
                      | cons i l =>
                        cases l with
                        | nil =>
                          exact ⟨a, b, c, d, e, f, g, h, i, rfl⟩
                        | cons j l => simp at hcard,
    fun ⟨_a, _b, _c, _d, _e, _f, _g, _h, _i, h⟩ => h.symm ▸ rfl⟩

private lemma Multiset.card_eq_ten {α : Type*} {s : Multiset α} :
    s.card = 10 ↔ ∃ a b c d e f g h i j, s = {a, b, c, d, e, f, g, h, i, j} :=
  ⟨Quot.inductionOn s fun l hcard => by
      cases l with
      | nil => simp at hcard
      | cons a l =>
        cases l with
        | nil => simp at hcard
        | cons b l =>
          cases l with
          | nil => simp at hcard
          | cons c l =>
            cases l with
            | nil => simp at hcard
            | cons d l =>
              cases l with
              | nil => simp at hcard
              | cons e l =>
                cases l with
                | nil => simp at hcard
                | cons f l =>
                  cases l with
                  | nil => simp at hcard
                  | cons g l =>
                    cases l with
                    | nil => simp at hcard
                    | cons h l =>
                      cases l with
                      | nil => simp at hcard
                      | cons i l =>
                        cases l with
                        | nil => simp at hcard
                        | cons j l =>
                          cases l with
                          | nil =>
                            exact ⟨a, b, c, d, e, f, g, h, i, j, rfl⟩
                          | cons k l => simp at hcard,
    fun ⟨_a, _b, _c, _d, _e, _f, _g, _h, _i, _j, h⟩ => h.symm ▸ rfl⟩

private lemma Multiset.card_eq_eleven {α : Type*} {s : Multiset α} :
    s.card = 11 ↔ ∃ a b c d e f g h i j k, s = {a, b, c, d, e, f, g, h, i, j, k} :=
  ⟨Quot.inductionOn s fun xs hcard => by
      cases xs with
      | nil => simp at hcard
      | cons a xs =>
        cases xs with
        | nil => simp at hcard
        | cons b xs =>
          cases xs with
          | nil => simp at hcard
          | cons c xs =>
            cases xs with
            | nil => simp at hcard
            | cons d xs =>
              cases xs with
              | nil => simp at hcard
              | cons e xs =>
                cases xs with
                | nil => simp at hcard
                | cons f xs =>
                  cases xs with
                  | nil => simp at hcard
                  | cons g xs =>
                    cases xs with
                    | nil => simp at hcard
                    | cons h xs =>
                      cases xs with
                      | nil => simp at hcard
                      | cons i xs =>
                        cases xs with
                        | nil => simp at hcard
                        | cons j xs =>
                          cases xs with
                          | nil => simp at hcard
                          | cons k xs =>
                            cases xs with
                            | nil =>
                              exact ⟨a, b, c, d, e, f, g, h, i, j, k, rfl⟩
                            | cons z zs => simp at hcard,
    fun ⟨_a, _b, _c, _d, _e, _f, _g, _h, _i, _j, _k, h⟩ => h.symm ▸ rfl⟩

private lemma partition_two_cases (p : Nat.Partition 2) :
    p = partitionTwo ∨ p = partitionOneOne := by
  have hcard_le : p.parts.card ≤ 2 := partition_parts_card_le p
  interval_cases hcard : p.parts.card
  · have hparts : p.parts = 0 := Multiset.card_eq_zero.mp hcard
    have : (0 : Nat) = 2 := by simpa [hparts] using p.parts_sum
    omega
  · obtain ⟨a, hparts⟩ := Multiset.card_eq_one.mp hcard
    have hsum : a = 2 := by simpa [hparts] using p.parts_sum
    left
    apply Nat.Partition.ext
    simp [partitionTwo, partitionOfParts, hparts, hsum]
  · obtain ⟨a, b, hparts⟩ := Multiset.card_eq_two.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hsum : a + b = 2 := by simpa [hparts] using p.parts_sum
    have ha : a = 1 := by omega
    have hb : b = 1 := by omega
    right
    apply Nat.Partition.ext
    simp [partitionOneOne, partitionOfParts, hparts, ha, hb]

private lemma partition_three_cases (p : Nat.Partition 3) :
    p = partitionThree ∨ p = partitionTwoOne ∨ p = partitionOneOneOne := by
  have hcard_le : p.parts.card ≤ 3 := partition_parts_card_le p
  interval_cases hcard : p.parts.card
  · have hparts : p.parts = 0 := Multiset.card_eq_zero.mp hcard
    have : (0 : Nat) = 3 := by simpa [hparts] using p.parts_sum
    omega
  · obtain ⟨a, hparts⟩ := Multiset.card_eq_one.mp hcard
    have hsum : a = 3 := by simpa [hparts] using p.parts_sum
    left
    apply Nat.Partition.ext
    simp [partitionThree, partitionOfParts, hparts, hsum]
  · obtain ⟨a, b, hparts⟩ := Multiset.card_eq_two.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hsum : a + b = 3 := by simpa [hparts] using p.parts_sum
    have hcases : (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) := by omega
    right
    left
    apply Nat.Partition.ext
    rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · simp [partitionTwoOne, partitionOfParts, hparts, ha, hb]
    · simpa [partitionTwoOne, partitionOfParts, hparts, ha, hb] using
        (show ({2, 1} : Multiset Nat) = {1, 2} by decide)
  · obtain ⟨a, b, c, hparts⟩ := Multiset.card_eq_three.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hsum : a + (b + c) = 3 := by simpa [hparts] using p.parts_sum
    have ha : a = 1 := by omega
    have hb : b = 1 := by omega
    have hc : c = 1 := by omega
    right
    right
    apply Nat.Partition.ext
    simp [partitionOneOneOne, partitionOfParts, hparts, ha, hb, hc]

private lemma partition_four_cases (p : Nat.Partition 4) :
    p = partitionFour ∨ p = partitionThreeOne ∨ p = partitionTwoTwo ∨
      p = partitionTwoOneOne ∨ p = partitionOneOneOneOne := by
  have hcard_le : p.parts.card ≤ 4 := partition_parts_card_le p
  interval_cases hcard : p.parts.card
  · have hparts : p.parts = 0 := Multiset.card_eq_zero.mp hcard
    have : (0 : Nat) = 4 := by simpa [hparts] using p.parts_sum
    omega
  · obtain ⟨a, hparts⟩ := Multiset.card_eq_one.mp hcard
    have hsum : a = 4 := by simpa [hparts] using p.parts_sum
    left
    apply Nat.Partition.ext
    simp [partitionFour, partitionOfParts, hparts, hsum]
  · obtain ⟨a, b, hparts⟩ := Multiset.card_eq_two.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hsum : a + b = 4 := by simpa [hparts] using p.parts_sum
    have hcases :
        (a = 1 ∧ b = 3) ∨ (a = 2 ∧ b = 2) ∨ (a = 3 ∧ b = 1) := by
      omega
    rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · right
      left
      apply Nat.Partition.ext
      simp [partitionThreeOne, partitionOfParts, hparts, ha, hb]
    · right
      right
      left
      apply Nat.Partition.ext
      simp [partitionTwoTwo, partitionOfParts, hparts, ha, hb]
    · right
      left
      apply Nat.Partition.ext
      simpa [partitionThreeOne, partitionOfParts, hparts, ha, hb] using
        (show ({3, 1} : Multiset Nat) = {1, 3} by decide)
  · obtain ⟨a, b, c, hparts⟩ := Multiset.card_eq_three.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hsum : a + (b + c) = 4 := by simpa [hparts] using p.parts_sum
    have hcases :
        (a = 2 ∧ b = 1 ∧ c = 1) ∨
          (a = 1 ∧ b = 2 ∧ c = 1) ∨
          (a = 1 ∧ b = 1 ∧ c = 2) := by
      omega
    right
    right
    right
    left
    apply Nat.Partition.ext
    rcases hcases with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
    · simpa [partitionTwoOneOne, partitionOfParts, hparts, ha, hb, hc] using
        (show ({2, 1, 1} : Multiset Nat) = {1, 1, 2} by decide)
    · simpa [partitionTwoOneOne, partitionOfParts, hparts, ha, hb, hc] using
        (show ({1, 2, 1} : Multiset Nat) = {1, 1, 2} by decide)
    · simp [partitionTwoOneOne, partitionOfParts, hparts, ha, hb, hc]
  · obtain ⟨a, b, c, d, hparts⟩ := Multiset.card_eq_four.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + d)) = 4 := by simpa [hparts] using p.parts_sum
    have ha : a = 1 := by omega
    have hb : b = 1 := by omega
    have hc : c = 1 := by omega
    have hd : d = 1 := by omega
    right
    right
    right
    right
    apply Nat.Partition.ext
    simp [partitionOneOneOneOne, partitionOfParts, hparts, ha, hb, hc, hd]

private lemma partition_five_cases (p : Nat.Partition 5) :
    p = partitionFive ∨ p = partitionFourOne ∨ p = partitionThreeTwo ∨
      p = partitionThreeOneOne ∨ p = partitionTwoTwoOne ∨
      p = partitionTwoOneOneOne ∨ p = partitionOneOneOneOneOne := by
  have hcard_le : p.parts.card ≤ 5 := partition_parts_card_le p
  interval_cases hcard : p.parts.card
  · have hparts : p.parts = 0 := Multiset.card_eq_zero.mp hcard
    have : (0 : Nat) = 5 := by simpa [hparts] using p.parts_sum
    omega
  · obtain ⟨a, hparts⟩ := Multiset.card_eq_one.mp hcard
    have hsum : a = 5 := by simpa [hparts] using p.parts_sum
    left
    apply Nat.Partition.ext
    simp [partitionFive, partitionOfParts, hparts, hsum]
  · obtain ⟨a, b, hparts⟩ := Multiset.card_eq_two.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hsum : a + b = 5 := by simpa [hparts] using p.parts_sum
    have hcases :
        (a = 1 ∧ b = 4) ∨ (a = 2 ∧ b = 3) ∨
          (a = 3 ∧ b = 2) ∨ (a = 4 ∧ b = 1) := by
      omega
    rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · right
      left
      apply Nat.Partition.ext
      simp [partitionFourOne, partitionOfParts, hparts, ha, hb]
    · right
      right
      left
      apply Nat.Partition.ext
      simp [partitionThreeTwo, partitionOfParts, hparts, ha, hb]
    · right
      right
      left
      apply Nat.Partition.ext
      simpa [partitionThreeTwo, partitionOfParts, hparts, ha, hb] using
        (show ({3, 2} : Multiset Nat) = {2, 3} by decide)
    · right
      left
      apply Nat.Partition.ext
      simpa [partitionFourOne, partitionOfParts, hparts, ha, hb] using
        (show ({4, 1} : Multiset Nat) = {1, 4} by decide)
  · obtain ⟨a, b, c, hparts⟩ := Multiset.card_eq_three.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hsum : a + (b + c) = 5 := by simpa [hparts] using p.parts_sum
    have hcases :
        (a = 3 ∧ b = 1 ∧ c = 1) ∨
          (a = 1 ∧ b = 3 ∧ c = 1) ∨
          (a = 1 ∧ b = 1 ∧ c = 3) ∨
          (a = 2 ∧ b = 2 ∧ c = 1) ∨
          (a = 2 ∧ b = 1 ∧ c = 2) ∨
          (a = 1 ∧ b = 2 ∧ c = 2) := by
      omega
    rcases hcases with
      ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ |
      ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
    · right
      right
      right
      left
      apply Nat.Partition.ext
      simpa [partitionThreeOneOne, partitionOfParts, hparts, ha, hb, hc] using
        (show ({3, 1, 1} : Multiset Nat) = {1, 1, 3} by decide)
    · right
      right
      right
      left
      apply Nat.Partition.ext
      simpa [partitionThreeOneOne, partitionOfParts, hparts, ha, hb, hc] using
        (show ({1, 3, 1} : Multiset Nat) = {1, 1, 3} by decide)
    · right
      right
      right
      left
      apply Nat.Partition.ext
      simp [partitionThreeOneOne, partitionOfParts, hparts, ha, hb, hc]
    · right
      right
      right
      right
      left
      apply Nat.Partition.ext
      simpa [partitionTwoTwoOne, partitionOfParts, hparts, ha, hb, hc] using
        (show ({2, 2, 1} : Multiset Nat) = {1, 2, 2} by decide)
    · right
      right
      right
      right
      left
      apply Nat.Partition.ext
      simpa [partitionTwoTwoOne, partitionOfParts, hparts, ha, hb, hc] using
        (show ({2, 1, 2} : Multiset Nat) = {1, 2, 2} by decide)
    · right
      right
      right
      right
      left
      apply Nat.Partition.ext
      simp [partitionTwoTwoOne, partitionOfParts, hparts, ha, hb, hc]
  · obtain ⟨a, b, c, d, hparts⟩ := Multiset.card_eq_four.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + d)) = 5 := by simpa [hparts] using p.parts_sum
    have hcases :
        (a = 2 ∧ b = 1 ∧ c = 1 ∧ d = 1) ∨
          (a = 1 ∧ b = 2 ∧ c = 1 ∧ d = 1) ∨
          (a = 1 ∧ b = 1 ∧ c = 2 ∧ d = 1) ∨
          (a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 2) := by
      omega
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rcases hcases with
      ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩ |
      ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
    · simpa [partitionTwoOneOneOne, partitionOfParts, hparts, ha, hb, hc, hd] using
        (show ({2, 1, 1, 1} : Multiset Nat) = {1, 1, 1, 2} by decide)
    · simpa [partitionTwoOneOneOne, partitionOfParts, hparts, ha, hb, hc, hd] using
        (show ({1, 2, 1, 1} : Multiset Nat) = {1, 1, 1, 2} by decide)
    · simpa [partitionTwoOneOneOne, partitionOfParts, hparts, ha, hb, hc, hd] using
        (show ({1, 1, 2, 1} : Multiset Nat) = {1, 1, 1, 2} by decide)
    · simp [partitionTwoOneOneOne, partitionOfParts, hparts, ha, hb, hc, hd]
  · obtain ⟨a, b, c, d, e, hparts⟩ := Multiset.card_eq_five.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + e))) = 5 := by simpa [hparts] using p.parts_sum
    have ha : a = 1 := by omega
    have hb : b = 1 := by omega
    have hc : c = 1 := by omega
    have hd : d = 1 := by omega
    have he : e = 1 := by omega
    right
    right
    right
    right
    right
    right
    apply Nat.Partition.ext
    simp [partitionOneOneOneOneOne, partitionOfParts, hparts, ha, hb, hc, hd, he]

private lemma partition_six_cases_from_parts (p : Nat.Partition 6)
    (hparts_cases :
      p.parts = {6} ∨ p.parts = {1, 5} ∨ p.parts = {2, 4} ∨
        p.parts = {1, 1, 4} ∨ p.parts = {3, 3} ∨
        p.parts = {1, 2, 3} ∨ p.parts = {1, 1, 1, 3} ∨
        p.parts = {2, 2, 2} ∨ p.parts = {1, 1, 2, 2} ∨
        p.parts = {1, 1, 1, 1, 2} ∨ p.parts = {1, 1, 1, 1, 1, 1}) :
    p = partitionSix ∨ p = partitionFiveOne ∨ p = partitionFourTwo ∨
      p = partitionFourOneOne ∨ p = partitionThreeThree ∨
      p = partitionThreeTwoOne ∨ p = partitionThreeOneOneOne ∨
      p = partitionTwoTwoTwo ∨ p = partitionTwoTwoOneOne ∨
      p = partitionTwoOneOneOneOne ∨ p = partitionOneOneOneOneOneOne := by
  rcases hparts_cases with h | h | h | h | h | h | h | h | h | h | h
  · left
    apply Nat.Partition.ext
    simpa [partitionSix, partitionOfParts] using h
  · right
    left
    apply Nat.Partition.ext
    simpa [partitionFiveOne, partitionOfParts] using h
  · right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourTwo, partitionOfParts] using h
  · right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeThree, partitionOfParts] using h
  · right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeTwoOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionTwoTwoTwo, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionTwoTwoOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionTwoOneOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    apply Nat.Partition.ext
    simpa [partitionOneOneOneOneOneOne, partitionOfParts] using h

private lemma partition_six_cases (p : Nat.Partition 6) :
    p = partitionSix ∨ p = partitionFiveOne ∨ p = partitionFourTwo ∨
      p = partitionFourOneOne ∨ p = partitionThreeThree ∨
      p = partitionThreeTwoOne ∨ p = partitionThreeOneOneOne ∨
      p = partitionTwoTwoTwo ∨ p = partitionTwoTwoOneOne ∨
      p = partitionTwoOneOneOneOne ∨ p = partitionOneOneOneOneOneOne := by
  have hcard_le : p.parts.card ≤ 6 := partition_parts_card_le p
  interval_cases hcard : p.parts.card
  · have hparts : p.parts = 0 := Multiset.card_eq_zero.mp hcard
    have : (0 : Nat) = 6 := by simpa [hparts] using p.parts_sum
    omega
  · obtain ⟨a, hparts⟩ := Multiset.card_eq_one.mp hcard
    have hsum : a = 6 := by simpa [hparts] using p.parts_sum
    apply partition_six_cases_from_parts
    left
    rw [hparts, hsum]
  · obtain ⟨a, b, hparts⟩ := Multiset.card_eq_two.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hsum : a + b = 6 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 5 := by omega
    have hb_le : b ≤ 5 := by omega
    interval_cases a <;> interval_cases b <;> try omega
    all_goals
      apply partition_six_cases_from_parts
      solve
      | right; left; rw [hparts] <;> decide
      | right; right; left; rw [hparts] <;> decide
      | right; right; right; right; left; rw [hparts]
  · obtain ⟨a, b, c, hparts⟩ := Multiset.card_eq_three.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hsum : a + (b + c) = 6 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 4 := by omega
    have hb_le : b ≤ 4 := by omega
    have hc_le : c ≤ 4 := by omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;> try omega
    all_goals
      apply partition_six_cases_from_parts
      solve
      | right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; left; rw [hparts]
  · obtain ⟨a, b, c, d, hparts⟩ := Multiset.card_eq_four.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + d)) = 6 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 3 := by omega
    have hb_le : b ≤ 3 := by omega
    have hc_le : c ≤ 3 := by omega
    have hd_le : d ≤ 3 := by omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
      try omega
    all_goals
      apply partition_six_cases_from_parts
      solve
      | right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, hparts⟩ := Multiset.card_eq_five.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + e))) = 6 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 2 := by omega
    have hb_le : b ≤ 2 := by omega
    have hc_le : c ≤ 2 := by omega
    have hd_le : d ≤ 2 := by omega
    have he_le : e ≤ 2 := by omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
      interval_cases e <;> try omega
    all_goals
      apply partition_six_cases_from_parts
      right
      right
      right
      right
      right
      right
      right
      right
      right
      left
      rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, f, hparts⟩ := Multiset.card_eq_six.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hf_pos : 0 < f := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + (e + f)))) = 6 := by simpa [hparts] using p.parts_sum
    have ha : a = 1 := by omega
    have hb : b = 1 := by omega
    have hc : c = 1 := by omega
    have hd : d = 1 := by omega
    have he : e = 1 := by omega
    have hf : f = 1 := by omega
    apply partition_six_cases_from_parts
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    rw [hparts, ha, hb, hc, hd, he, hf]

private lemma partition_seven_cases_from_parts (p : Nat.Partition 7)
    (hparts_cases :
      p.parts = {7} ∨ p.parts = {1, 6} ∨ p.parts = {2, 5} ∨ p.parts = {1, 1, 5} ∨ p.parts = {3, 4} ∨ p.parts = {1, 2, 4} ∨ p.parts = {1, 1, 1, 4} ∨ p.parts = {1, 3, 3} ∨ p.parts = {2, 2, 3} ∨ p.parts = {1, 1, 2, 3} ∨ p.parts = {1, 1, 1, 1, 3} ∨ p.parts = {1, 2, 2, 2} ∨ p.parts = {1, 1, 1, 2, 2} ∨ p.parts = {1, 1, 1, 1, 1, 2} ∨ p.parts = {1, 1, 1, 1, 1, 1, 1}) :
    p = partitionSeven ∨ p = partitionSixOne ∨ p = partitionFiveTwo ∨ p = partitionFiveOneOne ∨ p = partitionFourThree ∨ p = partitionFourTwoOne ∨ p = partitionFourOneOneOne ∨ p = partitionThreeThreeOne ∨ p = partitionThreeTwoTwo ∨ p = partitionThreeTwoOneOne ∨ p = partitionThreeOneOneOneOne ∨ p = partitionTwoTwoTwoOne ∨ p = partitionTwoTwoOneOneOne ∨ p = partitionTwoOneOneOneOneOne ∨ p = partitionOneOneOneOneOneOneOne := by
  rcases hparts_cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · left
    apply Nat.Partition.ext
    simpa [partitionSeven, partitionOfParts] using h
  · right
    left
    apply Nat.Partition.ext
    simpa [partitionSixOne, partitionOfParts] using h
  · right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFiveTwo, partitionOfParts] using h
  · right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFiveOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourThree, partitionOfParts] using h
  · right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourTwoOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeThreeOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeTwoTwo, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeTwoOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeOneOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionTwoTwoTwoOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionTwoTwoOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionTwoOneOneOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    apply Nat.Partition.ext
    simpa [partitionOneOneOneOneOneOneOne, partitionOfParts] using h

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
private lemma partition_seven_cases (p : Nat.Partition 7) :
    p = partitionSeven ∨ p = partitionSixOne ∨ p = partitionFiveTwo ∨ p = partitionFiveOneOne ∨ p = partitionFourThree ∨ p = partitionFourTwoOne ∨ p = partitionFourOneOneOne ∨ p = partitionThreeThreeOne ∨ p = partitionThreeTwoTwo ∨ p = partitionThreeTwoOneOne ∨ p = partitionThreeOneOneOneOne ∨ p = partitionTwoTwoTwoOne ∨ p = partitionTwoTwoOneOneOne ∨ p = partitionTwoOneOneOneOneOne ∨ p = partitionOneOneOneOneOneOneOne := by
  have hcard_le : p.parts.card ≤ 7 := partition_parts_card_le p
  interval_cases hcard : p.parts.card
  · have hparts : p.parts = 0 := Multiset.card_eq_zero.mp hcard
    have : (0 : Nat) = 7 := by simpa [hparts] using p.parts_sum
    omega
  · obtain ⟨a, hparts⟩ := Multiset.card_eq_one.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hsum : a = 7 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 7 := by omega
    interval_cases a <;> try omega
    all_goals
      apply partition_seven_cases_from_parts
      solve
      | left; rw [hparts] <;> decide
  · obtain ⟨a, b, hparts⟩ := Multiset.card_eq_two.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hsum : a + b = 7 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 6 := by omega
    have hb_le : b ≤ 6 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      apply partition_seven_cases_from_parts
      solve
      | right; left; rw [hparts] <;> decide
      | right; right; left; rw [hparts] <;> decide
      | right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, hparts⟩ := Multiset.card_eq_three.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hsum : a + (b + c) = 7 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 5 := by omega
    have hb_le : b ≤ 5 := by omega
    have hc_le : c ≤ 5 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      apply partition_seven_cases_from_parts
      solve
      | right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, hparts⟩ := Multiset.card_eq_four.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + d)) = 7 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 4 := by omega
    have hb_le : b ≤ 4 := by omega
    have hc_le : c ≤ 4 := by omega
    have hd_le : d ≤ 4 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      apply partition_seven_cases_from_parts
      solve
      | right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, hparts⟩ := Multiset.card_eq_five.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + e))) = 7 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 3 := by omega
    have hb_le : b ≤ 3 := by omega
    have hc_le : c ≤ 3 := by omega
    have hd_le : d ≤ 3 := by omega
    have he_le : e ≤ 3 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      interval_cases e <;> try omega
    all_goals
      apply partition_seven_cases_from_parts
      solve
      | right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, f, hparts⟩ := Multiset.card_eq_six.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hf_pos : 0 < f := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + (e + f)))) = 7 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 2 := by omega
    have hb_le : b ≤ 2 := by omega
    have hc_le : c ≤ 2 := by omega
    have hd_le : d ≤ 2 := by omega
    have he_le : e ≤ 2 := by omega
    have hf_le : f ≤ 2 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      interval_cases e <;> try omega
    all_goals
      interval_cases f <;> try omega
    all_goals
      apply partition_seven_cases_from_parts
      solve
      | right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, f, g, hparts⟩ := Multiset.card_eq_seven.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hf_pos : 0 < f := p.parts_pos (by simp [hparts])
    have hg_pos : 0 < g := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + (e + (f + g))))) = 7 := by simpa [hparts] using p.parts_sum
    have ha : a = 1 := by omega
    have hb : b = 1 := by omega
    have hc : c = 1 := by omega
    have hd : d = 1 := by omega
    have he : e = 1 := by omega
    have hf : f = 1 := by omega
    have hg : g = 1 := by omega
    apply partition_seven_cases_from_parts
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    rw [hparts, ha, hb, hc, hd, he, hf, hg]

private lemma partition_eight_cases_from_parts (p : Nat.Partition 8)
    (hparts_cases :
      p.parts = {8} ∨ p.parts = {1, 7} ∨ p.parts = {2, 6} ∨ p.parts = {1, 1, 6} ∨ p.parts = {3, 5} ∨ p.parts = {1, 2, 5} ∨ p.parts = {1, 1, 1, 5} ∨ p.parts = {4, 4} ∨ p.parts = {1, 3, 4} ∨ p.parts = {2, 2, 4} ∨ p.parts = {1, 1, 2, 4} ∨ p.parts = {1, 1, 1, 1, 4} ∨ p.parts = {2, 3, 3} ∨ p.parts = {1, 1, 3, 3} ∨ p.parts = {1, 2, 2, 3} ∨ p.parts = {1, 1, 1, 2, 3} ∨ p.parts = {1, 1, 1, 1, 1, 3} ∨ p.parts = {2, 2, 2, 2} ∨ p.parts = {1, 1, 2, 2, 2} ∨ p.parts = {1, 1, 1, 1, 2, 2} ∨ p.parts = {1, 1, 1, 1, 1, 1, 2} ∨ p.parts = {1, 1, 1, 1, 1, 1, 1, 1}) :
    p = partitionEight ∨ p = partitionSevenOne ∨ p = partitionSixTwo ∨ p = partitionSixOneOne ∨ p = partitionFiveThree ∨ p = partitionFiveTwoOne ∨ p = partitionFiveOneOneOne ∨ p = partitionFourFour ∨ p = partitionFourThreeOne ∨ p = partitionFourTwoTwo ∨ p = partitionFourTwoOneOne ∨ p = partitionFourOneOneOneOne ∨ p = partitionThreeThreeTwo ∨ p = partitionThreeThreeOneOne ∨ p = partitionThreeTwoTwoOne ∨ p = partitionThreeTwoOneOneOne ∨ p = partitionThreeOneOneOneOneOne ∨ p = partitionTwoTwoTwoTwo ∨ p = partitionTwoTwoTwoOneOne ∨ p = partitionTwoTwoOneOneOneOne ∨ p = partitionTwoOneOneOneOneOneOne ∨ p = partitionOneOneOneOneOneOneOneOne := by
  rcases hparts_cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · left
    apply Nat.Partition.ext
    simpa [partitionEight, partitionOfParts] using h
  · right
    left
    apply Nat.Partition.ext
    simpa [partitionSevenOne, partitionOfParts] using h
  · right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionSixTwo, partitionOfParts] using h
  · right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionSixOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFiveThree, partitionOfParts] using h
  · right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFiveTwoOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFiveOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourFour, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourThreeOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourTwoTwo, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourTwoOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourOneOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeThreeTwo, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeThreeOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeTwoTwoOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeTwoOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeOneOneOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionTwoTwoTwoTwo, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionTwoTwoTwoOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionTwoTwoOneOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionTwoOneOneOneOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    apply Nat.Partition.ext
    simpa [partitionOneOneOneOneOneOneOneOne, partitionOfParts] using h

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
private lemma partition_eight_cases (p : Nat.Partition 8) :
    p = partitionEight ∨ p = partitionSevenOne ∨ p = partitionSixTwo ∨ p = partitionSixOneOne ∨ p = partitionFiveThree ∨ p = partitionFiveTwoOne ∨ p = partitionFiveOneOneOne ∨ p = partitionFourFour ∨ p = partitionFourThreeOne ∨ p = partitionFourTwoTwo ∨ p = partitionFourTwoOneOne ∨ p = partitionFourOneOneOneOne ∨ p = partitionThreeThreeTwo ∨ p = partitionThreeThreeOneOne ∨ p = partitionThreeTwoTwoOne ∨ p = partitionThreeTwoOneOneOne ∨ p = partitionThreeOneOneOneOneOne ∨ p = partitionTwoTwoTwoTwo ∨ p = partitionTwoTwoTwoOneOne ∨ p = partitionTwoTwoOneOneOneOne ∨ p = partitionTwoOneOneOneOneOneOne ∨ p = partitionOneOneOneOneOneOneOneOne := by
  have hcard_le : p.parts.card ≤ 8 := partition_parts_card_le p
  interval_cases hcard : p.parts.card
  · have hparts : p.parts = 0 := Multiset.card_eq_zero.mp hcard
    have : (0 : Nat) = 8 := by simpa [hparts] using p.parts_sum
    omega
  · obtain ⟨a, hparts⟩ := Multiset.card_eq_one.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hsum : a = 8 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 8 := by omega
    interval_cases a <;> try omega
    all_goals
      apply partition_eight_cases_from_parts
      solve
      | left; rw [hparts] <;> decide
  · obtain ⟨a, b, hparts⟩ := Multiset.card_eq_two.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hsum : a + b = 8 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 7 := by omega
    have hb_le : b ≤ 7 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      apply partition_eight_cases_from_parts
      solve
      | right; left; rw [hparts] <;> decide
      | right; right; left; rw [hparts] <;> decide
      | right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, hparts⟩ := Multiset.card_eq_three.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hsum : a + (b + c) = 8 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 6 := by omega
    have hb_le : b ≤ 6 := by omega
    have hc_le : c ≤ 6 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      apply partition_eight_cases_from_parts
      solve
      | right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, hparts⟩ := Multiset.card_eq_four.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + d)) = 8 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 5 := by omega
    have hb_le : b ≤ 5 := by omega
    have hc_le : c ≤ 5 := by omega
    have hd_le : d ≤ 5 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      apply partition_eight_cases_from_parts
      solve
      | right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, hparts⟩ := Multiset.card_eq_five.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + e))) = 8 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 4 := by omega
    have hb_le : b ≤ 4 := by omega
    have hc_le : c ≤ 4 := by omega
    have hd_le : d ≤ 4 := by omega
    have he_le : e ≤ 4 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      interval_cases e <;> try omega
    all_goals
      apply partition_eight_cases_from_parts
      solve
      | right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, f, hparts⟩ := Multiset.card_eq_six.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hf_pos : 0 < f := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + (e + f)))) = 8 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 3 := by omega
    have hb_le : b ≤ 3 := by omega
    have hc_le : c ≤ 3 := by omega
    have hd_le : d ≤ 3 := by omega
    have he_le : e ≤ 3 := by omega
    have hf_le : f ≤ 3 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      interval_cases e <;> try omega
    all_goals
      interval_cases f <;> try omega
    all_goals
      apply partition_eight_cases_from_parts
      solve
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, f, g, hparts⟩ := Multiset.card_eq_seven.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hf_pos : 0 < f := p.parts_pos (by simp [hparts])
    have hg_pos : 0 < g := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + (e + (f + g))))) = 8 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 2 := by omega
    have hb_le : b ≤ 2 := by omega
    have hc_le : c ≤ 2 := by omega
    have hd_le : d ≤ 2 := by omega
    have he_le : e ≤ 2 := by omega
    have hf_le : f ≤ 2 := by omega
    have hg_le : g ≤ 2 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      interval_cases e <;> try omega
    all_goals
      interval_cases f <;> try omega
    all_goals
      interval_cases g <;> try omega
    all_goals
      apply partition_eight_cases_from_parts
      solve
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, f, g, h, hparts⟩ := Multiset.card_eq_eight.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hf_pos : 0 < f := p.parts_pos (by simp [hparts])
    have hg_pos : 0 < g := p.parts_pos (by simp [hparts])
    have hh_pos : 0 < h := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + (e + (f + (g + h)))))) = 8 := by simpa [hparts] using p.parts_sum
    have ha : a = 1 := by omega
    have hb : b = 1 := by omega
    have hc : c = 1 := by omega
    have hd : d = 1 := by omega
    have he : e = 1 := by omega
    have hf : f = 1 := by omega
    have hg : g = 1 := by omega
    have hh : h = 1 := by omega
    apply partition_eight_cases_from_parts
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    rw [hparts, ha, hb, hc, hd, he, hf, hg, hh]

private lemma partition_nine_cases_from_parts (p : Nat.Partition 9)
    (hparts_cases :
      p.parts = {9} ∨ p.parts = {1, 8} ∨ p.parts = {2, 7} ∨ p.parts = {1, 1, 7} ∨ p.parts = {3, 6} ∨ p.parts = {1, 2, 6} ∨ p.parts = {1, 1, 1, 6} ∨ p.parts = {4, 5} ∨ p.parts = {1, 3, 5} ∨ p.parts = {2, 2, 5} ∨ p.parts = {1, 1, 2, 5} ∨ p.parts = {1, 1, 1, 1, 5} ∨ p.parts = {1, 4, 4} ∨ p.parts = {2, 3, 4} ∨ p.parts = {1, 1, 3, 4} ∨ p.parts = {1, 2, 2, 4} ∨ p.parts = {1, 1, 1, 2, 4} ∨ p.parts = {1, 1, 1, 1, 1, 4} ∨ p.parts = {3, 3, 3} ∨ p.parts = {1, 2, 3, 3} ∨ p.parts = {1, 1, 1, 3, 3} ∨ p.parts = {2, 2, 2, 3} ∨ p.parts = {1, 1, 2, 2, 3} ∨ p.parts = {1, 1, 1, 1, 2, 3} ∨ p.parts = {1, 1, 1, 1, 1, 1, 3} ∨ p.parts = {1, 2, 2, 2, 2} ∨ p.parts = {1, 1, 1, 2, 2, 2} ∨ p.parts = {1, 1, 1, 1, 1, 2, 2} ∨ p.parts = {1, 1, 1, 1, 1, 1, 1, 2} ∨ p.parts = {1, 1, 1, 1, 1, 1, 1, 1, 1}) :
    p = partitionNine ∨ p = partitionEightOne ∨ p = partitionSevenTwo ∨ p = partitionSevenOneOne ∨ p = partitionSixThree ∨ p = partitionSixTwoOne ∨ p = partitionSixOneOneOne ∨ p = partitionFiveFour ∨ p = partitionFiveThreeOne ∨ p = partitionFiveTwoTwo ∨ p = partitionFiveTwoOneOne ∨ p = partitionFiveOneOneOneOne ∨ p = partitionFourFourOne ∨ p = partitionFourThreeTwo ∨ p = partitionFourThreeOneOne ∨ p = partitionFourTwoTwoOne ∨ p = partitionFourTwoOneOneOne ∨ p = partitionFourOneOneOneOneOne ∨ p = partitionThreeThreeThree ∨ p = partitionThreeThreeTwoOne ∨ p = partitionThreeThreeOneOneOne ∨ p = partitionThreeTwoTwoTwo ∨ p = partitionThreeTwoTwoOneOne ∨ p = partitionThreeTwoOneOneOneOne ∨ p = partitionThreeOneOneOneOneOneOne ∨ p = partitionTwoTwoTwoTwoOne ∨ p = partitionTwoTwoTwoOneOneOne ∨ p = partitionTwoTwoOneOneOneOneOne ∨ p = partitionTwoOneOneOneOneOneOneOne ∨ p = partitionOneOneOneOneOneOneOneOneOne := by
  rcases hparts_cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · left
    apply Nat.Partition.ext
    simpa [partitionNine, partitionOfParts] using h
  · right
    left
    apply Nat.Partition.ext
    simpa [partitionEightOne, partitionOfParts] using h
  · right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionSevenTwo, partitionOfParts] using h
  · right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionSevenOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionSixThree, partitionOfParts] using h
  · right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionSixTwoOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionSixOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFiveFour, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFiveThreeOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFiveTwoTwo, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFiveTwoOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFiveOneOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourFourOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourThreeTwo, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourThreeOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourTwoTwoOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourTwoOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourOneOneOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeThreeThree, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeThreeTwoOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeThreeOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeTwoTwoTwo, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeTwoTwoOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeTwoOneOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeOneOneOneOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionTwoTwoTwoTwoOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionTwoTwoTwoOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionTwoTwoOneOneOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionTwoOneOneOneOneOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    apply Nat.Partition.ext
    simpa [partitionOneOneOneOneOneOneOneOneOne, partitionOfParts] using h

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 1000000 in
private lemma partition_nine_cases (p : Nat.Partition 9) :
    p = partitionNine ∨ p = partitionEightOne ∨ p = partitionSevenTwo ∨ p = partitionSevenOneOne ∨ p = partitionSixThree ∨ p = partitionSixTwoOne ∨ p = partitionSixOneOneOne ∨ p = partitionFiveFour ∨ p = partitionFiveThreeOne ∨ p = partitionFiveTwoTwo ∨ p = partitionFiveTwoOneOne ∨ p = partitionFiveOneOneOneOne ∨ p = partitionFourFourOne ∨ p = partitionFourThreeTwo ∨ p = partitionFourThreeOneOne ∨ p = partitionFourTwoTwoOne ∨ p = partitionFourTwoOneOneOne ∨ p = partitionFourOneOneOneOneOne ∨ p = partitionThreeThreeThree ∨ p = partitionThreeThreeTwoOne ∨ p = partitionThreeThreeOneOneOne ∨ p = partitionThreeTwoTwoTwo ∨ p = partitionThreeTwoTwoOneOne ∨ p = partitionThreeTwoOneOneOneOne ∨ p = partitionThreeOneOneOneOneOneOne ∨ p = partitionTwoTwoTwoTwoOne ∨ p = partitionTwoTwoTwoOneOneOne ∨ p = partitionTwoTwoOneOneOneOneOne ∨ p = partitionTwoOneOneOneOneOneOneOne ∨ p = partitionOneOneOneOneOneOneOneOneOne := by
  have hcard_le : p.parts.card ≤ 9 := partition_parts_card_le p
  interval_cases hcard : p.parts.card
  · have hparts : p.parts = 0 := Multiset.card_eq_zero.mp hcard
    have : (0 : Nat) = 9 := by simpa [hparts] using p.parts_sum
    omega
  · obtain ⟨a, hparts⟩ := Multiset.card_eq_one.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hsum : a = 9 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 9 := by omega
    interval_cases a <;> try omega
    all_goals
      apply partition_nine_cases_from_parts
      solve
      | left; rw [hparts] <;> decide
  · obtain ⟨a, b, hparts⟩ := Multiset.card_eq_two.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hsum : a + b = 9 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 8 := by omega
    have hb_le : b ≤ 8 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      apply partition_nine_cases_from_parts
      solve
      | right; left; rw [hparts] <;> decide
      | right; right; left; rw [hparts] <;> decide
      | right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, hparts⟩ := Multiset.card_eq_three.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hsum : a + (b + c) = 9 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 7 := by omega
    have hb_le : b ≤ 7 := by omega
    have hc_le : c ≤ 7 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      apply partition_nine_cases_from_parts
      solve
      | right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, hparts⟩ := Multiset.card_eq_four.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + d)) = 9 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 6 := by omega
    have hb_le : b ≤ 6 := by omega
    have hc_le : c ≤ 6 := by omega
    have hd_le : d ≤ 6 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      apply partition_nine_cases_from_parts
      solve
      | right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, hparts⟩ := Multiset.card_eq_five.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + e))) = 9 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 5 := by omega
    have hb_le : b ≤ 5 := by omega
    have hc_le : c ≤ 5 := by omega
    have hd_le : d ≤ 5 := by omega
    have he_le : e ≤ 5 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      interval_cases e <;> try omega
    all_goals
      apply partition_nine_cases_from_parts
      solve
      | right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, f, hparts⟩ := Multiset.card_eq_six.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hf_pos : 0 < f := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + (e + f)))) = 9 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 4 := by omega
    have hb_le : b ≤ 4 := by omega
    have hc_le : c ≤ 4 := by omega
    have hd_le : d ≤ 4 := by omega
    have he_le : e ≤ 4 := by omega
    have hf_le : f ≤ 4 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      interval_cases e <;> try omega
    all_goals
      interval_cases f <;> try omega
    all_goals
      apply partition_nine_cases_from_parts
      solve
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, f, g, hparts⟩ := Multiset.card_eq_seven.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hf_pos : 0 < f := p.parts_pos (by simp [hparts])
    have hg_pos : 0 < g := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + (e + (f + g))))) = 9 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 3 := by omega
    have hb_le : b ≤ 3 := by omega
    have hc_le : c ≤ 3 := by omega
    have hd_le : d ≤ 3 := by omega
    have he_le : e ≤ 3 := by omega
    have hf_le : f ≤ 3 := by omega
    have hg_le : g ≤ 3 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      interval_cases e <;> try omega
    all_goals
      interval_cases f <;> try omega
    all_goals
      interval_cases g <;> try omega
    all_goals
      apply partition_nine_cases_from_parts
      solve
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, f, g, h, hparts⟩ := Multiset.card_eq_eight.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hf_pos : 0 < f := p.parts_pos (by simp [hparts])
    have hg_pos : 0 < g := p.parts_pos (by simp [hparts])
    have hh_pos : 0 < h := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + (e + (f + (g + h)))))) = 9 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 2 := by omega
    have hb_le : b ≤ 2 := by omega
    have hc_le : c ≤ 2 := by omega
    have hd_le : d ≤ 2 := by omega
    have he_le : e ≤ 2 := by omega
    have hf_le : f ≤ 2 := by omega
    have hg_le : g ≤ 2 := by omega
    have hh_le : h ≤ 2 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      interval_cases e <;> try omega
    all_goals
      interval_cases f <;> try omega
    all_goals
      interval_cases g <;> try omega
    all_goals
      interval_cases h <;> try omega
    all_goals
      apply partition_nine_cases_from_parts
      solve
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, f, g, h, i, hparts⟩ := Multiset.card_eq_nine.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hf_pos : 0 < f := p.parts_pos (by simp [hparts])
    have hg_pos : 0 < g := p.parts_pos (by simp [hparts])
    have hh_pos : 0 < h := p.parts_pos (by simp [hparts])
    have hi_pos : 0 < i := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + (e + (f + (g + (h + i))))))) = 9 := by simpa [hparts] using p.parts_sum
    have ha : a = 1 := by omega
    have hb : b = 1 := by omega
    have hc : c = 1 := by omega
    have hd : d = 1 := by omega
    have he : e = 1 := by omega
    have hf : f = 1 := by omega
    have hg : g = 1 := by omega
    have hh : h = 1 := by omega
    have hi : i = 1 := by omega
    apply partition_nine_cases_from_parts
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    rw [hparts, ha, hb, hc, hd, he, hf, hg, hh, hi]

private lemma partition_ten_cases_from_parts (p : Nat.Partition 10)
    (hparts_cases :
      p.parts = {10} ∨ p.parts = {1, 9} ∨ p.parts = {2, 8} ∨ p.parts = {1, 1, 8} ∨ p.parts = {3, 7} ∨ p.parts = {1, 2, 7} ∨ p.parts = {1, 1, 1, 7} ∨ p.parts = {4, 6} ∨ p.parts = {1, 3, 6} ∨ p.parts = {2, 2, 6} ∨ p.parts = {1, 1, 2, 6} ∨ p.parts = {1, 1, 1, 1, 6} ∨ p.parts = {5, 5} ∨ p.parts = {1, 4, 5} ∨ p.parts = {2, 3, 5} ∨ p.parts = {1, 1, 3, 5} ∨ p.parts = {1, 2, 2, 5} ∨ p.parts = {1, 1, 1, 2, 5} ∨ p.parts = {1, 1, 1, 1, 1, 5} ∨ p.parts = {2, 4, 4} ∨ p.parts = {1, 1, 4, 4} ∨ p.parts = {3, 3, 4} ∨ p.parts = {1, 2, 3, 4} ∨ p.parts = {1, 1, 1, 3, 4} ∨ p.parts = {2, 2, 2, 4} ∨ p.parts = {1, 1, 2, 2, 4} ∨ p.parts = {1, 1, 1, 1, 2, 4} ∨ p.parts = {1, 1, 1, 1, 1, 1, 4} ∨ p.parts = {1, 3, 3, 3} ∨ p.parts = {2, 2, 3, 3} ∨ p.parts = {1, 1, 2, 3, 3} ∨ p.parts = {1, 1, 1, 1, 3, 3} ∨ p.parts = {1, 2, 2, 2, 3} ∨ p.parts = {1, 1, 1, 2, 2, 3} ∨ p.parts = {1, 1, 1, 1, 1, 2, 3} ∨ p.parts = {1, 1, 1, 1, 1, 1, 1, 3} ∨ p.parts = {2, 2, 2, 2, 2} ∨ p.parts = {1, 1, 2, 2, 2, 2} ∨ p.parts = {1, 1, 1, 1, 2, 2, 2} ∨ p.parts = {1, 1, 1, 1, 1, 1, 2, 2} ∨ p.parts = {1, 1, 1, 1, 1, 1, 1, 1, 2} ∨ p.parts = {1, 1, 1, 1, 1, 1, 1, 1, 1, 1}) :
    p = partitionTen ∨ p = partitionNineOne ∨ p = partitionEightTwo ∨ p = partitionEightOneOne ∨ p = partitionSevenThree ∨ p = partitionSevenTwoOne ∨ p = partitionSevenOneOneOne ∨ p = partitionSixFour ∨ p = partitionSixThreeOne ∨ p = partitionSixTwoTwo ∨ p = partitionSixTwoOneOne ∨ p = partitionSixOneOneOneOne ∨ p = partitionFiveFive ∨ p = partitionFiveFourOne ∨ p = partitionFiveThreeTwo ∨ p = partitionFiveThreeOneOne ∨ p = partitionFiveTwoTwoOne ∨ p = partitionFiveTwoOneOneOne ∨ p = partitionFiveOneOneOneOneOne ∨ p = partitionFourFourTwo ∨ p = partitionFourFourOneOne ∨ p = partitionFourThreeThree ∨ p = partitionFourThreeTwoOne ∨ p = partitionFourThreeOneOneOne ∨ p = partitionFourTwoTwoTwo ∨ p = partitionFourTwoTwoOneOne ∨ p = partitionFourTwoOneOneOneOne ∨ p = partitionFourOneOneOneOneOneOne ∨ p = partitionThreeThreeThreeOne ∨ p = partitionThreeThreeTwoTwo ∨ p = partitionThreeThreeTwoOneOne ∨ p = partitionThreeThreeOneOneOneOne ∨ p = partitionThreeTwoTwoTwoOne ∨ p = partitionThreeTwoTwoOneOneOne ∨ p = partitionThreeTwoOneOneOneOneOne ∨ p = partitionThreeOneOneOneOneOneOneOne ∨ p = partitionTwoTwoTwoTwoTwo ∨ p = partitionTwoTwoTwoTwoOneOne ∨ p = partitionTwoTwoTwoOneOneOneOne ∨ p = partitionTwoTwoOneOneOneOneOneOne ∨ p = partitionTwoOneOneOneOneOneOneOneOne ∨ p = partitionOneOneOneOneOneOneOneOneOneOne := by
  rcases hparts_cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · left
    apply Nat.Partition.ext
    simpa [partitionTen, partitionOfParts] using h
  · right
    left
    apply Nat.Partition.ext
    simpa [partitionNineOne, partitionOfParts] using h
  · right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionEightTwo, partitionOfParts] using h
  · right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionEightOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionSevenThree, partitionOfParts] using h
  · right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionSevenTwoOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionSevenOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionSixFour, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionSixThreeOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionSixTwoTwo, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionSixTwoOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionSixOneOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFiveFive, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFiveFourOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFiveThreeTwo, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFiveThreeOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFiveTwoTwoOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFiveTwoOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFiveOneOneOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourFourTwo, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourFourOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourThreeThree, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourThreeTwoOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourThreeOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourTwoTwoTwo, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourTwoTwoOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourTwoOneOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionFourOneOneOneOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeThreeThreeOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeThreeTwoTwo, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeThreeTwoOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeThreeOneOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeTwoTwoTwoOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeTwoTwoOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeTwoOneOneOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionThreeOneOneOneOneOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionTwoTwoTwoTwoTwo, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionTwoTwoTwoTwoOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionTwoTwoTwoOneOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionTwoTwoOneOneOneOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    simpa [partitionTwoOneOneOneOneOneOneOneOne, partitionOfParts] using h
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    apply Nat.Partition.ext
    simpa [partitionOneOneOneOneOneOneOneOneOneOne, partitionOfParts] using h

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 2000000 in
private lemma partition_ten_cases (p : Nat.Partition 10) :
    p = partitionTen ∨ p = partitionNineOne ∨ p = partitionEightTwo ∨ p = partitionEightOneOne ∨ p = partitionSevenThree ∨ p = partitionSevenTwoOne ∨ p = partitionSevenOneOneOne ∨ p = partitionSixFour ∨ p = partitionSixThreeOne ∨ p = partitionSixTwoTwo ∨ p = partitionSixTwoOneOne ∨ p = partitionSixOneOneOneOne ∨ p = partitionFiveFive ∨ p = partitionFiveFourOne ∨ p = partitionFiveThreeTwo ∨ p = partitionFiveThreeOneOne ∨ p = partitionFiveTwoTwoOne ∨ p = partitionFiveTwoOneOneOne ∨ p = partitionFiveOneOneOneOneOne ∨ p = partitionFourFourTwo ∨ p = partitionFourFourOneOne ∨ p = partitionFourThreeThree ∨ p = partitionFourThreeTwoOne ∨ p = partitionFourThreeOneOneOne ∨ p = partitionFourTwoTwoTwo ∨ p = partitionFourTwoTwoOneOne ∨ p = partitionFourTwoOneOneOneOne ∨ p = partitionFourOneOneOneOneOneOne ∨ p = partitionThreeThreeThreeOne ∨ p = partitionThreeThreeTwoTwo ∨ p = partitionThreeThreeTwoOneOne ∨ p = partitionThreeThreeOneOneOneOne ∨ p = partitionThreeTwoTwoTwoOne ∨ p = partitionThreeTwoTwoOneOneOne ∨ p = partitionThreeTwoOneOneOneOneOne ∨ p = partitionThreeOneOneOneOneOneOneOne ∨ p = partitionTwoTwoTwoTwoTwo ∨ p = partitionTwoTwoTwoTwoOneOne ∨ p = partitionTwoTwoTwoOneOneOneOne ∨ p = partitionTwoTwoOneOneOneOneOneOne ∨ p = partitionTwoOneOneOneOneOneOneOneOne ∨ p = partitionOneOneOneOneOneOneOneOneOneOne := by
  have hcard_le : p.parts.card ≤ 10 := partition_parts_card_le p
  interval_cases hcard : p.parts.card
  · have hparts : p.parts = 0 := Multiset.card_eq_zero.mp hcard
    have : (0 : Nat) = 10 := by simpa [hparts] using p.parts_sum
    omega
  · obtain ⟨a, hparts⟩ := Multiset.card_eq_one.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hsum : a = 10 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 10 := by omega
    interval_cases a <;> try omega
    all_goals
      apply partition_ten_cases_from_parts
      solve
      | left; rw [hparts] <;> decide
  · obtain ⟨a, b, hparts⟩ := Multiset.card_eq_two.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hsum : a + b = 10 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 9 := by omega
    have hb_le : b ≤ 9 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      apply partition_ten_cases_from_parts
      solve
      | right; left; rw [hparts] <;> decide
      | right; right; left; rw [hparts] <;> decide
      | right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, hparts⟩ := Multiset.card_eq_three.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hsum : a + (b + c) = 10 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 8 := by omega
    have hb_le : b ≤ 8 := by omega
    have hc_le : c ≤ 8 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      apply partition_ten_cases_from_parts
      solve
      | right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, hparts⟩ := Multiset.card_eq_four.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + d)) = 10 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 7 := by omega
    have hb_le : b ≤ 7 := by omega
    have hc_le : c ≤ 7 := by omega
    have hd_le : d ≤ 7 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      apply partition_ten_cases_from_parts
      solve
      | right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, hparts⟩ := Multiset.card_eq_five.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + e))) = 10 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 6 := by omega
    have hb_le : b ≤ 6 := by omega
    have hc_le : c ≤ 6 := by omega
    have hd_le : d ≤ 6 := by omega
    have he_le : e ≤ 6 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      interval_cases e <;> try omega
    all_goals
      apply partition_ten_cases_from_parts
      solve
      | right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, f, hparts⟩ := Multiset.card_eq_six.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hf_pos : 0 < f := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + (e + f)))) = 10 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 5 := by omega
    have hb_le : b ≤ 5 := by omega
    have hc_le : c ≤ 5 := by omega
    have hd_le : d ≤ 5 := by omega
    have he_le : e ≤ 5 := by omega
    have hf_le : f ≤ 5 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      interval_cases e <;> try omega
    all_goals
      interval_cases f <;> try omega
    all_goals
      apply partition_ten_cases_from_parts
      solve
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, f, g, hparts⟩ := Multiset.card_eq_seven.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hf_pos : 0 < f := p.parts_pos (by simp [hparts])
    have hg_pos : 0 < g := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + (e + (f + g))))) = 10 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 4 := by omega
    have hb_le : b ≤ 4 := by omega
    have hc_le : c ≤ 4 := by omega
    have hd_le : d ≤ 4 := by omega
    have he_le : e ≤ 4 := by omega
    have hf_le : f ≤ 4 := by omega
    have hg_le : g ≤ 4 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      interval_cases e <;> try omega
    all_goals
      interval_cases f <;> try omega
    all_goals
      interval_cases g <;> try omega
    all_goals
      apply partition_ten_cases_from_parts
      solve
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, f, g, h, hparts⟩ := Multiset.card_eq_eight.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hf_pos : 0 < f := p.parts_pos (by simp [hparts])
    have hg_pos : 0 < g := p.parts_pos (by simp [hparts])
    have hh_pos : 0 < h := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + (e + (f + (g + h)))))) = 10 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 3 := by omega
    have hb_le : b ≤ 3 := by omega
    have hc_le : c ≤ 3 := by omega
    have hd_le : d ≤ 3 := by omega
    have he_le : e ≤ 3 := by omega
    have hf_le : f ≤ 3 := by omega
    have hg_le : g ≤ 3 := by omega
    have hh_le : h ≤ 3 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      interval_cases e <;> try omega
    all_goals
      interval_cases f <;> try omega
    all_goals
      interval_cases g <;> try omega
    all_goals
      interval_cases h <;> try omega
    all_goals
      apply partition_ten_cases_from_parts
      solve
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, f, g, h, i, hparts⟩ := Multiset.card_eq_nine.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hf_pos : 0 < f := p.parts_pos (by simp [hparts])
    have hg_pos : 0 < g := p.parts_pos (by simp [hparts])
    have hh_pos : 0 < h := p.parts_pos (by simp [hparts])
    have hi_pos : 0 < i := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + (e + (f + (g + (h + i))))))) = 10 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 2 := by omega
    have hb_le : b ≤ 2 := by omega
    have hc_le : c ≤ 2 := by omega
    have hd_le : d ≤ 2 := by omega
    have he_le : e ≤ 2 := by omega
    have hf_le : f ≤ 2 := by omega
    have hg_le : g ≤ 2 := by omega
    have hh_le : h ≤ 2 := by omega
    have hi_le : i ≤ 2 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      interval_cases e <;> try omega
    all_goals
      interval_cases f <;> try omega
    all_goals
      interval_cases g <;> try omega
    all_goals
      interval_cases h <;> try omega
    all_goals
      interval_cases i <;> try omega
    all_goals
      apply partition_ten_cases_from_parts
      solve
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, f, g, h, i, j, hparts⟩ := Multiset.card_eq_ten.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hf_pos : 0 < f := p.parts_pos (by simp [hparts])
    have hg_pos : 0 < g := p.parts_pos (by simp [hparts])
    have hh_pos : 0 < h := p.parts_pos (by simp [hparts])
    have hi_pos : 0 < i := p.parts_pos (by simp [hparts])
    have hj_pos : 0 < j := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + (e + (f + (g + (h + (i + j)))))))) = 10 := by simpa [hparts] using p.parts_sum
    have ha : a = 1 := by omega
    have hb : b = 1 := by omega
    have hc : c = 1 := by omega
    have hd : d = 1 := by omega
    have he : e = 1 := by omega
    have hf : f = 1 := by omega
    have hg : g = 1 := by omega
    have hh : h = 1 := by omega
    have hi : i = 1 := by omega
    have hj : j = 1 := by omega
    apply partition_ten_cases_from_parts
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    rw [hparts, ha, hb, hc, hd, he, hf, hg, hh, hi, hj]

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
set_option linter.unnecessarySeqFocus false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
private lemma partition_eleven_parts_cases (p : Nat.Partition 11) :
    p.parts = ({11} : Multiset Nat) ∨ p.parts = ({1, 10} : Multiset Nat) ∨ p.parts = ({2, 9} : Multiset Nat) ∨ p.parts = ({1, 1, 9} : Multiset Nat) ∨ p.parts = ({3, 8} : Multiset Nat) ∨ p.parts = ({1, 2, 8} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 8} : Multiset Nat) ∨ p.parts = ({4, 7} : Multiset Nat) ∨ p.parts = ({1, 3, 7} : Multiset Nat) ∨ p.parts = ({2, 2, 7} : Multiset Nat) ∨ p.parts = ({1, 1, 2, 7} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 7} : Multiset Nat) ∨ p.parts = ({5, 6} : Multiset Nat) ∨ p.parts = ({1, 4, 6} : Multiset Nat) ∨ p.parts = ({2, 3, 6} : Multiset Nat) ∨ p.parts = ({1, 1, 3, 6} : Multiset Nat) ∨ p.parts = ({1, 2, 2, 6} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 2, 6} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 1, 6} : Multiset Nat) ∨ p.parts = ({1, 5, 5} : Multiset Nat) ∨ p.parts = ({2, 4, 5} : Multiset Nat) ∨ p.parts = ({1, 1, 4, 5} : Multiset Nat) ∨ p.parts = ({3, 3, 5} : Multiset Nat) ∨ p.parts = ({1, 2, 3, 5} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 3, 5} : Multiset Nat) ∨ p.parts = ({2, 2, 2, 5} : Multiset Nat) ∨ p.parts = ({1, 1, 2, 2, 5} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 2, 5} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 1, 1, 5} : Multiset Nat) ∨ p.parts = ({3, 4, 4} : Multiset Nat) ∨ p.parts = ({1, 2, 4, 4} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 4, 4} : Multiset Nat) ∨ p.parts = ({1, 3, 3, 4} : Multiset Nat) ∨ p.parts = ({2, 2, 3, 4} : Multiset Nat) ∨ p.parts = ({1, 1, 2, 3, 4} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 3, 4} : Multiset Nat) ∨ p.parts = ({1, 2, 2, 2, 4} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 2, 2, 4} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 1, 2, 4} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 1, 1, 1, 4} : Multiset Nat) ∨ p.parts = ({2, 3, 3, 3} : Multiset Nat) ∨ p.parts = ({1, 1, 3, 3, 3} : Multiset Nat) ∨ p.parts = ({1, 2, 2, 3, 3} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 2, 3, 3} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 1, 3, 3} : Multiset Nat) ∨ p.parts = ({2, 2, 2, 2, 3} : Multiset Nat) ∨ p.parts = ({1, 1, 2, 2, 2, 3} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 2, 2, 3} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 1, 1, 2, 3} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 1, 1, 1, 1, 3} : Multiset Nat) ∨ p.parts = ({1, 2, 2, 2, 2, 2} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 2, 2, 2, 2} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 1, 2, 2, 2} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 1, 1, 1, 2, 2} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 1, 1, 1, 1, 1, 2} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1} : Multiset Nat) := by
  have hcard_le : p.parts.card ≤ 11 := partition_parts_card_le p
  interval_cases hcard : p.parts.card
  · have hparts : p.parts = 0 := Multiset.card_eq_zero.mp hcard
    have : (0 : Nat) = 11 := by simpa [hparts] using p.parts_sum
    omega
  · obtain ⟨a, hparts⟩ := Multiset.card_eq_one.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hsum : a = 11 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 11 := by omega
    interval_cases a <;> try omega
    all_goals
      solve
      | left; rw [hparts] <;> decide
  · obtain ⟨a, b, hparts⟩ := Multiset.card_eq_two.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hsum : a + (b) = 11 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 10 := by omega
    have hb_le : b ≤ 10 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      solve
      | right; left; rw [hparts] <;> decide
      | right; right; left; rw [hparts] <;> decide
      | right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, hparts⟩ := Multiset.card_eq_three.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c)) = 11 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 9 := by omega
    have hb_le : b ≤ 9 := by omega
    have hc_le : c ≤ 9 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      solve
      | right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, hparts⟩ := Multiset.card_eq_four.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d))) = 11 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 8 := by omega
    have hb_le : b ≤ 8 := by omega
    have hc_le : c ≤ 8 := by omega
    have hd_le : d ≤ 8 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      solve
      | right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, hparts⟩ := Multiset.card_eq_five.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + (e)))) = 11 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 7 := by omega
    have hb_le : b ≤ 7 := by omega
    have hc_le : c ≤ 7 := by omega
    have hd_le : d ≤ 7 := by omega
    have he_le : e ≤ 7 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      interval_cases e <;> try omega
    all_goals
      solve
      | right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, f, hparts⟩ := Multiset.card_eq_six.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hf_pos : 0 < f := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + (e + (f))))) = 11 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 6 := by omega
    have hb_le : b ≤ 6 := by omega
    have hc_le : c ≤ 6 := by omega
    have hd_le : d ≤ 6 := by omega
    have he_le : e ≤ 6 := by omega
    have hf_le : f ≤ 6 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      interval_cases e <;> try omega
    all_goals
      interval_cases f <;> try omega
    all_goals
      solve
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, f, g, hparts⟩ := Multiset.card_eq_seven.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hf_pos : 0 < f := p.parts_pos (by simp [hparts])
    have hg_pos : 0 < g := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + (e + (f + (g)))))) = 11 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 5 := by omega
    have hb_le : b ≤ 5 := by omega
    have hc_le : c ≤ 5 := by omega
    have hd_le : d ≤ 5 := by omega
    have he_le : e ≤ 5 := by omega
    have hf_le : f ≤ 5 := by omega
    have hg_le : g ≤ 5 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      interval_cases e <;> try omega
    all_goals
      interval_cases f <;> try omega
    all_goals
      interval_cases g <;> try omega
    all_goals
      solve
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, f, g, h, hparts⟩ := Multiset.card_eq_eight.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hf_pos : 0 < f := p.parts_pos (by simp [hparts])
    have hg_pos : 0 < g := p.parts_pos (by simp [hparts])
    have hh_pos : 0 < h := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + (e + (f + (g + (h))))))) = 11 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 4 := by omega
    have hb_le : b ≤ 4 := by omega
    have hc_le : c ≤ 4 := by omega
    have hd_le : d ≤ 4 := by omega
    have he_le : e ≤ 4 := by omega
    have hf_le : f ≤ 4 := by omega
    have hg_le : g ≤ 4 := by omega
    have hh_le : h ≤ 4 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      interval_cases e <;> try omega
    all_goals
      interval_cases f <;> try omega
    all_goals
      interval_cases g <;> try omega
    all_goals
      interval_cases h <;> try omega
    all_goals
      solve
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, f, g, h, i, hparts⟩ := Multiset.card_eq_nine.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hf_pos : 0 < f := p.parts_pos (by simp [hparts])
    have hg_pos : 0 < g := p.parts_pos (by simp [hparts])
    have hh_pos : 0 < h := p.parts_pos (by simp [hparts])
    have hi_pos : 0 < i := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + (e + (f + (g + (h + (i)))))))) = 11 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 3 := by omega
    have hb_le : b ≤ 3 := by omega
    have hc_le : c ≤ 3 := by omega
    have hd_le : d ≤ 3 := by omega
    have he_le : e ≤ 3 := by omega
    have hf_le : f ≤ 3 := by omega
    have hg_le : g ≤ 3 := by omega
    have hh_le : h ≤ 3 := by omega
    have hi_le : i ≤ 3 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      interval_cases e <;> try omega
    all_goals
      interval_cases f <;> try omega
    all_goals
      interval_cases g <;> try omega
    all_goals
      interval_cases h <;> try omega
    all_goals
      interval_cases i <;> try omega
    all_goals
      solve
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, f, g, h, i, j, hparts⟩ := Multiset.card_eq_ten.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hf_pos : 0 < f := p.parts_pos (by simp [hparts])
    have hg_pos : 0 < g := p.parts_pos (by simp [hparts])
    have hh_pos : 0 < h := p.parts_pos (by simp [hparts])
    have hi_pos : 0 < i := p.parts_pos (by simp [hparts])
    have hj_pos : 0 < j := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + (e + (f + (g + (h + (i + (j))))))))) = 11 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 2 := by omega
    have hb_le : b ≤ 2 := by omega
    have hc_le : c ≤ 2 := by omega
    have hd_le : d ≤ 2 := by omega
    have he_le : e ≤ 2 := by omega
    have hf_le : f ≤ 2 := by omega
    have hg_le : g ≤ 2 := by omega
    have hh_le : h ≤ 2 := by omega
    have hi_le : i ≤ 2 := by omega
    have hj_le : j ≤ 2 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      interval_cases e <;> try omega
    all_goals
      interval_cases f <;> try omega
    all_goals
      interval_cases g <;> try omega
    all_goals
      interval_cases h <;> try omega
    all_goals
      interval_cases i <;> try omega
    all_goals
      interval_cases j <;> try omega
    all_goals
      solve
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; rw [hparts] <;> decide
  · obtain ⟨a, b, c, d, e, f, g, h, i, j, k, hparts⟩ := Multiset.card_eq_eleven.mp hcard
    have ha_pos : 0 < a := p.parts_pos (by simp [hparts])
    have hb_pos : 0 < b := p.parts_pos (by simp [hparts])
    have hc_pos : 0 < c := p.parts_pos (by simp [hparts])
    have hd_pos : 0 < d := p.parts_pos (by simp [hparts])
    have he_pos : 0 < e := p.parts_pos (by simp [hparts])
    have hf_pos : 0 < f := p.parts_pos (by simp [hparts])
    have hg_pos : 0 < g := p.parts_pos (by simp [hparts])
    have hh_pos : 0 < h := p.parts_pos (by simp [hparts])
    have hi_pos : 0 < i := p.parts_pos (by simp [hparts])
    have hj_pos : 0 < j := p.parts_pos (by simp [hparts])
    have hk_pos : 0 < k := p.parts_pos (by simp [hparts])
    have hsum : a + (b + (c + (d + (e + (f + (g + (h + (i + (j + (k)))))))))) = 11 := by simpa [hparts] using p.parts_sum
    have ha_le : a ≤ 1 := by omega
    have hb_le : b ≤ 1 := by omega
    have hc_le : c ≤ 1 := by omega
    have hd_le : d ≤ 1 := by omega
    have he_le : e ≤ 1 := by omega
    have hf_le : f ≤ 1 := by omega
    have hg_le : g ≤ 1 := by omega
    have hh_le : h ≤ 1 := by omega
    have hi_le : i ≤ 1 := by omega
    have hj_le : j ≤ 1 := by omega
    have hk_le : k ≤ 1 := by omega
    interval_cases a <;> try omega
    all_goals
      interval_cases b <;> try omega
    all_goals
      interval_cases c <;> try omega
    all_goals
      interval_cases d <;> try omega
    all_goals
      interval_cases e <;> try omega
    all_goals
      interval_cases f <;> try omega
    all_goals
      interval_cases g <;> try omega
    all_goals
      interval_cases h <;> try omega
    all_goals
      interval_cases i <;> try omega
    all_goals
      interval_cases j <;> try omega
    all_goals
      interval_cases k <;> try omega
    all_goals
      solve
      | right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; rw [hparts] <;> decide

set_option maxRecDepth 100000 in
private lemma partition_eleven_cases_from_parts (p : Nat.Partition 11)
    (hparts_cases :
      p.parts = ({11} : Multiset Nat) ∨ p.parts = ({1, 10} : Multiset Nat) ∨ p.parts = ({2, 9} : Multiset Nat) ∨ p.parts = ({1, 1, 9} : Multiset Nat) ∨ p.parts = ({3, 8} : Multiset Nat) ∨ p.parts = ({1, 2, 8} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 8} : Multiset Nat) ∨ p.parts = ({4, 7} : Multiset Nat) ∨ p.parts = ({1, 3, 7} : Multiset Nat) ∨ p.parts = ({2, 2, 7} : Multiset Nat) ∨ p.parts = ({1, 1, 2, 7} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 7} : Multiset Nat) ∨ p.parts = ({5, 6} : Multiset Nat) ∨ p.parts = ({1, 4, 6} : Multiset Nat) ∨ p.parts = ({2, 3, 6} : Multiset Nat) ∨ p.parts = ({1, 1, 3, 6} : Multiset Nat) ∨ p.parts = ({1, 2, 2, 6} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 2, 6} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 1, 6} : Multiset Nat) ∨ p.parts = ({1, 5, 5} : Multiset Nat) ∨ p.parts = ({2, 4, 5} : Multiset Nat) ∨ p.parts = ({1, 1, 4, 5} : Multiset Nat) ∨ p.parts = ({3, 3, 5} : Multiset Nat) ∨ p.parts = ({1, 2, 3, 5} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 3, 5} : Multiset Nat) ∨ p.parts = ({2, 2, 2, 5} : Multiset Nat) ∨ p.parts = ({1, 1, 2, 2, 5} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 2, 5} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 1, 1, 5} : Multiset Nat) ∨ p.parts = ({3, 4, 4} : Multiset Nat) ∨ p.parts = ({1, 2, 4, 4} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 4, 4} : Multiset Nat) ∨ p.parts = ({1, 3, 3, 4} : Multiset Nat) ∨ p.parts = ({2, 2, 3, 4} : Multiset Nat) ∨ p.parts = ({1, 1, 2, 3, 4} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 3, 4} : Multiset Nat) ∨ p.parts = ({1, 2, 2, 2, 4} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 2, 2, 4} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 1, 2, 4} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 1, 1, 1, 4} : Multiset Nat) ∨ p.parts = ({2, 3, 3, 3} : Multiset Nat) ∨ p.parts = ({1, 1, 3, 3, 3} : Multiset Nat) ∨ p.parts = ({1, 2, 2, 3, 3} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 2, 3, 3} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 1, 3, 3} : Multiset Nat) ∨ p.parts = ({2, 2, 2, 2, 3} : Multiset Nat) ∨ p.parts = ({1, 1, 2, 2, 2, 3} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 2, 2, 3} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 1, 1, 2, 3} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 1, 1, 1, 1, 3} : Multiset Nat) ∨ p.parts = ({1, 2, 2, 2, 2, 2} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 2, 2, 2, 2} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 1, 2, 2, 2} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 1, 1, 1, 2, 2} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 1, 1, 1, 1, 1, 2} : Multiset Nat) ∨ p.parts = ({1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1} : Multiset Nat)) :
    p = partitionOfPartsChecked 11 ({11} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 10} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({2, 9} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 9} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({3, 8} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 2, 8} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 8} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({4, 7} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 3, 7} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({2, 2, 7} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 2, 7} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 7} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({5, 6} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 4, 6} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({2, 3, 6} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 3, 6} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 2, 2, 6} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 2, 6} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 6} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 5, 5} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({2, 4, 5} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 4, 5} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({3, 3, 5} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 2, 3, 5} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 3, 5} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({2, 2, 2, 5} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 2, 2, 5} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 2, 5} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 1, 5} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({3, 4, 4} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 2, 4, 4} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 4, 4} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 3, 3, 4} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({2, 2, 3, 4} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 2, 3, 4} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 3, 4} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 2, 2, 2, 4} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 2, 2, 4} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 2, 4} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 1, 1, 4} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({2, 3, 3, 3} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 3, 3, 3} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 2, 2, 3, 3} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 2, 3, 3} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 3, 3} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({2, 2, 2, 2, 3} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 2, 2, 2, 3} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 2, 2, 3} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 1, 2, 3} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 1, 1, 1, 3} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 2, 2, 2, 2, 2} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 2, 2, 2, 2} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 2, 2, 2} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 1, 1, 2, 2} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 1, 1, 1, 1, 2} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1} : Multiset Nat) := by
  rcases hparts_cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    apply Nat.Partition.ext
    rw [h]
    simp [partitionOfPartsChecked, partitionOfParts]

set_option maxRecDepth 100000 in
private lemma partition_eleven_cases (p : Nat.Partition 11) :
    p = partitionOfPartsChecked 11 ({11} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 10} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({2, 9} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 9} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({3, 8} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 2, 8} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 8} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({4, 7} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 3, 7} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({2, 2, 7} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 2, 7} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 7} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({5, 6} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 4, 6} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({2, 3, 6} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 3, 6} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 2, 2, 6} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 2, 6} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 6} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 5, 5} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({2, 4, 5} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 4, 5} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({3, 3, 5} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 2, 3, 5} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 3, 5} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({2, 2, 2, 5} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 2, 2, 5} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 2, 5} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 1, 5} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({3, 4, 4} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 2, 4, 4} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 4, 4} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 3, 3, 4} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({2, 2, 3, 4} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 2, 3, 4} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 3, 4} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 2, 2, 2, 4} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 2, 2, 4} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 2, 4} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 1, 1, 4} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({2, 3, 3, 3} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 3, 3, 3} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 2, 2, 3, 3} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 2, 3, 3} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 3, 3} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({2, 2, 2, 2, 3} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 2, 2, 2, 3} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 2, 2, 3} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 1, 2, 3} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 1, 1, 1, 3} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 2, 2, 2, 2, 2} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 2, 2, 2, 2} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 2, 2, 2} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 1, 1, 2, 2} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 1, 1, 1, 1, 2} : Multiset Nat) ∨ p = partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1} : Multiset Nat) :=
  partition_eleven_cases_from_parts p (partition_eleven_parts_cases p)

private def partitionElevenSet : Finset (Nat.Partition 11) :=
  {partitionOfPartsChecked 11 ({11} : Multiset Nat), partitionOfPartsChecked 11 ({1, 10} : Multiset Nat), partitionOfPartsChecked 11 ({2, 9} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 9} : Multiset Nat), partitionOfPartsChecked 11 ({3, 8} : Multiset Nat), partitionOfPartsChecked 11 ({1, 2, 8} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 1, 8} : Multiset Nat), partitionOfPartsChecked 11 ({4, 7} : Multiset Nat), partitionOfPartsChecked 11 ({1, 3, 7} : Multiset Nat), partitionOfPartsChecked 11 ({2, 2, 7} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 2, 7} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 1, 1, 7} : Multiset Nat), partitionOfPartsChecked 11 ({5, 6} : Multiset Nat), partitionOfPartsChecked 11 ({1, 4, 6} : Multiset Nat), partitionOfPartsChecked 11 ({2, 3, 6} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 3, 6} : Multiset Nat), partitionOfPartsChecked 11 ({1, 2, 2, 6} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 1, 2, 6} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 6} : Multiset Nat), partitionOfPartsChecked 11 ({1, 5, 5} : Multiset Nat), partitionOfPartsChecked 11 ({2, 4, 5} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 4, 5} : Multiset Nat), partitionOfPartsChecked 11 ({3, 3, 5} : Multiset Nat), partitionOfPartsChecked 11 ({1, 2, 3, 5} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 1, 3, 5} : Multiset Nat), partitionOfPartsChecked 11 ({2, 2, 2, 5} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 2, 2, 5} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 1, 1, 2, 5} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 1, 5} : Multiset Nat), partitionOfPartsChecked 11 ({3, 4, 4} : Multiset Nat), partitionOfPartsChecked 11 ({1, 2, 4, 4} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 1, 4, 4} : Multiset Nat), partitionOfPartsChecked 11 ({1, 3, 3, 4} : Multiset Nat), partitionOfPartsChecked 11 ({2, 2, 3, 4} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 2, 3, 4} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 1, 1, 3, 4} : Multiset Nat), partitionOfPartsChecked 11 ({1, 2, 2, 2, 4} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 1, 2, 2, 4} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 2, 4} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 1, 1, 4} : Multiset Nat), partitionOfPartsChecked 11 ({2, 3, 3, 3} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 3, 3, 3} : Multiset Nat), partitionOfPartsChecked 11 ({1, 2, 2, 3, 3} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 1, 2, 3, 3} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 3, 3} : Multiset Nat), partitionOfPartsChecked 11 ({2, 2, 2, 2, 3} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 2, 2, 2, 3} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 1, 1, 2, 2, 3} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 1, 2, 3} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 1, 1, 1, 3} : Multiset Nat), partitionOfPartsChecked 11 ({1, 2, 2, 2, 2, 2} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 1, 2, 2, 2, 2} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 2, 2, 2} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 1, 1, 2, 2} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 1, 1, 1, 1, 2} : Multiset Nat), partitionOfPartsChecked 11 ({1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1} : Multiset Nat)}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
private lemma partition_eleven_mem (p : Nat.Partition 11) : p ∈ partitionElevenSet := by
  rcases partition_eleven_cases p with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]
  · rw [h]
    simp [partitionElevenSet]

/-- `p(0) = 1`. -/
theorem partitionCount_zero : partitionCount 0 = 1 := by
  simp [partitionCount]

/-- `p(1) = 1`. -/
theorem partitionCount_one : partitionCount 1 = 1 := by
  simp [partitionCount]

/-- `p(2) = 2`. -/
theorem partitionCount_two : partitionCount 2 = 2 := by
  classical
  have huniv :
      (Finset.univ : Finset (Nat.Partition 2)) = {partitionTwo, partitionOneOne} := by
    ext p
    simp [partition_two_cases p]
  rw [partitionCount, Fintype.card, huniv]
  decide

/-- `p(3) = 3`. -/
theorem partitionCount_three : partitionCount 3 = 3 := by
  classical
  have huniv :
      (Finset.univ : Finset (Nat.Partition 3)) =
        {partitionThree, partitionTwoOne, partitionOneOneOne} := by
    ext p
    simp [partition_three_cases p]
  rw [partitionCount, Fintype.card, huniv]
  decide

/-- `p(4) = 5` (Chan Example 1.1). -/
theorem partitionCount_four : partitionCount 4 = 5 := by
  classical
  have huniv :
      (Finset.univ : Finset (Nat.Partition 4)) =
        {partitionFour, partitionThreeOne, partitionTwoTwo, partitionTwoOneOne,
          partitionOneOneOneOne} := by
    ext p
    simp [partition_four_cases p]
  rw [partitionCount, Fintype.card, huniv]
  decide

/-- `p(5) = 7`. -/
theorem partitionCount_five : partitionCount 5 = 7 := by
  classical
  have huniv :
      (Finset.univ : Finset (Nat.Partition 5)) =
        {partitionFive, partitionFourOne, partitionThreeTwo, partitionThreeOneOne,
          partitionTwoTwoOne, partitionTwoOneOneOne, partitionOneOneOneOneOne} := by
    ext p
    simp [partition_five_cases p]
  rw [partitionCount, Fintype.card, huniv]
  decide

/-- `p(6) = 11`. -/
theorem partitionCount_six : partitionCount 6 = 11 := by
  classical
  have huniv :
      (Finset.univ : Finset (Nat.Partition 6)) =
        {partitionSix, partitionFiveOne, partitionFourTwo, partitionFourOneOne,
          partitionThreeThree, partitionThreeTwoOne, partitionThreeOneOneOne,
          partitionTwoTwoTwo, partitionTwoTwoOneOne, partitionTwoOneOneOneOne,
          partitionOneOneOneOneOneOne} := by
    ext p
    simp [partition_six_cases p]
  rw [partitionCount, Fintype.card, huniv]
  decide

/-- `p(7) = 15`. -/
theorem partitionCount_seven : partitionCount 7 = 15 := by
  classical
  have huniv :
      (Finset.univ : Finset (Nat.Partition 7)) =
        {partitionSeven, partitionSixOne, partitionFiveTwo, partitionFiveOneOne, partitionFourThree, partitionFourTwoOne, partitionFourOneOneOne, partitionThreeThreeOne, partitionThreeTwoTwo, partitionThreeTwoOneOne, partitionThreeOneOneOneOne, partitionTwoTwoTwoOne, partitionTwoTwoOneOneOne, partitionTwoOneOneOneOneOne, partitionOneOneOneOneOneOneOne} := by
    ext p
    simp [partition_seven_cases p]
  rw [partitionCount, Fintype.card, huniv]
  decide

/-- `p(8) = 22`. -/
theorem partitionCount_eight : partitionCount 8 = 22 := by
  classical
  have huniv :
      (Finset.univ : Finset (Nat.Partition 8)) =
        {partitionEight, partitionSevenOne, partitionSixTwo, partitionSixOneOne, partitionFiveThree, partitionFiveTwoOne, partitionFiveOneOneOne, partitionFourFour, partitionFourThreeOne, partitionFourTwoTwo, partitionFourTwoOneOne, partitionFourOneOneOneOne, partitionThreeThreeTwo, partitionThreeThreeOneOne, partitionThreeTwoTwoOne, partitionThreeTwoOneOneOne, partitionThreeOneOneOneOneOne, partitionTwoTwoTwoTwo, partitionTwoTwoTwoOneOne, partitionTwoTwoOneOneOneOne, partitionTwoOneOneOneOneOneOne, partitionOneOneOneOneOneOneOneOne} := by
    ext p
    simp [partition_eight_cases p]
  rw [partitionCount, Fintype.card, huniv]
  decide

/-- `p(9) = 30`. -/
theorem partitionCount_nine : partitionCount 9 = 30 := by
  classical
  have huniv :
      (Finset.univ : Finset (Nat.Partition 9)) =
        {partitionNine, partitionEightOne, partitionSevenTwo, partitionSevenOneOne, partitionSixThree, partitionSixTwoOne, partitionSixOneOneOne, partitionFiveFour, partitionFiveThreeOne, partitionFiveTwoTwo, partitionFiveTwoOneOne, partitionFiveOneOneOneOne, partitionFourFourOne, partitionFourThreeTwo, partitionFourThreeOneOne, partitionFourTwoTwoOne, partitionFourTwoOneOneOne, partitionFourOneOneOneOneOne, partitionThreeThreeThree, partitionThreeThreeTwoOne, partitionThreeThreeOneOneOne, partitionThreeTwoTwoTwo, partitionThreeTwoTwoOneOne, partitionThreeTwoOneOneOneOne, partitionThreeOneOneOneOneOneOne, partitionTwoTwoTwoTwoOne, partitionTwoTwoTwoOneOneOne, partitionTwoTwoOneOneOneOneOne, partitionTwoOneOneOneOneOneOneOne, partitionOneOneOneOneOneOneOneOneOne} := by
    ext p
    simp [partition_nine_cases p]
  rw [partitionCount, Fintype.card, huniv]
  decide

/-- `p(10) = 42`. -/
theorem partitionCount_ten : partitionCount 10 = 42 := by
  classical
  have huniv :
      (Finset.univ : Finset (Nat.Partition 10)) =
        {partitionTen, partitionNineOne, partitionEightTwo, partitionEightOneOne, partitionSevenThree, partitionSevenTwoOne, partitionSevenOneOneOne, partitionSixFour, partitionSixThreeOne, partitionSixTwoTwo, partitionSixTwoOneOne, partitionSixOneOneOneOne, partitionFiveFive, partitionFiveFourOne, partitionFiveThreeTwo, partitionFiveThreeOneOne, partitionFiveTwoTwoOne, partitionFiveTwoOneOneOne, partitionFiveOneOneOneOneOne, partitionFourFourTwo, partitionFourFourOneOne, partitionFourThreeThree, partitionFourThreeTwoOne, partitionFourThreeOneOneOne, partitionFourTwoTwoTwo, partitionFourTwoTwoOneOne, partitionFourTwoOneOneOneOne, partitionFourOneOneOneOneOneOne, partitionThreeThreeThreeOne, partitionThreeThreeTwoTwo, partitionThreeThreeTwoOneOne, partitionThreeThreeOneOneOneOne, partitionThreeTwoTwoTwoOne, partitionThreeTwoTwoOneOneOne, partitionThreeTwoOneOneOneOneOne, partitionThreeOneOneOneOneOneOneOne, partitionTwoTwoTwoTwoTwo, partitionTwoTwoTwoTwoOneOne, partitionTwoTwoTwoOneOneOneOne, partitionTwoTwoOneOneOneOneOneOne, partitionTwoOneOneOneOneOneOneOneOne, partitionOneOneOneOneOneOneOneOneOneOne} := by
    ext p
    simp [partition_ten_cases p]
  rw [partitionCount, Fintype.card, huniv]
  decide


set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- `p(11) = 56`. -/
theorem partitionCount_eleven : partitionCount 11 = 56 := by
  classical
  have huniv :
      (Finset.univ : Finset (Nat.Partition 11)) = partitionElevenSet := by
    ext p
    constructor
    · intro _
      exact partition_eleven_mem p
    · intro _
      simp
  rw [partitionCount, Fintype.card, huniv]
  decide

/-- The pentagonal recurrence agrees with `partitionCount` at `0`. -/
theorem partitionCountRec_eq_partitionCount_zero : partitionCountRec 0 = partitionCount 0 := by
  rw [partitionCount_zero]
  decide

/-- The pentagonal recurrence agrees with `partitionCount` at `1`. -/
theorem partitionCountRec_eq_partitionCount_one : partitionCountRec 1 = partitionCount 1 := by
  rw [partitionCount_one]
  decide

/-- The pentagonal recurrence agrees with `partitionCount` at `2`. -/
theorem partitionCountRec_eq_partitionCount_two : partitionCountRec 2 = partitionCount 2 := by
  rw [partitionCount_two]
  decide

/-- The pentagonal recurrence agrees with `partitionCount` at `3`. -/
theorem partitionCountRec_eq_partitionCount_three : partitionCountRec 3 = partitionCount 3 := by
  rw [partitionCount_three]
  decide

/-- The pentagonal recurrence agrees with `partitionCount` at `4`. -/
theorem partitionCountRec_eq_partitionCount_four : partitionCountRec 4 = partitionCount 4 := by
  rw [partitionCount_four]
  decide

/-- The pentagonal recurrence agrees with `partitionCount` at `5`. -/
theorem partitionCountRec_eq_partitionCount_five : partitionCountRec 5 = partitionCount 5 := by
  rw [partitionCount_five]
  decide

/-- The pentagonal recurrence agrees with `partitionCount` at `6`. -/
theorem partitionCountRec_eq_partitionCount_six : partitionCountRec 6 = partitionCount 6 := by
  rw [partitionCount_six]
  decide

/-- The pentagonal recurrence agrees with `partitionCount` at `7`. -/
theorem partitionCountRec_eq_partitionCount_seven : partitionCountRec 7 = partitionCount 7 := by
  rw [partitionCount_seven]
  decide

/-- The pentagonal recurrence agrees with `partitionCount` at `8`. -/
theorem partitionCountRec_eq_partitionCount_eight : partitionCountRec 8 = partitionCount 8 := by
  rw [partitionCount_eight]
  decide

/-- The pentagonal recurrence agrees with `partitionCount` at `9`. -/
theorem partitionCountRec_eq_partitionCount_nine : partitionCountRec 9 = partitionCount 9 := by
  rw [partitionCount_nine]
  decide

/-- The pentagonal recurrence agrees with `partitionCount` at `10`. -/
theorem partitionCountRec_eq_partitionCount_ten : partitionCountRec 10 = partitionCount 10 := by
  rw [partitionCount_ten]
  decide

/-- The pentagonal recurrence agrees with `partitionCount` at `11`. -/
theorem partitionCountRec_eq_partitionCount_eleven : partitionCountRec 11 = partitionCount 11 := by
  rw [partitionCount_eleven]
  decide

section CommRing

variable {R : Type*} [CommRing R]

/-- Truncated partition generating function `∑_{n=0}^N p(n) q^n`. -/
def partitionGenFn (q : R) (N : Nat) : R :=
  natSum (fun n => (partitionCount n : R) * q ^ n) N

/-- Recursion: `partitionGenFn q (N+1) = partitionGenFn q N + p(N+1) · q^(N+1)`. -/
theorem partitionGenFn_succ (q : R) (N : Nat) :
    partitionGenFn q (N + 1) =
      partitionGenFn q N + (partitionCount (N + 1) : R) * q ^ (N + 1) := by
  simp [partitionGenFn]

/-- Concrete value for `N = 4`: matches Chan's `1 + q + 2q^2 + 3q^3 + 5q^4`. -/
theorem partitionGenFn_four (q : R) :
    partitionGenFn q 4 = 1 + q + 2 * q^2 + 3 * q^3 + 5 * q^4 := by
  simp [partitionGenFn, natSum, partitionCount_zero, partitionCount_one,
    partitionCount_two, partitionCount_three, partitionCount_four]

/-- Concrete value for `N = 10`: the partition numbers `p(0)` through `p(10)`. -/
theorem partitionGenFn_ten (q : R) :
    partitionGenFn q 10 =
      1 + q + 2 * q^2 + 3 * q^3 + 5 * q^4 +
      7 * q^5 + 11 * q^6 + 15 * q^7 + 22 * q^8 + 30 * q^9 + 42 * q^10 := by
  simp [partitionGenFn, natSum, partitionCount_zero, partitionCount_one,
    partitionCount_two, partitionCount_three, partitionCount_four, partitionCount_five,
    partitionCount_six, partitionCount_seven, partitionCount_eight, partitionCount_nine,
    partitionCount_ten]

/-- Concrete value for `N = 11`: the partition numbers `p(0)` through `p(11)`. -/
theorem partitionGenFn_eleven (q : R) :
    partitionGenFn q 11 =
      1 + q + 2 * q^2 + 3 * q^3 + 5 * q^4 + 7 * q^5 + 11 * q^6 + 15 * q^7 +
      22 * q^8 + 30 * q^9 + 42 * q^10 + 56 * q^11 := by
  simp [partitionGenFn, natSum, partitionCount_zero, partitionCount_one,
    partitionCount_two, partitionCount_three, partitionCount_four, partitionCount_five,
    partitionCount_six, partitionCount_seven, partitionCount_eight, partitionCount_nine,
    partitionCount_ten, partitionCount_eleven]

end CommRing

end Ch01
end QseriesFormalization
