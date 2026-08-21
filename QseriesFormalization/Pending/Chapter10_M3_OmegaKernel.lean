import Mathlib

/-!
# The same-sign line kernel `ω_L` — elementary telescoping (chan1, the 1ψ1 core)

The HM n=2,p=1 same-sign 1ψ1 kernel reduces (chan1) to the line-sign function
`ω_L(v) = sg(L−v, v)` and two finite identities: `ω_L(v) − ω_L(v−1) = 1_{v=0} − 1_{v=L+1}`
(telescoping) and `∑_v ω_L(v) = L+1`. These are elementary; no analytic 1ψ1 needed.
-/

namespace QseriesFormalization.Pending.Ch10M3OmegaKernel

/-- Same-sign indicator `sg(r,s)`: `+1` if both ≥0, `−1` if both <0, else 0. -/
def sg (r s : ℤ) : ℤ :=
  if 0 ≤ r ∧ 0 ≤ s then 1 else if r < 0 ∧ s < 0 then -1 else 0

/-- The line-sign function `ω_L(v) = sg(L−v, v)`. -/
def omega (L v : ℤ) : ℤ := sg (L - v) v

/-- Closed form: `ω_L(v) = 1` on `0 ≤ v ≤ L`, `−1` on `L < v < 0`, else `0`. -/
theorem omega_eq (L v : ℤ) :
    omega L v = if 0 ≤ v ∧ v ≤ L then 1 else if L < v ∧ v < 0 then -1 else 0 := by
  unfold omega sg
  by_cases h1 : 0 ≤ L - v ∧ 0 ≤ v
  · rw [if_pos h1]
    have : 0 ≤ v ∧ v ≤ L := ⟨h1.2, by omega⟩
    rw [if_pos this]
  · rw [if_neg h1]
    by_cases h2 : L - v < 0 ∧ v < 0
    · rw [if_pos h2]
      have hL : L < v ∧ v < 0 := ⟨by omega, h2.2⟩
      have : ¬ (0 ≤ v ∧ v ≤ L) := by omega
      rw [if_neg this, if_pos hL]
    · rw [if_neg h2]
      have a1 : ¬ (0 ≤ v ∧ v ≤ L) := by omega
      have a2 : ¬ (L < v ∧ v < 0) := by omega
      rw [if_neg a1, if_neg a2]

/-- THE telescoping identity: adjacent `ω` differences cancel except at the two endpoints. -/
theorem omega_telescope (L v : ℤ) :
    omega L v - omega L (v - 1) =
      (if v = 0 then 1 else 0) - (if v = L + 1 then 1 else 0) := by
  rw [omega_eq, omega_eq]
  rcases lt_trichotomy L 0 with hL | hL | hL
  · -- L < 0: ω is -1 on (L,0)
    by_cases h0 : v = 0 <;> by_cases hL1 : v = L + 1 <;> simp_all <;> omega
  · subst hL; by_cases h0 : v = 0 <;> by_cases hL1 : v = 1 <;> simp_all <;> omega
  · -- L > 0: ω is 1 on [0,L]
    by_cases h0 : v = 0 <;> by_cases hL1 : v = L + 1 <;> simp_all <;> omega

/-- `ω_L` as a single signed indicator over `Finset.Icc`, for `L ≥ 0`. -/
theorem omega_as_indicator_nonneg {L : ℤ} (hL : 0 ≤ L) (v : ℤ) :
    omega L v = if v ∈ Finset.Icc (0 : ℤ) L then (1 : ℤ) else 0 := by
  rw [omega_eq]
  simp only [Finset.mem_Icc]
  by_cases h : 0 ≤ v ∧ v ≤ L
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    have hmid : ¬ (L < v ∧ v < 0) := by omega
    rw [if_neg hmid]

/-- `ω_L` as a single signed indicator over `Finset.Icc`, for `L < 0`. -/
theorem omega_as_indicator_neg {L : ℤ} (hL : L < 0) (v : ℤ) :
    omega L v = if v ∈ Finset.Icc (L + 1) (-1 : ℤ) then (-1 : ℤ) else 0 := by
  rw [omega_eq]
  simp only [Finset.mem_Icc]
  have htop : ¬ (0 ≤ v ∧ v ≤ L) := by omega
  rw [if_neg htop]
  by_cases h : L < v ∧ v < 0
  · rw [if_pos h, if_pos (by omega : L + 1 ≤ v ∧ v ≤ -1)]
  · rw [if_neg h, if_neg (by omega : ¬ (L + 1 ≤ v ∧ v ≤ -1))]

/-- THE diagonal-collapse identity: `∑_v ω_L(v) = L + 1`. -/
theorem omega_sum (L : ℤ) : ∑ᶠ v : ℤ, omega L v = L + 1 := by
  by_cases hL : 0 ≤ L
  · -- L ≥ 0: ω = indicator of Icc 0 L, sum = card = L+1
    have hsub : Function.support (fun v : ℤ => omega L v) ⊆ ↑(Finset.Icc (0 : ℤ) L) := by
      intro v hv
      simp only [Function.mem_support, omega_as_indicator_nonneg hL] at hv
      simp only [Finset.coe_Icc, Set.mem_Icc]
      by_contra h
      rw [if_neg (fun hmem => h (Finset.mem_Icc.mp hmem))] at hv
      exact hv rfl
    rw [finsum_eq_finsetSum_of_support_subset _ hsub]
    have hcong : ∀ v ∈ Finset.Icc (0 : ℤ) L, omega L v = (1 : ℤ) := by
      intro v hv; rw [omega_as_indicator_nonneg hL, if_pos hv]
    rw [Finset.sum_congr rfl hcong, Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
    omega
  · -- L < 0: ω = −indicator of Icc (L+1) (−1), sum = −card = L+1
    have hLneg : L < 0 := by omega
    have hsub : Function.support (fun v : ℤ => omega L v) ⊆ ↑(Finset.Icc (L + 1) (-1 : ℤ)) := by
      intro v hv
      simp only [Function.mem_support, omega_as_indicator_neg hLneg] at hv
      simp only [Finset.coe_Icc, Set.mem_Icc]
      by_contra h
      rw [if_neg (fun hmem => h (Finset.mem_Icc.mp hmem))] at hv
      exact hv rfl
    rw [finsum_eq_finsetSum_of_support_subset _ hsub]
    have hcong : ∀ v ∈ Finset.Icc (L + 1) (-1 : ℤ), omega L v = (-1 : ℤ) := by
      intro v hv; rw [omega_as_indicator_neg hLneg, if_pos hv]
    rw [Finset.sum_congr rfl hcong, Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
    omega

end QseriesFormalization.Pending.Ch10M3OmegaKernel
