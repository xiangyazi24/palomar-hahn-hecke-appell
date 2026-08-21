import QseriesFormalization.Pending.Chapter10_HM
import QseriesFormalization.Chapter19_JacobiTripleSignChar

/-!
# `J₁³` as a `QLaurent` object for the Chapter 10 same-sign diagonal

This file packages

  J₁³ = ∑_{i≥0} (-1)^i (2i+1) Q^{i(i+1)/2}

as a `QLaurent`, compatible with the `Ch10HM` Laurent/Hahn layer.
The coefficient formula reuses the existing Chapter 19 API for

  `jacobiTripleSign`.

The main object is `J1CubeLaurent`; the diagonal monomial multiple is
`diagJ1CubeLaurent t`.
-/

namespace QseriesFormalization.Pending.Ch10M3J1Cube

open QseriesFormalization.Pending.Ch10HM
open QseriesFormalization.PartIV.Ch19
open scoped LaurentSeries

noncomputable section

/-- Natural triangular exponent `i(i+1)/2`, cast into the Laurent exponent group `ℤ`. -/
def Tnat (i : ℕ) : ℤ :=
  ((i * (i + 1) / 2 : ℕ) : ℤ)

/-- Integer triangular exponent `z(z-1)/2`. -/
def Tint (z : ℤ) : ℤ :=
  z * (z - 1) / 2

@[simp] theorem Tnat_toNat (i : ℕ) :
    (Tnat i).toNat = i * (i + 1) / 2 := by
  unfold Tnat
  exact Int.toNat_natCast _

theorem Tnat_nonneg (i : ℕ) :
    0 ≤ Tnat i := by
  unfold Tnat
  exact Int.natCast_nonneg _

theorem Tnat_strictMono : StrictMono Tnat := by
  intro a b hab
  unfold Tnat
  exact_mod_cast (triangular_strictMono hab)

theorem Tnat_injective : Function.Injective Tnat :=
  Tnat_strictMono.injective

/-- If an integer exponent is known to be the `i`-th triangular exponent,
then the index is bounded by the exponent's `toNat`.

This is the finite co-support bound for the `ℕ`-indexed family.
-/
theorem Tnat_root_le_toNat {i : ℕ} {e : ℤ} (hroot : Tnat i = e) :
    i ≤ e.toNat := by
  have hi : i ≤ (Tnat i).toNat := by
    rw [Tnat_toNat]
    exact k_le_triangular i
  simpa [hroot] using hi

/-- Convert a nonnegative integer exponent with triangular `toNat` back to `Tnat`. -/
theorem Tnat_eq_of_toNat_eq {e : ℤ} (he : 0 ≤ e) {i : ℕ}
    (h : e.toNat = i * (i + 1) / 2) :
    Tnat i = e := by
  have hcast : ((i * (i + 1) / 2 : ℕ) : ℤ) = (e.toNat : ℤ) := by
    exact_mod_cast h.symm
  calc
    Tnat i = ((i * (i + 1) / 2 : ℕ) : ℤ) := rfl
    _ = (e.toNat : ℤ) := hcast
    _ = e := Int.toNat_of_nonneg he

/-- If `Tnat i = e`, then `e.toNat` is the corresponding natural triangular number. -/
theorem toNat_eq_of_Tnat_eq {i : ℕ} {e : ℤ} (hroot : Tnat i = e) :
    e.toNat = i * (i + 1) / 2 := by
  have h := congrArg Int.toNat hroot
  simpa [Tnat] using h.symm

private theorem J1Cube_cosupport_bound {e : ℤ} {i : ℕ} (hroot : Tnat i = e) :
    i ∈ Finset.range (e.toNat + 1) := by
  rw [Finset.mem_range]
  exact Nat.lt_succ_of_le (Tnat_root_le_toNat hroot)

/-- The coefficient weight `(-1)^i (2i+1)` as a rational number. -/
def j1CubeWeight (i : ℕ) : ℚ :=
  (((-1 : ℤ) ^ i * (2 * (i : ℤ) + 1) : ℤ) : ℚ)

/-- One monomial of `J₁³`: `(-1)^i(2i+1) Q^{i(i+1)/2}`. -/
noncomputable def J1CubeTerm (i : ℕ) : QLaurent :=
  ((j1CubeWeight i : ℚ) : QLaurent) * Qpow (Tnat i)

/-- Coefficient of one `J₁³` monomial. -/
@[simp] theorem lcoeff_J1CubeTerm (i : ℕ) (e : ℤ) :
    lcoeff (J1CubeTerm i) e =
      if Tnat i = e then j1CubeWeight i else 0 := by
  unfold J1CubeTerm Qpow lcoeff
  rw [show (((j1CubeWeight i : ℚ) : QLaurent) *
        HahnSeries.single (Tnat i) (1 : ℚ)) =
      HahnSeries.single (Tnat i) (j1CubeWeight i : ℚ) by
        change HahnSeries.single (0 : ℤ) (j1CubeWeight i : ℚ) *
            HahnSeries.single (Tnat i) (1 : ℚ) =
          HahnSeries.single (Tnat i) (j1CubeWeight i : ℚ)
        rw [HahnSeries.single_mul_single]
        simp]
  by_cases h : Tnat i = e
  · simp [h]
  · have h' : e ≠ Tnat i := fun he => h he.symm
    simp [h, h']

/-- The weighted summable family for `J₁³`.

Support is bounded below by `0`, and coefficient support at exponent `e`
is contained in `Finset.range (e.toNat + 1)`.
-/
noncomputable def J1CubeFamily : HahnSeries.SummableFamily ℤ ℚ ℕ where
  toFun i := J1CubeTerm i
  isPWO_iUnion_support' := by
    refine ((BddBelow.isWF (⟨0, fun e he => he⟩ :
        BddBelow {e : ℤ | 0 ≤ e})).isPWO).mono ?_
    intro e he
    rw [Set.mem_iUnion] at he
    rcases he with ⟨i, hi⟩
    rw [HahnSeries.mem_support] at hi
    change lcoeff (J1CubeTerm i) e ≠ 0 at hi
    rw [lcoeff_J1CubeTerm] at hi
    by_cases hroot : Tnat i = e
    · simpa [hroot] using Tnat_nonneg i
    · simp [hroot] at hi
  finite_co_support' e := by
    refine (Finset.range (e.toNat + 1)).finite_toSet.subset ?_
    intro i hi
    rw [Set.mem_setOf_eq] at hi
    change (J1CubeTerm i).coeff e ≠ 0 at hi
    change lcoeff (J1CubeTerm i) e ≠ 0 at hi
    rw [lcoeff_J1CubeTerm] at hi
    by_cases hroot : Tnat i = e
    · exact J1Cube_cosupport_bound hroot
    · simp [hroot] at hi

/-- Coefficient function for the `QLaurent` version of `J₁³`.

This reuses the existing Chapter 19 coefficient package:
`jacobiTripleSign n = (-1)^i(2i+1)` at triangular `n = i(i+1)/2`,
and `0` otherwise.
-/
def J1CubeCoeff (e : ℤ) : ℚ :=
  if 0 ≤ e then ((jacobiTripleSign e.toNat : ℤ) : ℚ) else 0

/-- Negative exponents of `J₁³` vanish. -/
theorem J1CubeCoeff_of_neg {e : ℤ} (he : e < 0) :
    J1CubeCoeff e = 0 := by
  have hn : ¬ 0 ≤ e := by omega
  simp [J1CubeCoeff, hn]

/-- `J₁³` as a `QLaurent`. -/
noncomputable def J1CubeLaurent : QLaurent :=
  HahnSeries.ofSuppBddBelow J1CubeCoeff <| by
    refine ⟨0, ?_⟩
    intro e he
    by_contra hle
    have hlt : e < 0 := by omega
    have hz : J1CubeCoeff e = 0 := J1CubeCoeff_of_neg hlt
    exact he hz

/-- Coefficient extraction for `J1CubeLaurent`. -/
@[simp] theorem lcoeff_J1CubeLaurent (e : ℤ) :
    lcoeff J1CubeLaurent e = J1CubeCoeff e := by
  simp [lcoeff, J1CubeLaurent]

/-- Triangular coefficient formula:
`[Q^{i(i+1)/2}] J₁³ = (-1)^i(2i+1)`. -/
theorem J1CubeCoeff_triangular (i : ℕ) :
    J1CubeCoeff (Tnat i) = j1CubeWeight i := by
  unfold J1CubeCoeff
  rw [if_pos (Tnat_nonneg i)]
  rw [Tnat_toNat, jacobiTripleSign_triangular]
  unfold j1CubeWeight
  rfl

/-- Non-triangular coefficients of `J₁³` vanish. -/
theorem J1CubeCoeff_of_not_triangular {e : ℤ} (he : 0 ≤ e)
    (hno : ∀ k ≤ e.toNat, e.toNat ≠ k * (k + 1) / 2) :
    J1CubeCoeff e = 0 := by
  unfold J1CubeCoeff
  rw [if_pos he]
  rw [jacobiTripleSign_of_not_triangular e.toNat hno]
  simp

/-- The explicit finite coefficient sum for `J₁³` equals the `jacobiTripleSign`
coefficient package. -/
theorem J1Cube_range_sum_eq_coeff (e : ℤ) :
    (∑ i ∈ Finset.range (e.toNat + 1),
        if Tnat i = e then j1CubeWeight i else 0) = J1CubeCoeff e := by
  by_cases he : 0 ≤ e
  · by_cases htri : ∃ k ≤ e.toNat, e.toNat = k * (k + 1) / 2
    · rcases htri with ⟨k, hkle, hktri⟩
      have hkroot : Tnat k = e := Tnat_eq_of_toNat_eq he hktri
      have hkmem : k ∈ Finset.range (e.toNat + 1) := by
        rw [Finset.mem_range]
        omega
      have hsum :
          (∑ i ∈ Finset.range (e.toNat + 1),
              if Tnat i = e then j1CubeWeight i else 0)
            = (if Tnat k = e then j1CubeWeight k else 0) := by
        refine Finset.sum_eq_single k ?_ ?_
        · intro i hi hik
          have hnot : ¬ Tnat i = e := by
            intro hiroot
            apply hik
            exact Tnat_injective (hiroot.trans hkroot.symm)
          simp [hnot]
        · intro hknot
          exact False.elim (hknot hkmem)
      rw [hsum]
      simp [hkroot]
      rw [← hkroot, J1CubeCoeff_triangular]
    · push_neg at htri
      have hsum0 :
          (∑ i ∈ Finset.range (e.toNat + 1),
              if Tnat i = e then j1CubeWeight i else 0) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        have hnot : ¬ Tnat i = e := by
          intro hiroot
          have hile : i ≤ e.toNat := by
            rw [Finset.mem_range] at hi
            omega
          have htri_i : e.toNat = i * (i + 1) / 2 :=
            toNat_eq_of_Tnat_eq hiroot
          exact htri i hile htri_i
        simp [hnot]
      rw [hsum0, J1CubeCoeff_of_not_triangular he htri]
  · have hneg : e < 0 := by omega
    have hsum0 :
        (∑ i ∈ Finset.range (e.toNat + 1),
            if Tnat i = e then j1CubeWeight i else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      have hnot : ¬ Tnat i = e := by
        intro hroot
        have hnon := Tnat_nonneg i
        omega
      simp [hnot]
    rw [hsum0, J1CubeCoeff_of_neg hneg]

/-- The weighted family sums to the coefficient-defined `J₁³` object. -/
theorem J1CubeLaurent_eq_hsum :
    J1CubeLaurent = J1CubeFamily.hsum := by
  ext e
  change lcoeff J1CubeLaurent e = lcoeff J1CubeFamily.hsum e
  rw [lcoeff_J1CubeLaurent]
  symm
  change J1CubeFamily.hsum.coeff e = J1CubeCoeff e
  rw [HahnSeries.SummableFamily.coeff_hsum_eq_sum_of_subset
    (s := J1CubeFamily) (g := e) (t := Finset.range (e.toNat + 1))]
  · rw [← J1Cube_range_sum_eq_coeff e]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    change (J1CubeTerm i).coeff e =
      if Tnat i = e then j1CubeWeight i else 0
    change lcoeff (J1CubeTerm i) e =
      if Tnat i = e then j1CubeWeight i else 0
    rw [lcoeff_J1CubeTerm]
  · intro i hi
    change (J1CubeTerm i).coeff e ≠ 0 at hi
    change lcoeff (J1CubeTerm i) e ≠ 0 at hi
    rw [lcoeff_J1CubeTerm] at hi
    by_cases hroot : Tnat i = e
    · exact J1Cube_cosupport_bound hroot
    · simp [hroot] at hi

/-- Coefficient form of `J1CubeLaurent_eq_hsum`. -/
theorem lcoeff_J1CubeFamily_hsum (e : ℤ) :
    lcoeff J1CubeFamily.hsum e = J1CubeCoeff e := by
  rw [← J1CubeLaurent_eq_hsum]
  simp

/-- The diagonal RHS factor:
`(-1)^t Q^{T(t)} J₁³`, where `T(t)=t(t-1)/2`.

This is the object that should match the `x^t y^t` coefficient of
`J₁³ * j(xy;q)`.
-/
noncomputable def diagJ1CubeLaurent (t : ℤ) : QLaurent :=
  ((negOnePowIntQ t : ℚ) : QLaurent) * Qpow (Tint t) * J1CubeLaurent

/-- Coefficient extraction from the diagonal monomial multiple. -/
theorem lcoeff_diagJ1CubeLaurent (t N : ℤ) :
    lcoeff (diagJ1CubeLaurent t) N =
      negOnePowIntQ t * J1CubeCoeff (N - Tint t) := by
  unfold diagJ1CubeLaurent
  rw [show ((negOnePowIntQ t : ℚ) : QLaurent) * Qpow (Tint t) * J1CubeLaurent =
      ((negOnePowIntQ t : ℚ) : QLaurent) * (Qpow (Tint t) * J1CubeLaurent) by ring]
  change lcoeff
      ((HahnSeries.single (0 : ℤ) (negOnePowIntQ t : ℚ) : QLaurent) *
        (Qpow (Tint t) * J1CubeLaurent)) N =
    negOnePowIntQ t * J1CubeCoeff (N - Tint t)
  rw [lcoeff, HahnSeries.coeff_single_mul]
  simp only [sub_zero]
  change negOnePowIntQ t * lcoeff (Qpow (Tint t) * J1CubeLaurent) N =
    negOnePowIntQ t * J1CubeCoeff (N - Tint t)
  rw [lcoeff_Qpow_mul, lcoeff_J1CubeLaurent]

/-- Triangular coefficient of the diagonal factor. -/
theorem lcoeff_diagJ1CubeLaurent_triangular (t : ℤ) (i : ℕ) :
    lcoeff (diagJ1CubeLaurent t) (Tint t + Tnat i) =
      negOnePowIntQ t * j1CubeWeight i := by
  rw [lcoeff_diagJ1CubeLaurent]
  have hshift : Tint t + Tnat i - Tint t = Tnat i := by omega
  rw [hshift, J1CubeCoeff_triangular]

/-- Hsum version of the diagonal factor. -/
theorem diagJ1CubeLaurent_eq_hsum (t : ℤ) :
    diagJ1CubeLaurent t =
      ((negOnePowIntQ t : ℚ) : QLaurent) * Qpow (Tint t) * J1CubeFamily.hsum := by
  unfold diagJ1CubeLaurent
  rw [J1CubeLaurent_eq_hsum]

end

end QseriesFormalization.Pending.Ch10M3J1Cube
