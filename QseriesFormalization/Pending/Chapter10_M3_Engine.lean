import QseriesFormalization.Pending.Chapter10_TwoVar

open scoped Classical

namespace QseriesFormalization.Pending.Ch10M3Engine

open QseriesFormalization.Ch10TwoVar

noncomputable section

/-!
Step-1 monomial transport for the two-variable Chapter 10 Hahn-series kernel.

The x-slice is represented as the full family of y-slices
`j ↦ coeffXY F n j`, so a step in x may honestly transport the y-degree.
-/

/-- The full `x^n` slice, represented by its `y^j` coefficient series. -/
abbrev QYSlice := ℤ → K

/-- Extract the full `x^n` slice of a two-variable Hahn series. -/
noncomputable def sliceX (F : S) (n : ℤ) : QYSlice :=
  fun j => coeffXY F n j

/-- Multiply a Q/y-slice by a `K` scalar. -/
noncomputable def scaleQY (c : K) (A : QYSlice) : QYSlice :=
  fun j => c * A j

/-- Shift a Q/y-slice by `Q^q y^y`. -/
noncomputable def shiftQY (q y : ℤ) (A : QYSlice) : QYSlice :=
  fun j => Qpow q * A (j - y)

/-- The affine Q-shift `α n + β`. -/
def affineQ (α β n : ℤ) : ℤ := α * n + β

/-- The closed-form Q-shift accumulated from `α (n+k) + β` over `k = 0, ..., t-1`. -/
def step1QSum (α β n t : ℤ) : ℤ := α * Tn t + (α * n + β) * t

/-- Multiplication by a Q/x/y monomial. -/
noncomputable def shiftS (v : ℤ × ℤ × ℤ) (F : S) : S :=
  monom v.1 v.2.1 v.2.2 1 * F

/-- General monomial-times-slice lemma: a monomial shifts Q, x, and y degrees. -/
theorem coeffXY_monom_mul_all (a i j : ℤ) (c : ℚ) (F : S) (n m : ℤ) :
    coeffXY (monom a i j c * F) n m =
      HahnSeries.single a c * coeffXY F (n - i) (m - j) := by
  have hneg : -expQXY a i j = expQXY (-a) (-i) (-j) := by
    rw [neg_eq_iff_add_eq_zero, expQXY_add]
    rw [show a + -a = 0 by ring_nf, show i + -i = 0 by ring_nf,
      show j + -j = 0 by ring_nf]
    exact expQXY_zero
  apply HahnSeries.ext
  funext b
  rw [coeffXY_coeff, coeffQXY]
  rw [HahnSeries.coeff_single_mul, coeffXY_coeff, coeffQXY]
  show (HahnSeries.single (expQXY a i j) c * F).coeff (expQXY b n m)
      = c * F.coeff (expQXY (b - a) (n - i) (m - j))
  rw [HahnSeries.coeff_single_mul_S]
  rw [show expQXY b n m - expQXY a i j = expQXY (b - a) (n - i) (m - j) by
    rw [sub_eq_add_neg, sub_eq_add_neg, hneg, expQXY_add,
      show b + -a = b - a by ring_nf, show n + -i = n - i by ring_nf,
      show m + -j = m - j by ring_nf]]

/-- Coefficients after the packaged `S`-shift. -/
theorem coeffXY_shiftS (v : ℤ × ℤ × ℤ) (F : S) (n m : ℤ) :
    coeffXY (shiftS v F) n m =
      Qpow v.1 * coeffXY F (n - v.2.1) (m - v.2.2) := by
  unfold shiftS Qpow
  simpa using coeffXY_monom_mul_all v.1 v.2.1 v.2.2 (1 : ℚ) F n m

@[simp] theorem scaleQY_zero (c : K) : scaleQY c 0 = 0 := by
  ext j
  simp [scaleQY]

@[simp] theorem shiftQY_zero_slice (q y : ℤ) : shiftQY q y 0 = 0 := by
  ext j
  simp [shiftQY]

@[simp] theorem scaleQY_one (A : QYSlice) : scaleQY 1 A = A := by
  ext j
  simp [scaleQY]

@[simp] theorem shiftQY_zero (A : QYSlice) : shiftQY 0 0 A = A := by
  ext j
  simp [shiftQY, Qpow]

/-- Compose two Q/y shifts. -/
theorem shiftQY_add (q₁ y₁ q₂ y₂ : ℤ) (A : QYSlice) :
    shiftQY q₁ y₁ (shiftQY q₂ y₂ A) = shiftQY (q₁ + q₂) (y₁ + y₂) A := by
  ext j
  unfold shiftQY
  rw [← mul_assoc, Qpow_mul]
  congr 1
  ring_nf

/-- A shift followed by the opposite shift is the identity. -/
theorem shiftQY_neg_shift (q y : ℤ) (A : QYSlice) :
    shiftQY q y (shiftQY (-q) (-y) A) = A := by
  rw [shiftQY_add]
  simp

/-- The opposite shift followed by a shift is the identity. -/
theorem shiftQY_shift_neg (q y : ℤ) (A : QYSlice) :
    shiftQY (-q) (-y) (shiftQY q y A) = A := by
  rw [shiftQY_add]
  simp

/-- Compose scalar multiplication and Q/y shifts. -/
theorem scale_shift_scale_shift (c d : K) (q₁ y₁ q₂ y₂ : ℤ) (A : QYSlice) :
    scaleQY c (shiftQY q₁ y₁ (scaleQY d (shiftQY q₂ y₂ A))) =
      scaleQY (c * d) (shiftQY (q₁ + q₂) (y₁ + y₂) A) := by
  funext j
  unfold scaleQY shiftQY
  change c * (Qpow q₁ * (d * (Qpow q₂ * A ((j - y₁) - y₂)))) =
    c * d * (Qpow (q₁ + q₂) * A (j - (y₁ + y₂)))
  have hy : j - y₁ - y₂ = j - (y₁ + y₂) := by ring_nf
  rw [hy]
  rw [← Qpow_mul q₁ q₂]
  ring_nf

/-- Downward form of the step-1 Q/y-slice recurrence. -/
theorem qySlice_step_down (A : ℤ → QYSlice) (α β ystep n : ℤ)
    (hrec : ∀ r, A (r + 1) =
      scaleQY (-1 : K) (shiftQY (affineQ α β r) ystep (A r))) :
    A n = scaleQY (-1 : K) (shiftQY (-(affineQ α β n)) (-ystep) (A (n + 1))) := by
  rw [hrec n]
  funext j
  unfold scaleQY shiftQY
  change A n j = (-1 : K) *
    (Qpow (-(affineQ α β n)) *
      ((-1 : K) * (Qpow (affineQ α β n) * A n ((j - -ystep) - ystep))))
  have hj : j - -ystep - ystep = j := by ring_nf
  rw [hj]
  rw [show (-1 : K) * (Qpow (-(affineQ α β n)) *
        ((-1 : K) * (Qpow (affineQ α β n) * A n j))) =
        (Qpow (-(affineQ α β n)) * Qpow (affineQ α β n)) * A n j by ring_nf]
  rw [Qpow_mul, neg_add_cancel, Qpow_zero, one_mul]

theorem step1QSum_add_one (α β n t : ℤ) :
    step1QSum α β n (t + 1) =
      affineQ α β (n + t) + step1QSum α β n t := by
  unfold step1QSum affineQ
  rw [Tn_add_one]
  ring_nf

theorem step1QSum_sub_one (α β n t : ℤ) :
    step1QSum α β n (t - 1) =
      -(affineQ α β (n + t - 1)) + step1QSum α β n t := by
  have hT' := Tn_add_one (t - 1)
  have hT : Tn (t - 1) = Tn t - (t - 1) := by
    have ht : t - 1 + 1 = t := by ring_nf
    rw [ht] at hT'
    omega
  unfold step1QSum affineQ
  rw [hT]
  ring_nf

/-- Closed form for a generic affine step-1 Q/y-slice recurrence. -/
theorem qySlice_closed_form (A : ℤ → QYSlice) (α β ystep : ℤ)
    (hrec : ∀ n, A (n + 1) =
      scaleQY (-1 : K) (shiftQY (affineQ α β n) ystep (A n))) :
    ∀ n t : ℤ,
      A (n + t) =
        scaleQY ((-1 : K) ^ t) (shiftQY (step1QSum α β n t) (ystep * t) (A n)) := by
  intro n t
  refine Int.induction_on t ?_ ?_ ?_
  · funext j
    simp [scaleQY, shiftQY, step1QSum, Tn, Qpow]
  · intro k ih
    have hstep := hrec (n + (k : ℤ))
    rw [show n + ((k : ℤ) + 1) = (n + k) + 1 by ring_nf, hstep, ih]
    rw [scale_shift_scale_shift]
    rw [step1QSum_add_one]
    have hsign : ((-1 : K) ^ ((k : ℤ) + 1)) = (-1 : K) * ((-1 : K) ^ (k : ℤ)) := by
      rw [zpow_add₀ (by norm_num : (-1 : K) ≠ 0)]
      norm_num
    rw [hsign]
    rw [show ystep + ystep * (k : ℤ) = ystep * ((k : ℤ) + 1) by ring_nf]
  · intro k ih
    have hdown := qySlice_step_down A α β ystep (n + (-(k : ℤ) - 1)) hrec
    have hkey : A (n + (-(k : ℤ) - 1) + 1) = A (n + (-(k : ℤ))) := by
      congr 1
      ring_nf
    rw [hkey, ih] at hdown
    rw [hdown]
    rw [scale_shift_scale_shift]
    rw [step1QSum_sub_one]
    have hsign : ((-1 : K) ^ (-(k : ℤ) - 1)) = (-1 : K) * ((-1 : K) ^ (-(k : ℤ))) := by
      rw [show (-(k : ℤ) - 1) = (-(k : ℤ)) + (-1) by ring_nf,
        zpow_add₀ (by norm_num : (-1 : K) ≠ 0)]
      norm_num
    rw [hsign]
    rw [show -ystep + ystep * (-(k : ℤ)) = ystep * (-(k : ℤ) - 1) by ring_nf]
    rw [show n + (-(k : ℤ) - 1) = n + -(k : ℤ) - 1 by ring_nf]

/-- Closed form for the `x`-slice recurrence of a two-variable Hahn series. -/
theorem sliceX_closed_form_of_monom_step1 (F : S) (α β ystep : ℤ)
    (hrec : ∀ n, sliceX F (n + 1) =
      scaleQY (-1 : K) (shiftQY (affineQ α β n) ystep (sliceX F n))) :
    ∀ n t : ℤ,
      sliceX F (n + t) =
        scaleQY ((-1 : K) ^ t)
          (shiftQY (step1QSum α β n t) (ystep * t) (sliceX F n)) :=
  qySlice_closed_form (fun n => sliceX F n) α β ystep hrec

/-- Subtraction commutes with x-slice extraction. -/
theorem sliceX_sub (F G : S) (n : ℤ) :
    sliceX (F - G) n = fun j => coeffXY F n j - coeffXY G n j := by
  funext j
  apply HahnSeries.ext
  funext a
  simp [sliceX, coeffXY_coeff, coeffQXY]

/-- If every x-slice vanishes, then the whole two-variable Hahn series vanishes. -/
theorem eq_zero_of_sliceX_eq_zero (F : S) (h : ∀ n, sliceX F n = 0) : F = 0 := by
  apply ext_coeffQXY
  intro a i j
  have hs := congrArg (fun A : QYSlice => (A j).coeff a) (h i)
  simpa [sliceX, coeffXY_coeff, coeffQXY] using hs

/-- A single vanishing x-slice propagates to every x-slice along a step-1 recurrence. -/
theorem sliceX_eq_zero_of_monom_step1_and_initial (F : S) (α β ystep n₀ : ℤ)
    (hrec : ∀ n, sliceX F (n + 1) =
      scaleQY (-1 : K) (shiftQY (affineQ α β n) ystep (sliceX F n)))
    (hinit : sliceX F n₀ = 0) :
    ∀ n, sliceX F n = 0 := by
  have hclosed := sliceX_closed_form_of_monom_step1 F α β ystep hrec
  intro n
  have hcf := hclosed n₀ (n - n₀)
  have hn : n₀ + (n - n₀) = n := by ring_nf
  rw [hn] at hcf
  simpa [hinit] using hcf

/-- Vanishing propagates along a step-1 monomial-transport recurrence to the whole series. -/
theorem eq_zero_of_monom_step1_and_initial (F : S) (α β ystep n₀ : ℤ)
    (hrec : ∀ n, sliceX F (n + 1) =
      scaleQY (-1 : K) (shiftQY (affineQ α β n) ystep (sliceX F n)))
    (hinit : sliceX F n₀ = 0) :
    F = 0 :=
  eq_zero_of_sliceX_eq_zero F
    (sliceX_eq_zero_of_monom_step1_and_initial F α β ystep n₀ hrec hinit)

/-- Equality engine for the generic affine step-1 monomial-transport recurrence. -/
theorem eq_of_monom_step1_and_initial (F G : S) (α β ystep n₀ : ℤ)
    (hF : ∀ n, sliceX F (n + 1) =
      scaleQY (-1 : K) (shiftQY (affineQ α β n) ystep (sliceX F n)))
    (hG : ∀ n, sliceX G (n + 1) =
      scaleQY (-1 : K) (shiftQY (affineQ α β n) ystep (sliceX G n)))
    (hinit : sliceX F n₀ = sliceX G n₀) :
    F = G := by
  have hdrec : ∀ n, sliceX (F - G) (n + 1) =
      scaleQY (-1 : K) (shiftQY (affineQ α β n) ystep (sliceX (F - G) n)) := by
    intro n
    rw [sliceX_sub (F := F) (G := G) (n := n + 1),
      sliceX_sub (F := F) (G := G) (n := n)]
    funext j
    have hFj : coeffXY F (n + 1) j =
        (scaleQY (-1 : K) (shiftQY (affineQ α β n) ystep (sliceX F n))) j := by
      simpa [sliceX] using congrFun (hF n) j
    have hGj : coeffXY G (n + 1) j =
        (scaleQY (-1 : K) (shiftQY (affineQ α β n) ystep (sliceX G n))) j := by
      simpa [sliceX] using congrFun (hG n) j
    rw [hFj, hGj]
    unfold scaleQY shiftQY
    simp [sliceX]
    ring_nf
  have hdinit : sliceX (F - G) n₀ = 0 := by
    rw [sliceX_sub (F := F) (G := G) (n := n₀)]
    funext j
    have hj : coeffXY F n₀ j = coeffXY G n₀ j := by
      simpa [sliceX] using congrFun hinit j
    simp [hj]
  have hzero := eq_zero_of_monom_step1_and_initial (F - G) α β ystep n₀ hdrec hdinit
  exact sub_eq_zero.mp hzero

end

end QseriesFormalization.Pending.Ch10M3Engine
