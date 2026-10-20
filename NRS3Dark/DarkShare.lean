/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D1_CauchyGramInequality
public import NavaRobertsonIndependent.Mathematics.D37b_NRSAngle

/-!
# NRS³ · What is resolved and what is dark add up to one, for every field

Let `x`, `y` be the fluctuation vectors of two observables in a state: of any field, on any
complex Hilbert space. The product of the uncertainties `‖x‖² ‖y‖²` splits in two parts,

  `‖x‖² ‖y‖² = ‖⟪x, y⟫‖² + gramDefectC x y`.

The first is what the pair resolves: correlation and bracket, the whole Robertson–Schrödinger
bound. The second is the defect, the quantum the pair cannot resolve. Divided by the product,

  `lightShare x y + darkShare x y = 1`,

the squares of the cosine and the sine of the angle between `x` and `y`. Both shares lie in
`[0, 1]`. The dark share vanishes exactly when Cauchy–Schwarz saturates: the pair sits on the
edge of the cone, as light does. Nothing else is left: removing what is resolved leaves only
what cannot be resolved.

On the elemental pair `(T_d, P_d)` in the maximal current state, the state at the speed limit `c`
of the system, the light share is `1 / C(d)²` and the dark share `1 − 1 / C(d)²`. The dark share
is zero exactly for `d = 2, 3`, where light saturates, and positive from `d = 4` on. It depends on
`d` alone, not on the size of the system.

## Main results

- `DarkShare.lightShare_add_darkShare` : the two shares add up to one, for every pair.
- `DarkShare.darkShare_nonneg`, `DarkShare.lightShare_nonneg` : both are nonnegative.
- `DarkShare.darkShare_eq_zero_iff` : the dark share vanishes exactly on the edge of the cone.
- `DarkShare.lightShare_maxCurrentState` : at `c`, the light share is `1 / C(d)²`.
- `DarkShare.darkShare_maxCurrentState` : at `c`, the dark share is `1 − 1 / C(d)²`.
- `DarkShare.darkShare_maxCurrentState_eq_zero_iff` : it is zero exactly for `d = 2, 3`.
- `DarkShare.darkShare_maxCurrentState_pos` : it is positive for `d ≥ 4`.
-/

@[expose] public noncomputable section

open CauchyGram TransportPosition NRSInequality SpectralExtremal EigenvectorSaturation NRSAngle Gnomon
open PathGraph3DNRS

namespace DarkShare

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The share the pair resolves: `‖⟪x, y⟫‖² / (‖x‖² ‖y‖²)`. -/
def lightShare (x y : H) : ℝ := ‖inner ℂ x y‖ ^ 2 / (‖x‖ * ‖y‖) ^ 2

/-- The share the pair cannot resolve: the defect over the product of the uncertainties. -/
def darkShare (x y : H) : ℝ := gramDefectC x y / (‖x‖ * ‖y‖) ^ 2

/-- **What is resolved and what is dark add up to one**, for every pair of every field. -/
theorem lightShare_add_darkShare (x y : H) (h : ‖x‖ * ‖y‖ ≠ 0) :
    lightShare x y + darkShare x y = 1 := by
  rw [lightShare, darkShare, ← add_div, gramDefectC, varianceC, varianceC,
    div_eq_one_iff_eq (pow_ne_zero 2 h)]
  ring

theorem darkShare_nonneg (x y : H) : 0 ≤ darkShare x y :=
  div_nonneg (gramDefectC_nonneg x y) (sq_nonneg _)

theorem lightShare_nonneg (x y : H) : 0 ≤ lightShare x y :=
  div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **The dark share vanishes exactly on the edge of the cone**, where Cauchy–Schwarz saturates. -/
theorem darkShare_eq_zero_iff (x y : H) (h : ‖x‖ * ‖y‖ ≠ 0) :
    darkShare x y = 0 ↔ ‖inner ℂ x y‖ = ‖x‖ * ‖y‖ := by
  rw [darkShare, div_eq_zero_iff, or_iff_left (pow_ne_zero 2 h), gramDefectC_eq_zero_iff]

variable {d : ℕ}

/-- The fluctuations of `T_d` and `P_d` at the maximal current state are not zero. -/
theorem norm_mul_norm_ne_zero (hd : 2 ≤ d) :
    ‖centered (TdOp d) (maxCurrentState d)‖ * ‖centered (PdOp d) (maxCurrentState d)‖ ≠ 0 := by
  intro h0
  have h := cos_angleNRS hd
  rw [h0, div_zero] at h
  have : 0 < 1 / CoherenceConstant d := by
    have := CoherenceConstant_ge_one hd
    positivity
  linarith

/-- **At the speed limit `c`, the pair resolves `1 / C(d)²`.** -/
theorem lightShare_maxCurrentState (hd : 2 ≤ d) :
    lightShare (centered (TdOp d) (maxCurrentState d)) (centered (PdOp d) (maxCurrentState d)) =
      1 / CoherenceConstant d ^ 2 := by
  rw [lightShare, ← div_pow, cos_angleNRS hd, div_pow, one_pow]

/-- **At the speed limit `c`, the dark share is `1 − 1 / C(d)²`.** -/
theorem darkShare_maxCurrentState (hd : 2 ≤ d) :
    darkShare (centered (TdOp d) (maxCurrentState d)) (centered (PdOp d) (maxCurrentState d)) =
      1 - 1 / CoherenceConstant d ^ 2 := by
  rw [← lightShare_maxCurrentState hd, eq_sub_iff_add_eq', lightShare_add_darkShare _ _
    (norm_mul_norm_ne_zero hd)]

/-- **Light saturates exactly for `d = 2, 3`**: there the dark share is zero. -/
theorem darkShare_maxCurrentState_eq_zero_iff (hd : 2 ≤ d) :
    darkShare (centered (TdOp d) (maxCurrentState d)) (centered (PdOp d) (maxCurrentState d)) =
      0 ↔ d = 2 ∨ d = 3 := by
  have hC := CoherenceConstant_ge_one hd
  rw [darkShare_maxCurrentState hd, sub_eq_zero, eq_comm, div_eq_one_iff_eq (by positivity),
    ← CoherenceConstant_eq_one_iff d hd]
  constructor
  · intro h
    nlinarith [h]
  · intro h
    rw [h, one_pow]

/-- **From four positions on, every field keeps a dark share.** -/
theorem darkShare_maxCurrentState_pos (hd : 4 ≤ d) :
    0 < darkShare (centered (TdOp d) (maxCurrentState d))
      (centered (PdOp d) (maxCurrentState d)) := by
  have hC := one_lt_CoherenceConstant_of_four_le d hd
  rw [darkShare_maxCurrentState (by omega), sub_pos, div_lt_one (by positivity)]
  nlinarith

end DarkShare
