/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D26a_OmegaFromPi
public import NavaRobertsonIndependent.Mathematics.D37e_VolumetricQuantum

/-!
# NRS³ · The dark part: `1 − Ω_b`, the interior of the volumetric quantum

For any pair of non-commuting Hermitian observables on a complex Hilbert space with spatial axes
`x, y, z` of dimension at least `4`, the photon spectrum carries a quantum of irresolvability:
the volumetric quantum `𝒱 = δ(dx) δ(dy) δ(dz)` is positive and no refinement removes it
(`D37e`). Light resolves everything but that quantum.

What light resolves is what we see and measure, and what we see and measure is the baryon
density `Ω_b`. What light does not resolve, `1 − Ω_b`, is the interior of the volumetric quantum
throughout the universe: it is dark because light does not resolve it there, not because it is
empty.

`Ω_b` enters as a measured datum, as `c` enters as the slope of the light cone. Three independent
fronts measure it: the acoustic peaks of the CMB, primordial deuterium (BBN) and baryon acoustic
oscillations (BAO). The number `omegaPi = (1 − 1/C∞) e^{−1/C∞}` of `D26a` is a function of `π`
alone, from the same Szegő limit `C∞ = 1 + δ∞` that bounds the quantum, and it lies inside the
measured intervals.

## Main results

- `NRS3Dark.omegaPi_eq_deltaInf` : `omegaPi = (δ∞ / (1 + δ∞)) e^{−1/(1 + δ∞)}`.
- `NRS3Dark.omegaPi_gt`, `NRS3Dark.omegaPi_lt` : `0.0495436788 < omegaPi < 0.049543679`.
- `NRS3Dark.omegaB_planck`, `NRS3Dark.omegaPi_mem_planck` : Planck 2018 at `1σ`.
- `NRS3Dark.omegaB_luna`, `NRS3Dark.omegaPi_mem_luna` : BBN (LUNA 2020) with the Planck `h`, `1σ`.
- `NRS3Dark.omegaB_desi`, `NRS3Dark.omegaPi_mem_desi` : DESI 2024 BAO with BBN, `2σ`.
- `NRS3Dark.darkFraction_planck` : with `Ω_b` measured by Planck, `0.949 < 1 − Ω_b < 0.952`.
- `NRS3Dark.nrs3_dark` : the dark part and the volumetric quantum together.

## References

* Planck Collaboration, *Planck 2018 results. VI. Cosmological parameters*, A&A 641 (2020) A6:
  `Ω_b h² = 0.02237 ± 0.00015`, `H₀ = 67.36 ± 0.54 km s⁻¹ Mpc⁻¹`.
* V. Mossa et al. (LUNA), *The baryon density of the Universe from an improved rate of deuterium
  burning*, Nature 587 (2020) 210: `Ω_b h² = 0.02233 ± 0.00036`.
* DESI Collaboration, *DESI 2024 VI: cosmological constraints from the measurements of baryon
  acoustic oscillations*, arXiv:2404.03002: with a BBN prior `Ω_b h² = 0.02218 ± 0.00055` and the
  CMB acoustic angle, `H₀ = 68.52 ± 0.62 km s⁻¹ Mpc⁻¹`.
-/

@[expose] public noncomputable section

open Gnomon DimensionalQuantum VolumetricQuantum OmegaFromPi

namespace NRS3Dark

/-! ## 1. `omegaPi` from the quantum -/

/-- `g_s = 1 − 1/C∞` is the share of the quantum in `C∞ = 1 + δ∞`. -/
theorem gPi_eq_deltaInf : gPi = deltaInf / (1 + deltaInf) := by
  have h := CoherenceConstantInf_pos
  rw [gPi, deltaInf, add_sub_cancel]
  field_simp

/-- **`omegaPi` in terms of the quantum**: `(δ∞ / (1 + δ∞)) e^{−1/(1 + δ∞)}`. -/
theorem omegaPi_eq_deltaInf :
    omegaPi = deltaInf / (1 + deltaInf) * Real.exp (-1 / (1 + deltaInf)) := by
  rw [omegaPi, gPi_eq_deltaInf, boltzmannPi, deltaInf, add_sub_cancel]

theorem omegaPi_gt : (0.0495436788 : ℝ) < omegaPi := by
  have h := decimal_of_pi.2
  norm_num at h ⊢
  linarith

theorem omegaPi_lt : omegaPi < (0.049543679 : ℝ) := by
  have h := decimal_of_pi.1
  norm_num at h ⊢
  linarith

/-! ## 2. The measured baryon density -/

/-- `Ω_b = ω_b / h²` lies between the corners of the measured box. -/
theorem div_sq_mem {ωLo ωHi hLo hHi ω h : ℝ} (hLo0 : 0 < hLo) (hω : ωLo ≤ ω ∧ ω ≤ ωHi)
    (hh : hLo ≤ h ∧ h ≤ hHi) (hωLo : 0 ≤ ωLo) :
    ωLo / hHi ^ 2 ≤ ω / h ^ 2 ∧ ω / h ^ 2 ≤ ωHi / hLo ^ 2 := by
  have hh0 : 0 < h := hLo0.trans_le hh.1
  constructor
  · exact div_le_div₀ (hωLo.trans hω.1) hω.1 (by positivity) (by gcongr; exact hh.2)
  · exact div_le_div₀ ((hωLo.trans hω.1).trans hω.2) hω.2 (by positivity) (by gcongr; exact hh.1)

/-- **Planck 2018, `1σ`.** `0.02222 ≤ ω_b ≤ 0.02252`, `0.6682 ≤ h ≤ 0.6790`. -/
theorem omegaB_planck {ω h : ℝ} (hω : 0.02222 ≤ ω ∧ ω ≤ 0.02252) (hh : 0.6682 ≤ h ∧ h ≤ 0.6790) :
    0.02222 / 0.6790 ^ 2 ≤ ω / h ^ 2 ∧ ω / h ^ 2 ≤ 0.02252 / 0.6682 ^ 2 :=
  div_sq_mem (by norm_num) hω hh (by norm_num)

theorem omegaPi_mem_planck :
    (0.02222 : ℝ) / 0.6790 ^ 2 < omegaPi ∧ omegaPi < 0.02252 / 0.6682 ^ 2 := by
  constructor
  · exact lt_of_le_of_lt (by norm_num) omegaPi_gt
  · exact omegaPi_lt.trans_le (by norm_num)

/-- **BBN (LUNA 2020) with the Planck `h`, `1σ`.** `0.02197 ≤ ω_b ≤ 0.02269`. -/
theorem omegaB_luna {ω h : ℝ} (hω : 0.02197 ≤ ω ∧ ω ≤ 0.02269) (hh : 0.6682 ≤ h ∧ h ≤ 0.6790) :
    0.02197 / 0.6790 ^ 2 ≤ ω / h ^ 2 ∧ ω / h ^ 2 ≤ 0.02269 / 0.6682 ^ 2 :=
  div_sq_mem (by norm_num) hω hh (by norm_num)

theorem omegaPi_mem_luna :
    (0.02197 : ℝ) / 0.6790 ^ 2 < omegaPi ∧ omegaPi < 0.02269 / 0.6682 ^ 2 := by
  constructor
  · exact lt_of_le_of_lt (by norm_num) omegaPi_gt
  · exact omegaPi_lt.trans_le (by norm_num)

/-- **DESI 2024 BAO with BBN, `2σ`.** `0.02108 ≤ ω_b ≤ 0.02328`, `0.6728 ≤ h ≤ 0.6976`. At `1σ`
the upper corner `0.02273 / 0.6790²` is below `omegaPi`: this front sits at about `1.6σ`. -/
theorem omegaB_desi {ω h : ℝ} (hω : 0.02108 ≤ ω ∧ ω ≤ 0.02328) (hh : 0.6728 ≤ h ∧ h ≤ 0.6976) :
    0.02108 / 0.6976 ^ 2 ≤ ω / h ^ 2 ∧ ω / h ^ 2 ≤ 0.02328 / 0.6728 ^ 2 :=
  div_sq_mem (by norm_num) hω hh (by norm_num)

theorem omegaPi_mem_desi :
    (0.02108 : ℝ) / 0.6976 ^ 2 < omegaPi ∧ omegaPi < 0.02328 / 0.6728 ^ 2 := by
  constructor
  · exact lt_of_le_of_lt (by norm_num) omegaPi_gt
  · exact omegaPi_lt.trans_le (by norm_num)

/-! ## 3. The dark part -/

/-- What light does not resolve: `1 − Ω_b`. -/
def darkFraction (Ωb : ℝ) : ℝ := 1 - Ωb

/-- **With `Ω_b` measured by Planck, the dark part is between `0.949` and `0.952`.** -/
theorem darkFraction_planck {ω h : ℝ} (hω : 0.02222 ≤ ω ∧ ω ≤ 0.02252)
    (hh : 0.6682 ≤ h ∧ h ≤ 0.6790) :
    0.949 < darkFraction (ω / h ^ 2) ∧ darkFraction (ω / h ^ 2) < 0.952 := by
  have := omegaB_planck hω hh
  unfold darkFraction
  constructor
  · linarith [show (0.02252 : ℝ) / 0.6682 ^ 2 < 0.051 by norm_num]
  · linarith [show (0.048 : ℝ) < 0.02222 / 0.6790 ^ 2 by norm_num]

theorem darkFraction_omegaPi :
    0.950456321 < darkFraction omegaPi ∧ darkFraction omegaPi < 0.9504563212 := by
  unfold darkFraction
  constructor
  · linarith [omegaPi_lt]
  · linarith [omegaPi_gt]

/-- **NRS³ · dark.** On every cube with at least `4` positions per axis the volumetric quantum is
positive and below `δ∞³`; `omegaPi = (δ∞ / (1 + δ∞)) e^{−1/(1 + δ∞)}` lies inside the Planck
interval of the measured `Ω_b`; and the part light does not resolve, `1 − omegaPi`, is positive. -/
theorem nrs3_dark {dx dy dz : ℕ} (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz) :
    0 < volQuantum dx dy dz ∧ volQuantum dx dy dz < deltaInf ^ 3 ∧
      omegaPi = deltaInf / (1 + deltaInf) * Real.exp (-1 / (1 + deltaInf)) ∧
      ((0.02222 : ℝ) / 0.6790 ^ 2 < omegaPi ∧ omegaPi < 0.02252 / 0.6682 ^ 2) ∧
      0 < darkFraction omegaPi :=
  ⟨volQuantum_pos hx hy hz, volQuantum_lt_ceiling hx hy hz, omegaPi_eq_deltaInf,
    omegaPi_mem_planck, by linarith [darkFraction_omegaPi.1]⟩

end NRS3Dark
