# NRS³ · Dark: `1 − Ω_b`, the interior of the volumetric quantum

**What light does not resolve is dark.** For any pair of non-commuting Hermitian observables on a
complex Hilbert space with spatial axes `x, y, z` of dimension at least `4`, the photon spectrum
carries a quantum of irresolvability: the volumetric quantum `𝒱 = δ(dx) δ(dy) δ(dz)` is positive
and no refinement removes it. Light resolves everything but that quantum. What light resolves is
what we see and measure, the baryon density `Ω_b`; what it does not resolve, `1 − Ω_b`, is the
interior of the volumetric quantum throughout the universe. It is dark because light does not
resolve it there, not because it is empty. Lean 4, Mathlib and the base repository.

**[▶ Try it: move the axes of the cube; the three fronts against omegaPi](https://naype888-cloud.github.io/nrs3-dark/)**

## Two saturations

All white and all black are the same blindness. At `d = 2, 3` the uncertainty vector is
lightlike and the contrast `tan θ_NRS(d) = τ / ‖⟪x, y⟫‖` is zero: only light, the image washes out.
At the Szegő limit the contrast would be `√(C∞² − 1)`, the other saturation, which no dimension
reaches. Every real image lives strictly between the two (`properTimeQuantum_mem_Ioo` in Physlib,
`contrast_maxCurrentState` in [`nrs3-uncertainty-cone`](https://github.com/naype888-cloud/nrs3-uncertainty-cone)),
and the contrast depends on the dimension alone (`properTimeQuantum_eq_of_N_eq`): the same in a
microscope, a classroom and a telescope. The regulation of what light resolves against what it
does not is `Ω_b` against `1 − Ω_b`.

## The number

`omegaPi = (1 − 1/C∞) e^{−1/C∞} = 0.0495436788…`, a function of `π` alone through the Szegő limit
`C∞ = √(π²/3 − 2) = 1 + δ∞` (`D8`, `D26a`). The factor `1 − 1/C∞ = δ∞ / (1 + δ∞)` is the share of
the quantum in `C∞`:

`omegaPi = (δ∞ / (1 + δ∞)) · e^{−1/(1 + δ∞)}`  (`omegaPi_eq_deltaInf`)

## Three fronts

`Ω_b = ω_b / h²`. Each front gives a box for `(ω_b, h)`; Lean bounds `Ω_b` by its corners
(`div_sq_mem`) and places `omegaPi` inside.

| Front | Data | `Ω_b` box | `omegaPi` | Lean |
|---|---|---|---|---|
| CMB · Planck 2018 | `ω_b = 0.02237 ± 0.00015`, `H₀ = 67.36 ± 0.54` (1σ) | `[0.0482, 0.0504]` | inside, `≈ 0.3σ` | `omegaB_planck`, `omegaPi_mem_planck` |
| BBN · LUNA 2020 | `ω_b = 0.02233 ± 0.00036`, Planck `h` (1σ) | `[0.0477, 0.0508]` | inside | `omegaB_luna`, `omegaPi_mem_luna` |
| BAO · DESI 2024 | `ω_b = 0.02218 ± 0.00055` (BBN), `H₀ = 68.52 ± 0.62` (2σ) | `[0.0433, 0.0514]` | inside at 2σ, `≈ 1.6σ` | `omegaB_desi`, `omegaPi_mem_desi` |

## Error of each instrument

`omegaPi` is fixed by `π`. Central value
`Ω_b = ω_b / h²`, error propagated from `ω_b` and `h`:

| Front | `Ω_b` (centre) | `1σ` | `omegaPi − Ω_b` | Distance |
|---|---|---|---|---|
| CMB · Planck 2018 | `0.04930` | `± 0.00086` (1.7 %) | `+0.49 %` | `0.28σ` |
| BBN · LUNA 2020, Planck `h` | `0.04921` | `± 0.00112` (2.3 %) | `+0.67 %` | `0.30σ` |
| BAO · DESI 2024 + BBN | `0.04724` | `± 0.00145` (3.1 %) | `+4.87 %` | `1.59σ` |

The fraction is fixed by the theorem: the photon spectrum in vacuum is subject to it, so
everything a telescope sees is what light resolves, `Ω_b`, and everything it does not see is the
irresolvable interior, `1 − Ω_b`. Every observation records the same value; the spread between
fronts is the error of each instrument. Planck and LUNA sit within a third of their own error.
DESI's distance comes from its higher `H₀` (68.52 against 67.36): its `ω_b` is the BBN value,
close to the others.

## Results

| Statement | Lean |
|---|---|
| `g_s = 1 − 1/C∞ = δ∞ / (1 + δ∞)` | `gPi_eq_deltaInf` |
| `omegaPi = (δ∞ / (1 + δ∞)) e^{−1/(1 + δ∞)}` | `omegaPi_eq_deltaInf` |
| `0.0495436788 < omegaPi < 0.049543679` | `omegaPi_gt`, `omegaPi_lt` |
| with Planck's `Ω_b`, `0.949 < 1 − Ω_b < 0.952` | `darkFraction_planck` |
| `0.950456321 < 1 − omegaPi < 0.9504563212` | `darkFraction_omegaPi` |
| from `4 × 4 × 4`: `0 < 𝒱 < δ∞³`, `omegaPi` in the Planck box, `1 − omegaPi > 0` | `nrs3_dark` |

The volumetric quantum is `D37e` of the base repository; in Physlib it is `volQuantum`
(`PhyslibAlpha/CondensedMatter/TightBindingChain/VolumetricQuantum.lean`), and its proper time
and foam time are in `CausalCone.lean` and `SpacetimeFoam.lean`.

## Build

Lean 4 `v4.34.0`, Mathlib, and the base repository
[`nava-robertson-schrodinger`](https://github.com/naype888-cloud/nava-robertson-schrodinger)
(pinned in `lakefile.toml`).

```bash
lake exe cache get
lake build
lake env lean Verification/Axioms.lean   # only propext, Classical.choice, Quot.sound
```

## References

* Planck Collaboration, *Planck 2018 results. VI. Cosmological parameters*, A&A 641 (2020) A6,
  [arXiv:1807.06209](https://arxiv.org/abs/1807.06209).
* V. Mossa et al. (LUNA), *The baryon density of the Universe from an improved rate of deuterium
  burning*, Nature 587 (2020) 210, [doi:10.1038/s41586-020-2878-4](https://doi.org/10.1038/s41586-020-2878-4).
* DESI Collaboration, *DESI 2024 VI: cosmological constraints from the measurements of baryon
  acoustic oscillations*, [arXiv:2404.03002](https://arxiv.org/abs/2404.03002).

## Timeline 1911–1945

NRS answers a question of the Solvay era with later tools. The series is placed in that window:
what falls inside it is the history the theorem belongs to; what falls after it is a proposal,
not part of NRS³.

| Year | Event | Repository |
|---|---|---|
| 1900–06 | Planck and Boltzmann: `S = k_B log W` | [`nrs3-de-sitter`](https://github.com/naype888-cloud/nrs3-de-sitter) |
| 1911 | First Solvay conference: radiation and the quanta | |
| 1911–12 | Poincaré: Planck's law forces discrete levels | [`nrs3-poincare`](https://github.com/naype888-cloud/nrs3-poincare) |
| 1915–20 | Szegő: limit theorems for Toeplitz matrices (the limit `C∞`, `D8`) | [base repository (NRS, NRS³)](https://github.com/naype888-cloud/nava-robertson-schrodinger) |
| 1917 | Einstein: the cosmological constant; de Sitter: the empty universe with `Λ` | [`nrs3-de-sitter`](https://github.com/naype888-cloud/nrs3-de-sitter) |
| 1922–27 | Friedmann and Lemaître: the expanding universe | [`nrs3-de-sitter`](https://github.com/naype888-cloud/nrs3-de-sitter) |
| 1925–27 | Pauli: exclusion, shells `2n²`, spin matrices | [`nrs3-pauli-dirac`](https://github.com/naype888-cloud/nrs3-pauli-dirac) |
| 1927–32 | von Neumann: the entropy of a quantum state; Klein's inequality (1931) | [`nrs3-landauer-carnot`](https://github.com/naype888-cloud/nrs3-landauer-carnot) |
| 1928 | Dirac: the `4 × 4` gamma matrices | [`nrs3-pauli-dirac`](https://github.com/naype888-cloud/nrs3-pauli-dirac) |
| 1929 | van der Waerden: spinors, `SL(2, ℂ)` on Hermitian matrices; the uncertainty cone | [`nrs3-uncertainty-cone`](https://github.com/naype888-cloud/nrs3-uncertainty-cone) |
| **1929–30** | **Robertson and Schrödinger: the uncertainty inequality** | **[base repository (NRS, NRS³)](https://github.com/naype888-cloud/nava-robertson-schrodinger)** |
| 1945–46 | Mandelstam–Tamm: the time–energy bound; Rao (1945), Cramér (1946) | [`nrs3-mandelstam-tamm-cramer-rao`](https://github.com/naype888-cloud/nrs3-mandelstam-tamm-cramer-rao) |

**After the window.** The measured `Ω_b` comes from the CMB (Planck 2018), primordial deuterium
(LUNA 2020) and baryon acoustic oscillations (DESI 2024). They are data, as `c` is: this repository
takes them as measured and compares them with `omegaPi`, a function of `π` alone.

## The mosaic

- [NRS and NRS³ — the base theorem](https://github.com/naype888-cloud/nava-robertson-schrodinger)
- [NRS³ · Mandelstam–Tamm and Cramér–Rao](https://github.com/naype888-cloud/nrs3-mandelstam-tamm-cramer-rao)
- [NRS³ · Landauer and Carnot](https://github.com/naype888-cloud/nrs3-landauer-carnot)
- [NRS³ · de Sitter](https://github.com/naype888-cloud/nrs3-de-sitter)
- [NRS³ · Penrose](https://github.com/naype888-cloud/nrs3-penrose) (proposal)
- [NRS³ · Pauli–Dirac](https://github.com/naype888-cloud/nrs3-pauli-dirac)
- [NRS³ · The uncertainty cone](https://github.com/naype888-cloud/nrs3-uncertainty-cone)
- [NRS³ · Poincaré](https://github.com/naype888-cloud/nrs3-poincare)
- [NRS³ · Defect and curvature](https://github.com/naype888-cloud/nrs3-defect-curvature)
- [NRS³ · Rovelli — Loop Quantum Gravity](https://github.com/naype888-cloud/nrs3-rovelli-lqg) (proposal)
- **[NRS³ · Dark](https://github.com/naype888-cloud/nrs3-dark)** (this one)

## License

NRS Noncommercial License 1.0.0, see [`LICENSE`](LICENSE). Author: Eduardo Nava-Hernandez.
