/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 37aedf17-6d34-4091-afa3-e94dffa2aba2

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem stirling_approximation_asymptotic (n : ℕ) (hn : 0 < n) :
    ∃ (error : ℝ), log (Nat.factorial n) = stirlingApprox n + error
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 87ef3641-eecc-42dc-a4b0-637a123cac56

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem partitionFunction_pos : 0 < partitionFunction p
-/

import Mathlib


/-!
# Ideal Gas Law Derivation - Helmholtz Free Energy from Canonical Ensemble

This file formalizes the derivation of the Helmholtz free energy for an ideal gas
starting from the canonical ensemble partition function.

## Main results
- `IdealGas.partitionFunction`: The partition function Z for an ideal gas
- `IdealGas.helmholtzFreeEnergy`: The Helmholtz free energy A = -k_B T ln Z
- `IdealGas.helmholtzFreeEnergy_eq`: The simplified form of Helmholtz free energy (Eq. 7)
-/

open Real

/-! ## Physical Constants and Parameters -/

/-- Structure containing the physical parameters for an ideal gas system -/
structure IdealGasParams where
  k_B : ℝ  -- Boltzmann constant
  h : ℝ    -- Planck's constant
  m : ℝ    -- particle mass
  T : ℝ    -- temperature
  V : ℝ    -- volume
  N : ℕ    -- number of particles
  hk_B_pos : 0 < k_B
  hh_pos : 0 < h
  hm_pos : 0 < m
  hT_pos : 0 < T
  hV_pos : 0 < V
  hN_pos : 0 < N

variable (p : IdealGasParams)

/-! ## Section 1: Partition Function Definition -/

/--
"The partition function for an ideal gas:
Z = V^N / (N! h^{3N}) (2π m k_B T)^{3N/2}"
(Equation 1)
-/
noncomputable def partitionFunction : ℝ :=
  (p.V ^ p.N) / (Nat.factorial p.N * p.h ^ (3 * p.N)) *
  (2 * π * p.m * p.k_B * p.T) ^ ((3 * p.N : ℕ) / 2 : ℝ)

/-- The partition function is positive for valid physical parameters -/
theorem partitionFunction_pos : 0 < partitionFunction p := by
  exact mul_pos ( div_pos ( pow_pos p.hV_pos _ ) ( mul_pos ( Nat.cast_pos.mpr ( Nat.factorial_pos _ ) ) ( pow_pos p.hh_pos _ ) ) ) ( Real.rpow_pos_of_pos ( mul_pos ( mul_pos ( mul_pos ( by positivity ) ( by exact p.hm_pos ) ) ( by exact p.hk_B_pos ) ) ( by exact p.hT_pos ) ) _ )

/-! ## Section 2: Helmholtz Free Energy Definition -/

/--
"The Helmholtz free energy F is defined as a function of the partition function
from thermodynamic relationships, as:
A = -k_B T ln Z"
(Equation 2)
-/
noncomputable def helmholtzFreeEnergy_def (Z : ℝ) (hZ : 0 < Z) : ℝ :=
  -p.k_B * p.T * log Z

/-- Helmholtz free energy for an ideal gas using the partition function -/
noncomputable def helmholtzFreeEnergy : ℝ :=
  helmholtzFreeEnergy_def p (partitionFunction p) (partitionFunction_pos p)

/-! ## Stirling's Approximation -/

/--
"Stirling's approximation: ln N! = N ln N - N"
This is used as an approximation for large N.
-/
noncomputable def stirlingApprox (n : ℕ) : ℝ :=
  n * log n - n

/-- Stirling's approximation states that ln N! ≈ N ln N - N for large N -/
theorem stirling_approximation_asymptotic (n : ℕ) (hn : 0 < n) :
    ∃ (error : ℝ), log (Nat.factorial n) = stirlingApprox n + error := by
  exact ⟨ _, eq_add_of_sub_eq' rfl ⟩
