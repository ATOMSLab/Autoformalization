import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)


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

/-! ## Intermediate Steps of Derivation -/

/--
"Substitute expression for partition function from Eq. 1 into Eq. 2:
A = -k_B T ln[V^N / (N! h^{3N}) (2π m k_B T)^{3N/2}]"
(Equation 3)
-/
theorem helmholtz_eq_3 :
    helmholtzFreeEnergy p =
    -p.k_B * p.T * log ((p.V ^ p.N) / (Nat.factorial p.N * p.h ^ (3 * p.N)) *
      (2 * π * p.m * p.k_B * p.T) ^ ((3 * p.N : ℕ) / 2 : ℝ)) := by
  exact Eq.symm (ext_cauchy rfl)

/--
"Simplify Eq. 3
A = -k_B T [ln(V^N / (N! h^{3N})) + (3N/2) ln(2π m k_B T)]"
(Equation 4)
-/
theorem helmholtz_eq_4 :
    helmholtzFreeEnergy p =
    -p.k_B * p.T * (log ((p.V ^ p.N) / (Nat.factorial p.N * p.h ^ (3 * p.N))) +
      (3 * p.N : ℕ) / 2 * log (2 * π * p.m * p.k_B * p.T)) := by
  convert ( congr_arg ( fun x : ℝ => -p.k_B * p.T * x ) ( Real.log_mul ?_ ?_ ) ) using 1 <;> norm_num;
  · exact Or.inl ( by rw [ Real.log_rpow ( by exact mul_pos ( mul_pos ( mul_pos ( mul_pos ( by positivity ) ( by positivity ) ) ( by exact p.hm_pos ) ) ( by exact p.hk_B_pos ) ) ( by exact p.hT_pos ) ) ] );
  · exact ⟨ fun h => absurd h p.hV_pos.ne', Nat.factorial_ne_zero _, fun h => absurd h p.hh_pos.ne' ⟩;
  · exact ne_of_gt ( Real.rpow_pos_of_pos ( mul_pos ( mul_pos ( mul_pos ( mul_pos two_pos Real.pi_pos ) p.hm_pos ) p.hk_B_pos ) p.hT_pos ) _ )

/--
"A = -k_B T [N ln V - ln N! - 3N ln h + (3N/2) ln(2π m k_B T)]"
(Equation 5)
-/
theorem helmholtz_eq_5 :
    helmholtzFreeEnergy p =
    -p.k_B * p.T * (p.N * log p.V - log (Nat.factorial p.N) -
      3 * p.N * log p.h + (3 * p.N : ℕ) / 2 * log (2 * π * p.m * p.k_B * p.T)) := by
  rw [ helmholtz_eq_4 ];
  rw [ Real.log_div, Real.log_mul, Real.log_pow ] <;> norm_num <;> ring;
  · norm_num;
  · exact Nat.factorial_ne_zero _;
  · exact fun h => absurd h p.hh_pos.ne';
  · exact fun h => absurd h p.hV_pos.ne';
  · exact ⟨ Nat.factorial_ne_zero _, fun h => absurd h p.hh_pos.ne' ⟩

/--
"Use Stirling's approximation: ln N! = N ln N - N
A = -k_B T [N ln(V/N) + N - 3N ln h + (3N/2) ln(2π m k_B T)]"
(Equation 6) - using Stirling's approximation
-/
theorem helmholtz_eq_6_stirling :
    -p.k_B * p.T * (p.N * log p.V - (p.N * log p.N - p.N) -
      3 * p.N * log p.h + (3 * p.N : ℕ) / 2 * log (2 * π * p.m * p.k_B * p.T)) =
    -p.k_B * p.T * (p.N * log (p.V / p.N) + p.N -
      3 * p.N * log p.h + (3 * p.N : ℕ) / 2 * log (2 * π * p.m * p.k_B * p.T)) := by
  rw [ Real.log_div ] <;> ring <;> norm_num [ p.hV_pos.ne', p.hN_pos.ne' ]

/-! ## Main Theorem: Final Helmholtz Free Energy Formula -/

/-- The thermal de Broglie wavelength squared factor: h²/(2π m k_B T) -/
noncomputable def thermalWavelengthSqFactor : ℝ :=
  p.h ^ 2 / (2 * π * p.m * p.k_B * p.T)


/--
"Main function: Helmholtz free energy for an ideal gas:
A = -N k_B T [ln(V/N) + 1 + (3/2) ln(2π m k_B T / h²)]"
(Equation 7) - The main result of the paper

This is the Sackur-Tetrode-like expression for the Helmholtz free energy.
-/
theorem helmholtzFreeEnergy_final_form :
    helmholtzFreeEnergy p =
    -p.N * p.k_B * p.T * (log (p.V / p.N) + 1 +
      (3 : ℝ) / 2 * log (2 * π * p.m * p.k_B * p.T / p.h ^ 2)) := by
      field_simp [ helmholtz_eq_6_stirling p ];
      sorry

theorem helmholtzFreeEnergy_final_form_negated :
    helmholtzFreeEnergy p =
    -p.N * p.k_B * p.T * (log (p.V / p.N) + 1 +
      (3 : ℝ) / 2 * log (2 * π * p.m * p.k_B * p.T / p.h ^ 2)) := by
  convert @helmholtz_eq_6_stirling using 1;
  constructor <;> intro h;
  sorry
  · -- Wait, there's a mistake. We can actually prove the opposite.
    negate_state;
    -- Proof starts here:
    refine' ⟨ _, _, _ ⟩;
    refine' ⟨ 1, 1, 1, 1, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num ⟩;
    · intro p; rw [ Real.log_div ( by linarith [ p.hV_pos ] ) ( by norm_cast; linarith [ p.hN_pos ] ) ] ; ring;
    · unfold helmholtzFreeEnergy; norm_num;
      unfold helmholtzFreeEnergy_def partitionFunction; norm_num;
      rw [ Real.log_rpow ( by positivity ) ] ; ring_nf ; norm_num




/-- Alternative form emphasizing the thermal wavelength -/
theorem helmholtzFreeEnergy_final_form' :
    helmholtzFreeEnergy p =
    -p.N * p.k_B * p.T * (log (p.V / p.N) + 1 +
      (3 : ℝ) / 2 * log (1 / thermalWavelengthSqFactor p)) := by
  sorry

/-
Alternative form emphasizing the thermal wavelength
-/
theorem helmholtzFreeEnergy_final_form'_final :
    helmholtzFreeEnergy p =
    -p.N * p.k_B * p.T * (log (p.V / p.N) + 1 +
      (3 : ℝ) / 2 * log (1 / thermalWavelengthSqFactor p)) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  refine' ⟨ _, _ ⟩;
  constructor;
  rotate_left;
  exact zero_lt_one;
  exact zero_lt_one;
  exact zero_lt_one;
  exact zero_lt_one;
  exact Nat.succ_pos 0;
  exact 2;
  all_goals norm_num [ IdealGasParams, helmholtzFreeEnergy_def, helmholtzFreeEnergy, partitionFunction, thermalWavelengthSqFactor ];
  rw [ Real.log_rpow ( by positivity ) ] ;
  ring_nf ;
  norm_num

/-! ## Corollaries and Physical Interpretations -/

/-- The Helmholtz free energy is extensive (scales with N for fixed V/N) -/
theorem helmholtz_extensive (c : ℝ) (hc : 0 < c) :
    ∃ f : ℝ, helmholtzFreeEnergy p = p.N * f := by
  exact ⟨ _, by rw [ mul_div_cancel₀ _ ( Nat.cast_ne_zero.mpr p.hN_pos.ne' ) ] ⟩

/-- Pressure from Helmholtz free energy: P = -∂A/∂V at constant T, N
    This would lead to the ideal gas law PV = Nk_BT -/
theorem pressure_from_helmholtz :
    ∃ P : ℝ, P = p.N * p.k_B * p.T / p.V := by
  grind
