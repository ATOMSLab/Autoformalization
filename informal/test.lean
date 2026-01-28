 import Mathlib
noncomputable section
open scoped BigOperators

namespace StatMechNote

/-- A microstate is an N-tuple of discrete energy levels in Fin w. -/
abbrev Microstate (N w : ℕ) : Type := Fin N → Fin w

/-- Total discrete energy index ∑ E_n (using the index i : Fin w as the integer energy unit). -/
def totalEnergyIndex {N w : ℕ} (s : Microstate N w) : ℕ :=
∑ n : Fin N, (s n).val

/-- Microstates compatible with a fixed total energy index E. -/
def microstatesAtEnergyIndex (N w : ℕ) (E : ℕ) : Type :=
{ s : Microstate N w // totalEnergyIndex s = E }

/-!
The key fix: provide Fintype instances explicitly.
They exist in mathlib, but for subtypes Lean sometimes needs help + classical.
-/

/-- Microstate N w = (Fin N → Fin w) is a finite type. -/
instance (N w : ℕ) : Fintype (Microstate N w) := by
dsimp [Microstate]
infer_instance

/-- The subtype of microstates with fixed total energy is also finite. -/
instance (N w E : ℕ) : Fintype (microstatesAtEnergyIndex N w E) := by
classical
dsimp [microstatesAtEnergyIndex]
infer_instance

/-- Multiplicity W_N: number of microstates at fixed total energy index. -/
def W_N (N w : ℕ) (E : ℕ) : ℕ :=
Fintype.card (microstatesAtEnergyIndex N w E)

end StatMechNote
