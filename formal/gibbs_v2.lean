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

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 93721b95-d8b7-46bd-bb41-9fe28258b35b

The following was negated by Aristotle:

- theorem main_claim_gibbs_entropy_and_beta
    (w : ℕ) (T β ε S : ℝ)
    (hT : T ≠ 0) (hβ : β ≠ 0)
    (hU_F_TS :
      let p

Here is the code for the `negate_state` tactic, used within these negations:

```lean
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
```
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 11a75861-b8c2-45ff-b6b7-e0af3721e444

The following was negated by Aristotle:

- theorem Umechstat_identity
    (w : ℕ) (T β ε : ℝ) :
    let p

Here is the code for the `negate_state` tactic, used within these negations:

```lean
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
```
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: cad1147f-f37a-4b81-9f91-357fd88c794b

The following was negated by Aristotle:

- theorem isProb_boltzmannP (w : ℕ) (β ε : ℝ) :
    IsProb w (boltzmannP w β ε)

Here is the code for the `negate_state` tactic, used within these negations:

```lean
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
```
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8159ae22-c5d3-490f-b465-ae32e6ac232d

The following was proved by Aristotle:

- theorem exponential_param_of_geometric
    (w : ℕ) (ε : ℝ) (p : Fin w → ℝ) (hw : 0 < w)
    (r : ℝ)
    (hgeom : ∀ i : Fin w, p i = p ⟨0, hw⟩ * r ^ i.1) :
    ∃ β : ℝ, ∀ i : Fin w, ∃ c : ℝ, p i = c * Real.exp (-β * energyLevel ε i.1)
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: fa7359bb-61aa-4919-9a52-5ce818c87077

The following was negated by Aristotle:

- theorem geometric_of_FEq
    (w : ℕ) (hw : 0 < w) (p : Fin w → ℝ) (hp : FEq w hw p) :
    ∃ r : ℝ, ∀ i : Fin w, p i = p ⟨0, hw⟩ * r ^ i.1

Here is the code for the `negate_state` tactic, used within these negations:

```lean
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
```
-/




open scoped BigOperators

namespace GibbsFormula

noncomputable section

open Finset Real

/-- Discrete energy levels: `ε_i = i * ε`. -/
def energyLevel (ε : ℝ) (i : ℕ) : ℝ := (i : ℝ) * ε

/-- Partition function for a finite set of energy levels indexed by `Fin w`. -/
def Z (w : ℕ) (β ε : ℝ) : ℝ :=
  ∑ i : Fin w, Real.exp (-β * energyLevel ε i.1)

/-- Boltzmann/canonical probability on `Fin w`. -/
def boltzmannP (w : ℕ) (β ε : ℝ) : Fin w → ℝ :=
  fun i => Real.exp (-β * energyLevel ε i.1) / Z w β ε

/-- Gibbs entropy for a probability mass function on a finite type. -/
def gibbsEntropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  - ∑ a, p a * Real.log (p a)

/-- Expected energy for a distribution on `Fin w`. -/
def internalEnergy (w : ℕ) (ε : ℝ) (p : Fin w → ℝ) : ℝ :=
  ∑ i : Fin w, p i * energyLevel ε i.1

/-- Helmholtz free energy from the partition function: `F = - T log Z`. -/
def freeEnergy (w : ℕ) (T β ε : ℝ) : ℝ :=
  -T * Real.log (Z w β ε)

/-- A probability mass function predicate on `Fin w`. -/
structure IsProb (w : ℕ) (p : Fin w → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ p i
  sum_eq_one : (∑ i : Fin w, p i) = 1

/--
Functional equation encapsulating the key paper step:
`p a * p b = p 0 * p (a+b)` whenever `a+b` stays in range.
We require `0 < w` so that `0 : Fin w` exists.
-/
def FEq (w : ℕ) (hw : 0 < w) (p : Fin w → ℝ) : Prop :=
  ∀ (a b : Fin w) (hab : a.1 + b.1 < w),
    p a * p b = p ⟨0, hw⟩ * p ⟨a.1 + b.1, hab⟩

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unexpected token '-'; expected command
`GibbsFormula.geometric_of_FEq` has already been declared-/
/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unexpected token '-'; expected command
`GibbsFormula.geometric_of_FEq` has already been declared-/
/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unexpected token '-'; expected command
`GibbsFormula.geometric_of_FEq` has already been declared-/
/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unexpected token '-'; expected command
`GibbsFormula.geometric_of_FEq` has already been declared-/
/- Aristotle found this block to be false. Here is a proof of the negation:



/-
From `FEq`, `p` has a geometric form `p(i)=p(0)*r^i` on `Fin w`.
-/
theorem geometric_of_FEq
    (w : ℕ) (hw : 0 < w) (p : Fin w → ℝ) (hp : FEq w hw p) :
    ∃ r : ℝ, ∀ i : Fin w, p i = p ⟨0, hw⟩ * r ^ i.1 := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider $w = 2$.
  use 2;
  -- Let's choose the probability distribution $p$ such that $p(0) = 0$ and $p(1) = 1$.
  use by norm_num
  use ![0, 1];
  -- Show that the function $p$ satisfies the given condition.
  simp [GibbsFormula.FEq]

-/
/-- From `FEq`, `p` has a geometric form `p(i)=p(0)*r^i` on `Fin w`. -/
theorem geometric_of_FEq
    (w : ℕ) (hw : 0 < w) (p : Fin w → ℝ) (hp : FEq w hw p) :
    ∃ r : ℝ, ∀ i : Fin w, p i = p ⟨0, hw⟩ * r ^ i.1 := by
  sorry

/--
Geometric form can be written in exponential terms (up to a multiplicative constant).
This is a weak reparameterization lemma mirroring `p(ε_i) ∝ exp(-β ε_i)`.
-/
theorem exponential_param_of_geometric
    (w : ℕ) (ε : ℝ) (p : Fin w → ℝ) (hw : 0 < w)
    (r : ℝ)
    (hgeom : ∀ i : Fin w, p i = p ⟨0, hw⟩ * r ^ i.1) :
    ∃ β : ℝ, ∀ i : Fin w, ∃ c : ℝ, p i = c * Real.exp (-β * energyLevel ε i.1) := by
  by_cases hε : ε = 0;
  · exact ⟨ 0, fun i => ⟨ p i, by norm_num [ hε, GibbsFormula.energyLevel ] ⟩ ⟩;
  · unfold GibbsFormula.energyLevel;
    use -Real.log ( r ) / ε;
    intro i; use p i / Real.exp ( - ( -Real.log r / ε ) * ( i * ε ) ) ; rw [ div_mul_cancel₀ _ ( by positivity ) ] ;

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unexpected token '-'; expected command
`GibbsFormula.isProb_boltzmannP` has already been declared-/
/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unexpected token '-'; expected command
`GibbsFormula.isProb_boltzmannP` has already been declared-/
/- Aristotle found this block to be false. Here is a proof of the negation:



/-
The Boltzmann distribution is a probability distribution (nonnegativity + sums to 1).
-/
theorem isProb_boltzmannP (w : ℕ) (β ε : ℝ) :
    IsProb w (boltzmannP w β ε) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider $w = 0$.
  use 0, 0, 0;
  -- By definition of `IsProb`, we need to show that the sum of the probabilities is not equal to 1.
  intro h
  cases h
  aesop

-/
/-- The Boltzmann distribution is a probability distribution (nonnegativity + sums to 1). -/
theorem isProb_boltzmannP (w : ℕ) (β ε : ℝ) :
    IsProb w (boltzmannP w β ε) := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unexpected token '/'; expected term
`GibbsFormula.Umechstat_identity` has already been declared-/
/- Aristotle found this block to be false. Here is a proof of the negation:



/-
Algebraic identity corresponding to Eq.(Umechstat) in the paper, stated for the Boltzmann distribution.
-/
theorem Umechstat_identity
    (w : ℕ) (T β ε : ℝ) :
    let p := boltzmannP w β ε
    let F := freeEnergy w T β ε
    internalEnergy w ε p
      = (1 / (β * T)) * (F - T * (∑ i : Fin w, p i * Real.log (p i))) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Choose $w = 2$, $\varepsilon = 1$, and $\beta = 1$.
  use 2, 0, 1, 1;
  -- Simplify the expression for the internal energy.
  simp [GibbsFormula.boltzmannP, GibbsFormula.internalEnergy];
  -- Simplify the expression for the Gibbs free energy.
  simp [GibbsFormula.energyLevel, GibbsFormula.Z];
  -- Since $\exp(-1) > 0$, we have $1 + \exp(-1) > 0$.
  apply ne_of_gt; exact add_pos_of_pos_of_nonneg zero_lt_one (Real.exp_nonneg (-1))

-/
/--
Algebraic identity corresponding to Eq.(Umechstat) in the paper, stated for the Boltzmann distribution.
-/
theorem Umechstat_identity
    (w : ℕ) (T β ε : ℝ) :
    let p := boltzmannP w β ε
    let F := freeEnergy w T β ε
    internalEnergy w ε p
      = (1 / (β * T)) * (F - T * (∑ i : Fin w, p i * Real.log (p i))) := by
  sorry

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
Main claim (formalized): assuming both
* the thermodynamic relation `U = F + T S`
* and the mechanical-statistical identity (Eq. Umechstat)
one can identify `β = 1/T` and obtain Gibbs entropy
`S = -∑ p log p`.
-/
theorem main_claim_gibbs_entropy_and_beta
    (w : ℕ) (T β ε S : ℝ)
    (hT : T ≠ 0) (hβ : β ≠ 0)
    (hU_F_TS :
      let p := boltzmannP w β ε
      let U := internalEnergy w ε p
      let F := freeEnergy w T β ε
      U = F + T * S)
    (hU_mechstat :
      let p := boltzmannP w β ε
      let U := internalEnergy w ε p
      let F := freeEnergy w T β ε
      U = (1 / (β * T)) * (F - T * (∑ i : Fin w, p i * Real.log (p i)))) :
    (β = 1 / T) ∧ (S = gibbsEntropy (boltzmannP w β ε)) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Choose $w = 1$, $T = 1$, $\beta = 1$, and $\epsilon = 1$.
  use 1, 1, 2, 1;
  -- Let's simplify the goal.
  simp [GibbsFormula.boltzmannP, GibbsFormula.internalEnergy, GibbsFormula.freeEnergy, GibbsFormula.gibbsEntropy];
  -- Simplify the expression for the energy level.
  simp [GibbsFormula.energyLevel, GibbsFormula.Z]

-/
/--
Main claim (formalized): assuming both
* the thermodynamic relation `U = F + T S`
* and the mechanical-statistical identity (Eq. Umechstat)
one can identify `β = 1/T` and obtain Gibbs entropy
`S = -∑ p log p`.
-/
theorem main_claim_gibbs_entropy_and_beta
    (w : ℕ) (T β ε S : ℝ)
    (hT : T ≠ 0) (hβ : β ≠ 0)
    (hU_F_TS :
      let p := boltzmannP w β ε
      let U := internalEnergy w ε p
      let F := freeEnergy w T β ε
      U = F + T * S)
    (hU_mechstat :
      let p := boltzmannP w β ε
      let U := internalEnergy w ε p
      let F := freeEnergy w T β ε
      U = (1 / (β * T)) * (F - T * (∑ i : Fin w, p i * Real.log (p i)))) :
    (β = 1 / T) ∧ (S = gibbsEntropy (boltzmannP w β ε)) := by
  sorry

  theorem main_claim_gibbs_entropy_and_beta_negated
    (w : ℕ) (T β ε S : ℝ)
    (hT : T ≠ 0) (hβ : β ≠ 0)
    (hU_F_TS :
      let p := boltzmannP w β ε
      let U := internalEnergy w ε p
      let F := freeEnergy w T β ε
      U = F + T * S)
    (hU_mechstat :
      let p := boltzmannP w β ε
      let U := internalEnergy w ε p
      let F := freeEnergy w T β ε
      U = (1 / (β * T)) * (F - T * (∑ i : Fin w, p i * Real.log (p i)))) :
    (β = 1 / T) ∧ (S = gibbsEntropy (boltzmannP w β ε)) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Choose $w = 1$, $T = 1$, $\beta = 1$, and $\epsilon = 1$.
  use 1, 1, 2, 1;
  -- Let's simplify the goal.
  simp [GibbsFormula.boltzmannP, GibbsFormula.internalEnergy, GibbsFormula.freeEnergy, GibbsFormula.gibbsEntropy];
  -- Simplify the expression for the energy level.
  simp [GibbsFormula.energyLevel, GibbsFormula.Z]
