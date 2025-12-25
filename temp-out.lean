/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a36f0d87-9157-4af5-bef7-4179e30911a6

The following was proved by Aristotle:

- lemma exponential_from_functional_eq {f : ℝ → ℝ} (hf : ExponentialFunctionalEq f)
    (hf_pos : ∀ x, 0 < f x) (hf_cont : Continuous f) :
    ∃ c : ℝ, ∀ x, f x = f 0 * Real.exp (c * x)
-/

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
# Boltzmann Distribution Derivation

This file formalizes the derivation of the Boltzmann distribution from the
fundamental postulate of statistical mechanics.
-/

open Real BigOperators

/-- Energy levels are indexed by a finite type with at least one element -/
structure EnergyLevels (w : ℕ) [NeZero w] where
  ε : Fin w → ℝ
  ε_nonneg : ∀ i, 0 ≤ ε i
  ε_zero : ε ⟨0, NeZero.pos w⟩ = 0

/-- A probability distribution over energy levels -/
structure ProbDist (w : ℕ) where
  p : Fin w → ℝ
  p_nonneg : ∀ i, 0 ≤ p i
  p_sum_one : ∑ i, p i = 1

/-- The partition function Z = Σᵢ exp(-β·εᵢ) -/
noncomputable def partitionFunction {w : ℕ} [NeZero w] (levels : EnergyLevels w) (β : ℝ) : ℝ :=
  ∑ i, Real.exp (-β * levels.ε i)

/-- The Boltzmann distribution: pᵢ = (1/Z)·exp(-β·εᵢ) -/
noncomputable def boltzmannProb {w : ℕ} [NeZero w] (levels : EnergyLevels w) (β : ℝ) (i : Fin w) : ℝ :=
  Real.exp (-β * levels.ε i) / partitionFunction levels β

/-- Gibbs entropy: S = -Σᵢ pᵢ·ln(pᵢ) -/
noncomputable def gibbsEntropy {w : ℕ} (dist : ProbDist w) : ℝ :=
  -∑ i, dist.p i * Real.log (dist.p i)

/-- Internal energy: U = Σᵢ pᵢ·εᵢ -/
noncomputable def internalEnergy {w : ℕ} [NeZero w] (levels : EnergyLevels w) (dist : ProbDist w) : ℝ :=
  ∑ i, dist.p i * levels.ε i

/-- Free energy (Helmholtz): F = -T·ln(Z) -/
noncomputable def freeEnergy {w : ℕ} [NeZero w] (levels : EnergyLevels w) (T : ℝ) : ℝ :=
  -T * Real.log (partitionFunction levels (1/T))

/-- The fundamental functional equation characterizing exponential distributions -/
def ExponentialFunctionalEq (f : ℝ → ℝ) : Prop :=
  ∀ a b, f a * f b = f 0 * f (a + b)

/-- Lemma: The functional equation f(a)·f(b) = f(0)·f(a+b) implies f is exponential -/
lemma exponential_from_functional_eq {f : ℝ → ℝ} (hf : ExponentialFunctionalEq f)
    (hf_pos : ∀ x, 0 < f x) (hf_cont : Continuous f) :
    ∃ c : ℝ, ∀ x, f x = f 0 * Real.exp (c * x) := by
      -- Define $g(x) = \ln(f(x)/f(0))$. Then $g$ satisfies $g(a) + g(b) = g(a+b)$.
      set g : ℝ → ℝ := fun x => Real.log (f x / f 0)
      have hg_add : ∀ a b, g a + g b = g (a + b) := by
        -- Substitute the definition of $g$ into the equation and use the functional equation $hf$.
        intros a b
        simp [g, hf a b];
        rw [ ← Real.log_mul ( ne_of_gt ( div_pos ( hf_pos _ ) ( hf_pos _ ) ) ) ( ne_of_gt ( div_pos ( hf_pos _ ) ( hf_pos _ ) ) ), div_mul_div_comm ];
        rw [ hf a b ];
        rw [ mul_div_mul_left _ _ ( ne_of_gt ( hf_pos 0 ) ) ];
      -- Since $g$ is continuous and satisfies $g(a) + g(b) = g(a+b)$, it must be linear.
      have hg_linear : ∃ c : ℝ, ∀ x, g x = c * x := by
        have hg_linear : ∀ q : ℚ, g q = q * g 1 := by
          -- By induction on $n$, we can show that $g(nx) = ng(x)$ for any integer $n$.
          have hg_int : ∀ n : ℤ, ∀ x : ℝ, g (n * x) = n * g x := by
            -- We'll use induction on $n$ to show that $g(nx) = ng(x)$ for any integer $n$.
            intros n x
            induction' n using Int.induction_on with n ih;
            · simp +zetaDelta at *;
            · have := hg_add ( n * x ) x; push_cast at *; ring_nf at *; linarith;
            · grind;
          -- By definition of rational numbers, for any rational number $q$, we can write $q = \frac{m}{n}$ where $m$ and $n$ are integers.
          intro q
          obtain ⟨m, n, hn_ne_zero, hq⟩ : ∃ m n : ℤ, n ≠ 0 ∧ q = m / n := by
            exact ⟨ q.num, q.den, Nat.cast_ne_zero.mpr q.pos.ne', q.num_div_den.symm ⟩;
          have := hg_int n ( 1 / n ) ; simp_all +decide [ div_eq_mul_inv, mul_assoc ] ;
        -- Since $g$ is continuous and linear over the rationals, it must be linear over the reals.
        have hg_cont : Continuous g := by
          exact Continuous.log ( hf_cont.div_const _ ) fun x => ne_of_gt ( div_pos ( hf_pos x ) ( hf_pos 0 ) );
        use g 1;
        intros x
        by_contra hg_nonlinear;
        -- Since $g$ is continuous and $g(x) \neq g(1) * x$, there exists a neighborhood around $x$ where $g$ does not take the form $g(1) * x$.
        obtain ⟨ε, hε⟩ : ∃ ε > 0, ∀ y, abs (y - x) < ε → g y ≠ g 1 * y := by
          exact Metric.mem_nhds_iff.mp ( IsOpen.mem_nhds ( isOpen_compl_iff.mpr <| isClosed_eq hg_cont <| continuous_const.mul continuous_id' ) hg_nonlinear );
        rcases exists_rat_btwn ( show x - ε < x by linarith ) with ⟨ q, hq₁, hq₂ ⟩ ; exact hε.2 q ( abs_lt.2 ⟨ by linarith, by linarith ⟩ ) ( by linarith [ hg_linear q ] );
      exact ⟨ hg_linear.choose, fun x => by rw [ ← hg_linear.choose_spec x, Real.exp_log ( div_pos ( hf_pos x ) ( hf_pos 0 ) ), mul_div_cancel₀ _ ( ne_of_gt ( hf_pos 0 ) ) ] ⟩