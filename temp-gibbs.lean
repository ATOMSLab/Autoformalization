/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7568efe7-d82d-44a0-85c6-a5285bbf475c

The following was proved by Aristotle:

- theorem thermodynamic_identity {w : ℕ} [NeZero w] (levels : EnergyLevels w) (T : ℝ) (hT : 0 < T) :
    let β

- theorem gibbs_entropy_formula {w : ℕ} [NeZero w] (levels : EnergyLevels w) (T : ℝ) (hT : 0 < T) :
    let β

- theorem beta_equals_inverse_temperature {w : ℕ} [NeZero w] (levels : EnergyLevels w)
    (T : ℝ) (hT : 0 < T) :
    let β

- theorem gibbs_helmholtz {w : ℕ} [NeZero w] (levels : EnergyLevels w) (T : ℝ) (hT : 0 < T) :
    let β


- theorem boltzmann_distribution_derivation {w : ℕ} [NeZero w]
    (levels : EnergyLevels w) (p : Fin w → ℝ)
    (hp_pos : ∀ i, 0 < p i)
    (hp_normalized : ∑ i, p i = 1)
    (hp_functional : ∀ a b : Fin w, ∀ (hab : (a : ℕ) + b < w),
      p a * p b = p ⟨0, NeZero.pos w⟩ * p ⟨(a : ℕ) + b, hab⟩) :
    ∃ β : ℝ, ∀ i, p i = boltzmannProb levels β i

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

- lemma boltzmannProb_sum_one {w : ℕ} [NeZero w] (levels : EnergyLevels w) (β : ℝ)
    (hβ : 0 ≤ β) : ∑ i, boltzmannProb levels β i = 1


- lemma boltzmannProb_nonneg {w : ℕ} [NeZero w] (levels : EnergyLevels w) (β : ℝ)
    (hβ : 0 ≤ β) (i : Fin w) : 0 ≤ boltzmannProb levels β i


- lemma partitionFunction_pos {w : ℕ} [NeZero w] (levels : EnergyLevels w) (β : ℝ)
    (hβ : 0 ≤ β) : 0 < partitionFunction levels β

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
  -- Define g(x) = ln(f(x)/f(0)). Then g(a + b) = g(a) + g(b) and g is continuous.
  set g : ℝ → ℝ := fun x => Real.log (f x / f 0)
  have hg_add : ∀ a b, g (a + b) = g a + g b := by
    norm_num +zetaDelta at *;
    intro a b; rw [ ← Real.log_mul ( ne_of_gt ( div_pos ( hf_pos _ ) ( hf_pos _ ) ) ) ( ne_of_gt ( div_pos ( hf_pos _ ) ( hf_pos _ ) ) ) ] ; rw [ div_mul_div_comm ] ; rw [ show f ( a + b ) = f a * f b / f 0 by rw [ eq_div_iff ( ne_of_gt ( hf_pos _ ) ) ] ; linarith [ hf a b ] ] ; ring
  have hg_cont : Continuous g := by
    exact Continuous.log ( hf_cont.div_const _ ) fun x => ne_of_gt ( div_pos ( hf_pos x ) ( hf_pos 0 ) );
  -- Since g is additive and continuous, it must be linear.
  have hg_linear : ∃ c : ℝ, ∀ x, g x = c * x := by
    have hg_linear : ∀ q : ℚ, g q = q * g 1 := by
      -- By induction on $n$, we can show that $g(n \cdot x) = n \cdot g(x)$ for any integer $n$ and real $x$.
      have hg_mul_int (n : ℤ) (x : ℝ) : g (n * x) = n * g x := by
        -- We prove this by induction on $n$.
        induction' n using Int.induction_on with n ih;
        · simpa using hg_add 0 x;
        · simp_all +decide [ add_mul ];
        · grind;
      -- For any rational number $q = \frac{m}{n}$, we can write $g(q) = g(\frac{m}{n}) = \frac{m}{n} g(1)$.
      intro q
      obtain ⟨m, n, hn_pos, hn_denom_pos, q_eq⟩ : ∃ m n : ℤ, n ≠ 0 ∧ q = m / n := by
        exact ⟨ q.num, q.den, Nat.cast_ne_zero.mpr q.pos.ne', q.num_div_den.symm ⟩;
      have := hg_mul_int n ( 1 / n ) ; simp_all +decide [ div_eq_mul_inv, mul_assoc ] ;
    use g 1;
    -- By the density of rationals in reals, for any real number $x$, there exists a sequence of rational numbers $q_n$ such that $q_n \to x$.
    intro x
    obtain ⟨q_n, hq_n⟩ : ∃ q_n : ℕ → ℚ, Filter.Tendsto (fun n => q_n n : ℕ → ℝ) Filter.atTop (nhds x) := by
      exact ⟨ fun n => Classical.choose <| exists_rat_btwn <| sub_lt_self x <| inv_pos.mpr <| Nat.cast_add_one_pos n, by exact tendsto_iff_dist_tendsto_zero.mpr <| squeeze_zero ( fun _ => by positivity ) ( fun n => by simpa using abs_sub_le_iff.mpr ⟨ by linarith [ Classical.choose_spec <| exists_rat_btwn <| sub_lt_self x <| inv_pos.mpr <| Nat.cast_add_one_pos n ], by linarith [ Classical.choose_spec <| exists_rat_btwn <| sub_lt_self x <| inv_pos.mpr <| Nat.cast_add_one_pos n ] ⟩ ) <| tendsto_one_div_add_atTop_nhds_zero_nat ⟩;
    exact tendsto_nhds_unique ( hg_cont.continuousAt.tendsto.comp hq_n ) ( by simpa [ mul_comm ] using Filter.Tendsto.congr ( by aesop ) ( hq_n.mul_const ( g 1 ) ) );
  exact hg_linear.imp fun c hc x => by rw [ ← hc x, Real.exp_log ( div_pos ( hf_pos x ) ( hf_pos 0 ) ), mul_div_cancel₀ _ ( ne_of_gt ( hf_pos 0 ) ) ] ;

/-- The partition function is positive when β ≥ 0 -/
lemma partitionFunction_pos {w : ℕ} [NeZero w] (levels : EnergyLevels w) (β : ℝ)
    (hβ : 0 ≤ β) : 0 < partitionFunction levels β := by
  exact Finset.sum_pos ( fun i _ => Real.exp_pos _ ) Finset.univ_nonempty

/-- Boltzmann probabilities are non-negative -/
lemma boltzmannProb_nonneg {w : ℕ} [NeZero w] (levels : EnergyLevels w) (β : ℝ)
    (hβ : 0 ≤ β) (i : Fin w) : 0 ≤ boltzmannProb levels β i := by
  exact div_nonneg ( Real.exp_nonneg _ ) ( Finset.sum_nonneg fun _ _ => Real.exp_nonneg _ )

/-- Boltzmann probabilities sum to 1 -/
lemma boltzmannProb_sum_one {w : ℕ} [NeZero w] (levels : EnergyLevels w) (β : ℝ)
    (hβ : 0 ≤ β) : ∑ i, boltzmannProb levels β i = 1 := by
  -- By definition of boltzmannProb, we can rewrite the sum as:
  have h_sum_def : ∑ i, boltzmannProb levels β i = ∑ i, (Real.exp (-β * levels.ε i) / partitionFunction levels β) := by
    rfl;
  rw [ h_sum_def, ← Finset.sum_div ];
  exact div_self <| ne_of_gt <| partitionFunction_pos levels β hβ

/-- The Boltzmann distribution as a valid probability distribution -/
noncomputable def boltzmannDist {w : ℕ} [NeZero w] (levels : EnergyLevels w) (β : ℝ)
    (hβ : 0 ≤ β) : ProbDist w where
  p := boltzmannProb levels β
  p_nonneg := boltzmannProb_nonneg levels β hβ
  p_sum_one := boltzmannProb_sum_one levels β hβ

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected name `AristotleLemmas` after `end`: The current section is unnamed

Hint: Delete the name `AristotleLemmas` to end the current unnamed scope; outer named scopes can then be closed using additional `end` command(s):
  end ̵A̵r̵i̵s̵t̵o̵t̵l̵e̵L̵e̵m̵m̵a̵s̵
unexpected token '/'; expected term
`boltzmann_distribution_derivation` has already been declared-/
/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected name `AristotleLemmas` after `end`: The current section is unnamed

Hint: Delete the name `AristotleLemmas` to end the current unnamed scope; outer named scopes can then be closed using additional `end` command(s):
  end ̵A̵r̵i̵s̵t̵o̵t̵l̵e̵L̵e̵m̵m̵a̵s̵
unexpected token '/'; expected term
`boltzmann_distribution_derivation` has already been declared-/
/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected name `AristotleLemmas` after `end`: The current section is unnamed

Hint: Delete the name `AristotleLemmas` to end the current unnamed scope; outer named scopes can then be closed using additional `end` command(s):
  end ̵A̵r̵i̵s̵t̵o̵t̵l̵e̵L̵e̵m̵m̵a̵s̵
unexpected token '/'; expected term
`boltzmann_distribution_derivation` has already been declared-/
/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected name `AristotleLemmas` after `end`: The current section is unnamed

Hint: Delete the name `AristotleLemmas` to end the current unnamed scope; outer named scopes can then be closed using additional `end` command(s):
  end ̵A̵r̵i̵s̵t̵o̵t̵l̵e̵L̵e̵m̵m̵a̵s̵
unexpected token '/'; expected term
`boltzmann_distribution_derivation` has already been declared-/
/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Energy levels for the counterexample: ε₀=0, ε₁=1, ε₂=4. These are non-linear with respect to the index.
-/
def badLevels : EnergyLevels 3 where
  ε i := if i.val = 0 then 0 else if i.val = 1 then 1 else 4
  ε_nonneg := by
    norm_cast
  ε_zero := by
    grind

/-
Definition of the counterexample probability distribution and proof that it is positive everywhere.
-/
def badP : Fin 3 → ℝ := fun i => if i.val = 0 then 1/7 else if i.val = 1 then 2/7 else 4/7

lemma badP_pos : ∀ i, 0 < badP i := by
  intro i
  fin_cases i <;> simp [badP] <;> norm_num

/-
Proof that the sum of probabilities in the counterexample is 1.
-/
lemma badP_sum : ∑ i, badP i = 1 := by
  simp [badP, Fin.sum_univ_three]
  norm_num

/-
Proof that the counterexample satisfies the functional equation.
-/
lemma badP_functional : ∀ a b : Fin 3, ∀ (hab : (a : ℕ) + b < 3),
      badP a * badP b = badP ⟨0, by
        norm_num⟩ * badP ⟨(a : ℕ) + b, hab⟩ := by
        unfold badP; norm_num [ Fin.forall_fin_succ ] ;

/-
Proof that the counterexample is not a Boltzmann distribution. We derive a contradiction by comparing the ratios p(1)/p(0) and p(2)/p(0).
-/
lemma badP_not_boltzmann : ¬ ∃ β : ℝ, ∀ i, badP i = boltzmannProb badLevels β i := by
  unfold boltzmannProb badP badLevels ; norm_num;
  by_contra! h;
  simp_all +decide [ Fin.forall_fin_succ ];
  norm_num [ div_eq_mul_inv, Real.exp_mul, Real.exp_neg ] at *;
  grind

/-
Disproof of the Boltzmann distribution derivation theorem using the counterexample.
-/
theorem boltzmann_distribution_derivation_false : ¬ (∀ {w : ℕ} [NeZero w]
    (levels : EnergyLevels w) (p : Fin w → ℝ)
    (hp_pos : ∀ i, 0 < p i)
    (hp_normalized : ∑ i, p i = 1)
    (hp_functional : ∀ a b : Fin w, ∀ (hab : (a : ℕ) + b < w),
      p a * p b = p ⟨0, NeZero.pos w⟩ * p ⟨(a : ℕ) + b, hab⟩),
    ∃ β : ℝ, ∀ i, p i = boltzmannProb levels β i) := by
  intro h
  specialize h badLevels badP badP_pos badP_sum badP_functional
  exact badP_not_boltzmann h

end AristotleLemmas

/-
Main theorem: Derivation of Boltzmann distribution from equiprobability.
    If a probability distribution p over energy levels satisfies the multiplicative
    property p(εₐ)·p(εᵦ) = p(0)·p(εₐ + εᵦ) arising from the fundamental postulate,
    then p must be the Boltzmann distribution.
-/
theorem boltzmann_distribution_derivation {w : ℕ} [NeZero w]
    (levels : EnergyLevels w) (p : Fin w → ℝ)
    (hp_pos : ∀ i, 0 < p i)
    (hp_normalized : ∑ i, p i = 1)
    (hp_functional : ∀ a b : Fin w, ∀ (hab : (a : ℕ) + b < w),
      p a * p b = p ⟨0, NeZero.pos w⟩ * p ⟨(a : ℕ) + b, hab⟩) :
    ∃ β : ℝ, ∀ i, p i = boltzmannProb levels β i := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose any $w$ and define the energy levels and probability distribution as described.
  use 3, by
    -- Show that 3 is a positive natural number.
    infer_instance
  generalize_proofs at *
  generalize_proofs at *;
  -- Let's choose the energy levels and probability distribution as described.
  use badLevels, badP
  generalize_proofs at *;
  -- Now let's verify the functional equation.
  apply And.intro (badP_pos) (And.intro (badP_sum) (And.intro (badP_functional) (fun x => by
    by_contra! h;
    exact badP_not_boltzmann ⟨ x, h ⟩)))

-/
/-- Main theorem: Derivation of Boltzmann distribution from equiprobability.
    If a probability distribution p over energy levels satisfies the multiplicative
    property p(εₐ)·p(εᵦ) = p(0)·p(εₐ + εᵦ) arising from the fundamental postulate,
    then p must be the Boltzmann distribution. -/

theorem boltzmann_distribution_derivation' {w : ℕ} [NeZero w]
    (levels : EnergyLevels w) (p : Fin w → ℝ)
    (hp_pos : ∀ i, 0 < p i)
    (hp_normalized : ∑ i, p i = 1)
    (hp_functional : ∀ a b : Fin w, ∀ (hab : (a : ℕ) + b < w),
      p a * p b = p ⟨0, NeZero.pos w⟩ * p ⟨(a : ℕ) + b, hab⟩) :
    ∃ β : ℝ, ∀ i, p i = boltzmannProb levels β i := by
  sorry

def badLevels : EnergyLevels 3 where
  ε i := if i.val = 0 then 0 else if i.val = 1 then 1 else 4
  ε_nonneg := by
    norm_cast
  ε_zero := by
    grind

/-
Definition of the counterexample probability distribution and proof that it is positive everywhere.
-/
noncomputable def badP : Fin 3 → ℝ := fun i => if i.val = 0 then 1/7 else if i.val = 1 then 2/7 else 4/7

lemma badP_pos : ∀ i, 0 < badP i := by
  intro i
  fin_cases i <;> simp [badP] <;> norm_num

/-
Proof that the sum of probabilities in the counterexample is 1.
-/
lemma badP_sum : ∑ i, badP i = 1 := by
  simp [badP, Fin.sum_univ_three]
  norm_num

/-
Proof that the counterexample satisfies the functional equation.
-/
lemma badP_functional : ∀ a b : Fin 3, ∀ (hab : (a : ℕ) + b < 3),
      badP a * badP b = badP ⟨0, by
        norm_num⟩ * badP ⟨(a : ℕ) + b, hab⟩ := by
        unfold badP; norm_num [ Fin.forall_fin_succ ] ;

/-
Proof that the counterexample is not a Boltzmann distribution. We derive a contradiction by comparing the ratios p(1)/p(0) and p(2)/p(0).
-/
lemma badP_not_boltzmann : ¬ ∃ β : ℝ, ∀ i, badP i = boltzmannProb badLevels β i := by
  unfold boltzmannProb badP badLevels ; norm_num;
  by_contra! h;
  simp_all +decide [ Fin.forall_fin_succ ];
  norm_num [ div_eq_mul_inv, Real.exp_mul, Real.exp_neg ] at *;
  grind

/-
Disproof of the Boltzmann distribution derivation theorem using the counterexample.
-/
theorem boltzmann_distribution_derivation_false : ¬ (∀ {w : ℕ} [NeZero w]
    (levels : EnergyLevels w) (p : Fin w → ℝ)
    (hp_pos : ∀ i, 0 < p i)
    (hp_normalized : ∑ i, p i = 1)
    (hp_functional : ∀ a b : Fin w, ∀ (hab : (a : ℕ) + b < w),
      p a * p b = p ⟨0, NeZero.pos w⟩ * p ⟨(a : ℕ) + b, hab⟩),
    ∃ β : ℝ, ∀ i, p i = boltzmannProb levels β i) := by
  intro h
  specialize h badLevels badP badP_pos badP_sum badP_functional
  exact badP_not_boltzmann h


/-
Main theorem: Derivation of Boltzmann distribution from equiprobability.
    If a probability distribution p over energy levels satisfies the multiplicative
    property p(εₐ)·p(εᵦ) = p(0)·p(εₐ + εᵦ) arising from the fundamental postulate,
    then p must be the Boltzmann distribution.
-/
theorem boltzmann_distribution_derivation {w : ℕ} [NeZero w]
    (levels : EnergyLevels w) (p : Fin w → ℝ)
    (hp_pos : ∀ i, 0 < p i)
    (hp_normalized : ∑ i, p i = 1)
    (hp_functional : ∀ a b : Fin w, ∀ (hab : (a : ℕ) + b < w),
      p a * p b = p ⟨0, NeZero.pos w⟩ * p ⟨(a : ℕ) + b, hab⟩) :
    ∃ β : ℝ, ∀ i, p i = boltzmannProb levels β i := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose any $w$ and define the energy levels and probability distribution as described.
  use 3, by
    -- Show that 3 is a positive natural number.
    infer_instance
  generalize_proofs at *
  generalize_proofs at *;
  -- Let's choose the energy levels and probability distribution as described.
  use badLevels, badP
  generalize_proofs at *;
  -- Now let's verify the functional equation.
  apply And.intro (badP_pos) (And.intro (badP_sum) (And.intro (badP_functional) (fun x => by
    by_contra! h;
    exact badP_not_boltzmann ⟨ x, h ⟩)))




/-- Helper lemma: 1/T > 0 when T > 0 -/
lemma one_div_pos_of_pos {T : ℝ} (hT : 0 < T) : 0 < 1 / T := by
  exact one_div_pos.mpr hT

/-- Helper lemma: 1/T ≥ 0 when T > 0 -/
lemma one_div_nonneg_of_pos {T : ℝ} (hT : 0 < T) : 0 ≤ 1 / T := by
  exact le_of_lt (one_div_pos.mpr hT)

/-- Gibbs-Helmholtz relation: U = ∂(F/T)/∂(1/T) -/
theorem gibbs_helmholtz {w : ℕ} [NeZero w] (levels : EnergyLevels w) (T : ℝ) (hT : 0 < T) :
    let β := 1/T
    let dist := boltzmannDist levels β (one_div_nonneg_of_pos hT)
    internalEnergy levels dist =
      -deriv (fun β' => Real.log (partitionFunction levels β')) (1/T) := by
  unfold internalEnergy boltzmannDist
  generalize_proofs at *;
  unfold partitionFunction boltzmannProb;
  unfold partitionFunction; rw [ deriv.log ] <;> norm_num [ mul_comm ];
  · simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
  · exact ne_of_gt <| Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) Finset.univ_nonempty

/-- The relationship F = -T·ln(Z) -/
theorem free_energy_partition {w : ℕ} [NeZero w] (levels : EnergyLevels w) (T : ℝ) (hT : 0 < T) :
    freeEnergy levels T = -T * Real.log (partitionFunction levels (1/T)) := by
  rfl

/-- Identification of β = 1/T from thermodynamic consistency -/
theorem beta_equals_inverse_temperature {w : ℕ} [NeZero w] (levels : EnergyLevels w)
    (T : ℝ) (hT : 0 < T) :
    let β := 1/T
    let dist := boltzmannDist levels β (one_div_nonneg_of_pos hT)
    let U := internalEnergy levels dist
    let S := gibbsEntropy dist
    let F := freeEnergy levels T
    U = F + T * S := by
  -- Next, we use the definition of the Gibbs entropy and the fact that it is a maximum for the Boltzmann distribution.
  have h_gibbs_entropy : gibbsEntropy (boltzmannDist levels (1 / T) (one_div_nonneg_of_pos hT)) = (1 / T) * (internalEnergy levels (boltzmannDist levels (1 / T) (one_div_nonneg_of_pos hT))) + Real.log (partitionFunction levels (1 / T)) := by
    unfold gibbsEntropy internalEnergy boltzmannDist;
    simp +decide [ boltzmannProb, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Real.log_div, Real.log_mul, ne_of_gt ( show 0 < partitionFunction levels ( 1 / T ) from Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) ⟨ ⟨ 0, NeZero.pos w ⟩, Finset.mem_univ _ ⟩ ) ];
    rw [ Finset.sum_congr rfl fun i _ => by rw [ Real.log_div ( by positivity ) ( by exact ne_of_gt <| Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) ⟨ i, Finset.mem_univ _ ⟩ ) ] ] ; ring;
    norm_num [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
    simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, partitionFunction ];
    rw [ inv_mul_eq_div, div_eq_iff ( ne_of_gt <| Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) ⟨ ⟨ 0, NeZero.pos w ⟩, Finset.mem_univ _ ⟩ ) ];
  simp_all +decide [ Real.log_div, ne_of_gt ];
  unfold freeEnergy; ring; norm_num [ hT.ne' ] ;

/-- Gibbs entropy formula derived from Boltzmann distribution -/
theorem gibbs_entropy_formula {w : ℕ} [NeZero w] (levels : EnergyLevels w) (T : ℝ) (hT : 0 < T) :
    let β := 1/T
    let dist := boltzmannDist levels β (one_div_nonneg_of_pos hT)
    gibbsEntropy dist = Real.log (partitionFunction levels β) +
      β * internalEnergy levels dist := by
  field_simp;
  have := beta_equals_inverse_temperature levels T hT;
  unfold freeEnergy at *; aesop;

/-- The complete thermodynamic identity: F = U - TS with S = -Σᵢ pᵢ ln pᵢ -/
theorem thermodynamic_identity {w : ℕ} [NeZero w] (levels : EnergyLevels w) (T : ℝ) (hT : 0 < T) :
    let β := 1/T
    let dist := boltzmannDist levels β (one_div_nonneg_of_pos hT)
    freeEnergy levels T = internalEnergy levels dist - T * gibbsEntropy dist := by
  have := @beta_equals_inverse_temperature w _ levels T hT;
  bound
