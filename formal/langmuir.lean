import Mathlib

-- Define the basic types and structures for the Langmuir model
structure LangmuirSystem where
  S₀ : ℝ  -- Total surface sites
  S : ℝ   -- Free surface sites
  A_ad : ℝ -- Adsorbed A molecules
  p_A : ℝ  -- Partial pressure of A
  k_ad : ℝ -- Adsorption rate constant
  k_d : ℝ  -- Desorption rate constant
  S₀_pos : 0 < S₀
  S_nonneg : 0 ≤ S
  A_ad_nonneg : 0 ≤ A_ad
  p_A_nonneg : 0 ≤ p_A
  k_ad_pos : 0 < k_ad
  k_d_pos : 0 < k_d

-- Define equilibrium constant
noncomputable def K_eq (sys : LangmuirSystem) : ℝ := sys.k_ad / sys.k_d

-- Define fractional coverage
noncomputable def theta_A (sys : LangmuirSystem) : ℝ := sys.A_ad / sys.S₀

-- Define adsorption rate
noncomputable def r_ad (sys : LangmuirSystem) : ℝ := sys.k_ad * sys.p_A * sys.S

-- Define desorption rate
noncomputable def r_d (sys : LangmuirSystem) : ℝ := sys.k_d * sys.A_ad

-- Site conservation law
def site_conservation (sys : LangmuirSystem) : Prop :=
  sys.S₀ = sys.S + sys.A_ad

-- Equilibrium condition
def equilibrium_condition (sys : LangmuirSystem) : Prop :=
  r_ad sys = r_d sys

-- Langmuir equilibrium relation
lemma langmuir_equilibrium (sys : LangmuirSystem)
  (h_eq : equilibrium_condition sys)
  (h_pA_pos : 0 < sys.p_A) :
  sys.S = (sys.k_d * sys.A_ad) / (sys.k_ad * sys.p_A) := by
  -- Substitute the expressions for r_ad and r_d into the equilibrium condition.
  have h_eq_subst : sys.k_ad * sys.p_A * sys.S = sys.k_d * sys.A_ad := by
    exact h_eq;
  rw [ ← h_eq_subst, mul_div_cancel_left₀ _ ( by nlinarith [ sys.k_ad_pos, sys.k_d_pos ] ) ]

lemma langmuir_total_sites (sys : LangmuirSystem)
  (h_cons : site_conservation sys)
  (h_eq : equilibrium_condition sys)
  (h_pA_pos : 0 < sys.p_A) :
  sys.S₀ = sys.A_ad / ((K_eq sys * sys.p_A) / (1 + K_eq sys * sys.p_A)) := by
  unfold K_eq
  field_simp;
  -- Substitute the expression for S from the equilibrium condition into the total surface sites equation and simplify.
  have h_sub : sys.S₀ = (sys.k_d * sys.A_ad) / (sys.k_ad * sys.p_A) + sys.A_ad := by
    -- Substitute the expression for S from the equilibrium condition into the site conservation equation to get the desired result.
    rw [h_cons, langmuir_equilibrium sys h_eq h_pA_pos];
  -- Substitute h_sub into the left side and simplify.
  rw [h_sub]
  field_simp
  ring_nf;
  norm_num [ mul_assoc, mul_comm sys.k_d, ne_of_gt sys.k_ad_pos, ne_of_gt sys.k_d_pos ];
  -- By commutativity of addition, we can rearrange the terms on the right-hand side.
  rw [add_comm]


lemma langmuir_coverage_ratio (sys : LangmuirSystem)
  (h_cons : site_conservation sys)
  (h_eq : equilibrium_condition sys)
  (h_pA_pos : 0 < sys.p_A) :
  sys.A_ad / sys.S₀ = (K_eq sys * sys.p_A) / (1 + K_eq sys * sys.p_A) := by
  -- Using the site conservation and equilibrium conditions, we can derive the expression for theta_A.
  have h_theta_A : sys.A_ad = (K_eq sys * sys.p_A * sys.S₀) / (1 + K_eq sys * sys.p_A) := by
    -- Using the site conservation and equilibrium conditions, we can express sys.A_ad in terms of sys.p_A and sys.S₀.
    have h_A_ad : sys.A_ad = (K_eq sys * sys.p_A * sys.S) := by
      -- Using the equilibrium condition and the definition of K_eq, we can derive the expression for A_ad.
      have h_A_ad : sys.A_ad = (sys.k_ad / sys.k_d) * sys.p_A * sys.S := by
        have h_eq : sys.k_ad * sys.p_A * sys.S = sys.k_d * sys.A_ad := by
          exact h_eq
        rw [ div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff ] <;> linarith [ sys.k_d_pos ];
      exact h_A_ad;
    rw [ eq_div_iff ] <;> nlinarith [ h_cons.symm, show 0 ≤ K_eq sys * sys.p_A by exact mul_nonneg ( div_nonneg sys.k_ad_pos.le sys.k_d_pos.le ) h_pA_pos.le ];
  rw [ h_theta_A, div_eq_iff ] <;> ring_nf ; linarith [ sys.S₀_pos ]


-- Main Langmuir isotherm theorem
theorem langmuir_isotherm (sys : LangmuirSystem)
  (h_cons : site_conservation sys)
  (h_eq : equilibrium_condition sys)
  (h_pA_pos : 0 < sys.p_A) :
  theta_A sys = (K_eq sys * sys.p_A) / (1 + K_eq sys * sys.p_A) := by
  -- By definition of $theta_A$, we have $theta_A = A_ad / S₀$.
  unfold theta_A;
  exact langmuir_coverage_ratio sys h_cons h_eq h_pA_pos


/-
The number of free surface sites S is strictly positive at equilibrium.
-/
lemma langmuir_S_pos (sys : LangmuirSystem)
  (h_cons : site_conservation sys)
  (h_eq : equilibrium_condition sys) :
  0 < sys.S := by
    cases eq_or_lt_of_le sys.S_nonneg <;> aesop;
    rw [ eq_comm ] at h; specialize h_cons; specialize h_eq; unfold equilibrium_condition at h_eq; unfold r_ad r_d at *; aesop;
    · linarith [ sys.k_d_pos ];
    · linarith [ sys.S₀_pos, h_cons.symm ]

/-
The ratio of adsorbed to free sites is not equal to KP/(1+KP) (which is the fractional coverage), but rather KP.
-/

lemma langmuir_coverage_ratio_false (sys : LangmuirSystem)
  (h_cons : site_conservation sys)
  (h_eq : equilibrium_condition sys)
  (h_pA_pos : 0 < sys.p_A) :
  sys.A_ad / sys.S ≠ (K_eq sys * sys.p_A) / (1 + K_eq sys * sys.p_A) := by
    -- From `equilibrium_condition`, `k_ad * p_A * S = k_d * A_ad`.
    -- So `A_ad / S = (k_ad * p_A) / k_d = K_eq * p_A`.
    have h_A_S : (sys.A_ad / sys.S) = K_eq sys * (sys.p_A) := by
      rw [ div_eq_iff ];
      · -- By definition of equilibrium condition, we have $k_ad * p_A * S = k_d * A_ad$.
        have h_eq : sys.k_ad * sys.p_A * sys.S = sys.k_d * sys.A_ad := by
          exact h_eq;
        unfold K_eq;
        rw [ div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff ] <;> linarith [ sys.k_d_pos ];
      · exact ne_of_gt ( langmuir_S_pos sys h_cons h_eq );
    norm_num +zetaDelta at *;
    rw [ eq_div_iff ] <;> nlinarith [ show 0 < K_eq sys * sys.p_A by exact mul_pos ( div_pos sys.k_ad_pos sys.k_d_pos ) h_pA_pos ]
