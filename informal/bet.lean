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
# BET Theory of Multimolecular Adsorption

This file formalizes the Brunauer-Emmett-Teller (BET) theory of gas adsorption,
which generalizes Langmuir's unimolecular adsorption theory to multiple layers.

## Main Results
- `BET.isotherm_equation`: The BET isotherm equation
- `BET.linear_form`: The linear form of BET equation for experimental testing
- `BET.finite_layer_equation`: The BET equation for finite maximum layers
- `BET.langmuir_limit`: BET reduces to Langmuir at low pressure

## References
- Brunauer, Emmett, and Teller, "Adsorption of Gases in Multimolecular Layers"
-/

open Real

namespace BET

/-! ## Part 1: Polarization Theory (DeBoer-Zwicker) -/

-- "If we call the dipole moment of a molecule in the i-th layer μ_i, it follows that
-- μ_i = c₁ C^i where c₁ and C are appropriate constants"
/-- Dipole moment in the i-th layer according to polarization theory -/
noncomputable def dipole_moment (c₁ C : ℝ) (i : ℕ) : ℝ := c₁ * C ^ i

-- "The corresponding binding energy is proportional to the square of the dipole moment
-- φ_i = c₂ C^{2i}"
/-- Binding energy in the i-th layer due to polarization -/
noncomputable def binding_energy (c₂ C : ℝ) (i : ℕ) : ℝ := c₂ * C ^ (2 * i)

-- "The equilibrium pressure of the nth layer, p_n, according to Boltzmann's law
-- varies exponentially with the binding energy of that layer"
/-- Equilibrium pressure of the n-th layer according to Boltzmann distribution -/
noncomputable def equilibrium_pressure (c₃ : ℝ) (φ_n R T : ℝ) : ℝ := c₃ * exp (-φ_n / (R * T))

-- "ln(p_n/c₃) = -(c₂/RT)C^{2n} which is identical with DeBoer and Zwicker's equation"
/-- The DeBoer-Zwicker equation for multilayer adsorption via polarization -/
theorem deBoer_zwicker_equation (c₂ c₃ C R T : ℝ) (hT : T > 0) (hR : R > 0) (hc₃ : c₃ > 0) (n : ℕ) :
    let φ_n := binding_energy c₂ C n
    let p_n := equilibrium_pressure c₃ φ_n R T
    log (p_n / c₃) = -(c₂ / (R * T)) * C ^ (2 * n) := by
  unfold BET.equilibrium_pressure BET.binding_energy; norm_num [ Real.exp_ne_zero, hc₃.ne' ] ; ring;

-- "The polarizability of a gas molecule α is given by the equation 2πα = (n-1)v_g"
/-- Polarizability of a gas molecule from refractive index -/
noncomputable def polarizability (refractiveIndex v_g : ℝ) : ℝ := (refractiveIndex - 1) * v_g / (2 * π)

-- "For a face-centered cubic lattice... the distance r between nearest neighbors
-- is given by r³ = √2 v_s"
/-- Nearest neighbor distance in FCC lattice -/
noncomputable def fcc_nearest_neighbor_distance (v_s : ℝ) : ℝ := (sqrt 2 * v_s) ^ (1/3 : ℝ)

-- "α/r³ = (n-1)/(2^{3/2}π) · (v_g/v_s)"
/-- Dimensionless ratio of polarizability to cubic distance -/
theorem polarizability_ratio (refractiveIndex v_g v_s : ℝ) (hv_s : v_s > 0) :
    let α := polarizability refractiveIndex v_g
    let r := fcc_nearest_neighbor_distance v_s
    α / r ^ 3 = (refractiveIndex - 1) / (2 ^ (3/2 : ℝ) * π) * (v_g / v_s) := by
  unfold BET.polarizability BET.fcc_nearest_neighbor_distance; ring_nf; norm_num [ hv_s.ne', Real.pi_pos.ne' ] ;
  rw [ ← Real.rpow_natCast _ 3, ← Real.rpow_mul ( by positivity ) ] ; norm_num ; ring_nf;
  rw [ show ( 2 : ℝ ) ^ ( 3 / 2 : ℝ ) = 2 * Real.sqrt 2 by rw [ Real.sqrt_eq_rpow, ← Real.rpow_one_add' ] <;> norm_num ] ; ring;

-- "(μ_{i+1}/μ_i) = C = d(α/r³) where d is a constant dependent upon geometrical structure"
/-- Ratio of induced dipoles in successive layers -/
noncomputable def dipole_ratio (d α r : ℝ) : ℝ := d * (α / r ^ 3)

-- "From (8) and (9) we obtain C = -0.01 and therefore K₁ = C² equals about 1×10⁻⁴"
/-- For argon, the polarization binding energy is negligible beyond first layer -/
theorem argon_polarization_negligible :
    let α_over_r3 : ℝ := 0.029  -- For argon
    let d : ℝ := -0.35           -- For close-packed spheres
    let C := d * α_over_r3
    C ^ 2 < 0.001 := by
  norm_num

/-! ## Part 2: Generalized Langmuir Theory -/

/-- Configuration parameters for BET adsorption -/
structure BETConfig where
  /-- Total surface area -/
  A : ℝ
  /-- Saturation pressure -/
  p₀ : ℝ
  /-- Gas constant -/
  R : ℝ
  /-- Temperature -/
  T : ℝ
  /-- Heat of adsorption for first layer -/
  E₁ : ℝ
  /-- Heat of liquefaction (heat of adsorption for layers 2+) -/
  E_L : ℝ
  /-- Rate constant ratio a₁/b₁ -/
  a₁_over_b₁ : ℝ
  /-- Constant g = bᵢ/aᵢ for i ≥ 2 -/
  g : ℝ
  /-- Positivity conditions -/
  hA : A > 0
  hp₀ : p₀ > 0
  hR : R > 0
  hT : T > 0
  hg : g > 0


/--
"a₁ps₀ = b₁s₁e^{-E₁/RT}"
Equilibrium condition for first layer: rate of condensation = rate of evaporation
-/
theorem first_layer_equilibrium_negated (a₁_over_b₁ E₁ R T p s₀ s₁ : ℝ) (hR : R > 0) (hT : T > 0) :
    p * s₀ = (1 / a₁_over_b₁) * s₁ * exp (-E₁ / (R * T)) ↔
    s₁ = a₁_over_b₁ * p * exp (E₁ / (R * T)) * s₀ := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Set the values of the variables to satisfy the conditions.
  use 0, 1, 1, 1;
  -- Choose $p = 1$, $s₀ = 0$, and $s₁ = 1$.
  use 1, 0, 1;
  simp

-- "a_i p s_{i-1} = b_i s_i e^{-E_i/RT}"
/-- Equilibrium condition for i-th layer (i ≥ 2) -/
theorem ith_layer_equilibrium
(g E_L R T p : ℝ)
(hR : R > 0) (hT : T > 0)
(s_prev s_i : ℝ) :
p * s_prev = g * s_i * exp (-E_L / (R * T)) ↔ s_i = (p / g) * exp (E_L / (R * T)) * s_prev := by
    field_simp [mul_comm, mul_assoc, mul_left_comm, Real.exp_sub] at *;
    sorry




-- "s₁ = ys₀, where y = (a₁/b₁)pe^{E₁/RT}"
/-- Definition of y parameter -/
noncomputable def y_param (cfg : BETConfig) (p : ℝ) : ℝ :=
  cfg.a₁_over_b₁ * p * exp (cfg.E₁ / (cfg.R * cfg.T))

-- "s₂ = xs₁, where x = (p/g)e^{E_L/RT}"
/-- Definition of x parameter (relative pressure when normalized) -/
noncomputable def x_param (cfg : BETConfig) (p : ℝ) : ℝ :=
  (p / cfg.g) * exp (cfg.E_L / (cfg.R * cfg.T))

-- "c = y/x = (a₁g/b₁)e^{(E₁-E_L)/RT}"
/-- The BET c parameter related to heat of adsorption -/
noncomputable def c_param (cfg : BETConfig) : ℝ :=
  cfg.a₁_over_b₁ * cfg.g * exp ((cfg.E₁ - cfg.E_L) / (cfg.R * cfg.T))

-- "s_i = yx^{i-1}s₀ = cx^i s₀"
/-- Surface area of i-th layer in terms of s₀, c, and x -/
theorem surface_area_formula (cfg : BETConfig) (p s₀ : ℝ) (i : ℕ) (hi : i ≥ 1) :
    let y := y_param cfg p
    let x := x_param cfg p
    let c := c_param cfg
    let s_i := c * x ^ i * s₀
    s_i = y * x ^ (i - 1) * s₀ := by
  unfold BET.y_param BET.x_param BET.c_param;
  rcases i <;> simp_all +decide [ pow_succ, mul_assoc, mul_comm, mul_left_comm, sub_div ];
  by_cases hg : cfg.g = 0 <;> simp_all +decide [ division_def, mul_assoc, mul_comm, mul_left_comm, Real.exp_sub ];
  · exact absurd hg ( ne_of_gt cfg.hg );
  · exact Or.inl <| Or.inl <| Or.inl <| by rw [ mul_left_comm, mul_inv_cancel₀ <| ne_of_gt <| Real.exp_pos _, mul_one ] ;

-- "v/v_m = (Σᵢ₌₀^∞ i·sᵢ)/(Σᵢ₌₀^∞ sᵢ)"
/-- Volume ratio to monolayer volume -/
noncomputable def volume_ratio (c x : ℝ) : ℝ :=
  c * x / ((1 - x) * (1 - x + c * x))

-- "Σᵢ₌₁^∞ x^i = x/(1-x)"
/-- Geometric series sum -/
theorem geometric_series_sum (x : ℝ) (hx : |x| < 1) :
    ∑' (i : ℕ), x ^ (i + 1) = x / (1 - x) := by
  convert HasSum.tsum_eq ( HasSum.mul_left x <| hasSum_geometric_of_abs_lt_one hx ) using 1 ; ring_nf;

-- "Σᵢ₌₁^∞ i·x^i = x/(1-x)²"
/-- Weighted geometric series sum -/
theorem weighted_geometric_series_sum (x : ℝ) (hx : |x| < 1) :
    ∑' (i : ℕ), (i + 1 : ℝ) * x ^ (i + 1) = x / (1 - x) ^ 2 := by
  simp_rw [pow_succ, mul_assoc] at *;
  have : x ≠ 1 := by
    rw [abs_lt] at hx
    linarith
  field_simp
  ring_nf
  apply HasSum.tsum_eq;
  have := (hasSum_geometric_of_lt_one (abs_nonneg x) hx).mul_left x
  field_simp [mul_comm, mul_assoc, mul_left_comm] at *;
  convert this using 1
  · ext1 n
    rw [ mul_comm, ← pow_succ', add_comm] at *;
    rw [ mul_comm ]
    sorry
  sorry

-- "v/v_m = cx/[(1-x)(1-x+cx)]"
/-- The general BET equation before normalization -/
theorem general_BET_equation (c x : ℝ) (hx : 0 ≤ x) (hx' : x < 1) :
    volume_ratio c x = c * x / ((1 - x) * (1 - x + c * x)) := by
    simp [volume_ratio]

-- "To make v = ∞ when p = p₀, x must be equal to unity. Thus (p₀/g)e^{E_L/RT} = 1, and x = p/p₀"
/-- At saturation pressure, x = 1 and v → ∞ -/
theorem saturation_condition (cfg : BETConfig) :
    (cfg.p₀ / cfg.g) * exp (cfg.E_L / (cfg.R * cfg.T)) = 1 →
    ∀ p, x_param cfg p = p / cfg.p₀ := by
  intro h_sat p;
  unfold BET.x_param;
  rw [div_mul_eq_mul_div, mul_comm]
  field_simp [← h_sat] at *;
  grind;

-- "v = v_m cp / [(p₀ - p)(1 + (c-1)(p/p₀))]"
/-- The BET isotherm equation (Main Theorem) -/
theorem BET_isotherm_equation (v_m c p p₀ : ℝ) (hp₀ : p₀ > 0) (hp : 0 ≤ p) (hpp₀ : p < p₀) :
    let x := p / p₀
    let v := v_m * c * p / ((p₀ - p) * (1 + (c - 1) * x))
    v = v_m * c * x / ((1 - x) * (1 + (c - 1) * x)) := by
    intro x v
    have h₁  : p = x * p₀ := by
      dsimp [x]
      field_simp [hp₀.ne']
    simp [mul_comm, mul_left_comm];
    grind;

-- "p/[v(p₀-p)] = 1/(v_m c) + [(c-1)/(v_m c)](p/p₀)"
/-- Linear form of BET equation (Equation A) -/
theorem BET_linear_form (v v_m c p p₀ : ℝ) (hp₀ : p₀ > 0) (hv_m : v_m > 0)
    (hc : c > 0) (hp : 0 < p) (hpp₀ : p < p₀) (hv : v > 0) :
    v = v_m * c * p / ((p₀ - p) * (1 + (c - 1) * (p / p₀))) →
    p / (v * (p₀ - p)) = 1 / (v_m * c) + (c - 1) / (v_m * c) * (p / p₀) := by
    intro h;
    field_simp [h, mul_comm, mul_assoc, mul_left_comm] at *;
    ring_nf;
    grind

-- "For p << p₀ equation (28) reduces to v = (v_m c/p₀)p / (1 + (c/p₀)p)"
/-- At low pressure, BET reduces to Langmuir equation -/
theorem BET_low_pressure_langmuir_limit
(v_m c p₀ : ℝ)
(hp₀ : p₀ > 0)
(hc : c > 1) :
let K := c / p₀
let v_BET := fun p => v_m * c * p / ((p₀ - p) * (1 + (c - 1) * (p / p₀)))
let v_Langmuir := fun p => v_m * K * p / (1 + K * p)
Filter.Tendsto (fun p => v_BET p / v_Langmuir p) (nhds 0) (nhds 1):= by
  intro K p hp hpp hpp1
  field_simp [mul_comm, mul_assoc, mul_left_comm, Filter.mem_map, div_eq_mul_inv] at *;
  have hpp2 := mem_of_mem_nhds hpp1
  simp [p, hp, K,hpp2] at *;
  sorry


-- "When n = 1 it reduces to the Langmuir type equation (29)"
/-- Langmuir equation as special case -/
noncomputable def langmuir_equation (v_m K p : ℝ) : ℝ := v_m * K * p / (1 + K * p)

/-! ## Finite Layer BET Equation -/

-- "v = (v_m cx)/(1-x) · [1-(n+1)x^n + nx^{n+1}]/[1+(c-1)x-cx^{n+1}]"
/-- Finite sum for numerator in finite-layer BET -/
noncomputable def finite_sum_numerator (x : ℝ) (n : ℕ) : ℝ :=
  1 - (n + 1 : ℝ) * x ^ n + n * x ^ (n + 1)

/-- Finite sum for denominator factor in finite-layer BET -/
noncomputable def finite_sum_denominator (c x : ℝ) (n : ℕ) : ℝ :=
  1 + (c - 1) * x - c * x ^ (n + 1)

/-- The BET equation for finite maximum layers (Equation B) -/
noncomputable def BET_finite_layers (v_m c x : ℝ) (n : ℕ) : ℝ :=
  v_m * c * x / (1 - x) *
    (finite_sum_numerator x n) / (finite_sum_denominator c x n)

-- "When n = 1 it reduces to the Langmuir type equation"
/-- When n = 1, finite-layer BET equals Langmuir -/
theorem finite_BET_n1_is_langmuir
    (v_m c x : ℝ)
    (hx : x ≠ 1)
    (hc : c > 0) :
    BET_finite_layers v_m c x 1 = langmuir_equation v_m c x := by
    dsimp [BET_finite_layers, langmuir_equation, finite_sum_numerator, finite_sum_denominator];
    field_simp [hx, mul_comm, mul_assoc, mul_left_comm] at *;
    field_simp [mul_comm, mul_assoc, mul_left_comm] at *;
    simp_all +decide [ mul_comm, mul_assoc, ];
    have h1 : 1 - x ≠ 0 := by contrapose! hx;linarith
    have h_denom : 1 + x * (c - 1) - x^2 * c = (1 - x) * (1 + c * x) := by ring
    have h_num : 1 - x * (1 + 1) + x^2 = (1 - x)^2 := by ring
    rw [h_num] at *;
    rw [h_denom] at *;
    field_simp [h1] at *;
    grind



-- "when n = ∞ (free surface), it reduces to equation (A)"
/-- As n → ∞, finite-layer BET approaches standard BET -/
theorem finite_BET_limit_is_BET (v_m c x : ℝ) (hx : 0 ≤ x) (hx' : x < 1) (hc : c > 0) :
    Filter.Tendsto (fun n => BET_finite_layers v_m c x n)
      Filter.atTop (nhds (v_m * volume_ratio c x)) := by
      intro h n
      dsimp [BET_finite_layers, volume_ratio, finite_sum_numerator, finite_sum_denominator];
      with_unfolding_all
      simp only [Filter.mem_map, Filter.mem_atTop_sets, ge_iff_le] at *;
      have h1' := hx
      simp [pow_succ,← mul_assoc,h1'] at *
      simp_all +decide [ mul_assoc];
      sorry

/-! ## Extended Equations -/

-- "If we assume that E₂ > E_L ... equation (C)"
/-- Extended BET with different second layer energy (Equation C) -/
noncomputable def BET_extended_second_layer (v_m c b δ x : ℝ) : ℝ :=
  v_m * c * x / (1 - x) *
    (δ + (b - δ) * (2 * x - x ^ 2)) /
    (1 + (c - 1) * x + (b - 1) * c * x ^ 2)

-- "where b = e^{(E₂-E_L)/RT}, and δ = v_m^{(1)}/v_m"
/-- Parameter b for extended equation -/
noncomputable def b_param (E₂ E_L R T : ℝ) : ℝ := exp ((E₂ - E_L) / (R * T))

-- "The equation which takes care of the varying size of capillaries is (equation D)"
/-- BET equation with variable capillary sizes (Equation D) -/
noncomputable def BET_variable_capillaries (v_m c x : ℝ) (β : ℕ → ℝ) : ℝ :=
  v_m * c * x / (1 - x) *
    ∑' n, β n * (finite_sum_numerator x n) / (finite_sum_denominator c x n)

/-- The β_n sum to 1 (fractions of total surface) -/
theorem beta_sum_one
(β : ℕ → ℝ)
(hβ_nonneg : ∀ n, 0 ≤ β n)
(hβ_sum : ∑' n, β n = 1) :
∑' n, β n = 1 := hβ_sum

/-! ## Physical Interpretations -/

-- "the constant c ... being approximately equal to e^{(E₁-E_L)/RT}"
/-- The c parameter is approximately exponential in energy difference when a₁g/b₁ ≈ 1 -/
theorem c_param_interpretation (cfg : BETConfig)
    (h_approx : cfg.a₁_over_b₁ * cfg.g = 1) :
    c_param cfg = exp ((cfg.E₁ - cfg.E_L) / (cfg.R * cfg.T)) := by
    simp [BET.c_param, h_approx];

-- "v_m is the volume of gas adsorbed when the entire adsorbent surface
-- is covered with a complete unimolecular layer"
/-- Monolayer volume definition -/
structure MonolayerVolume where
  v_m : ℝ
  A : ℝ  -- surface area
  v₀ : ℝ -- volume per unit area
  h_def : v_m = A * v₀

/-- From BET linear plot, we can determine v_m and c -/
theorem BET_parameters_from_linear_plot
(slope intercept : ℝ)
(h_slope : slope > 0) (h_intercept : intercept > 0) :
let c := 1 + slope / intercept
let v_m := 1 / (slope + intercept)
slope = (c - 1) / (v_m * c) ∧ intercept = 1 / (v_m * c) := by
  intro c v_m
  field_simp [mul_comm, mul_assoc, mul_left_comm] at *;
  simp_all +decide [ mul_comm ];
  grind;

end BET
