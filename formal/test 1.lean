import Mathlib


-- Physical constants and parameters for BET theory
variable (s₀ : ℝ)

-- surface area of zeroth layer
variable (E₁ E_L R T : ℝ)

-- activation energies, gas constant, temperature
variable (a₁ b₁ g : ℝ)

-- fitted constants
variable (P P₀ V₀ : ℝ)

-- pressure, saturation pressure, monolayer volume

-- Derived constants
noncomputable def C_L (E_L R T g : ℝ) : ℝ := Real.exp (E_L / (R * T)) / g

noncomputable def C₁ (a₁ b₁ E₁ R T : ℝ) : ℝ := (a₁ / b₁) * Real.exp (E₁ / (R * T))

-- BET parameters
noncomputable def x (P : ℝ) (E_L R T g : ℝ) : ℝ := P * C_L E_L R T g

noncomputable def y (P : ℝ) (a₁ b₁ E₁ R T : ℝ) : ℝ := P * C₁ a₁ b₁ E₁ R T

noncomputable def C (P : ℝ) (a₁ b₁ E₁ E_L R T g : ℝ) : ℝ :=
  y P a₁ b₁ E₁ R T / x P E_L R T g

-- Surface area of i-th layer
noncomputable def s_i (i : ℕ) (s₀ : ℝ) (P : ℝ) (a₁ b₁ E₁ E_L R T g : ℝ) : ℝ :=
  if i = 0 then s₀
  else C P a₁ b₁ E₁ E_L R T g * (x P E_L R T g)^i * s₀

-- Total catalyst surface area
noncomputable def A (s₀ : ℝ) (P : ℝ) (a₁ b₁ E₁ E_L R T g : ℝ) : ℝ :=
  s₀ * (1 + C P a₁ b₁ E₁ E_L R T g * ∑' i : ℕ, (x P E_L R T g)^(i+1))

-- Volume adsorbed
noncomputable def V (s₀ V₀ : ℝ) (P : ℝ) (a₁ b₁ E₁ E_L R T g : ℝ) : ℝ :=
  C P a₁ b₁ E₁ E_L R T g * s₀ * V₀ * ∑' i : ℕ, (i+1 : ℝ) * (x P E_L R T g)^(i+1)

-- BET equation (main result)
noncomputable def BET_equation (s₀ V₀ : ℝ) (P : ℝ) (a₁ b₁ E₁ E_L R T g : ℝ) : ℝ :=
  V s₀ V₀ P a₁ b₁ E₁ E_L R T g / (A s₀ P a₁ b₁ E₁ E_L R T g * V₀)

-- Simplified BET equation
noncomputable def BET_simplified (P P₀ : ℝ) (a₁ b₁ E₁ E_L R T g : ℝ) : ℝ :=
  (C P a₁ b₁ E₁ E_L R T g * P) / ((P₀ - P) * (1 + (C P a₁ b₁ E₁ E_L R T g - 1) * (P / P₀)))

-- Alternative form using geometric series directly
noncomputable def BET_series_form (s₀ : ℝ) (P : ℝ) (a₁ b₁ E₁ E_L R T g : ℝ) : ℝ :=
  (C P a₁ b₁ E₁ E_L R T g * s₀ * ∑' i : ℕ, (i+1 : ℝ) * (x P E_L R T g)^(i+1)) /
  (s₀ * (1 + C P a₁ b₁ E₁ E_L R T g * ∑' i : ℕ, (x P E_L R T g)^(i+1)))

-- Main theorem: BET equation derivation
theorem BET_derivation (s₀ V₀ P P₀ a₁ b₁ E₁ E_L R T g : ℝ)
  (h₁ : s₀ > 0) (h₂ : V₀ > 0) (h₃ : P > 0) (h₄ : P₀ > 0) (h₅ : P < P₀)
  (h₆ : R > 0) (h₇ : T > 0) (h₈ : g > 0) (h₉ : a₁ > 0) (h₁₀ : b₁ > 0)
  (h₁₁ : abs (x P E_L R T g) < 1) -- convergence condition
  (h₁₂ : P₀ = 1 / C_L E_L R T g) -- saturation pressure relation
  : BET_equation s₀ V₀ P a₁ b₁ E₁ E_L R T g = BET_simplified P P₀ a₁ b₁ E₁ E_L R T g := by
  unfold BET_equation BET_simplified;
  aesop;
  -- Let's simplify the expression for the BET equation.
  have h_sum : ∑' i : ℕ, (i + 1) * (x P E_L R T g) ^ (i + 1) = (x P E_L R T g) / (1 - x P E_L R T g) ^ 2 ∧ ∑' i : ℕ, (x P E_L R T g) ^ (i + 1) = (x P E_L R T g) / (1 - x P E_L R T g) := by
    -- Apply the known formulas for the sums of geometric series and their derivatives.
    have h_geo_series : ∑' i : ℕ, (i + 1) * (x P E_L R T g) ^ i = 1 / (1 - x P E_L R T g) ^ 2 := by
      -- Apply the formula for the sum of a geometric series and its derivative.
      have h_geo_series : ∑' i : ℕ, (i + 1) * (x P E_L R T g) ^ i = (∑' i : ℕ, (i : ℝ) * (x P E_L R T g) ^ i) + (∑' i : ℕ, (x P E_L R T g) ^ i) := by
        rw [ ← Summable.tsum_add ] ; congr ; ext i ; ring;
        · refine' summable_of_ratio_norm_eventually_le _ _;
          exact ( 1 + |x P E_L R T g| ) / 2;
          · linarith;
          · norm_num [ pow_succ, mul_assoc ];
            refine' ⟨ ⌈ ( 1 + |x P E_L R T g| ) / ( 1 - |x P E_L R T g| ) ⌉₊ + 1, fun n hn => _ ⟩ ; rw [ abs_of_nonneg ( by positivity : 0 ≤ ( n : ℝ ) + 1 ) ] ; nlinarith [ Nat.le_ceil ( ( 1 + |x P E_L R T g| ) / ( 1 - |x P E_L R T g| ) ), show ( n : ℝ ) ≥ ⌈ ( 1 + |x P E_L R T g| ) / ( 1 - |x P E_L R T g| ) ⌉₊ + 1 by exact_mod_cast hn, abs_nonneg ( x P E_L R T g ), pow_nonneg ( abs_nonneg ( x P E_L R T g ) ) n, mul_le_mul_of_nonneg_right ( show ( |x P E_L R T g| : ℝ ) ≤ 1 by linarith [ abs_nonneg ( x P E_L R T g ) ] ) ( pow_nonneg ( abs_nonneg ( x P E_L R T g ) ) n ), mul_div_cancel₀ ( 1 + |x P E_L R T g| ) ( by linarith [ abs_nonneg ( x P E_L R T g ) ] : ( 1 - |x P E_L R T g| ) ≠ 0 ) ];
        · exact summable_geometric_of_abs_lt_one h₁₁;
      have h_geo_series_deriv : ∑' i : ℕ, (i : ℝ) * (x P E_L R T g) ^ i = x P E_L R T g / (1 - x P E_L R T g) ^ 2 := by
        have h_geo_series_deriv : ∀ r : ℝ, |r| < 1 → ∑' i : ℕ, (i : ℝ) * r ^ i = r / (1 - r) ^ 2 := by
          exact fun r a ↦ tsum_coe_mul_geometric_of_norm_lt_one a;
        exact h_geo_series_deriv _ h₁₁;
      rw [ h_geo_series, h_geo_series_deriv, tsum_geometric_of_abs_lt_one h₁₁ ];
      grind;
    exact ⟨ by rw [ show ( ∑' i : ℕ, ( ( i : ℝ ) + 1 ) * x P E_L R T g ^ ( i + 1 ) ) = x P E_L R T g * ( ∑' i : ℕ, ( ( i : ℝ ) + 1 ) * x P E_L R T g ^ i ) by rw [ ← tsum_mul_left ] ; exact tsum_congr fun i => by ring ] ; rw [ h_geo_series ] ; ring, by rw [ show ( ∑' i : ℕ, x P E_L R T g ^ ( i + 1 ) ) = x P E_L R T g * ( ∑' i : ℕ, ( x P E_L R T g ) ^ i ) by rw [ ← tsum_mul_left ] ; exact tsum_congr fun i => by ring, tsum_geometric_of_abs_lt_one h₁₁ ] ; ring ⟩;
  unfold A V at * ; aesop;
  unfold x; ring_nf;
  field_simp;
  grind

-- Theorem: Series form equals main BET equation
theorem BET_series_equivalence (s₀ V₀ P a₁ b₁ E₁ E_L R T g : ℝ)
  (h₁ : s₀ > 0) (h₂ : V₀ > 0) (h₃ : P > 0)
  (h₄ : R > 0) (h₅ : T > 0) (h₆ : g > 0) (h₇ : a₁ > 0) (h₈ : b₁ > 0)
  (h₉ : abs (x P E_L R T g) < 1) -- convergence condition
  : BET_equation s₀ V₀ P a₁ b₁ E₁ E_L R T g = BET_series_form s₀ P a₁ b₁ E₁ E_L R T g := by
  unfold BET_equation BET_series_form;
  unfold V A C x; ring_nf;
  grind

-- Auxiliary lemma: geometric series convergence
lemma geometric_series_summable (x : ℝ) (hx : abs x < 1) :
  Summable (fun n : ℕ => x^(n+1)) := by
  simpa only [ pow_succ' ] using Summable.mul_left _ ( summable_geometric_of_abs_lt_one hx )

-- Auxiliary lemma: weighted geometric series
lemma weighted_geometric_series (x : ℝ) (hx : abs x < 1) :
  ∑' n : ℕ, (n+1 : ℝ) * x^(n+1) = x / (1 - x)^2 := by
  -- Recognize that this is a geometric series with the common ratio $x$ and first term $x$.
  have h_geo_series : ∑' (n : ℕ), (n + 1) * x ^ n = 1 / (1 - x) ^ 2 := by
    -- We'll use the fact that if the series $\sum_{n=0}^{\infty} a_n x^n$ converges to $f(x)$, then $\sum_{n=0}^{\infty} (n+1) a_n x^n$ converges to $f'(x)$.
    have h_deriv : HasSum (fun n : ℕ => (n + 1) * x ^ n) (1 / (1 - x) ^ 2) := by
      have h_sum : HasSum (fun n : ℕ => (n : ℝ) * x ^ n) (x / (1 - x) ^ 2) := by
        exact hasSum_coe_mul_geometric_of_norm_lt_one hx;
      convert HasSum.add ( hasSum_geometric_of_abs_lt_one hx ) h_sum using 1 <;> ring;
      · exact funext fun n => by ring;
      · nlinarith [ abs_lt.mp hx, inv_mul_cancel₀ ( by nlinarith [ abs_lt.mp hx ] : ( 1 - x * 2 + x ^ 2 ) ≠ 0 ), inv_mul_cancel₀ ( by nlinarith [ abs_lt.mp hx ] : ( 1 - x ) ≠ 0 ) ];
    exact h_deriv.tsum_eq;
  convert congr_arg ( · * x ) h_geo_series using 1 <;> ring;
  rw [ ← tsum_mul_left ] ; congr ; ext n ; ring

-- Auxiliary lemma: simple geometric series
lemma simple_geometric_series (x : ℝ) (hx : abs x < 1) :
  ∑' n : ℕ, x^(n+1) = x / (1 - x) := by
  ring_nf;
  rw [ tsum_mul_left, tsum_geometric_of_abs_lt_one hx ]

-- Lemma: BET main mathematical identity
lemma BET_main_math (x C : ℝ) (hx : abs x < 1) (hC : C > 0) :
  (C * ∑' i : ℕ, (i+1 : ℝ) * x^(i+1)) / (1 + C * ∑' i : ℕ, x^(i+1)) =
  (C * x) / ((1 - x) * (1 - x + C * x)) := by
  -- Using the results of the geometric series sums, we can simplify the expression.
  have h_simp : (C * (x / (1 - x)^2)) / (1 + C * (x / (1 - x))) = (C * x) / ((1 - x) * (1 - x + C * x)) := by
    grind +ring;
  convert h_simp using 4;
  · exact weighted_geometric_series x hx;
  · exact simple_geometric_series x hx
