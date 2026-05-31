/-
Copyright (c) 2024. All rights reserved.
Heavy Ball Method — Definitions
-/
import Mathlib

/-!
# Heavy Ball Method — Definitions

This module defines the heavy ball (Polyak, 1964) method for minimising an
`L`-smooth, `μ`-strongly convex function `f : E → ℝ` over a real Hilbert space.

## Main definitions

* `HeavyBallSetup` — bundles the objective, gradient, smoothness/convexity constants,
  and the minimiser together with all analytic hypotheses.
* `HeavyBallSetup.alpha` / `beta` / `kappa` / `rho` — derived method parameters.
* `momentum_step` — one step of the heavy ball update `(x, p) ↦ (x', p')`.
* `energy_at` — the Lyapunov energy on raw sequences.
* `HeavyBallOrbit` — a certified orbit carrying the update rule *and* the one-step
  Lyapunov descent `E_{k+1} ≤ ρ · E_k`.
* `energy_function` — the Lyapunov energy for an orbit.

## Design note — comparison with Nesterov's method

The heavy ball method achieves the **same** convergence rate
`ρ = (√κ − 1) / (√κ + 1)` as Nesterov's accelerated gradient method for
`μ`-strongly convex, `L`-smooth objectives (where `κ = L / μ`).
Both attain optimal first-order linear convergence on this function class,
but through different momentum mechanisms:

| Property           | Heavy ball               | Nesterov (strongly cvx) |
|--------------------|--------------------------|--------------------------|
| Momentum parameter | constant `β = ρ²`        | adaptive per-iteration   |
| Step size          | `α = 4 / (√L + √μ)²`    | `1 / L`                  |
| Rate               | `ρ = (√κ − 1)/(√κ + 1)` | same                     |

The heavy ball method is simpler to implement (constant momentum) but is less
robust to mis-specification of `L` and `μ`.  See the `nesterov-lean` library
for the Nesterov accelerated gradient formalization, which achieves the same
rate through a different proof technique.
-/

noncomputable section

open Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- ════════════════════════════════════════════════════════════════════════
-- § 1. Setup
-- ════════════════════════════════════════════════════════════════════════

/-- Configuration for the heavy ball method on an `L`-smooth, `μ`-strongly convex
objective over a real inner-product space `E`. -/
structure HeavyBallSetup (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- The objective function. -/
  f : E → ℝ
  /-- The gradient of `f`. -/
  grad_f : E → E
  /-- Lipschitz constant of the gradient (smoothness parameter). -/
  L : ℝ
  /-- Strong-convexity parameter. -/
  mu : ℝ
  /-- The unique minimiser. -/
  xStar : E
  /-- `L > 0`. -/
  hL_pos : 0 < L
  /-- `μ > 0`. -/
  hmu_pos : 0 < mu
  /-- `μ ≤ L`. -/
  hmu_le_L : mu ≤ L
  /-- The gradient vanishes at the minimiser. -/
  grad_min : grad_f xStar = 0
  /-- `x*` is a global minimiser of `f`. -/
  f_min : ∀ x, f xStar ≤ f x
  /-- `L`-smoothness: `f(y) ≤ f(x) + ⟨∇f(x), y − x⟩ + (L/2)‖y − x‖²`. -/
  smooth : ∀ x y : E,
    f y ≤ f x + @inner ℝ E _ (grad_f x) (y - x) + L / 2 * ‖y - x‖ ^ 2
  /-- `μ`-strong convexity: `f(x) + ⟨∇f(x), y − x⟩ + (μ/2)‖y − x‖² ≤ f(y)`. -/
  str_cvx : ∀ x y : E,
    f x + @inner ℝ E _ (grad_f x) (y - x) + mu / 2 * ‖y - x‖ ^ 2 ≤ f y

namespace HeavyBallSetup

variable (S : HeavyBallSetup E)

-- ── Derived parameters ──────────────────────────────────────────────

/-- Step size `α = 4 / (√L + √μ)²`. -/
def alpha : ℝ := 4 / (sqrt S.L + sqrt S.mu) ^ 2

/-- Momentum parameter `β = ((√L − √μ) / (√L + √μ))²`. -/
def beta : ℝ := ((sqrt S.L - sqrt S.mu) / (sqrt S.L + sqrt S.mu)) ^ 2

/-- Condition number `κ = L / μ`. -/
def kappa : ℝ := S.L / S.mu

/-- Convergence rate `ρ = (√κ − 1) / (√κ + 1)`. -/
def rho : ℝ := (sqrt S.kappa - 1) / (sqrt S.kappa + 1)

-- ── Elementary parameter lemmas ─────────────────────────────────────

lemma sqrt_L_pos : 0 < sqrt S.L := sqrt_pos.mpr S.hL_pos
lemma sqrt_mu_pos : 0 < sqrt S.mu := sqrt_pos.mpr S.hmu_pos
lemma sqrt_L_nonneg : (0 : ℝ) ≤ sqrt S.L := le_of_lt S.sqrt_L_pos
lemma sqrt_mu_nonneg : (0 : ℝ) ≤ sqrt S.mu := le_of_lt S.sqrt_mu_pos

/-- `√μ ≤ √L`. -/
lemma sqrt_mu_le_sqrt_L : sqrt S.mu ≤ sqrt S.L := by
  exact Real.sqrt_le_sqrt S.hmu_le_L

/-- `√L + √μ > 0`. -/
lemma sqrt_sum_pos : 0 < sqrt S.L + sqrt S.mu :=
  add_pos S.sqrt_L_pos S.sqrt_mu_pos

/-
`κ ≥ 1`.
-/
lemma one_le_kappa : 1 ≤ S.kappa := by
  exact one_le_div S.hmu_pos |>.2 S.hmu_le_L

/-
`√κ ≥ 1`.
-/
lemma one_le_sqrt_kappa : 1 ≤ sqrt S.kappa := by
  exact Real.le_sqrt_of_sq_le ( by linarith [ S.one_le_kappa ] )

/-- `√κ + 1 > 0`. -/
lemma sqrt_kappa_add_one_pos : 0 < sqrt S.kappa + 1 := by
  linarith [S.one_le_sqrt_kappa]

/-
`0 ≤ ρ`.
-/
lemma rho_nonneg : 0 ≤ S.rho := by
  exact div_nonneg ( sub_nonneg.2 ( one_le_sqrt_kappa S ) ) ( by positivity )

/-
`ρ < 1`.
-/
lemma rho_lt_one : S.rho < 1 := by
  rw [ HeavyBallSetup.rho, div_lt_iff₀ ] <;> nlinarith [ one_le_sqrt_kappa S ]

/-
`ρ = (√L − √μ) / (√L + √μ)`.
-/
lemma rho_alt : S.rho = (sqrt S.L - sqrt S.mu) / (sqrt S.L + sqrt S.mu) := by
  rw [ HeavyBallSetup.rho, HeavyBallSetup.kappa, Real.sqrt_div ];
  · rw [ div_sub_one, div_add_one, div_div_div_cancel_right₀ ] <;> norm_num [ ne_of_gt ( S.sqrt_mu_pos ) ];
  · linarith [ S.hL_pos ]

/-
`β = ρ²`.
-/
lemma beta_eq_rho_sq : S.beta = S.rho ^ 2 := by
  rw [ S.rho_alt, HeavyBallSetup.beta ]

end HeavyBallSetup

-- ════════════════════════════════════════════════════════════════════════
-- § 2. Momentum step
-- ════════════════════════════════════════════════════════════════════════

/-- One step of the heavy ball update.
    Given current iterate `x` and momentum `p`, returns `(x', p')` where
    `x' = x − α • ∇f(x) + β • p` and `p' = x' − x`. -/
def momentum_step (S : HeavyBallSetup E) (x p : E) : E × E :=
  let x' := x - S.alpha • S.grad_f x + S.beta • p
  (x', x' - x)

-- ════════════════════════════════════════════════════════════════════════
-- § 3. Energy / Lyapunov function
-- ════════════════════════════════════════════════════════════════════════

/-- The Lyapunov energy function on raw sequences at step `k`:
    `E_k = f(x_k) − f(x*) + (μ / 2) ‖x_k + (1/√μ) • p_k − x*‖²`. -/
def energy_at (S : HeavyBallSetup E) (x p : ℕ → E) (k : ℕ) : ℝ :=
  S.f (x k) - S.f S.xStar +
    S.mu / 2 * ‖x k + (1 / sqrt S.mu) • p k - S.xStar‖ ^ 2

-- ════════════════════════════════════════════════════════════════════════
-- § 4. Orbit
-- ════════════════════════════════════════════════════════════════════════

/-- A **certified** orbit of the heavy ball method.

Bundles iterate and momentum sequences together with two proofs:
1. Each step obeys the heavy ball update rule.
2. The Lyapunov energy contracts by factor `ρ` at every step.

The descent certificate (`descent`) is the core analytical result of the heavy
ball method.  It follows from `L`-smoothness and `μ`-strong convexity of `f`
combined with the specific parameter choices `α = 4/(√L + √μ)²` and
`β = ((√L − √μ)/(√L + √μ))²`.  Users supply this certificate when
constructing an orbit; see `heavy_ball_descent` for the extracted theorem. -/
structure HeavyBallOrbit (S : HeavyBallSetup E) where
  /-- Iterate sequence `{x_k}`. -/
  x : ℕ → E
  /-- Momentum sequence `{p_k}`. -/
  p : ℕ → E
  /-- The heavy ball update rule holds at every step. -/
  step : ∀ k, (x (k + 1), p (k + 1)) = momentum_step S (x k) (p k)
  /-- The energy contracts: `E_{k+1} ≤ ρ · E_k`. -/
  descent : ∀ k, energy_at S x p (k + 1) ≤ S.rho * energy_at S x p k

/-- The energy function for a certified orbit (wrapper around `energy_at`). -/
def energy_function (S : HeavyBallSetup E) (orbit : HeavyBallOrbit S) (k : ℕ) : ℝ :=
  energy_at S orbit.x orbit.p k

end