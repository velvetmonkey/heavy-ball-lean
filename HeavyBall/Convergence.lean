/-
Copyright (c) 2024. All rights reserved.
Heavy Ball Method — Convergence
-/
import HeavyBall.Descent

/-!
# Heavy Ball Method — Linear Convergence

This module proves the main convergence theorem for the heavy ball method:
the function-value gap `f(x_k) − f*` decays geometrically with rate
`ρ = (√κ − 1) / (√κ + 1) < 1`, where `κ = L / μ` is the condition number.

## Main results

* `fval_le_energy` — `f(x_k) − f(x*) ≤ E_k` for every `k`.
* `heavy_ball_convergence` — `f(x_k) − f(x*) ≤ E_0 · ρ^k`.

## Comparison with Nesterov's method

Both the heavy ball method and Nesterov's accelerated gradient achieve
convergence rate `ρ = (√κ − 1)/(√κ + 1)` for `μ`-strongly convex, `L`-smooth
objectives.  This is **optimal** among first-order methods on this class.

The heavy ball method uses a **constant** momentum `β = ρ²` and step size
`α = 4/(√L + √μ)²`, while Nesterov's method uses **adaptive** momentum that
varies at each iteration.

Key differences:
- Heavy ball is simpler to implement (two constant hyper-parameters).
- Nesterov's method extends more naturally to the non-strongly-convex case
  (achieving `O(1/k²)` rates) and is generally more robust.
- The heavy ball Lyapunov analysis is specific to the strongly convex regime.

See `nesterov-lean` for the Nesterov accelerated gradient formalization.
-/

noncomputable section

open Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {S : HeavyBallSetup E} (orbit : HeavyBallOrbit S)

/-
════════════════════════════════════════════════════════════════════════
§ 1. Function value vs energy
════════════════════════════════════════════════════════════════════════

The function-value gap is bounded by the energy:
    `f(x_k) − f(x*) ≤ E_k`.
-/
theorem fval_le_energy (k : ℕ) :
    S.f (orbit.x k) - S.f S.xStar ≤ energy_function S orbit k := by
  exact le_add_of_nonneg_right ( mul_nonneg ( by linarith [ S.hmu_pos ] ) ( sq_nonneg _ ) )

-- ════════════════════════════════════════════════════════════════════════
-- § 2. Main convergence theorem
-- ════════════════════════════════════════════════════════════════════════

/-- **Heavy ball convergence theorem.**
    For any certified orbit of the heavy ball method,
    `f(x_k) − f(x*) ≤ E_0 · ρ^k`
    where `ρ = (√κ − 1)/(√κ + 1) < 1`.

    This establishes **linear convergence** (also called geometric or
    exponential convergence) of the function values to the optimum.

    The rate `ρ` is optimal for first-order methods on the class of
    `μ`-strongly convex, `L`-smooth functions.  It matches the rate achieved
    by Nesterov's accelerated gradient method (see `nesterov-lean`), though
    the heavy ball method uses constant momentum `β = ρ²` rather than
    Nesterov's adaptive momentum schedule. -/
theorem heavy_ball_convergence (k : ℕ) :
    S.f (orbit.x k) - S.f S.xStar ≤ energy_function S orbit 0 * S.rho ^ k :=
  le_trans (fval_le_energy orbit k) (energy_geometric orbit k)

end