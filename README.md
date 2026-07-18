# heavy-ball-lean

[![thread](https://img.shields.io/badge/%F0%9F%A7%B5-how%20it%20works-1DA1F2)](https://x.com/thevelvetmonke)
[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-proven%20%2F%200%20sorry-brightgreen)](HeavyBall)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20480592.svg)](https://doi.org/10.5281/zenodo.20480592)

**heavy-ball-lean: Formal Proofs for Heavy Ball Linear Convergence in Lean 4**

Lean 4 formal proofs for the heavy ball method, also known as Polyak momentum, for L-smooth and mu-strongly convex objectives. The development covers the heavy ball setup, optimal constant parameters, momentum update, Lyapunov energy, certified orbit descent, geometric energy decay, and linear convergence of function values.

**Zero sorry statements.** Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

## What this is, and why it matters

This library formalizes a Lyapunov convergence wrapper for Polyak's heavy ball method. Its headline theorem, `heavy_ball_convergence`, proves that the function-value gap of a certified orbit is bounded by its initial energy times `rho^k`, where `rho` is the classical condition-number expression and is proved to lie below one.

The checked proof turns one-step contraction into a global rate. It proves the parameter facts, iterates the energy inequality, and uses the nonnegative quadratic part of the Lyapunov energy to bound the objective gap. This isolates a reusable, machine-checked convergence implication.

The essential analytical step is assumed. `HeavyBallOrbit` includes both the momentum update and a field asserting `E_(k+1) <= rho*E_k`; the library does not derive that descent certificate from smoothness and strong convexity. The headline therefore applies to certified orbits, not automatically to every orbit generated from the listed parameter formulas.

## Background and motivation

The heavy ball method is a classical accelerated first-order method for smooth strongly convex optimisation. It updates the current point using both the gradient and a momentum term:

```text
x' = x - alpha * grad f(x) + beta * p
p' = x' - x
```

For an `L`-smooth, `mu`-strongly convex objective, the classical parameter choice is:

```text
alpha = 4 / (sqrt(L) + sqrt(mu))^2
beta = ((sqrt(L) - sqrt(mu)) / (sqrt(L) + sqrt(mu)))^2
```

The resulting linear rate is:

```text
rho = (sqrt(kappa) - 1) / (sqrt(kappa) + 1)
kappa = L / mu
```

This library machine-checks the parameter facts and the convergence implication from a certified Lyapunov descent property.

## Setting

A general real inner product space `E`, objective `f : E -> Real`, gradient oracle `grad_f : E -> E`, smoothness constant `L`, strong convexity constant `mu`, and minimiser `xStar`.

The setup assumes:

- `0 < L`
- `0 < mu`
- `mu <= L`
- `grad_f xStar = 0`
- `xStar` is a global minimiser of `f`
- `f` is `L`-smooth
- `f` is `mu`-strongly convex

The Lyapunov energy is:

```text
E_k = f(x_k) - f(xStar)
      + mu / 2 * ||x_k + (1 / sqrt(mu)) * p_k - xStar||^2
```

The `HeavyBallOrbit` structure carries both the update rule and the certified descent property:

```text
E_{k+1} <= rho * E_k
```

## Main result

For any certified heavy ball orbit, the main theorem proves:

```text
f(x_k) - f(xStar) <= E_0 * rho^k
```

This is linear, or geometric, convergence of function values for the certified heavy ball orbit.

## Project structure

```text
HeavyBall/
├── Defs.lean        — HeavyBallSetup, alpha, beta, kappa, rho,
│                      momentum_step, energy_at, HeavyBallOrbit
├── Descent.lean     — certified one-step descent, energy nonnegativity,
│                      geometric energy decay
└── Convergence.lean — function-value gap bound and main convergence theorem
HeavyBall.lean       — Root module
```

## Theorem inventory

| # | Name | Statement |
|---|------|-----------|
| 1 | `sqrt_L_pos` | `0 < sqrt L` |
| 2 | `sqrt_mu_pos` | `0 < sqrt mu` |
| 3 | `sqrt_L_nonneg` | `0 <= sqrt L` |
| 4 | `sqrt_mu_nonneg` | `0 <= sqrt mu` |
| 5 | `sqrt_mu_le_sqrt_L` | `sqrt mu <= sqrt L` |
| 6 | `sqrt_sum_pos` | `0 < sqrt L + sqrt mu` |
| 7 | `one_le_kappa` | `1 <= kappa` |
| 8 | `one_le_sqrt_kappa` | `1 <= sqrt kappa` |
| 9 | `sqrt_kappa_add_one_pos` | `0 < sqrt kappa + 1` |
| 10 | `rho_nonneg` | `0 <= rho` |
| 11 | `rho_lt_one` | `rho < 1` |
| 12 | `rho_alt` | `rho = (sqrt L - sqrt mu) / (sqrt L + sqrt mu)` |
| 13 | `beta_eq_rho_sq` | `beta = rho^2` |
| 14 | `heavy_ball_descent` | For a certified orbit, `E_{k+1} <= rho * E_k` |
| 15 | `energy_nonneg` | `0 <= E_k` |
| 16 | `energy_geometric` | `E_k <= E_0 * rho^k` |
| 17 | `fval_le_energy` | `f(x_k) - f(xStar) <= E_k` |
| 18 | `heavy_ball_convergence` | `f(x_k) - f(xStar) <= E_0 * rho^k` |

## Dependencies

- Lean 4.28.0
- Mathlib v4.28.0

## Related work

- [nesterov-lean](https://github.com/velvetmonkey/nesterov-lean) — Lean 4 Nesterov accelerated gradient descent
- [gradient-descent-lean](https://github.com/velvetmonkey/gradient-descent-lean) — Lean 4 gradient descent convergence
- [contraction-lean](https://github.com/velvetmonkey/contraction-lean) — Lean 4 contraction and convergence reasoning
- [admm-lean](https://github.com/velvetmonkey/admm-lean) — Lean 4 ADMM residual and objective convergence

## Acknowledgements

Proofs in this library were generated using [Aristotle](https://aristotle.harmonic.fun), an AI proof assistant for Lean 4 and Mathlib. The proof discipline — zero sorry, standard axioms only — was specified by the author and enforced by the Lean type checker.

## Author

Ben Cassie · [@thevelvetmonke](https://x.com/thevelvetmonke)
## Part of the Lean proof corpus

One of a family of small, machine-checked Lean 4 developments. Index: [velvetmonkey/lean](https://github.com/velvetmonkey/lean) ([live index](https://velvetmonkey.github.io/lean)).
