# heavy-ball-lean: Formal Proofs for Heavy Ball Linear Convergence in Lean 4

Ben Cassie  
ORCID: 0009-0004-1899-7627  
DOI: 10.5281/zenodo.20480592  
2026-05-31

## Abstract

`heavy-ball-lean` is a Lean 4 / Mathlib library formalising a certified convergence argument for the heavy ball method, also known as Polyak momentum. The library works over a real inner product space, packages smoothness and strong-convexity assumptions, defines the classical constant parameters, records a momentum update and Lyapunov energy, and proves geometric decay of the certified energy and function-value gap. The method is a Lyapunov-energy proof of linear convergence for a certified heavy-ball orbit. The development is machine-checked in Lean 4 with zero `sorry`, zero `admit`, and standard Lean/Mathlib axioms only.

## 1. Introduction

The heavy ball method augments gradient descent with momentum. Its update uses both the current gradient and the previous displacement:

```text
x' = x - alpha * grad f(x) + beta * p,
p' = x' - x.
```

For smooth strongly convex objectives, the classical parameter choice depends on the condition number `kappa = L / mu` and gives a linear rate controlled by

```text
rho = (sqrt(kappa) - 1) / (sqrt(kappa) + 1).
```

The Lean library formalises the parameter algebra and the convergence consequence of a certified Lyapunov descent property. It does not derive the descent certificate from all analytic assumptions; instead, the orbit structure carries the update rule and the energy decrease property needed for the final convergence theorem.

## 2. Mathematical Setting

`HeavyBall/Defs.lean` defines `HeavyBallSetup` over a real inner product space `E`. The setup includes an objective `f`, gradient oracle `grad_f`, constants `L` and `mu`, a minimiser `xStar`, positivity and ordering hypotheses for `L` and `mu`, and smoothness and strong-convexity assumptions.

The classical parameters are defined as

```text
alpha = 4 / (sqrt L + sqrt mu)^2
beta  = ((sqrt L - sqrt mu) / (sqrt L + sqrt mu))^2
kappa = L / mu
rho   = (sqrt kappa - 1) / (sqrt kappa + 1).
```

The Lyapunov energy combines objective suboptimality with a momentum-weighted squared norm:

```text
E_k = f(x_k) - f(xStar)
      + mu / 2 * ||x_k + (1 / sqrt mu) * p_k - xStar||^2.
```

## 3. Main Theorems

The setup proves parameter facts including `sqrt_L_pos`, `sqrt_mu_pos`, `sqrt_mu_le_sqrt_L`, `one_le_kappa`, `rho_nonneg`, `rho_lt_one`, `rho_alt`, and `beta_eq_rho_sq`.

`Descent.lean` proves the certified descent theorem

```text
heavy_ball_descent:
  E_{k+1} <= rho * E_k,
```

as well as `energy_nonneg` and `energy_geometric`:

```text
E_k <= E_0 * rho^k.
```

`Convergence.lean` proves `fval_le_energy`, showing the function-value gap is bounded by the energy, and the main theorem `heavy_ball_convergence`:

```text
f(x_k) - f(xStar) <= E_0 * rho^k.
```

## 4. Proof Sketch

The proof is organised around the Lyapunov energy. The parameter lemmas show that the rate is well formed: `rho` is nonnegative and strictly less than one, and `beta` equals `rho^2`. The `HeavyBallOrbit` structure supplies both the state recurrence and the descent certificate.

Given `E_{k+1} <= rho * E_k`, induction yields the geometric estimate `E_k <= E_0 * rho^k`. Nonnegativity of the squared norm term implies the function-value gap is bounded above by the energy. Combining those two results gives the final linear convergence theorem.

## 5. Relation to Sibling Libraries

`heavy-ball-lean` is closest to `nesterov-lean`, DOI `10.5281/zenodo.20474481`, and `gradient-descent-lean`, DOI `10.5281/zenodo.20472996`. Those libraries formalise first-order convergence without Polyak momentum. `contraction-lean`, DOI `10.5281/zenodo.20474762`, supplies a related geometric-decay proof pattern, while `admm-lean` uses a Lyapunov decrease argument for residual convergence rather than momentum acceleration.

## 6. Conclusion

`heavy-ball-lean` formalises the parameter algebra and Lyapunov convergence shell for the heavy ball method. It proves that any certified orbit satisfying the stated energy descent condition has a geometrically decaying objective gap. Future work could derive the descent certificate directly from smoothness and strong convexity, compare the rate to Nesterov acceleration, and instantiate the framework for quadratic objectives.

## References

Polyak, B. T. (1964). *Some methods of speeding up the convergence of iteration methods*. USSR Computational Mathematics and Mathematical Physics, 4(5), 1-17.

Nesterov, Y. (2018). *Lectures on Convex Optimization*. Springer.

The Mathlib Community. (2024). *The Lean Mathematical Library*. GitHub repository. <https://github.com/leanprover-community/mathlib4>

Cassie, B. (2026). *gradient-descent-lean: Formal Proofs of Gradient Descent Convergence in Lean 4*. Zenodo. <https://doi.org/10.5281/zenodo.20472996>

Cassie, B. (2026). *nesterov-lean: Formal Proofs of Nesterov Accelerated Gradient Descent in Lean 4*. Zenodo. <https://doi.org/10.5281/zenodo.20474481>

Cassie, B. (2026). *contraction-lean*. Zenodo. <https://doi.org/10.5281/zenodo.20474762>
