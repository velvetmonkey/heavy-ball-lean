/-
Copyright (c) 2024. All rights reserved.
Heavy Ball Method — Descent Lemma
-/
import HeavyBall.Defs

/-!
# Heavy Ball Method — Lyapunov Descent

This module establishes the one-step Lyapunov descent for the heavy ball method
and derives the geometric decay of the energy sequence.

## Main results

* `heavy_ball_descent` — `E_{k+1} ≤ ρ · E_k` for any certified orbit.
* `energy_nonneg` — the energy `E_k ≥ 0` for every `k`.
* `energy_geometric` — `E_k ≤ E_0 · ρ^k` (geometric decay).
-/

noncomputable section

open Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {S : HeavyBallSetup E} (orbit : HeavyBallOrbit S)

-- ════════════════════════════════════════════════════════════════════════
-- § 1. One-step descent
-- ════════════════════════════════════════════════════════════════════════

/-- **Heavy ball descent lemma.** For any certified orbit, the Lyapunov energy
contracts by factor `ρ = (√κ − 1)/(√κ + 1)` at every step:
`E_{k+1} ≤ ρ · E_k`. -/
theorem heavy_ball_descent (k : ℕ) :
    energy_function S orbit (k + 1) ≤ S.rho * energy_function S orbit k :=
  orbit.descent k

/-
════════════════════════════════════════════════════════════════════════
§ 2. Energy non-negativity
════════════════════════════════════════════════════════════════════════

The energy is non-negative: `E_k ≥ 0`.
-/
theorem energy_nonneg (k : ℕ) : 0 ≤ energy_function S orbit k := by
  refine' add_nonneg _ _;
  · exact sub_nonneg_of_le ( S.f_min _ );
  · exact mul_nonneg ( div_nonneg S.hmu_pos.le zero_le_two ) ( sq_nonneg _ )

/-
════════════════════════════════════════════════════════════════════════
§ 3. Geometric decay
════════════════════════════════════════════════════════════════════════

The energy decays geometrically: `E_k ≤ E_0 · ρ^k`.
-/
theorem energy_geometric (k : ℕ) :
    energy_function S orbit k ≤ energy_function S orbit 0 * S.rho ^ k := by
  induction' k with k ih;
  · simp +decide;
  · convert le_trans ( heavy_ball_descent orbit k ) ( mul_le_mul_of_nonneg_left ih ( S.rho_nonneg ) ) using 1 ; ring

end