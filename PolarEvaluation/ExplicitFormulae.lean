import PolarEvaluation.Basic
import PolarEvaluation.ExternalResults

/-!
# Explicit Formulae and Fourier Analysis of the Kernel (Section 2)

Formalizes Lemma 2.1 (`horizontal_zero_sum`), Lemma 2.2 (`guinand_weil_bandlimited`),
and Lemma 2.3 (`kernelK_fourier` and `majorant_fourier_decay`).
-/

noncomputable section

open Complex Real MeasureTheory Filter Topology

namespace PolarEvaluation

/-- **Lemma 2.1** (Horizontal zero-sum representation). -/
theorem horizontal_zero_sum (D : LFunctionData) :
    ∃ C₀ : ℝ, C₀ > 0 ∧
      ∀ (q : ℕ) (hq : q ≥ 1) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive),
        D.GRH q hq χ hχ →
        ∀ (θ : ℝ), |θ| < Real.pi / 2 →
        ∀ (t : ℝ), D.nonvanishing q χ t → (q = 1 → |t| ≥ 10) →
          Summable (fun n : ℕ => kernelK θ (t - D.zeros q χ n)) ∧
          |polarLogL D q χ t θ -
            ((Real.cos θ / 2) * Real.log (analyticConductor q t) +
              ∑' n : ℕ, kernelK θ (t - D.zeros q χ n))| ≤ C₀ :=
  horizontal_zero_sum_external D

/-- **Lemma 2.2** (Guinand–Weil Explicit Formula for bandlimited test functions). -/
theorem guinand_weil_bandlimited (D : LFunctionData) :
    ∃ C₁ : ℝ, C₁ > 0 ∧
      ∀ (q : ℕ) (hq : q ≥ 1) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive),
        D.GRH q hq χ hχ →
        ∀ (h : ℂ → ℂ) (Δ M_sup : ℝ), Δ ≥ 1 → M_sup ≥ 0 →
          HasExponentialType h (2 * Real.pi * Δ) →
          (∀ x : ℝ, ‖h x‖ ≤ M_sup / (1 + x ^ 2)) →
          (∀ x : ℝ, (h x).im = 0) →
          ∀ (t : ℝ), (q = 1 → |t| ≥ 10) →
            Summable (fun n : ℕ => (h (t - D.zeros q χ n)).re) ∧
            |∑' n : ℕ, (h (t - D.zeros q χ n)).re -
              ((Real.log (analyticConductor q t) / (2 * Real.pi)) * (∫ x : ℝ, (h x).re) -
                primePowerSum q χ (fourierHat (fun x : ℝ => h x)) (Real.exp (2 * Real.pi * Δ)) t)| ≤
              C₁ * (M_sup + (if q = 1 then Real.exp (Real.pi * Δ) / t ^ 2 * M_sup else 0)) :=
  guinand_weil_external D

/-- **Lemma 2.3 (Part 1)**: Explicit Fourier transform `K̂_θ(ξ)` for `θ ∈ [-π/2, π/2]` and `ξ ≠ 0`,
together with `K̂_θ(0) = -π cos θ`. -/
theorem kernelK_fourier (θ : ℝ) (hθ : |θ| ≤ Real.pi / 2) :
    fourierHat (fun x : ℝ => (kernelK θ x : ℂ)) 0 = (-Real.pi * Real.cos θ : ℂ) ∧
    ∀ ξ : ℝ, ξ ≠ 0 →
      fourierHat (fun x : ℝ => (kernelK θ x : ℂ)) ξ =
        -(Real.cos θ : ℂ) * ((1 - Complex.exp (-2 * Real.pi * |ξ|)) / (2 * |ξ|)) -
          Complex.I * (Real.sin θ : ℂ) *
            ((1 - Complex.exp (-2 * Real.pi * |ξ|)) / (2 * ξ) -
              Real.pi * (if 0 < ξ then (1 : ℂ) else -1) * Complex.exp (-2 * Real.pi * |ξ|)) := by
  sorry

/-- **Lemma 2.3 (Part 2)**: Fourier decay of any bandlimited `L^1`-close majorant `M_{θ,Δ}`
at `ξ = ± log p / (2π)`. -/
theorem majorant_fourier_decay (θ C_L1 Δ₀ : ℝ) (hθ : |θ| ≤ Real.pi / 2) (hΔ₀ : Δ₀ ≥ 1) :
    ∃ C_dec > 0, ∀ (Δ : ℝ) (M : ℝ → ℝ), Δ ≥ Δ₀ →
      Integrable (fun x : ℝ => M x - kernelK θ x) →
      (∫ x : ℝ, |M x - kernelK θ x|) ≤ C_L1 / Δ →
      ∀ (p : ℕ), Nat.Prime p →
        ‖fourierHat (fun x : ℝ => (M x : ℂ)) (Real.log p / (2 * Real.pi))‖ ≤
          C_dec * (1 / Real.log p + 1 / Δ) ∧
        ‖fourierHat (fun x : ℝ => (M x : ℂ)) (-(Real.log p / (2 * Real.pi)))‖ ≤
          C_dec * (1 / Real.log p + 1 / Δ) := by
  sorry

end PolarEvaluation
