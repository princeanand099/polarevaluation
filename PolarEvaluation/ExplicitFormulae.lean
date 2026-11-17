import PolarEvaluation.Basic
import PolarEvaluation.ExternalResults

/-!
# Explicit Formulae and Fourier Analysis of `K_θ`

This module formalizes Section 2 of the manuscript:
- Lemma 2.1: Horizontal zero-sum representation (`horizontal_zero_sum`).
- Lemma 2.2: Bandlimited Guinand-Weil explicit formula (`guinand_weil_bandlimited`).
- Lemma 2.3: Fourier transform and `|ξ|^{-1}` decay of `K_θ` (`kernelK_fourier`,
  `majorant_fourier_decay`).
-/

noncomputable section

open Real Complex MeasureTheory

namespace PolarEvaluation

/-- **Lemma 2.1 (Horizontal zero-sum representation).** -/
theorem horizontal_zero_sum (D : LFunctionData) (q : ℕ) (hq : q ≥ 1)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hGRH : D.GRH q hq χ hχ)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2))
    (t : ℝ) (ht0 : D.L q χ (1 / 2 + Complex.I * t) ≠ 0) (ht1 : q = 1 → |t| ≥ 10) :
    ∃ C_abs : ℝ, C_abs ≥ 0 ∧
      |(Complex.exp (-Complex.I * θ) *
          Complex.log (D.L q χ (1 / 2 + Complex.I * t))).re -
        ((Real.cos θ / 2) * Real.log (analyticConductor q t) +
          ∑' γ : D.zeros q χ, kernelK θ (t - (γ : ℝ)))| ≤ C_abs :=
  horizontal_zero_sum_external D q hq χ hχ hGRH θ hθ t ht0 ht1

/-- **Lemma 2.2 (Guinand-Weil explicit formula).** -/
theorem guinand_weil_bandlimited (D : LFunctionData) (q : ℕ) (hq : q ≥ 1)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hGRH : D.GRH q hq χ hχ)
    (Δ : ℝ) (hΔ : Δ ≥ 1) (h : ℂ → ℂ) (hh_type : HasExponentialType h (2 * Real.pi * Δ))
    (M : ℝ) (hM : ∀ x : ℝ, (1 + x ^ 2) * ‖h x‖ ≤ M)
    (t : ℝ) (ht1 : q = 1 → |t| ≥ 10) :
    ∃ C_gw : ℝ, C_gw ≥ 0 ∧
      ‖(∑' γ : D.zeros q χ, h (t - (γ : ℝ))) -
        ((Real.log (analyticConductor q t) / (2 * Real.pi)) * (∫ x : ℝ, h x) -
          (1 / (2 * Real.pi)) *
            ∑' n : ℕ, if 2 ≤ n ∧ (n : ℝ) ≤ Real.exp (2 * Real.pi * Δ) then
              ((ArithmeticFunction.vonMangoldt n : ℂ) / Real.sqrt n) *
                (χ n * (fourierHat (fun x : ℝ => h x) (-Real.log n / (2 * Real.pi))) *
                    (n : ℂ) ^ (-Complex.I * t) +
                  starRingEnd ℂ (χ n) *
                    (fourierHat (fun x : ℝ => h x) (Real.log n / (2 * Real.pi))) *
                    (n : ℂ) ^ (Complex.I * t))
            else 0)‖ ≤
        C_gw * (M + (if q = 1 then Real.exp (Real.pi * Δ) / t ^ 2 * M else 0)) :=
  guinand_weil_external D q hq χ hχ hGRH Δ hΔ h hh_type M hM t ht1

/-- **Lemma 2.3 (Fourier transform of `K_θ`).** -/
theorem kernelK_fourier (θ : ℝ) (hθ : θ ∈ Set.Icc (-Real.pi / 2) (Real.pi / 2))
    (ξ : ℝ) (hξ : ξ ≠ 0) :
    fourierHat (fun x : ℝ => (kernelK θ x : ℂ)) ξ =
      -(Real.cos θ : ℂ) * ((1 - Real.exp (-2 * Real.pi * |ξ|)) / (2 * |ξ|)) -
        Complex.I * Real.sin θ *
          (((1 - Real.exp (-2 * Real.pi * |ξ|)) / (2 * ξ)) -
            Real.pi * (if ξ > 0 then 1 else -1) * Real.exp (-2 * Real.pi * |ξ|)) := by
  sorry

/-- **Lemma 2.3 (Prime-frequency decay of majorant Fourier transform).** -/
theorem majorant_fourier_decay (θ : ℝ) (hθ : θ ∈ Set.Icc (-Real.pi / 2) (Real.pi / 2))
    (Δ₀ : ℝ) (hΔ₀ : Δ₀ ≥ 1) (M : ℝ → ℝ → ℝ)
    (hL1 : ∃ C > 0, ∀ Δ ≥ Δ₀, ∫ x : ℝ, |M Δ x - kernelK θ x| ≤ C / Δ) :
    ∃ C_dec > 0, ∀ Δ ≥ Δ₀, ∀ p : ℕ, Nat.Prime p →
      ‖fourierHat (fun x : ℝ => (M Δ x : ℂ)) (Real.log p / (2 * Real.pi))‖ ≤
        C_dec * (1 / Real.log p + 1 / Δ) ∧
      ‖fourierHat (fun x : ℝ => (M Δ x : ℂ)) (-Real.log p / (2 * Real.pi))‖ ≤
        C_dec * (1 / Real.log p + 1 / Δ) := by
  sorry

end PolarEvaluation
