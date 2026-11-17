import PolarEvaluation.Basic
import PolarEvaluation.ExternalResults
import PolarEvaluation.ExplicitFormulae

/-!
# High-Moment Estimates for Prime Sums

This module formalizes Section 5 of the manuscript:
- Lemma 5.1: Uniform bounds on prime-square `P^{(2)}` and higher-power `P^{(≥ 3)}` sums.
- Lemma 5.2: `2k`-th moment bounds on `P^{(1)}` in both the `t`-aspect and `q`-aspect.
-/

noncomputable section

open Real Complex MeasureTheory

namespace PolarEvaluation

/-- Prime-power sum `P_{θ,Δ}(t, χ)` from the Guinand-Weil explicit formula. -/
def primePowerSum (M : ℝ → ℝ) (X : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  (1 / (2 * Real.pi : ℂ)) *
    ∑' n : ℕ, if 2 ≤ n ∧ (n : ℝ) ≤ X then
      ((ArithmeticFunction.vonMangoldt n : ℂ) / Real.sqrt n) *
        (χ n * (fourierIntegral (fun x : ℝ => (M x : ℂ)) (-Real.log n / (2 * Real.pi))) *
            (n : ℂ) ^ (-Complex.I * t) +
          starRingEnd ℂ (χ n) *
            (fourierIntegral (fun x : ℝ => (M x : ℂ)) (Real.log n / (2 * Real.pi))) *
            (n : ℂ) ^ (Complex.I * t))
    else 0

/-- Prime sum `P^{(1)}_{θ,Δ}(t, χ)` restricted to primes `p ≤ X`. -/
def primeSum1 (M : ℝ → ℝ) (X : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  (1 / (2 * Real.pi : ℂ)) *
    ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 (Nat.floor X)),
      ((Real.log p : ℂ) / Real.sqrt p) *
        (χ p * (fourierIntegral (fun x : ℝ => (M x : ℂ)) (-Real.log p / (2 * Real.pi))) *
            (p : ℂ) ^ (-Complex.I * t) +
          starRingEnd ℂ (χ p) *
            (fourierIntegral (fun x : ℝ => (M x : ℂ)) (Real.log p / (2 * Real.pi))) *
            (p : ℂ) ^ (Complex.I * t))

/-- **Lemma 5.1 (Prime-square and higher-power sums).** -/
theorem prime_power_tail_bounds (θ : ℝ) (hθ : θ ∈ Set.Icc (-Real.pi / 2) (Real.pi / 2))
    (Δ₀ : ℝ) (hΔ₀ : Δ₀ ≥ 1) (M : ℝ → ℝ → ℝ)
    (hL1 : ∃ C > 0, ∀ Δ ≥ Δ₀, ∫ x : ℝ, |M Δ x - kernelK θ x| ≤ C / Δ) :
    ∃ C_2 C_3 : ℝ, C_2 > 0 ∧ C_3 > 0 ∧
      ∀ Δ ≥ Δ₀, ∀ q : ℕ, ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
        ‖primePowerSum (M Δ) (Real.exp (2 * Real.pi * Δ)) q χ t -
          primeSum1 (M Δ) (Real.exp (2 * Real.pi * Δ)) q χ t‖ ≤
          C_2 * Real.log (Real.log (Real.exp (2 * Real.pi * Δ))) + C_3 := by
  sorry

/-- **Lemma 5.2(i) (`2k`-th moment bound in the `t`-aspect).** -/
theorem prime_moment_t_aspect (θ : ℝ) (hθ : θ ∈ Set.Icc (-Real.pi / 2) (Real.pi / 2))
    (Δ₀ : ℝ) (hΔ₀ : Δ₀ ≥ 1) (M : ℝ → ℝ → ℝ)
    (hL1 : ∃ C > 0, ∀ Δ ≥ Δ₀, ∫ x : ℝ, |M Δ x - kernelK θ x| ≤ C / Δ) :
    ∃ B_θ > 0, ∀ Δ ≥ Δ₀, ∀ k : ℕ, k ≥ 1 → ∀ q ≥ 1, ∀ χ : DirichletCharacter ℂ q,
      ∀ T : ℝ, T ≥ (Real.exp (2 * Real.pi * Δ)) ^ k →
        (1 / T) * ∫ t in Set.Icc T (2 * T),
          ‖primeSum1 (M Δ) (Real.exp (2 * Real.pi * Δ)) q χ t‖ ^ (2 * k) ≤
          (B_θ * k * Real.log (Real.log (Real.exp (2 * Real.pi * Δ)))) ^ k := by
  sorry

/-- **Lemma 5.2(ii) (`2k`-th moment bound in the `q`-aspect).** -/
theorem prime_moment_q_aspect (θ : ℝ) (hθ : θ ∈ Set.Icc (-Real.pi / 2) (Real.pi / 2))
    (Δ₀ : ℝ) (hΔ₀ : Δ₀ ≥ 1) (M : ℝ → ℝ → ℝ)
    (hL1 : ∃ C > 0, ∀ Δ ≥ Δ₀, ∫ x : ℝ, |M Δ x - kernelK θ x| ≤ C / Δ) :
    ∃ B_θ > 0, ∀ Δ ≥ Δ₀, ∀ k : ℕ, k ≥ 1 → ∀ q : ℕ,
      (Real.exp (2 * Real.pi * Δ)) ^ k < q → ∀ t₀ : ℝ,
        (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then
            ‖primeSum1 (M Δ) (Real.exp (2 * Real.pi * Δ)) q χ t₀‖ ^ (2 * k)
          else 0) ≤
          (Nat.totient q : ℝ) *
            (B_θ * k * Real.log (Real.log (Real.exp (2 * Real.pi * Δ)))) ^ k := by
  sorry

end PolarEvaluation
