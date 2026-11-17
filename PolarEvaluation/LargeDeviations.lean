import PolarEvaluation.Basic
import PolarEvaluation.ShiftedLattice
import PolarEvaluation.PrimeMoments

/-!
# Large-Deviation Bounds in the `t`-Aspect and `q`-Aspect

This module formalizes Section 6 of the manuscript:
- Theorem 1.4: `t`-aspect large-deviation bound (`t_aspect_large_deviation`).
- Theorem 1.5: `q`-aspect large-deviation bound (`q_aspect_large_deviation`).
- Corollary 1.6: Large-deviation bound for `|S(t, χ)|` (`S_large_deviation_t`,
  `S_large_deviation_q`).
-/

noncomputable section

open Real Complex MeasureTheory

namespace PolarEvaluation

/-- **Theorem 1.4 (`t`-aspect large-deviation bound).** -/
theorem t_aspect_large_deviation (D : LFunctionData)
    (q : ℕ) (hq : q ≥ 1) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hGRH : D.GRH q hq χ hχ)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2)) :
    ∃ c_θ A_θ T₀ : ℝ, c_θ > 0 ∧ A_θ > 1 ∧ T₀ ≥ 10 ∧
      ∀ T ≥ T₀, ∀ V : ℝ, A_θ * Real.log (Real.log T) ≤ V → V ≤ Real.log T / Real.log (Real.log T) →
        (1 / T) * (MeasureTheory.volume {t ∈ Set.Icc T (2 * T) |
          D.L q χ (1 / 2 + Complex.I * t) ≠ 0 ∧
          (Complex.exp (-Complex.I * θ) *
            Complex.log (D.L q χ (1 / 2 + Complex.I * t))).re ≥ V}).toReal ≤
          Real.exp (-c_θ * V * Real.log (V / Real.log (Real.log T))) := by
  sorry

/-- **Theorem 1.5 (`q`-aspect large-deviation bound).** -/
theorem q_aspect_large_deviation (D : LFunctionData) (t₀ : ℝ)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2)) :
    ∃ c_θ A_θ : ℝ, ∃ q₀ : ℕ, c_θ > 0 ∧ A_θ > 1 ∧ q₀ ≥ 3 ∧
      ∀ q ≥ q₀,
        (∀ χ : DirichletCharacter ℂ q, ∀ hχ : χ.IsPrimitive, D.GRH q (by omega) χ hχ) →
        let phiStar := (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)).card
        phiStar ≥ 1 →
        ∀ V : ℝ, A_θ * Real.log (Real.log q) ≤ V → V ≤ Real.log q / Real.log (Real.log q) →
          ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
            χ.IsPrimitive ∧ D.L q χ (1 / 2 + Complex.I * t₀) ≠ 0 ∧
            (Complex.exp (-Complex.I * θ) *
              Complex.log (D.L q χ (1 / 2 + Complex.I * t₀))).re ≥ V)).card : ℝ) /
            (phiStar : ℝ) ≤
            Real.exp (-c_θ * V * Real.log (V / Real.log (Real.log q))) := by
  sorry

/-- **Corollary 1.6(i): `t`-aspect large-deviation bound for `|S(t, χ)|`.** -/
theorem S_large_deviation_t (D : LFunctionData)
    (q : ℕ) (hq : q ≥ 1) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hGRH : D.GRH q hq χ hχ) (α : ℝ) (hα : α > 0) :
    ∃ c > 0, ∃ T₀ : ℝ, T₀ ≥ 10 ∧ ∀ T ≥ T₀,
      (1 / T) * (MeasureTheory.volume {t ∈ Set.Icc T (2 * T) |
        D.L q χ (1 / 2 + Complex.I * t) ≠ 0 ∧
        |D.S q χ t| > α * Real.sqrt (Real.log T * Real.log (Real.log T))}).toReal ≤
        Real.exp (-c * α * Real.sqrt (Real.log T) * (Real.log (Real.log T)) ^ ((3 : ℝ) / 2)) := by
  sorry

end PolarEvaluation
