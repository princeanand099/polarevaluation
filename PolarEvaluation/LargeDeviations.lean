import PolarEvaluation.Basic
import PolarEvaluation.ExternalResults
import PolarEvaluation.ExplicitFormulae
import PolarEvaluation.ShiftedLattice
import PolarEvaluation.PrimeMoments

/-!
# Large-Deviation Bounds in the t-Aspect and q-Aspect (Section 7 & Theorems 1.4–1.5, Corollary 1.6)
-/

noncomputable section

open Complex Real MeasureTheory Filter Topology

namespace PolarEvaluation

/-- **Theorem 1.4** (`t`-aspect large-deviation bound). -/
theorem t_aspect_large_deviation (D : LFunctionData) (q : ℕ) (hq : q ≥ 1)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hGRH : D.GRH q hq χ hχ)
    (θ : ℝ) (hθ : |θ| < Real.pi / 2) :
    ∃ (c c' A T₀ : ℝ), c > 0 ∧ c' > 0 ∧ A > 1 ∧ T₀ ≥ 100 ∧
      (∀ (T V : ℝ), T ≥ T₀ →
        A * Real.log (Real.log T) ≤ V → V ≤ Real.log T / Real.log (Real.log T) →
        (1 / T) * (volume { t ∈ Set.Icc T (2 * T) |
          D.nonvanishing q χ t ∧ polarLogL D q χ t θ ≥ V }).toReal ≤
          Real.exp (-c * V * Real.log (V / Real.log (Real.log T)))) ∧
      (∀ (T α : ℝ), T ≥ T₀ → α > 0 →
        let V := α * Real.sqrt (Real.log T * Real.log (Real.log T))
        V ≤ Real.log T / Real.log (Real.log T) →
        (volume { t ∈ Set.Icc T (2 * T) |
          D.nonvanishing q χ t ∧ polarLogL D q χ t θ ≥ V }).toReal ≤
          T * Real.exp (-c' * α * Real.sqrt (Real.log T) * (Real.log (Real.log T)) ^ (3 / 2 : ℝ))) := by
  sorry

/-- **Theorem 1.5** (`q`-aspect large-deviation bound). -/
theorem q_aspect_large_deviation (D : LFunctionData) (t₀ θ : ℝ) (hθ : |θ| < Real.pi / 2) :
    ∃ (c c' A : ℝ) (q₀ : ℕ), c > 0 ∧ c' > 0 ∧ A > 1 ∧ q₀ ≥ 3 ∧
      (∀ (q : ℕ) (hq1 : q ≥ 1), q ≥ q₀ → totientStar q ≥ 1 →
        (∀ (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive), D.GRH q hq1 χ hχ) →
        ∀ V : ℝ, A * Real.log (Real.log q) ≤ V → V ≤ Real.log q / Real.log (Real.log q) →
        letI := Classical.decPred (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)
        (1 / (totientStar q : ℝ)) *
          ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
            χ.IsPrimitive ∧ D.nonvanishing q χ t₀ ∧ polarLogL D q χ t₀ θ ≥ V)).card : ℝ) ≤
          Real.exp (-c * V * Real.log (V / Real.log (Real.log q)))) ∧
      (∀ (q : ℕ) (hq1 : q ≥ 1), q ≥ q₀ → totientStar q ≥ 1 →
        (∀ (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive), D.GRH q hq1 χ hχ) →
        ∀ α : ℝ, α > 0 →
        let V := α * Real.sqrt (Real.log q * Real.log (Real.log q))
        V ≤ Real.log q / Real.log (Real.log q) →
        letI := Classical.decPred (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)
        (1 / (totientStar q : ℝ)) *
          ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
            χ.IsPrimitive ∧ D.nonvanishing q χ t₀ ∧ polarLogL D q χ t₀ θ ≥ V)).card : ℝ) ≤
          Real.exp (-c' * α * Real.sqrt (Real.log q) * (Real.log (Real.log q)) ^ (3 / 2 : ℝ))) := by
  sorry

/-- **Corollary 1.6(i)** (`t`-aspect large-deviation bound for `|S(t, χ)|`). -/
theorem S_large_deviation_t (D : LFunctionData) (q : ℕ) (hq : q ≥ 1)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hGRH : D.GRH q hq χ hχ) :
    ∀ α > 0, ∃ (c T₀ : ℝ), c > 0 ∧ T₀ ≥ 100 ∧
      ∀ T ≥ T₀,
        let V := α * Real.sqrt (Real.log T * Real.log (Real.log T))
        V ≤ Real.log T / Real.log (Real.log T) →
        (volume { t ∈ Set.Icc T (2 * T) |
          D.nonvanishing q χ t ∧ |D.S_val q χ t| ≥ V }).toReal ≤
          T * Real.exp (-c * α * Real.sqrt (Real.log T) * (Real.log (Real.log T)) ^ (3 / 2 : ℝ)) := by
  sorry

/-- **Corollary 1.6(ii)** (`q`-aspect large-deviation bound for `|S(t₀, χ)|`). -/
theorem S_large_deviation_q (D : LFunctionData) (t₀ : ℝ) :
    ∀ α > 0, ∃ (c : ℝ) (q₀ : ℕ), c > 0 ∧ q₀ ≥ 3 ∧
      ∀ (q : ℕ) (hq1 : q ≥ 1), q ≥ q₀ → totientStar q ≥ 1 →
        (∀ (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive), D.GRH q hq1 χ hχ) →
        let V := α * Real.sqrt (Real.log q * Real.log (Real.log q))
        V ≤ Real.log q / Real.log (Real.log q) →
        letI := Classical.decPred (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)
        (1 / (totientStar q : ℝ)) *
          ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
            χ.IsPrimitive ∧ D.nonvanishing q χ t₀ ∧ |D.S_val q χ t₀| ≥ V)).card : ℝ) ≤
          Real.exp (-c * α * Real.sqrt (Real.log q) * (Real.log (Real.log q)) ^ (3 / 2 : ℝ)) := by
  sorry

end PolarEvaluation
