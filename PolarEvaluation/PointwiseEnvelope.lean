import PolarEvaluation.Basic
import PolarEvaluation.ExternalResults
import PolarEvaluation.ExplicitFormulae
import PolarEvaluation.ShiftedLattice

/-!
# Pointwise Polar Envelope and Universal Convex Domain (Section 5 & Theorems 1.1–1.2, Corollary 1.3)
-/

noncomputable section

open Complex Real MeasureTheory Filter Topology

namespace PolarEvaluation

/-- **Theorem 1.1** (Pointwise directional envelope). -/
theorem directional_envelope_bound (D : LFunctionData) (θ : ℝ) (hθ : |θ| < Real.pi / 2) :
    ∃ (Q₀ C_err : ℝ), Q₀ ≥ 100 ∧ C_err > 0 ∧
      ∀ (q : ℕ) (hq : q ≥ 1) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive),
        D.GRH q hq χ hχ →
        ∀ (t : ℝ), D.nonvanishing q χ t → analyticConductor q t ≥ Q₀ →
          polarLogL D q χ t θ ≤
            (envelopeC θ + C_err * Real.log (Real.log (Real.log (analyticConductor q t))) /
              Real.log (Real.log (analyticConductor q t))) *
              (Real.log (analyticConductor q t) / Real.log (Real.log (analyticConductor q t))) := by
  sorry

/-- **Theorem 1.2 (Part 1)** (Universal convex domain confinement):
For every `ε > 0`, `z(t, χ)` lies in the `ε`-neighborhood of `Ω` for `q(|t| + 2) ≥ q₀(ε)`. -/
theorem convex_domain_confinement (D : LFunctionData) :
    ∀ ε > 0, ∃ Q₀ : ℝ, Q₀ ≥ 100 ∧
      ∀ (q : ℕ) (hq : q ≥ 1) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive),
        D.GRH q hq χ hχ →
        ∀ (t : ℝ), D.nonvanishing q χ t → analyticConductor q t ≥ Q₀ →
          ∃ w ∈ convexOmega, ‖normalizedLogL D q χ t - w‖ < ε := by
  sorry

/-- **Theorem 1.2 (Part 2)** (Modulus–argument tradeoff):
If `log|L(1/2 + it, χ)| ≥ (α - δ) log q / log log q` with `α ≤ (log 2)/2`,
then `|S(t, χ)| ≤ (arccos(e^{2α}/2)/(2π) + o(1)) log q / log log q`. -/
theorem modulus_argument_tradeoff (D : LFunctionData) (α : ℝ) (hα : α ≤ Real.log 2 / 2) :
    ∀ ε > 0, ∃ (δ Q₀ : ℝ), δ > 0 ∧ Q₀ ≥ 100 ∧
      ∀ (q : ℕ) (hq : q ≥ 1) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive),
        D.GRH q hq χ hχ →
        ∀ (t : ℝ), D.nonvanishing q χ t → analyticConductor q t ≥ Q₀ →
          D.logAbsL q χ t ≥ (α - δ) * (Real.log (analyticConductor q t) /
            Real.log (Real.log (analyticConductor q t))) →
          |D.S_val q χ t| ≤
            (Real.arccos (Real.exp (2 * α) / 2) / (2 * Real.pi) + ε) *
              (Real.log (analyticConductor q t) / Real.log (Real.log (analyticConductor q t))) := by
  sorry

/-- **Corollary 1.3(i)**: Whenever `|L(1/2 + it, χ)| ≥ 1`, `|S(t, χ)| ≤ (1/6 + o(1)) log q / log log q`. -/
theorem corollary_1_3_i (D : LFunctionData) :
    ∀ ε > 0, ∃ Q₀ : ℝ, Q₀ ≥ 100 ∧
      ∀ (q : ℕ) (hq : q ≥ 1) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive),
        D.GRH q hq χ hχ →
        ∀ (t : ℝ), D.nonvanishing q χ t → analyticConductor q t ≥ Q₀ →
          D.logAbsL q χ t ≥ 0 →
          |D.S_val q χ t| ≤ (1 / 6 + ε) *
            (Real.log (analyticConductor q t) / Real.log (Real.log (analyticConductor q t))) := by
  intro ε hε
  have hα : (0 : ℝ) ≤ Real.log 2 / 2 := by positivity
  obtain ⟨δ, Q₀, hδ, hQ₀, hmain⟩ := modulus_argument_tradeoff D 0 hα ε hε
  refine ⟨Q₀, hQ₀, fun q hq χ hχ hGRH t ht hcond hlog => ?_⟩
  have hscale : 0 ≤ Real.log (analyticConductor q t) / Real.log (Real.log (analyticConductor q t)) := by
    have h1 : Real.log (analyticConductor q t) ≥ Real.log 100 := Real.log_le_log (by norm_num) hcond
    have h2 : Real.log 100 > Real.exp 1 := by
      have : (100 : ℝ) > Real.exp (Real.exp 1) := by
        have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
        calc Real.exp (Real.exp 1) < Real.exp 3 := Real.exp_lt_exp.mpr he
        _ = Real.exp 1 * Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
        _ < 3 * 3 * 3 := by gcongr
        _ < 100 := by norm_num
      linarith [Real.log_lt_log (by positivity) this, Real.log_exp (Real.exp 1)]
    have hlog_pos : 0 < Real.log (analyticConductor q t) := by linarith [Real.exp_pos 1]
    have hloglog_pos : 0 < Real.log (Real.log (analyticConductor q t)) := by
      apply Real.log_pos
      linarith [Real.one_lt_exp_iff.mpr one_pos]
    positivity
  have hlog' : D.logAbsL q χ t ≥ (0 - δ) * (Real.log (analyticConductor q t) /
      Real.log (Real.log (analyticConductor q t))) := by
    have : (0 - δ) * (Real.log (analyticConductor q t) /
        Real.log (Real.log (analyticConductor q t))) ≤ 0 := by
      nlinarith
    linarith
  have hres := hmain q hq χ hχ hGRH t ht hcond hlog'
  have harc : Real.arccos (Real.exp (2 * 0) / 2) / (2 * Real.pi) = 1 / 6 := by
    rw [mul_zero, Real.exp_zero]
    have hcos : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
    rw [← hcos, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]
    field_simp [Real.pi_ne_zero]
    ring
  rwa [harc] at hres

/-- **Corollary 1.3(ii)**: Whenever `log|L(1/2 + it, χ)| ≥ ((log 2)/2 - δ) log q / log log q`,
we have `|S(t, χ)| ≤ ε log q / log log q`. -/
theorem corollary_1_3_ii (D : LFunctionData) :
    ∀ ε > 0, ∃ (δ Q₀ : ℝ), δ > 0 ∧ Q₀ ≥ 100 ∧
      ∀ (q : ℕ) (hq : q ≥ 1) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive),
        D.GRH q hq χ hχ →
        ∀ (t : ℝ), D.nonvanishing q χ t → analyticConductor q t ≥ Q₀ →
          D.logAbsL q χ t ≥ (Real.log 2 / 2 - δ) * (Real.log (analyticConductor q t) /
            Real.log (Real.log (analyticConductor q t))) →
          |D.S_val q χ t| ≤ ε *
            (Real.log (analyticConductor q t) / Real.log (Real.log (analyticConductor q t))) := by
  intro ε hε
  obtain ⟨δ, Q₀, hδ, hQ₀, hmain⟩ := modulus_argument_tradeoff D (Real.log 2 / 2) le_rfl ε hε
  refine ⟨δ, Q₀, hδ, hQ₀, fun q hq χ hχ hGRH t ht hcond hlog => ?_⟩
  have hres := hmain q hq χ hχ hGRH t ht hcond hlog
  have harc : Real.arccos (Real.exp (2 * (Real.log 2 / 2)) / 2) / (2 * Real.pi) = 0 := by
    have h1 : 2 * (Real.log 2 / 2) = Real.log 2 := by ring
    rw [h1, Real.exp_log (by norm_num), div_self (by norm_num), Real.arccos_one, zero_div]
  rwa [harc, zero_add] at hres

/-- **Corollary 1.3(iii)**: In the `q`-aspect at `s = 1/2`, normalized `log L(1/2, χ)` lies in the
`ε`-neighborhood of `Ω` for `q ≥ q₀(ε)`. -/
theorem corollary_1_3_iii (D : LFunctionData) :
    ∀ ε > 0, ∃ q₀ : ℕ, q₀ ≥ 10 ∧
      ∀ (q : ℕ) (hq1 : q ≥ 1), q ≥ q₀ → ∀ (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive),
        D.GRH q hq1 χ hχ →
        D.nonvanishing q χ 0 →
        let scale := Real.log (q : ℝ) / Real.log (Real.log (q : ℝ))
        ∃ w ∈ convexOmega, ‖(⟨D.logAbsL q χ 0 / scale, (Real.pi * D.S_val q χ 0) / scale⟩ : ℂ) - w‖ < ε := by
  sorry

end PolarEvaluation
