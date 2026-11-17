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
  intro ε hε
  let f : ℝ → ℝ := fun r => Real.arccos (min 1 (Real.exp (2 * r) / 2))
  have hf_cont : Continuous f := by
    apply Continuous.comp Real.continuous_arccos
    exact continuous_const.min ((Real.continuous_exp.comp (continuous_const.mul continuous_id')).div_const 2)
  have hf_at : f α = Real.arccos (Real.exp (2 * α) / 2) := by
    have hle : Real.exp (2 * α) / 2 ≤ 1 := by
      have : 2 * α ≤ Real.log 2 := by linarith
      calc Real.exp (2 * α) / 2 ≤ Real.exp (Real.log 2) / 2 := by gcongr
        _ = 1 := by rw [Real.exp_log (by norm_num)]; norm_num
    simp [f, min_eq_right hle]
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.mp hf_cont.continuousAt (Real.pi * ε) (by positivity)
  set ε₁ := min (η / 3) (Real.pi * ε / 2)
  have hε₁_pos : 0 < ε₁ := by positivity
  obtain ⟨Q₀, hQ₀, hconf⟩ := convex_domain_confinement D ε₁ hε₁_pos
  refine ⟨η / 3, Q₀, by positivity, hQ₀, fun q hq χ hχ hGRH t ht hcond hlog => ?_⟩
  have hscale : 0 < Real.log (analyticConductor q t) / Real.log (Real.log (analyticConductor q t)) := by
    have h1 : Real.log (analyticConductor q t) ≥ Real.log 100 :=
      Real.log_le_log (by norm_num) (le_trans hQ₀ hcond)
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
  set scale := Real.log (analyticConductor q t) / Real.log (Real.log (analyticConductor q t))
  obtain ⟨w, hw, hzw⟩ := hconf q hq χ hχ hGRH t ht hcond
  have hre : |(normalizedLogL D q χ t - w).re| < ε₁ :=
    (Complex.abs_re_le_norm _).trans_lt hzw
  have him : |(normalizedLogL D q χ t - w).im| < ε₁ :=
    (Complex.abs_im_le_norm _).trans_lt hzw
  have hz_re : (normalizedLogL D q χ t).re ≥ α - η / 3 := by
    simp only [normalizedLogL]
    rw [ge_iff_le, le_div_iff₀ hscale]
    exact hlog
  have hw_re : w.re > α - η / 3 - ε₁ := by
    have : (normalizedLogL D q χ t - w).re = (normalizedLogL D q χ t).re - w.re := rfl
    linarith [(abs_lt.mp hre).2]
  have hw_im_bd : |w.im| < Real.pi / 4 := hw.1
  have hw_exp : Real.exp (2 * w.re) ≤ 2 * Real.cos (2 * w.im) := hw.2
  have hcos_ge : min 1 (Real.exp (2 * (α - η / 3 - ε₁)) / 2) ≤ Real.cos (2 * w.im) := by
    refine le_trans (min_le_right _ _) ?_
    have : Real.exp (2 * (α - η / 3 - ε₁)) ≤ Real.exp (2 * w.re) := by gcongr
    linarith
  have h2wim_nonneg : 0 ≤ 2 * |w.im| := by positivity
  have h2wim_le : 2 * |w.im| ≤ Real.pi := by linarith [abs_nonneg w.im, Real.pi_pos]
  have harccos_eq : 2 * |w.im| = Real.arccos (Real.cos (2 * w.im)) := by
    rw [← Real.cos_abs (2 * w.im), show |2 * w.im| = 2 * |w.im| by rw [abs_mul, abs_of_pos two_pos]]
    exact (Real.arccos_cos h2wim_nonneg h2wim_le).symm
  have harccos_le : Real.arccos (Real.cos (2 * w.im)) ≤ f (α - η / 3 - ε₁) := by
    apply Real.arccos_le_arccos
    · have : 0 ≤ min 1 (Real.exp (2 * (α - η / 3 - ε₁)) / 2) := le_min (by norm_num) (by positivity)
      linarith
    · exact hcos_ge
    · exact Real.cos_le_one _
  have hdist : dist (α - η / 3 - ε₁) α < η := by
    rw [Real.dist_eq, show α - η / 3 - ε₁ - α = -(η / 3 + ε₁) by ring, abs_neg,
      abs_of_pos (by positivity)]
    have : ε₁ ≤ η / 3 := min_le_left _ _
    linarith
  have hf_lt : f (α - η / 3 - ε₁) < Real.arccos (Real.exp (2 * α) / 2) + Real.pi * ε := by
    have h1 := hcont hdist
    rw [Real.dist_eq, hf_at] at h1
    linarith [(abs_lt.mp h1).2]
  have hw_im_le : |w.im| ≤ Real.arccos (Real.exp (2 * α) / 2) / 2 + Real.pi * ε / 2 := by
    linarith
  have hz_im_le : |(normalizedLogL D q χ t).im| ≤
      Real.arccos (Real.exp (2 * α) / 2) / 2 + Real.pi * ε := by
    have him' : |(normalizedLogL D q χ t).im - w.im| < ε₁ := him
    have htri : |(normalizedLogL D q χ t).im| ≤ |w.im| + |(normalizedLogL D q χ t).im - w.im| := by
      simpa [add_comm] using abs_le_abs_add_abs_sub (normalizedLogL D q χ t).im w.im
    have hε₁_le : ε₁ ≤ Real.pi * ε / 2 := min_le_right _ _
    linarith
  have hS_eq : |D.S_val q χ t| = |(normalizedLogL D q χ t).im| * scale / Real.pi := by
    simp only [normalizedLogL]
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hscale]
    field_simp [Real.pi_ne_zero]
  rw [hS_eq]
  calc |(normalizedLogL D q χ t).im| * scale / Real.pi
      ≤ (Real.arccos (Real.exp (2 * α) / 2) / 2 + Real.pi * ε) * scale / Real.pi := by
        gcongr
    _ = (Real.arccos (Real.exp (2 * α) / 2) / (2 * Real.pi) + ε) * scale := by
        field_simp [Real.pi_ne_zero]
        ring

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
    have h1 : Real.log (analyticConductor q t) ≥ Real.log 100 :=
      Real.log_le_log (by norm_num) (le_trans hQ₀ hcond)
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
