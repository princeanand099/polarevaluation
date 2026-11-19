import PolarEvaluation.Basic
import PolarEvaluation.ExternalResults
import PolarEvaluation.ExplicitFormulae
import PolarEvaluation.ShiftedLattice
import PolarEvaluation.PrimeMoments

/-!
# Large-Deviation Bounds in the t-Aspect (Theorem 1.4)
-/

noncomputable section

open Complex Real MeasureTheory Filter Topology Classical

namespace PolarEvaluation

lemma ld_integral_univ_inv_one_add_sq : ∫ x : ℝ, (1 + x ^ 2)⁻¹ = Real.pi := by
  have h_tend := intervalIntegral_tendsto_integral integrable_inv_one_add_sq tendsto_neg_atTop_atBot tendsto_id
  have h_eq : (fun R : ℝ => ∫ x in (-R)..id R, (1 + x ^ 2)⁻¹) = fun R : ℝ => Real.arctan R - Real.arctan (-R) := by
    ext R; exact integral_inv_one_add_sq
  rw [h_eq] at h_tend
  have h_lim : Tendsto (fun R : ℝ => Real.arctan R - Real.arctan (-R)) atTop (𝓝 (Real.pi / 2 - -(Real.pi / 2))) :=
    (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).sub ((tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp tendsto_neg_atTop_atBot)
  have h_pi : Real.pi / 2 - -(Real.pi / 2) = Real.pi := by ring
  rw [h_pi] at h_lim
  exact tendsto_nhds_unique h_tend h_lim

/-- Helper: `S(t, χ)` horizontal zero-sum at `θ = π / 2` obtained by dominated convergence
as `θ → π / 2` from `horizontal_zero_sum_external`. -/
lemma S_val_horizontal_zero_sum (D : LFunctionData) :
    ∃ C₀ : ℝ, C₀ > 0 ∧
      ∀ (q : ℕ) (hq : q ≥ 1) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive),
        D.GRH q hq χ hχ →
        ∀ (t : ℝ), D.nonvanishing q χ t → (q = 1 → |t| ≥ 10) →
          Summable (fun n : ℕ => kernelK (Real.pi / 2) (t - D.zeros q χ n)) ∧
          |Real.pi * D.S_val q χ t -
            ∑' n : ℕ => kernelK (Real.pi / 2) (t - D.zeros q χ n)| ≤ C₀ := by
  obtain ⟨C₀, hC₀, h_hzs⟩ := horizontal_zero_sum_external D
  refine ⟨C₀, hC₀, fun q hq χ hχ hGRH t ht hq1 => ?_⟩
  have h0 := h_hzs q hq χ hχ hGRH 0 (by simp; positivity) t ht hq1
  have hK_dom : ∀ (θ x : ℝ), x ≠ 0 → |kernelK θ x| ≤ 13 * (-kernelK 0 x) := by
    intro θ x hx
    have hK0_neg : 0 < -kernelK 0 x := by
      unfold kernelK
      simp only [Real.cos_zero, Real.sin_zero, zero_mul, add_zero]
      have h1 : 1 < (x ^ 2 + 1) / x ^ 2 := by
        rw [lt_div_iff₀ (sq_pos_of_ne_zero hx)]; linarith
      have := Real.log_pos h1
      linarith
    have hKpi_le : |kernelK (Real.pi / 2) x| ≤ 12 * (-kernelK 0 x) := by
      unfold kernelK
      simp only [Real.cos_pi_div_two, zero_div, neg_zero, zero_mul, zero_add, Real.sin_pi_div_two, one_mul]
      rcases le_or_gt 1 |x| with hx1 | hx1
      · have h_ar : |Real.arctan (1 / x) - x / (x ^ 2 + 1)| ≤ 2 / x ^ 2 := by
          have h := kernelK_bound_large (Real.pi / 2) hx1
          unfold kernelK at h
          simpa using h
        have h_log : 1 / x ^ 2 ≤ 2 * Real.log ((x ^ 2 + 1) / x ^ 2) := by
          have hu_pos : 0 < 1 / x ^ 2 := by positivity
          have hu_le : 1 / x ^ 2 ≤ 1 := by
            rw [div_le_one (sq_pos_of_ne_zero hx), ← sq_abs x]; nlinarith
          have h_eq : (x ^ 2 + 1) / x ^ 2 = 1 + 1 / x ^ 2 := by field_simp [hx]
          rw [h_eq]
          have h_l := Real.one_sub_inv_le_log_of_pos (by positivity : 0 < 1 + 1 / x ^ 2)
          have h_l2 : (1 / x ^ 2) / (1 + 1 / x ^ 2) = 1 - (1 + 1 / x ^ 2)⁻¹ := by
            field_simp [(by positivity : (0 : ℝ) < 1 + 1 / x ^ 2)]; ring
          have h_l3 : (1 / x ^ 2) / 2 ≤ (1 / x ^ 2) / (1 + 1 / x ^ 2) :=
            div_le_div_of_nonneg_left hu_pos (by positivity) (by linarith)
          linarith
        have h_k0 : -kernelK 0 x = (1 / 2 : ℝ) * Real.log ((x ^ 2 + 1) / x ^ 2) := by
          unfold kernelK; simp; ring
        linarith
      · have h_ar : |Real.arctan (1 / x) - x / (x ^ 2 + 1)| ≤ 3 := by
          have h1 : |Real.arctan (1 / x)| ≤ Real.pi / 2 := (Real.abs_arctan_lt_pi_div_two _).le
          have h2 : |x / (x ^ 2 + 1)| ≤ 1 := by
            rw [abs_div, abs_of_pos (by positivity : 0 < x ^ 2 + 1)]
            exact div_le_one_of_le₀ (by linarith [sq_nonneg x]) (by positivity)
          linarith [Real.pi_lt_four]
        have h_log : 1 / 4 ≤ -kernelK 0 x := by
          have h_k0 : -kernelK 0 x = (1 / 2 : ℝ) * Real.log ((x ^ 2 + 1) / x ^ 2) := by
            unfold kernelK; simp; ring
          have h1 : 2 ≤ (x ^ 2 + 1) / x ^ 2 := by
            rw [le_div_iff₀ (sq_pos_of_ne_zero hx)]
            have : x ^ 2 ≤ 1 := by rw [← sq_abs x]; nlinarith [abs_nonneg x]
            linarith
          have h2 : 1 / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
          have h3 := Real.log_le_log (by norm_num) h1
          linarith
        linarith
    have hK0_abs : |kernelK 0 x| = -kernelK 0 x := abs_of_neg (by linarith)
    have h_tri : |kernelK θ x| ≤ |Real.cos θ| * |kernelK 0 x| + |Real.sin θ| * |kernelK (Real.pi / 2) x| := by
      have heq : kernelK θ x = Real.cos θ * kernelK 0 x + Real.sin θ * kernelK (Real.pi / 2) x := by
        unfold kernelK; simp; ring
      rw [heq]
      refine (abs_add_le _ _).trans (add_le_add (by rw [abs_mul]) (by rw [abs_mul]))
    calc |kernelK θ x| ≤ 1 * |kernelK 0 x| + 1 * |kernelK (Real.pi / 2) x| := by
          gcongr
          · exact Real.abs_cos_le_one θ
          · exact Real.abs_sin_le_one θ
      _ ≤ (-kernelK 0 x) + 12 * (-kernelK 0 x) := by linarith
      _ = 13 * (-kernelK 0 x) := by ring
  have h_summ_dom : Summable (fun n : ℕ => 13 * (-kernelK 0 (t - D.zeros q χ n))) :=
    h0.1.neg.mul_left 13
  have h_summ_pi2 : Summable (fun n : ℕ => kernelK (Real.pi / 2) (t - D.zeros q χ n)) := by
    refine h_summ_dom.of_norm_bounded fun n => ?_
    rw [Real.norm_eq_abs]
    have hne := sub_ne_zero.mpr (D.nonvanishing_zeros q χ t ht n)
    have h1 := hK_dom (Real.pi / 2) (t - D.zeros q χ n) hne
    exact h1
  refine ⟨h_summ_pi2, ?_⟩
  let θ_seq : ℕ → ℝ := fun k => Real.pi / 2 - 1 / (k + 3 : ℝ)
  have hθ_lt : ∀ k : ℕ, |θ_seq k| < Real.pi / 2 := by
    intro k
    dsimp only [θ_seq]
    rw [abs_lt]
    have h1 : (1 : ℝ) / (k + 3 : ℝ) ≤ 1 / 3 := by
      gcongr; linarith
    constructor <;> linarith [Real.two_le_pi]
  have hθ_tend : Tendsto θ_seq atTop (nhds (Real.pi / 2)) := by
    have h0 : Tendsto (fun k : ℕ => (1 : ℝ) / (k + 3 : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa [θ_seq] using tendsto_const_nhds.sub h0
  have h_tsum_tend : Tendsto (fun k : ℕ => ∑' n : ℕ, kernelK (θ_seq k) (t - D.zeros q χ n))
      atTop (nhds (∑' n : ℕ, kernelK (Real.pi / 2) (t - D.zeros q χ n))) := by
    refine tendsto_tsum_of_dominated_convergence h_summ_dom (fun n => ?_) (fun k n => ?_)
    · have hne := sub_ne_zero.mpr (D.nonvanishing_zeros q χ t ht n)
      have h_cont : Continuous (fun θ : ℝ => kernelK θ (t - D.zeros q χ n)) := by
        unfold kernelK; fun_prop
      exact h_cont.continuousAt.tendsto.comp hθ_tend
    · rw [Real.norm_eq_abs]
      exact hK_dom (θ_seq k) (t - D.zeros q χ n) (sub_ne_zero.mpr (D.nonvanishing_zeros q χ t ht n))
  have h_lhs_tend : Tendsto (fun k : ℕ => polarLogL D q χ t (θ_seq k) -
      ((Real.cos (θ_seq k) / 2) * Real.log (analyticConductor q t) +
        ∑' n : ℕ, kernelK (θ_seq k) (t - D.zeros q χ n)))
      atTop (nhds (Real.pi * D.S_val q χ t -
        ∑' n : ℕ, kernelK (Real.pi / 2) (t - D.zeros q χ n))) := by
    have h1 : Tendsto (fun k : ℕ => polarLogL D q χ t (θ_seq k)) atTop (nhds (Real.pi * D.S_val q χ t)) := by
      unfold polarLogL
      have hc := (Real.continuous_cos.continuousAt.tendsto.comp hθ_tend).mul_const (D.logAbsL q χ t)
      have hs := (Real.continuous_sin.continuousAt.tendsto.comp hθ_tend).mul_const (Real.pi * D.S_val q χ t)
      simpa [Real.cos_pi_div_two, Real.sin_pi_div_two] using hc.add hs
    have h2 : Tendsto (fun k : ℕ => (Real.cos (θ_seq k) / 2) * Real.log (analyticConductor q t)) atTop (nhds 0) := by
      have hc := ((Real.continuous_cos.continuousAt.tendsto.comp hθ_tend).div_const 2).mul_const
        (Real.log (analyticConductor q t))
      simpa [Real.cos_pi_div_two] using hc
    simpa using h1.sub (h2.add h_tsum_tend)
  exact le_of_tendsto h_lhs_tend.abs (Eventually.of_forall fun k =>
    (h_hzs q hq χ hχ hGRH (θ_seq k) (hθ_lt k) t ht hq1).2)

/-- Helper: `t`-aspect large-deviation reduction from `polarLogL` to `primeSum1`. -/
private lemma t_aspect_polar_ld_core (D : LFunctionData) (q : ℕ) (hq : q ≥ 1)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hGRH : D.GRH q hq χ hχ)
    (θ : ℝ) (hθ : |θ| < Real.pi / 2) :
    ∃ (c A T₀ : ℝ), c > 0 ∧ A > 1 ∧ T₀ ≥ 100 ∧
      ∀ (T V : ℝ), T ≥ T₀ →
        A * Real.log (Real.log T) ≤ V → V ≤ Real.log T / Real.log (Real.log T) →
        (1 / T) * (volume { t ∈ Set.Icc T (2 * T) |
          D.nonvanishing q χ t ∧ polarLogL D q χ t θ ≥ V }).toReal ≤
          Real.exp (-c * V * Real.log (V / Real.log (Real.log T))) := by
  obtain ⟨C₀, hC₀, h_hzs⟩ := horizontal_zero_sum_external D
  obtain ⟨C₁, hC₁, h_gw⟩ := guinand_weil_external D
  obtain ⟨Δ₀, C_sup, C_L1, C_err_M, hΔ₀, hC_sup, hC_L1, hC_err_M, h_maj⟩ := asymmetric_majorant θ hθ
  have hK_int := kernelK_integrable θ
  have hK_int_val : ∫ x : ℝ, kernelK θ x = -Real.pi * Real.cos θ := kernelK_integral_eq θ
  let C_L1_tot : ℝ := max C_L1 (2 * envelopeC θ + C_err_M + 1)
  obtain ⟨C_tail, hC_tail, h_tail⟩ := prime_power_tail_bounds θ C_L1_tot Δ₀ hθ.le hΔ₀
  obtain ⟨B, hB, h_mom⟩ := prime_moment_t_aspect θ C_L1_tot Δ₀ hθ.le hΔ₀
  have hC_env : 0 < envelopeC θ := envelopeC_pos hθ
  let K_scale : ℝ := max 1 (2 * envelopeC θ / Real.pi)
  have hK_scale_pos : 0 < K_scale := by positivity
  let C_B : ℝ := 16 * B * (2 * Real.pi * K_scale)
  let A : ℝ := max 2 (max (Real.exp 1 * C_B + 1) (max (C_B ^ 2 + 1) (8 * C_tail + 8 * C₀ + 8 * C₁ * C_sup + 8 * C_err_M + 8)))
  have hA_gt_1 : A > 1 := by linarith [le_max_left (2 : ℝ) (max (Real.exp 1 * C_B + 1) (max (C_B ^ 2 + 1) (8 * C_tail + 8 * C₀ + 8 * C₁ * C_sup + 8 * C_err_M + 8)))]
  let L_min : ℝ := max (max 100 (Real.pi * Δ₀ / K_scale + 1)) (max (16 * Real.pi * K_scale) 10)
  let T₀ : ℝ := max (max 100 ((q : ℝ) * 4 + 4)) (Real.exp (Real.exp L_min))
  have hT₀_ge : T₀ ≥ 100 := le_trans (le_max_left _ _) (le_max_left _ _)
  let c : ℝ := 1 / (8 * (2 * Real.pi * K_scale))
  refine ⟨c, A, T₀, by positivity, hA_gt_1, hT₀_ge, fun T V hT hV_lb hV_ub => ?_⟩
  have hT_ge_100 : 100 ≤ T := le_trans hT₀_ge hT
  have hT_pos : 0 < T := by linarith
  have hT_ge_exp : Real.exp (Real.exp L_min) ≤ T := le_trans (le_max_right _ _) hT
  have hlogT_ge_exp : Real.exp L_min ≤ Real.log T := by
    rw [← Real.log_exp (Real.exp L_min)]
    exact Real.log_le_log (Real.exp_pos _) hT_ge_exp
  have hLLT_ge : L_min ≤ Real.log (Real.log T) := by
    rw [← Real.log_exp L_min]
    exact Real.log_le_log (Real.exp_pos _) hlogT_ge_exp
  have hLLT_ge_10 : 10 ≤ Real.log (Real.log T) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLLT_ge
  have hlogT_pos : 0 < Real.log T := by linarith [Real.exp_pos L_min]
  have hq_2T : (q : ℝ) * (2 * T + 2) ≤ T ^ 2 := by
    have hq4 : (q : ℝ) * 4 + 4 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
    nlinarith
  have hlog_q2T_le : Real.log ((q : ℝ) * (2 * T + 2)) ≤ 2 * Real.log T := by
    have h1 : Real.log ((q : ℝ) * (2 * T + 2)) ≤ Real.log (T ^ 2) :=
      Real.log_le_log (by positivity) hq_2T
    rwa [Real.log_pow] at h1
  have hlog_q2T_ge : Real.log T ≤ Real.log ((q : ℝ) * (2 * T + 2)) := by
    refine Real.log_le_log hT_pos ?_
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith
  let Δ : ℝ := K_scale * Real.log ((q : ℝ) * (2 * T + 2)) / V
  have hV_pos : 0 < V := by
    have hA_pos : 0 < A := by linarith
    nlinarith
  have hΔ_ge_Δ₀ : Δ₀ ≤ Δ := by
    have h1 : K_scale * Real.log (Real.log T) ≤ Δ := by
      dsimp only [Δ]
      rw [le_div_iff₀ hV_pos]
      have h_v : V * Real.log (Real.log T) ≤ Real.log T := by
        rwa [le_div_iff₀ (by linarith)] at hV_ub
      calc K_scale * Real.log (Real.log T) * V = K_scale * (V * Real.log (Real.log T)) := by ring
        _ ≤ K_scale * Real.log T := by gcongr
        _ ≤ K_scale * Real.log ((q : ℝ) * (2 * T + 2)) := by gcongr
    have h2 : Δ₀ ≤ K_scale * Real.log (Real.log T) := by
      have h_l : Real.pi * Δ₀ / K_scale + 1 ≤ Real.log (Real.log T) :=
        le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLLT_ge
      rw [div_add_one (by positivity), div_le_iff₀ hK_scale_pos] at h_l
      nlinarith [Real.two_le_pi]
    exact h2.trans h1
  have hΔ_ge_1 : 1 ≤ Δ := le_trans hΔ₀ hΔ_ge_Δ₀
  have hΔ_pos : 0 < Δ := by linarith
  let X : ℝ := Real.exp (2 * Real.pi * Δ)
  have hlogX_eq : Real.log X = 2 * Real.pi * Δ := Real.log_exp _
  have hlogX_le_half : Real.log X ≤ Real.log T / 2 := by
    rw [hlogX_eq]
    have h_v : A * Real.log (Real.log T) ≤ V := hV_lb
    have h_l : 16 * Real.pi * K_scale ≤ Real.log (Real.log T) :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLLT_ge
    have h_v2 : 16 * Real.pi * K_scale ≤ V := by
      have : 1 ≤ A := by linarith
      nlinarith
    calc 2 * Real.pi * Δ = 2 * Real.pi * K_scale * Real.log ((q : ℝ) * (2 * T + 2)) / V := by dsimp only [Δ]; ring
      _ ≤ 2 * Real.pi * K_scale * (2 * Real.log T) / V := by gcongr
      _ = (4 * Real.pi * K_scale / V) * Real.log T := by ring
      _ ≤ (1 / 2 : ℝ) * Real.log T := by
          gcongr
          rw [div_le_iff₀ hV_pos]
          linarith
      _ = Real.log T / 2 := by ring
  have hX_le_T : X ≤ T := by
    rw [← Real.log_le_log_iff (Real.exp_pos _) hT_pos, Real.log_exp]
    linarith [hlogX_le_half, hlogX_eq]
  have hX_ge_e : Real.exp 1 ≤ X := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.two_le_pi]
  have hlogX_pos : 0 < Real.log X := by
    rw [hlogX_eq]; positivity
  let k : ℕ := Nat.floor (Real.log T / Real.log X)
  have hk_ge_2 : 2 ≤ k := by
    have h1 : 2 ≤ Real.log T / Real.log X := by
      rw [le_div_iff₀ hlogX_pos]; linarith
    exact Nat.le_floor h1
  have hk_pos : 0 < k := by omega
  have hXk_le_T : X ^ k ≤ T := by
    rw [← Real.log_le_log_iff (pow_pos (Real.exp_pos _) _) hT_pos, Real.log_pow]
    have hk_le := Nat.floor_le (div_nonneg hlogT_pos.le hlogX_pos.le)
    rw [le_div_iff₀ hlogX_pos] at hk_le
    exact hk_le
  have hk_lb : V / (2 * (2 * Real.pi * K_scale)) ≤ k := by
    have h_le : Real.log T / Real.log X < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have h_k2 : Real.log T / Real.log X / 2 ≤ (k : ℝ) := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk_ge_2
      linarith
    have h_lx : Real.log X ≤ 4 * Real.pi * K_scale * Real.log T / V := by
      rw [hlogX_eq]
      calc 2 * Real.pi * Δ = 2 * Real.pi * K_scale * Real.log ((q : ℝ) * (2 * T + 2)) / V := by dsimp only [Δ]; ring
        _ ≤ 2 * Real.pi * K_scale * (2 * Real.log T) / V := by gcongr
        _ = 4 * Real.pi * K_scale * Real.log T / V := by ring
    have h_div : V / (4 * Real.pi * K_scale) ≤ Real.log T / Real.log X := by
      rw [div_le_div_iff₀ (by positivity) hlogX_pos]
      rw [le_div_iff₀ hV_pos] at h_lx
      nlinarith
    linarith
  have hk_ub : (k : ℝ) ≤ V / (2 * Real.pi * K_scale) := by
    have hk_le := Nat.floor_le (div_nonneg hlogT_pos.le hlogX_pos.le)
    have h_lx : 2 * Real.pi * K_scale * Real.log T / V ≤ Real.log X := by
      rw [hlogX_eq]
      dsimp only [Δ]
      have : Real.log T ≤ Real.log ((q : ℝ) * (2 * T + 2)) := hlog_q2T_ge
      calc 2 * Real.pi * K_scale * Real.log T / V
          ≤ 2 * Real.pi * K_scale * Real.log ((q : ℝ) * (2 * T + 2)) / V := by gcongr
        _ = 2 * Real.pi * (K_scale * Real.log ((q : ℝ) * (2 * T + 2)) / V) := by ring
    calc (k : ℝ) ≤ Real.log T / Real.log X := hk_le
      _ ≤ Real.log T / (2 * Real.pi * K_scale * Real.log T / V) :=
          div_le_div_of_nonneg_left hlogT_pos.le (by positivity) h_lx
      _ = V / (2 * Real.pi * K_scale) := by field_simp [hlogT_pos.ne', hK_scale_pos.ne', Real.pi_ne_zero]; ring
  obtain ⟨α, M_entire, hα, hM_exp, hM_real, hM_int, hM_sup, hM_L1, hM_maj, hM_err⟩ := h_maj Δ hΔ_ge_Δ₀
  let h_hat := fourierHat (fun x : ℝ => (majorantM θ Δ α x : ℂ))
  have hM_L1_diff : ∫ x : ℝ, |majorantM θ Δ α x - kernelK θ x| ≤ C_L1_tot / Δ := by
    have h_eq : ∫ x : ℝ, |majorantM θ Δ α x - kernelK θ x| = ∫ x : ℝ, (majorantM θ Δ α x - kernelK θ x) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_iff.mpr (by simp : volume {x : ℝ | ¬x ≠ 0} = 0)] with x hx
      exact abs_of_nonneg (sub_nonneg.mpr (hM_maj x hx))
    rw [h_eq]
    have h1 : ∫ x : ℝ, (majorantM θ Δ α x - kernelK θ x) ≤ 2 * envelopeC θ / Δ + C_err_M * Real.exp (-2 * Real.pi * Δ) := by
      linarith [(abs_le.mp hM_err).2]
    have h2 : Δ * Real.exp (-2 * Real.pi * Δ) ≤ 1 := by
      have he := Real.add_one_le_exp (2 * Real.pi * Δ)
      have h3 : Δ ≤ Real.exp (2 * Real.pi * Δ) := by nlinarith [Real.two_le_pi]
      rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]; exact h3.trans_eq (one_mul _).symm
    have h3 : Real.exp (-2 * Real.pi * Δ) ≤ 1 / Δ := by rwa [le_div_iff₀ hΔ_pos, mul_comm]
    calc ∫ x : ℝ, (majorantM θ Δ α x - kernelK θ x)
        ≤ 2 * envelopeC θ / Δ + C_err_M * (1 / Δ) := by linarith [mul_le_mul_of_nonneg_left h3 hC_err_M.le]
      _ = (2 * envelopeC θ + C_err_M) / Δ := by ring
      _ ≤ C_L1_tot / Δ := by gcongr; exact le_trans (by linarith) (le_max_right C_L1 _)
  have hM_L1_tot : ∫ x : ℝ, |majorantM θ Δ α x| ≤ C_L1_tot :=
    h_L1.trans (le_max_left _ _)
  have h_tail_bd := h_tail q χ Δ (majorantM θ Δ α) hΔ_ge_Δ₀ hM_int hM_L1_diff hM_L1_tot
  have h_subset : { t ∈ Set.Icc T (2 * T) | D.nonvanishing q χ t ∧ polarLogL D q χ t θ ≥ V } ⊆
      { t ∈ Set.Icc T (2 * T) | |primeSum1 q χ h_hat X t| ≥ V / 4 } := by
    intro t ⟨ht_icc, ht_nv, ht_pol⟩
    refine ⟨ht_icc, ?_⟩
    have hq1_t : q = 1 → |t| ≥ 10 := fun _ => by rw [abs_of_pos (by linarith [ht_icc.1])]; linarith [ht_icc.1]
    obtain ⟨hsumm_K, h_hzs_bd⟩ := h_hzs q hq χ hχ hGRH θ hθ t ht_nv hq1_t
    have hM_im : ∀ x : ℝ, (M_entire x).im = 0 := fun x => (hM_real x).1
    have hM_sup_bd : ∀ x : ℝ, ‖M_entire x‖ ≤ (C_sup * Real.log Δ) / (1 + x ^ 2) := by
      intro x
      have hre : M_entire x = ((majorantM θ Δ α x : ℝ) : ℂ) := Complex.ext (hM_real x).2 (hM_real x).1
      rw [hre, Complex.norm_real, Real.norm_eq_abs, le_div_iff₀ (by positivity : 0 < 1 + x ^ 2), mul_comm]
      exact hM_sup x
    obtain ⟨hsumm_M, h_gw_bd⟩ := h_gw q hq χ hχ hGRH M_entire Δ (C_sup * Real.log Δ)
      hΔ_ge_1 (mul_nonneg hC_sup.le (Real.log_nonneg hΔ_ge_1)) hM_exp hM_sup_bd hM_im t hq1_t
    have h_sum_le : ∑' n : ℕ, kernelK θ (t - D.zeros q χ n) ≤ ∑' n : ℕ, (M_entire (t - D.zeros q χ n)).re := by
      refine Summable.tsum_le_tsum (fun n => ?_) hsumm_K hsumm_M
      rw [(hM_real _).2]; exact hM_maj _ (sub_ne_zero.mpr (D.nonvanishing_zeros q χ t ht_nv n))
    have hM_int_re : (∫ x : ℝ, (M_entire x).re) = (∫ x : ℝ, majorantM θ Δ α x - kernelK θ x) + (-Real.pi * Real.cos θ) := by
      have heq_M : (fun x : ℝ => (M_entire x).re) = fun x => majorantM θ Δ α x := funext fun x => (hM_real x).2
      rw [heq_M, ← hK_int_val, ← integral_add hM_int hK_int]
      congr 1; ext x; ring
    have h_hat_eq : fourierHat (fun x : ℝ => M_entire x) = h_hat := by
      ext ξ; unfold fourierHat; congr 1; ext x
      have hre : M_entire x = ((majorantM θ Δ α x : ℝ) : ℂ) := Complex.ext (hM_real x).2 (hM_real x).1
      rw [hre]
    rw [h_hat_eq] at h_gw_bd
    set Q : ℝ := analyticConductor q t
    have hQ_le : Q ≤ (q : ℝ) * (2 * T + 2) := by
      dsimp only [Q, analyticConductor]
      have ht_abs : |t| ≤ 2 * T := by rw [abs_of_pos (by linarith [ht_icc.1])]; exact ht_icc.2
      gcongr
    have hQ_ge_100 : 100 ≤ Q := by
      dsimp only [Q, analyticConductor]
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
      have ht1 : 100 ≤ |t| := by rw [abs_of_pos (by linarith [ht_icc.1])]; exact ht_icc.1
      nlinarith
    have h_main_int : (Real.log Q / (2 * Real.pi)) * (∫ x : ℝ, (M_entire x).re) ≤
        -(Real.cos θ / 2) * Real.log Q + envelopeC θ * (Real.log Q / (Real.pi * Δ)) +
        (Real.log Q / (2 * Real.pi)) * (C_err_M * Real.exp (-2 * Real.pi * Δ)) := by
      rw [hM_int_re]
      have h1 : ∫ x : ℝ, majorantM θ Δ α x - kernelK θ x ≤ 2 * envelopeC θ / Δ + C_err_M * Real.exp (-2 * Real.pi * Δ) := by
        linarith [(abs_le.mp hM_err).2]
      have h2 : 0 ≤ Real.log Q / (2 * Real.pi) := div_nonneg (Real.log_nonneg (by linarith)) (by positivity)
      calc (Real.log Q / (2 * Real.pi)) * ((∫ x : ℝ, majorantM θ Δ α x - kernelK θ x) + (-Real.pi * Real.cos θ))
          ≤ (Real.log Q / (2 * Real.pi)) * ((2 * envelopeC θ / Δ + C_err_M * Real.exp (-2 * Real.pi * Δ)) + (-Real.pi * Real.cos θ)) := by
            gcongr
        _ = _ := by field_simp [Real.pi_ne_zero]; ring
    have h_env_le : envelopeC θ * (Real.log Q / (Real.pi * Δ)) ≤ V / 2 := by
      have h_logQ : Real.log Q ≤ Real.log ((q : ℝ) * (2 * T + 2)) :=
        Real.log_le_log (by linarith) hQ_le
      have h_k : 2 * envelopeC θ / Real.pi ≤ K_scale := le_max_right _ _
      calc envelopeC θ * (Real.log Q / (Real.pi * Δ))
          ≤ envelopeC θ * (Real.log ((q : ℝ) * (2 * T + 2)) / (Real.pi * Δ)) := by gcongr
        _ = (envelopeC θ / (Real.pi * K_scale)) * V := by
            dsimp only [Δ]; field_simp [Real.pi_ne_zero, hK_scale_pos.ne', hV_pos.ne']; ring
        _ ≤ (1 / 2 : ℝ) * V := by
            gcongr; rw [div_le_iff₀ (by positivity)]; linarith
        _ = V / 2 := by ring
    have h_exp_err : (Real.log Q / (2 * Real.pi)) * (C_err_M * Real.exp (-2 * Real.pi * Δ)) ≤ C_err_M * Real.log (Real.log T) := by
      have h_2piΔ : Real.log (Real.log T) ≤ 2 * Real.pi * Δ := by
        have h_1 : 1 ≤ Real.pi * K_scale := by nlinarith [Real.two_le_pi, show 1 ≤ K_scale by exact le_max_left _ _]
        have h_v : V * Real.log (Real.log T) ≤ Real.log T := by rwa [le_div_iff₀ (by linarith)] at hV_ub
        calc Real.log (Real.log T) ≤ Real.pi * K_scale * Real.log (Real.log T) := le_mul_of_one_le_left (by linarith) h_1
          _ ≤ 2 * Real.pi * (K_scale * Real.log ((q : ℝ) * (2 * T + 2)) / V) := by
              rw [le_div_iff₀ hV_pos]
              calc Real.pi * K_scale * Real.log (Real.log T) * V = Real.pi * K_scale * (V * Real.log (Real.log T)) := by ring
                _ ≤ Real.pi * K_scale * Real.log T := by gcongr
                _ ≤ 2 * Real.pi * K_scale * Real.log ((q : ℝ) * (2 * T + 2)) := by
                    nlinarith [hlog_q2T_ge, Real.pi_pos]
      have h_exp_lt : Real.exp (-2 * Real.pi * Δ) ≤ 1 / Real.log T := by
        rw [Real.exp_neg, inv_eq_one_div]
        exact div_le_div_of_nonneg_left zero_le_one hlogT_pos (by
          calc Real.log T = Real.exp (Real.log (Real.log T)) := (Real.exp_log hlogT_pos).symm
            _ ≤ Real.exp (2 * Real.pi * Δ) := Real.exp_le_exp.mpr h_2piΔ)
      have h_logQ_le : Real.log Q ≤ 2 * Real.log T := by
        exact (Real.log_le_log (by linarith) hQ_le).trans hlog_q2T_le
      calc (Real.log Q / (2 * Real.pi)) * (C_err_M * Real.exp (-2 * Real.pi * Δ))
          ≤ (2 * Real.log T / (2 * Real.pi)) * (C_err_M * (1 / Real.log T)) := by gcongr
        _ = C_err_M / Real.pi := by field_simp [hlogT_pos.ne', Real.pi_ne_zero]; ring
        _ ≤ C_err_M * Real.log (Real.log T) := by
            have : 1 / Real.pi ≤ Real.log (Real.log T) := by
              have : 1 / Real.pi ≤ 1 := div_le_one_of_le₀ (by linarith [Real.two_le_pi]) Real.pi_pos.le
              linarith
            nlinarith [hC_err_M]
    have h_gw_err : C₁ * (C_sup * Real.log Δ +
        (if q = 1 then Real.exp (Real.pi * Δ) / t ^ 2 * (C_sup * Real.log Δ) else 0)) ≤
        2 * C₁ * C_sup * Real.log (Real.log T) := by
      have hΔ_le_T : Δ ≤ Real.log T := by
        dsimp only [Δ]
        calc K_scale * Real.log ((q : ℝ) * (2 * T + 2)) / V ≤ K_scale * (2 * Real.log T) / V := by gcongr
          _ = (2 * K_scale / V) * Real.log T := by ring
          _ ≤ 1 * Real.log T := by
              gcongr; rw [div_le_one hV_pos]
              have h_l : 16 * Real.pi * K_scale ≤ Real.log (Real.log T) :=
                le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLLT_ge
              have : 1 ≤ A := by linarith
              nlinarith [Real.two_le_pi]
          _ = Real.log T := one_mul _
      have h_logΔ : Real.log Δ ≤ Real.log (Real.log T) := Real.log_le_log hΔ_pos hΔ_le_T
      have h_if : (if q = 1 then Real.exp (Real.pi * Δ) / t ^ 2 * (C_sup * Real.log Δ) else 0) ≤ C_sup * Real.log Δ := by
        split_ifs
        · have h_e : Real.exp (Real.pi * Δ) ≤ T := by
            have : Real.pi * Δ ≤ 2 * Real.pi * Δ := by nlinarith [Real.pi_pos]
            exact (Real.exp_le_exp.mpr this).trans hX_le_T
          have h_t2 : T ≤ t ^ 2 := by
            have : T ≤ t := ht_icc.1
            nlinarith
          have h_div : Real.exp (Real.pi * Δ) / t ^ 2 ≤ 1 := div_le_one_of_le₀ (h_e.trans h_t2) (sq_nonneg t)
          exact mul_le_of_le_one_left (mul_nonneg hC_sup.le (Real.log_nonneg hΔ_ge_1)) h_div
        · exact mul_nonneg hC_sup.le (Real.log_nonneg hΔ_ge_1)
      nlinarith
    have h_tail_t := h_tail_bd t
    have h_loglogX : Real.log (Real.log X) ≤ Real.log (Real.log T) :=
      Real.log_le_log hlogX_pos (by linarith [hlogX_le_half])
    have h_P_split : primePowerSum q χ h_hat X t =
        primeSum1 q χ h_hat X t + primeSum2 q χ h_hat X t + primeSumGe3 q χ h_hat X t := by
      unfold primeSumGe3; ring
    have h_p23 : |primeSum2 q χ h_hat X t + primeSumGe3 q χ h_hat X t| ≤ 2 * C_tail * Real.log (Real.log T) := by
      have h1 : |primeSum2 q χ h_hat X t| ≤ C_tail * Real.log (Real.log T) :=
        h_tail_t.1.trans (mul_le_mul_of_nonneg_left h_loglogX hC_tail.le)
      have h2 : |primeSumGe3 q χ h_hat X t| ≤ C_tail * Real.log (Real.log T) :=
        h_tail_t.2.trans (le_mul_of_one_le_right hC_tail.le (by linarith))
      linarith [abs_add_le (primeSum2 q χ h_hat X t) (primeSumGe3 q χ h_hat X t)]
    have h_C₀_le : C₀ ≤ C₀ * Real.log (Real.log T) := le_mul_of_one_le_right hC₀.le (by linarith)
    have h_tot_err : 2 * C_tail * Real.log (Real.log T) + C₀ + 2 * C₁ * C_sup * Real.log (Real.log T) +
        C_err_M * Real.log (Real.log T) ≤ V / 4 := by
      have h_a : (8 * C_tail + 8 * C₀ + 8 * C₁ * C_sup + 8 * C_err_M + 8) ≤ A :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
      nlinarith
    have h_pol_le : V ≤ V / 2 - primeSum1 q χ h_hat X t + V / 4 := by
      have h_g := (abs_le.mp h_gw_bd).2
      have h_h := (abs_le.mp h_hzs_bd).2
      have h_p := (abs_le.mp h_p23).1
      linarith
    have h_neg : -primeSum1 q χ h_hat X t ≥ V / 4 := by linarith
    exact le_trans h_neg (neg_le_abs _)
  have h_meas_le : (volume { t ∈ Set.Icc T (2 * T) | D.nonvanishing q χ t ∧ polarLogL D q χ t θ ≥ V }).toReal ≤
      (volume { t ∈ Set.Icc T (2 * T) | |primeSum1 q χ h_hat X t| ≥ V / 4 }).toReal := by
    exact ENNReal.toReal_mono (measure_lt_top _ _).ne (measure_mono h_subset)
  let F_t : ℝ → ℝ := fun t => |primeSum1 q χ h_hat X t| ^ (2 * k)
  have hF_cont : Continuous F_t := by
    dsimp only [F_t]; unfold primeSum1
    refine (Continuous.abs (continuous_const.mul (continuous_finset_sum _ fun p _ =>
      continuous_const.mul (Complex.continuous_re.comp ?_)))).pow (2 * k)
    refine Continuous.add ?_ ?_
    · exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))
    · exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))
  have hF_int : IntegrableOn F_t (Set.Icc T (2 * T)) := hF_cont.continuousOn.integrableOn_Icc
  have h_markov : (V / 4) ^ (2 * k) * (volume { t ∈ Set.Icc T (2 * T) | |primeSum1 q χ h_hat X t| ≥ V / 4 }).toReal ≤
      ∫ t in Set.Icc T (2 * T), F_t t := by
    have h_sub_set : { t ∈ Set.Icc T (2 * T) | |primeSum1 q χ h_hat X t| ≥ V / 4 } =
        Set.Icc T (2 * T) ∩ { t : ℝ | (V / 4) ^ (2 * k) ≤ F_t t } := by
      ext t; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, ge_iff_le]
      constructor
      · rintro ⟨ht, h1⟩; exact ⟨ht, pow_le_pow_left₀ (by positivity) h1 (2 * k)⟩
      · rintro ⟨ht, h1⟩
        refine ⟨ht, ?_⟩
        by_contra hlt; push_neg at hlt
        have := pow_lt_pow_left₀ hlt (abs_nonneg _) (by positivity : 2 * k ≠ 0)
        linarith
    rw [h_sub_set]
    have h_m := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict (Set.Icc T (2 * T)))
      (ae_of_all _ fun t => by dsimp only [F_t]; positivity) hF_int ((V / 4) ^ (2 * k))
    simpa [Measure.restrict_apply (hF_cont.measurable (measurableSet_le measurable_const measurable_id) :
      MeasurableSet { t : ℝ | (V / 4) ^ (2 * k) ≤ F_t t }), Set.inter_comm] using h_m
  have h_mom_bd := h_mom q χ Δ T k (majorantM θ Δ α) hq hΔ_ge_Δ₀ (by linarith) hXk_le_T hM_int hM_L1_diff hM_L1_tot
  have h_loglogX : Real.log (Real.log X) ≤ Real.log (Real.log T) :=
    Real.log_le_log hlogX_pos (by linarith [hlogX_le_half])
  have h_base : (4 / V) ^ 2 * (B * k * Real.log (Real.log X)) ≤ C_B * Real.log (Real.log T) / V := by
    calc (4 / V) ^ 2 * (B * k * Real.log (Real.log X))
        ≤ (16 / V ^ 2) * (B * (V / (2 * Real.pi * K_scale)) * Real.log (Real.log T)) := by
          gcongr; ring_nf; rfl
      _ = (8 * B / (Real.pi * K_scale)) * Real.log (Real.log T) / V := by
          field_simp [hV_pos.ne', Real.pi_ne_zero, hK_scale_pos.ne']; ring
      _ ≤ C_B * Real.log (Real.log T) / V := by
          gcongr
          dsimp only [C_B]
          have : 1 ≤ 2 * Real.pi * K_scale := by nlinarith [Real.two_le_pi, show 1 ≤ K_scale by exact le_max_left _ _]
          nlinarith [Real.two_le_pi]
  have h_div_v : (1 / T) * (volume { t ∈ Set.Icc T (2 * T) | D.nonvanishing q χ t ∧ polarLogL D q χ t θ ≥ V }).toReal ≤
      (C_B * Real.log (Real.log T) / V) ^ k := by
    have h1 : (1 / T) * (volume { t ∈ Set.Icc T (2 * T) | |primeSum1 q χ h_hat X t| ≥ V / 4 }).toReal ≤
        ((4 / V) ^ 2 * (B * k * Real.log (Real.log X))) ^ k := by
      have h_pow_pos : 0 < (V / 4) ^ (2 * k) := pow_pos (by positivity) (2 * k)
      calc (1 / T) * (volume { t ∈ Set.Icc T (2 * T) | |primeSum1 q χ h_hat X t| ≥ V / 4 }).toReal
          ≤ (1 / T) * ((∫ t in Set.Icc T (2 * T), F_t t) / (V / 4) ^ (2 * k)) := by
            gcongr; rwa [le_div_iff₀ h_pow_pos, mul_comm]
        _ = (1 / (V / 4) ^ (2 * k)) * ((1 / T) * ∫ t in Set.Icc T (2 * T), F_t t) := by ring
        _ ≤ (1 / (V / 4) ^ (2 * k)) * (B * k * Real.log (Real.log X)) ^ k := by gcongr
        _ = ((4 / V) ^ 2 * (B * k * Real.log (Real.log X))) ^ k := by
            rw [mul_pow, ← pow_mul, mul_comm 2 k, one_div_pow, div_pow, one_div_div]; ring
    exact (mul_le_mul_of_nonneg_left h_meas_le (by positivity)).trans (h1.trans (pow_le_pow_left₀ (by positivity) h_base k))
  have h_ratio_le : C_B * Real.log (Real.log T) / V ≤ (Real.log (Real.log T) / V) ^ (1 / 2 : ℝ) := by
    have h_a : C_B ^ 2 ≤ A := le_trans (by linarith) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
    have h_cb_le : C_B ^ 2 * Real.log (Real.log T) ≤ V := by
      calc C_B ^ 2 * Real.log (Real.log T) ≤ A * Real.log (Real.log T) := by gcongr
        _ ≤ V := hV_lb
    have h_sq : (C_B * Real.log (Real.log T) / V) ^ 2 ≤ Real.log (Real.log T) / V := by
      rw [div_pow, div_le_div_iff₀ (sq_pos_of_pos hV_pos) hV_pos]
      nlinarith [h_cb_le, show 0 ≤ Real.log (Real.log T) by linarith]
    calc C_B * Real.log (Real.log T) / V = Real.sqrt ((C_B * Real.log (Real.log T) / V) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (Real.log (Real.log T) / V) := Real.sqrt_le_sqrt h_sq
      _ = (Real.log (Real.log T) / V) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have h_log_ratio : (1 / 2 : ℝ) * Real.log (V / Real.log (Real.log T)) ≤ -Real.log (C_B * Real.log (Real.log T) / V) := by
    have h1 : Real.log (C_B * Real.log (Real.log T) / V) ≤ (1 / 2 : ℝ) * Real.log (Real.log (Real.log T) / V) := by
      calc Real.log (C_B * Real.log (Real.log T) / V)
          ≤ Real.log ((Real.log (Real.log T) / V) ^ (1 / 2 : ℝ)) := Real.log_le_log (by positivity) h_ratio_le
        _ = (1 / 2 : ℝ) * Real.log (Real.log (Real.log T) / V) := Real.log_rpow (by positivity) _
    have h2 : Real.log (Real.log (Real.log T) / V) = -Real.log (V / Real.log (Real.log T)) := by
      rw [← Real.log_inv, inv_div]
    linarith
  have h_exp_final : (C_B * Real.log (Real.log T) / V) ^ k ≤
      Real.exp (-c * V * Real.log (V / Real.log (Real.log T))) := by
    rw [← Real.exp_log (pow_pos (by positivity) k), Real.log_pow]
    apply Real.exp_le_exp.mpr
    have h_v_log : 0 ≤ Real.log (V / Real.log (Real.log T)) := by
      apply Real.log_nonneg
      rw [one_le_div (by linarith)]
      have : 1 ≤ A := by linarith
      nlinarith
    calc (k : ℝ) * Real.log (C_B * Real.log (Real.log T) / V)
        ≤ (k : ℝ) * (-(1 / 2 : ℝ) * Real.log (V / Real.log (Real.log T))) := by
          gcongr; linarith
      _ = -(1 / 2 : ℝ) * (k : ℝ) * Real.log (V / Real.log (Real.log T)) := by ring
      _ ≤ -(1 / 2 : ℝ) * (V / (2 * (2 * Real.pi * K_scale))) * Real.log (V / Real.log (Real.log T)) := by
          gcongr
      _ ≤ -c * V * Real.log (V / Real.log (Real.log T)) := by
          dsimp only [c]; ring_nf; linarith [mul_nonneg hV_pos.le h_v_log]
  exact h_div_v.trans h_exp_final

/-- **Theorem 1.4** (`t`-aspect large-deviation bound). -/
theorem t_aspect_large_deviation (D : LFunctionData) (q : ℕ) (hq : q ≥ 1)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hGRH : D.GRH q hq χ hχ)
    (θ : ℝ) (hθ : |θ| < Real.pi / 2) :
    ∃ (c c' A : ℝ), c > 0 ∧ c' > 0 ∧ A > 1 ∧
      (∃ T₀ : ℝ, T₀ ≥ 100 ∧
        ∀ (T V : ℝ), T ≥ T₀ →
          A * Real.log (Real.log T) ≤ V → V ≤ Real.log T / Real.log (Real.log T) →
          (1 / T) * (volume { t ∈ Set.Icc T (2 * T) |
            D.nonvanishing q χ t ∧ polarLogL D q χ t θ ≥ V }).toReal ≤
            Real.exp (-c * V * Real.log (V / Real.log (Real.log T)))) ∧
      (∀ α : ℝ, α > 0 → ∃ T₀ : ℝ, T₀ ≥ 100 ∧
        ∀ T : ℝ, T ≥ T₀ →
          let V := α * Real.sqrt (Real.log T * Real.log (Real.log T))
          V ≤ Real.log T / Real.log (Real.log T) →
          (volume { t ∈ Set.Icc T (2 * T) |
            D.nonvanishing q χ t ∧ polarLogL D q χ t θ ≥ V }).toReal ≤
            T * Real.exp (-c' * α * Real.sqrt (Real.log T) * (Real.log (Real.log T)) ^ (3 / 2 : ℝ))) := by
  obtain ⟨c, A, T₀, hc, hA, hT₀, h_part1⟩ := t_aspect_polar_ld_core D q hq χ hχ hGRH θ hθ
  refine ⟨c, c / 4, A, hc, by positivity, hA, ⟨T₀, hT₀, h_part1⟩, fun α hα => ?_⟩
  let L_α : ℝ := max 100 (max ((A / α) ^ 2) ((Real.exp 1 / α) ^ 4))
  let T₁ : ℝ := max T₀ (Real.exp (Real.exp L_α))
  refine ⟨T₁, le_trans hT₀ (le_max_left _ _), fun T hT V hV_ub => ?_⟩
  have hT_ge_T₀ : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hT_ge_exp : Real.exp (Real.exp L_α) ≤ T := le_trans (le_max_right _ _) hT
  have hlogT_ge : Real.exp L_α ≤ Real.log T := by
    rw [← Real.log_exp (Real.exp L_α)]; exact Real.log_le_log (Real.exp_pos _) hT_ge_exp
  have hLLT_ge : L_α ≤ Real.log (Real.log T) := by
    rw [← Real.log_exp L_α]; exact Real.log_le_log (Real.exp_pos _) hlogT_ge
  have hT_pos : 0 < T := by linarith [hT₀, hT_ge_T₀]
  have hLLT_pos : 0 < Real.log (Real.log T) := by linarith [le_max_left (100 : ℝ) (max ((A / α) ^ 2) ((Real.exp 1 / α) ^ 4))]
  have hlogT_pos : 0 < Real.log T := by linarith [Real.exp_pos L_α]
  have h_ratio_ge : (Real.log T / Real.log (Real.log T)) ≥ (Real.log (Real.log T)) ^ 2 := by
    have he4 := Real.pow_div_factorial_le_exp (Real.log (Real.log T)) hLLT_pos.le 4
    have h3 : (Real.log (Real.log T)) ^ 4 / 24 ≤ Real.log T := by
      calc (Real.log (Real.log T)) ^ 4 / 24 = (Real.log (Real.log T)) ^ 4 / Nat.factorial 4 := by norm_num
        _ ≤ Real.exp (Real.log (Real.log T)) := he4
        _ = Real.log T := Real.exp_log hlogT_pos
    have h_llt : 24 ≤ Real.log (Real.log T) := by linarith [le_max_left (100 : ℝ) (max ((A / α) ^ 2) ((Real.exp 1 / α) ^ 4))]
    rw [ge_iff_le, le_div_iff₀ hLLT_pos]
    nlinarith [pow_nonneg hLLT_pos.le 3]
  have hV_lb : A * Real.log (Real.log T) ≤ V := by
    have h1 : (A / α) ^ 2 ≤ Real.log (Real.log T) :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hLLT_ge)
    have h2 : A / α ≤ Real.sqrt (Real.log (Real.log T)) := by
      calc A / α = Real.sqrt ((A / α) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (Real.log (Real.log T)) := Real.sqrt_le_sqrt h1
    have h3 : Real.log (Real.log T) ≤ Real.sqrt (Real.log T / Real.log (Real.log T)) := by
      rw [← Real.sqrt_sq hLLT_pos.le]
      exact Real.sqrt_le_sqrt h_ratio_ge
    have h4 : A / α ≤ Real.sqrt (Real.log T / Real.log (Real.log T)) := by
      have : 1 ≤ Real.log (Real.log T) := by linarith [le_max_left (100 : ℝ) (max ((A / α) ^ 2) ((Real.exp 1 / α) ^ 4))]
      calc A / α ≤ Real.sqrt (Real.log (Real.log T)) := h2
        _ ≤ Real.log (Real.log T) := by
            rw [← Real.sqrt_sq hLLT_pos.le]; exact Real.sqrt_le_sqrt (by nlinarith)
        _ ≤ Real.sqrt (Real.log T / Real.log (Real.log T)) := h3
    have h5 : V / Real.log (Real.log T) = α * Real.sqrt (Real.log T / Real.log (Real.log T)) := by
      dsimp only [V]
      rw [Real.sqrt_mul hlogT_pos.le, Real.sqrt_div hlogT_pos.le]
      field_simp [hLLT_pos.ne']
      rw [← Real.sq_sqrt hLLT_pos.le]; ring
    rw [← div_le_iff₀ hLLT_pos]
    rw [h5, ← div_le_iff₀' hα]
    exact h4
  have h_p1 := h_part1 T V hT_ge_T₀ hV_lb hV_ub
  have h_log_v : (1 / 4 : ℝ) * Real.log (Real.log T) ≤ Real.log (V / Real.log (Real.log T)) := by
    have h_v_eq : V / Real.log (Real.log T) = α * Real.sqrt (Real.log T / Real.log (Real.log T)) := by
      dsimp only [V]
      rw [Real.sqrt_mul hlogT_pos.le, Real.sqrt_div hlogT_pos.le]
      field_simp [hLLT_pos.ne']
      rw [← Real.sq_sqrt hLLT_pos.le]; ring
    have h_ge_exp : (Real.log (Real.log T)) ^ (1 / 4 : ℝ) ≤ α * Real.sqrt (Real.log T / Real.log (Real.log T)) := by
      have h1 : (Real.exp 1 / α) ^ 4 ≤ Real.log (Real.log T) :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hLLT_ge)
      have h2 : Real.exp 1 / α ≤ (Real.log (Real.log T)) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast (Real.exp 1 / α) 4] at h1
        have := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
        rwa [← Real.rpow_mul (by positivity), show (4 : ℕ) * (1 / 4 : ℝ) = 1 by norm_num, Real.rpow_one] at this
      have h3 : (Real.log (Real.log T)) ^ (1 / 2 : ℝ) ≤ Real.sqrt (Real.log T / Real.log (Real.log T)) := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.sqrt_le_sqrt (by
          have : 1 ≤ Real.log (Real.log T) := by linarith [le_max_left (100 : ℝ) (max ((A / α) ^ 2) ((Real.exp 1 / α) ^ 4))]
          nlinarith [h_ratio_ge])
      have h4 : (Real.log (Real.log T)) ^ (1 / 4 : ℝ) * (Real.log (Real.log T)) ^ (1 / 4 : ℝ) =
          (Real.log (Real.log T)) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hLLT_pos]; norm_num
      have h5 : 1 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      calc (Real.log (Real.log T)) ^ (1 / 4 : ℝ)
          = 1 * (Real.log (Real.log T)) ^ (1 / 4 : ℝ) := (one_mul _).symm
        _ ≤ Real.exp 1 * (Real.log (Real.log T)) ^ (1 / 4 : ℝ) := by gcongr
        _ = α * ((Real.exp 1 / α) * (Real.log (Real.log T)) ^ (1 / 4 : ℝ)) := by field_simp [hα.ne']
        _ ≤ α * ((Real.log (Real.log T)) ^ (1 / 4 : ℝ) * (Real.log (Real.log T)) ^ (1 / 4 : ℝ)) := by gcongr
        _ = α * (Real.log (Real.log T)) ^ (1 / 2 : ℝ) := by rw [h4]
        _ ≤ α * Real.sqrt (Real.log T / Real.log (Real.log T)) := by gcongr
    rw [h_v_eq]
    calc (1 / 4 : ℝ) * Real.log (Real.log T) = Real.log ((Real.log (Real.log T)) ^ (1 / 4 : ℝ)) :=
          (Real.log_rpow hLLT_pos _).symm
      _ ≤ Real.log (α * Real.sqrt (Real.log T / Real.log (Real.log T))) :=
          Real.log_le_log (by positivity) h_ge_exp
  have h_exp_le : Real.exp (-c * V * Real.log (V / Real.log (Real.log T))) ≤
      Real.exp (-(c / 4) * α * Real.sqrt (Real.log T) * (Real.log (Real.log T)) ^ (3 / 2 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have h_v_eq : V * Real.log (Real.log T) = α * Real.sqrt (Real.log T) * (Real.log (Real.log T)) ^ (3 / 2 : ℝ) := by
      dsimp only [V]
      rw [Real.sqrt_mul hlogT_pos.le, Real.sqrt_eq_rpow (Real.log (Real.log T))]
      have h_32 : (Real.log (Real.log T)) ^ (1 / 2 : ℝ) * Real.log (Real.log T) =
          (Real.log (Real.log T)) ^ (3 / 2 : ℝ) := by
        conv_lhs => rhs; rw [← Real.rpow_one (Real.log (Real.log T))]
        rw [← Real.rpow_add hLLT_pos]; norm_num
      nlinarith [h_32]
    nlinarith [mul_nonneg hc.le (show 0 ≤ V by dsimp only [V]; positivity)]
  rw [← div_le_iff₀' (by positivity : 0 < T)]
  rw [one_div_mul_eq_div] at h_p1
  exact h_p1.trans h_exp_le

end PolarEvaluation
