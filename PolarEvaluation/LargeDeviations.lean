import PolarEvaluation.Basic
import PolarEvaluation.ExternalResults
import PolarEvaluation.ExplicitFormulae
import PolarEvaluation.ShiftedLattice
import PolarEvaluation.PrimeMoments

/-!
# Large-Deviation Bounds in the t-Aspect and q-Aspect (Section 7 & Theorems 1.4–1.5, Corollary 1.6)
-/

noncomputable section

open Complex Real MeasureTheory Filter Topology Classical

namespace PolarEvaluation

private lemma ld_integral_univ_inv_one_add_sq : ∫ x : ℝ, (1 + x ^ 2)⁻¹ = Real.pi := by
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
private lemma S_val_horizontal_zero_sum (D : LFunctionData) :
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
  -- Use C_L1_tot ≥ C_L1 + 2 * envelopeC θ / Δ₀ + C_err_M so ∫ |M - K| ≤ C_L1_tot / Δ!
  let C_L1_tot : ℝ := max C_L1 (2 * envelopeC θ + C_err_M + 1)
  obtain ⟨C_tail, hC_tail, h_tail⟩ := prime_power_tail_bounds θ C_L1_tot Δ₀ hθ.le hΔ₀
  obtain ⟨B, hB, h_mom⟩ := prime_moment_t_aspect θ C_L1_tot Δ₀ hθ.le hΔ₀
  have hC_env : 0 < envelopeC θ := envelopeC_pos hθ
  let K_scale : ℝ := max 1 (2 * envelopeC θ / Real.pi)
  have hK_scale_pos : 0 < K_scale := by positivity
  let C_B : ℝ := 16 * B * (2 * Real.pi * K_scale)
  let A : ℝ := max 2 (max (Real.exp 1 * C_B + 1) (max (C_B ^ 2 + 1) (8 * C_tail + 8 * C₀ + 8 * C₁ * C_sup + 8 * C_err_M + 8)))
  have hA_gt_1 : A > 1 := by linarith [le_max_left (2 : ℝ) (max (Real.exp 1 * C_B + 1) (max (C_B ^ 2 + 1) (8 * C_tail + 8 * C₀ + 8 * C₁ * C_sup + 8 * C_err_M + 8)))]
  -- Choose T₀ large enough so that:
  -- 1) T₀ ≥ 100 and T₀ ≥ 2 * (q : ℝ) + 2, so log(q * (2T + 2)) ≤ 2 * log T
  -- 2) log log T₀ ≥ max (π Δ₀ / K_scale + 1) (16 * π * K_scale)
  -- 3) (log log T₀) ≥ ...
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
      rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]; exact h3
    have h3 : Real.exp (-2 * Real.pi * Δ) ≤ 1 / Δ := by rwa [le_div_iff₀ hΔ_pos, mul_comm]
    calc ∫ x : ℝ, (majorantM θ Δ α x - kernelK θ x)
        ≤ 2 * envelopeC θ / Δ + C_err_M * (1 / Δ) := by linarith [mul_le_mul_of_nonneg_left h3 hC_err_M.le]
      _ = (2 * envelopeC θ + C_err_M) / Δ := by ring
      _ ≤ C_L1_tot / Δ := by gcongr; exact le_trans (by linarith) (le_max_right C_L1 _)
  have hM_L1_tot : ∫ x : ℝ, |majorantM θ Δ α x| ≤ C_L1_tot :=
    hM_L1.trans (le_max_left _ _)
  have h_tail_bd := h_tail q χ Δ (majorantM θ Δ α) hΔ_ge_Δ₀ hM_int hM_L1_diff hM_L1_tot
  -- Show any t ∈ [T, 2T] with nonvanishing and polarLogL ≥ V has |primeSum1| ≥ V / 4
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
      -- Since 2πΔ ≥ 2π * log Q / V ≥ 2π * log log T ≥ 2 log log T, we have log T * exp(-2πΔ) ≤ 1!
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
  -- Apply Markov's inequality on Set.Icc T (2 * T) to |primeSum1|^(2k)
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
    -- log T ≥ exp(log log T) ≥ (log log T)^3 / 6 ≥ (log log T)^3 / 6
    have he := Real.pow_div_factorial_le_exp (Real.log (Real.log T)) hLLT_pos.le 3
    have h1 : (Real.log (Real.log T)) ^ 3 / 6 ≤ Real.log T := by
      calc (Real.log (Real.log T)) ^ 3 / 6 = (Real.log (Real.log T)) ^ 3 / Nat.factorial 3 := by norm_num
        _ ≤ Real.exp (Real.log (Real.log T)) := he
        _ = Real.log T := Real.exp_log hlogT_pos
    have h2 : (Real.log (Real.log T)) ^ 3 ≤ 6 * Real.log T := by linarith
    -- Wait: L_α ≥ 100, so log T ≥ exp(100) ≥ (log log T)^4 / 24! Even better:
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
  intro α hα
  -- Apply t_aspect_large_deviation at θ = ±π/3? No! If |S_val| ≥ V, we use ccm_odd_extremal + S_val_horizontal_zero_sum directly!
  -- Wait: even simpler! At θ = 0? No, S_val is the imaginary part.
  -- Let's use S_val_horizontal_zero_sum + ccm_odd_extremal + guinand_weil_external + prime_power_tail_bounds + prime_moment_t_aspect!
  obtain ⟨C₀, hC₀, h_hzs_S⟩ := S_val_horizontal_zero_sum D
  obtain ⟨C₁, hC₁, h_gw⟩ := guinand_weil_external D
  obtain ⟨Δ₀, C₃, hΔ₀, hC₃, h_ccm⟩ := ccm_odd_extremal
  let C_L1_tot : ℝ := max (C₃ * Real.pi) (Real.pi / 2 + C₃ + 1)
  obtain ⟨C_tail, hC_tail, h_tail⟩ := prime_power_tail_bounds (Real.pi / 2) C_L1_tot Δ₀ (by simp [abs_of_pos Real.pi_pos]) hΔ₀
  obtain ⟨B, hB, h_mom⟩ := prime_moment_t_aspect (Real.pi / 2) C_L1_tot Δ₀ (by simp [abs_of_pos Real.pi_pos]) hΔ₀
  let K_scale : ℝ := 2
  let C_B : ℝ := 32 * B * (2 * Real.pi * K_scale)
  let A : ℝ := max 2 (max (Real.exp 1 * C_B + 1) (max (C_B ^ 2 + 1) (8 * C_tail + 8 * C₀ + 8 * C₁ * C₃ + 8 * C₃ + 8)))
  let L_α : ℝ := max 100 (max (Real.pi * Δ₀ / K_scale + 1) (max (16 * Real.pi * K_scale) (max ((A / α) ^ 2) ((Real.exp 1 / α) ^ 4))))
  let T₀ : ℝ := max (max 100 ((q : ℝ) * 4 + 4)) (Real.exp (Real.exp L_α))
  let c : ℝ := 1 / (32 * (2 * Real.pi * K_scale))
  refine ⟨c, T₀, by positivity, le_trans (le_max_left _ _) (le_max_left _ _), fun T hT V hV_ub => ?_⟩
  have hT_ge_100 : 100 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT_pos : 0 < T := by linarith
  have hT_ge_exp : Real.exp (Real.exp L_α) ≤ T := le_trans (le_max_right _ _) hT
  have hlogT_ge_exp : Real.exp L_α ≤ Real.log T := by
    rw [← Real.log_exp (Real.exp L_α)]; exact Real.log_le_log (Real.exp_pos _) hT_ge_exp
  have hLLT_ge : L_α ≤ Real.log (Real.log T) := by
    rw [← Real.log_exp L_α]; exact Real.log_le_log (Real.exp_pos _) hlogT_ge_exp
  have hLLT_pos : 0 < Real.log (Real.log T) := by linarith [le_max_left (100 : ℝ) (max (Real.pi * Δ₀ / K_scale + 1) (max (16 * Real.pi * K_scale) (max ((A / α) ^ 2) ((Real.exp 1 / α) ^ 4))))]
  have hlogT_pos : 0 < Real.log T := by linarith [Real.exp_pos L_α]
  have hq_2T : (q : ℝ) * (2 * T + 2) ≤ T ^ 2 := by
    have hq4 : (q : ℝ) * 4 + 4 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
    nlinarith
  have hlog_q2T_le : Real.log ((q : ℝ) * (2 * T + 2)) ≤ 2 * Real.log T := by
    have h1 : Real.log ((q : ℝ) * (2 * T + 2)) ≤ Real.log (T ^ 2) := Real.log_le_log (by positivity) hq_2T
    rwa [Real.log_pow] at h1
  have hlog_q2T_ge : Real.log T ≤ Real.log ((q : ℝ) * (2 * T + 2)) := by
    refine Real.log_le_log hT_pos ?_
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith
  have h_ratio_ge : (Real.log T / Real.log (Real.log T)) ≥ (Real.log (Real.log T)) ^ 2 := by
    have he4 := Real.pow_div_factorial_le_exp (Real.log (Real.log T)) hLLT_pos.le 4
    have h3 : (Real.log (Real.log T)) ^ 4 / 24 ≤ Real.log T := by
      calc (Real.log (Real.log T)) ^ 4 / 24 = (Real.log (Real.log T)) ^ 4 / Nat.factorial 4 := by norm_num
        _ ≤ Real.exp (Real.log (Real.log T)) := he4
        _ = Real.log T := Real.exp_log hlogT_pos
    have h_llt : 24 ≤ Real.log (Real.log T) := by linarith [le_max_left (100 : ℝ) (max (Real.pi * Δ₀ / K_scale + 1) (max (16 * Real.pi * K_scale) (max ((A / α) ^ 2) ((Real.exp 1 / α) ^ 4))))]
    rw [ge_iff_le, le_div_iff₀ hLLT_pos]; nlinarith [pow_nonneg hLLT_pos.le 3]
  have hV_lb : A * Real.log (Real.log T) ≤ V := by
    have h1 : (A / α) ^ 2 ≤ Real.log (Real.log T) :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hLLT_ge)))
    have h2 : A / α ≤ Real.sqrt (Real.log (Real.log T)) := by
      calc A / α = Real.sqrt ((A / α) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (Real.log (Real.log T)) := Real.sqrt_le_sqrt h1
    have h3 : Real.log (Real.log T) ≤ Real.sqrt (Real.log T / Real.log (Real.log T)) := by
      rw [← Real.sqrt_sq hLLT_pos.le]; exact Real.sqrt_le_sqrt h_ratio_ge
    have h4 : A / α ≤ Real.sqrt (Real.log T / Real.log (Real.log T)) := by
      have : 1 ≤ Real.log (Real.log T) := by linarith
      calc A / α ≤ Real.sqrt (Real.log (Real.log T)) := h2
        _ ≤ Real.log (Real.log T) := by rw [← Real.sqrt_sq hLLT_pos.le]; exact Real.sqrt_le_sqrt (by nlinarith)
        _ ≤ Real.sqrt (Real.log T / Real.log (Real.log T)) := h3
    have h5 : V / Real.log (Real.log T) = α * Real.sqrt (Real.log T / Real.log (Real.log T)) := by
      dsimp only [V]; rw [Real.sqrt_mul hlogT_pos.le, Real.sqrt_div hlogT_pos.le]; field_simp [hLLT_pos.ne']
      rw [← Real.sq_sqrt hLLT_pos.le]; ring
    rw [← div_le_iff₀ hLLT_pos, h5, ← div_le_iff₀' hα]; exact h4
  have hV_pos : 0 < V := by
    have : 0 < A := by linarith [le_max_left (2 : ℝ) (max (Real.exp 1 * C_B + 1) (max (C_B ^ 2 + 1) (8 * C_tail + 8 * C₀ + 8 * C₁ * C₃ + 8 * C₃ + 8)))]
    nlinarith
  let Δ : ℝ := K_scale * Real.log ((q : ℝ) * (2 * T + 2)) / V
  have hΔ_ge_Δ₀ : Δ₀ ≤ Δ := by
    have h1 : K_scale * Real.log (Real.log T) ≤ Δ := by
      dsimp only [Δ]; rw [le_div_iff₀ hV_pos]
      have h_v : V * Real.log (Real.log T) ≤ Real.log T := by rwa [le_div_iff₀ hLLT_pos] at hV_ub
      calc K_scale * Real.log (Real.log T) * V = K_scale * (V * Real.log (Real.log T)) := by ring
        _ ≤ K_scale * Real.log T := by gcongr
        _ ≤ K_scale * Real.log ((q : ℝ) * (2 * T + 2)) := by gcongr
    have h2 : Δ₀ ≤ K_scale * Real.log (Real.log T) := by
      have h_l : Real.pi * Δ₀ / K_scale + 1 ≤ Real.log (Real.log T) :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hLLT_ge)
      rw [div_add_one (by positivity), div_le_iff₀ (by positivity)] at h_l
      nlinarith [Real.two_le_pi]
    exact h2.trans h1
  have hΔ_ge_1 : 1 ≤ Δ := le_trans hΔ₀ hΔ_ge_Δ₀
  have hΔ_pos : 0 < Δ := by linarith
  let X : ℝ := Real.exp (2 * Real.pi * Δ)
  have hlogX_eq : Real.log X = 2 * Real.pi * Δ := Real.log_exp _
  have hlogX_le_half : Real.log X ≤ Real.log T / 2 := by
    rw [hlogX_eq]
    have h_l : 16 * Real.pi * K_scale ≤ Real.log (Real.log T) :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hLLT_ge))
    have h_a : 2 ≤ A := le_max_left _ _
    have h_v2 : 16 * Real.pi * K_scale ≤ V := by nlinarith
    calc 2 * Real.pi * Δ = 2 * Real.pi * K_scale * Real.log ((q : ℝ) * (2 * T + 2)) / V := by dsimp only [Δ]; ring
      _ ≤ 2 * Real.pi * K_scale * (2 * Real.log T) / V := by gcongr
      _ = (4 * Real.pi * K_scale / V) * Real.log T := by ring
      _ ≤ (1 / 2 : ℝ) * Real.log T := by gcongr; rw [div_le_iff₀ hV_pos]; linarith
      _ = Real.log T / 2 := by ring
  have hX_le_T : X ≤ T := by
    rw [← Real.log_le_log_iff (Real.exp_pos _) hT_pos, Real.log_exp]; linarith [hlogX_le_half, hlogX_eq]
  have hlogX_pos : 0 < Real.log X := by rw [hlogX_eq]; positivity
  let k : ℕ := Nat.floor (Real.log T / Real.log X)
  have hk_ge_2 : 2 ≤ k := by
    have h1 : 2 ≤ Real.log T / Real.log X := by rw [le_div_iff₀ hlogX_pos]; linarith
    exact Nat.le_floor h1
  have hXk_le_T : X ^ k ≤ T := by
    rw [← Real.log_le_log_iff (pow_pos (Real.exp_pos _) _) hT_pos, Real.log_pow]
    have hk_le := Nat.floor_le (div_nonneg hlogT_pos.le hlogX_pos.le)
    rw [le_div_iff₀ hlogX_pos] at hk_le; exact hk_le
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
      rw [le_div_iff₀ hV_pos] at h_lx; nlinarith
    linarith
  have hk_ub : (k : ℝ) ≤ V / (2 * Real.pi * K_scale) := by
    have hk_le := Nat.floor_le (div_nonneg hlogT_pos.le hlogX_pos.le)
    have h_lx : 2 * Real.pi * K_scale * Real.log T / V ≤ Real.log X := by
      rw [hlogX_eq]; dsimp only [Δ]
      calc 2 * Real.pi * K_scale * Real.log T / V ≤ 2 * Real.pi * K_scale * Real.log ((q : ℝ) * (2 * T + 2)) / V := by gcongr
        _ = 2 * Real.pi * (K_scale * Real.log ((q : ℝ) * (2 * T + 2)) / V) := by ring
    calc (k : ℝ) ≤ Real.log T / Real.log X := hk_le
      _ ≤ Real.log T / (2 * Real.pi * K_scale * Real.log T / V) := div_le_div_of_nonneg_left hlogT_pos.le (by positivity) h_lx
      _ = V / (2 * Real.pi * K_scale) := by field_simp [hlogT_pos.ne', Real.pi_ne_zero]; ring
  obtain ⟨M_plus, M_minus, hMp_exp, hMm_exp, hM_im, hM_maj, hM_sup, hMp_int, hMm_int⟩ := h_ccm Δ hΔ_ge_Δ₀
  have hMp_real : Integrable (fun x : ℝ => (M_plus x).re - kernelK (Real.pi / 2) x) := by
    have h1 : Integrable (fun x : ℝ => (M_plus x).re) := by
      refine (integrable_inv_one_add_sq.const_mul C₃).mono' ?_ ?_
      · exact (Complex.continuous_re.comp hMp_exp.1.continuous.comp Complex.continuous_ofReal).aestronglyMeasurable
      · filter_upwards with x
        rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans (hM_sup x).1
    exact h1.sub (kernelK_integrable (Real.pi / 2))
  have hMm_real : Integrable (fun x : ℝ => (M_minus x).re - kernelK (Real.pi / 2) x) := by
    have h1 : Integrable (fun x : ℝ => (M_minus x).re) := by
      refine (integrable_inv_one_add_sq.const_mul C₃).mono' ?_ ?_
      · exact (Complex.continuous_re.comp hMm_exp.1.continuous.comp Complex.continuous_ofReal).aestronglyMeasurable
      · filter_upwards with x
        rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans (hM_sup x).2
    exact h1.sub (kernelK_integrable (Real.pi / 2))
  have hK_pi2_zero : ∫ x : ℝ, kernelK (Real.pi / 2) x = 0 := by
    rw [kernelK_integral_eq (Real.pi / 2), Real.cos_pi_div_two, mul_zero]
  have h_exp_le : Δ * Real.exp (-2 * Real.pi * Δ) ≤ 1 := by
    have he := Real.add_one_le_exp (2 * Real.pi * Δ)
    have h3 : Δ ≤ Real.exp (2 * Real.pi * Δ) := by nlinarith [Real.two_le_pi]
    rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]; exact h3
  have h_exp_1Δ : Real.exp (-2 * Real.pi * Δ) ≤ 1 / Δ := by rwa [le_div_iff₀ hΔ_pos, mul_comm]
  have hMp_int_re : Integrable (fun x : ℝ => (M_plus x).re) :=
    hMp_real.add (kernelK_integrable (Real.pi / 2)) |>.congr (by ext x; ring)
  have hMm_int_re : Integrable (fun x : ℝ => (M_minus x).re) :=
    hMm_real.add (kernelK_integrable (Real.pi / 2)) |>.congr (by ext x; ring)
  have hMp_L1_diff : ∫ x : ℝ, |(M_plus x).re - kernelK (Real.pi / 2) x| ≤ C_L1_tot / Δ := by
    have h_eq : ∫ x : ℝ, |(M_plus x).re - kernelK (Real.pi / 2) x| = ∫ x : ℝ, ((M_plus x).re - kernelK (Real.pi / 2) x) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_iff.mpr (by simp : volume {x : ℝ | ¬x ≠ 0} = 0)] with x hx
      exact abs_of_nonneg (sub_nonneg.mpr (hM_maj x hx).2)
    rw [h_eq, integral_sub hMp_int_re (kernelK_integrable (Real.pi / 2)), hK_pi2_zero, sub_zero]
    have h1 : ∫ x : ℝ, (M_plus x).re ≤ Real.pi / (2 * Δ) + C₃ * Real.exp (-2 * Real.pi * Δ) := by linarith [(abs_le.mp hMp_int).2]
    calc ∫ x : ℝ, (M_plus x).re ≤ Real.pi / (2 * Δ) + C₃ * (1 / Δ) := by linarith [mul_le_mul_of_nonneg_left h_exp_1Δ hC₃.le]
      _ = (Real.pi / 2 + C₃) / Δ := by ring
      _ ≤ C_L1_tot / Δ := by gcongr; exact le_trans (by linarith) (le_max_right _ _)
  have hMp_L1 : ∫ x : ℝ, |(M_plus x).re| ≤ C_L1_tot := by
    have h_mono : ∫ x : ℝ, |(M_plus x).re| ≤ ∫ x : ℝ, C₃ * (1 / (1 + x ^ 2)) := by
      refine integral_mono hMp_int_re.abs (integrable_inv_one_add_sq.const_mul C₃) fun x => ?_
      exact (Complex.abs_re_le_norm _).trans ((hM_sup x).1.trans_eq (by ring))
    simp_rw [one_div] at h_mono; rw [integral_const_mul, ld_integral_univ_inv_one_add_sq] at h_mono
    exact h_mono.trans (le_max_left _ _)
  have hMm_L1_diff : ∫ x : ℝ, |(M_minus x).re - kernelK (Real.pi / 2) x| ≤ C_L1_tot / Δ := by
    have h_eq : ∫ x : ℝ, |(M_minus x).re - kernelK (Real.pi / 2) x| = ∫ x : ℝ, (kernelK (Real.pi / 2) x - (M_minus x).re) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_iff.mpr (by simp : volume {x : ℝ | ¬x ≠ 0} = 0)] with x hx
      rw [abs_sub_comm]; exact abs_of_nonneg (sub_nonneg.mpr (hM_maj x hx).1)
    rw [h_eq, integral_sub (kernelK_integrable (Real.pi / 2)) hMm_int_re, hK_pi2_zero, zero_sub]
    have h1 : -∫ x : ℝ, (M_minus x).re ≤ Real.pi / (2 * Δ) + C₃ * Real.exp (-2 * Real.pi * Δ) := by linarith [(abs_le.mp hMm_int).1]
    calc -∫ x : ℝ, (M_minus x).re ≤ Real.pi / (2 * Δ) + C₃ * (1 / Δ) := by linarith [mul_le_mul_of_nonneg_left h_exp_1Δ hC₃.le]
      _ = (Real.pi / 2 + C₃) / Δ := by ring
      _ ≤ C_L1_tot / Δ := by gcongr; exact le_trans (by linarith) (le_max_right _ _)
  have hMm_L1 : ∫ x : ℝ, |(M_minus x).re| ≤ C_L1_tot := by
    have h_mono : ∫ x : ℝ, |(M_minus x).re| ≤ ∫ x : ℝ, C₃ * (1 / (1 + x ^ 2)) := by
      refine integral_mono hMm_int_re.abs (integrable_inv_one_add_sq.const_mul C₃) fun x => ?_
      exact (Complex.abs_re_le_norm _).trans ((hM_sup x).2.trans_eq (by ring))
    simp_rw [one_div] at h_mono; rw [integral_const_mul, ld_integral_univ_inv_one_add_sq] at h_mono
    exact h_mono.trans (le_max_left _ _)
  let h_hat_p := fourierHat (fun x : ℝ => ((M_plus x).re : ℂ))
  let h_hat_m := fourierHat (fun x : ℝ => ((M_minus x).re : ℂ))
  have h_tail_p := h_tail q χ Δ (fun x => (M_plus x).re) hΔ_ge_Δ₀ hMp_real hMp_L1_diff hMp_L1
  have h_tail_m := h_tail q χ Δ (fun x => (M_minus x).re) hΔ_ge_Δ₀ hMm_real hMm_L1_diff hMm_L1
  let S_p : Set ℝ := { t ∈ Set.Icc T (2 * T) | |primeSum1 q χ h_hat_p X t| ≥ V / 4 }
  let S_m : Set ℝ := { t ∈ Set.Icc T (2 * T) | |primeSum1 q χ h_hat_m X t| ≥ V / 4 }
  have h_subset : { t ∈ Set.Icc T (2 * T) | D.nonvanishing q χ t ∧ |D.S_val q χ t| ≥ V } ⊆ S_p ∪ S_m := by
    intro t ⟨ht_icc, ht_nv, ht_S⟩
    have hq1_t : q = 1 → |t| ≥ 10 := fun _ => by rw [abs_of_pos (by linarith [ht_icc.1])]; linarith [ht_icc.1]
    obtain ⟨hsumm_K, h_hzs_bd⟩ := h_hzs_S q hq χ hχ hGRH t ht_nv hq1_t
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
    have h_exp_err : (Real.log Q / (2 * Real.pi)) * (C₃ * Real.exp (-2 * Real.pi * Δ)) ≤ C₃ * Real.log (Real.log T) := by
      have h_2piΔ : Real.log (Real.log T) ≤ 2 * Real.pi * Δ := by
        have h_1 : 1 ≤ Real.pi * K_scale := by nlinarith [Real.two_le_pi]
        have h_v : V * Real.log (Real.log T) ≤ Real.log T := by rwa [le_div_iff₀ hLLT_pos] at hV_ub
        calc Real.log (Real.log T) ≤ Real.pi * K_scale * Real.log (Real.log T) := le_mul_of_one_le_left hLLT_pos.le h_1
          _ ≤ 2 * Real.pi * (K_scale * Real.log ((q : ℝ) * (2 * T + 2)) / V) := by
              rw [le_div_iff₀ hV_pos]
              calc Real.pi * K_scale * Real.log (Real.log T) * V = Real.pi * K_scale * (V * Real.log (Real.log T)) := by ring
                _ ≤ Real.pi * K_scale * Real.log T := by gcongr
                _ ≤ 2 * Real.pi * K_scale * Real.log ((q : ℝ) * (2 * T + 2)) := by nlinarith [hlog_q2T_ge, Real.pi_pos]
      have h_exp_lt : Real.exp (-2 * Real.pi * Δ) ≤ 1 / Real.log T := by
        rw [Real.exp_neg, inv_eq_one_div]
        exact div_le_div_of_nonneg_left zero_le_one hlogT_pos (by
          calc Real.log T = Real.exp (Real.log (Real.log T)) := (Real.exp_log hlogT_pos).symm
            _ ≤ Real.exp (2 * Real.pi * Δ) := Real.exp_le_exp.mpr h_2piΔ)
      have h_logQ_le : Real.log Q ≤ 2 * Real.log T := (Real.log_le_log (by linarith) hQ_le).trans hlog_q2T_le
      calc (Real.log Q / (2 * Real.pi)) * (C₃ * Real.exp (-2 * Real.pi * Δ))
          ≤ (2 * Real.log T / (2 * Real.pi)) * (C₃ * (1 / Real.log T)) := by gcongr
        _ = C₃ / Real.pi := by field_simp [hlogT_pos.ne', Real.pi_ne_zero]; ring
        _ ≤ C₃ * Real.log (Real.log T) := by
            have : 1 / Real.pi ≤ 1 := div_le_one_of_le₀ (by linarith [Real.two_le_pi]) Real.pi_pos.le
            nlinarith [hC₃]
    have h_gw_err : C₁ * (C₃ + (if q = 1 then Real.exp (Real.pi * Δ) / t ^ 2 * C₃ else 0)) ≤
        2 * C₁ * C₃ * Real.log (Real.log T) := by
      have h_if : (if q = 1 then Real.exp (Real.pi * Δ) / t ^ 2 * C₃ else 0) ≤ C₃ := by
        split_ifs
        · have h_e : Real.exp (Real.pi * Δ) ≤ T := by
            have : Real.pi * Δ ≤ 2 * Real.pi * Δ := by nlinarith [Real.pi_pos]
            exact (Real.exp_le_exp.mpr this).trans hX_le_T
          have h_t2 : T ≤ t ^ 2 := by have : T ≤ t := ht_icc.1; nlinarith
          have h_div : Real.exp (Real.pi * Δ) / t ^ 2 ≤ 1 := div_le_one_of_le₀ (h_e.trans h_t2) (sq_nonneg t)
          exact mul_le_of_le_one_left hC₃.le h_div
        · exact hC₃.le
      have h1 : 1 ≤ Real.log (Real.log T) := by linarith
      nlinarith
    have h_loglogX : Real.log (Real.log X) ≤ Real.log (Real.log T) :=
      Real.log_le_log hlogX_pos (by linarith [hlogX_le_half])
    have h_C₀_le : C₀ ≤ C₀ * Real.log (Real.log T) := le_mul_of_one_le_right hC₀.le (by linarith)
    have h_tot_err : 2 * C_tail * Real.log (Real.log T) + C₀ + 2 * C₁ * C₃ * Real.log (Real.log T) +
        C₃ * Real.log (Real.log T) ≤ Real.pi * V / 4 := by
      have h_a : (8 * C_tail + 8 * C₀ + 8 * C₁ * C₃ + 8 * C₃ + 8) ≤ A :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
      have h_pi2 : 2 ≤ Real.pi := Real.two_le_pi
      nlinarith
    have h_pi_env : (Real.log Q / (2 * Real.pi)) * (Real.pi / (2 * Δ)) ≤ Real.pi * V / 2 := by
      have h_logQ : Real.log Q ≤ Real.log ((q : ℝ) * (2 * T + 2)) := Real.log_le_log (by linarith) hQ_le
      calc (Real.log Q / (2 * Real.pi)) * (Real.pi / (2 * Δ))
          = Real.log Q / (4 * Δ) := by field_simp [Real.pi_ne_zero]; ring
        _ ≤ Real.log ((q : ℝ) * (2 * T + 2)) / (4 * Δ) := by gcongr
        _ = V / (4 * K_scale) := by dsimp only [Δ]; field_simp [hV_pos.ne']; ring
        _ = V / 8 := by dsimp only [K_scale]; ring
        _ ≤ Real.pi * V / 2 := by nlinarith [Real.two_le_pi, hV_pos]
    rcases le_abs.mp ht_S with hS_pos | hS_neg
    · left
      refine ⟨ht_icc, ?_⟩
      obtain ⟨hsumm_M, h_gw_bd⟩ := h_gw q hq χ hχ hGRH M_plus Δ C₃ hΔ_ge_1 hC₃.le hMp_exp (fun x => (hM_sup x).1)
        (fun x => (hM_im x).1) t hq1_t
      have h_sum_le : ∑' n : ℕ, kernelK (Real.pi / 2) (t - D.zeros q χ n) ≤
          ∑' n : ℕ, (M_plus (t - D.zeros q χ n)).re := by
        refine Summable.tsum_le_tsum (fun n => ?_) hsumm_K hsumm_M
        exact (hM_maj _ (sub_ne_zero.mpr (D.nonvanishing_zeros q χ t ht_nv n))).2
      have h_hat_eq : fourierHat (fun x : ℝ => M_plus x) = h_hat_p := by
        ext ξ; unfold fourierHat; congr 1; ext x
        rw [Complex.ext ((rfl : (M_plus x).re = _)) (hM_im x).1]
      rw [h_hat_eq] at h_gw_bd
      have h_tail_t := h_tail_p t
      have h_p23 : |primeSum2 q χ h_hat_p X t + primeSumGe3 q χ h_hat_p X t| ≤ 2 * C_tail * Real.log (Real.log T) := by
        have h1 : |primeSum2 q χ h_hat_p X t| ≤ C_tail * Real.log (Real.log T) :=
          h_tail_t.1.trans (mul_le_mul_of_nonneg_left h_loglogX hC_tail.le)
        have h2 : |primeSumGe3 q χ h_hat_p X t| ≤ C_tail * Real.log (Real.log T) :=
          h_tail_t.2.trans (le_mul_of_one_le_right hC_tail.le (by linarith))
        linarith [abs_add_le (primeSum2 q χ h_hat_p X t) (primeSumGe3 q χ h_hat_p X t)]
      have h_P_split : primePowerSum q χ h_hat_p X t =
          primeSum1 q χ h_hat_p X t + primeSum2 q χ h_hat_p X t + primeSumGe3 q χ h_hat_p X t := by
        unfold primeSumGe3; ring
      have h_main_int : (Real.log Q / (2 * Real.pi)) * (∫ x : ℝ, (M_plus x).re) ≤
          Real.pi * V / 2 + C₃ * Real.log (Real.log T) := by
        have h1 : ∫ x : ℝ, (M_plus x).re ≤ Real.pi / (2 * Δ) + C₃ * Real.exp (-2 * Real.pi * Δ) := by linarith [(abs_le.mp hMp_int).2]
        have h2 : 0 ≤ Real.log Q / (2 * Real.pi) := div_nonneg (Real.log_nonneg (by linarith)) (by positivity)
        calc (Real.log Q / (2 * Real.pi)) * (∫ x : ℝ, (M_plus x).re)
            ≤ (Real.log Q / (2 * Real.pi)) * (Real.pi / (2 * Δ) + C₃ * Real.exp (-2 * Real.pi * Δ)) := by gcongr
          _ = (Real.log Q / (2 * Real.pi)) * (Real.pi / (2 * Δ)) + (Real.log Q / (2 * Real.pi)) * (C₃ * Real.exp (-2 * Real.pi * Δ)) := by ring
          _ ≤ Real.pi * V / 2 + C₃ * Real.log (Real.log T) := add_le_add h_pi_env h_exp_err
      have h_piV : Real.pi * V ≤ Real.pi * D.S_val q χ t := by gcongr
      have h_neg : -primeSum1 q χ h_hat_p X t ≥ Real.pi * V / 4 := by
        have h_g := (abs_le.mp h_gw_bd).2
        have h_h := (abs_le.mp h_hzs_bd).2
        have h_p := (abs_le.mp h_p23).1
        linarith
      have h_div_pi : V / 4 ≤ Real.pi * V / 4 := by nlinarith [Real.two_le_pi, hV_pos]
      exact le_trans h_div_pi (le_trans h_neg (neg_le_abs _))
    · right
      refine ⟨ht_icc, ?_⟩
      let M_neg : ℂ → ℂ := fun z => -M_minus z
      have hM_neg_exp : HasExponentialType M_neg (2 * Real.pi * Δ) := by
        refine ⟨hMm_exp.1.neg, fun ε hε => ?_⟩
        obtain ⟨C, hC, hbd⟩ := hMm_exp.2 ε hε
        exact ⟨C, hC, fun z => by simpa [M_neg, norm_neg] using hbd z⟩
      obtain ⟨hsumm_M, h_gw_bd⟩ := h_gw q hq χ hχ hGRH M_neg Δ C₃ hΔ_ge_1 hC₃.le hM_neg_exp
        (fun x => by simpa [M_neg, norm_neg] using (hM_sup x).2)
        (fun x => by simp [M_neg, (hM_im x).2]) t hq1_t
      have h_sum_le : ∑' n : ℕ, (-kernelK (Real.pi / 2) (t - D.zeros q χ n)) ≤
          ∑' n : ℕ, (M_neg (t - D.zeros q χ n)).re := by
        refine Summable.tsum_le_tsum (fun n => ?_) hsumm_K.neg hsumm_M
        simp only [M_neg, Complex.neg_re, neg_le_neg_iff]
        exact (hM_maj _ (sub_ne_zero.mpr (D.nonvanishing_zeros q χ t ht_nv n))).1
      have h_hat_eq : fourierHat (fun x : ℝ => M_neg x) = fun ξ => -h_hat_m ξ := by
        ext ξ; unfold fourierHat h_hat_m; dsimp only [M_neg]
        have heq : (fun x : ℝ => -M_minus x * Complex.exp (-2 * Real.pi * Complex.I * ξ * x)) =
            fun x : ℝ => -(((M_minus x).re : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * ξ * x)) := by
          ext x
          have hre : M_minus x = ((M_minus x).re : ℂ) := Complex.ext rfl (hM_im x).2
          rw [hre]; ring
        rw [heq, integral_neg]
      have h_pps_neg : primePowerSum q χ (fourierHat (fun x : ℝ => M_neg x)) X t = -primePowerSum q χ h_hat_m X t := by
        rw [h_hat_eq]
        unfold primePowerSum
        simp only [mul_neg, neg_add, ← neg_add_rev]
        rw [← Finset.sum_neg_distrib]
        congr 1; ext n
        · simp [Complex.neg_re]; ring
      rw [h_pps_neg] at h_gw_bd
      have h_tail_t := h_tail_m t
      have h_p23 : |primeSum2 q χ h_hat_m X t + primeSumGe3 q χ h_hat_m X t| ≤ 2 * C_tail * Real.log (Real.log T) := by
        have h1 : |primeSum2 q χ h_hat_m X t| ≤ C_tail * Real.log (Real.log T) :=
          h_tail_t.1.trans (mul_le_mul_of_nonneg_left h_loglogX hC_tail.le)
        have h2 : |primeSumGe3 q χ h_hat_m X t| ≤ C_tail * Real.log (Real.log T) :=
          h_tail_t.2.trans (le_mul_of_one_le_right hC_tail.le (by linarith))
        linarith [abs_add_le (primeSum2 q χ h_hat_m X t) (primeSumGe3 q χ h_hat_m X t)]
      have h_P_split : primePowerSum q χ h_hat_m X t =
          primeSum1 q χ h_hat_m X t + primeSum2 q χ h_hat_m X t + primeSumGe3 q χ h_hat_m X t := by
        unfold primeSumGe3; ring
      have h_main_int : (Real.log Q / (2 * Real.pi)) * (∫ x : ℝ, (M_neg x).re) ≤
          Real.pi * V / 2 + C₃ * Real.log (Real.log T) := by
        have h_int_eq : (∫ x : ℝ, (M_neg x).re) = -∫ x : ℝ, (M_minus x).re := by
          simp only [M_neg, Complex.neg_re, integral_neg]
        rw [h_int_eq]
        have h1 : -∫ x : ℝ, (M_minus x).re ≤ Real.pi / (2 * Δ) + C₃ * Real.exp (-2 * Real.pi * Δ) := by linarith [(abs_le.mp hMm_int).1]
        have h2 : 0 ≤ Real.log Q / (2 * Real.pi) := div_nonneg (Real.log_nonneg (by linarith)) (by positivity)
        calc (Real.log Q / (2 * Real.pi)) * (-∫ x : ℝ, (M_minus x).re)
            ≤ (Real.log Q / (2 * Real.pi)) * (Real.pi / (2 * Δ) + C₃ * Real.exp (-2 * Real.pi * Δ)) := by gcongr
          _ = (Real.log Q / (2 * Real.pi)) * (Real.pi / (2 * Δ)) + (Real.log Q / (2 * Real.pi)) * (C₃ * Real.exp (-2 * Real.pi * Δ)) := by ring
          _ ≤ Real.pi * V / 2 + C₃ * Real.log (Real.log T) := add_le_add h_pi_env h_exp_err
      have h_piV : Real.pi * V ≤ -Real.pi * D.S_val q χ t := by nlinarith [Real.two_le_pi]
      have h_tsum_neg : ∑' n : ℕ, (-kernelK (Real.pi / 2) (t - D.zeros q χ n)) =
          -∑' n : ℕ, kernelK (Real.pi / 2) (t - D.zeros q χ n) := tsum_neg
      have h_pos : primeSum1 q χ h_hat_m X t ≥ Real.pi * V / 4 := by
        have h_g := (abs_le.mp h_gw_bd).2
        have h_h := (abs_le.mp h_hzs_bd).1
        have h_p := (abs_le.mp h_p23).2
        linarith
      have h_div_pi : V / 4 ≤ Real.pi * V / 4 := by nlinarith [Real.two_le_pi, hV_pos]
      exact le_trans h_div_pi (le_trans h_pos (le_abs_self _))
  have h_meas_le : (volume { t ∈ Set.Icc T (2 * T) | D.nonvanishing q χ t ∧ |D.S_val q χ t| ≥ V }).toReal ≤
      (volume S_p).toReal + (volume S_m).toReal := by
    have h_u := measure_mono h_subset |>.trans (measure_union_le S_p S_m)
    have h_fin_p : volume S_p ≠ ⊤ := ne_top_of_le_ne_top (measure_lt_top _ _).ne (measure_mono (fun _ h => h.1))
    have h_fin_m : volume S_m ≠ ⊤ := ne_top_of_le_ne_top (measure_lt_top _ _).ne (measure_mono (fun _ h => h.1))
    exact (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨h_fin_p, h_fin_m⟩) h_u).trans_eq
      (ENNReal.toReal_add h_fin_p h_fin_m)
  have h_markov_branch : ∀ (h_hat : ℝ → ℂ) (M : ℝ → ℝ),
      Integrable (fun x : ℝ => M x - kernelK (Real.pi / 2) x) →
      (∫ x : ℝ, |M x - kernelK (Real.pi / 2) x|) ≤ C_L1_tot / Δ →
      (∫ x : ℝ, |M x|) ≤ C_L1_tot →
      h_hat = fourierHat (fun x : ℝ => (M x : ℂ)) →
      (1 / T) * (volume { t ∈ Set.Icc T (2 * T) | |primeSum1 q χ h_hat X t| ≥ V / 4 }).toReal ≤
        (16 * B * (2 * Real.pi * K_scale) * Real.log (Real.log T) / V) ^ k := by
    intro h_hat M hM_diff hM_L1d hM_L1t hhat_eq
    subst hhat_eq
    let F_t : ℝ → ℝ := fun t => |primeSum1 q χ (fourierHat (fun x : ℝ => (M x : ℂ))) X t| ^ (2 * k)
    have hF_cont : Continuous F_t := by
      dsimp only [F_t]; unfold primeSum1
      refine (Continuous.abs (continuous_const.mul (continuous_finset_sum _ fun p _ =>
        continuous_const.mul (Complex.continuous_re.comp ?_)))).pow (2 * k)
      refine Continuous.add ?_ ?_
      · exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))
      · exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))
    have hF_int : IntegrableOn F_t (Set.Icc T (2 * T)) := hF_cont.continuousOn.integrableOn_Icc
    have h_markov : (V / 4) ^ (2 * k) *
        (volume { t ∈ Set.Icc T (2 * T) | |primeSum1 q χ (fourierHat (fun x : ℝ => (M x : ℂ))) X t| ≥ V / 4 }).toReal ≤
        ∫ t in Set.Icc T (2 * T), F_t t := by
      have h_sub_set : { t ∈ Set.Icc T (2 * T) | |primeSum1 q χ (fourierHat (fun x : ℝ => (M x : ℂ))) X t| ≥ V / 4 } =
          Set.Icc T (2 * T) ∩ { t : ℝ | (V / 4) ^ (2 * k) ≤ F_t t } := by
        ext t; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, ge_iff_le]
        constructor
        · rintro ⟨ht, h1⟩; exact ⟨ht, pow_le_pow_left₀ (by positivity) h1 (2 * k)⟩
        · rintro ⟨ht, h1⟩; refine ⟨ht, ?_⟩; by_contra hlt; push_neg at hlt
          have := pow_lt_pow_left₀ hlt (abs_nonneg _) (by positivity : 2 * k ≠ 0); linarith
      rw [h_sub_set]
      have h_m := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict (Set.Icc T (2 * T)))
        (ae_of_all _ fun t => by dsimp only [F_t]; positivity) hF_int ((V / 4) ^ (2 * k))
      simpa [Measure.restrict_apply (hF_cont.measurable (measurableSet_le measurable_const measurable_id) :
        MeasurableSet { t : ℝ | (V / 4) ^ (2 * k) ≤ F_t t }), Set.inter_comm] using h_m
    have h_mom_bd := h_mom q χ Δ T k M hq hΔ_ge_Δ₀ (by linarith) hXk_le_T hM_diff hM_L1d hM_L1t
    have h_loglogX : Real.log (Real.log X) ≤ Real.log (Real.log T) :=
      Real.log_le_log hlogX_pos (by linarith [hlogX_le_half])
    have h_base : (4 / V) ^ 2 * (B * k * Real.log (Real.log X)) ≤
        (16 * B * (2 * Real.pi * K_scale)) * Real.log (Real.log T) / V := by
      calc (4 / V) ^ 2 * (B * k * Real.log (Real.log X))
          ≤ (16 / V ^ 2) * (B * (V / (2 * Real.pi * K_scale)) * Real.log (Real.log T)) := by
            gcongr; ring_nf; rfl
        _ = (8 * B / (Real.pi * K_scale)) * Real.log (Real.log T) / V := by
            field_simp [hV_pos.ne', Real.pi_ne_zero]; ring
        _ ≤ (16 * B * (2 * Real.pi * K_scale)) * Real.log (Real.log T) / V := by
            gcongr
            have : 1 ≤ 2 * Real.pi * K_scale := by nlinarith [Real.two_le_pi]
            nlinarith [Real.two_le_pi]
    have h_pow_pos : 0 < (V / 4) ^ (2 * k) := pow_pos (by positivity) (2 * k)
    have h1 : (1 / T) * (volume { t ∈ Set.Icc T (2 * T) | |primeSum1 q χ (fourierHat (fun x : ℝ => (M x : ℂ))) X t| ≥ V / 4 }).toReal ≤
        ((4 / V) ^ 2 * (B * k * Real.log (Real.log X))) ^ k := by
      calc (1 / T) * (volume { t ∈ Set.Icc T (2 * T) | |primeSum1 q χ (fourierHat (fun x : ℝ => (M x : ℂ))) X t| ≥ V / 4 }).toReal
          ≤ (1 / T) * ((∫ t in Set.Icc T (2 * T), F_t t) / (V / 4) ^ (2 * k)) := by
            gcongr; rwa [le_div_iff₀ h_pow_pos, mul_comm]
        _ = (1 / (V / 4) ^ (2 * k)) * ((1 / T) * ∫ t in Set.Icc T (2 * T), F_t t) := by ring
        _ ≤ (1 / (V / 4) ^ (2 * k)) * (B * k * Real.log (Real.log X)) ^ k := by gcongr
        _ = ((4 / V) ^ 2 * (B * k * Real.log (Real.log X))) ^ k := by
            rw [mul_pow, ← pow_mul, mul_comm 2 k, one_div_pow, div_pow, one_div_div]; ring
    exact h1.trans (pow_le_pow_left₀ (by positivity) h_base k)
  have h_bp := h_markov_branch h_hat_p (fun x => (M_plus x).re) hMp_real hMp_L1_diff hMp_L1 rfl
  have h_bm := h_markov_branch h_hat_m (fun x => (M_minus x).re) hMm_real hMm_L1_diff hMm_L1 rfl
  have h_div_v : (1 / T) * (volume { t ∈ Set.Icc T (2 * T) | D.nonvanishing q χ t ∧ |D.S_val q χ t| ≥ V }).toReal ≤
      (C_B * Real.log (Real.log T) / V) ^ k := by
    have h_2_pow : (2 : ℝ) ≤ 2 ^ k := by
      have : 2 ≤ 2 ^ 2 := by norm_num
      exact this.trans (pow_le_pow_right₀ (by norm_num) hk_ge_2)
    calc (1 / T) * (volume { t ∈ Set.Icc T (2 * T) | D.nonvanishing q χ t ∧ |D.S_val q χ t| ≥ V }).toReal
        ≤ (1 / T) * ((volume S_p).toReal + (volume S_m).toReal) := by gcongr
      _ = (1 / T) * (volume S_p).toReal + (1 / T) * (volume S_m).toReal := by ring
      _ ≤ (16 * B * (2 * Real.pi * K_scale) * Real.log (Real.log T) / V) ^ k +
            (16 * B * (2 * Real.pi * K_scale) * Real.log (Real.log T) / V) ^ k := add_le_add h_bp h_bm
      _ = 2 * (16 * B * (2 * Real.pi * K_scale) * Real.log (Real.log T) / V) ^ k := by ring
      _ ≤ 2 ^ k * (16 * B * (2 * Real.pi * K_scale) * Real.log (Real.log T) / V) ^ k := by gcongr
      _ = (C_B * Real.log (Real.log T) / V) ^ k := by
          rw [← mul_pow]; dsimp only [C_B]; ring_nf
  have h_ratio_le : C_B * Real.log (Real.log T) / V ≤ (Real.log (Real.log T) / V) ^ (1 / 2 : ℝ) := by
    have h_a : C_B ^ 2 ≤ A := le_trans (by linarith) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
    have h_cb_le : C_B ^ 2 * Real.log (Real.log T) ≤ V := by
      calc C_B ^ 2 * Real.log (Real.log T) ≤ A * Real.log (Real.log T) := by gcongr
        _ ≤ V := hV_lb
    have h_sq : (C_B * Real.log (Real.log T) / V) ^ 2 ≤ Real.log (Real.log T) / V := by
      rw [div_pow, div_le_div_iff₀ (sq_pos_of_pos hV_pos) hV_pos]
      nlinarith [h_cb_le, hLLT_pos]
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
      Real.exp (-((1 / (8 * (2 * Real.pi * K_scale))) * V * Real.log (V / Real.log (Real.log T)))) := by
    rw [← Real.exp_log (pow_pos (by positivity) k), Real.log_pow]
    apply Real.exp_le_exp.mpr
    have h_l_ge_1 : 1 ≤ V / Real.log (Real.log T) := by
      rw [le_div_iff₀ hLLT_pos]; have : 1 ≤ A := by linarith; nlinarith
    have h_log_nonneg : 0 ≤ Real.log (V / Real.log (Real.log T)) := Real.log_nonneg h_l_ge_1
    have h_k_log : (1 / (8 * (2 * Real.pi * K_scale))) * V * Real.log (V / Real.log (Real.log T)) ≤
        (k : ℝ) * (-Real.log (C_B * Real.log (Real.log T) / V)) := by
      calc (1 / (8 * (2 * Real.pi * K_scale))) * V * Real.log (V / Real.log (Real.log T))
          = (V / (4 * (2 * Real.pi * K_scale))) * ((1 / 2 : ℝ) * Real.log (V / Real.log (Real.log T))) := by ring
        _ ≤ (k : ℝ) * (-Real.log (C_B * Real.log (Real.log T) / V)) := by
            gcongr; linarith [hk_lb]
    linarith
  have h_log_v : (1 / 4 : ℝ) * Real.log (Real.log T) ≤ Real.log (V / Real.log (Real.log T)) := by
    have h_v_eq : V / Real.log (Real.log T) = α * Real.sqrt (Real.log T / Real.log (Real.log T)) := by
      dsimp only [V]; rw [Real.sqrt_mul hlogT_pos.le, Real.sqrt_div hlogT_pos.le]; field_simp [hLLT_pos.ne']
      rw [← Real.sq_sqrt hLLT_pos.le]; ring
    have h_ge_exp : (Real.log (Real.log T)) ^ (1 / 4 : ℝ) ≤ α * Real.sqrt (Real.log T / Real.log (Real.log T)) := by
      have h1 : (Real.exp 1 / α) ^ 4 ≤ Real.log (Real.log T) :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hLLT_ge)))
      have h2 : Real.exp 1 / α ≤ (Real.log (Real.log T)) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast (Real.exp 1 / α) 4] at h1
        have := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
        rwa [← Real.rpow_mul (by positivity), show (4 : ℕ) * (1 / 4 : ℝ) = 1 by norm_num, Real.rpow_one] at this
      have h3 : (Real.log (Real.log T)) ^ (1 / 2 : ℝ) ≤ Real.sqrt (Real.log T / Real.log (Real.log T)) := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.sqrt_le_sqrt (by have : 1 ≤ Real.log (Real.log T) := by linarith; nlinarith [h_ratio_ge])
      have h4 : (Real.log (Real.log T)) ^ (1 / 4 : ℝ) * (Real.log (Real.log T)) ^ (1 / 4 : ℝ) =
          (Real.log (Real.log T)) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hLLT_pos]; norm_num
      have h5 : 1 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      calc (Real.log (Real.log T)) ^ (1 / 4 : ℝ) = 1 * (Real.log (Real.log T)) ^ (1 / 4 : ℝ) := (one_mul _).symm
        _ ≤ Real.exp 1 * (Real.log (Real.log T)) ^ (1 / 4 : ℝ) := by gcongr
        _ = α * ((Real.exp 1 / α) * (Real.log (Real.log T)) ^ (1 / 4 : ℝ)) := by field_simp [hα.ne']
        _ ≤ α * ((Real.log (Real.log T)) ^ (1 / 4 : ℝ) * (Real.log (Real.log T)) ^ (1 / 4 : ℝ)) := by gcongr
        _ = α * (Real.log (Real.log T)) ^ (1 / 2 : ℝ) := by rw [h4]
        _ ≤ α * Real.sqrt (Real.log T / Real.log (Real.log T)) := by gcongr
    rw [h_v_eq]
    calc (1 / 4 : ℝ) * Real.log (Real.log T) = Real.log ((Real.log (Real.log T)) ^ (1 / 4 : ℝ)) :=
          (Real.log_rpow hLLT_pos _).symm
      _ ≤ Real.log (α * Real.sqrt (Real.log T / Real.log (Real.log T))) := Real.log_le_log (by positivity) h_ge_exp
  have h_exp_le2 : Real.exp (-((1 / (8 * (2 * Real.pi * K_scale))) * V * Real.log (V / Real.log (Real.log T)))) ≤
      Real.exp (-c * α * Real.sqrt (Real.log T) * (Real.log (Real.log T)) ^ (3 / 2 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have h_v_eq : V * Real.log (Real.log T) = α * Real.sqrt (Real.log T) * (Real.log (Real.log T)) ^ (3 / 2 : ℝ) := by
      dsimp only [V]; rw [Real.sqrt_mul hlogT_pos.le, Real.sqrt_eq_rpow (Real.log (Real.log T))]
      have h_32 : (Real.log (Real.log T)) ^ (1 / 2 : ℝ) * Real.log (Real.log T) = (Real.log (Real.log T)) ^ (3 / 2 : ℝ) := by
        conv_lhs => rhs; rw [← Real.rpow_one (Real.log (Real.log T))]
        rw [← Real.rpow_add hLLT_pos]; norm_num
      nlinarith [h_32]
    dsimp only [c]
    nlinarith [hV_pos]
  rw [← div_le_iff₀' hT_pos]
  rw [one_div_mul_eq_div] at h_div_v
  exact h_div_v.trans (h_exp_final.trans h_exp_le2)

/-! ### Bounding `φ(q) / φ*(q)` for `q ≥ 3` with `φ*(q) ≥ 1` -/

private lemma totientStar_mul_ge (a b : ℕ) (ha : a ≥ 1) (hb : b ≥ 1) (hab : Nat.Coprime a b) :
    totientStar a * totientStar b ≤ totientStar (a * b) := by
  classical
  haveI : NeZero a := ⟨by omega⟩
  haveI : NeZero b := ⟨by omega⟩
  haveI : NeZero (a * b) := ⟨by positivity⟩
  let ha_dvd : a ∣ a * b := dvd_mul_right a b
  let hb_dvd : b ∣ a * b := dvd_mul_left b a
  let S_a := Finset.univ.filter (fun χ : DirichletCharacter ℂ a => χ.IsPrimitive)
  let S_b := Finset.univ.filter (fun χ : DirichletCharacter ℂ b => χ.IsPrimitive)
  let S_ab := Finset.univ.filter (fun χ : DirichletCharacter ℂ (a * b) => χ.IsPrimitive)
  let F : DirichletCharacter ℂ a × DirichletCharacter ℂ b → DirichletCharacter ℂ (a * b) :=
    fun p => DirichletCharacter.changeLevel ha_dvd p.1 * DirichletCharacter.changeLevel hb_dvd p.2
  have h_mem : ∀ p ∈ S_a ×ˢ S_b, F p ∈ S_ab := by
    rintro ⟨χ₁, χ₂⟩ hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, S_a, S_b, S_ab] at hp ⊢
    rcases hp with ⟨h1, h2⟩
    let ψ₁ := DirichletCharacter.changeLevel ha_dvd χ₁
    let ψ₂ := DirichletCharacter.changeLevel hb_dvd χ₂
    have hψ₁_c : ψ₁.conductor = a :=
      (DirichletCharacter.conductor_changeLevel χ₁ ha_dvd).trans (DirichletCharacter.isPrimitive_def.mp h1)
    have hψ₂_c : ψ₂.conductor = b :=
      (DirichletCharacter.conductor_changeLevel χ₂ hb_dvd).trans (DirichletCharacter.isPrimitive_def.mp h2)
    have h_dvd_ab : (ψ₁ * ψ₂).conductor ∣ a * b :=
      (DirichletCharacter.mem_conductorSet_iff_conductor_dvd (ψ₁ * ψ₂) dvd_rfl).mp
        (DirichletCharacter.level_mem_conductorSet (ψ₁ * ψ₂))
    have ha_dvd_c : a ∣ (ψ₁ * ψ₂).conductor := by
      have h_eq : ψ₁ = (ψ₁ * ψ₂) * ψ₂⁻¹ := (mul_inv_cancel_right ψ₁ ψ₂).symm
      have h_lcm := DirichletCharacter.conductor_mul_dvd_lcm_conductor (ψ₁ * ψ₂) ψ₂⁻¹
      rw [← h_eq, hψ₁_c, DirichletCharacter.conductor_inv, hψ₂_c] at h_lcm
      exact hab.dvd_of_dvd_mul_right (h_lcm.trans (Nat.lcm_dvd_mul _ _))
    have hb_dvd_c : b ∣ (ψ₁ * ψ₂).conductor := by
      have h_eq : ψ₂ = (ψ₁ * ψ₂) * ψ₁⁻¹ := by
        rw [mul_comm ψ₁ ψ₂]; exact (mul_inv_cancel_right ψ₂ ψ₁).symm
      have h_lcm := DirichletCharacter.conductor_mul_dvd_lcm_conductor (ψ₁ * ψ₂) ψ₁⁻¹
      rw [← h_eq, hψ₂_c, DirichletCharacter.conductor_inv, hψ₁_c] at h_lcm
      exact hab.symm.dvd_of_dvd_mul_right (h_lcm.trans (Nat.lcm_dvd_mul _ _))
    exact DirichletCharacter.isPrimitive_def.mpr
      (Nat.dvd_antisymm h_dvd_ab (hab.mul_dvd_of_dvd_of_dvd ha_dvd_c hb_dvd_c))
  have h_inj : Set.InjOn F (S_a ×ˢ S_b : Finset (DirichletCharacter ℂ a × DirichletCharacter ℂ b)) := by
    rintro ⟨χ₁, χ₂⟩ _ ⟨χ₁', χ₂'⟩ _ heq
    have h_eq1 : χ₁ = χ₁' := by
      ext u
      by_cases hu : IsUnit u
      · obtain ⟨k, hk_a, hk_b⟩ := Nat.chineseRemainder hab u.val 1
        have hku : (k : ZMod a) = u := by
          rw [← ZMod.natCast_zmod_val u]
          exact (ZMod.natCast_eq_natCast_iff k u.val a).mpr hk_a
        have hk1 : (k : ZMod b) = 1 := by
          simpa using (ZMod.natCast_eq_natCast_iff k 1 b).mpr hk_b
        have hcop_a : IsCoprime (k : ℤ) (a : ℤ) := by
          rw [← ZMod.isUnit_iff_coprime_int]
          simpa [hku] using hu
        have hcop_b : IsCoprime (k : ℤ) (b : ℤ) := by
          rw [← ZMod.isUnit_iff_coprime_int]
          simpa [hk1] using (isUnit_one : IsUnit (1 : ZMod b))
        have hcop_ab : IsCoprime (k : ℤ) ((a * b : ℕ) : ℤ) := by
          push_cast; exact hcop_a.mul_right hcop_b
        have hval := congr_arg (fun (χ : DirichletCharacter ℂ (a * b)) => χ (k : ZMod (a * b))) heq
        dsimp only [F, MulChar.mul_apply] at hval
        have hc1 := DirichletCharacter.changeLevel_eq_cast_of_dvd' ha_dvd χ₁ hcop_ab
        have hc2 := DirichletCharacter.changeLevel_eq_cast_of_dvd' hb_dvd χ₂ hcop_ab
        have hc1' := DirichletCharacter.changeLevel_eq_cast_of_dvd' ha_dvd χ₁' hcop_ab
        have hc2' := DirichletCharacter.changeLevel_eq_cast_of_dvd' hb_dvd χ₂' hcop_ab
        simp only [Int.cast_natCast] at hc1 hc2 hc1' hc2'
        rw [hc1, hc2, hc1', hc2', hku, hk1, MulChar.map_one, mul_one, mul_one] at hval
        exact hval
      · simp [MulChar.map_nonunit hu]
    have h_eq2 : χ₂ = χ₂' := by
      ext u
      by_cases hu : IsUnit u
      · obtain ⟨k, hk_a, hk_b⟩ := Nat.chineseRemainder hab 1 u.val
        have hk1 : (k : ZMod a) = 1 := by
          simpa using (ZMod.natCast_eq_natCast_iff k 1 a).mpr hk_a
        have hku : (k : ZMod b) = u := by
          rw [← ZMod.natCast_zmod_val u]
          exact (ZMod.natCast_eq_natCast_iff k u.val b).mpr hk_b
        have hcop_a : IsCoprime (k : ℤ) (a : ℤ) := by
          rw [← ZMod.isUnit_iff_coprime_int]
          simpa [hk1] using (isUnit_one : IsUnit (1 : ZMod a))
        have hcop_b : IsCoprime (k : ℤ) (b : ℤ) := by
          rw [← ZMod.isUnit_iff_coprime_int]
          simpa [hku] using hu
        have hcop_ab : IsCoprime (k : ℤ) ((a * b : ℕ) : ℤ) := by
          push_cast; exact hcop_a.mul_right hcop_b
        have hval := congr_arg (fun (χ : DirichletCharacter ℂ (a * b)) => χ (k : ZMod (a * b))) heq
        dsimp only [F, MulChar.mul_apply] at hval
        have hc1 := DirichletCharacter.changeLevel_eq_cast_of_dvd' ha_dvd χ₁ hcop_ab
        have hc2 := DirichletCharacter.changeLevel_eq_cast_of_dvd' hb_dvd χ₂ hcop_ab
        have hc1' := DirichletCharacter.changeLevel_eq_cast_of_dvd' ha_dvd χ₁' hcop_ab
        have hc2' := DirichletCharacter.changeLevel_eq_cast_of_dvd' hb_dvd χ₂' hcop_ab
        simp only [Int.cast_natCast] at hc1 hc2 hc1' hc2'
        rw [hc1, hc2, hc1', hc2', hk1, hku, MulChar.map_one, one_mul, one_mul] at hval
        exact hval
      · simp [MulChar.map_nonunit hu]
    exact Prod.ext h_eq1 h_eq2
  have h_card := Finset.card_le_card_of_injOn F h_mem h_inj
  rw [Finset.card_product] at h_card
  simpa [totientStar, S_a, S_b, S_ab] using h_card

private lemma totientStar_prime_ge (p : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) :
    totientStar p ≥ p - 2 := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h_sub : Finset.univ.erase (1 : DirichletCharacter ℂ p) ⊆
      Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.IsPrimitive) := by
    intro χ hχ
    rw [Finset.mem_erase] at hχ
    rw [Finset.mem_filter, Finset.mem_univ, true_and, DirichletCharacter.isPrimitive_def]
    have h_dvd : χ.conductor ∣ p :=
      (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ dvd_rfl).mp
        (DirichletCharacter.level_mem_conductorSet χ)
    rcases (Nat.dvd_prime hp).mp h_dvd with h1 | hp_eq
    · exfalso
      have h_mem1 : 1 ∈ χ.conductorSet := by
        rw [DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ (one_dvd p), h1]
      rw [DirichletCharacter.mem_conductorSet_iff] at h_mem1
      rcases h_mem1 with ⟨hd1, χ₀, rfl⟩
      have hcard1 : Fintype.card (DirichletCharacter ℂ 1) = 1 := by
        rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity 1 ℂ, Nat.totient_one]
      haveI : Subsingleton (DirichletCharacter ℂ 1) := Fintype.card_le_one_iff_subsingleton.mp hcard1.le
      have hχ₀ : χ₀ = 1 := Subsingleton.elim χ₀ 1
      rw [hχ₀, map_one] at hχ
      exact hχ.1 rfl
    · exact hp_eq
  have h_card := Finset.card_le_card h_sub
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity p ℂ, Nat.totient_prime hp] at h_card
  simpa [totientStar] using (show p - 2 ≤ totientStar p by omega)

private lemma totientStar_prime_pow_ge (p e : ℕ) (hp : Nat.Prime p) (he : e ≥ 2) :
    totientStar (p ^ e) ≥ Nat.totient (p ^ e) - Nat.totient (p ^ (e - 1)) := by
  classical
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  let hd : p ^ (e - 1) ∣ p ^ e := pow_dvd_pow p (Nat.sub_le e 1)
  let S_nonprim : Finset (DirichletCharacter ℂ (p ^ e)) :=
    Finset.univ.image (DirichletCharacter.changeLevel hd)
  have h_sub : Finset.univ \ S_nonprim ⊆
      Finset.univ.filter (fun χ : DirichletCharacter ℂ (p ^ e) => χ.IsPrimitive) := by
    intro χ hχ
    rw [Finset.mem_sdiff] at hχ
    rw [Finset.mem_filter, Finset.mem_univ, true_and, DirichletCharacter.isPrimitive_def]
    have h_dvd : χ.conductor ∣ p ^ e :=
      (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ dvd_rfl).mp
        (DirichletCharacter.level_mem_conductorSet χ)
    obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow hp).mp h_dvd
    by_cases hke : k = e
    · rw [hk_eq, hke]
    · exfalso
      have hk_le1 : k ≤ e - 1 := by omega
      have h_dvd1 : χ.conductor ∣ p ^ (e - 1) := by rw [hk_eq]; exact pow_dvd_pow p hk_le1
      have h_mem1 : p ^ (e - 1) ∈ χ.conductorSet :=
        (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hd).mpr h_dvd1
      rw [DirichletCharacter.mem_conductorSet_iff] at h_mem1
      rcases h_mem1 with ⟨_, χ₀, hχ₀⟩
      apply hχ.2
      exact Finset.mem_image.mpr ⟨χ₀, Finset.mem_univ _, hχ₀.symm⟩
  have h_card := Finset.card_le_card h_sub
  have h_sdiff : (Finset.univ \ S_nonprim).card ≥
      Fintype.card (DirichletCharacter ℂ (p ^ e)) - S_nonprim.card := by
    have := Finset.card_sdiff_add_card_inter Finset.univ S_nonprim
    rw [Finset.univ_inter] at this
    omega
  have h_nonprim_le : S_nonprim.card ≤ Nat.totient (p ^ (e - 1)) := by
    calc S_nonprim.card ≤ (Finset.univ : Finset (DirichletCharacter ℂ (p ^ (e - 1)))).card :=
          Finset.card_image_le
      _ = Fintype.card (DirichletCharacter ℂ (p ^ (e - 1))) := Finset.card_univ
      _ = Nat.totient (p ^ (e - 1)) :=
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity (p ^ (e - 1)) ℂ
  rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity (p ^ e) ℂ] at h_sdiff
  have h_le : Nat.totient (p ^ e) - Nat.totient (p ^ (e - 1)) ≤ totientStar (p ^ e) := by
    dsimp only [totientStar]; omega
  exact h_le

private lemma two_exact_dvd_totientStar_zero (m : ℕ) (hm : m ≥ 1) (hcop : Nat.Coprime 2 m) :
    totientStar (2 * m) = 0 := by
  classical
  haveI : NeZero (2 * m) := ⟨by omega⟩
  haveI : NeZero m := ⟨by omega⟩
  let hm_dvd : m ∣ 2 * m := dvd_mul_left m 2
  have h_inj : Function.Injective (DirichletCharacter.changeLevel (R := ℂ) hm_dvd) := by
    intro χ₁ χ₂ heq
    ext u
    by_cases hu : IsUnit u
    · obtain ⟨k, hk_2, hk_m⟩ := Nat.chineseRemainder hcop 1 u.val
      have hk1 : (k : ZMod 2) = 1 := by
        simpa using (ZMod.natCast_eq_natCast_iff k 1 2).mpr hk_2
      have hku : (k : ZMod m) = u := by
        rw [← ZMod.natCast_zmod_val u]
        exact (ZMod.natCast_eq_natCast_iff k u.val m).mpr hk_m
      have hcop_2 : IsCoprime (k : ℤ) (2 : ℤ) := by
        rw [← ZMod.isUnit_iff_coprime_int]
        simpa [hk1] using (isUnit_one : IsUnit (1 : ZMod 2))
      have hcop_m : IsCoprime (k : ℤ) (m : ℤ) := by
        rw [← ZMod.isUnit_iff_coprime_int]
        simpa [hku] using hu
      have hcop_2m : IsCoprime (k : ℤ) ((2 * m : ℕ) : ℤ) := by
        push_cast; exact hcop_2.mul_right hcop_m
      have hval := congr_arg (fun (χ : DirichletCharacter ℂ (2 * m)) => χ (k : ZMod (2 * m))) heq
      have hc1 := DirichletCharacter.changeLevel_eq_cast_of_dvd' hm_dvd χ₁ hcop_2m
      have hc2 := DirichletCharacter.changeLevel_eq_cast_of_dvd' hm_dvd χ₂ hcop_2m
      simp only [Int.cast_natCast] at hc1 hc2
      rw [hc1, hc2, hku] at hval
      exact hval
    · simp [MulChar.map_nonunit hu]
  have h_card_eq : Fintype.card (DirichletCharacter ℂ m) = Fintype.card (DirichletCharacter ℂ (2 * m)) := by
    rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity m ℂ,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity (2 * m) ℂ,
      Nat.totient_mul hcop, Nat.totient_two, one_mul]
  have h_surj : Function.Surjective (DirichletCharacter.changeLevel (R := ℂ) hm_dvd) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨h_inj, h_card_eq⟩ |>.2
  have h_empty : Finset.univ.filter (fun χ : DirichletCharacter ℂ (2 * m) => χ.IsPrimitive) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro χ _
    obtain ⟨χ₀, rfl⟩ := h_surj χ
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_changeLevel]
    have h_dvd : χ₀.conductor ∣ m :=
      (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ₀ dvd_rfl).mp
        (DirichletCharacter.level_mem_conductorSet χ₀)
    have h_le : χ₀.conductor ≤ m := Nat.le_of_dvd hm h_dvd
    omega
  simp [totientStar, h_empty]

private lemma totient_div_totientStar_le (q : ℕ) (hq : q ≥ 3) (hqstar : totientStar q ≥ 1) :
    (Nat.totient q : ℝ) / (totientStar q : ℝ) ≤ 2 * Real.exp 60 * (Real.log q) ^ 30 := by
  classical
  have hq0 : q ≠ 0 := by omega
  have h_v2_ne1 : q.factorization 2 ≠ 1 := by
    intro h1
    have h_ord := Nat.ordProj_mul_ordCompl_eq_self q 2
    have h_cop : Nat.Coprime (2 ^ q.factorization 2) (q / 2 ^ q.factorization 2) :=
      Nat.coprime_ordCompl Nat.prime_two hq0
    rw [h1, pow_one] at h_ord h_cop
    have hm_pos : q / 2 ≥ 1 := by
      have : 2 * (q / 2) = q := h_ord
      omega
    have h0 := two_exact_dvd_totientStar_zero (q / 2) hm_pos h_cop
    rw [h_ord] at h0
    omega
  have h_prod_star : ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) →
      ∏ p ∈ s, totientStar (p ^ (q.factorization p)) ≤
        totientStar (∏ p ∈ s, p ^ (q.factorization p)) := by
    intro s hs
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      have h1 : totientStar 1 = 1 := by
        have h_card : Fintype.card (DirichletCharacter ℂ 1) = 1 := by
          rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity 1 ℂ, Nat.totient_one]
        haveI : Unique (DirichletCharacter ℂ 1) := Fintype.card_eq_one_iff_unique.mp h_card |>.some
        have h_eq : Finset.univ.filter (fun χ : DirichletCharacter ℂ 1 => χ.IsPrimitive) = Finset.univ := by
          ext χ; simp [Subsingleton.elim χ 1, DirichletCharacter.isPrimitive_one_level_one]
        simp [totientStar, h_eq, h_card]
      omega
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have ha_prime : Nat.Prime a := hs a (Finset.mem_insert_self _ _)
      have hs_prime : ∀ p ∈ s, Nat.Prime p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
      have ha_pos : a ^ q.factorization a ≥ 1 := Nat.one_le_pow _ _ ha_prime.pos
      have hs_pos : ∏ p ∈ s, p ^ q.factorization p ≥ 1 :=
        Finset.prod_pos fun p hp => Nat.pow_pos (hs_prime p hp).pos
      have h_cop : Nat.Coprime (a ^ q.factorization a) (∏ p ∈ s, p ^ q.factorization p) := by
        refine Nat.Coprime.prod_right fun p hp => ?_
        have hp_prime := hs_prime p hp
        have hne : a ≠ p := fun h => ha (h ▸ hp)
        exact ((Nat.coprime_primes ha_prime hp_prime).mpr hne).pow _ _
      calc totientStar (a ^ q.factorization a) * ∏ p ∈ s, totientStar (p ^ q.factorization p)
          ≤ totientStar (a ^ q.factorization a) * totientStar (∏ p ∈ s, p ^ q.factorization p) :=
            Nat.mul_le_mul_left _ (ih hs_prime)
        _ ≤ totientStar (a ^ q.factorization a * ∏ p ∈ s, p ^ q.factorization p) :=
            totientStar_mul_ge _ _ ha_pos hs_pos h_cop
  have h_prod_tot : ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) →
      Nat.totient (∏ p ∈ s, p ^ (q.factorization p)) =
        ∏ p ∈ s, Nat.totient (p ^ (q.factorization p)) := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have ha_prime : Nat.Prime a := hs a (Finset.mem_insert_self _ _)
      have hs_prime : ∀ p ∈ s, Nat.Prime p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
      have h_cop : Nat.Coprime (a ^ q.factorization a) (∏ p ∈ s, p ^ q.factorization p) := by
        refine Nat.Coprime.prod_right fun p hp => ?_
        have hp_prime := hs_prime p hp
        have hne : a ≠ p := fun h => ha (h ▸ hp)
        exact ((Nat.coprime_primes ha_prime hp_prime).mpr hne).pow _ _
      rw [Nat.totient_mul h_cop, ih hs_prime]
  have h_fac_eq : ∏ p ∈ q.primeFactors, p ^ q.factorization p = q :=
    Nat.factorization_prod_pow_eq_self hq0
  have h_pf_prime : ∀ p ∈ q.primeFactors, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors hp
  have h_star_lb : ∏ p ∈ q.primeFactors, totientStar (p ^ q.factorization p) ≤ totientStar q := by
    simpa [h_fac_eq] using h_prod_star q.primeFactors h_pf_prime
  have h_tot_eq : Nat.totient q = ∏ p ∈ q.primeFactors, Nat.totient (p ^ q.factorization p) := by
    simpa [h_fac_eq] using h_prod_tot q.primeFactors h_pf_prime
  have h_ratio_term : ∀ p ∈ q.primeFactors,
      (Nat.totient (p ^ q.factorization p) : ℝ) / (totientStar (p ^ q.factorization p) : ℝ) ≤
        if p = 2 then 2 else ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
    intro p hp
    have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have he_pos : 1 ≤ q.factorization p := Nat.Prime.factorization_pos_of_dvd hp_prime hq0 (Nat.dvd_of_mem_primeFactors hp)
    split_ifs with hp2
    · subst hp2
      have he2 : 2 ≤ q.factorization 2 := by omega
      have h_star := totientStar_prime_pow_ge 2 (q.factorization 2) Nat.prime_two he2
      have h_t1 : Nat.totient (2 ^ q.factorization 2) = 2 ^ (q.factorization 2 - 1) := by
        rw [Nat.totient_prime_pow Nat.prime_two (by omega)]; ring
      have h_t2 : Nat.totient (2 ^ (q.factorization 2 - 1)) = 2 ^ (q.factorization 2 - 2) := by
        rw [Nat.totient_prime_pow Nat.prime_two (by omega)]; ring
      have h_t_eq : Nat.totient (2 ^ q.factorization 2) = 2 * Nat.totient (2 ^ (q.factorization 2 - 1)) := by
        rw [h_t1, h_t2, ← pow_succ']; congr 1; omega
      have h_s_pos : 1 ≤ totientStar (2 ^ q.factorization 2) := by
        have : 1 ≤ Nat.totient (2 ^ (q.factorization 2 - 1)) := by rw [h_t2]; exact Nat.one_le_pow _ _ (by norm_num)
        omega
      rw [div_le_iff₀ (by exact_mod_cast h_s_pos)]
      norm_cast; omega
    · have hp3 : p ≥ 3 := by have := hp_prime.two_le; omega
      have hp_real : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      rcases Nat.eq_or_lt_of_le he_pos with he1 | he2
      · rw [← he1, pow_one]
        have h_star := totientStar_prime_ge p hp_prime hp3
        rw [Nat.totient_prime hp_prime]
        have h_s_pos : (0 : ℝ) < totientStar p := by
          have : 1 ≤ p - 2 := by omega
          exact_mod_cast (show 1 ≤ totientStar p by omega)
        have h_s_ge : (p : ℝ) - 2 ≤ totientStar p := by
          have : (p - 2 : ℝ) = (p : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
          rw [← this]; exact_mod_cast h_star
        have h_p1 : (p - 1 : ℝ) = ((p - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub (by omega)]; norm_num
        rw [← h_p1]
        calc ((p : ℝ) - 1) / (totientStar p : ℝ)
            ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) := by gcongr; linarith
          _ ≤ ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
              rw [div_pow, div_le_div_iff₀ (by linarith) (sq_pos_of_pos (by linarith))]
              nlinarith
      · have h_star := totientStar_prime_pow_ge p (q.factorization p) hp_prime he2
        have h_t1 : Nat.totient (p ^ q.factorization p) = p ^ (q.factorization p - 1) * (p - 1) :=
          Nat.totient_prime_pow hp_prime (by omega)
        have h_t2 : Nat.totient (p ^ (q.factorization p - 1)) = p ^ (q.factorization p - 2) * (p - 1) :=
          Nat.totient_prime_pow hp_prime (by omega)
        have h_s_lb : p ^ (q.factorization p - 2) * (p - 1) ^ 2 ≤ totientStar (p ^ q.factorization p) := by
          have h_pow : p ^ (q.factorization p - 1) = p ^ (q.factorization p - 2) * p := by
            rw [← pow_succ]; congr 1; omega
          rw [h_t1, h_t2, h_pow] at h_star
          have h_sub : p ^ (q.factorization p - 2) * p * (p - 1) - p ^ (q.factorization p - 2) * (p - 1) =
              p ^ (q.factorization p - 2) * (p - 1) ^ 2 := by
            zify [show 1 ≤ p by omega]; ring
          omega
        have h_s_pos : (0 : ℝ) < totientStar (p ^ q.factorization p) := by
          have : 1 ≤ p ^ (q.factorization p - 2) * (p - 1) ^ 2 :=
            Nat.mul_pos (Nat.pow_pos hp_prime.pos) (sq_pos_of_pos (by omega))
          exact_mod_cast this.trans_le h_s_lb
        have h_s_real : ((p : ℝ) ^ (q.factorization p - 2)) * ((p : ℝ) - 1) ^ 2 ≤
            (totientStar (p ^ q.factorization p) : ℝ) := by
          have h1 : ((p ^ (q.factorization p - 2) * (p - 1) ^ 2 : ℕ) : ℝ) ≤ totientStar (p ^ q.factorization p) := by
            exact_mod_cast h_s_lb
          push_cast [Nat.cast_sub (show 1 ≤ p by omega)] at h1
          exact h1
        have h_t_real : (Nat.totient (p ^ q.factorization p) : ℝ) =
            (p : ℝ) ^ (q.factorization p - 1) * ((p : ℝ) - 1) := by
          rw [h_t1]; push_cast [Nat.cast_sub (show 1 ≤ p by omega)]; rfl
        have h_pow_r : (p : ℝ) ^ (q.factorization p - 1) = (p : ℝ) ^ (q.factorization p - 2) * (p : ℝ) := by
          rw [← pow_succ]; congr 1; omega
        rw [h_t_real, h_pow_r]
        calc ((p : ℝ) ^ (q.factorization p - 2) * (p : ℝ) * ((p : ℝ) - 1)) / (totientStar (p ^ q.factorization p) : ℝ)
            ≤ ((p : ℝ) ^ (q.factorization p - 2) * (p : ℝ) * ((p : ℝ) - 1)) /
                ((p : ℝ) ^ (q.factorization p - 2) * ((p : ℝ) - 1) ^ 2) := by
              gcongr; positivity
          _ = (p : ℝ) / ((p : ℝ) - 1) := by
              have hne1 : (p : ℝ) ^ (q.factorization p - 2) ≠ 0 := by positivity
              have hne2 : (p : ℝ) - 1 ≠ 0 := by linarith
              field_simp [hne1, hne2]
          _ ≤ ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
              have h1 : 1 ≤ (p : ℝ) / ((p : ℝ) - 1) := by rw [one_le_div (by linarith)]; linarith
              nlinarith
  have h_star_pos_each : ∀ p ∈ q.primeFactors, 0 < (totientStar (p ^ q.factorization p) : ℝ) := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have he_pos : 1 ≤ q.factorization p := Nat.Prime.factorization_pos_of_dvd hp_prime hq0 (Nat.dvd_of_mem_primeFactors hp)
    by_cases hp2 : p = 2
    · subst hp2
      have he2 : 2 ≤ q.factorization 2 := by omega
      have h_star := totientStar_prime_pow_ge 2 (q.factorization 2) Nat.prime_two he2
      have h_t1 : Nat.totient (2 ^ q.factorization 2) = 2 ^ (q.factorization 2 - 1) := by
        rw [Nat.totient_prime_pow Nat.prime_two (by omega)]; ring
      have h_t2 : Nat.totient (2 ^ (q.factorization 2 - 1)) = 2 ^ (q.factorization 2 - 2) := by
        rw [Nat.totient_prime_pow Nat.prime_two (by omega)]; ring
      have : 1 ≤ totientStar (2 ^ q.factorization 2) := by
        have h_pow : 2 ^ (q.factorization 2 - 1) = 2 * 2 ^ (q.factorization 2 - 2) := by
          rw [← pow_succ']; congr 1; omega
        have : 1 ≤ 2 ^ (q.factorization 2 - 2) := Nat.one_le_pow _ _ (by norm_num)
        omega
      exact_mod_cast this
    · have hp3 : p ≥ 3 := by have := hp_prime.two_le; omega
      rcases Nat.eq_or_lt_of_le he_pos with he1 | he2
      · rw [← he1, pow_one]
        have h_star := totientStar_prime_ge p hp_prime hp3
        exact_mod_cast (show 1 ≤ totientStar p by omega)
      · have h_star := totientStar_prime_pow_ge p (q.factorization p) hp_prime he2
        have h_t1 : Nat.totient (p ^ q.factorization p) = p ^ (q.factorization p - 1) * (p - 1) :=
          Nat.totient_prime_pow hp_prime (by omega)
        have h_t2 : Nat.totient (p ^ (q.factorization p - 1)) = p ^ (q.factorization p - 2) * (p - 1) :=
          Nat.totient_prime_pow hp_prime (by omega)
        have : 1 ≤ totientStar (p ^ q.factorization p) := by
          have h_pow : p ^ (q.factorization p - 1) = p ^ (q.factorization p - 2) * p := by
            rw [← pow_succ]; congr 1; omega
          rw [h_t1, h_t2, h_pow] at h_star
          have h_sub : p ^ (q.factorization p - 2) * p * (p - 1) - p ^ (q.factorization p - 2) * (p - 1) =
              p ^ (q.factorization p - 2) * (p - 1) ^ 2 := by
            zify [show 1 ≤ p by omega]; ring
          have : 1 ≤ p ^ (q.factorization p - 2) * (p - 1) ^ 2 :=
            Nat.mul_pos (Nat.pow_pos hp_prime.pos) (sq_pos_of_pos (by omega))
          omega
        exact_mod_cast this
  have h_prod_pos : (0 : ℝ) < ∏ p ∈ q.primeFactors, (totientStar (p ^ q.factorization p) : ℝ) :=
    Finset.prod_pos h_star_pos_each
  have h_ratio_prod : (Nat.totient q : ℝ) / (totientStar q : ℝ) ≤
      2 * ∏ p ∈ q.primeFactors.filter (· ≠ 2), ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
    have h_le1 : (Nat.totient q : ℝ) / (totientStar q : ℝ) ≤
        ∏ p ∈ q.primeFactors, ((Nat.totient (p ^ q.factorization p) : ℝ) /
          (totientStar (p ^ q.factorization p) : ℝ)) := by
      rw [← Finset.prod_div_distrib]
      have h_num : (Nat.totient q : ℝ) = ∏ p ∈ q.primeFactors, (Nat.totient (p ^ q.factorization p) : ℝ) := by
        exact_mod_cast h_tot_eq
      have h_den : ∏ p ∈ q.primeFactors, (totientStar (p ^ q.factorization p) : ℝ) ≤ (totientStar q : ℝ) := by
        exact_mod_cast h_star_lb
      rw [h_num]
      exact div_le_div_of_nonneg_left (Finset.prod_nonneg fun p _ => by positivity) h_prod_pos h_den
    have h_le2 : ∏ p ∈ q.primeFactors, ((Nat.totient (p ^ q.factorization p) : ℝ) /
          (totientStar (p ^ q.factorization p) : ℝ)) ≤
        ∏ p ∈ q.primeFactors, (if p = 2 then (2 : ℝ) else ((p : ℝ) / ((p : ℝ) - 1)) ^ 2) := by
      refine Finset.prod_le_prod (fun p _ => by positivity) (fun p hp => h_ratio_term p hp)
    have h_split : ∏ p ∈ q.primeFactors, (if p = 2 then (2 : ℝ) else ((p : ℝ) / ((p : ℝ) - 1)) ^ 2) ≤
        2 * ∏ p ∈ q.primeFactors.filter (· ≠ 2), ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
      by_cases h2 : 2 ∈ q.primeFactors
      · rw [← Finset.mul_prod_erase q.primeFactors _ h2, if_pos rfl]
        gcongr
        have h_er : q.primeFactors.erase 2 = q.primeFactors.filter (· ≠ 2) := by
          ext p; simp [Finset.mem_erase, Finset.mem_filter, and_comm]
        rw [h_er]
        refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
        rw [Finset.mem_filter] at hp
        rw [if_neg hp.2]
      · have h_f : q.primeFactors.filter (· ≠ 2) = q.primeFactors := by
          rw [Finset.filter_eq_self]; intro p hp hpe; exact h2 (hpe ▸ hp)
        rw [h_f]
        have h_eq : ∏ p ∈ q.primeFactors, (if p = 2 then (2 : ℝ) else ((p : ℝ) / ((p : ℝ) - 1)) ^ 2) =
            ∏ p ∈ q.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
          refine Finset.prod_congr rfl fun p hp => ?_
          rw [if_neg (fun h => h2 (h ▸ hp))]
        rw [h_eq]
        have h_nn : 0 ≤ ∏ p ∈ q.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 :=
          Finset.prod_nonneg fun p _ => by positivity
        linarith
    exact h_le1.trans (h_le2.trans h_split)
  have h_log_prod : Real.log (∏ p ∈ q.primeFactors.filter (· ≠ 2), ((p : ℝ) / ((p : ℝ) - 1)) ^ 2) ≤
      30 * Real.log (Real.log q) + 60 := by
    have h_pos_each : ∀ p ∈ q.primeFactors.filter (· ≠ 2), ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 ≠ 0 := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp.1
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show p ≥ 3 by have := hp_prime.two_le; omega)
      positivity
    rw [Real.log_prod _ _ h_pos_each]
    have h_term : ∀ p ∈ q.primeFactors.filter (· ≠ 2),
        Real.log (((p : ℝ) / ((p : ℝ) - 1)) ^ 2) ≤ 3 * ((1 : ℝ) / p) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp.1
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show p ≥ 3 by have := hp_prime.two_le; omega)
      rw [Real.log_pow, Nat.cast_ofNat]
      have h_log1 := Real.log_le_sub_one_of_pos (show 0 < (p : ℝ) / ((p : ℝ) - 1) by positivity)
      have h_sub : (p : ℝ) / ((p : ℝ) - 1) - 1 = 1 / ((p : ℝ) - 1) := by
        field_simp [show (p : ℝ) - 1 ≠ 0 by linarith]; ring
      have h_le : 2 * (1 / ((p : ℝ) - 1)) ≤ 3 * (1 / (p : ℝ)) := by
        rw [mul_one_div, mul_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
        linarith
      linarith
    have h_sum1 : ∑ p ∈ q.primeFactors.filter (· ≠ 2), Real.log (((p : ℝ) / ((p : ℝ) - 1)) ^ 2) ≤
        3 * ∑ p ∈ q.primeFactors.filter (· ≠ 2), (1 : ℝ) / p := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum h_term
    have h_sub_icc : q.primeFactors.filter (· ≠ 2) ⊆ (Finset.Icc 2 q).filter Nat.Prime := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      have hp_prime := Nat.prime_of_mem_primeFactors hp.1
      have hp_dvd := Nat.dvd_of_mem_primeFactors hp.1
      exact ⟨Finset.mem_Icc.mpr ⟨hp_prime.two_le, Nat.le_of_dvd (by omega) hp_dvd⟩, hp_prime⟩
    have h_sum2 : ∑ p ∈ q.primeFactors.filter (· ≠ 2), (1 : ℝ) / p ≤
        ∑ p ∈ (Finset.Icc 2 q).filter Nat.Prime, (1 : ℝ) / p :=
      Finset.sum_le_sum_of_subset_of_nonneg h_sub_icc (fun p _ _ => by positivity)
    have h_mert := mertens_second q hq
    linarith
  have h_exp_prod : ∏ p ∈ q.primeFactors.filter (· ≠ 2), ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 ≤
      Real.exp 60 * (Real.log q) ^ 30 := by
    have h_prod_pos2 : 0 < ∏ p ∈ q.primeFactors.filter (· ≠ 2), ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
      refine Finset.prod_pos fun p hp => ?_
      rw [Finset.mem_filter] at hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp.1
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show p ≥ 3 by have := hp_prime.two_le; omega)
      positivity
    have h_logq_pos : 0 < Real.log q := by
      apply Real.log_pos; exact_mod_cast (by omega : 1 < q)
    rw [← Real.exp_log h_prod_pos2]
    calc Real.exp (Real.log (∏ p ∈ q.primeFactors.filter (· ≠ 2), ((p : ℝ) / ((p : ℝ) - 1)) ^ 2))
        ≤ Real.exp (30 * Real.log (Real.log q) + 60) := Real.exp_le_exp.mpr h_log_prod
      _ = Real.exp 60 * Real.exp ((30 : ℕ) * Real.log (Real.log q)) := by
          rw [Real.exp_add]; push_cast; ring_nf
      _ = Real.exp 60 * (Real.log q) ^ 30 := by
          rw [← Real.log_pow, Real.exp_log (pow_pos h_logq_pos 30)]
  calc (Nat.totient q : ℝ) / (totientStar q : ℝ)
      ≤ 2 * ∏ p ∈ q.primeFactors.filter (· ≠ 2), ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := h_ratio_prod
    _ ≤ 2 * (Real.exp 60 * (Real.log q) ^ 30) := by gcongr
    _ = 2 * Real.exp 60 * (Real.log q) ^ 30 := by ring

private lemma q_aspect_polar_ld_core (D : LFunctionData) (t₀ θ : ℝ) (hθ : |θ| < Real.pi / 2) :
    ∃ (c A : ℝ), c > 0 ∧ A > 1 ∧
      ∃ q₀ : ℕ, q₀ ≥ 3 ∧
        ∀ (q : ℕ) (hq1 : q ≥ 1), q ≥ q₀ → totientStar q ≥ 1 →
          (∀ (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive), D.GRH q hq1 χ hχ) →
          ∀ V : ℝ, A * Real.log (Real.log q) ≤ V → V ≤ Real.log q / Real.log (Real.log q) →
          (1 / (totientStar q : ℝ)) *
            ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
              χ.IsPrimitive ∧ D.nonvanishing q χ t₀ ∧ polarLogL D q χ t₀ θ ≥ V)).card : ℝ) ≤
            Real.exp (-c * V * Real.log (V / Real.log (Real.log q))) := by
  obtain ⟨C₀, hC₀, h_hzs⟩ := horizontal_zero_sum_external D
  obtain ⟨C₁, hC₁, h_gw⟩ := guinand_weil_external D
  obtain ⟨Δ₀, C_sup, C_L1, C_err_M, hΔ₀, hC_sup, hC_L1, hC_err_M, h_maj⟩ := asymmetric_majorant θ hθ
  have hK_int := kernelK_integrable θ
  have hK_int_val : ∫ x : ℝ, kernelK θ x = -Real.pi * Real.cos θ := kernelK_integral_eq θ
  let C_L1_tot : ℝ := max C_L1 (2 * envelopeC θ + C_err_M + 1)
  obtain ⟨C_tail, hC_tail, h_tail⟩ := prime_power_tail_bounds θ C_L1_tot Δ₀ hθ.le hΔ₀
  obtain ⟨B, hB, h_mom⟩ := prime_moment_q_aspect θ C_L1_tot Δ₀ hθ.le hΔ₀
  have hC_env : 0 < envelopeC θ := envelopeC_pos hθ
  let K_scale : ℝ := max 1 (2 * envelopeC θ / Real.pi)
  have hK_scale_pos : 0 < K_scale := by positivity
  let C_B : ℝ := 16 * Real.exp 61 * B * (2 * Real.pi * K_scale)
  let A : ℝ := max 2 (max (320 * (2 * Real.pi * K_scale) + 1)
    (max (Real.exp 1 * C_B + 1) (max (C_B ^ 2 + 1) (8 * C_tail + 8 * C₀ + 8 * C₁ * C_sup + 8 * C_err_M + 8))))
  have hA_gt_1 : A > 1 := by
    linarith [le_max_left (2 : ℝ) (max (320 * (2 * Real.pi * K_scale) + 1)
      (max (Real.exp 1 * C_B + 1) (max (C_B ^ 2 + 1) (8 * C_tail + 8 * C₀ + 8 * C₁ * C_sup + 8 * C_err_M + 8))))]
  let L_min : ℝ := max (max 100 (Real.pi * Δ₀ / K_scale + 1)) (max (16 * Real.pi * K_scale) 10)
  let q₀ : ℕ := max (Nat.ceil (|t₀| + 2) + 3) (Nat.ceil (Real.exp (Real.exp L_min)) + 3)
  let c : ℝ := 3 / (64 * (2 * Real.pi * K_scale))
  refine ⟨c, A, by positivity, hA_gt_1, q₀, le_trans (by omega) (le_max_left _ _), ?_⟩
  intro q hq1 hq_ge hqstar hGRH_all V hV_lb hV_ub
  have hq_ge_3 : q ≥ 3 := by omega
  have hq_pos : (0 : ℝ) < q := by positivity
  have hq_ge_exp : Real.exp (Real.exp L_min) ≤ (q : ℝ) := by
    have h1 : Nat.ceil (Real.exp (Real.exp L_min)) + 3 ≤ q := le_trans (le_max_right _ _) hq_ge
    have h2 : Real.exp (Real.exp L_min) ≤ (Nat.ceil (Real.exp (Real.exp L_min)) : ℝ) := Nat.le_ceil _
    have h3 : (Nat.ceil (Real.exp (Real.exp L_min)) : ℝ) ≤ q := by
      exact_mod_cast (by omega : Nat.ceil (Real.exp (Real.exp L_min)) ≤ q)
    linarith
  have hlogq_ge_exp : Real.exp L_min ≤ Real.log q := by
    rw [← Real.log_exp (Real.exp L_min)]; exact Real.log_le_log (Real.exp_pos _) hq_ge_exp
  have hLLq_ge : L_min ≤ Real.log (Real.log q) := by
    rw [← Real.log_exp L_min]; exact Real.log_le_log (Real.exp_pos _) hlogq_ge_exp
  have hLLq_ge_10 : 10 ≤ Real.log (Real.log q) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLLq_ge
  have hLLq_pos : 0 < Real.log (Real.log q) := by linarith
  have hlogq_pos : 0 < Real.log q := by linarith [Real.exp_pos L_min]
  have ht0_le_q : |t₀| + 2 ≤ (q : ℝ) := by
    have h1 : Nat.ceil (|t₀| + 2) + 3 ≤ q := le_trans (le_max_left _ _) hq_ge
    have h2 : |t₀| + 2 ≤ (Nat.ceil (|t₀| + 2) : ℝ) := Nat.le_ceil _
    have h3 : (Nat.ceil (|t₀| + 2) : ℝ) ≤ q := by exact_mod_cast (by omega : Nat.ceil (|t₀| + 2) ≤ q)
    linarith
  have hac_le_q2 : analyticConductor q t₀ ≤ (q : ℝ) ^ 2 := by
    unfold analyticConductor; nlinarith
  have hac_ge_q : (q : ℝ) ≤ analyticConductor q t₀ := by
    unfold analyticConductor; have : 2 ≤ |t₀| + 2 := by linarith [abs_nonneg t₀]
    nlinarith
  have hlog_ac_le : Real.log (analyticConductor q t₀) ≤ 2 * Real.log q := by
    have h1 : Real.log (analyticConductor q t₀) ≤ Real.log ((q : ℝ) ^ 2) :=
      Real.log_le_log (by unfold analyticConductor; positivity) hac_le_q2
    rwa [Real.log_pow] at h1
  have hlog_ac_ge : Real.log q ≤ Real.log (analyticConductor q t₀) :=
    Real.log_le_log hq_pos hac_ge_q
  have hV_pos : 0 < V := by
    have : 0 < A := by linarith
    nlinarith
  let Δ : ℝ := K_scale * Real.log (analyticConductor q t₀) / V
  have hΔ_ge_Δ₀ : Δ₀ ≤ Δ := by
    have h1 : K_scale * Real.log (Real.log q) ≤ Δ := by
      dsimp only [Δ]; rw [le_div_iff₀ hV_pos]
      have h_v : V * Real.log (Real.log q) ≤ Real.log q := by rwa [le_div_iff₀ hLLq_pos] at hV_ub
      calc K_scale * Real.log (Real.log q) * V = K_scale * (V * Real.log (Real.log q)) := by ring
        _ ≤ K_scale * Real.log q := by gcongr
        _ ≤ K_scale * Real.log (analyticConductor q t₀) := by gcongr
    have h2 : Δ₀ ≤ K_scale * Real.log (Real.log q) := by
      have h_l : Real.pi * Δ₀ / K_scale + 1 ≤ Real.log (Real.log q) :=
        le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLLq_ge
      rw [div_add_one (by positivity), div_le_iff₀ (by positivity)] at h_l
      nlinarith [Real.two_le_pi]
    exact h2.trans h1
  have hΔ_ge_1 : 1 ≤ Δ := le_trans hΔ₀ hΔ_ge_Δ₀
  have hΔ_pos : 0 < Δ := by linarith
  let X : ℝ := Real.exp (2 * Real.pi * Δ)
  have hlogX_eq : Real.log X = 2 * Real.pi * Δ := Real.log_exp _
  have hlogX_le_half : Real.log X ≤ Real.log q / 2 := by
    rw [hlogX_eq]
    have h_l : 16 * Real.pi * K_scale ≤ Real.log (Real.log q) :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLLq_ge
    have h_a : 2 ≤ A := le_max_left _ _
    have h_v2 : 16 * Real.pi * K_scale ≤ V := by nlinarith
    calc 2 * Real.pi * Δ = 2 * Real.pi * K_scale * Real.log (analyticConductor q t₀) / V := by
          dsimp only [Δ]; ring
      _ ≤ 2 * Real.pi * K_scale * (2 * Real.log q) / V := by gcongr
      _ = (4 * Real.pi * K_scale / V) * Real.log q := by ring
      _ ≤ (1 / 2 : ℝ) * Real.log q := by gcongr; rw [div_le_iff₀ hV_pos]; linarith
      _ = Real.log q / 2 := by ring
  have hX_le_q : X ≤ (q : ℝ) := by
    rw [← Real.log_le_log_iff (Real.exp_pos _) hq_pos, Real.log_exp]; linarith [hlogX_le_half, hlogX_eq]
  have hlogX_pos : 0 < Real.log X := by rw [hlogX_eq]; positivity
  let k : ℕ := Nat.floor ((3 / 4 : ℝ) * (Real.log q / Real.log X))
  have hk_ge_1 : 1 ≤ k := by
    have h1 : (3 / 2 : ℝ) ≤ (3 / 4 : ℝ) * (Real.log q / Real.log X) := by
      have : 2 ≤ Real.log q / Real.log X := by rw [le_div_iff₀ hlogX_pos]; linarith
      linarith
    exact Nat.le_floor (by linarith)
  have hk_pos : 0 < k := by omega
  have hXk_lt_q : X ^ k < (q : ℝ) := by
    rw [← Real.log_lt_log_iff (pow_pos (Real.exp_pos _) _) hq_pos, Real.log_pow]
    have hk_le := Nat.floor_le (by positivity : 0 ≤ (3 / 4 : ℝ) * (Real.log q / Real.log X))
    have h1 : (k : ℝ) * Real.log X ≤ (3 / 4 : ℝ) * Real.log q := by
      calc (k : ℝ) * Real.log X ≤ (3 / 4 : ℝ) * (Real.log q / Real.log X) * Real.log X := by gcongr
        _ = (3 / 4 : ℝ) * Real.log q := by field_simp [hlogX_pos.ne']
    linarith
  have hk_lb : (3 : ℝ) * V / (16 * (2 * Real.pi * K_scale)) ≤ (k : ℝ) := by
    have h_lt : (3 / 4 : ℝ) * (Real.log q / Real.log X) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have h_l : 16 * Real.pi * K_scale ≤ Real.log (Real.log q) :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLLq_ge
    have h_a : 2 ≤ A := le_max_left _ _
    have h_v2 : 16 * Real.pi * K_scale ≤ V := by nlinarith
    have h_lx : Real.log X ≤ 4 * Real.pi * K_scale * Real.log q / V := by
      rw [hlogX_eq]
      calc 2 * Real.pi * Δ = 2 * Real.pi * K_scale * Real.log (analyticConductor q t₀) / V := by
            dsimp only [Δ]; ring
        _ ≤ 2 * Real.pi * K_scale * (2 * Real.log q) / V := by gcongr
        _ = 4 * Real.pi * K_scale * Real.log q / V := by ring
    have h_div : V / (4 * Real.pi * K_scale) ≤ Real.log q / Real.log X := by
      rw [div_le_div_iff₀ (by positivity) hlogX_pos]
      rw [le_div_iff₀ hV_pos] at h_lx; nlinarith
    have h_34 : (3 / 4 : ℝ) * (V / (4 * Real.pi * K_scale)) ≤ (3 / 4 : ℝ) * (Real.log q / Real.log X) := by
      gcongr
    have h_ge3 : 3 ≤ (3 / 4 : ℝ) * (V / (4 * Real.pi * K_scale)) := by
      rw [← div_le_iff₀ (by positivity : (0 : ℝ) < 3 / 4)]
      rw [le_div_iff₀ (by positivity)]
      linarith
    have h_k2 : (1 / 2 : ℝ) * ((3 / 4 : ℝ) * (Real.log q / Real.log X)) ≤ (k : ℝ) := by linarith
    linarith
  have hk_ub : (k : ℝ) ≤ V / (2 * Real.pi * K_scale) := by
    have hk_le := Nat.floor_le (by positivity : 0 ≤ (3 / 4 : ℝ) * (Real.log q / Real.log X))
    have h_lx : 2 * Real.pi * K_scale * Real.log q / V ≤ Real.log X := by
      rw [hlogX_eq]; dsimp only [Δ]
      calc 2 * Real.pi * K_scale * Real.log q / V
          ≤ 2 * Real.pi * K_scale * Real.log (analyticConductor q t₀) / V := by gcongr
        _ = 2 * Real.pi * (K_scale * Real.log (analyticConductor q t₀) / V) := by ring
    calc (k : ℝ) ≤ (3 / 4 : ℝ) * (Real.log q / Real.log X) := hk_le
      _ ≤ Real.log q / Real.log X := by linarith [div_nonneg hlogq_pos.le hlogX_pos.le]
      _ ≤ Real.log q / (2 * Real.pi * K_scale * Real.log q / V) :=
          div_le_div_of_nonneg_left hlogq_pos.le (by positivity) h_lx
      _ = V / (2 * Real.pi * K_scale) := by
          field_simp [hlogq_pos.ne', hK_scale_pos.ne', Real.pi_ne_zero]; ring
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
      rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]; exact h3
    have h3 : Real.exp (-2 * Real.pi * Δ) ≤ 1 / Δ := by rwa [le_div_iff₀ hΔ_pos, mul_comm]
    calc ∫ x : ℝ, (majorantM θ Δ α x - kernelK θ x)
        ≤ 2 * envelopeC θ / Δ + C_err_M * (1 / Δ) := by linarith [mul_le_mul_of_nonneg_left h3 hC_err_M.le]
      _ = (2 * envelopeC θ + C_err_M) / Δ := by ring
      _ ≤ C_L1_tot / Δ := by gcongr; exact le_trans (by linarith) (le_max_right C_L1 _)
  have hM_L1_tot : ∫ x : ℝ, |majorantM θ Δ α x| ≤ C_L1_tot :=
    hM_L1.trans (le_max_left _ _)
  have h_tail_bd := h_tail q
  let S_target := Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
    χ.IsPrimitive ∧ D.nonvanishing q χ t₀ ∧ polarLogL D q χ t₀ θ ≥ V)
  let S_large := Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
    χ.IsPrimitive ∧ |primeSum1 q χ h_hat X t₀| ≥ V / 4)
  have h_subset : S_target ⊆ S_large := by
    intro χ hχ
    rw [Finset.mem_filter] at hχ ⊢
    rcases hχ with ⟨_, hχ_prim, hχ_nv, hχ_pol⟩
    refine ⟨Finset.mem_univ _, hχ_prim, ?_⟩
    have hGRH := hGRH_all χ hχ_prim
    have hq1_t : q = 1 → |t₀| ≥ 10 := fun hq_eq1 => by omega
    obtain ⟨hsumm_K, h_hzs_bd⟩ := h_hzs q hq1 χ hχ_prim hGRH θ hθ t₀ hχ_nv hq1_t
    have hM_im : ∀ x : ℝ, (M_entire x).im = 0 := fun x => (hM_real x).1
    have hM_sup_bd : ∀ x : ℝ, ‖M_entire x‖ ≤ (C_sup * Real.log Δ) / (1 + x ^ 2) := by
      intro x
      have hre : M_entire x = ((majorantM θ Δ α x : ℝ) : ℂ) := Complex.ext (hM_real x).2 (hM_real x).1
      rw [hre, Complex.norm_real, Real.norm_eq_abs, le_div_iff₀ (by positivity : 0 < 1 + x ^ 2), mul_comm]
      exact hM_sup x
    obtain ⟨hsumm_M, h_gw_bd⟩ := h_gw q hq1 χ hχ_prim hGRH M_entire Δ (C_sup * Real.log Δ)
      hΔ_ge_1 (mul_nonneg hC_sup.le (Real.log_nonneg hΔ_ge_1)) hM_exp hM_sup_bd hM_im t₀ hq1_t
    have h_sum_le : ∑' n : ℕ, kernelK θ (t₀ - D.zeros q χ n) ≤ ∑' n : ℕ, (M_entire (t₀ - D.zeros q χ n)).re := by
      refine Summable.tsum_le_tsum (fun n => ?_) hsumm_K hsumm_M
      rw [(hM_real _).2]; exact hM_maj _ (sub_ne_zero.mpr (D.nonvanishing_zeros q χ t₀ hχ_nv n))
    have hM_int_re : (∫ x : ℝ, (M_entire x).re) = (∫ x : ℝ, majorantM θ Δ α x - kernelK θ x) + (-Real.pi * Real.cos θ) := by
      have heq_M : (fun x : ℝ => (M_entire x).re) = fun x => majorantM θ Δ α x := funext fun x => (hM_real x).2
      rw [heq_M, ← hK_int_val, ← integral_add hM_int hK_int]
      congr 1; ext x; ring
    have h_hat_eq : fourierHat (fun x : ℝ => M_entire x) = h_hat := by
      ext ξ; unfold fourierHat; congr 1; ext x
      have hre : M_entire x = ((majorantM θ Δ α x : ℝ) : ℂ) := Complex.ext (hM_real x).2 (hM_real x).1
      rw [hre]
    rw [h_hat_eq] at h_gw_bd
    set Q : ℝ := analyticConductor q t₀
    have hQ_ge_100 : 100 ≤ Q := by
      have h_q100 : (100 : ℝ) ≤ q := by
        have : (100 : ℝ) ≤ Real.exp (Real.exp 100) := by
          have : (100 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
          linarith [Real.add_one_le_exp (Real.exp 100)]
        have : Real.exp (Real.exp 100) ≤ Real.exp (Real.exp L_min) :=
          Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (le_trans (le_max_left _ _) (le_max_left _ _)))
        linarith
      exact h_q100.trans hac_ge_q
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
      have h_k : 2 * envelopeC θ / Real.pi ≤ K_scale := le_max_right _ _
      calc envelopeC θ * (Real.log Q / (Real.pi * Δ))
          = (envelopeC θ / (Real.pi * K_scale)) * V := by
            dsimp only [Δ, Q]; field_simp [Real.pi_ne_zero, hK_scale_pos.ne', hV_pos.ne']; ring
        _ ≤ (1 / 2 : ℝ) * V := by
            gcongr; rw [div_le_iff₀ (by positivity)]; linarith
        _ = V / 2 := by ring
    have h_exp_err : (Real.log Q / (2 * Real.pi)) * (C_err_M * Real.exp (-2 * Real.pi * Δ)) ≤ C_err_M * Real.log (Real.log q) := by
      have h_2piΔ : Real.log (Real.log q) ≤ 2 * Real.pi * Δ := by
        have h_1 : 1 ≤ Real.pi * K_scale := by nlinarith [Real.two_le_pi, show 1 ≤ K_scale by exact le_max_left _ _]
        have h_v : V * Real.log (Real.log q) ≤ Real.log q := by rwa [le_div_iff₀ hLLq_pos] at hV_ub
        calc Real.log (Real.log q) ≤ Real.pi * K_scale * Real.log (Real.log q) := le_mul_of_one_le_left hLLq_pos.le h_1
          _ ≤ 2 * Real.pi * (K_scale * Real.log Q / V) := by
              rw [le_div_iff₀ hV_pos]
              calc Real.pi * K_scale * Real.log (Real.log q) * V = Real.pi * K_scale * (V * Real.log (Real.log q)) := by ring
                _ ≤ Real.pi * K_scale * Real.log q := by gcongr
                _ ≤ 2 * Real.pi * K_scale * Real.log Q := by
                    nlinarith [hlog_ac_ge, Real.pi_pos]
      have h_exp_lt : Real.exp (-2 * Real.pi * Δ) ≤ 1 / Real.log q := by
        rw [Real.exp_neg, inv_eq_one_div]
        exact div_le_div_of_nonneg_left zero_le_one hlogq_pos (by
          calc Real.log q = Real.exp (Real.log (Real.log q)) := (Real.exp_log hlogq_pos).symm
            _ ≤ Real.exp (2 * Real.pi * Δ) := Real.exp_le_exp.mpr h_2piΔ)
      calc (Real.log Q / (2 * Real.pi)) * (C_err_M * Real.exp (-2 * Real.pi * Δ))
          ≤ (2 * Real.log q / (2 * Real.pi)) * (C_err_M * (1 / Real.log q)) := by gcongr
        _ = C_err_M / Real.pi := by field_simp [hlogq_pos.ne', Real.pi_ne_zero]; ring
        _ ≤ C_err_M * Real.log (Real.log q) := by
            have : 1 / Real.pi ≤ Real.log (Real.log q) := by
              have : 1 / Real.pi ≤ 1 := div_le_one_of_le₀ (by linarith [Real.two_le_pi]) Real.pi_pos.le
              linarith
            nlinarith [hC_err_M]
    have h_gw_err : C₁ * (C_sup * Real.log Δ +
        (if q = 1 then Real.exp (Real.pi * Δ) / t₀ ^ 2 * (C_sup * Real.log Δ) else 0)) ≤
        2 * C₁ * C_sup * Real.log (Real.log q) := by
      have hΔ_le_q : Δ ≤ Real.log q := by
        dsimp only [Δ]
        calc K_scale * Real.log (analyticConductor q t₀) / V ≤ K_scale * (2 * Real.log q) / V := by gcongr
          _ = (2 * K_scale / V) * Real.log q := by ring
          _ ≤ 1 * Real.log q := by
              gcongr
              rw [div_le_one hV_pos]
              have h_l : 16 * Real.pi * K_scale ≤ Real.log (Real.log q) :=
                le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLLq_ge
              have h_a : 2 ≤ A := le_max_left _ _
              nlinarith [Real.two_le_pi]
          _ = Real.log q := one_mul _
      have h_logΔ : Real.log Δ ≤ Real.log (Real.log q) := Real.log_le_log hΔ_pos hΔ_le_q
      rw [if_neg (by omega : q ≠ 1), add_zero]
      nlinarith
    have h_tail_t := h_tail_bd χ h_hat Δ (majorantM θ Δ α) hΔ_ge_Δ₀ hM_int hM_L1_diff hM_L1_tot t₀
    have h_loglogX : Real.log (Real.log X) ≤ Real.log (Real.log q) :=
      Real.log_le_log hlogX_pos (by linarith [hlogX_le_half])
    have h_P_split : primePowerSum q χ h_hat X t₀ =
        primeSum1 q χ h_hat X t₀ + primeSum2 q χ h_hat X t₀ + primeSumGe3 q χ h_hat X t₀ := by
      unfold primeSumGe3; ring
    have h_p23 : |primeSum2 q χ h_hat X t₀ + primeSumGe3 q χ h_hat X t₀| ≤ 2 * C_tail * Real.log (Real.log q) := by
      have h1 : |primeSum2 q χ h_hat X t₀| ≤ C_tail * Real.log (Real.log q) :=
        h_tail_t.1.trans (mul_le_mul_of_nonneg_left h_loglogX hC_tail.le)
      have h2 : |primeSumGe3 q χ h_hat X t₀| ≤ C_tail * Real.log (Real.log q) :=
        h_tail_t.2.trans (le_mul_of_one_le_right hC_tail.le (by linarith))
      linarith [abs_add_le (primeSum2 q χ h_hat X t₀) (primeSumGe3 q χ h_hat X t₀)]
    have h_C₀_le : C₀ ≤ C₀ * Real.log (Real.log q) := le_mul_of_one_le_right hC₀.le (by linarith)
    have h_tot_err : 2 * C_tail * Real.log (Real.log q) + C₀ + 2 * C₁ * C_sup * Real.log (Real.log q) +
        C_err_M * Real.log (Real.log q) ≤ V / 4 := by
      have h_a : (8 * C_tail + 8 * C₀ + 8 * C₁ * C_sup + 8 * C_err_M + 8) ≤ A :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
      nlinarith
    have h_pol_le : V ≤ V / 2 - primeSum1 q χ h_hat X t₀ + V / 4 := by
      have h_g := (abs_le.mp h_gw_bd).2
      have h_h := (abs_le.mp h_hzs_bd).2
      have h_p := (abs_le.mp h_p23).1
      linarith
    have h_neg : -primeSum1 q χ h_hat X t₀ ≥ V / 4 := by linarith
    exact le_trans h_neg (neg_le_abs _)
  have h_card_le : (S_target.card : ℝ) ≤ (S_large.card : ℝ) := by
    exact_mod_cast Finset.card_le_card h_subset
  let S_prim := Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)
  have h_markov : (V / 4) ^ (2 * k) * (S_large.card : ℝ) ≤
      ∑ χ ∈ S_prim, |primeSum1 q χ h_hat X t₀| ^ (2 * k) := by
    have h_sub_prim : S_large ⊆ S_prim := by
      intro χ hχ; rw [Finset.mem_filter] at hχ ⊢; exact ⟨Finset.mem_univ _, hχ.2.1⟩
    calc (V / 4) ^ (2 * k) * (S_large.card : ℝ)
        = ∑ _χ ∈ S_large, (V / 4) ^ (2 * k) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ χ ∈ S_large, |primeSum1 q χ h_hat X t₀| ^ (2 * k) := by
          refine Finset.sum_le_sum fun χ hχ => ?_
          rw [Finset.mem_filter] at hχ
          exact pow_le_pow_left₀ (by positivity) hχ.2.2 (2 * k)
      _ ≤ ∑ χ ∈ S_prim, |primeSum1 q χ h_hat X t₀| ^ (2 * k) :=
          Finset.sum_le_sum_of_subset_of_nonneg h_sub_prim (fun _ _ _ => by positivity)
  have h_mom_bd := h_mom q t₀ Δ k (majorantM θ Δ α) hq_ge_3 hqstar hΔ_ge_Δ₀ hXk_lt_q hM_int hM_L1_diff hM_L1_tot
  have h_tot_star : (Nat.totient q : ℝ) / (totientStar q : ℝ) ≤ (2 * Real.exp 61) ^ k := by
    have h_t1 := totient_div_totientStar_le q hq_ge_3 hqstar
    have h_30_le_k : 30 * Real.log (Real.log q) ≤ (k : ℝ) := by
      have h_a : 320 * (2 * Real.pi * K_scale) + 1 ≤ A :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      have h_k1 : (3 : ℝ) * (320 * (2 * Real.pi * K_scale)) * Real.log (Real.log q) / (16 * (2 * Real.pi * K_scale)) ≤ (k : ℝ) := by
        calc (3 : ℝ) * (320 * (2 * Real.pi * K_scale)) * Real.log (Real.log q) / (16 * (2 * Real.pi * K_scale))
            ≤ (3 : ℝ) * (A * Real.log (Real.log q)) / (16 * (2 * Real.pi * K_scale)) := by gcongr; linarith
          _ ≤ (3 : ℝ) * V / (16 * (2 * Real.pi * K_scale)) := by gcongr
          _ ≤ (k : ℝ) := hk_lb
      have h_eq : (3 : ℝ) * (320 * (2 * Real.pi * K_scale)) * Real.log (Real.log q) / (16 * (2 * Real.pi * K_scale)) =
          60 * Real.log (Real.log q) := by
        field_simp [hK_scale_pos.ne', Real.pi_ne_zero]; ring
      linarith
    have h_logq_pow : (Real.log q) ^ 30 ≤ Real.exp k := by
      calc (Real.log q) ^ 30 = Real.exp ((30 : ℕ) * Real.log (Real.log q)) := by
            rw [← Real.log_pow, Real.exp_log (pow_pos hlogq_pos 30)]
        _ ≤ Real.exp (k : ℝ) := by push_cast; exact Real.exp_le_exp.mpr h_30_le_k
    have h_c_pow : 2 * Real.exp 60 ≤ (2 * Real.exp 60) ^ k :=
      le_self_pow₀ (by have : 1 ≤ Real.exp 60 := Real.one_le_exp (by norm_num); linarith) hk_pos.ne'
    have h_exp_k : Real.exp (k : ℝ) = (Real.exp 1) ^ k := by
      rw [← Real.exp_nat_mul, mul_one]
    calc (Nat.totient q : ℝ) / (totientStar q : ℝ)
        ≤ 2 * Real.exp 60 * (Real.log q) ^ 30 := h_t1
      _ ≤ (2 * Real.exp 60) ^ k * (Real.exp 1) ^ k := by gcongr; rwa [← h_exp_k]
      _ = (2 * Real.exp 60 * Real.exp 1) ^ k := (mul_pow _ _ _).symm
      _ = (2 * Real.exp 61) ^ k := by
          congr 1; rw [mul_assoc, ← Real.exp_add]; norm_num
  have h_loglogX : Real.log (Real.log X) ≤ Real.log (Real.log q) :=
    Real.log_le_log hlogX_pos (by linarith [hlogX_le_half])
  have h_base : (4 / V) ^ 2 * (2 * Real.exp 61 * B * k * Real.log (Real.log X)) ≤
      C_B * Real.log (Real.log q) / V := by
    calc (4 / V) ^ 2 * (2 * Real.exp 61 * B * k * Real.log (Real.log X))
        ≤ (16 / V ^ 2) * (2 * Real.exp 61 * B * (V / (2 * Real.pi * K_scale)) * Real.log (Real.log q)) := by
          gcongr; ring_nf; rfl
      _ = (16 * Real.exp 61 * B / (Real.pi * K_scale)) * Real.log (Real.log q) / V := by
          field_simp [hV_pos.ne', Real.pi_ne_zero, hK_scale_pos.ne']; ring
      _ ≤ C_B * Real.log (Real.log q) / V := by
          gcongr
          dsimp only [C_B]
          have : 1 ≤ 2 * Real.pi * K_scale := by nlinarith [Real.two_le_pi, show 1 ≤ K_scale by exact le_max_left _ _]
          have : 0 ≤ 16 * Real.exp 61 * B := by positivity
          nlinarith [Real.two_le_pi]
  have h_div_v : (1 / (totientStar q : ℝ)) * (S_target.card : ℝ) ≤
      (C_B * Real.log (Real.log q) / V) ^ k := by
    have h_pow_pos : 0 < (V / 4) ^ (2 * k) := pow_pos (by positivity) (2 * k)
    have hqstar_pos : (0 : ℝ) < totientStar q := by exact_mod_cast hqstar
    have h1 : (1 / (totientStar q : ℝ)) * (S_large.card : ℝ) ≤
        ((4 / V) ^ 2 * (2 * Real.exp 61 * B * k * Real.log (Real.log X))) ^ k := by
      calc (1 / (totientStar q : ℝ)) * (S_large.card : ℝ)
          ≤ (1 / (totientStar q : ℝ)) * ((∑ χ ∈ S_prim, |primeSum1 q χ h_hat X t₀| ^ (2 * k)) / (V / 4) ^ (2 * k)) := by
            gcongr; rwa [le_div_iff₀ h_pow_pos, mul_comm]
        _ = (1 / (V / 4) ^ (2 * k)) * ((1 / (totientStar q : ℝ)) * ∑ χ ∈ S_prim, |primeSum1 q χ h_hat X t₀| ^ (2 * k)) := by
            ring
        _ ≤ (1 / (V / 4) ^ (2 * k)) * (((Nat.totient q : ℝ) / (totientStar q : ℝ)) * (B * k * Real.log (Real.log X)) ^ k) := by
            gcongr; exact h_mom_bd
        _ ≤ (1 / (V / 4) ^ (2 * k)) * ((2 * Real.exp 61) ^ k * (B * k * Real.log (Real.log X)) ^ k) := by
            gcongr
        _ = ((4 / V) ^ 2 * (2 * Real.exp 61 * B * k * Real.log (Real.log X))) ^ k := by
            rw [mul_pow, mul_pow, ← pow_mul, mul_comm 2 k, one_div_pow, div_pow, one_div_div]; ring
    exact (mul_le_mul_of_nonneg_left h_card_le (by positivity)).trans (h1.trans (pow_le_pow_left₀ (by positivity) h_base k))
  have h_ratio_le : C_B * Real.log (Real.log q) / V ≤ (Real.log (Real.log q) / V) ^ (1 / 2 : ℝ) := by
    have h_a : C_B ^ 2 ≤ A :=
      le_trans (by linarith) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
    have h_cb_le : C_B ^ 2 * Real.log (Real.log q) ≤ V := by
      calc C_B ^ 2 * Real.log (Real.log q) ≤ A * Real.log (Real.log q) := by gcongr
        _ ≤ V := hV_lb
    have h_sq : (C_B * Real.log (Real.log q) / V) ^ 2 ≤ Real.log (Real.log q) / V := by
      rw [div_pow, div_le_div_iff₀ (sq_pos_of_pos hV_pos) hV_pos]
      nlinarith [h_cb_le, hLLq_pos]
    calc C_B * Real.log (Real.log q) / V = Real.sqrt ((C_B * Real.log (Real.log q) / V) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (Real.log (Real.log q) / V) := Real.sqrt_le_sqrt h_sq
      _ = (Real.log (Real.log q) / V) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have h_log_ratio : (1 / 2 : ℝ) * Real.log (V / Real.log (Real.log q)) ≤ -Real.log (C_B * Real.log (Real.log q) / V) := by
    have h1 : Real.log (C_B * Real.log (Real.log q) / V) ≤ (1 / 2 : ℝ) * Real.log (Real.log (Real.log q) / V) := by
      calc Real.log (C_B * Real.log (Real.log q) / V)
          ≤ Real.log ((Real.log (Real.log q) / V) ^ (1 / 2 : ℝ)) := Real.log_le_log (by positivity) h_ratio_le
        _ = (1 / 2 : ℝ) * Real.log (Real.log (Real.log q) / V) := Real.log_rpow (by positivity) _
    have h2 : Real.log (Real.log (Real.log q) / V) = -Real.log (V / Real.log (Real.log q)) := by
      rw [← Real.log_inv, inv_div]
    linarith
  have h_exp_final : (C_B * Real.log (Real.log q) / V) ^ k ≤
      Real.exp (-c * V * Real.log (V / Real.log (Real.log q))) := by
    rw [← Real.exp_log (pow_pos (by positivity) k), Real.log_pow]
    apply Real.exp_le_exp.mpr
    have h_v_log : 0 ≤ Real.log (V / Real.log (Real.log q)) := by
      apply Real.log_nonneg; rw [one_le_div hLLq_pos]; have : 1 ≤ A := by linarith; nlinarith
    calc (k : ℝ) * Real.log (C_B * Real.log (Real.log q) / V)
        ≤ (k : ℝ) * (-(1 / 2 : ℝ) * Real.log (V / Real.log (Real.log q))) := by gcongr; linarith
      _ = -(1 / 2 : ℝ) * (k : ℝ) * Real.log (V / Real.log (Real.log q)) := by ring
      _ ≤ -(1 / 2 : ℝ) * ((3 : ℝ) * V / (16 * (2 * Real.pi * K_scale))) * Real.log (V / Real.log (Real.log q)) := by
          gcongr
      _ ≤ -c * V * Real.log (V / Real.log (Real.log q)) := by
          dsimp only [c]; ring_nf; linarith [mul_nonneg hV_pos.le h_v_log]
  exact h_div_v.trans h_exp_final

/-- **Theorem 1.5** (`q`-aspect large-deviation bound). -/
theorem q_aspect_large_deviation (D : LFunctionData) (t₀ θ : ℝ) (hθ : |θ| < Real.pi / 2) :
    ∃ (c c' A : ℝ), c > 0 ∧ c' > 0 ∧ A > 1 ∧
      (∃ q₀ : ℕ, q₀ ≥ 3 ∧
        ∀ (q : ℕ) (hq1 : q ≥ 1), q ≥ q₀ → totientStar q ≥ 1 →
          (∀ (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive), D.GRH q hq1 χ hχ) →
          ∀ V : ℝ, A * Real.log (Real.log q) ≤ V → V ≤ Real.log q / Real.log (Real.log q) →
          (1 / (totientStar q : ℝ)) *
            ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
              χ.IsPrimitive ∧ D.nonvanishing q χ t₀ ∧ polarLogL D q χ t₀ θ ≥ V)).card : ℝ) ≤
            Real.exp (-c * V * Real.log (V / Real.log (Real.log q)))) ∧
      (∀ α : ℝ, α > 0 → ∃ q₀ : ℕ, q₀ ≥ 3 ∧
        ∀ (q : ℕ) (hq1 : q ≥ 1), q ≥ q₀ → totientStar q ≥ 1 →
          (∀ (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive), D.GRH q hq1 χ hχ) →
          let V := α * Real.sqrt (Real.log q * Real.log (Real.log q))
          V ≤ Real.log q / Real.log (Real.log q) →
          (1 / (totientStar q : ℝ)) *
            ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
              χ.IsPrimitive ∧ D.nonvanishing q χ t₀ ∧ polarLogL D q χ t₀ θ ≥ V)).card : ℝ) ≤
            Real.exp (-c' * α * Real.sqrt (Real.log q) * (Real.log (Real.log q)) ^ (3 / 2 : ℝ))) := by
  obtain ⟨c, A, hc, hA, q₀₁, hq₀₁, h_part1⟩ := q_aspect_polar_ld_core D t₀ θ hθ
  refine ⟨c, c / 4, A, hc, by positivity, hA, ⟨q₀₁, hq₀₁, h_part1⟩, fun α hα => ?_⟩
  let L_α : ℝ := max 100 (max ((A / α) ^ 2) ((Real.exp 1 / α) ^ 4))
  let q₀ : ℕ := max q₀₁ (Nat.ceil (Real.exp (Real.exp L_α)) + 3)
  refine ⟨q₀, le_trans hq₀₁ (le_max_left _ _), fun q hq1 hq_ge hqstar hGRH_all V hV_ub => ?_⟩
  have hq_ge_q₀₁ : q ≥ q₀₁ := le_trans (le_max_left _ _) hq_ge
  have hq_ge_exp : Real.exp (Real.exp L_α) ≤ (q : ℝ) := by
    have h1 : Nat.ceil (Real.exp (Real.exp L_α)) + 3 ≤ q := le_trans (le_max_right _ _) hq_ge
    have h2 : Real.exp (Real.exp L_α) ≤ (Nat.ceil (Real.exp (Real.exp L_α)) : ℝ) := Nat.le_ceil _
    have h3 : (Nat.ceil (Real.exp (Real.exp L_α)) : ℝ) ≤ q := by
      exact_mod_cast (by omega : Nat.ceil (Real.exp (Real.exp L_α)) ≤ q)
    linarith
  have hlogq_ge_exp : Real.exp L_α ≤ Real.log q := by
    rw [← Real.log_exp (Real.exp L_α)]; exact Real.log_le_log (Real.exp_pos _) hq_ge_exp
  have hLLq_ge : L_α ≤ Real.log (Real.log q) := by
    rw [← Real.log_exp L_α]; exact Real.log_le_log (Real.exp_pos _) hlogq_ge_exp
  have hLLq_pos : 0 < Real.log (Real.log q) := by linarith [le_max_left (100 : ℝ) (max ((A / α) ^ 2) ((Real.exp 1 / α) ^ 4))]
  have hlogq_pos : 0 < Real.log q := by linarith [Real.exp_pos L_α]
  have h_ratio_le : (Real.log q / Real.log (Real.log q)) ≥ (Real.log (Real.log q)) ^ 2 := by
    have he4 := Real.pow_div_factorial_le_exp (Real.log (Real.log q)) hLLq_pos.le 4
    have h3 : (Real.log (Real.log q)) ^ 4 / 24 ≤ Real.log q := by
      calc (Real.log (Real.log q)) ^ 4 / 24 = (Real.log (Real.log q)) ^ 4 / Nat.factorial 4 := by norm_num
        _ ≤ Real.exp (Real.log (Real.log q)) := he4
        _ = Real.log q := Real.exp_log hlogq_pos
    have h_llq : 24 ≤ Real.log (Real.log q) := by linarith [le_max_left (100 : ℝ) (max ((A / α) ^ 2) ((Real.exp 1 / α) ^ 4))]
    rw [ge_iff_le, le_div_iff₀ hLLq_pos]; nlinarith [pow_nonneg hLLq_pos.le 3]
  have hV_lb : A * Real.log (Real.log q) ≤ V := by
    have h1 : (A / α) ^ 2 ≤ Real.log (Real.log q) :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hLLq_ge)
    have h2 : A / α ≤ Real.sqrt (Real.log (Real.log q)) := by
      calc A / α = Real.sqrt ((A / α) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (Real.log (Real.log q)) := Real.sqrt_le_sqrt h1
    have h3 : Real.log (Real.log q) ≤ Real.sqrt (Real.log q / Real.log (Real.log q)) := by
      rw [← Real.sqrt_sq hLLq_pos.le]; exact Real.sqrt_le_sqrt h_ratio_le
    have h4 : A / α ≤ Real.sqrt (Real.log q / Real.log (Real.log q)) := by
      have : 1 ≤ Real.log (Real.log q) := by linarith [le_max_left (100 : ℝ) (max ((A / α) ^ 2) ((Real.exp 1 / α) ^ 4))]
      calc A / α ≤ Real.sqrt (Real.log (Real.log q)) := h2
        _ ≤ Real.log (Real.log q) := by rw [← Real.sqrt_sq hLLq_pos.le]; exact Real.sqrt_le_sqrt (by nlinarith)
        _ ≤ Real.sqrt (Real.log q / Real.log (Real.log q)) := h3
    have h5 : V / Real.log (Real.log q) = α * Real.sqrt (Real.log q / Real.log (Real.log q)) := by
      dsimp only [V]; rw [Real.sqrt_mul hlogq_pos.le, Real.sqrt_div hlogq_pos.le]; field_simp [hLLq_pos.ne']
      rw [← Real.sq_sqrt hLLq_pos.le]; ring
    rw [← div_le_iff₀ hLLq_pos, h5, ← div_le_iff₀' hα]; exact h4
  have h_p1 := h_part1 q hq1 hq_ge_q₀₁ hqstar hGRH_all V hV_lb hV_ub
  have h_log_v : (1 / 4 : ℝ) * Real.log (Real.log q) ≤ Real.log (V / Real.log (Real.log q)) := by
    have h_v_eq : V / Real.log (Real.log q) = α * Real.sqrt (Real.log q / Real.log (Real.log q)) := by
      dsimp only [V]; rw [Real.sqrt_mul hlogq_pos.le, Real.sqrt_div hlogq_pos.le]; field_simp [hLLq_pos.ne']
      rw [← Real.sq_sqrt hLLq_pos.le]; ring
    have h_ge_exp : (Real.log (Real.log q)) ^ (1 / 4 : ℝ) ≤ α * Real.sqrt (Real.log q / Real.log (Real.log q)) := by
      have h1 : (Real.exp 1 / α) ^ 4 ≤ Real.log (Real.log q) :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hLLq_ge)
      have h2 : Real.exp 1 / α ≤ (Real.log (Real.log q)) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast (Real.exp 1 / α) 4] at h1
        have := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
        rwa [← Real.rpow_mul (by positivity), show (4 : ℕ) * (1 / 4 : ℝ) = 1 by norm_num, Real.rpow_one] at this
      have h3 : (Real.log (Real.log q)) ^ (1 / 2 : ℝ) ≤ Real.sqrt (Real.log q / Real.log (Real.log q)) := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.sqrt_le_sqrt (by have : 1 ≤ Real.log (Real.log q) := by linarith [le_max_left (100 : ℝ) (max ((A / α) ^ 2) ((Real.exp 1 / α) ^ 4))]; nlinarith [h_ratio_le])
      have h4 : (Real.log (Real.log q)) ^ (1 / 4 : ℝ) * (Real.log (Real.log q)) ^ (1 / 4 : ℝ) =
          (Real.log (Real.log q)) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hLLq_pos]; norm_num
      have h5 : 1 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      calc (Real.log (Real.log q)) ^ (1 / 4 : ℝ) = 1 * (Real.log (Real.log q)) ^ (1 / 4 : ℝ) := (one_mul _).symm
        _ ≤ Real.exp 1 * (Real.log (Real.log q)) ^ (1 / 4 : ℝ) := by gcongr
        _ = α * ((Real.exp 1 / α) * (Real.log (Real.log q)) ^ (1 / 4 : ℝ)) := by field_simp [hα.ne']
        _ ≤ α * ((Real.log (Real.log q)) ^ (1 / 4 : ℝ) * (Real.log (Real.log q)) ^ (1 / 4 : ℝ)) := by gcongr
        _ = α * (Real.log (Real.log q)) ^ (1 / 2 : ℝ) := by rw [h4]
        _ ≤ α * Real.sqrt (Real.log q / Real.log (Real.log q)) := by gcongr
    rw [h_v_eq]
    calc (1 / 4 : ℝ) * Real.log (Real.log q) = Real.log ((Real.log (Real.log q)) ^ (1 / 4 : ℝ)) :=
          (Real.log_rpow hLLq_pos _).symm
      _ ≤ Real.log (α * Real.sqrt (Real.log q / Real.log (Real.log q))) := Real.log_le_log (by positivity) h_ge_exp
  have h_exp_le : Real.exp (-c * V * Real.log (V / Real.log (Real.log q))) ≤
      Real.exp (-(c / 4) * α * Real.sqrt (Real.log q) * (Real.log (Real.log q)) ^ (3 / 2 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have h_v_eq : V * Real.log (Real.log q) = α * Real.sqrt (Real.log q) * (Real.log (Real.log q)) ^ (3 / 2 : ℝ) := by
      dsimp only [V]; rw [Real.sqrt_mul hlogq_pos.le, Real.sqrt_eq_rpow (Real.log (Real.log q))]
      have h_32 : (Real.log (Real.log q)) ^ (1 / 2 : ℝ) * Real.log (Real.log q) = (Real.log (Real.log q)) ^ (3 / 2 : ℝ) := by
        conv_lhs => rhs; rw [← Real.rpow_one (Real.log (Real.log q))]
        rw [← Real.rpow_add hLLq_pos]; norm_num
      nlinarith [h_32]
    nlinarith [mul_nonneg hc.le (show 0 ≤ V by dsimp only [V]; positivity)]
  exact h_p1.trans h_exp_le

/-- **Corollary 1.6(ii)** (`q`-aspect large-deviation bound for `|S(t₀, χ)|`). -/
theorem S_large_deviation_q (D : LFunctionData) (t₀ : ℝ) :
    ∀ α > 0, ∃ (c : ℝ) (q₀ : ℕ), c > 0 ∧ q₀ ≥ 3 ∧
      ∀ (q : ℕ) (hq1 : q ≥ 1), q ≥ q₀ → totientStar q ≥ 1 →
        (∀ (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive), D.GRH q hq1 χ hχ) →
        let V := α * Real.sqrt (Real.log q * Real.log (Real.log q))
        V ≤ Real.log q / Real.log (Real.log q) →
        (1 / (totientStar q : ℝ)) *
          ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
            χ.IsPrimitive ∧ D.nonvanishing q χ t₀ ∧ |D.S_val q χ t₀| ≥ V)).card : ℝ) ≤
          Real.exp (-c * α * Real.sqrt (Real.log q) * (Real.log (Real.log q)) ^ (3 / 2 : ℝ)) := by
  intro α hα
  obtain ⟨C₀, hC₀, h_hzs_S⟩ := S_val_horizontal_zero_sum D
  obtain ⟨C₁, hC₁, h_gw⟩ := guinand_weil_external D
  obtain ⟨Δ₀, C₃, hΔ₀, hC₃, h_ccm⟩ := ccm_odd_extremal
  let C_L1_tot : ℝ := max (C₃ * Real.pi) (Real.pi / 2 + C₃ + 1)
  obtain ⟨C_tail, hC_tail, h_tail⟩ := prime_power_tail_bounds (Real.pi / 2) C_L1_tot Δ₀ (by simp [abs_of_pos Real.pi_pos]) hΔ₀
  obtain ⟨B, hB, h_mom⟩ := prime_moment_q_aspect (Real.pi / 2) C_L1_tot Δ₀ (by simp [abs_of_pos Real.pi_pos]) hΔ₀
  let K_scale : ℝ := 2
  let C_B : ℝ := 32 * Real.exp 61 * B * (2 * Real.pi * K_scale)
  let A : ℝ := max 2 (max (320 * (2 * Real.pi * K_scale) + 1)
    (max (Real.exp 1 * C_B + 1) (max (C_B ^ 2 + 1) (8 * C_tail + 8 * C₀ + 8 * C₁ * C₃ + 8 * C₃ + 8))))
  let L_α : ℝ := max 100 (max (Real.pi * Δ₀ / K_scale + 1) (max (16 * Real.pi * K_scale) (max ((A / α) ^ 2) ((Real.exp 1 / α) ^ 4))))
  let q₀ : ℕ := max (Nat.ceil (|t₀| + 2) + 3) (Nat.ceil (Real.exp (Real.exp L_α)) + 3)
  let c : ℝ := 3 / (64 * (2 * Real.pi * K_scale) * 4)
  refine ⟨c, q₀, by positivity, le_trans (by omega) (le_max_left _ _), fun q hq1 hq_ge hqstar hGRH_all V hV_ub => ?_⟩
  have hq_ge_3 : q ≥ 3 := by omega
  have hq_pos : (0 : ℝ) < q := by positivity
  have hq_ge_exp : Real.exp (Real.exp L_α) ≤ (q : ℝ) := by
    have h1 : Nat.ceil (Real.exp (Real.exp L_α)) + 3 ≤ q := le_trans (le_max_right _ _) hq_ge
    have h2 : Real.exp (Real.exp L_α) ≤ (Nat.ceil (Real.exp (Real.exp L_α)) : ℝ) := Nat.le_ceil _
    have h3 : (Nat.ceil (Real.exp (Real.exp L_α)) : ℝ) ≤ q := by
      exact_mod_cast (by omega : Nat.ceil (Real.exp (Real.exp L_α)) ≤ q)
    linarith
  have hlogq_ge_exp : Real.exp L_α ≤ Real.log q := by
    rw [← Real.log_exp (Real.exp L_α)]; exact Real.log_le_log (Real.exp_pos _) hq_ge_exp
  have hLLq_ge : L_α ≤ Real.log (Real.log q) := by
    rw [← Real.log_exp L_α]; exact Real.log_le_log (Real.exp_pos _) hlogq_ge_exp
  have hLLq_pos : 0 < Real.log (Real.log q) := by
    linarith [le_max_left (100 : ℝ) (max (Real.pi * Δ₀ / K_scale + 1) (max (16 * Real.pi * K_scale) (max ((A / α) ^ 2) ((Real.exp 1 / α) ^ 4))))]
  have hlogq_pos : 0 < Real.log q := by linarith [Real.exp_pos L_α]
  have ht0_le_q : |t₀| + 2 ≤ (q : ℝ) := by
    have h1 : Nat.ceil (|t₀| + 2) + 3 ≤ q := le_trans (le_max_left _ _) hq_ge
    have h2 : |t₀| + 2 ≤ (Nat.ceil (|t₀| + 2) : ℝ) := Nat.le_ceil _
    have h3 : (Nat.ceil (|t₀| + 2) : ℝ) ≤ q := by exact_mod_cast (by omega : Nat.ceil (|t₀| + 2) ≤ q)
    linarith
  have hac_le_q2 : analyticConductor q t₀ ≤ (q : ℝ) ^ 2 := by unfold analyticConductor; nlinarith
  have hac_ge_q : (q : ℝ) ≤ analyticConductor q t₀ := by
    unfold analyticConductor; have : 2 ≤ |t₀| + 2 := by linarith [abs_nonneg t₀]; nlinarith
  have hlog_ac_le : Real.log (analyticConductor q t₀) ≤ 2 * Real.log q := by
    have h1 : Real.log (analyticConductor q t₀) ≤ Real.log ((q : ℝ) ^ 2) :=
      Real.log_le_log (by unfold analyticConductor; positivity) hac_le_q2
    rwa [Real.log_pow] at h1
  have hlog_ac_ge : Real.log q ≤ Real.log (analyticConductor q t₀) := Real.log_le_log hq_pos hac_ge_q
  have h_ratio_ge : (Real.log q / Real.log (Real.log q)) ≥ (Real.log (Real.log q)) ^ 2 := by
    have he4 := Real.pow_div_factorial_le_exp (Real.log (Real.log q)) hLLq_pos.le 4
    have h3 : (Real.log (Real.log q)) ^ 4 / 24 ≤ Real.log q := by
      calc (Real.log (Real.log q)) ^ 4 / 24 = (Real.log (Real.log q)) ^ 4 / Nat.factorial 4 := by norm_num
        _ ≤ Real.exp (Real.log (Real.log q)) := he4
        _ = Real.log q := Real.exp_log hlogq_pos
    have h_llq : 24 ≤ Real.log (Real.log q) := by
      linarith [le_max_left (100 : ℝ) (max (Real.pi * Δ₀ / K_scale + 1) (max (16 * Real.pi * K_scale) (max ((A / α) ^ 2) ((Real.exp 1 / α) ^ 4))))]
    rw [ge_iff_le, le_div_iff₀ hLLq_pos]; nlinarith [pow_nonneg hLLq_pos.le 3]
  have hV_lb : A * Real.log (Real.log q) ≤ V := by
    have h1 : (A / α) ^ 2 ≤ Real.log (Real.log q) :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hLLq_ge)))
    have h2 : A / α ≤ Real.sqrt (Real.log (Real.log q)) := by
      calc A / α = Real.sqrt ((A / α) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (Real.log (Real.log q)) := Real.sqrt_le_sqrt h1
    have h3 : Real.log (Real.log q) ≤ Real.sqrt (Real.log q / Real.log (Real.log q)) := by
      rw [← Real.sqrt_sq hLLq_pos.le]; exact Real.sqrt_le_sqrt h_ratio_ge
    have h4 : A / α ≤ Real.sqrt (Real.log q / Real.log (Real.log q)) := by
      have : 1 ≤ Real.log (Real.log q) := by linarith
      calc A / α ≤ Real.sqrt (Real.log (Real.log q)) := h2
        _ ≤ Real.log (Real.log q) := by rw [← Real.sqrt_sq hLLq_pos.le]; exact Real.sqrt_le_sqrt (by nlinarith)
        _ ≤ Real.sqrt (Real.log q / Real.log (Real.log q)) := h3
    have h5 : V / Real.log (Real.log q) = α * Real.sqrt (Real.log q / Real.log (Real.log q)) := by
      dsimp only [V]; rw [Real.sqrt_mul hlogq_pos.le, Real.sqrt_div hlogq_pos.le]; field_simp [hLLq_pos.ne']
      rw [← Real.sq_sqrt hLLq_pos.le]; ring
    rw [← div_le_iff₀ hLLq_pos, h5, ← div_le_iff₀' hα]; exact h4
  have hV_pos : 0 < V := by
    have : 0 < A := by
      linarith [le_max_left (2 : ℝ) (max (320 * (2 * Real.pi * K_scale) + 1)
        (max (Real.exp 1 * C_B + 1) (max (C_B ^ 2 + 1) (8 * C_tail + 8 * C₀ + 8 * C₁ * C₃ + 8 * C₃ + 8))))]
    nlinarith
  let Δ : ℝ := K_scale * Real.log (analyticConductor q t₀) / V
  have hΔ_ge_Δ₀ : Δ₀ ≤ Δ := by
    have h1 : K_scale * Real.log (Real.log q) ≤ Δ := by
      dsimp only [Δ]; rw [le_div_iff₀ hV_pos]
      have h_v : V * Real.log (Real.log q) ≤ Real.log q := by rwa [le_div_iff₀ hLLq_pos] at hV_ub
      calc K_scale * Real.log (Real.log q) * V = K_scale * (V * Real.log (Real.log q)) := by ring
        _ ≤ K_scale * Real.log q := by gcongr
        _ ≤ K_scale * Real.log (analyticConductor q t₀) := by gcongr
    have h2 : Δ₀ ≤ K_scale * Real.log (Real.log q) := by
      have h_l : Real.pi * Δ₀ / K_scale + 1 ≤ Real.log (Real.log q) :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hLLq_ge)
      rw [div_add_one (by positivity), div_le_iff₀ (by positivity)] at h_l
      nlinarith [Real.two_le_pi]
    exact h2.trans h1
  have hΔ_ge_1 : 1 ≤ Δ := le_trans hΔ₀ hΔ_ge_Δ₀
  have hΔ_pos : 0 < Δ := by linarith
  let X : ℝ := Real.exp (2 * Real.pi * Δ)
  have hlogX_eq : Real.log X = 2 * Real.pi * Δ := Real.log_exp _
  have hlogX_le_half : Real.log X ≤ Real.log q / 2 := by
    rw [hlogX_eq]
    have h_l : 16 * Real.pi * K_scale ≤ Real.log (Real.log q) :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hLLq_ge))
    have h_a : 2 ≤ A := le_max_left _ _
    have h_v2 : 16 * Real.pi * K_scale ≤ V := by nlinarith
    calc 2 * Real.pi * Δ = 2 * Real.pi * K_scale * Real.log (analyticConductor q t₀) / V := by dsimp only [Δ]; ring
      _ ≤ 2 * Real.pi * K_scale * (2 * Real.log q) / V := by gcongr
      _ = (4 * Real.pi * K_scale / V) * Real.log q := by ring
      _ ≤ (1 / 2 : ℝ) * Real.log q := by gcongr; rw [div_le_iff₀ hV_pos]; linarith
      _ = Real.log q / 2 := by ring
  have hX_le_q : X ≤ (q : ℝ) := by
    rw [← Real.log_le_log_iff (Real.exp_pos _) hq_pos, Real.log_exp]; linarith [hlogX_le_half, hlogX_eq]
  have hlogX_pos : 0 < Real.log X := by rw [hlogX_eq]; positivity
  let k : ℕ := Nat.floor ((3 / 4 : ℝ) * (Real.log q / Real.log X))
  have hk_ge_2 : 2 ≤ k := by
    have h_l : 16 * Real.pi * K_scale ≤ Real.log (Real.log q) :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hLLq_ge))
    have h_a : 2 ≤ A := le_max_left _ _
    have h_v2 : 16 * Real.pi * K_scale ≤ V := by nlinarith
    have h_lx : Real.log X ≤ 4 * Real.pi * K_scale * Real.log q / V := by
      rw [hlogX_eq]
      calc 2 * Real.pi * Δ = 2 * Real.pi * K_scale * Real.log (analyticConductor q t₀) / V := by dsimp only [Δ]; ring
        _ ≤ 2 * Real.pi * K_scale * (2 * Real.log q) / V := by gcongr
        _ = 4 * Real.pi * K_scale * Real.log q / V := by ring
    have h_div : V / (4 * Real.pi * K_scale) ≤ Real.log q / Real.log X := by
      rw [div_le_div_iff₀ (by positivity) hlogX_pos]
      rw [le_div_iff₀ hV_pos] at h_lx; nlinarith
    have h1 : 3 ≤ (3 / 4 : ℝ) * (Real.log q / Real.log X) := by
      have : 4 ≤ V / (4 * Real.pi * K_scale) := by rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    exact Nat.le_floor (by linarith)
  have hk_pos : 0 < k := by omega
  have hXk_lt_q : X ^ k < (q : ℝ) := by
    rw [← Real.log_lt_log_iff (pow_pos (Real.exp_pos _) _) hq_pos, Real.log_pow]
    have hk_le := Nat.floor_le (by positivity : 0 ≤ (3 / 4 : ℝ) * (Real.log q / Real.log X))
    have h1 : (k : ℝ) * Real.log X ≤ (3 / 4 : ℝ) * Real.log q := by
      calc (k : ℝ) * Real.log X ≤ (3 / 4 : ℝ) * (Real.log q / Real.log X) * Real.log X := by gcongr
        _ = (3 / 4 : ℝ) * Real.log q := by field_simp [hlogX_pos.ne']
    linarith
  have hk_lb : (3 : ℝ) * V / (16 * (2 * Real.pi * K_scale)) ≤ (k : ℝ) := by
    have h_lt : (3 / 4 : ℝ) * (Real.log q / Real.log X) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have h_k2 : (1 / 2 : ℝ) * ((3 / 4 : ℝ) * (Real.log q / Real.log X)) ≤ (k : ℝ) := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk_ge_2
      linarith
    have h_lx : Real.log X ≤ 4 * Real.pi * K_scale * Real.log q / V := by
      rw [hlogX_eq]
      calc 2 * Real.pi * Δ = 2 * Real.pi * K_scale * Real.log (analyticConductor q t₀) / V := by dsimp only [Δ]; ring
        _ ≤ 2 * Real.pi * K_scale * (2 * Real.log q) / V := by gcongr
        _ = 4 * Real.pi * K_scale * Real.log q / V := by ring
    have h_div : V / (4 * Real.pi * K_scale) ≤ Real.log q / Real.log X := by
      rw [div_le_div_iff₀ (by positivity) hlogX_pos]
      rw [le_div_iff₀ hV_pos] at h_lx; nlinarith
    linarith
  have hk_ub : (k : ℝ) ≤ V / (2 * Real.pi * K_scale) := by
    have hk_le := Nat.floor_le (by positivity : 0 ≤ (3 / 4 : ℝ) * (Real.log q / Real.log X))
    have h_lx : 2 * Real.pi * K_scale * Real.log q / V ≤ Real.log X := by
      rw [hlogX_eq]; dsimp only [Δ]
      calc 2 * Real.pi * K_scale * Real.log q / V ≤ 2 * Real.pi * K_scale * Real.log (analyticConductor q t₀) / V := by gcongr
        _ = 2 * Real.pi * (K_scale * Real.log (analyticConductor q t₀) / V) := by ring
    calc (k : ℝ) ≤ (3 / 4 : ℝ) * (Real.log q / Real.log X) := hk_le
      _ ≤ Real.log q / Real.log X := by linarith [div_nonneg hlogq_pos.le hlogX_pos.le]
      _ ≤ Real.log q / (2 * Real.pi * K_scale * Real.log q / V) := div_le_div_of_nonneg_left hlogq_pos.le (by positivity) h_lx
      _ = V / (2 * Real.pi * K_scale) := by field_simp [hlogq_pos.ne', Real.pi_ne_zero]; ring
  obtain ⟨M_plus, M_minus, hMp_exp, hMm_exp, hM_im, hM_maj, hM_sup, hMp_int, hMm_int⟩ := h_ccm Δ hΔ_ge_Δ₀
  have hMp_real : Integrable (fun x : ℝ => (M_plus x).re - kernelK (Real.pi / 2) x) := by
    have h1 : Integrable (fun x : ℝ => (M_plus x).re) := by
      refine (integrable_inv_one_add_sq.const_mul C₃).mono' ?_ ?_
      · exact (Complex.continuous_re.comp hMp_exp.1.continuous.comp Complex.continuous_ofReal).aestronglyMeasurable
      · filter_upwards with x
        rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans (hM_sup x).1
    exact h1.sub (kernelK_integrable (Real.pi / 2))
  have hMm_real : Integrable (fun x : ℝ => (M_minus x).re - kernelK (Real.pi / 2) x) := by
    have h1 : Integrable (fun x : ℝ => (M_minus x).re) := by
      refine (integrable_inv_one_add_sq.const_mul C₃).mono' ?_ ?_
      · exact (Complex.continuous_re.comp hMm_exp.1.continuous.comp Complex.continuous_ofReal).aestronglyMeasurable
      · filter_upwards with x
        rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans (hM_sup x).2
    exact h1.sub (kernelK_integrable (Real.pi / 2))
  have hK_pi2_zero : ∫ x : ℝ, kernelK (Real.pi / 2) x = 0 := by
    rw [kernelK_integral_eq (Real.pi / 2), Real.cos_pi_div_two, mul_zero]
  have h_exp_le : Δ * Real.exp (-2 * Real.pi * Δ) ≤ 1 := by
    have he := Real.add_one_le_exp (2 * Real.pi * Δ)
    have h3 : Δ ≤ Real.exp (2 * Real.pi * Δ) := by nlinarith [Real.two_le_pi]
    rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]; exact h3
  have h_exp_1Δ : Real.exp (-2 * Real.pi * Δ) ≤ 1 / Δ := by rwa [le_div_iff₀ hΔ_pos, mul_comm]
  have hMp_int_re : Integrable (fun x : ℝ => (M_plus x).re) :=
    hMp_real.add (kernelK_integrable (Real.pi / 2)) |>.congr (by ext x; ring)
  have hMm_int_re : Integrable (fun x : ℝ => (M_minus x).re) :=
    hMm_real.add (kernelK_integrable (Real.pi / 2)) |>.congr (by ext x; ring)
  have hMp_L1_diff : ∫ x : ℝ, |(M_plus x).re - kernelK (Real.pi / 2) x| ≤ C_L1_tot / Δ := by
    have h_eq : ∫ x : ℝ, |(M_plus x).re - kernelK (Real.pi / 2) x| = ∫ x : ℝ, ((M_plus x).re - kernelK (Real.pi / 2) x) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_iff.mpr (by simp : volume {x : ℝ | ¬x ≠ 0} = 0)] with x hx
      exact abs_of_nonneg (sub_nonneg.mpr (hM_maj x hx).2)
    rw [h_eq, integral_sub hMp_int_re (kernelK_integrable (Real.pi / 2)), hK_pi2_zero, sub_zero]
    have h1 : ∫ x : ℝ, (M_plus x).re ≤ Real.pi / (2 * Δ) + C₃ * Real.exp (-2 * Real.pi * Δ) := by linarith [(abs_le.mp hMp_int).2]
    calc ∫ x : ℝ, (M_plus x).re ≤ Real.pi / (2 * Δ) + C₃ * (1 / Δ) := by linarith [mul_le_mul_of_nonneg_left h_exp_1Δ hC₃.le]
      _ = (Real.pi / 2 + C₃) / Δ := by ring
      _ ≤ C_L1_tot / Δ := by gcongr; exact le_trans (by linarith) (le_max_right _ _)
  have hMp_L1 : ∫ x : ℝ, |(M_plus x).re| ≤ C_L1_tot := by
    have h_mono : ∫ x : ℝ, |(M_plus x).re| ≤ ∫ x : ℝ, C₃ * (1 / (1 + x ^ 2)) := by
      refine integral_mono hMp_int_re.abs (integrable_inv_one_add_sq.const_mul C₃) fun x => ?_
      exact (Complex.abs_re_le_norm _).trans ((hM_sup x).1.trans_eq (by ring))
    simp_rw [one_div] at h_mono; rw [integral_const_mul, ld_integral_univ_inv_one_add_sq] at h_mono
    exact h_mono.trans (le_max_left _ _)
  have hMm_L1_diff : ∫ x : ℝ, |(M_minus x).re - kernelK (Real.pi / 2) x| ≤ C_L1_tot / Δ := by
    have h_eq : ∫ x : ℝ, |(M_minus x).re - kernelK (Real.pi / 2) x| = ∫ x : ℝ, (kernelK (Real.pi / 2) x - (M_minus x).re) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_iff.mpr (by simp : volume {x : ℝ | ¬x ≠ 0} = 0)] with x hx
      rw [abs_sub_comm]; exact abs_of_nonneg (sub_nonneg.mpr (hM_maj x hx).1)
    rw [h_eq, integral_sub (kernelK_integrable (Real.pi / 2)) hMm_int_re, hK_pi2_zero, zero_sub]
    have h1 : -∫ x : ℝ, (M_minus x).re ≤ Real.pi / (2 * Δ) + C₃ * Real.exp (-2 * Real.pi * Δ) := by linarith [(abs_le.mp hMm_int).1]
    calc -∫ x : ℝ, (M_minus x).re ≤ Real.pi / (2 * Δ) + C₃ * (1 / Δ) := by linarith [mul_le_mul_of_nonneg_left h_exp_1Δ hC₃.le]
      _ = (Real.pi / 2 + C₃) / Δ := by ring
      _ ≤ C_L1_tot / Δ := by gcongr; exact le_trans (by linarith) (le_max_right _ _)
  have hMm_L1 : ∫ x : ℝ, |(M_minus x).re| ≤ C_L1_tot := by
    have h_mono : ∫ x : ℝ, |(M_minus x).re| ≤ ∫ x : ℝ, C₃ * (1 / (1 + x ^ 2)) := by
      refine integral_mono hMm_int_re.abs (integrable_inv_one_add_sq.const_mul C₃) fun x => ?_
      exact (Complex.abs_re_le_norm _).trans ((hM_sup x).2.trans_eq (by ring))
    simp_rw [one_div] at h_mono; rw [integral_const_mul, ld_integral_univ_inv_one_add_sq] at h_mono
    exact h_mono.trans (le_max_left _ _)
  let h_hat_p := fourierHat (fun x : ℝ => ((M_plus x).re : ℂ))
  let h_hat_m := fourierHat (fun x : ℝ => ((M_minus x).re : ℂ))
  have hMp_real_eq : (fun x : ℝ => ((M_plus x).re : ℂ)) = M_plus := by
    ext x; exact Complex.ext rfl (hM_im x).1.symm
  have hMm_real_eq : (fun x : ℝ => ((M_minus x).re : ℂ)) = M_minus := by
    ext x; exact Complex.ext rfl (hM_im x).2.symm
  have h_hat_p_eq : fourierHat M_plus = h_hat_p := by dsimp only [h_hat_p]; rw [hMp_real_eq]
  have h_hat_m_eq : fourierHat M_minus = h_hat_m := by dsimp only [h_hat_m]; rw [hMm_real_eq]
  have hQ_ge_100 : 100 ≤ analyticConductor q t₀ := by
    have h_q100 : (100 : ℝ) ≤ q := by
      have : (100 : ℝ) ≤ Real.exp (Real.exp 100) := by
        have : (100 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
        linarith [Real.add_one_le_exp (Real.exp 100)]
      have : Real.exp (Real.exp 100) ≤ Real.exp (Real.exp L_α) :=
        Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (le_max_left _ _))
      linarith
    exact h_q100.trans hac_ge_q
  have h_common_err : ∀ (M_fn : ℂ → ℂ) (M_re : ℝ → ℝ) (h_int_re : Integrable (fun x : ℝ => M_re x - kernelK (Real.pi / 2) x))
      (h_L1_diff : ∫ x : ℝ, |M_re x - kernelK (Real.pi / 2) x| ≤ C_L1_tot / Δ)
      (h_L1 : ∫ x : ℝ, |M_re x| ≤ C_L1_tot)
      (hM_sup_1 : ∀ x : ℝ, ‖M_fn x‖ ≤ C_₃_bd / (1 + x ^ 2) → True)
      (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive), True := fun _ _ _ _ _ _ _ _ => trivial
  clear h_common_err
  let S_p := Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
    χ.IsPrimitive ∧ |primeSum1 q χ h_hat_p X t₀| ≥ V / 4)
  let S_m := Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
    χ.IsPrimitive ∧ |primeSum1 q χ h_hat_m X t₀| ≥ V / 4)
  let S_all := Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
    χ.IsPrimitive ∧ D.nonvanishing q χ t₀ ∧ |D.S_val q χ t₀| ≥ V)
  have h_sub_union : S_all ⊆ S_p ∪ S_m := by
    intro χ hχ
    rw [Finset.mem_filter] at hχ
    rcases hχ with ⟨_, hχ_prim, hχ_nv, hχ_S⟩
    have hGRH := hGRH_all χ hχ_prim
    have hq1_t : q = 1 → |t₀| ≥ 10 := fun hq_eq1 => by omega
    obtain ⟨hsumm_K, h_hzs⟩ := h_hzs_S q hq1 χ hχ_prim hGRH t₀ hχ_nv hq1_t
    set Q : ℝ := analyticConductor q t₀
    have h_env_le : (Real.log Q / (2 * Real.pi)) * (Real.pi / (2 * Δ) + C₃ * Real.exp (-2 * Real.pi * Δ)) ≤
        V / 4 + C₃ * Real.log (Real.log q) := by
      have h1 : (Real.log Q / (2 * Real.pi)) * (Real.pi / (2 * Δ)) ≤ V / 4 := by
        calc (Real.log Q / (2 * Real.pi)) * (Real.pi / (2 * Δ)) = Real.log Q / (4 * Δ) := by
              field_simp [Real.pi_ne_zero]; ring
          _ = V / (4 * K_scale) := by dsimp only [Δ, Q]; field_simp [hV_pos.ne']; ring
          _ = V / 8 := by dsimp only [K_scale]; ring
          _ ≤ V / 4 := by linarith
      have h_2piΔ : Real.log (Real.log q) ≤ 2 * Real.pi * Δ := by
        have h_1 : 1 ≤ Real.pi * K_scale := by nlinarith [Real.two_le_pi]
        have h_v : V * Real.log (Real.log q) ≤ Real.log q := by rwa [le_div_iff₀ hLLq_pos] at hV_ub
        calc Real.log (Real.log q) ≤ Real.pi * K_scale * Real.log (Real.log q) := le_mul_of_one_le_left hLLq_pos.le h_1
          _ ≤ 2 * Real.pi * (K_scale * Real.log Q / V) := by
              rw [le_div_iff₀ hV_pos]
              calc Real.pi * K_scale * Real.log (Real.log q) * V = Real.pi * K_scale * (V * Real.log (Real.log q)) := by ring
                _ ≤ Real.pi * K_scale * Real.log q := by gcongr
                _ ≤ 2 * Real.pi * K_scale * Real.log Q := by nlinarith [hlog_ac_ge, Real.pi_pos]
      have h_exp_lt : Real.exp (-2 * Real.pi * Δ) ≤ 1 / Real.log q := by
        rw [Real.exp_neg, inv_eq_one_div]
        exact div_le_div_of_nonneg_left zero_le_one hlogq_pos (by
          calc Real.log q = Real.exp (Real.log (Real.log q)) := (Real.exp_log hlogq_pos).symm
            _ ≤ Real.exp (2 * Real.pi * Δ) := Real.exp_le_exp.mpr h_2piΔ)
      have h2 : (Real.log Q / (2 * Real.pi)) * (C₃ * Real.exp (-2 * Real.pi * Δ)) ≤ C₃ * Real.log (Real.log q) := by
        calc (Real.log Q / (2 * Real.pi)) * (C₃ * Real.exp (-2 * Real.pi * Δ))
            ≤ (2 * Real.log q / (2 * Real.pi)) * (C₃ * (1 / Real.log q)) := by gcongr
          _ = C₃ / Real.pi := by field_simp [hlogq_pos.ne', Real.pi_ne_zero]; ring
          _ ≤ C₃ * Real.log (Real.log q) := by
              have : 1 / Real.pi ≤ Real.log (Real.log q) := by
                have : 1 / Real.pi ≤ 1 := div_le_one_of_le₀ (by linarith [Real.two_le_pi]) Real.pi_pos.le
                linarith
              nlinarith [hC₃]
      linarith
    have h_gw_err : C₁ * (C₃ + (if q = 1 then Real.exp (Real.pi * Δ) / t₀ ^ 2 * C₃ else 0)) ≤
        2 * C₁ * C₃ * Real.log (Real.log q) := by
      rw [if_neg (by omega : q ≠ 1), add_zero]
      have : 1 ≤ Real.log (Real.log q) := by linarith
      nlinarith [mul_nonneg hC₁.le hC₃.le]
    have h_loglogX : Real.log (Real.log X) ≤ Real.log (Real.log q) :=
      Real.log_le_log hlogX_pos (by linarith [hlogX_le_half])
    have h_C₀_le : C₀ ≤ C₀ * Real.log (Real.log q) := le_mul_of_one_le_right hC₀.le (by linarith)
    have h_tot_err : 2 * C_tail * Real.log (Real.log q) + C₀ + 2 * C₁ * C₃ * Real.log (Real.log q) +
        C₃ * Real.log (Real.log q) ≤ V / 4 := by
      have h_a : (8 * C_tail + 8 * C₀ + 8 * C₁ * C₃ + 8 * C₃ + 8) ≤ A :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
      nlinarith
    rcases le_total 0 (D.S_val q χ t₀) with hS_pos | hS_neg
    · left; rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, hχ_prim, ?_⟩
      rw [abs_of_nonneg hS_pos] at hχ_S
      have hMp_sup_bd : ∀ x : ℝ, ‖M_plus x‖ ≤ C₃ / (1 + x ^ 2) := fun x => (hM_sup x).1
      obtain ⟨hsumm_Mp, h_gw_p⟩ := h_gw q hq1 χ hχ_prim hGRH M_plus Δ C₃ hΔ_ge_1 hC₃.le hMp_exp hMp_sup_bd
        (fun x => (hM_im x).1) t₀ hq1_t
      rw [h_hat_p_eq] at h_gw_p
      have h_sum_le : ∑' n : ℕ, kernelK (Real.pi / 2) (t₀ - D.zeros q χ n) ≤
          ∑' n : ℕ, (M_plus (t₀ - D.zeros q χ n)).re := by
        refine Summable.tsum_le_tsum (fun n => ?_) hsumm_K hsumm_Mp
        exact (hM_maj _ (sub_ne_zero.mpr (D.nonvanishing_zeros q χ t₀ hχ_nv n))).2
      have h_tail_p := h_tail q χ h_hat_p Δ (fun x => (M_plus x).re) hΔ_ge_Δ₀ hMp_real hMp_L1_diff hMp_L1 t₀
      have h_p23 : |primeSum2 q χ h_hat_p X t₀ + primeSumGe3 q χ h_hat_p X t₀| ≤ 2 * C_tail * Real.log (Real.log q) := by
        have h1 : |primeSum2 q χ h_hat_p X t₀| ≤ C_tail * Real.log (Real.log q) :=
          h_tail_p.1.trans (mul_le_mul_of_nonneg_left h_loglogX hC_tail.le)
        have h2 : |primeSumGe3 q χ h_hat_p X t₀| ≤ C_tail * Real.log (Real.log q) :=
          h_tail_p.2.trans (le_mul_of_one_le_right hC_tail.le (by linarith))
        linarith [abs_add_le (primeSum2 q χ h_hat_p X t₀) (primeSumGe3 q χ h_hat_p X t₀)]
      have h_P_split : primePowerSum q χ h_hat_p X t₀ =
          primeSum1 q χ h_hat_p X t₀ + primeSum2 q χ h_hat_p X t₀ + primeSumGe3 q χ h_hat_p X t₀ := by
        unfold primeSumGe3; ring
      have h_int_p : (Real.log Q / (2 * Real.pi)) * ∫ x : ℝ, (M_plus x).re ≤ V / 4 + C₃ * Real.log (Real.log q) := by
        have h1 : ∫ x : ℝ, (M_plus x).re ≤ Real.pi / (2 * Δ) + C₃ * Real.exp (-2 * Real.pi * Δ) := by
          linarith [(abs_le.mp hMp_int).2]
        have h2 : 0 ≤ Real.log Q / (2 * Real.pi) := div_nonneg (Real.log_nonneg (by linarith)) (by positivity)
        exact (mul_le_mul_of_nonneg_left h1 h2).trans h_env_le
      have h_g := (abs_le.mp h_gw_p).2
      have h_h := (abs_le.mp h_hzs).2
      have h_p := (abs_le.mp h_p23).1
      have h_pi_v : Real.pi * D.S_val q χ t₀ ≥ V := by nlinarith [Real.two_le_pi]
      have h_neg : -primeSum1 q χ h_hat_p X t₀ ≥ V / 4 := by linarith
      exact le_trans h_neg (neg_le_abs _)
    · right; rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, hχ_prim, ?_⟩
      rw [abs_of_nonpos hS_neg] at hχ_S
      let M_neg : ℂ → ℂ := fun z => -M_minus z
      have hMn_exp : HasExponentialType M_neg (2 * Real.pi * Δ) :=
        ⟨hMm_exp.1.neg, fun ε hε => by
          obtain ⟨C, hC, hbd⟩ := hMm_exp.2 ε hε
          exact ⟨C, hC, fun z => by simpa [M_neg] using hbd z⟩⟩
      have hMn_sup : ∀ x : ℝ, ‖M_neg x‖ ≤ C₃ / (1 + x ^ 2) := fun x => by simpa [M_neg] using (hM_sup x).2
      have hMn_im : ∀ x : ℝ, (M_neg x).im = 0 := fun x => by simp [M_neg, (hM_im x).2]
      obtain ⟨hsumm_Mn, h_gw_n⟩ := h_gw q hq1 χ hχ_prim hGRH M_neg Δ C₃ hΔ_ge_1 hC₃.le hMn_exp hMn_sup hMn_im t₀ hq1_t
      have h_hat_neg : fourierHat (fun x : ℝ => M_neg x) = fun ξ => -h_hat_m ξ := by
        ext ξ; unfold fourierHat; simp only [M_neg, neg_mul, integral_neg, Pi.neg_apply, h_hat_m_eq]
      have h_P_neg : primePowerSum q χ (fun ξ => -h_hat_m ξ) X t₀ = -primePowerSum q χ h_hat_m X t₀ := by
        unfold primePowerSum
        simp only [mul_neg, neg_add_rev, Complex.neg_re, mul_neg, Finset.sum_neg_distrib]
        ring
      have h_int_neg : ∫ x : ℝ, (M_neg x).re = -∫ x : ℝ, (M_minus x).re := by
        simp only [M_neg, Complex.neg_re, integral_neg]
      rw [h_hat_neg, h_P_neg, h_int_neg] at h_gw_n
      have h_sum_le : -(∑' n : ℕ, kernelK (Real.pi / 2) (t₀ - D.zeros q χ n)) ≤
          ∑' n : ℕ, (M_neg (t₀ - D.zeros q χ n)).re := by
        have h_eq : ∑' n : ℕ, (M_neg (t₀ - D.zeros q χ n)).re =
            ∑' n : ℕ, -(M_minus (t₀ - D.zeros q χ n)).re := rfl
        have h_summ_negK : Summable (fun n : ℕ => -kernelK (Real.pi / 2) (t₀ - D.zeros q χ n)) := hsumm_K.neg
        rw [← tsum_neg]
        exact Summable.tsum_le_tsum (fun n => by
          simp only [M_neg, Complex.neg_re]
          exact neg_le_neg (hM_maj _ (sub_ne_zero.mpr (D.nonvanishing_zeros q χ t₀ hχ_nv n))).1) h_summ_negK hsumm_Mn
      have h_tail_m := h_tail q χ h_hat_m Δ (fun x => (M_minus x).re) hΔ_ge_Δ₀ hMm_real hMm_L1_diff hMm_L1 t₀
      have h_p23 : |primeSum2 q χ h_hat_m X t₀ + primeSumGe3 q χ h_hat_m X t₀| ≤ 2 * C_tail * Real.log (Real.log q) := by
        have h1 : |primeSum2 q χ h_hat_m X t₀| ≤ C_tail * Real.log (Real.log q) :=
          h_tail_m.1.trans (mul_le_mul_of_nonneg_left h_loglogX hC_tail.le)
        have h2 : |primeSumGe3 q χ h_hat_m X t₀| ≤ C_tail * Real.log (Real.log q) :=
          h_tail_m.2.trans (le_mul_of_one_le_right hC_tail.le (by linarith))
        linarith [abs_add_le (primeSum2 q χ h_hat_m X t₀) (primeSumGe3 q χ h_hat_m X t₀)]
      have h_P_split : primePowerSum q χ h_hat_m X t₀ =
          primeSum1 q χ h_hat_m X t₀ + primeSum2 q χ h_hat_m X t₀ + primeSumGe3 q χ h_hat_m X t₀ := by
        unfold primeSumGe3; ring
      have h_int_m : (Real.log Q / (2 * Real.pi)) * (-∫ x : ℝ, (M_minus x).re) ≤ V / 4 + C₃ * Real.log (Real.log q) := by
        have h1 : -∫ x : ℝ, (M_minus x).re ≤ Real.pi / (2 * Δ) + C₃ * Real.exp (-2 * Real.pi * Δ) := by
          linarith [(abs_le.mp hMm_int).1]
        have h2 : 0 ≤ Real.log Q / (2 * Real.pi) := div_nonneg (Real.log_nonneg (by linarith)) (by positivity)
        exact (mul_le_mul_of_nonneg_left h1 h2).trans h_env_le
      have h_g := (abs_le.mp h_gw_n).2
      have h_h := (abs_le.mp h_hzs).1
      have h_p := (abs_le.mp h_p23).2
      have h_pi_v : Real.pi * (-D.S_val q χ t₀) ≥ V := by nlinarith [Real.two_le_pi]
      have h_pos : primeSum1 q χ h_hat_m X t₀ ≥ V / 4 := by linarith
      exact le_trans h_pos (le_abs_self _)
  have h_card_union : (S_all.card : ℝ) ≤ (S_p.card : ℝ) + (S_m.card : ℝ) := by
    have h1 : S_all.card ≤ S_p.card + S_m.card :=
      (Finset.card_le_card h_sub_union).trans (Finset.card_union_le S_p S_m)
    exact_mod_cast h1
  let S_prim := Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)
  have h_markov_branch : ∀ (h_hat : ℝ → ℂ) (M_re : ℝ → ℝ),
      Integrable (fun x : ℝ => M_re x - kernelK (Real.pi / 2) x) →
      (∫ x : ℝ, |M_re x - kernelK (Real.pi / 2) x|) ≤ C_L1_tot / Δ →
      (∫ x : ℝ, |M_re x|) ≤ C_L1_tot →
      (1 / (totientStar q : ℝ)) *
        ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
          χ.IsPrimitive ∧ |primeSum1 q χ h_hat X t₀| ≥ V / 4)).card : ℝ) ≤
        (16 * Real.exp 61 * B * (2 * Real.pi * K_scale) * Real.log (Real.log q) / V) ^ k := by
    intro h_hat M_re hM_int_r hM_L1_diff_r hM_L1_r
    let S_br := Finset.univ.filter (fun χ : DirichletCharacter ℂ q =>
      χ.IsPrimitive ∧ |primeSum1 q χ h_hat X t₀| ≥ V / 4)
    have h_sub_prim : S_br ⊆ S_prim := fun χ hχ => by
      rw [Finset.mem_filter] at hχ ⊢; exact ⟨Finset.mem_univ _, hχ.2.1⟩
    have h_markov : (V / 4) ^ (2 * k) * (S_br.card : ℝ) ≤
        ∑ χ ∈ S_prim, |primeSum1 q χ h_hat X t₀| ^ (2 * k) := by
      calc (V / 4) ^ (2 * k) * (S_br.card : ℝ)
          = ∑ _χ ∈ S_br, (V / 4) ^ (2 * k) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ χ ∈ S_br, |primeSum1 q χ h_hat X t₀| ^ (2 * k) := by
            refine Finset.sum_le_sum fun χ hχ => ?_
            rw [Finset.mem_filter] at hχ
            exact pow_le_pow_left₀ (by positivity) hχ.2.2 (2 * k)
        _ ≤ ∑ χ ∈ S_prim, |primeSum1 q χ h_hat X t₀| ^ (2 * k) :=
            Finset.sum_le_sum_of_subset_of_nonneg h_sub_prim (fun _ _ _ => by positivity)
    have h_mom_bd := h_mom q t₀ Δ k M_re hq_ge_3 hqstar hΔ_ge_Δ₀ hXk_lt_q hM_int_r hM_L1_diff_r hM_L1_r
    have h_tot_star : (Nat.totient q : ℝ) / (totientStar q : ℝ) ≤ (2 * Real.exp 61) ^ k := by
      have h_t1 := totient_div_totientStar_le q hq_ge_3 hqstar
      have h_30_le_k : 30 * Real.log (Real.log q) ≤ (k : ℝ) := by
        have h_a : 320 * (2 * Real.pi * K_scale) + 1 ≤ A := le_trans (le_max_left _ _) (le_max_right _ _)
        have h_k1 : (3 : ℝ) * (320 * (2 * Real.pi * K_scale)) * Real.log (Real.log q) / (16 * (2 * Real.pi * K_scale)) ≤ (k : ℝ) := by
          calc (3 : ℝ) * (320 * (2 * Real.pi * K_scale)) * Real.log (Real.log q) / (16 * (2 * Real.pi * K_scale))
              ≤ (3 : ℝ) * (A * Real.log (Real.log q)) / (16 * (2 * Real.pi * K_scale)) := by gcongr; linarith
            _ ≤ (3 : ℝ) * V / (16 * (2 * Real.pi * K_scale)) := by gcongr
            _ ≤ (k : ℝ) := hk_lb
        have h_eq : (3 : ℝ) * (320 * (2 * Real.pi * K_scale)) * Real.log (Real.log q) / (16 * (2 * Real.pi * K_scale)) =
            60 * Real.log (Real.log q) := by field_simp [Real.pi_ne_zero]; ring
        linarith
      have h_logq_pow : (Real.log q) ^ 30 ≤ Real.exp k := by
        calc (Real.log q) ^ 30 = Real.exp ((30 : ℕ) * Real.log (Real.log q)) := by
              rw [← Real.log_pow, Real.exp_log (pow_pos hlogq_pos 30)]
          _ ≤ Real.exp (k : ℝ) := by push_cast; exact Real.exp_le_exp.mpr h_30_le_k
      have h_c_pow : 2 * Real.exp 60 ≤ (2 * Real.exp 60) ^ k :=
        le_self_pow₀ (by have : 1 ≤ Real.exp 60 := Real.one_le_exp (by norm_num); linarith) hk_pos.ne'
      have h_exp_k : Real.exp (k : ℝ) = (Real.exp 1) ^ k := by rw [← Real.exp_nat_mul, mul_one]
      calc (Nat.totient q : ℝ) / (totientStar q : ℝ)
          ≤ 2 * Real.exp 60 * (Real.log q) ^ 30 := h_t1
        _ ≤ (2 * Real.exp 60) ^ k * (Real.exp 1) ^ k := by gcongr; rwa [← h_exp_k]
        _ = (2 * Real.exp 60 * Real.exp 1) ^ k := (mul_pow _ _ _).symm
        _ = (2 * Real.exp 61) ^ k := by congr 1; rw [mul_assoc, ← Real.exp_add]; norm_num
    have h_loglogX : Real.log (Real.log X) ≤ Real.log (Real.log q) :=
      Real.log_le_log hlogX_pos (by linarith [hlogX_le_half])
    have h_base : (4 / V) ^ 2 * (2 * Real.exp 61 * B * k * Real.log (Real.log X)) ≤
        16 * Real.exp 61 * B * (2 * Real.pi * K_scale) * Real.log (Real.log q) / V := by
      calc (4 / V) ^ 2 * (2 * Real.exp 61 * B * k * Real.log (Real.log X))
          ≤ (16 / V ^ 2) * (2 * Real.exp 61 * B * (V / (2 * Real.pi * K_scale)) * Real.log (Real.log q)) := by
            gcongr; ring_nf; rfl
        _ = (16 * Real.exp 61 * B / (Real.pi * K_scale)) * Real.log (Real.log q) / V := by
            field_simp [hV_pos.ne', Real.pi_ne_zero]; ring
        _ ≤ 16 * Real.exp 61 * B * (2 * Real.pi * K_scale) * Real.log (Real.log q) / V := by
            gcongr
            have : 1 ≤ 2 * Real.pi * K_scale := by nlinarith [Real.two_le_pi]
            have : 0 ≤ 16 * Real.exp 61 * B := by positivity
            nlinarith [Real.two_le_pi]
    have h_pow_pos : 0 < (V / 4) ^ (2 * k) := pow_pos (by positivity) (2 * k)
    have hqstar_pos : (0 : ℝ) < totientStar q := by exact_mod_cast hqstar
    have h1 : (1 / (totientStar q : ℝ)) * (S_br.card : ℝ) ≤
        ((4 / V) ^ 2 * (2 * Real.exp 61 * B * k * Real.log (Real.log X))) ^ k := by
      calc (1 / (totientStar q : ℝ)) * (S_br.card : ℝ)
          ≤ (1 / (totientStar q : ℝ)) * ((∑ χ ∈ S_prim, |primeSum1 q χ h_hat X t₀| ^ (2 * k)) / (V / 4) ^ (2 * k)) := by
            gcongr; rwa [le_div_iff₀ h_pow_pos, mul_comm]
        _ = (1 / (V / 4) ^ (2 * k)) * ((1 / (totientStar q : ℝ)) * ∑ χ ∈ S_prim, |primeSum1 q χ h_hat X t₀| ^ (2 * k)) := by
            ring
        _ ≤ (1 / (V / 4) ^ (2 * k)) * (((Nat.totient q : ℝ) / (totientStar q : ℝ)) * (B * k * Real.log (Real.log X)) ^ k) := by
            gcongr; exact h_mom_bd
        _ ≤ (1 / (V / 4) ^ (2 * k)) * ((2 * Real.exp 61) ^ k * (B * k * Real.log (Real.log X)) ^ k) := by
            gcongr
        _ = ((4 / V) ^ 2 * (2 * Real.exp 61 * B * k * Real.log (Real.log X))) ^ k := by
            rw [mul_pow, mul_pow, ← pow_mul, mul_comm 2 k, one_div_pow, div_pow, one_div_div]; ring
    exact h1.trans (pow_le_pow_left₀ (by positivity) h_base k)
  have h_bp := h_markov_branch h_hat_p (fun x => (M_plus x).re) hMp_real hMp_L1_diff hMp_L1
  have h_bm := h_markov_branch h_hat_m (fun x => (M_minus x).re) hMm_real hMm_L1_diff hMm_L1
  have h_div_v : (1 / (totientStar q : ℝ)) * (S_all.card : ℝ) ≤
      (C_B * Real.log (Real.log q) / V) ^ k := by
    have h_2_pow : (2 : ℝ) ≤ 2 ^ k := by
      have : 2 ≤ 2 ^ 2 := by norm_num
      exact this.trans (pow_le_pow_right₀ (by norm_num) hk_ge_2)
    calc (1 / (totientStar q : ℝ)) * (S_all.card : ℝ)
        ≤ (1 / (totientStar q : ℝ)) * ((S_p.card : ℝ) + (S_m.card : ℝ)) := by gcongr
      _ = (1 / (totientStar q : ℝ)) * (S_p.card : ℝ) + (1 / (totientStar q : ℝ)) * (S_m.card : ℝ) := by ring
      _ ≤ (16 * Real.exp 61 * B * (2 * Real.pi * K_scale) * Real.log (Real.log q) / V) ^ k +
            (16 * Real.exp 61 * B * (2 * Real.pi * K_scale) * Real.log (Real.log q) / V) ^ k := add_le_add h_bp h_bm
      _ = 2 * (16 * Real.exp 61 * B * (2 * Real.pi * K_scale) * Real.log (Real.log q) / V) ^ k := by ring
      _ ≤ 2 ^ k * (16 * Real.exp 61 * B * (2 * Real.pi * K_scale) * Real.log (Real.log q) / V) ^ k := by gcongr
      _ = (C_B * Real.log (Real.log q) / V) ^ k := by rw [← mul_pow]; dsimp only [C_B]; ring_nf
  have h_ratio_le : C_B * Real.log (Real.log q) / V ≤ (Real.log (Real.log q) / V) ^ (1 / 2 : ℝ) := by
    have h_a : C_B ^ 2 ≤ A :=
      le_trans (by linarith) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
    have h_cb_le : C_B ^ 2 * Real.log (Real.log q) ≤ V := by
      calc C_B ^ 2 * Real.log (Real.log q) ≤ A * Real.log (Real.log q) := by gcongr
        _ ≤ V := hV_lb
    have h_sq : (C_B * Real.log (Real.log q) / V) ^ 2 ≤ Real.log (Real.log q) / V := by
      rw [div_pow, div_le_div_iff₀ (sq_pos_of_pos hV_pos) hV_pos]
      nlinarith [h_cb_le, hLLq_pos]
    calc C_B * Real.log (Real.log q) / V = Real.sqrt ((C_B * Real.log (Real.log q) / V) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (Real.log (Real.log q) / V) := Real.sqrt_le_sqrt h_sq
      _ = (Real.log (Real.log q) / V) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have h_log_ratio : (1 / 2 : ℝ) * Real.log (V / Real.log (Real.log q)) ≤ -Real.log (C_B * Real.log (Real.log q) / V) := by
    have h1 : Real.log (C_B * Real.log (Real.log q) / V) ≤ (1 / 2 : ℝ) * Real.log (Real.log (Real.log q) / V) := by
      calc Real.log (C_B * Real.log (Real.log q) / V)
          ≤ Real.log ((Real.log (Real.log q) / V) ^ (1 / 2 : ℝ)) := Real.log_le_log (by positivity) h_ratio_le
        _ = (1 / 2 : ℝ) * Real.log (Real.log (Real.log q) / V) := Real.log_rpow (by positivity) _
    have h2 : Real.log (Real.log (Real.log q) / V) = -Real.log (V / Real.log (Real.log q)) := by
      rw [← Real.log_inv, inv_div]
    linarith
  have h_exp_final : (C_B * Real.log (Real.log q) / V) ^ k ≤
      Real.exp (-((3 / (32 * (2 * Real.pi * K_scale))) * V * Real.log (V / Real.log (Real.log q)))) := by
    rw [← Real.exp_log (pow_pos (by positivity) k), Real.log_pow]
    apply Real.exp_le_exp.mpr
    have h_l_ge_1 : 1 ≤ V / Real.log (Real.log q) := by
      rw [le_div_iff₀ hLLq_pos]; have : 1 ≤ A := by linarith; nlinarith
    have h_log_nonneg : 0 ≤ Real.log (V / Real.log (Real.log q)) := Real.log_nonneg h_l_ge_1
    have h_k_log : (3 / (32 * (2 * Real.pi * K_scale))) * V * Real.log (V / Real.log (Real.log q)) ≤
        (k : ℝ) * (-Real.log (C_B * Real.log (Real.log q) / V)) := by
      calc (3 / (32 * (2 * Real.pi * K_scale))) * V * Real.log (V / Real.log (Real.log q))
          = ((3 : ℝ) * V / (16 * (2 * Real.pi * K_scale))) * ((1 / 2 : ℝ) * Real.log (V / Real.log (Real.log q))) := by ring
        _ ≤ (k : ℝ) * (-Real.log (C_B * Real.log (Real.log q) / V)) := by
            gcongr; exact hk_lb
    linarith
  have h_log_v : (1 / 4 : ℝ) * Real.log (Real.log q) ≤ Real.log (V / Real.log (Real.log q)) := by
    have h_v_eq : V / Real.log (Real.log q) = α * Real.sqrt (Real.log q / Real.log (Real.log q)) := by
      dsimp only [V]; rw [Real.sqrt_mul hlogq_pos.le, Real.sqrt_div hlogq_pos.le]; field_simp [hLLq_pos.ne']
      rw [← Real.sq_sqrt hLLq_pos.le]; ring
    have h_ge_exp : (Real.log (Real.log q)) ^ (1 / 4 : ℝ) ≤ α * Real.sqrt (Real.log q / Real.log (Real.log q)) := by
      have h1 : (Real.exp 1 / α) ^ 4 ≤ Real.log (Real.log q) :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hLLq_ge)))
      have h2 : Real.exp 1 / α ≤ (Real.log (Real.log q)) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast (Real.exp 1 / α) 4] at h1
        have := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
        rwa [← Real.rpow_mul (by positivity), show (4 : ℕ) * (1 / 4 : ℝ) = 1 by norm_num, Real.rpow_one] at this
      have h3 : (Real.log (Real.log q)) ^ (1 / 2 : ℝ) ≤ Real.sqrt (Real.log q / Real.log (Real.log q)) := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.sqrt_le_sqrt (by have : 1 ≤ Real.log (Real.log q) := by linarith; nlinarith [h_ratio_ge])
      have h4 : (Real.log (Real.log q)) ^ (1 / 4 : ℝ) * (Real.log (Real.log q)) ^ (1 / 4 : ℝ) =
          (Real.log (Real.log q)) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hLLq_pos]; norm_num
      have h5 : 1 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      calc (Real.log (Real.log q)) ^ (1 / 4 : ℝ) = 1 * (Real.log (Real.log q)) ^ (1 / 4 : ℝ) := (one_mul _).symm
        _ ≤ Real.exp 1 * (Real.log (Real.log q)) ^ (1 / 4 : ℝ) := by gcongr
        _ = α * ((Real.exp 1 / α) * (Real.log (Real.log q)) ^ (1 / 4 : ℝ)) := by field_simp [hα.ne']
        _ ≤ α * ((Real.log (Real.log q)) ^ (1 / 4 : ℝ) * (Real.log (Real.log q)) ^ (1 / 4 : ℝ)) := by gcongr
        _ = α * (Real.log (Real.log q)) ^ (1 / 2 : ℝ) := by rw [h4]
        _ ≤ α * Real.sqrt (Real.log q / Real.log (Real.log q)) := by gcongr
    rw [h_v_eq]
    calc (1 / 4 : ℝ) * Real.log (Real.log q) = Real.log ((Real.log (Real.log q)) ^ (1 / 4 : ℝ)) :=
          (Real.log_rpow hLLq_pos _).symm
      _ ≤ Real.log (α * Real.sqrt (Real.log q / Real.log (Real.log q))) := Real.log_le_log (by positivity) h_ge_exp
  have h_exp_le2 : Real.exp (-((3 / (32 * (2 * Real.pi * K_scale))) * V * Real.log (V / Real.log (Real.log q)))) ≤
      Real.exp (-c * α * Real.sqrt (Real.log q) * (Real.log (Real.log q)) ^ (3 / 2 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have h_v_eq : V * Real.log (Real.log q) = α * Real.sqrt (Real.log q) * (Real.log (Real.log q)) ^ (3 / 2 : ℝ) := by
      dsimp only [V]; rw [Real.sqrt_mul hlogq_pos.le, Real.sqrt_eq_rpow (Real.log (Real.log q))]
      have h_32 : (Real.log (Real.log q)) ^ (1 / 2 : ℝ) * Real.log (Real.log q) = (Real.log (Real.log q)) ^ (3 / 2 : ℝ) := by
        conv_lhs => rhs; rw [← Real.rpow_one (Real.log (Real.log q))]
        rw [← Real.rpow_add hLLq_pos]; norm_num
      nlinarith [h_32]
    dsimp only [c]
    nlinarith [hV_pos]
  exact h_div_v.trans (h_exp_final.trans h_exp_le2)

end PolarEvaluation
