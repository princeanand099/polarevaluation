import PolarEvaluation.Basic
import PolarEvaluation.ExternalResults
import PolarEvaluation.ExplicitFormulae
import PolarEvaluation.ShiftedLattice
import PolarEvaluation.PrimeMoments
import PolarEvaluation.TotientStar
import PolarEvaluation.LargeDeviationsT

/-!
# Large-Deviation Bounds for `S(t₀, χ)` in the q-Aspect (Corollary 1.6(ii))
-/

noncomputable section

open Complex Real MeasureTheory Filter Topology Classical

namespace PolarEvaluation

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
    rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]; exact h3.trans_eq (one_mul _).symm
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
