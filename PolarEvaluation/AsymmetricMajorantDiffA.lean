import PolarEvaluation.AsymmetricMajorantBounds

noncomputable section

open Complex Real MeasureTheory Filter Topology
open scoped FourierTransform

namespace PolarEvaluation

private lemma normSq_sub_I_mul (y v : ℝ) : ‖(y : ℂ) - Complex.I * v‖ ^ 2 = y ^ 2 + v ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  ring

private lemma normSq_I_mul_sub (Δ y : ℝ) : ‖Complex.I * Δ - (y : ℂ)‖ ^ 2 = y ^ 2 + Δ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  ring

lemma limitingJ_upper_bound (θ : ℝ) (hθ : |θ| < Real.pi / 2) :
    ∃ C_up > 0, ∀ y : ℝ, 1 ≤ |y| → |limitingJ y θ| ≤ C_up / y ^ 2 := by
  obtain ⟨Y₀, C_inf, hY₀, hC_inf, h_asymp⟩ := limitingJ_asymptotic θ hθ
  have hcont_pos : ContinuousOn (fun y : ℝ => |limitingJ y θ|) (Set.Icc 1 Y₀) :=
    (limitingJ_continuousOn_Icc θ hθ hY₀ (fun h => by linarith [h.1])).abs
  obtain ⟨y_plus, _, hy_plus_max⟩ := isCompact_Icc.exists_isMaxOn ⟨1, Set.left_mem_Icc.mpr hY₀⟩ hcont_pos
  have hcont_neg : ContinuousOn (fun y : ℝ => |limitingJ y θ|) (Set.Icc (-Y₀) (-1)) :=
    (limitingJ_continuousOn_Icc θ hθ (by linarith) (fun h => by linarith [h.2])).abs
  obtain ⟨y_minus, _, hy_minus_max⟩ := isCompact_Icc.exists_isMaxOn ⟨-1, Set.right_mem_Icc.mpr (by linarith)⟩ hcont_neg
  let M_mid : ℝ := max |limitingJ y_plus θ| |limitingJ y_minus θ|
  let C_up : ℝ := max (M_mid * Y₀ ^ 2 + 1) (2 * |envelopeC θ| / Real.pi ^ 2 + C_inf)
  refine ⟨C_up, by positivity, fun y hy => ?_⟩
  rcases le_or_gt |y| Y₀ with hy_le | hy_gt
  · have h_mid : |limitingJ y θ| ≤ M_mid := by
      rcases le_total 0 y with hy0 | hy0
      · rw [abs_of_nonneg hy0] at hy hy_le
        exact (hy_plus_max ⟨hy, hy_le⟩).trans (le_max_left _ _)
      · rw [abs_of_nonpos hy0] at hy hy_le
        exact (hy_minus_max ⟨by linarith, by linarith⟩).trans (le_max_right _ _)
    have h1 : y ^ 2 ≤ Y₀ ^ 2 := by rw [← sq_abs y]; exact sq_le_sq' (by linarith) hy_le
    calc |limitingJ y θ| ≤ M_mid := h_mid
      _ ≤ (M_mid * Y₀ ^ 2 + 1) / y ^ 2 := by
          rw [le_div_iff₀ (by rw [← sq_abs]; nlinarith)]
          nlinarith [abs_nonneg (limitingJ y_plus θ), le_max_left |limitingJ y_plus θ| |limitingJ y_minus θ|]
      _ ≤ C_up / y ^ 2 := div_le_div_of_nonneg_right (le_max_left _ _) (sq_nonneg y)
  · have h_as := h_asymp y hy_gt.le
    have h1 : |limitingJ y θ| ≤ 2 * |envelopeC θ| / (Real.pi ^ 2 * y ^ 2) + C_inf / |y| ^ 3 := by
      have htri := abs_sub_abs_le_abs_sub (limitingJ y θ) (2 * envelopeC θ / (Real.pi ^ 2 * y ^ 2))
      have h_eq : |2 * envelopeC θ / (Real.pi ^ 2 * y ^ 2)| = 2 * |envelopeC θ| / (Real.pi ^ 2 * y ^ 2) := by
        rw [abs_div, abs_mul, abs_two, abs_of_pos (mul_pos (pow_pos Real.pi_pos 2) (by rw [← sq_abs]; positivity))]
      linarith
    have h2 : C_inf / |y| ^ 3 ≤ C_inf / y ^ 2 := by
      rw [show |y| ^ 3 = |y| * y ^ 2 by rw [← sq_abs y]; ring]
      exact div_le_div_of_nonneg_left hC_inf.le (by rw [← sq_abs]; nlinarith)
        (le_mul_of_one_le_left (sq_nonneg y) hy)
    have h3 : 2 * |envelopeC θ| / (Real.pi ^ 2 * y ^ 2) + C_inf / y ^ 2 =
        (2 * |envelopeC θ| / Real.pi ^ 2 + C_inf) / y ^ 2 := by ring
    calc |limitingJ y θ| ≤ 2 * |envelopeC θ| / (Real.pi ^ 2 * y ^ 2) + C_inf / y ^ 2 := by linarith
      _ = (2 * |envelopeC θ| / Real.pi ^ 2 + C_inf) / y ^ 2 := h3
      _ ≤ C_up / y ^ 2 := div_le_div_of_nonneg_right (le_max_right _ _) (sq_nonneg y)

private lemma int_exp_neg_two_pi_Ioi (a : ℝ) (ha : 0 ≤ a) :
    ∫ v in Set.Ioi a, Real.exp (-2 * Real.pi * v) = (1 / (2 * Real.pi)) * Real.exp (-2 * Real.pi * a) := by
  have h_lim : Tendsto (fun v : ℝ => -(1 / (2 * Real.pi)) * Real.exp (-2 * Real.pi * v)) atTop (nhds 0) := by
    have h1 : Tendsto (fun v : ℝ => Real.exp (-(2 * Real.pi) * v)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith [Real.pi_pos] : -(2 * Real.pi) < 0))
    simpa using h1.const_mul (-(1 / (2 * Real.pi)))
  have h_int : IntegrableOn (fun v : ℝ => Real.exp (-2 * Real.pi * v)) (Set.Ioi a) := by
    have hc : IntegrableOn (fun v : ℝ => Complex.exp ((-2 * Real.pi : ℂ) * v)) (Set.Ioi a) :=
      integrableOn_exp_mul_complex_Ioi (by simp; positivity) a
    refine hc.norm.congr (Eventually.of_forall fun v => ?_)
    dsimp only
    rw [show (-2 * (Real.pi : ℂ) * v) = ((-2 * Real.pi * v : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h_d : ∀ v ∈ Set.Ici a, HasDerivAt (fun t : ℝ => -(1 / (2 * Real.pi)) * Real.exp (-2 * Real.pi * t))
      (Real.exp (-2 * Real.pi * v)) v := by
    intro v _
    have hd := ((hasDerivAt_id v).const_mul (-2 * Real.pi)).exp.const_mul (-(1 / (2 * Real.pi)))
    refine hd.congr_deriv ?_
    simp only [id_eq]; field_simp [Real.pi_ne_zero]
  have hres := integral_Ioi_of_hasDerivAt_of_tendsto' h_d h_int h_lim
  linarith

private lemma int_mul_exp_neg_two_pi_Ioi (a : ℝ) (ha : 0 ≤ a) :
    ∫ v in Set.Ioi a, v * Real.exp (-2 * Real.pi * v) =
      (a / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2)) * Real.exp (-2 * Real.pi * a) := by
  let G : ℝ → ℝ := fun v => -(v / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2)) * Real.exp (-2 * Real.pi * v)
  have h_int : IntegrableOn (fun v : ℝ => v * Real.exp (-2 * Real.pi * v)) (Set.Ioi a) := by
    have h_e : IntegrableOn (fun v : ℝ => Real.exp (-Real.pi * v)) (Set.Ioi a) := by
      have hc : IntegrableOn (fun v : ℝ => Complex.exp ((-Real.pi : ℂ) * v)) (Set.Ioi a) :=
        integrableOn_exp_mul_complex_Ioi (by simp; positivity) a
      refine hc.norm.congr (Eventually.of_forall fun v => ?_)
      dsimp only
      rw [show (-(Real.pi : ℂ) * v) = ((-Real.pi * v : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine h_e.mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 ≤ v := le_trans ha hv.le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hv0 (Real.exp_pos _).le)]
    have h_v : v ≤ Real.exp (Real.pi * v) := by
      have := Real.add_one_le_exp (Real.pi * v)
      nlinarith [Real.two_le_pi, hv0]
    calc v * Real.exp (-2 * Real.pi * v)
        ≤ Real.exp (Real.pi * v) * Real.exp (-2 * Real.pi * v) := by gcongr
      _ = Real.exp (-Real.pi * v) := by rw [← Real.exp_add]; ring_nf
  have h_lim : Tendsto G atTop (nhds 0) := by
    have h_bnd : ∀ᶠ v : ℝ in atTop, ‖G v‖ ≤ (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2)) * Real.exp (-Real.pi * v) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with v hv
      dsimp only [G]
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by positivity), abs_of_pos (Real.exp_pos _)]
      have h_v : v ≤ Real.exp (Real.pi * v) := by
        have := Real.add_one_le_exp (Real.pi * v)
        nlinarith [Real.two_le_pi]
      calc (v / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2)) * Real.exp (-2 * Real.pi * v)
          ≤ (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2)) * v * Real.exp (-2 * Real.pi * v) := by
            gcongr
            rw [add_mul, mul_comm (1 / (2 * Real.pi)) v, ← mul_div_assoc, mul_one]
            gcongr
            exact le_mul_of_one_le_right (by positivity) hv
        _ ≤ (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2)) * Real.exp (Real.pi * v) * Real.exp (-2 * Real.pi * v) := by gcongr
        _ = (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2)) * Real.exp (-Real.pi * v) := by
            rw [mul_assoc, ← Real.exp_add]; ring_nf
    have h_lim_r : Tendsto (fun v : ℝ => (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2)) * Real.exp (-Real.pi * v)) atTop (nhds 0) := by
      have h1 : Tendsto (fun v : ℝ => Real.exp (-Real.pi * v)) atTop (nhds 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith [Real.pi_pos] : -Real.pi < 0))
      simpa using h1.const_mul _
    exact tendsto_zero_iff_norm_tendsto_zero.mpr (tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds h_lim_r (Eventually.of_forall fun _ => norm_nonneg _) h_bnd)
  have h_d : ∀ v ∈ Set.Ici a, HasDerivAt G (v * Real.exp (-2 * Real.pi * v)) v := by
    intro v _
    have hd1 : HasDerivAt (fun t : ℝ => -(t / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2))) (-(1 / (2 * Real.pi))) v :=
      ((hasDerivAt_neg _).comp v (((hasDerivAt_id v).div_const (2 * Real.pi)).add_const (1 / (4 * Real.pi ^ 2)))).congr_deriv (by ring)
    have hd2 : HasDerivAt (fun t : ℝ => Real.exp (-2 * Real.pi * t)) (-2 * Real.pi * Real.exp (-2 * Real.pi * v)) v := by
      simpa [mul_comm] using ((hasDerivAt_id v).const_mul (-2 * Real.pi)).exp
    refine (hd1.mul hd2).congr_deriv ?_
    field_simp [Real.pi_ne_zero]; ring
  have hres := integral_Ioi_of_hasDerivAt_of_tendsto' h_d h_int h_lim
  dsimp only [G] at hres
  linarith

private lemma diffA_part3_small (θ Δ α c_sin y : ℝ) (hΔ : Δ ≥ 1) (hc_pos : 0 < c_sin)
    (hlb : c_sin * Real.exp (Real.pi * Δ) ≤ ‖Complex.sin (Real.pi * (Complex.I * Δ - α))‖) :
    |(Δ * Real.sin θ / (Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ - y))).re| ≤
      (1 / c_sin ^ 2) * Real.exp (-2 * Real.pi * Δ) := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by linarith : 0 < Δ), norm_pow]
  have hden : (c_sin * Real.exp (Real.pi * Δ)) ^ 2 ≤ ‖Complex.sin (Real.pi * (Complex.I * Δ - α))‖ ^ 2 :=
    sq_le_sq' (by linarith [mul_pos hc_pos (Real.exp_pos (Real.pi * Δ))]) hlb
  have h_iy : Δ ≤ ‖Complex.I * Δ - y‖ := by
    have hsq : Δ ^ 2 ≤ ‖Complex.I * Δ - y‖ ^ 2 := by
      rw [normSq_I_mul_sub]; exact le_add_of_nonneg_left (sq_nonneg y)
    exact (sq_le_sq₀ (by linarith) (norm_nonneg _)).mp hsq
  have hΔ0 : 0 ≤ Δ := zero_le_one.trans hΔ
  have hΔ_pos : 0 < Δ := zero_lt_one.trans_le hΔ
  calc Δ * |Real.sin θ| / (‖Complex.sin (Real.pi * (Complex.I * Δ - α))‖ ^ 2 * ‖Complex.I * Δ - y‖)
      ≤ Δ * 1 / ((c_sin * Real.exp (Real.pi * Δ)) ^ 2 * Δ) :=
        div_le_div₀ (mul_nonneg hΔ0 zero_le_one)
          (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one θ) hΔ0)
          (mul_pos (pow_pos (mul_pos hc_pos (Real.exp_pos _)) 2) hΔ_pos)
          (mul_le_mul hden h_iy hΔ0 (pow_nonneg (norm_nonneg _) 2))
    _ = (1 / c_sin ^ 2) * Real.exp (-2 * Real.pi * Δ) := by
        rw [mul_pow, ← Real.exp_nat_mul]; push_cast
        rw [show (2 : ℝ) * (Real.pi * Δ) = -(-2 * Real.pi * Δ) by ring, Real.exp_neg]
        field_simp [hΔ_pos.ne', hc_pos.ne']

private lemma diffA_part3_large (θ Δ α c_sin y : ℝ) (hΔ : Δ ≥ 1) (hy0 : 0 < |y|) (hc_pos : 0 < c_sin)
    (hlb : c_sin * Real.exp (Real.pi * Δ) ≤ ‖Complex.sin (Real.pi * (Complex.I * Δ - α))‖) :
    |(Δ * Real.sin θ / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ / ((y : ℂ) * (Complex.I * Δ - y)))).re| ≤
      (1 / c_sin ^ 2) * Δ ^ 2 * Real.exp (-2 * Real.pi * Δ) / y ^ 2 := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by linarith : 0 < Δ), norm_pow, norm_div, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < Δ), norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hden : (c_sin * Real.exp (Real.pi * Δ)) ^ 2 ≤ ‖Complex.sin (Real.pi * (Complex.I * Δ - α))‖ ^ 2 :=
    sq_le_sq' (by linarith [mul_pos hc_pos (Real.exp_pos (Real.pi * Δ))]) hlb
  have h_sq : |y| ^ 2 ≤ ‖Complex.I * (Δ : ℂ) - (y : ℂ)‖ ^ 2 := by
    rw [normSq_I_mul_sub, sq_abs]; exact le_add_of_nonneg_right (sq_nonneg Δ)
  have h_n : |y| ≤ ‖Complex.I * (Δ : ℂ) - (y : ℂ)‖ := by
    rw [← sq_le_sq₀ (abs_nonneg y) (norm_nonneg _)]; exact h_sq
  have h_y2 : y ^ 2 ≤ |y| * ‖Complex.I * Δ - y‖ := by rw [← sq_abs y, sq]; exact mul_le_mul_of_nonneg_left h_n (abs_nonneg y)
  have hΔ0 : 0 ≤ Δ := zero_le_one.trans hΔ
  have hy2_pos : 0 < y ^ 2 := by rw [← sq_abs y]; exact sq_pos_of_pos hy0
  have h_den_pos : 0 < (c_sin * Real.exp (Real.pi * Δ)) ^ 2 := pow_pos (mul_pos hc_pos (Real.exp_pos _)) 2
  have h_div1 : Δ * |Real.sin θ| / ‖Complex.sin (Real.pi * (Complex.I * Δ - α))‖ ^ 2 ≤
      Δ * 1 / (c_sin * Real.exp (Real.pi * Δ)) ^ 2 :=
    div_le_div₀ (mul_nonneg hΔ0 zero_le_one) (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one θ) hΔ0) h_den_pos hden
  have h_div2 : Δ / (|y| * ‖Complex.I * (Δ : ℂ) - (y : ℂ)‖) ≤ Δ / y ^ 2 :=
    div_le_div_of_nonneg_left hΔ0 hy2_pos h_y2
  calc Δ * |Real.sin θ| / ‖Complex.sin (Real.pi * (Complex.I * Δ - α))‖ ^ 2 * (Δ / (|y| * ‖Complex.I * (Δ : ℂ) - (y : ℂ)‖))
      ≤ Δ * 1 / (c_sin * Real.exp (Real.pi * Δ)) ^ 2 * (Δ / y ^ 2) :=
        mul_le_mul h_div1 h_div2 (div_nonneg hΔ0 (mul_nonneg (abs_nonneg y) (norm_nonneg _)))
          (div_nonneg (mul_nonneg hΔ0 zero_le_one) h_den_pos.le)
    _ = (1 / c_sin ^ 2) * Δ ^ 2 * Real.exp (-2 * Real.pi * Δ) / y ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul]; push_cast
        rw [show (2 : ℝ) * (Real.pi * Δ) = -(-2 * Real.pi * Δ) by ring, Real.exp_neg]
        field_simp [hc_pos.ne']

private noncomputable def diffA_C_err1 (θ : ℝ) : ℝ :=
  let α_star : ℝ := 1 / 2 - θ / Real.pi
  let δ_star : ℝ := min (α_star / 2) ((1 - α_star) / 2)
  let δ : ℝ := min (δ_star / 2) (1 / 2)
  let c_sin : ℝ := Real.sin (Real.pi * δ) / Real.exp Real.pi
  let C_diff : ℝ := 2 * Real.pi / c_sin ^ 4
  let C_tail : ℝ := 4 / Real.cos θ ^ 2
  C_diff * (2 + 1 / (2 * Real.pi)) + C_tail * (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2) + 1) + 1 / c_sin ^ 2 + 1

private lemma diffA_combine_small (C_diff C_tail c_sin Δ a_diff log_y A1 A2 A3 : ℝ)
    (hΔ : Δ ≥ 1) (hC_diff : 0 ≤ C_diff) (hC_tail : 0 ≤ C_tail) (hc_sin : 0 ≤ 1 / c_sin ^ 2)
    (h_log : 0 ≤ log_y) (h_a : 0 ≤ a_diff)
    (h1 : |A1| ≤ C_diff * a_diff * (2 + log_y))
    (h2 : |A2| ≤ C_tail * (1 / (2 * Real.pi)) * Real.exp (-2 * Real.pi * Δ))
    (h3 : |A3| ≤ (1 / c_sin ^ 2) * Real.exp (-2 * Real.pi * Δ)) :
    |A1 - A2 - A3| ≤
      (C_diff * (2 + 1 / (2 * Real.pi)) + C_tail * (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2) + 1) + 1 / c_sin ^ 2 + 1) *
        (Δ * Real.exp (-2 * Real.pi * Δ) + a_diff) * (1 + log_y) := by
  let C_err1 : ℝ := C_diff * (2 + 1 / (2 * Real.pi)) + C_tail * (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2) + 1) + 1 / c_sin ^ 2 + 1
  have h_1_le_log : 1 ≤ 1 + log_y := by linarith
  have h_2_le : 2 + log_y ≤ 2 * (1 + log_y) := by linarith
  have h_exp_le : Real.exp (-2 * Real.pi * Δ) ≤ Δ * Real.exp (-2 * Real.pi * Δ) :=
    le_mul_of_one_le_left (Real.exp_pos _).le hΔ
  have h_tri : |A1 - A2 - A3| ≤ |A1| + |A2| + |A3| :=
    (abs_sub (A1 - A2) A3).trans (add_le_add (abs_sub A1 A2) le_rfl)
  have h1' : C_diff * a_diff * (2 + log_y) ≤ C_diff * a_diff * (2 * (1 + log_y)) := by gcongr
  have h2' : C_tail * (1 / (2 * Real.pi)) * Real.exp (-2 * Real.pi * Δ) ≤
      C_tail * (1 / (2 * Real.pi)) * (Δ * Real.exp (-2 * Real.pi * Δ)) * (1 + log_y) := by
    calc C_tail * (1 / (2 * Real.pi)) * Real.exp (-2 * Real.pi * Δ)
        ≤ C_tail * (1 / (2 * Real.pi)) * (Δ * Real.exp (-2 * Real.pi * Δ)) := by gcongr
      _ = C_tail * (1 / (2 * Real.pi)) * (Δ * Real.exp (-2 * Real.pi * Δ)) * 1 := (mul_one _).symm
      _ ≤ _ := by gcongr
  have h3' : (1 / c_sin ^ 2) * Real.exp (-2 * Real.pi * Δ) ≤
      (1 / c_sin ^ 2) * (Δ * Real.exp (-2 * Real.pi * Δ)) * (1 + log_y) := by
    calc (1 / c_sin ^ 2) * Real.exp (-2 * Real.pi * Δ)
        ≤ (1 / c_sin ^ 2) * (Δ * Real.exp (-2 * Real.pi * Δ)) := by gcongr
      _ = (1 / c_sin ^ 2) * (Δ * Real.exp (-2 * Real.pi * Δ)) * 1 := (mul_one _).symm
      _ ≤ _ := by gcongr
  have h_c1 : 2 * C_diff ≤ C_err1 := by
    have h1 : 2 * C_diff ≤ C_diff * (2 + 1 / (2 * Real.pi)) := by
      rw [mul_add, mul_comm C_diff 2]
      exact le_add_of_nonneg_right (mul_nonneg hC_diff (div_nonneg zero_le_one (mul_pos two_pos Real.pi_pos).le))
    have h_t : 0 ≤ C_tail * (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2) + 1) + 1 / c_sin ^ 2 + 1 := by positivity
    dsimp only [C_err1]; linarith
  have h_c2 : C_tail * (1 / (2 * Real.pi)) + 1 / c_sin ^ 2 ≤ C_err1 := by
    dsimp only [C_err1]
    have : 0 ≤ C_diff * (2 + 1 / (2 * Real.pi)) := by positivity
    have : 0 ≤ C_tail * (1 / (4 * Real.pi ^ 2) + 1) := by positivity
    linarith
  have h_nonneg1 : 0 ≤ Δ * Real.exp (-2 * Real.pi * Δ) := by positivity
  calc |A1 - A2 - A3| ≤ |A1| + |A2| + |A3| := h_tri
    _ ≤ C_diff * a_diff * (2 * (1 + log_y)) +
        C_tail * (1 / (2 * Real.pi)) * (Δ * Real.exp (-2 * Real.pi * Δ)) * (1 + log_y) +
        (1 / c_sin ^ 2) * (Δ * Real.exp (-2 * Real.pi * Δ)) * (1 + log_y) :=
          add_le_add (add_le_add (h1.trans h1') (h2.trans h2')) (h3.trans h3')
    _ = (C_diff * a_diff * 2 +
          (C_tail * (1 / (2 * Real.pi)) * (Δ * Real.exp (-2 * Real.pi * Δ)) +
            (1 / c_sin ^ 2) * (Δ * Real.exp (-2 * Real.pi * Δ)))) * (1 + log_y) := by ring
    _ ≤ (C_err1 * a_diff + C_err1 * (Δ * Real.exp (-2 * Real.pi * Δ))) * (1 + log_y) := by
          have h_s1 : C_diff * a_diff * 2 ≤ C_err1 * a_diff := by
            rw [mul_right_comm, mul_comm C_diff 2]; exact mul_le_mul_of_nonneg_right h_c1 h_a
          have h_s2 : C_tail * (1 / (2 * Real.pi)) * (Δ * Real.exp (-2 * Real.pi * Δ)) +
              (1 / c_sin ^ 2) * (Δ * Real.exp (-2 * Real.pi * Δ)) ≤ C_err1 * (Δ * Real.exp (-2 * Real.pi * Δ)) := by
            rw [← add_mul]; exact mul_le_mul_of_nonneg_right h_c2 h_nonneg1
          exact mul_le_mul_of_nonneg_right (add_le_add h_s1 h_s2) (by linarith)
    _ = C_err1 * (Δ * Real.exp (-2 * Real.pi * Δ) + a_diff) * (1 + log_y) := by ring

private lemma diffA_combine_large (C_diff C_tail c_sin Δ a_diff y A1 A2 A3 : ℝ)
    (hΔ : Δ ≥ 1) (hC_diff : 0 ≤ C_diff) (hC_tail : 0 ≤ C_tail) (hc_sin : 0 ≤ 1 / c_sin ^ 2)
    (h_a : 0 ≤ a_diff)
    (h1 : |A1| ≤ C_diff * a_diff * (1 / (4 * Real.pi ^ 2)) / y ^ 2)
    (h2 : |A2| ≤ C_tail * (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2)) * Δ * Real.exp (-2 * Real.pi * Δ) / y ^ 2)
    (h3 : |A3| ≤ (1 / c_sin ^ 2) * Δ ^ 2 * Real.exp (-2 * Real.pi * Δ) / y ^ 2) :
    |A1 - A2 - A3| ≤
      (C_diff * (2 + 1 / (2 * Real.pi)) + C_tail * (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2) + 1) + 1 / c_sin ^ 2 + 1) *
        (Δ ^ 2 * Real.exp (-2 * Real.pi * Δ) + a_diff) / y ^ 2 := by
  let C_err1 : ℝ := C_diff * (2 + 1 / (2 * Real.pi)) + C_tail * (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2) + 1) + 1 / c_sin ^ 2 + 1
  have h_Δ_le : Δ * Real.exp (-2 * Real.pi * Δ) ≤ Δ ^ 2 * Real.exp (-2 * Real.pi * Δ) := by
    have : Δ ≤ Δ ^ 2 := by nlinarith
    gcongr
  have h_tri : |A1 - A2 - A3| ≤ |A1| + |A2| + |A3| :=
    (abs_sub (A1 - A2) A3).trans (add_le_add (abs_sub A1 A2) le_rfl)
  have h_c1 : C_diff * (1 / (4 * Real.pi ^ 2)) ≤ C_err1 := by
    have hpi2 : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
    have h_inv : 1 / (4 * Real.pi ^ 2) ≤ 1 := div_le_one_of_le₀ hpi2 (by positivity)
    have h_le1 : 1 / (4 * Real.pi ^ 2) ≤ 2 + 1 / (2 * Real.pi) :=
      h_inv.trans (le_add_of_le_of_nonneg (by norm_num) (div_nonneg zero_le_one (mul_pos two_pos Real.pi_pos).le))
    have h_le2 : C_diff * (1 / (4 * Real.pi ^ 2)) ≤ C_diff * (2 + 1 / (2 * Real.pi)) :=
      mul_le_mul_of_nonneg_left h_le1 hC_diff
    have h_tail_nn : 0 ≤ C_tail * (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2) + 1) + 1 / c_sin ^ 2 + 1 := by positivity
    dsimp only [C_err1]; linarith
  have h_c2 : C_tail * (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2)) + 1 / c_sin ^ 2 ≤ C_err1 := by
    have h_d_nn : 0 ≤ C_diff * (2 + 1 / (2 * Real.pi)) := by positivity
    have h_t_le : C_tail * (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2)) ≤ C_tail * (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2) + 1) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hC_tail
    dsimp only [C_err1]; linarith
  have h_le2 : C_tail * (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2)) * Δ * Real.exp (-2 * Real.pi * Δ) / y ^ 2 ≤
      C_tail * (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2)) * (Δ ^ 2 * Real.exp (-2 * Real.pi * Δ)) / y ^ 2 := by
    rw [mul_assoc (C_tail * (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2))) Δ (Real.exp (-2 * Real.pi * Δ))]
    gcongr
  have h_step1 : |A1 - A2 - A3| ≤
      C_diff * a_diff * (1 / (4 * Real.pi ^ 2)) / y ^ 2 +
      C_tail * (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2)) * (Δ ^ 2 * Real.exp (-2 * Real.pi * Δ)) / y ^ 2 +
      (1 / c_sin ^ 2) * Δ ^ 2 * Real.exp (-2 * Real.pi * Δ) / y ^ 2 :=
    h_tri.trans (add_le_add (add_le_add h1 (h2.trans h_le2)) h3)
  refine h_step1.trans ?_
  rw [← add_div, ← add_div]
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg y)
  have h_nonneg1 : 0 ≤ Δ ^ 2 * Real.exp (-2 * Real.pi * Δ) := by positivity
  have h_s1 : C_diff * a_diff * (1 / (4 * Real.pi ^ 2)) ≤ C_err1 * a_diff := by
    rw [mul_right_comm]; exact mul_le_mul_of_nonneg_right h_c1 h_a
  have h_s2 : C_tail * (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2)) * (Δ ^ 2 * Real.exp (-2 * Real.pi * Δ)) +
      (1 / c_sin ^ 2) * Δ ^ 2 * Real.exp (-2 * Real.pi * Δ) ≤ C_err1 * (Δ ^ 2 * Real.exp (-2 * Real.pi * Δ)) := by
    rw [mul_assoc (1 / c_sin ^ 2), ← add_mul]
    exact mul_le_mul_of_nonneg_right h_c2 h_nonneg1
  calc C_diff * a_diff * (1 / (4 * Real.pi ^ 2)) +
        C_tail * (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2)) * (Δ ^ 2 * Real.exp (-2 * Real.pi * Δ)) +
        (1 / c_sin ^ 2) * Δ ^ 2 * Real.exp (-2 * Real.pi * Δ)
      = C_diff * a_diff * (1 / (4 * Real.pi ^ 2)) +
          (C_tail * (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2)) * (Δ ^ 2 * Real.exp (-2 * Real.pi * Δ)) +
            (1 / c_sin ^ 2) * Δ ^ 2 * Real.exp (-2 * Real.pi * Δ)) := by ring
    _ ≤ C_err1 * a_diff + C_err1 * (Δ ^ 2 * Real.exp (-2 * Real.pi * Δ)) := add_le_add h_s1 h_s2
    _ = C_err1 * (Δ ^ 2 * Real.exp (-2 * Real.pi * Δ) + a_diff) := by ring

private lemma majorant_contour_diff_small (θ : ℝ) (hθ : |θ| < Real.pi / 2)
    (Δ α : ℝ) (hΔ : Δ ≥ 1) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hα_near : |α - (1 / 2 - θ / Real.pi)| ≤ (min ((1 / 2 - θ / Real.pi) / 2) ((1 - (1 / 2 - θ / Real.pi)) / 2)) / 2)
    (hsumm_b : Summable (fun n : ℤ => rescaledFDeriv θ Δ (n + α)))
    (hsum0 : ∑' n : ℤ, rescaledFDeriv θ Δ (n + α) = 0) :
    ∀ y : ℝ, 0 < |y| → |y| < 1 →
      |(vaalerInterpolant θ Δ α y - rescaledF θ Δ y) - Real.sin (Real.pi * (y - α)) ^ 2 * limitingJ y θ| ≤
        Real.sin (Real.pi * (y - α)) ^ 2 * (diffA_C_err1 θ * (Δ * Real.exp (-2 * Real.pi * Δ) + |α - (1 / 2 - θ / Real.pi)|) * (1 + Real.log (1 / |y|))) := by
  let α_star : ℝ := 1 / 2 - θ / Real.pi
  have hα_star : α_star ∈ Set.Ioo (0 : ℝ) 1 := by
    have := abs_lt.mp hθ
    constructor
    · dsimp only [α_star]; rw [sub_pos, div_lt_iff₀ Real.pi_pos]; linarith
    · dsimp only [α_star]; rw [sub_lt_iff_lt_add]; linarith [show -(1 / 2 : ℝ) < θ / Real.pi by rw [lt_div_iff₀ Real.pi_pos]; linarith]
  let δ_star : ℝ := min (α_star / 2) ((1 - α_star) / 2)
  let δ : ℝ := min (δ_star / 2) (1 / 2)
  have hδ0 : 0 < δ := lt_min (div_pos (lt_min (div_pos hα_star.1 (by norm_num)) (div_pos (sub_pos.mpr hα_star.2) (by norm_num))) (by norm_num)) (by norm_num)
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  have hα_star1 : δ ≤ α_star := by
    have : δ ≤ δ_star / 2 := min_le_left _ _
    have : δ_star ≤ α_star / 2 := min_le_left _ _
    linarith
  have hα_star2 : α_star ≤ 1 - δ := by
    have : δ ≤ δ_star / 2 := min_le_left _ _
    have : δ_star ≤ (1 - α_star) / 2 := min_le_right _ _
    linarith
  let c_sin : ℝ := Real.sin (Real.pi * δ) / Real.exp Real.pi
  have hsin_δ_pos : 0 < Real.sin (Real.pi * δ) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hc_pos : 0 < c_sin := div_pos hsin_δ_pos (Real.exp_pos _)
  let C_diff : ℝ := 2 * Real.pi / c_sin ^ 4
  let C_tail : ℝ := 4 / Real.cos θ ^ 2
  let C_err1 : ℝ := C_diff * (2 + 1 / (2 * Real.pi)) + C_tail * (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2) + 1) + 1 / c_sin ^ 2 + 1
  have hα1 : δ ≤ α := by
    have h1 := (abs_le.mp hα_near).1
    have h2 : δ ≤ δ_star / 2 := min_le_left _ _
    have h3 : δ_star ≤ α_star / 2 := min_le_left _ _
    dsimp only [δ_star, α_star] at h2 h3
    linarith
  have hα2 : α ≤ 1 - δ := by
    have h1 := (abs_le.mp hα_near).2
    have h2 : δ ≤ δ_star / 2 := min_le_left _ _
    have h3 : δ_star ≤ (1 - α_star) / 2 := min_le_right _ _
    dsimp only [δ_star, α_star] at h2 h3
    linarith
  have h_sin_star : ∀ v : ℝ, Complex.sin (Real.pi * (Complex.I * v - α_star)) ^ 2 =
      Complex.cos (θ + Complex.I * Real.pi * v) ^ 2 := by
    intro v
    have heq : (Real.pi : ℂ) * (Complex.I * v - α_star) = -(Real.pi / 2 - (θ + Complex.I * Real.pi * v)) := by
      dsimp only [α_star]; push_cast; field_simp [Real.pi_ne_zero]; ring
    rw [heq, Complex.sin_neg, neg_sq, Complex.sin_pi_div_two_sub]
  let Φ : ℝ → ℂ := fun v => Complex.exp (-Complex.I * θ) / Complex.sin (Real.pi * (Complex.I * v - α)) ^ 2
  let Φ_star : ℝ → ℂ := fun v => Complex.exp (-Complex.I * θ) / Complex.cos (θ + Complex.I * Real.pi * v) ^ 2
  have hΦ_diff : ∀ v : ℝ, 0 ≤ v → ‖Φ v - Φ_star v‖ ≤ C_diff * |α - α_star| * Real.exp (-2 * Real.pi * v) := by
    intro v hv
    dsimp only [Φ, Φ_star]
    rw [← h_sin_star v, ← mul_one_div (Complex.exp (-Complex.I * θ)), ← mul_one_div (Complex.exp (-Complex.I * θ)),
      ← mul_sub, norm_mul]
    have hexp : ‖Complex.exp (-Complex.I * θ)‖ = 1 := by
      rw [show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    rw [hexp, one_mul]
    exact sin_pi_iv_alpha_diff hδ0 hδ1 hα1 hα2 hα_star1 hα_star2 v hv
  have hΦ_star_bd : ∀ v : ℝ, 0 ≤ v → ‖Φ_star v‖ ≤ C_tail * Real.exp (-2 * Real.pi * v) :=
    fun v hv => cTheta_norm_le hθ hv
  have hc₀_zero := contour_c0_eq_zero θ Δ α hθ hΔ hα hsumm_b hsum0
  have hc_star_zero : ∫ v in Set.Ioi (0 : ℝ), (Φ_star v).im = 0 := cTheta_im_integral_zero hθ
  have hΦ_bd : ∀ v : ℝ, 0 ≤ v → ‖Φ v‖ ≤ 1 / c_sin ^ 2 * Real.exp (-2 * Real.pi * v) := by
    intro v hv
    dsimp only [Φ]
    have hexp : ‖Complex.exp (-Complex.I * θ)‖ = 1 := by
      rw [show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    rw [norm_div, hexp, norm_pow]
    have hlb := sin_pi_iv_beta_lb hδ0 hδ1 hα1 hα2 v hv
    have hden : (c_sin * Real.exp (Real.pi * v)) ^ 2 ≤ ‖Complex.sin (Real.pi * (Complex.I * v - α))‖ ^ 2 :=
      sq_le_sq' (by linarith [mul_pos hc_pos (Real.exp_pos (Real.pi * v))]) hlb
    calc 1 / ‖Complex.sin (Real.pi * (Complex.I * v - α))‖ ^ 2
        ≤ 1 / (c_sin * Real.exp (Real.pi * v)) ^ 2 := div_le_div_of_nonneg_left zero_le_one (by positivity) hden
      _ = 1 / c_sin ^ 2 * Real.exp (-2 * Real.pi * v) := by
          rw [mul_pow, ← Real.exp_nat_mul]; push_cast; rw [show (2 : ℝ) * (Real.pi * v) = -(-2 * Real.pi * v) by ring, Real.exp_neg]; field_simp
  have h_common_split : ∀ (y : ℝ) (hy_ne : y ≠ 0),
      ((∫ v in Set.Ioo (0 : ℝ) Δ, (Φ v / ((y : ℂ) - Complex.I * v)).im) -
        (Δ * Real.sin θ / (Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ - y))).re) -
        limitingJ y θ =
      (∫ v in Set.Ioo (0 : ℝ) Δ, ((Φ v - Φ_star v) / ((y : ℂ) - Complex.I * v)).im) -
        (∫ v in Set.Ioi Δ, (Φ_star v / ((y : ℂ) - Complex.I * v)).im) -
        (Δ * Real.sin θ / (Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ - y))).re := by
    intro y hy_ne
    have hy0 : 0 < |y| := abs_pos.mpr hy_ne
    have h_int_sub : IntegrableOn (fun v : ℝ => (Φ_star v / ((y : ℂ) - Complex.I * v)).im) (Set.Ioi 0) := by
      refine ((cTheta_integrableOn hθ).norm.div_const |y|).mono' ?_ ?_
      · refine Complex.continuous_im.comp_continuousOn ?_ |>.aestronglyMeasurable measurableSet_Ioi
        refine ContinuousOn.div ?_ (by fun_prop) (fun v _ h => ?_)
        · exact continuousOn_const.div (ContinuousOn.pow (Complex.continuous_cos.comp (by fun_prop)).continuousOn 2)
            (fun v _ => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ))
        · have hre := congr_arg Complex.re h; simp at hre; exact hy_ne hre
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
        rw [Real.norm_eq_abs]; refine (Complex.abs_im_le_norm _).trans ?_; rw [norm_div]
        have h_sq : |y| ^ 2 ≤ ‖(y : ℂ) - Complex.I * v‖ ^ 2 := by
          rw [normSq_sub_I_mul, sq_abs]; exact le_add_of_nonneg_right (sq_nonneg v)
        exact div_le_div_of_nonneg_left (norm_nonneg _) hy0 ((sq_le_sq₀ (abs_nonneg y) (norm_nonneg _)).mp h_sq)
    have h_split : limitingJ y θ =
        (∫ v in Set.Ioo (0 : ℝ) Δ, (Φ_star v / ((y : ℂ) - Complex.I * v)).im) +
        (∫ v in Set.Ioi Δ, (Φ_star v / ((y : ℂ) - Complex.I * v)).im) := by
      unfold limitingJ
      have h_eq_fn : (fun v : ℝ => (Complex.exp (-Complex.I * θ) / (Complex.cos (θ + Complex.I * Real.pi * v) ^ 2 * (y - Complex.I * v))).im) =
          (fun v : ℝ => (Φ_star v / ((y : ℂ) - Complex.I * v)).im) := by
        ext v; dsimp only [Φ_star]; rw [div_div]
      rw [h_eq_fn, ← integral_Ioc_eq_integral_Ioo, ← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (h_int_sub.mono_set Set.Ioc_subset_Ioi_self) (h_int_sub.mono_set (Set.Ioi_subset_Ioi (by linarith)))]
      rw [show Set.Ioc (0 : ℝ) Δ ∪ Set.Ioi Δ = Set.Ioi 0 by ext x; simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]; exact ⟨fun h => h.elim (fun a => a.1) (fun a => by linarith only [a, hΔ]), fun h => by rcases le_or_gt x Δ with h' | h'; exact Or.inl ⟨h, h'⟩; exact Or.inr h'⟩]
    have hΦy_int : IntegrableOn (fun v : ℝ => (Φ v / ((y : ℂ) - Complex.I * v)).im) (Set.Ioo 0 Δ) := by
      refine ((continuousOn_const : ContinuousOn (fun _ : ℝ => (1 / c_sin ^ 2) / |y|) (Set.Icc 0 Δ)).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self).mono' ?_ ?_
      · refine Complex.continuous_im.comp_continuousOn ?_ |>.aestronglyMeasurable measurableSet_Ioo
        refine ContinuousOn.div (continuousOn_const.div (ContinuousOn.pow (Complex.continuous_sin.continuousOn.comp (by fun_prop) (fun _ _ => Set.mem_univ _)) 2) ?_) (by fun_prop) ?_
        · intro v hv; have hlb := sin_pi_iv_beta_lb hδ0 hδ1 hα1 hα2 v hv.1.le
          exact pow_ne_zero 2 (norm_ne_zero_iff.mp (by linarith [mul_pos hc_pos (Real.exp_pos (Real.pi * v))]))
        · intro v _ h; have hre := congr_arg Complex.re h; simp at hre; exact hy_ne hre
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
        rw [Real.norm_eq_abs]; refine (Complex.abs_im_le_norm _).trans ?_; rw [norm_div]
        have hΦ_n : ‖Φ v‖ ≤ 1 / c_sin ^ 2 := (hΦ_bd v hv.1.le).trans
          (mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) hv.1.le)))
        have h_sq : |y| ^ 2 ≤ ‖(y : ℂ) - Complex.I * v‖ ^ 2 := by
          rw [normSq_sub_I_mul, sq_abs]; exact le_add_of_nonneg_right (sq_nonneg v)
        exact div_le_div₀ (by positivity) hΦ_n hy0 ((sq_le_sq₀ (abs_nonneg y) (norm_nonneg _)).mp h_sq)
    have h_sub_int : (∫ v in Set.Ioo (0 : ℝ) Δ, ((Φ v - Φ_star v) / ((y : ℂ) - Complex.I * v)).im) =
        (∫ v in Set.Ioo (0 : ℝ) Δ, (Φ v / ((y : ℂ) - Complex.I * v)).im) -
        (∫ v in Set.Ioo (0 : ℝ) Δ, (Φ_star v / ((y : ℂ) - Complex.I * v)).im) := by
      rw [← integral_sub hΦy_int (h_int_sub.mono_set Set.Ioo_subset_Ioi_self)]
      congr 1; ext v; rw [← Complex.sub_im, ← sub_div]
    rw [h_split, h_sub_int]; ring
  intro y hy0 hy1
  have hy_ne : y ≠ 0 := abs_pos.mp hy0
  have hcr := contour_representation θ Δ α hθ hΔ hα y hy_ne
  rw [hcr]
  have h_eq1 : (∫ v in Set.Ioo (0 : ℝ) Δ,
      (Complex.exp (-Complex.I * θ) / (Complex.sin (Real.pi * (Complex.I * v - α)) ^ 2 * (y - Complex.I * v))).im) =
      ∫ v in Set.Ioo (0 : ℝ) Δ, (Φ v / ((y : ℂ) - Complex.I * v)).im := by
    congr 1; ext v; dsimp only [Φ]; rw [div_div]
  rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
  gcongr
  rw [h_eq1, h_common_split y hy_ne]
  dsimp only [diffA_C_err1]
  have h_part1 : |∫ v in Set.Ioo (0 : ℝ) Δ, ((Φ v - Φ_star v) / ((y : ℂ) - Complex.I * v)).im| ≤
      C_diff * |α - α_star| * (2 + Real.log (1 / |y|)) := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    let g : ℝ → ℝ := fun v => C_diff * |α - α_star| * (Real.exp (-2 * Real.pi * v) / max |y| v)
    have hg_int1 : IntegrableOn g (Set.Ioo 0 |y|) := by
      refine ((continuousOn_const : ContinuousOn (fun _ : ℝ => C_diff * |α - α_star| / |y|) (Set.Icc 0 |y|)).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self).mono' ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
        dsimp only [g]
        refine ContinuousOn.mul continuousOn_const (ContinuousOn.div (by fun_prop) ?_ fun v _ => (lt_max_of_lt_left hy0).ne')
        exact Continuous.continuousOn (continuous_const.max continuous_id)
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
        dsimp only [g]
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have h_m : max |y| v = |y| := max_eq_left hv.2.le
        rw [h_m]
        have he : Real.exp (-2 * Real.pi * v) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) hv.1.le)
        calc C_diff * |α - α_star| * (Real.exp (-2 * Real.pi * v) / |y|)
            ≤ C_diff * |α - α_star| * (1 / |y|) := by gcongr
          _ = C_diff * |α - α_star| / |y| := by ring
    have hg_int2 : IntegrableOn g (Set.Ioo |y| 1) := by
      refine ((continuousOn_const : ContinuousOn (fun _ : ℝ => C_diff * |α - α_star| / |y|) (Set.Icc |y| 1)).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self).mono' ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
        dsimp only [g]
        refine ContinuousOn.mul continuousOn_const (ContinuousOn.div (by fun_prop) (Continuous.continuousOn (continuous_const.max continuous_id))
          fun v _ => (lt_max_of_lt_left hy0).ne')
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
        dsimp only [g]
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have h_m : max |y| v = v := max_eq_right hv.1.le
        rw [h_m]
        have he : Real.exp (-2 * Real.pi * v) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) (by linarith [hv.1, hy0]))
        calc C_diff * |α - α_star| * (Real.exp (-2 * Real.pi * v) / v)
            ≤ C_diff * |α - α_star| * (1 / |y|) := by
              gcongr; exact hv.1.le
          _ = C_diff * |α - α_star| / |y| := by ring
    have hg_int3 : IntegrableOn g (Set.Ioo 1 Δ) := by
      refine ((continuousOn_const : ContinuousOn (fun _ : ℝ => C_diff * |α - α_star|) (Set.Icc 1 Δ)).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self).mono' ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
        dsimp only [g]
        refine ContinuousOn.mul continuousOn_const (ContinuousOn.div (by fun_prop) (Continuous.continuousOn (continuous_const.max continuous_id))
          fun v _ => (lt_max_of_lt_left hy0).ne')
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
        dsimp only [g]
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have h_m : 1 ≤ max |y| v := le_trans hv.1.le (le_max_right _ _)
        have hv0 : 0 ≤ v := by linarith [hv.1]
        have he : Real.exp (-2 * Real.pi * v) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) hv0)
        calc C_diff * |α - α_star| * (Real.exp (-2 * Real.pi * v) / max |y| v)
            ≤ C_diff * |α - α_star| * (1 / 1) := by gcongr
          _ = C_diff * |α - α_star| := by ring
    have hg_int : IntegrableOn g (Set.Ioo 0 Δ) := by
      have h_u : Set.Ioo 0 |y| ∪ Set.Ioo |y| 1 ∪ Set.Ioo 1 Δ =ᵐ[volume] Set.Ioo (0 : ℝ) Δ := by
        change ∀ᵐ v ∂volume, (v ∈ Set.Ioo 0 |y| ∪ Set.Ioo |y| 1 ∪ Set.Ioo 1 Δ) = (v ∈ Set.Ioo (0 : ℝ) Δ)
        rw [ae_iff]
        have h_null : volume ({|y|, (1 : ℝ)} : Set ℝ) = 0 :=
          Set.Finite.measure_zero (by simp : ({|y|, (1 : ℝ)} : Set ℝ).Finite) volume
        refine measure_mono_null (fun v hv => ?_) h_null
        simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
        by_contra hne
        push Not at hne
        apply hv; apply propext; simp only [Set.mem_Ioo, Set.mem_union]
        rcases lt_or_gt_of_ne hne.1 with h1 | h1 <;> rcases lt_or_gt_of_ne hne.2 with h2 | h2
        · exact ⟨fun a => a.elim (fun b => b.elim (fun c => ⟨c.1, by linarith only [c.2, hy1, hΔ]⟩) (fun c => by linarith only [c.1, h1])) (fun b => by linarith only [b.1, h2]), fun a => Or.inl (Or.inl ⟨a.1, h1⟩)⟩
        · exact ⟨fun a => a.elim (fun b => b.elim (fun c => ⟨c.1, by linarith only [c.2, hy1, hΔ]⟩) (fun c => by linarith only [c.1, h1])) (fun b => by linarith only [h1, h2, hy1]), fun a => Or.inl (Or.inl ⟨a.1, h1⟩)⟩
        · exact ⟨fun a => a.elim (fun b => b.elim (fun c => ⟨c.1, by linarith only [c.2, hy1, hΔ]⟩) (fun c => ⟨by linarith only [c.1, hy0], by linarith only [c.2, hΔ]⟩)) (fun b => by linarith only [b.1, h2]), fun a => Or.inl (Or.inr ⟨h1, h2⟩)⟩
        · exact ⟨fun a => a.elim (fun b => b.elim (fun c => ⟨c.1, by linarith only [c.2, hy1, hΔ]⟩) (fun c => ⟨by linarith only [c.1, hy0], by linarith only [c.2, hΔ]⟩)) (fun b => ⟨by linarith only [b.1], b.2⟩), fun a => Or.inr ⟨h2, a.2⟩⟩
      exact ((hg_int1.union hg_int2).union hg_int3).congr_set_ae h_u.symm
    have hf_le_g : ∀ v ∈ Set.Ioo (0 : ℝ) Δ, ‖((Φ v - Φ_star v) / ((y : ℂ) - Complex.I * v)).im‖ ≤ g v := by
      intro v hv
      rw [Real.norm_eq_abs]
      refine (Complex.abs_im_le_norm _).trans ?_
      rw [norm_div]
      have h_n : max |y| v ≤ ‖(y : ℂ) - Complex.I * v‖ := by
        have hsq : (max |y| v) ^ 2 ≤ ‖(y : ℂ) - Complex.I * v‖ ^ 2 := by
          rw [normSq_sub_I_mul]
          rcases max_choice |y| v with h | h <;> rw [h]
          · rw [sq_abs]; exact le_add_of_nonneg_right (sq_nonneg v)
          · exact le_add_of_nonneg_left (sq_nonneg y)
        exact (sq_le_sq₀ (le_max_of_le_left (abs_nonneg y)) (norm_nonneg _)).mp hsq
      calc ‖Φ v - Φ_star v‖ / ‖(y : ℂ) - Complex.I * v‖
          ≤ (C_diff * |α - α_star| * Real.exp (-2 * Real.pi * v)) / max |y| v :=
            div_le_div₀ (by positivity) (hΦ_diff v hv.1.le) (lt_max_of_lt_left hy0) h_n
        _ = g v := by dsimp only [g]; ring
    have h_mono : ∫ v in Set.Ioo (0 : ℝ) Δ, ‖((Φ v - Φ_star v) / ((y : ℂ) - Complex.I * v)).im‖ ≤
        ∫ v in Set.Ioo (0 : ℝ) Δ, g v := by
      refine setIntegral_mono_on ?_ hg_int measurableSet_Ioo hf_le_g
      refine hg_int.mono' ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
        refine ContinuousOn.norm (Complex.continuous_im.comp_continuousOn ?_)
        refine ContinuousOn.div (ContinuousOn.sub ?_ ?_) (by fun_prop) (fun v _ h => ?_)
        · refine continuousOn_const.div (ContinuousOn.pow (Complex.continuous_sin.continuousOn.comp (by fun_prop) (fun _ _ => Set.mem_univ _)) 2) ?_
          intro v hv; have hlb := sin_pi_iv_beta_lb hδ0 hδ1 hα1 hα2 v hv.1.le
          exact pow_ne_zero 2 (norm_ne_zero_iff.mp (by linarith [mul_pos hc_pos (Real.exp_pos (Real.pi * v))]))
        · exact continuousOn_const.div (ContinuousOn.pow (Complex.continuous_cos.comp (by fun_prop)).continuousOn 2)
            (fun v _ => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ))
        · have hre := congr_arg Complex.re h; simp at hre; exact hy_ne hre
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
        rw [Real.norm_eq_abs, abs_norm]
        exact hf_le_g v hv
    have h_g_split : ∫ v in Set.Ioo (0 : ℝ) Δ, g v =
        (∫ v in Set.Ioo 0 |y|, g v) + (∫ v in Set.Ioo |y| 1, g v) + (∫ v in Set.Ioo 1 Δ, g v) := by
      have h_eq12 : Set.Ioo (0 : ℝ) 1 =ᵐ[volume] Set.Ioo 0 |y| ∪ Set.Ioo |y| 1 := by
        change ∀ᵐ v ∂volume, (v ∈ Set.Ioo (0 : ℝ) 1) = (v ∈ Set.Ioo 0 |y| ∪ Set.Ioo |y| 1)
        rw [ae_iff]
        refine measure_mono_null (fun v hv => ?_) (measure_singleton |y|)
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        by_contra hne
        apply hv; apply propext; simp only [Set.mem_Ioo, Set.mem_union]
        rcases lt_or_gt_of_ne hne with h | h
        · exact ⟨fun a => Or.inl ⟨a.1, h⟩, fun a => a.elim (fun b => ⟨b.1, by linarith only [b.2, hy1]⟩) (fun b => by linarith only [b.1, h])⟩
        · exact ⟨fun a => Or.inr ⟨h, a.2⟩, fun a => a.elim (fun b => by linarith only [b.2, h]) (fun b => ⟨by linarith only [b.1, hy0], b.2⟩)⟩
      have h_eq123 : Set.Ioo (0 : ℝ) Δ =ᵐ[volume] Set.Ioo 0 1 ∪ Set.Ioo 1 Δ := by
        change ∀ᵐ v ∂volume, (v ∈ Set.Ioo (0 : ℝ) Δ) = (v ∈ Set.Ioo 0 1 ∪ Set.Ioo 1 Δ)
        rw [ae_iff]
        refine measure_mono_null (fun v hv => ?_) (measure_singleton (1 : ℝ))
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        by_contra hne
        apply hv; apply propext; simp only [Set.mem_Ioo, Set.mem_union]
        rcases lt_or_gt_of_ne hne with h | h
        · exact ⟨fun a => Or.inl ⟨a.1, h⟩, fun a => a.elim (fun b => ⟨b.1, by linarith only [b.2, hΔ]⟩) (fun b => by linarith only [b.1, h])⟩
        · exact ⟨fun a => Or.inr ⟨h, a.2⟩, fun a => a.elim (fun b => by linarith only [b.2, h]) (fun b => ⟨by linarith only [b.1], b.2⟩)⟩
      rw [setIntegral_congr_set h_eq123, setIntegral_union (Set.disjoint_iff.mpr fun x ⟨hx1, hx2⟩ => by linarith only [hx1.2, hx2.1]) measurableSet_Ioo
        (hg_int.mono_set (Set.Ioo_subset_Ioo_right hΔ)) hg_int3,
        setIntegral_congr_set h_eq12, setIntegral_union (Set.disjoint_iff.mpr fun x ⟨hx1, hx2⟩ => by linarith only [hx1.2, hx2.1]) measurableSet_Ioo
        hg_int1 hg_int2]
    have h_g1 : ∫ v in Set.Ioo 0 |y|, g v ≤ C_diff * |α - α_star| := by
      have h_c : ∫ _ in Set.Ioo (0 : ℝ) |y|, C_diff * |α - α_star| / |y| = C_diff * |α - α_star| := by
        rw [setIntegral_const, Real.volume_real_Ioo_of_le hy0.le, sub_zero, smul_eq_mul]
        field_simp [hy0.ne']
      rw [← h_c]
      refine setIntegral_mono_on hg_int1 (continuousOn_const.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self) measurableSet_Ioo fun v hv => ?_
      dsimp only [g]; rw [max_eq_left hv.2.le]
      have he : Real.exp (-2 * Real.pi * v) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) hv.1.le)
      calc C_diff * |α - α_star| * (Real.exp (-2 * Real.pi * v) / |y|)
          ≤ C_diff * |α - α_star| * (1 / |y|) := by gcongr
        _ = C_diff * |α - α_star| / |y| := by ring
    have h_g2 : ∫ v in Set.Ioo |y| 1, g v ≤ C_diff * |α - α_star| * Real.log (1 / |y|) := by
      have h_inv_int : IntegrableOn (fun v : ℝ => C_diff * |α - α_star| * (1 / v)) (Set.Ioo |y| 1) := by
        refine ((continuousOn_const : ContinuousOn (fun _ : ℝ => C_diff * |α - α_star| / |y|) (Set.Icc |y| 1)).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self).mono'
          (by fun_prop) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
        have hv0 : 0 ≤ v := by linarith [hv.1, hy0]
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (one_div_nonneg.mpr hv0))]
        calc C_diff * |α - α_star| * (1 / v) ≤ C_diff * |α - α_star| * (1 / |y|) := by gcongr; exact hv.1.le
          _ = C_diff * |α - α_star| / |y| := by ring
      have h_eq_log : ∫ v in Set.Ioo |y| 1, C_diff * |α - α_star| * (1 / v) = C_diff * |α - α_star| * Real.log (1 / |y|) := by
        rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hy1.le]
        simp_rw [one_div]
        rw [integral_inv (fun h => by rcases Set.mem_uIcc.mp h with h1 | h1 <;> linarith [h1.1, h1.2]), one_div]
      rw [← h_eq_log]
      refine setIntegral_mono_on hg_int2 h_inv_int measurableSet_Ioo fun v hv => ?_
      dsimp only [g]; rw [max_eq_right hv.1.le]
      have hv0 : 0 ≤ v := by linarith [hv.1, hy0]
      have he : Real.exp (-2 * Real.pi * v) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) hv0)
      gcongr
    have h_g3 : ∫ v in Set.Ioo 1 Δ, g v ≤ C_diff * |α - α_star| * (1 / (2 * Real.pi)) := by
      have h_e_int : IntegrableOn (fun v : ℝ => C_diff * |α - α_star| * Real.exp (-2 * Real.pi * v)) (Set.Ioi 1) := by
        have hc : IntegrableOn (fun v : ℝ => Complex.exp ((-2 * Real.pi : ℂ) * v)) (Set.Ioi 1) :=
          integrableOn_exp_mul_complex_Ioi (by simp; positivity) 1
        have hr : IntegrableOn (fun v : ℝ => Real.exp (-2 * Real.pi * v)) (Set.Ioi 1) := by
          refine hc.norm.congr (Eventually.of_forall fun v => ?_)
          dsimp only
          rw [show (-2 * (Real.pi : ℂ) * v) = ((-2 * Real.pi * v : ℝ) : ℂ) by push_cast; ring,
            ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact hr.const_mul _
      have h_mono1 : ∫ v in Set.Ioo 1 Δ, g v ≤ ∫ v in Set.Ioo 1 Δ, C_diff * |α - α_star| * Real.exp (-2 * Real.pi * v) := by
        refine setIntegral_mono_on hg_int3 (h_e_int.mono_set Set.Ioo_subset_Ioi_self) measurableSet_Ioo fun v hv => ?_
        dsimp only [g]
        have h_m : 1 ≤ max |y| v := le_trans hv.1.le (le_max_right _ _)
        have : Real.exp (-2 * Real.pi * v) / max |y| v ≤ Real.exp (-2 * Real.pi * v) :=
          div_le_self (Real.exp_pos _).le h_m
        exact mul_le_mul_of_nonneg_left this (by positivity)
      have h_mono2 : ∫ v in Set.Ioo 1 Δ, C_diff * |α - α_star| * Real.exp (-2 * Real.pi * v) ≤
          ∫ v in Set.Ioi 1, C_diff * |α - α_star| * Real.exp (-2 * Real.pi * v) := by
        refine setIntegral_mono_set h_e_int ?_ Set.Ioo_subset_Ioi_self.eventuallyLE
        filter_upwards with v; positivity
      have h_val : ∫ v in Set.Ioi 1, C_diff * |α - α_star| * Real.exp (-2 * Real.pi * v) ≤
          C_diff * |α - α_star| * (1 / (2 * Real.pi)) := by
        rw [integral_const_mul, int_exp_neg_two_pi_Ioi 1 zero_le_one]
        gcongr
        exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos]))
      linarith
    calc ∫ v in Set.Ioo (0 : ℝ) Δ, ‖((Φ v - Φ_star v) / ((y : ℂ) - Complex.I * v)).im‖
        ≤ ∫ v in Set.Ioo (0 : ℝ) Δ, g v := h_mono
      _ = (∫ v in Set.Ioo 0 |y|, g v) + (∫ v in Set.Ioo |y| 1, g v) + (∫ v in Set.Ioo 1 Δ, g v) := h_g_split
      _ ≤ C_diff * |α - α_star| + C_diff * |α - α_star| * Real.log (1 / |y|) +
            C_diff * |α - α_star| * (1 / (2 * Real.pi)) := by linarith
      _ ≤ C_diff * |α - α_star| * (2 + Real.log (1 / |y|)) := by
          have h1 : 1 / (2 * Real.pi) ≤ 1 := div_le_one_of_le₀ (by linarith [Real.two_le_pi]) (by positivity)
          nlinarith [show 0 ≤ C_diff * |α - α_star| by positivity]
  have h_part2 : |∫ v in Set.Ioi Δ, (Φ_star v / ((y : ℂ) - Complex.I * v)).im| ≤
      C_tail * (1 / (2 * Real.pi)) * Real.exp (-2 * Real.pi * Δ) := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    have h_e_int : IntegrableOn (fun v : ℝ => C_tail * Real.exp (-2 * Real.pi * v)) (Set.Ioi Δ) := by
      have hc : IntegrableOn (fun v : ℝ => Complex.exp ((-2 * Real.pi : ℂ) * v)) (Set.Ioi Δ) :=
        integrableOn_exp_mul_complex_Ioi (by simp; positivity) Δ
      have hr : IntegrableOn (fun v : ℝ => Real.exp (-2 * Real.pi * v)) (Set.Ioi Δ) := by
        refine hc.norm.congr (Eventually.of_forall fun v => ?_)
        dsimp only
        rw [show (-2 * (Real.pi : ℂ) * v) = ((-2 * Real.pi * v : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hr.const_mul _
    have h_mono : ∫ v in Set.Ioi Δ, ‖(Φ_star v / ((y : ℂ) - Complex.I * v)).im‖ ≤
        ∫ v in Set.Ioi Δ, C_tail * Real.exp (-2 * Real.pi * v) := by
      refine setIntegral_mono_on ?_ h_e_int measurableSet_Ioi fun v hv => ?_
      · refine h_e_int.mono' ?_ ?_
        · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
          refine ContinuousOn.norm (Complex.continuous_im.comp_continuousOn ?_)
          refine ContinuousOn.div (continuousOn_const.div (ContinuousOn.pow (Complex.continuous_cos.comp (by fun_prop)).continuousOn 2)
            (fun v _ => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ))) (by fun_prop) (fun v _ h => ?_)
          have hre := congr_arg Complex.re h; simp at hre; exact hy_ne hre
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
          rw [Real.norm_eq_abs, abs_norm, Real.norm_eq_abs]
          refine (Complex.abs_im_le_norm _).trans ?_; rw [norm_div]
          have hv1 : 1 ≤ ‖(y : ℂ) - Complex.I * v‖ := by
            have hsq : 1 ^ 2 ≤ ‖(y : ℂ) - Complex.I * v‖ ^ 2 := by
              rw [normSq_sub_I_mul]
              have : 1 ≤ v := by linarith [hv.out]
              exact le_add_of_nonneg_of_le (sq_nonneg y) (by simpa using one_le_pow₀ this (n := 2))
            exact (sq_le_sq₀ zero_le_one (norm_nonneg _)).mp hsq
          exact (div_le_self (norm_nonneg _) hv1).trans (hΦ_star_bd v (by linarith [hv.out]))
      · rw [Real.norm_eq_abs]
        refine (Complex.abs_im_le_norm _).trans ?_; rw [norm_div]
        have hv1 : 1 ≤ ‖(y : ℂ) - Complex.I * v‖ := by
          have hsq : 1 ^ 2 ≤ ‖(y : ℂ) - Complex.I * v‖ ^ 2 := by
            rw [normSq_sub_I_mul]
            have : 1 ≤ v := by linarith [hv.out]
            exact le_add_of_nonneg_of_le (sq_nonneg y) (by simpa using one_le_pow₀ this (n := 2))
          exact (sq_le_sq₀ zero_le_one (norm_nonneg _)).mp hsq
        exact (div_le_self (norm_nonneg _) hv1).trans (hΦ_star_bd v (by linarith [hv.out]))
    rw [integral_const_mul, int_exp_neg_two_pi_Ioi Δ (by linarith)] at h_mono
    linarith [h_mono]
  have h_part3 := diffA_part3_small θ Δ α c_sin y hΔ hc_pos (sin_pi_iv_beta_lb hδ0 hδ1 hα1 hα2 Δ (by linarith))
  exact diffA_combine_small C_diff C_tail c_sin Δ |α - α_star| (Real.log (1 / |y|)) _ _ _
    hΔ (div_nonneg (mul_pos two_pos Real.pi_pos).le (pow_nonneg hc_pos.le 4))
    (div_nonneg (by norm_num) (sq_nonneg _)) (div_nonneg zero_le_one (sq_nonneg _))
    (Real.log_nonneg ((one_le_div hy0).mpr hy1.le)) (abs_nonneg _) h_part1 h_part2 h_part3

private lemma majorant_contour_diff_large (θ : ℝ) (hθ : |θ| < Real.pi / 2)
    (Δ α : ℝ) (hΔ : Δ ≥ 1) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hα_near : |α - (1 / 2 - θ / Real.pi)| ≤ (min ((1 / 2 - θ / Real.pi) / 2) ((1 - (1 / 2 - θ / Real.pi)) / 2)) / 2)
    (hsumm_b : Summable (fun n : ℤ => rescaledFDeriv θ Δ (n + α)))
    (hsum0 : ∑' n : ℤ, rescaledFDeriv θ Δ (n + α) = 0) :
    ∀ y : ℝ, 1 ≤ |y| →
      |(vaalerInterpolant θ Δ α y - rescaledF θ Δ y) - Real.sin (Real.pi * (y - α)) ^ 2 * limitingJ y θ| ≤
        Real.sin (Real.pi * (y - α)) ^ 2 * (diffA_C_err1 θ * (Δ ^ 2 * Real.exp (-2 * Real.pi * Δ) + |α - (1 / 2 - θ / Real.pi)|) / y ^ 2) := by
  let α_star : ℝ := 1 / 2 - θ / Real.pi
  have hα_star : α_star ∈ Set.Ioo (0 : ℝ) 1 := by
    have := abs_lt.mp hθ
    constructor
    · dsimp only [α_star]; rw [sub_pos, div_lt_iff₀ Real.pi_pos]; linarith
    · dsimp only [α_star]; rw [sub_lt_iff_lt_add]; linarith [show -(1 / 2 : ℝ) < θ / Real.pi by rw [lt_div_iff₀ Real.pi_pos]; linarith]
  let δ_star : ℝ := min (α_star / 2) ((1 - α_star) / 2)
  let δ : ℝ := min (δ_star / 2) (1 / 2)
  have hδ0 : 0 < δ := lt_min (div_pos (lt_min (div_pos hα_star.1 (by norm_num)) (div_pos (sub_pos.mpr hα_star.2) (by norm_num))) (by norm_num)) (by norm_num)
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  have hα_star1 : δ ≤ α_star := by
    have : δ ≤ δ_star / 2 := min_le_left _ _
    have : δ_star ≤ α_star / 2 := min_le_left _ _
    linarith
  have hα_star2 : α_star ≤ 1 - δ := by
    have : δ ≤ δ_star / 2 := min_le_left _ _
    have : δ_star ≤ (1 - α_star) / 2 := min_le_right _ _
    linarith
  let c_sin : ℝ := Real.sin (Real.pi * δ) / Real.exp Real.pi
  have hsin_δ_pos : 0 < Real.sin (Real.pi * δ) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hc_pos : 0 < c_sin := div_pos hsin_δ_pos (Real.exp_pos _)
  let C_diff : ℝ := 2 * Real.pi / c_sin ^ 4
  let C_tail : ℝ := 4 / Real.cos θ ^ 2
  let C_err1 : ℝ := C_diff * (2 + 1 / (2 * Real.pi)) + C_tail * (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2) + 1) + 1 / c_sin ^ 2 + 1
  have hα1 : δ ≤ α := by
    have h1 := (abs_le.mp hα_near).1
    have h2 : δ ≤ δ_star / 2 := min_le_left _ _
    have h3 : δ_star ≤ α_star / 2 := min_le_left _ _
    dsimp only [δ_star, α_star] at h2 h3
    linarith
  have hα2 : α ≤ 1 - δ := by
    have h1 := (abs_le.mp hα_near).2
    have h2 : δ ≤ δ_star / 2 := min_le_left _ _
    have h3 : δ_star ≤ (1 - α_star) / 2 := min_le_right _ _
    dsimp only [δ_star, α_star] at h2 h3
    linarith
  have h_sin_star : ∀ v : ℝ, Complex.sin (Real.pi * (Complex.I * v - α_star)) ^ 2 =
      Complex.cos (θ + Complex.I * Real.pi * v) ^ 2 := by
    intro v
    have heq : (Real.pi : ℂ) * (Complex.I * v - α_star) = -(Real.pi / 2 - (θ + Complex.I * Real.pi * v)) := by
      dsimp only [α_star]; push_cast; field_simp [Real.pi_ne_zero]; ring
    rw [heq, Complex.sin_neg, neg_sq, Complex.sin_pi_div_two_sub]
  let Φ : ℝ → ℂ := fun v => Complex.exp (-Complex.I * θ) / Complex.sin (Real.pi * (Complex.I * v - α)) ^ 2
  let Φ_star : ℝ → ℂ := fun v => Complex.exp (-Complex.I * θ) / Complex.cos (θ + Complex.I * Real.pi * v) ^ 2
  have hΦ_diff : ∀ v : ℝ, 0 ≤ v → ‖Φ v - Φ_star v‖ ≤ C_diff * |α - α_star| * Real.exp (-2 * Real.pi * v) := by
    intro v hv
    dsimp only [Φ, Φ_star]
    rw [← h_sin_star v, ← mul_one_div (Complex.exp (-Complex.I * θ)), ← mul_one_div (Complex.exp (-Complex.I * θ)),
      ← mul_sub, norm_mul]
    have hexp : ‖Complex.exp (-Complex.I * θ)‖ = 1 := by
      rw [show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    rw [hexp, one_mul]
    exact sin_pi_iv_alpha_diff hδ0 hδ1 hα1 hα2 hα_star1 hα_star2 v hv
  have hΦ_star_bd : ∀ v : ℝ, 0 ≤ v → ‖Φ_star v‖ ≤ C_tail * Real.exp (-2 * Real.pi * v) :=
    fun v hv => cTheta_norm_le hθ hv
  have hc₀_zero := contour_c0_eq_zero θ Δ α hθ hΔ hα hsumm_b hsum0
  have hc_star_zero : ∫ v in Set.Ioi (0 : ℝ), (Φ_star v).im = 0 := cTheta_im_integral_zero hθ
  have hΦ_bd : ∀ v : ℝ, 0 ≤ v → ‖Φ v‖ ≤ 1 / c_sin ^ 2 * Real.exp (-2 * Real.pi * v) := by
    intro v hv
    dsimp only [Φ]
    have hexp : ‖Complex.exp (-Complex.I * θ)‖ = 1 := by
      rw [show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    rw [norm_div, hexp, norm_pow]
    have hlb := sin_pi_iv_beta_lb hδ0 hδ1 hα1 hα2 v hv
    have hden : (c_sin * Real.exp (Real.pi * v)) ^ 2 ≤ ‖Complex.sin (Real.pi * (Complex.I * v - α))‖ ^ 2 :=
      sq_le_sq' (by linarith [mul_pos hc_pos (Real.exp_pos (Real.pi * v))]) hlb
    calc 1 / ‖Complex.sin (Real.pi * (Complex.I * v - α))‖ ^ 2
        ≤ 1 / (c_sin * Real.exp (Real.pi * v)) ^ 2 := div_le_div_of_nonneg_left zero_le_one (by positivity) hden
      _ = 1 / c_sin ^ 2 * Real.exp (-2 * Real.pi * v) := by
          rw [mul_pow, ← Real.exp_nat_mul]; push_cast; rw [show (2 : ℝ) * (Real.pi * v) = -(-2 * Real.pi * v) by ring, Real.exp_neg]; field_simp
  have h_common_split : ∀ (y : ℝ) (hy_ne : y ≠ 0),
      ((∫ v in Set.Ioo (0 : ℝ) Δ, (Φ v / ((y : ℂ) - Complex.I * v)).im) -
        (Δ * Real.sin θ / (Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ - y))).re) -
        limitingJ y θ =
      (∫ v in Set.Ioo (0 : ℝ) Δ, ((Φ v - Φ_star v) / ((y : ℂ) - Complex.I * v)).im) -
        (∫ v in Set.Ioi Δ, (Φ_star v / ((y : ℂ) - Complex.I * v)).im) -
        (Δ * Real.sin θ / (Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ - y))).re := by
    intro y hy_ne
    have hy0 : 0 < |y| := abs_pos.mpr hy_ne
    have h_int_sub : IntegrableOn (fun v : ℝ => (Φ_star v / ((y : ℂ) - Complex.I * v)).im) (Set.Ioi 0) := by
      refine ((cTheta_integrableOn hθ).norm.div_const |y|).mono' ?_ ?_
      · refine Complex.continuous_im.comp_continuousOn ?_ |>.aestronglyMeasurable measurableSet_Ioi
        refine ContinuousOn.div ?_ (by fun_prop) (fun v _ h => ?_)
        · exact continuousOn_const.div (ContinuousOn.pow (Complex.continuous_cos.comp (by fun_prop)).continuousOn 2)
            (fun v _ => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ))
        · have hre := congr_arg Complex.re h; simp at hre; exact hy_ne hre
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
        rw [Real.norm_eq_abs]; refine (Complex.abs_im_le_norm _).trans ?_; rw [norm_div]
        have h_sq : |y| ^ 2 ≤ ‖(y : ℂ) - Complex.I * v‖ ^ 2 := by
          rw [normSq_sub_I_mul, sq_abs]; exact le_add_of_nonneg_right (sq_nonneg v)
        exact div_le_div_of_nonneg_left (norm_nonneg _) hy0 ((sq_le_sq₀ (abs_nonneg y) (norm_nonneg _)).mp h_sq)
    have h_split : limitingJ y θ =
        (∫ v in Set.Ioo (0 : ℝ) Δ, (Φ_star v / ((y : ℂ) - Complex.I * v)).im) +
        (∫ v in Set.Ioi Δ, (Φ_star v / ((y : ℂ) - Complex.I * v)).im) := by
      unfold limitingJ
      have h_eq_fn : (fun v : ℝ => (Complex.exp (-Complex.I * θ) / (Complex.cos (θ + Complex.I * Real.pi * v) ^ 2 * (y - Complex.I * v))).im) =
          (fun v : ℝ => (Φ_star v / ((y : ℂ) - Complex.I * v)).im) := by
        ext v; dsimp only [Φ_star]; rw [div_div]
      rw [h_eq_fn, ← integral_Ioc_eq_integral_Ioo, ← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (h_int_sub.mono_set Set.Ioc_subset_Ioi_self) (h_int_sub.mono_set (Set.Ioi_subset_Ioi (by linarith)))]
      rw [show Set.Ioc (0 : ℝ) Δ ∪ Set.Ioi Δ = Set.Ioi 0 by ext x; simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]; exact ⟨fun h => h.elim (fun a => a.1) (fun a => by linarith only [a, hΔ]), fun h => by rcases le_or_gt x Δ with h' | h'; exact Or.inl ⟨h, h'⟩; exact Or.inr h'⟩]
    have hΦy_int : IntegrableOn (fun v : ℝ => (Φ v / ((y : ℂ) - Complex.I * v)).im) (Set.Ioo 0 Δ) := by
      refine ((continuousOn_const : ContinuousOn (fun _ : ℝ => (1 / c_sin ^ 2) / |y|) (Set.Icc 0 Δ)).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self).mono' ?_ ?_
      · refine Complex.continuous_im.comp_continuousOn ?_ |>.aestronglyMeasurable measurableSet_Ioo
        refine ContinuousOn.div (continuousOn_const.div (ContinuousOn.pow (Complex.continuous_sin.continuousOn.comp (by fun_prop) (fun _ _ => Set.mem_univ _)) 2) ?_) (by fun_prop) ?_
        · intro v hv; have hlb := sin_pi_iv_beta_lb hδ0 hδ1 hα1 hα2 v hv.1.le
          exact pow_ne_zero 2 (norm_ne_zero_iff.mp (by linarith [mul_pos hc_pos (Real.exp_pos (Real.pi * v))]))
        · intro v _ h; have hre := congr_arg Complex.re h; simp at hre; exact hy_ne hre
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
        rw [Real.norm_eq_abs]; refine (Complex.abs_im_le_norm _).trans ?_; rw [norm_div]
        have hΦ_n : ‖Φ v‖ ≤ 1 / c_sin ^ 2 := (hΦ_bd v hv.1.le).trans
          (mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) hv.1.le)))
        have h_sq : |y| ^ 2 ≤ ‖(y : ℂ) - Complex.I * v‖ ^ 2 := by
          rw [normSq_sub_I_mul, sq_abs]; exact le_add_of_nonneg_right (sq_nonneg v)
        exact div_le_div₀ (by positivity) hΦ_n hy0 ((sq_le_sq₀ (abs_nonneg y) (norm_nonneg _)).mp h_sq)
    have h_sub_int : (∫ v in Set.Ioo (0 : ℝ) Δ, ((Φ v - Φ_star v) / ((y : ℂ) - Complex.I * v)).im) =
        (∫ v in Set.Ioo (0 : ℝ) Δ, (Φ v / ((y : ℂ) - Complex.I * v)).im) -
        (∫ v in Set.Ioo (0 : ℝ) Δ, (Φ_star v / ((y : ℂ) - Complex.I * v)).im) := by
      rw [← integral_sub hΦy_int (h_int_sub.mono_set Set.Ioo_subset_Ioi_self)]
      congr 1; ext v; rw [← Complex.sub_im, ← sub_div]
    rw [h_split, h_sub_int]; ring
  intro y hy1
  have hy0 : 0 < |y| := by linarith
  have hy_ne : y ≠ 0 := abs_pos.mp hy0
  have hcr := contour_representation θ Δ α hθ hΔ hα y hy_ne
  rw [hcr]
  have h_eq1 : (∫ v in Set.Ioo (0 : ℝ) Δ,
      (Complex.exp (-Complex.I * θ) / (Complex.sin (Real.pi * (Complex.I * v - α)) ^ 2 * (y - Complex.I * v))).im) =
      ∫ v in Set.Ioo (0 : ℝ) Δ, (Φ v / ((y : ℂ) - Complex.I * v)).im := by
    congr 1; ext v; dsimp only [Φ]; rw [div_div]
  rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
  gcongr
  rw [h_eq1, h_common_split y hy_ne]
  have h_int_Φ : IntegrableOn (fun v : ℝ => (Φ v).im) (Set.Ioo 0 Δ) := by
    refine ((continuousOn_const : ContinuousOn (fun _ : ℝ => 1 / c_sin ^ 2) (Set.Icc 0 Δ)).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self).mono' ?_ ?_
    · refine Complex.continuous_im.comp_continuousOn ?_ |>.aestronglyMeasurable measurableSet_Ioo
      refine continuousOn_const.div (ContinuousOn.pow (Complex.continuous_sin.continuousOn.comp (by fun_prop) (fun _ _ => Set.mem_univ _)) 2) ?_
      intro v hv; have hlb := sin_pi_iv_beta_lb hδ0 hδ1 hα1 hα2 v hv.1.le
      exact pow_ne_zero 2 (norm_ne_zero_iff.mp (by linarith [mul_pos hc_pos (Real.exp_pos (Real.pi * v))]))
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      rw [Real.norm_eq_abs]; exact (Complex.abs_im_le_norm _).trans ((hΦ_bd v hv.1.le).trans
        (mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) hv.1.le))))
  have h_int_Φs : IntegrableOn (fun v : ℝ => (Φ_star v).im) (Set.Ioi 0) :=
    Complex.imCLM.integrable_comp (cTheta_integrableOn hθ)
  have h_sub_c0 :
      ((∫ v in Set.Ioo (0 : ℝ) Δ, ((Φ v - Φ_star v) / ((y : ℂ) - Complex.I * v)).im) -
        (∫ v in Set.Ioi Δ, (Φ_star v / ((y : ℂ) - Complex.I * v)).im) -
        (Δ * Real.sin θ / (Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ - y))).re) =
      (∫ v in Set.Ioo (0 : ℝ) Δ, ((Φ v - Φ_star v) * (Complex.I * v / ((y : ℂ) * ((y : ℂ) - Complex.I * v)))).im) -
        (∫ v in Set.Ioi Δ, (Φ_star v * (Complex.I * v / ((y : ℂ) * ((y : ℂ) - Complex.I * v)))).im) -
        (Δ * Real.sin θ / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ / ((y : ℂ) * (Complex.I * Δ - y)))).re := by
    have h_diff_c0 : ((∫ v in Set.Ioo (0 : ℝ) Δ, (Φ v - Φ_star v).im) - (∫ v in Set.Ioi Δ, (Φ_star v).im) +
        (Δ * Real.sin θ / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2).re) / y = 0 := by
      have h_s1 : ∫ v in Set.Ioi (0 : ℝ), (Φ_star v).im =
          (∫ v in Set.Ioo (0 : ℝ) Δ, (Φ_star v).im) + (∫ v in Set.Ioi Δ, (Φ_star v).im) := by
        rw [← integral_Ioc_eq_integral_Ioo, ← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
          (h_int_Φs.mono_set Set.Ioc_subset_Ioi_self) (h_int_Φs.mono_set (Set.Ioi_subset_Ioi (by linarith)))]
        rw [show Set.Ioc (0 : ℝ) Δ ∪ Set.Ioi Δ = Set.Ioi 0 by
          ext v; simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
          exact ⟨fun h => h.elim (fun a => a.1) (fun a => by linarith),
            fun h => by rcases le_or_gt v Δ with h' | h'; exact Or.inl ⟨h, h'⟩; exact Or.inr h'⟩]
      have h_s2 : ∫ v in Set.Ioo (0 : ℝ) Δ, (Φ v - Φ_star v).im =
          (∫ v in Set.Ioo (0 : ℝ) Δ, (Φ v).im) - (∫ v in Set.Ioo (0 : ℝ) Δ, (Φ_star v).im) :=
        integral_sub h_int_Φ (h_int_Φs.mono_set Set.Ioo_subset_Ioi_self)
      have h_eq0 : (∫ v in Set.Ioo (0 : ℝ) Δ, (Φ v - Φ_star v).im) - (∫ v in Set.Ioi Δ, (Φ_star v).im) +
          (Δ * Real.sin θ / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2).re = 0 := by
        have h1 : (∫ v in Set.Ioo (0 : ℝ) Δ, (Φ v).im) +
            (Δ * Real.sin θ / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2).re = 0 := hc₀_zero
        have h2 : (∫ v in Set.Ioo (0 : ℝ) Δ, (Φ_star v).im) + (∫ v in Set.Ioi Δ, (Φ_star v).im) = 0 := by
          rw [← h_s1]; exact hc_star_zero
        linarith
      rw [h_eq0, zero_div]
    have h_id1 : ∀ v : ℝ, ((Φ v - Φ_star v) / ((y : ℂ) - Complex.I * v)).im - (Φ v - Φ_star v).im / y =
        ((Φ v - Φ_star v) * (Complex.I * v / ((y : ℂ) * ((y : ℂ) - Complex.I * v)))).im := by
      intro v
      rw [← Complex.div_ofReal_im, ← Complex.sub_im]
      congr 1
      have hne : (y : ℂ) - Complex.I * v ≠ 0 := by intro h; have hre := congr_arg Complex.re h; simp at hre; exact hy_ne hre
      have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy_ne
      field_simp [hne, hyc]; ring
    have h_id2 : ∀ v : ℝ, (Φ_star v / ((y : ℂ) - Complex.I * v)).im - (Φ_star v).im / y =
        (Φ_star v * (Complex.I * v / ((y : ℂ) * ((y : ℂ) - Complex.I * v)))).im := by
      intro v
      rw [← Complex.div_ofReal_im, ← Complex.sub_im]
      congr 1
      have hne : (y : ℂ) - Complex.I * v ≠ 0 := by intro h; have hre := congr_arg Complex.re h; simp at hre; exact hy_ne hre
      have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy_ne
      field_simp [hne, hyc]; ring
    have h_id3 : (Δ * Real.sin θ / (Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ - y))).re +
        (Δ * Real.sin θ / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2).re / y =
        (Δ * Real.sin θ / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ / ((y : ℂ) * (Complex.I * Δ - y)))).re := by
      rw [← Complex.div_ofReal_re, ← Complex.add_re]
      congr 1
      have hne : Complex.I * (Δ : ℂ) - y ≠ 0 := by intro h; have hre := congr_arg Complex.re h; simp at hre; exact hy_ne hre
      have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy_ne
      rw [← div_div, div_eq_mul_one_div ((Δ : ℂ) * Real.sin θ / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2) (Complex.I * (Δ : ℂ) - y),
        div_eq_mul_one_div ((Δ : ℂ) * Real.sin θ / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2) (y : ℂ),
        ← mul_add]
      congr 1
      field_simp [hne, hyc]; ring
    have h_i1 : IntegrableOn (fun v : ℝ => ((Φ v - Φ_star v) / ((y : ℂ) - Complex.I * v)).im) (Set.Ioo 0 Δ) := by
      refine ((continuousOn_const : ContinuousOn (fun _ : ℝ => C_diff * |α - α_star| / |y|) (Set.Icc 0 Δ)).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self).mono' ?_ ?_
      · refine Complex.continuous_im.comp_continuousOn ?_ |>.aestronglyMeasurable measurableSet_Ioo
        refine ContinuousOn.div (ContinuousOn.sub ?_ ?_) (by fun_prop) (fun v _ h => ?_)
        · refine continuousOn_const.div (ContinuousOn.pow (Complex.continuous_sin.continuousOn.comp (by fun_prop) (fun _ _ => Set.mem_univ _)) 2) ?_
          intro v hv; have hlb := sin_pi_iv_beta_lb hδ0 hδ1 hα1 hα2 v hv.1.le
          exact pow_ne_zero 2 (norm_ne_zero_iff.mp (by linarith [mul_pos hc_pos (Real.exp_pos (Real.pi * v))]))
        · exact continuousOn_const.div (ContinuousOn.pow (Complex.continuous_cos.comp (by fun_prop)).continuousOn 2)
            (fun v _ => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ))
        · have hre := congr_arg Complex.re h; simp at hre; exact hy_ne hre
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
        rw [Real.norm_eq_abs]; refine (Complex.abs_im_le_norm _).trans ?_; rw [norm_div]
        have h_sq : |y| ^ 2 ≤ ‖(y : ℂ) - Complex.I * v‖ ^ 2 := by
          rw [normSq_sub_I_mul, sq_abs]; exact le_add_of_nonneg_right (sq_nonneg v)
        have h1 := (hΦ_diff v hv.1.le).trans (mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) hv.1.le)))
        exact div_le_div₀ (by positivity) h1 hy0 ((sq_le_sq₀ (abs_nonneg y) (norm_nonneg _)).mp h_sq)
    have h_i2 : IntegrableOn (fun v : ℝ => (Φ_star v / ((y : ℂ) - Complex.I * v)).im) (Set.Ioi Δ) := by
      refine ((cTheta_integrableOn hθ).mono_set (Set.Ioi_subset_Ioi (by linarith))).norm.div_const |y| |>.mono' ?_ ?_
      · refine Complex.continuous_im.comp_continuousOn ?_ |>.aestronglyMeasurable measurableSet_Ioi
        refine ContinuousOn.div ?_ (by fun_prop) (fun v _ h => ?_)
        · exact continuousOn_const.div (ContinuousOn.pow (Complex.continuous_cos.comp (by fun_prop)).continuousOn 2)
            (fun v _ => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ))
        · have hre := congr_arg Complex.re h; simp at hre; exact hy_ne hre
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
        rw [Real.norm_eq_abs]; refine (Complex.abs_im_le_norm _).trans ?_; rw [norm_div]
        have h_sq : |y| ^ 2 ≤ ‖(y : ℂ) - Complex.I * v‖ ^ 2 := by
          rw [normSq_sub_I_mul, sq_abs]; exact le_add_of_nonneg_right (sq_nonneg v)
        exact div_le_div_of_nonneg_left (norm_nonneg _) hy0 ((sq_le_sq₀ (abs_nonneg y) (norm_nonneg _)).mp h_sq)
    have h_sub1 : (∫ v in Set.Ioo (0 : ℝ) Δ, ((Φ v - Φ_star v) / ((y : ℂ) - Complex.I * v)).im) -
        (∫ v in Set.Ioo (0 : ℝ) Δ, (Φ v - Φ_star v).im) / y =
        ∫ v in Set.Ioo (0 : ℝ) Δ, ((Φ v - Φ_star v) * (Complex.I * v / ((y : ℂ) * ((y : ℂ) - Complex.I * v)))).im := by
      rw [← integral_div, ← integral_sub h_i1 ((h_int_Φ.sub (h_int_Φs.mono_set Set.Ioo_subset_Ioi_self)).congr_fun
        (fun v _ => by simp [Complex.sub_im]) measurableSet_Ioo |>.div_const y)]
      congr 1; ext v; exact h_id1 v
    have h_sub2 : (∫ v in Set.Ioi Δ, (Φ_star v / ((y : ℂ) - Complex.I * v)).im) -
        (∫ v in Set.Ioi Δ, (Φ_star v).im) / y =
        ∫ v in Set.Ioi Δ, (Φ_star v * (Complex.I * v / ((y : ℂ) * ((y : ℂ) - Complex.I * v)))).im := by
      rw [← integral_div, ← integral_sub h_i2 ((h_int_Φs.mono_set (Set.Ioi_subset_Ioi (by linarith))).div_const y)]
      congr 1; ext v; exact h_id2 v
    have h_diff_c0' : (∫ v in Set.Ioo (0 : ℝ) Δ, (Φ v - Φ_star v).im) / y -
        (∫ v in Set.Ioi Δ, (Φ_star v).im) / y +
        (Δ * Real.sin θ / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2).re / y = 0 := by
      rw [← sub_div, ← add_div]; exact h_diff_c0
    linarith [h_diff_c0', h_sub1, h_sub2, h_id3]
  rw [h_sub_c0]
  change |((∫ v in Set.Ioo (0 : ℝ) Δ, ((Φ v - Φ_star v) * (Complex.I * v / ((y : ℂ) * ((y : ℂ) - Complex.I * v)))).im) - (∫ v in Set.Ioi Δ, (Φ_star v * (Complex.I * v / ((y : ℂ) * ((y : ℂ) - Complex.I * v)))).im) - (Δ * Real.sin θ / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ / ((y : ℂ) * (Complex.I * Δ - y)))).re)| ≤ diffA_C_err1 θ * (Δ ^ 2 * Real.exp (-2 * Real.pi * Δ) + |α - α_star|) / y ^ 2
  dsimp only [diffA_C_err1]
  have h_p1 : |∫ v in Set.Ioo (0 : ℝ) Δ, ((Φ v - Φ_star v) * (Complex.I * v / ((y : ℂ) * ((y : ℂ) - Complex.I * v)))).im| ≤
      C_diff * |α - α_star| * (1 / (4 * Real.pi ^ 2)) / y ^ 2 := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    have h_v_int : IntegrableOn (fun v : ℝ => C_diff * |α - α_star| / y ^ 2 * (v * Real.exp (-2 * Real.pi * v))) (Set.Ioi 0) := by
      have h_e : IntegrableOn (fun v : ℝ => Real.exp (-Real.pi * v)) (Set.Ioi 0) := by
        have hc : IntegrableOn (fun v : ℝ => Complex.exp ((-Real.pi : ℂ) * v)) (Set.Ioi 0) :=
          integrableOn_exp_mul_complex_Ioi (by simp; positivity) 0
        refine hc.norm.congr (Eventually.of_forall fun v => ?_)
        dsimp only
        rw [show (-(Real.pi : ℂ) * v) = ((-Real.pi * v : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine (h_e.const_mul (C_diff * |α - α_star| / y ^ 2)).mono' (by fun_prop) ?_
      have hC_diff_nn : 0 ≤ C_diff := div_nonneg (mul_pos two_pos Real.pi_pos).le (pow_nonneg hc_pos.le 4)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (div_nonneg (mul_nonneg hC_diff_nn (abs_nonneg _)) (sq_nonneg y)) (mul_nonneg hv.out.le (Real.exp_pos _).le))]
      have h_v : v ≤ Real.exp (Real.pi * v) := by have := Real.add_one_le_exp (Real.pi * v); nlinarith [Real.two_le_pi, hv.out]
      calc C_diff * |α - α_star| / y ^ 2 * (v * Real.exp (-2 * Real.pi * v))
          ≤ C_diff * |α - α_star| / y ^ 2 * (Real.exp (Real.pi * v) * Real.exp (-2 * Real.pi * v)) := by gcongr
        _ = C_diff * |α - α_star| / y ^ 2 * Real.exp (-Real.pi * v) := by rw [← Real.exp_add]; ring_nf
    have h_mono1 : ∫ v in Set.Ioo (0 : ℝ) Δ, ‖((Φ v - Φ_star v) * (Complex.I * v / ((y : ℂ) * ((y : ℂ) - Complex.I * v)))).im‖ ≤
        ∫ v in Set.Ioo (0 : ℝ) Δ, C_diff * |α - α_star| / y ^ 2 * (v * Real.exp (-2 * Real.pi * v)) := by
      refine setIntegral_mono_on ?_ (h_v_int.mono_set Set.Ioo_subset_Ioi_self) measurableSet_Ioo fun v hv => ?_
      · refine (h_v_int.mono_set Set.Ioo_subset_Ioi_self).mono' ?_ ?_
        · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
          refine ContinuousOn.norm (Complex.continuous_im.comp_continuousOn ?_)
          refine ContinuousOn.mul (ContinuousOn.sub ?_ ?_) (ContinuousOn.div (by fun_prop) (by fun_prop) fun v _ h => ?_)
          · refine continuousOn_const.div (ContinuousOn.pow (Complex.continuous_sin.continuousOn.comp (by fun_prop) (fun _ _ => Set.mem_univ _)) 2) ?_
            intro v hv; have hlb := sin_pi_iv_beta_lb hδ0 hδ1 hα1 hα2 v hv.1.le
            exact pow_ne_zero 2 (norm_ne_zero_iff.mp (by linarith [mul_pos hc_pos (Real.exp_pos (Real.pi * v))]))
          · exact continuousOn_const.div (ContinuousOn.pow (Complex.continuous_cos.comp (by fun_prop)).continuousOn 2)
              (fun v _ => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ))
          · rcases mul_eq_zero.mp h with h1 | h1
            · exact hy_ne (Complex.ofReal_eq_zero.mp h1)
            · have hre := congr_arg Complex.re h1; simp at hre; exact hy_ne hre
        · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
          rw [Real.norm_eq_abs, abs_norm, Real.norm_eq_abs]
          refine (Complex.abs_im_le_norm _).trans ?_; rw [norm_mul, norm_div, norm_mul, Complex.norm_I, one_mul,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv.1, norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have h_sq : |y| ^ 2 ≤ ‖(y : ℂ) - Complex.I * v‖ ^ 2 := by
            rw [normSq_sub_I_mul, sq_abs]; exact le_add_of_nonneg_right (sq_nonneg v)
          have h_n : |y| ≤ ‖(y : ℂ) - Complex.I * v‖ := (sq_le_sq₀ (abs_nonneg y) (norm_nonneg _)).mp h_sq
          have h_y2 : y ^ 2 ≤ |y| * ‖(y : ℂ) - Complex.I * v‖ := by rw [← sq_abs y, sq]; exact mul_le_mul_of_nonneg_left h_n (abs_nonneg y)
          have h_div : v / (|y| * ‖(y : ℂ) - Complex.I * v‖) ≤ v / y ^ 2 :=
            div_le_div_of_nonneg_left hv.1.le (by positivity) h_y2
          calc ‖Φ v - Φ_star v‖ * (v / (|y| * ‖(y : ℂ) - Complex.I * v‖))
              ≤ (C_diff * |α - α_star| * Real.exp (-2 * Real.pi * v)) * (v / y ^ 2) :=
                mul_le_mul (hΦ_diff v hv.1.le) h_div (div_nonneg hv.1.le (by positivity)) (by positivity)
            _ = _ := by ring
      · rw [Real.norm_eq_abs]
        refine (Complex.abs_im_le_norm _).trans ?_; rw [norm_mul, norm_div, norm_mul, Complex.norm_I, one_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv.1, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have h_sq : |y| ^ 2 ≤ ‖(y : ℂ) - Complex.I * v‖ ^ 2 := by
          rw [normSq_sub_I_mul, sq_abs]; exact le_add_of_nonneg_right (sq_nonneg v)
        have h_n : |y| ≤ ‖(y : ℂ) - Complex.I * v‖ := (sq_le_sq₀ (abs_nonneg y) (norm_nonneg _)).mp h_sq
        have h_y2 : y ^ 2 ≤ |y| * ‖(y : ℂ) - Complex.I * v‖ := by rw [← sq_abs y, sq]; exact mul_le_mul_of_nonneg_left h_n (abs_nonneg y)
        have h_div : v / (|y| * ‖(y : ℂ) - Complex.I * v‖) ≤ v / y ^ 2 :=
          div_le_div_of_nonneg_left hv.1.le (by positivity) h_y2
        calc ‖Φ v - Φ_star v‖ * (v / (|y| * ‖(y : ℂ) - Complex.I * v‖))
            ≤ (C_diff * |α - α_star| * Real.exp (-2 * Real.pi * v)) * (v / y ^ 2) :=
              mul_le_mul (hΦ_diff v hv.1.le) h_div (div_nonneg hv.1.le (by positivity)) (by positivity)
          _ = _ := by ring
    have h_mono2 : ∫ v in Set.Ioo (0 : ℝ) Δ, C_diff * |α - α_star| / y ^ 2 * (v * Real.exp (-2 * Real.pi * v)) ≤
        ∫ v in Set.Ioi (0 : ℝ), C_diff * |α - α_star| / y ^ 2 * (v * Real.exp (-2 * Real.pi * v)) := by
      refine setIntegral_mono_set h_v_int ?_ Set.Ioo_subset_Ioi_self.eventuallyLE
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact mul_nonneg (by positivity) (mul_nonneg hv.out.le (Real.exp_pos _).le)
    have h_val : ∫ v in Set.Ioi (0 : ℝ), C_diff * |α - α_star| / y ^ 2 * (v * Real.exp (-2 * Real.pi * v)) =
        C_diff * |α - α_star| * (1 / (4 * Real.pi ^ 2)) / y ^ 2 := by
      rw [integral_const_mul, int_mul_exp_neg_two_pi_Ioi 0 le_rfl]; simp; ring
    exact h_mono1.trans (h_mono2.trans h_val.le)
  have h_p2 : |∫ v in Set.Ioi Δ, (Φ_star v * (Complex.I * v / ((y : ℂ) * ((y : ℂ) - Complex.I * v)))).im| ≤
      C_tail * (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2)) * Δ * Real.exp (-2 * Real.pi * Δ) / y ^ 2 := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    have h_v_int : IntegrableOn (fun v : ℝ => C_tail / y ^ 2 * (v * Real.exp (-2 * Real.pi * v))) (Set.Ioi Δ) := by
      have h_e : IntegrableOn (fun v : ℝ => Real.exp (-Real.pi * v)) (Set.Ioi Δ) := by
        have hc : IntegrableOn (fun v : ℝ => Complex.exp ((-Real.pi : ℂ) * v)) (Set.Ioi Δ) :=
          integrableOn_exp_mul_complex_Ioi (by simp; positivity) Δ
        refine hc.norm.congr (Eventually.of_forall fun v => ?_)
        dsimp only
        rw [show (-(Real.pi : ℂ) * v) = ((-Real.pi * v : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine (h_e.const_mul (C_tail / y ^ 2)).mono' (by fun_prop) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv0 : 0 ≤ v := by linarith [hv.out]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h_v : v ≤ Real.exp (Real.pi * v) := by have := Real.add_one_le_exp (Real.pi * v); nlinarith [Real.two_le_pi, hv0]
      calc C_tail / y ^ 2 * (v * Real.exp (-2 * Real.pi * v))
          ≤ C_tail / y ^ 2 * (Real.exp (Real.pi * v) * Real.exp (-2 * Real.pi * v)) := by gcongr
        _ = C_tail / y ^ 2 * Real.exp (-Real.pi * v) := by rw [← Real.exp_add]; ring_nf
    have h_mono : ∫ v in Set.Ioi Δ, ‖(Φ_star v * (Complex.I * v / ((y : ℂ) * ((y : ℂ) - Complex.I * v)))).im‖ ≤
        ∫ v in Set.Ioi Δ, C_tail / y ^ 2 * (v * Real.exp (-2 * Real.pi * v)) := by
      refine setIntegral_mono_on ?_ h_v_int measurableSet_Ioi fun v hv => ?_
      · refine h_v_int.mono' ?_ ?_
        · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
          refine ContinuousOn.norm (Complex.continuous_im.comp_continuousOn ?_)
          refine ContinuousOn.mul (continuousOn_const.div (ContinuousOn.pow (Complex.continuous_cos.comp (by fun_prop)).continuousOn 2)
            (fun v _ => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ))) (ContinuousOn.div (by fun_prop) (by fun_prop) fun v _ h => ?_)
          rcases mul_eq_zero.mp h with h1 | h1
          · exact hy_ne (Complex.ofReal_eq_zero.mp h1)
          · have hre := congr_arg Complex.re h1; simp at hre; exact hy_ne hre
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
          have hv0 : 0 ≤ v := by linarith [hv.out]
          rw [Real.norm_eq_abs, abs_norm, Real.norm_eq_abs]
          refine (Complex.abs_im_le_norm _).trans ?_; rw [norm_mul (Φ_star v), norm_div (Complex.I * (v : ℂ)), norm_mul, Complex.norm_I, one_mul,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv0, norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have h_sq : |y| ^ 2 ≤ ‖(y : ℂ) - Complex.I * v‖ ^ 2 := by
            rw [normSq_sub_I_mul, sq_abs]; exact le_add_of_nonneg_right (sq_nonneg v)
          have h_n : |y| ≤ ‖(y : ℂ) - Complex.I * v‖ := (sq_le_sq₀ (abs_nonneg y) (norm_nonneg _)).mp h_sq
          have h_y2 : y ^ 2 ≤ |y| * ‖(y : ℂ) - Complex.I * v‖ := by rw [← sq_abs y, sq]; exact mul_le_mul_of_nonneg_left h_n (abs_nonneg y)
          have h_div : v / (|y| * ‖(y : ℂ) - Complex.I * v‖) ≤ v / y ^ 2 :=
            div_le_div_of_nonneg_left hv0 (by positivity) h_y2
          calc ‖Φ_star v‖ * (v / (|y| * ‖(y : ℂ) - Complex.I * v‖))
              ≤ (C_tail * Real.exp (-2 * Real.pi * v)) * (v / y ^ 2) :=
                mul_le_mul (hΦ_star_bd v hv0) h_div (div_nonneg hv0 (by positivity)) (by positivity)
            _ = _ := by ring
      · have hv0 : 0 ≤ v := by linarith [hv.out]
        rw [Real.norm_eq_abs]
        refine (Complex.abs_im_le_norm _).trans ?_; rw [norm_mul (Φ_star v), norm_div (Complex.I * (v : ℂ)), norm_mul, Complex.norm_I, one_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv0, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have h_sq : |y| ^ 2 ≤ ‖(y : ℂ) - Complex.I * v‖ ^ 2 := by
          rw [normSq_sub_I_mul, sq_abs]; exact le_add_of_nonneg_right (sq_nonneg v)
        have h_n : |y| ≤ ‖(y : ℂ) - Complex.I * v‖ := (sq_le_sq₀ (abs_nonneg y) (norm_nonneg _)).mp h_sq
        have h_y2 : y ^ 2 ≤ |y| * ‖(y : ℂ) - Complex.I * v‖ := by rw [← sq_abs y, sq]; exact mul_le_mul_of_nonneg_left h_n (abs_nonneg y)
        have h_div : v / (|y| * ‖(y : ℂ) - Complex.I * v‖) ≤ v / y ^ 2 :=
          div_le_div_of_nonneg_left hv0 (by positivity) h_y2
        calc ‖Φ_star v‖ * (v / (|y| * ‖(y : ℂ) - Complex.I * v‖))
            ≤ (C_tail * Real.exp (-2 * Real.pi * v)) * (v / y ^ 2) :=
              mul_le_mul (hΦ_star_bd v hv0) h_div (div_nonneg hv0 (by positivity)) (by positivity)
          _ = _ := by ring
    rw [integral_const_mul, int_mul_exp_neg_two_pi_Ioi Δ (by linarith)] at h_mono
    have h_le : Δ / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2) ≤ (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2)) * Δ := by
      rw [add_mul, mul_comm (1 / (2 * Real.pi)) Δ, ← mul_div_assoc, mul_one]
      gcongr
      exact le_mul_of_one_le_right (by positivity) hΔ
    calc ∫ v in Set.Ioi Δ, _ ≤ C_tail / y ^ 2 * ((Δ / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2)) * Real.exp (-2 * Real.pi * Δ)) := h_mono
      _ ≤ C_tail / y ^ 2 * ((1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2)) * Δ * Real.exp (-2 * Real.pi * Δ)) := by gcongr
      _ = C_tail * (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2)) * Δ * Real.exp (-2 * Real.pi * Δ) / y ^ 2 := by ring
  have h_p3 := diffA_part3_large θ Δ α c_sin y hΔ hy0 hc_pos (sin_pi_iv_beta_lb hδ0 hδ1 hα1 hα2 Δ (by linarith))
  exact diffA_combine_large C_diff C_tail c_sin Δ |α - α_star| y _ _ _
    hΔ (div_nonneg (mul_pos two_pos Real.pi_pos).le (pow_nonneg hc_pos.le 4))
    (div_nonneg (by norm_num) (sq_nonneg _)) (div_nonneg zero_le_one (sq_nonneg _))
    (abs_nonneg _) h_p1 h_p2 h_p3

lemma majorant_contour_diff_bounds (θ : ℝ) (hθ : |θ| < Real.pi / 2) :
    ∃ (Δ₂ C_err1 : ℝ), Δ₂ ≥ 1 ∧ C_err1 > 0 ∧
      ∀ (Δ α : ℝ), Δ ≥ Δ₂ → α ∈ Set.Ioo (0 : ℝ) 1 →
        |α - (1 / 2 - θ / Real.pi)| ≤ (min ((1 / 2 - θ / Real.pi) / 2) ((1 - (1 / 2 - θ / Real.pi)) / 2)) / 2 →
        Summable (fun n : ℤ => rescaledFDeriv θ Δ (n + α)) →
        ∑' n : ℤ, rescaledFDeriv θ Δ (n + α) = 0 →
        (∀ y : ℝ, 0 < |y| → |y| < 1 →
          |(vaalerInterpolant θ Δ α y - rescaledF θ Δ y) - Real.sin (Real.pi * (y - α)) ^ 2 * limitingJ y θ| ≤
            Real.sin (Real.pi * (y - α)) ^ 2 * (C_err1 * (Δ * Real.exp (-2 * Real.pi * Δ) + |α - (1 / 2 - θ / Real.pi)|) * (1 + Real.log (1 / |y|)))) ∧
        (∀ y : ℝ, 1 ≤ |y| →
          |(vaalerInterpolant θ Δ α y - rescaledF θ Δ y) - Real.sin (Real.pi * (y - α)) ^ 2 * limitingJ y θ| ≤
            Real.sin (Real.pi * (y - α)) ^ 2 * (C_err1 * (Δ ^ 2 * Real.exp (-2 * Real.pi * Δ) + |α - (1 / 2 - θ / Real.pi)|) / y ^ 2)) := by
  let α_star : ℝ := 1 / 2 - θ / Real.pi
  have hα_star : α_star ∈ Set.Ioo (0 : ℝ) 1 := by
    have := abs_lt.mp hθ
    constructor
    · dsimp only [α_star]; rw [sub_pos, div_lt_iff₀ Real.pi_pos]; linarith
    · dsimp only [α_star]; rw [sub_lt_iff_lt_add]; linarith [show -(1 / 2 : ℝ) < θ / Real.pi by rw [lt_div_iff₀ Real.pi_pos]; linarith]
  let δ_star : ℝ := min (α_star / 2) ((1 - α_star) / 2)
  let δ : ℝ := min (δ_star / 2) (1 / 2)
  have hδ0 : 0 < δ := lt_min (div_pos (lt_min (div_pos hα_star.1 (by norm_num)) (div_pos (sub_pos.mpr hα_star.2) (by norm_num))) (by norm_num)) (by norm_num)
  let c_sin : ℝ := Real.sin (Real.pi * δ) / Real.exp Real.pi
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  have hsin_δ_pos : 0 < Real.sin (Real.pi * δ) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hc_pos : 0 < c_sin := div_pos hsin_δ_pos (Real.exp_pos _)
  let C_diff : ℝ := 2 * Real.pi / c_sin ^ 4
  let C_tail : ℝ := 4 / Real.cos θ ^ 2
  let C_err1 : ℝ := C_diff * (2 + 1 / (2 * Real.pi)) + C_tail * (1 / (2 * Real.pi) + 1 / (4 * Real.pi ^ 2) + 1) + 1 / c_sin ^ 2 + 1
  refine ⟨1, diffA_C_err1 θ, le_rfl, ?_, fun Δ α hΔ hα hα_near hsumm_b hsum0 => ?_⟩
  · change 0 < C_err1; positivity
  · exact ⟨majorant_contour_diff_small θ hθ Δ α hΔ hα hα_near hsumm_b hsum0,
           majorant_contour_diff_large θ hθ Δ α hΔ hα hα_near hsumm_b hsum0⟩

end PolarEvaluation
