import PolarEvaluation.AsymmetricMajorantDiffA

noncomputable section

open Complex Real MeasureTheory Filter Topology
open scoped FourierTransform

namespace PolarEvaluation

noncomputable def majorantEntire (θ Δ α : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℤ, ((rescaledF θ Δ (n + α) : ℂ) * sincPi (Δ * z - n - α) ^ 2 +
    (rescaledFDeriv θ Δ (n + α) : ℂ) * (Δ * z - n - α) * sincPi (Δ * z - n - α) ^ 2)

lemma sincPi_deriv_bound (R : ℝ) (hR : 0 ≤ R) :
    ∃ C_d > 0, ∀ u : ℂ, |u.im| ≤ R → ‖deriv sincPi u‖ ≤ C_d := by
  have h_cont : Continuous (fun u : ℂ => ‖deriv sincPi u‖) := by
    refine Continuous.norm ?_
    rw [continuous_iff_continuousAt]
    intro u
    exact ((differentiable_sincPi.analyticAt u).deriv).continuousAt
  obtain ⟨u₀, _, hu₀⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_isMaxOn
    ⟨0, Metric.mem_closedBall_self zero_le_one⟩ h_cont.continuousOn
  let M_d : ℝ := max ‖deriv sincPi u₀‖ (2 * Real.exp (Real.pi * R)) + 1
  refine ⟨M_d, by positivity, fun u hu => ?_⟩
  by_cases hu1 : ‖u‖ ≤ 1
  · have hle : ‖deriv sincPi u‖ ≤ ‖deriv sincPi u₀‖ := hu₀ (Metric.mem_closedBall.mpr (by simpa using hu1))
    dsimp only [M_d]; linarith [le_max_left ‖deriv sincPi u₀‖ (2 * Real.exp (Real.pi * R))]
  · have hu_gt : 1 < ‖u‖ := not_le.mp hu1
    have hu_ne : u ≠ 0 := norm_ne_zero_iff.mp (by linarith)
    have h_ev : sincPi =ᶠ[𝓝 u] fun w => Complex.sin (Real.pi * w) / (Real.pi * w) := by
      filter_upwards [isOpen_ne.mem_nhds hu_ne] with w hw
      dsimp only [sincPi]; simp [hw]
    have hd_eq : deriv sincPi u = Complex.cos (Real.pi * u) / u - Complex.sin (Real.pi * u) / (Real.pi * u ^ 2) := by
      rw [h_ev.deriv_eq]
      have hpw : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w) (Real.pi : ℂ) u := by
        simpa using (hasDerivAt_id u).const_mul (Real.pi : ℂ)
      have hq := (hpw.sin).div hpw (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) hu_ne)
      rw [hq.deriv]
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp [hpi, hu_ne]; ring
    have h_sin_bd : ∀ w : ℂ, ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
      intro w
      have hsin_def : Complex.sin w = (Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2 := by unfold Complex.sin; ring_nf
      rw [hsin_def]
      have h1 : ‖Complex.exp (-w * Complex.I)‖ ≤ Real.exp |w.im| := by
        rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (by simp [Complex.mul_re]; exact le_abs_self _)
      have h2 : ‖Complex.exp (w * Complex.I)‖ ≤ Real.exp |w.im| := by
        rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (by simp [Complex.mul_re]; exact neg_le_abs _)
      calc ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2‖
          = ‖Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)‖ / 2 := by
            rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
        _ ≤ (‖Complex.exp (-w * Complex.I)‖ + ‖Complex.exp (w * Complex.I)‖) / 2 := by gcongr; exact norm_sub_le _ _
        _ ≤ (Real.exp |w.im| + Real.exp |w.im|) / 2 := by gcongr
        _ = Real.exp |w.im| := by ring
    have h_cos_bd : ∀ w : ℂ, ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
      intro w
      have hcos_def : Complex.cos w = (Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)) / 2 := by
        unfold Complex.cos; ring_nf
      rw [hcos_def]
      have h1 : ‖Complex.exp (w * Complex.I)‖ ≤ Real.exp |w.im| := by
        rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (by simp [Complex.mul_re]; exact neg_le_abs _)
      have h2 : ‖Complex.exp (-w * Complex.I)‖ ≤ Real.exp |w.im| := by
        rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (by simp [Complex.mul_re]; exact le_abs_self _)
      calc ‖(Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)) / 2‖
          = ‖Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)‖ / 2 := by
            rw [norm_div, Complex.norm_ofNat]
        _ ≤ (‖Complex.exp (w * Complex.I)‖ + ‖Complex.exp (-w * Complex.I)‖) / 2 := by gcongr; exact norm_add_le _ _
        _ ≤ (Real.exp |w.im| + Real.exp |w.im|) / 2 := by gcongr
        _ = Real.exp |w.im| := by ring
    have him : |(Real.pi * u).im| ≤ Real.pi * R := by
      simp [Complex.mul_im, abs_mul, abs_of_pos Real.pi_pos]
      exact mul_le_mul_of_nonneg_left hu Real.pi_pos.le
    rw [hd_eq]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_div, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have h1 : ‖Complex.cos (Real.pi * u)‖ / ‖u‖ ≤ Real.exp (Real.pi * R) := by
      calc ‖Complex.cos (Real.pi * u)‖ / ‖u‖ ≤ Real.exp |(Real.pi * u).im| / 1 :=
            div_le_div₀ (by positivity) (h_cos_bd _) zero_lt_one hu_gt.le
        _ = Real.exp |(Real.pi * u).im| := div_one _
        _ ≤ Real.exp (Real.pi * R) := Real.exp_le_exp.mpr him
    have h2 : ‖Complex.sin (Real.pi * u)‖ / (Real.pi * ‖u‖ ^ 2) ≤ Real.exp (Real.pi * R) := by
      have hden : 1 ≤ Real.pi * ‖u‖ ^ 2 := by
        have : 2 ≤ Real.pi := Real.two_le_pi
        nlinarith [sq_nonneg ‖u‖]
      calc ‖Complex.sin (Real.pi * u)‖ / (Real.pi * ‖u‖ ^ 2) ≤ Real.exp |(Real.pi * u).im| / 1 :=
            div_le_div₀ (by positivity) (h_sin_bd _) zero_lt_one hden
        _ = Real.exp |(Real.pi * u).im| := div_one _
        _ ≤ Real.exp (Real.pi * R) := Real.exp_le_exp.mpr him
    dsimp only [M_d]
    linarith [le_max_right ‖deriv sincPi u₀‖ (2 * Real.exp (Real.pi * R))]

lemma majorantEntire_props (θ Δ α : ℝ) (hΔ : Δ ≥ 1) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hsumm_b : Summable (fun n : ℤ => rescaledFDeriv θ Δ (n + α))) :
    HasExponentialType (majorantEntire θ Δ α) (2 * Real.pi * Δ) ∧
    (∀ x : ℝ, (majorantEntire θ Δ α x).im = 0 ∧ (majorantEntire θ Δ α x).re = majorantM θ Δ α x) := by
  have ha_summ : Summable (fun n : ℤ => |rescaledF θ Δ (n + α)|) := rescaledF_summable θ Δ α hΔ hα
  have hb_summ : Summable (fun n : ℤ => |rescaledFDeriv θ Δ (n + α)|) := hsumm_b.abs
  let S_ab : ℝ := ∑' n : ℤ, (|rescaledF θ Δ (n + α)| + |rescaledFDeriv θ Δ (n + α)|)
  let term : ℤ → ℂ → ℂ := fun n z =>
    (rescaledF θ Δ (n + α) : ℂ) * sincPi (Δ * z - n - α) ^ 2 +
      (rescaledFDeriv θ Δ (n + α) : ℂ) * (Δ * z - n - α) * sincPi (Δ * z - n - α) ^ 2
  have h_term_bd : ∀ (n : ℤ) (z : ℂ),
      ‖term n z‖ ≤ (|rescaledF θ Δ (n + α)| + |rescaledFDeriv θ Δ (n + α)|) * Real.exp (2 * Real.pi * Δ * ‖z‖ + 4) := by
    intro n z
    have hsb := sincPi_bound (Δ * z - n - α)
    have him : |(Δ * z - n - α).im| ≤ Δ * ‖z‖ := by
      have h1 : (Δ * z - n - α).im = Δ * z.im := by simp [Complex.sub_im, Complex.mul_im]
      rw [h1, abs_mul, abs_of_pos (by linarith : 0 < Δ)]
      exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm z) (by linarith)
    have hs1 : ‖sincPi (Δ * z - n - α) ^ 2‖ ≤ Real.exp (2 * Real.pi * Δ * ‖z‖ + 4) := by
      rw [norm_pow]
      calc ‖sincPi (Δ * z - n - α)‖ ^ 2 ≤ (Real.exp (Real.pi * |(Δ * z - n - α).im| + 2)) ^ 2 := by gcongr; exact hsb.1
        _ = Real.exp (2 * Real.pi * |(Δ * z - n - α).im| + 4) := by rw [← Real.exp_nat_mul]; ring_nf
        _ ≤ Real.exp (2 * Real.pi * (Δ * ‖z‖) + 4) := Real.exp_le_exp.mpr (by gcongr)
        _ = Real.exp (2 * Real.pi * Δ * ‖z‖ + 4) := by ring_nf
    have hs2 : ‖(Δ * z - n - α) * sincPi (Δ * z - n - α) ^ 2‖ ≤ Real.exp (2 * Real.pi * Δ * ‖z‖ + 4) :=
      hsb.2.trans (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos]))
    dsimp only [term]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc ((rescaledFDeriv θ Δ (n + α) : ℝ) : ℂ),
      norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |rescaledF θ Δ (n + α)| * ‖sincPi (Δ * z - n - α) ^ 2‖ +
          |rescaledFDeriv θ Δ (n + α)| * ‖(Δ * z - n - α) * sincPi (Δ * z - n - α) ^ 2‖
        ≤ |rescaledF θ Δ (n + α)| * Real.exp (2 * Real.pi * Δ * ‖z‖ + 4) +
          |rescaledFDeriv θ Δ (n + α)| * Real.exp (2 * Real.pi * Δ * ‖z‖ + 4) := by gcongr
      _ = (|rescaledF θ Δ (n + α)| + |rescaledFDeriv θ Δ (n + α)|) * Real.exp (2 * Real.pi * Δ * ‖z‖ + 4) := by ring
  have h_summ_z : ∀ z : ℂ, Summable (fun n : ℤ => term n z) := by
    intro z
    exact ((ha_summ.add hb_summ).mul_right (Real.exp (2 * Real.pi * Δ * ‖z‖ + 4))).of_norm_bounded (fun n => h_term_bd n z)
  have h_diff : Differentiable ℂ (majorantEntire θ Δ α) := by
    intro z₀
    have h_unif : TendstoUniformlyOn (fun s : Finset ℤ => fun z : ℂ => ∑ n ∈ s, term n z)
        (majorantEntire θ Δ α) Filter.atTop (Metric.ball z₀ 1) := by
      refine tendstoUniformlyOn_tsum
        ((ha_summ.add hb_summ).mul_right (Real.exp (2 * Real.pi * Δ * (‖z₀‖ + 1) + 4))) ?_
      intro n z hz
      have hz_norm : ‖z‖ ≤ ‖z₀‖ + 1 := by
        have := Metric.mem_ball.mp hz
        linarith [norm_sub_norm_le z z₀, dist_eq_norm z z₀]
      refine (h_term_bd n z).trans ?_
      gcongr
      linarith
    have h_term_diff : ∀ n : ℤ, Differentiable ℂ (term n) := by
      intro n
      have hs : Differentiable ℂ (fun w : ℂ => sincPi (Δ * w - n - α)) :=
        differentiable_sincPi.comp (((differentiable_id.const_mul (Δ : ℂ)).sub_const _).sub_const _)
      have h1 : Differentiable ℂ (fun w : ℂ => (rescaledF θ Δ (n + α) : ℂ) * sincPi (Δ * w - n - α) ^ 2) :=
        (hs.pow 2).const_mul _
      have h2 : Differentiable ℂ (fun w : ℂ => (rescaledFDeriv θ Δ (n + α) : ℂ) * (Δ * w - n - α) * sincPi (Δ * w - n - α) ^ 2) :=
        ((((differentiable_id.const_mul (Δ : ℂ)).sub_const _).sub_const _).const_mul _).mul (hs.pow 2)
      exact h1.add h2
    have h_diff_on : DifferentiableOn ℂ (majorantEntire θ Δ α) (Metric.ball z₀ 1) :=
      h_unif.tendstoLocallyUniformlyOn.differentiableOn
        (Filter.Eventually.of_forall fun s =>
          (Differentiable.fun_sum fun n _ => h_term_diff n).differentiableOn)
        Metric.isOpen_ball
    exact h_diff_on.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one))
  refine ⟨⟨h_diff, fun ε hε => ?_⟩, fun x => ?_⟩
  · refine ⟨(S_ab + 1) * Real.exp 4, by positivity, fun z => ?_⟩
    calc ‖majorantEntire θ Δ α z‖
        ≤ ∑' n : ℤ, ‖term n z‖ := norm_tsum_le_tsum_norm (h_summ_z z).norm
      _ ≤ ∑' n : ℤ, (|rescaledF θ Δ (n + α)| + |rescaledFDeriv θ Δ (n + α)|) * Real.exp (2 * Real.pi * Δ * ‖z‖ + 4) :=
          Summable.tsum_le_tsum (fun n => h_term_bd n z) (h_summ_z z).norm
            ((ha_summ.add hb_summ).mul_right _)
      _ = S_ab * Real.exp (2 * Real.pi * Δ * ‖z‖ + 4) := tsum_mul_right
      _ = (S_ab * Real.exp 4) * Real.exp (2 * Real.pi * Δ * ‖z‖) := by rw [add_comm, Real.exp_add]; ring
      _ ≤ ((S_ab + 1) * Real.exp 4) * Real.exp ((2 * Real.pi * Δ + ε) * ‖z‖) := by
          gcongr
          · linarith
          · linarith [norm_nonneg z]
  · have h_real : ∀ n : ℤ, (term n x).im = 0 := by
      intro n
      dsimp only [term]
      rw [sincPi_ofReal (Δ * x - n - α)]
      have heq : (Δ * (x : ℂ) - n - α) = ((Δ * x - n - α : ℝ) : ℂ) := by push_cast; ring
      rw [heq]
      norm_cast
      simp
    have h_re_sum : (majorantEntire θ Δ α x).im = 0 ∧ (majorantEntire θ Δ α x).re =
        ∑' n : ℤ, (term n x).re := by
      have hs := h_summ_z x
      rw [majorantEntire, Complex.im_tsum hs, Complex.re_tsum hs]
      simp_rw [h_real, tsum_zero]
      exact ⟨rfl, rfl⟩
    refine ⟨h_re_sum.1, ?_⟩
    rw [h_re_sum.2]
    unfold majorantM vaalerInterpolant
    by_cases hlat : ∃ m : ℤ, Δ * x = m + α
    · obtain ⟨m, hm⟩ := hlat
      rw [if_pos ⟨m, hm⟩]
      have h_eq : ∀ n : ℤ, (term n x).re = if n = m then rescaledF θ Δ (Δ * x) else 0 := by
        intro n
        dsimp only [term]
        rw [sincPi_ofReal (Δ * x - n - α)]
        have heq : (Δ * (x : ℂ) - n - α) = ((Δ * x - n - α : ℝ) : ℂ) := by push_cast; ring
        rw [heq]
        norm_cast
        by_cases hnm : n = m
        · subst hnm
          have h0 : Δ * x - n - α = 0 := by linarith
          simp [h0, hm]
        · have hne : Δ * x - n - α ≠ 0 := by intro h; exact hnm (by exact_mod_cast (by linarith : (n : ℝ) = m))
          have hsin0 : Real.sin (Real.pi * (Δ * x - n - α)) = 0 := by
            have h1 : Real.pi * (Δ * x - n - α) = ((m - n : ℤ) : ℝ) * Real.pi := by rw [hm]; push_cast; ring
            rw [h1, Real.sin_int_mul_pi]
          simp [hnm, hne, hsin0]
      simp_rw [h_eq, tsum_ite_eq]
    · rw [if_neg hlat]
      have h_eq : ∀ n : ℤ, (term n x).re =
          (Real.sin (Real.pi * (Δ * x - α)) ^ 2 / Real.pi ^ 2) *
            (rescaledF θ Δ (n + α) / (Δ * x - n - α) ^ 2 + rescaledFDeriv θ Δ (n + α) / (Δ * x - n - α)) := by
        intro n
        dsimp only [term]
        rw [sincPi_ofReal (Δ * x - n - α)]
        have heq : (Δ * (x : ℂ) - n - α) = ((Δ * x - n - α : ℝ) : ℂ) := by push_cast; ring
        rw [heq]
        norm_cast
        have hne : Δ * x - n - α ≠ 0 := fun h => hlat ⟨n, by linarith⟩
        have hsin_eq : Real.sin (Real.pi * (Δ * x - n - α)) ^ 2 = Real.sin (Real.pi * (Δ * x - α)) ^ 2 := by
          have h1 : Real.pi * (Δ * x - α) = Real.pi * (Δ * x - n - α) + (n : ℝ) * Real.pi := by ring
          rw [h1, Real.sin_add_int_mul_pi]
          simp [mul_pow, ← pow_mul, mul_comm n 2]
        simp only [if_neg hne, hsin_eq]
        field_simp [hne, Real.pi_ne_zero]; ring
      simp_rw [h_eq, tsum_mul_left]

private lemma diffB_tail_bound (θ Δ α δ y : ℝ) (hΔ : 1 ≤ Δ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hy : |y| ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (h_na_lb : ∀ n : ℤ, δ ≤ |(n : ℝ) + α|)
    (hF_unif : ∀ n : ℤ, |rescaledF θ Δ (n + α)| ≤ 4 + Real.log (1 / δ) + Real.log Δ)
    (hFd_bd : ∀ n : ℤ, |rescaledFDeriv θ Δ (n + α)| ≤ 1 / |(n : ℝ) + α| + 2 / Δ)
    (F5 F_mid : Finset ℤ) (hF5 : F5 = Finset.Icc (-2) 2)
    (hF_mid : ∀ n : ℤ, n ∉ F5 → |(n : ℝ)| ≤ Δ → n ∈ F_mid)
    (f_mid f_inv_sq : ℤ → ℝ)
    (hf_mid_eq : ∀ n : ℤ, n ∈ F_mid → f_mid n = 2 / Δ)
    (hf_mid_nn : ∀ n : ℤ, 0 ≤ f_mid n)
    (hf_inv_eq : ∀ n : ℤ, n ∉ F5 → f_inv_sq n = 1 / (n : ℝ) ^ 2)
    (hf_inv_nn : ∀ n : ℤ, 0 ≤ f_inv_sq n) :
    ∀ n : ℤ, |if n ∈ F5 then 0 else Real.sin (Real.pi * (y - α)) ^ 2 / Real.pi ^ 2 *
        (rescaledF θ Δ (n + α) / (y - n - α) ^ 2 + rescaledFDeriv θ Δ (n + α) / (y - n - α))| ≤
      (1 / Real.pi ^ 2) * (((4 + Real.log (1 / δ) + Real.log Δ) * 9 + 24) * f_inv_sq n + f_mid n) := by
  intro n
  have hΔ_pos : 0 < Δ := zero_lt_one.trans_le hΔ
  by_cases hn : n ∈ F5
  · simp only [hn, ↓reduceIte, abs_zero]
    have hK_nn : 0 ≤ (4 + Real.log (1 / δ) + Real.log Δ) * 9 + 24 := by
      have h1 := Real.log_nonneg ((one_le_div hδ0).mpr hδ1)
      have h2 := Real.log_nonneg hΔ
      linarith
    exact mul_nonneg (div_nonneg zero_le_one (sq_nonneg _)) (add_nonneg (mul_nonneg hK_nn (hf_inv_nn n)) (hf_mid_nn n))
  · simp only [hn, ↓reduceIte, hf_inv_eq n hn]
    have hn3 : 3 ≤ |n| := by
      rw [hF5] at hn
      simp only [Finset.mem_Icc, not_and, not_le] at hn
      by_contra h; push Not at h
      rcases abs_lt.mp h with ⟨h1, h2⟩
      rcases lt_or_ge n 0 with h0 | h0
      · exact absurd (hn (by omega)) (by omega)
      · exact absurd (hn (by omega)) (by omega)
    have hn_real : (3 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast hn3
    have hyna_lb : |(n : ℝ)| / 3 ≤ |y - n - α| := by
      have h1 : |y - α| ≤ 2 := by
        calc |y - α| ≤ |y| + |α| := abs_sub _ _
          _ ≤ 1 + 1 := add_le_add hy (by rw [abs_of_pos hα.1]; exact hα.2.le)
          _ = 2 := by norm_num
      have h2 := abs_sub_abs_le_abs_sub (n : ℝ) (y - α)
      have h3 : |(n : ℝ) - (y - α)| = |y - n - α| := by rw [abs_sub_comm]; ring_nf
      rw [h3] at h2; linarith
    have h_inv_sq : 1 / (y - n - α) ^ 2 ≤ 9 / (n : ℝ) ^ 2 := by
      have hsq : (n : ℝ) ^ 2 / 9 ≤ (y - n - α) ^ 2 := by
        rw [← sq_abs (y - n - α), ← sq_abs (n : ℝ)]; nlinarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have h_t1 : |rescaledF θ Δ (n + α) / (y - n - α) ^ 2| ≤
        (4 + Real.log (1 / δ) + Real.log Δ) * (9 / (n : ℝ) ^ 2) := by
      rw [abs_div, abs_of_nonneg (sq_nonneg _), div_eq_mul_one_div]
      exact mul_le_mul (hF_unif n) h_inv_sq (by positivity) (by
        have := Real.log_nonneg ((one_le_div hδ0).mpr hδ1)
        have := Real.log_nonneg hΔ
        linarith)
    have h_t2 : |rescaledFDeriv θ Δ (n + α) / (y - n - α)| ≤ 24 / (n : ℝ) ^ 2 + f_mid n := by
      rw [abs_div]
      by_cases h_leΔ : |(n : ℝ)| ≤ Δ
      · have hf_eq : f_mid n = 2 / Δ := hf_mid_eq n (hF_mid n hn h_leΔ)
        rw [hf_eq]
        have h1 := hFd_bd n
        have h2 : 1 / |(n : ℝ) + α| ≤ 2 / |(n : ℝ)| := by
          have hna_lb2 : |(n : ℝ)| / 2 ≤ |(n : ℝ) + α| := by
            have h1' : |α| ≤ 1 := by rw [abs_of_pos hα.1]; exact hα.2.le
            have h2' := abs_sub_abs_le_abs_sub (n : ℝ) (-α)
            simp only [abs_neg, sub_neg_eq_add] at h2'; linarith
          rw [div_le_div_iff₀ (lt_of_lt_of_le hδ0 (h_na_lb n)) (by linarith)]; linarith
        calc |rescaledFDeriv θ Δ (n + α)| / |y - n - α|
            ≤ (2 / |(n : ℝ)| + 2 / Δ) / (|(n : ℝ)| / 3) :=
              div_le_div₀ (by positivity) (by linarith) (by positivity) hyna_lb
          _ = 6 / (n : ℝ) ^ 2 + 6 / (Δ * |(n : ℝ)|) := by
              rw [← sq_abs (n : ℝ)]; field_simp [(by linarith : |(n : ℝ)| ≠ 0), hΔ_pos.ne']; ring
          _ ≤ 24 / (n : ℝ) ^ 2 + 2 / Δ := by
              have h6 : 6 / (Δ * |(n : ℝ)|) ≤ 2 / Δ := by
                rw [div_le_div_iff₀ (by positivity) hΔ_pos]; nlinarith
              linarith [show (0 : ℝ) ≤ 18 / (n : ℝ) ^ 2 by positivity]
      · have h_gtΔ : Δ < |(n : ℝ)| := not_le.mp h_leΔ
        have hne : (n : ℝ) + α ≠ 0 := abs_pos.mp (lt_of_lt_of_le hδ0 (h_na_lb n))
        have hbm := rescaledFDeriv_mul_bound θ Δ (n + α) hΔ_pos hne
        rw [abs_mul] at hbm
        have hna_ge_23 : (2 / 3 : ℝ) * |(n : ℝ)| ≤ |(n : ℝ) + α| := by
          have h1 : |α| ≤ 1 := by rw [abs_of_pos hα.1]; exact hα.2.le
          have h2 := abs_sub_abs_le_abs_sub (n : ℝ) (-α)
          simp only [abs_neg, sub_neg_eq_add] at h2; linarith
        have hb_le : |rescaledFDeriv θ Δ (n + α)| ≤ 2 * Δ ^ 2 / |(n : ℝ) + α| ^ 3 := by
          rw [← le_div_iff₀' (lt_of_lt_of_le hδ0 (h_na_lb n))] at hbm
          calc |rescaledFDeriv θ Δ (n + α)| ≤ (2 * Δ ^ 2 / ((n : ℝ) + α) ^ 2) / |(n : ℝ) + α| := hbm
            _ = 2 * Δ ^ 2 / |(n : ℝ) + α| ^ 3 := by rw [← sq_abs ((n : ℝ) + α)]; ring
        have h_sq_le : Δ ^ 2 ≤ (9 / 4 : ℝ) * |(n : ℝ) + α| ^ 2 := by nlinarith
        have hb_le2 : |rescaledFDeriv θ Δ (n + α)| ≤ (27 / 4 : ℝ) / |(n : ℝ)| := by
          calc |rescaledFDeriv θ Δ (n + α)| ≤ 2 * Δ ^ 2 / |(n : ℝ) + α| ^ 3 := hb_le
            _ ≤ 2 * ((9 / 4 : ℝ) * |(n : ℝ) + α| ^ 2) / |(n : ℝ) + α| ^ 3 := by gcongr
            _ = (9 / 2 : ℝ) / |(n : ℝ) + α| := by field_simp [(by linarith : |(n : ℝ) + α| ≠ 0)]; ring
            _ ≤ (9 / 2 : ℝ) / ((2 / 3 : ℝ) * |(n : ℝ)|) :=
                div_le_div_of_nonneg_left (by positivity) (by positivity) hna_ge_23
            _ = (27 / 4 : ℝ) / |(n : ℝ)| := by ring
        have hf_nn : 0 ≤ f_mid n := hf_mid_nn n
        calc |rescaledFDeriv θ Δ (n + α)| / |y - n - α|
            ≤ ((27 / 4 : ℝ) / |(n : ℝ)|) / (|(n : ℝ)| / 3) :=
              div_le_div₀ (by positivity) hb_le2 (by positivity) hyna_lb
          _ = (81 / 4 : ℝ) / (n : ℝ) ^ 2 := by
              rw [← sq_abs (n : ℝ)]; field_simp [(by linarith : |(n : ℝ)| ≠ 0)]; ring
          _ ≤ 24 / (n : ℝ) ^ 2 + f_mid n := by
              have : (81 / 4 : ℝ) / (n : ℝ) ^ 2 ≤ 24 / (n : ℝ) ^ 2 := by gcongr; norm_num
              linarith
    rw [abs_mul, abs_div, abs_of_pos (sq_pos_of_pos Real.pi_pos)]
    have hsin1 : Real.sin (Real.pi * (y - α)) ^ 2 ≤ 1 := by
      have := Real.abs_sin_le_one (Real.pi * (y - α))
      nlinarith [sq_abs (Real.sin (Real.pi * (y - α)))]
    rw [abs_of_nonneg (sq_nonneg _)]
    calc Real.sin (Real.pi * (y - α)) ^ 2 / Real.pi ^ 2 *
          |rescaledF θ Δ (n + α) / (y - n - α) ^ 2 + rescaledFDeriv θ Δ (n + α) / (y - n - α)|
        ≤ (1 / Real.pi ^ 2) * (|rescaledF θ Δ (n + α) / (y - n - α) ^ 2| + |rescaledFDeriv θ Δ (n + α) / (y - n - α)|) := by
          gcongr; exact abs_add_le _ _
      _ ≤ (1 / Real.pi ^ 2) * (((4 + Real.log (1 / δ) + Real.log Δ) * 9 + 24) * (1 / (n : ℝ) ^ 2) + f_mid n) := by
          gcongr; linarith

private lemma diffB_f_inv_sum (F5 : Finset ℤ) (hF5 : F5 = Finset.Icc (-2) 2)
    (C_z : ℝ) (hCz : C_z = ∑' k : ℕ, (1 : ℝ) / (k + 1 : ℝ) ^ 2) :
    Summable (fun n : ℤ => if n ∈ F5 then (0 : ℝ) else 1 / (n : ℝ) ^ 2) ∧
    (∑' n : ℤ, if n ∈ F5 then (0 : ℝ) else 1 / (n : ℝ) ^ 2) ≤ 8 * C_z := by
  subst hF5 hCz
  let f_inv_sq : ℤ → ℝ := fun n => if n ∈ Finset.Icc (-2 : ℤ) 2 then 0 else 1 / (n : ℝ) ^ 2
  have hf_inv_pos : Summable (fun k : ℕ => f_inv_sq k) := by
    refine (summable_one_div_sq_nat.mul_left 4).of_nonneg_of_le
      (fun k => by dsimp only [f_inv_sq]; split_ifs <;> positivity) (fun k => ?_)
    dsimp only [f_inv_sq]; split_ifs with h
    · positivity
    · have hk0 : k ≠ 0 := by rintro rfl; exact h (by decide)
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
      have hsq : ((k : ℝ) + 1) ^ 2 ≤ 4 * (k : ℝ) ^ 2 := by nlinarith
      simp only [Int.cast_natCast]
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hf_inv_neg : Summable (fun k : ℕ => f_inv_sq (-↑k)) := by
    refine (summable_one_div_sq_nat.mul_left 4).of_nonneg_of_le
      (fun k => by dsimp only [f_inv_sq]; split_ifs <;> positivity) (fun k => ?_)
    dsimp only [f_inv_sq]; split_ifs with h
    · positivity
    · have hk0 : k ≠ 0 := by rintro rfl; exact h (by decide)
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
      have hsq : ((k : ℝ) + 1) ^ 2 ≤ 4 * (k : ℝ) ^ 2 := by nlinarith
      simp only [Int.cast_neg, Int.cast_natCast, neg_sq]
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hf_inv_s : Summable f_inv_sq := Summable.of_nat_of_neg hf_inv_pos hf_inv_neg
  refine ⟨hf_inv_s, ?_⟩
  have h1 : ∑' k : ℕ, f_inv_sq k ≤ 4 * ∑' k : ℕ, (1 : ℝ) / (k + 1 : ℝ) ^ 2 := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun k => ?_) hf_inv_pos (summable_one_div_sq_nat.mul_left 4)
    dsimp only [f_inv_sq]; split_ifs with h
    · positivity
    · have hk0 : k ≠ 0 := by rintro rfl; exact h (by decide)
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
      have hsq : ((k : ℝ) + 1) ^ 2 ≤ 4 * (k : ℝ) ^ 2 := by nlinarith
      simp only [Int.cast_natCast]
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h2 : ∑' k : ℕ, f_inv_sq (-↑k) ≤ 4 * ∑' k : ℕ, (1 : ℝ) / (k + 1 : ℝ) ^ 2 := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun k => ?_) hf_inv_neg (summable_one_div_sq_nat.mul_left 4)
    dsimp only [f_inv_sq]; split_ifs with h
    · positivity
    · have hk0 : k ≠ 0 := by rintro rfl; exact h (by decide)
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
      have hsq : ((k : ℝ) + 1) ^ 2 ≤ 4 * (k : ℝ) ^ 2 := by nlinarith
      simp only [Int.cast_neg, Int.cast_natCast, neg_sq]
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hf_nn : ∀ n : ℤ, 0 ≤ f_inv_sq n := fun n => by dsimp only [f_inv_sq]; split_ifs <;> positivity
  have h_fin : ∀ s : Finset ℤ, ∑ n ∈ s, f_inv_sq n ≤ (∑' k : ℕ, f_inv_sq k) + ∑' k : ℕ, f_inv_sq (-↑k) := by
    intro s
    let sN : Finset ℕ := s.image Int.natAbs
    have h_sub : s ⊆ sN.image (fun k : ℕ => (k : ℤ)) ∪ sN.image (fun k : ℕ => -(k : ℤ)) := by
      intro n hn
      rcases Int.natAbs_eq n with h_eq | h_eq
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨n.natAbs, Finset.mem_image_of_mem _ hn, h_eq.symm⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨n.natAbs, Finset.mem_image_of_mem _ hn, h_eq.symm⟩)
    calc ∑ n ∈ s, f_inv_sq n
        ≤ ∑ n ∈ sN.image (fun k : ℕ => (k : ℤ)) ∪ sN.image (fun k : ℕ => -(k : ℤ)), f_inv_sq n :=
          Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun n _ _ => hf_nn n)
      _ ≤ (∑ n ∈ sN.image (fun k : ℕ => (k : ℤ)), f_inv_sq n) +
          ∑ n ∈ sN.image (fun k : ℕ => -(k : ℤ)), f_inv_sq n := by
          have h_ui := Finset.sum_union_inter (s₁ := sN.image (fun k : ℕ => (k : ℤ)))
            (s₂ := sN.image (fun k : ℕ => -(k : ℤ))) (f := f_inv_sq)
          have h_in : 0 ≤ ∑ n ∈ sN.image (fun k : ℕ => (k : ℤ)) ∩ sN.image (fun k : ℕ => -(k : ℤ)), f_inv_sq n :=
            Finset.sum_nonneg (fun n _ => hf_nn n)
          linarith
      _ = (∑ k ∈ sN, f_inv_sq k) + ∑ k ∈ sN, f_inv_sq (-↑k) := by
          rw [Finset.sum_image (fun a _ b _ h => Int.ofNat.inj h),
              Finset.sum_image (fun a _ b _ h => Int.ofNat.inj (neg_inj.mp h))]
      _ ≤ (∑' k : ℕ, f_inv_sq k) + ∑' k : ℕ, f_inv_sq (-↑k) :=
          add_le_add (hf_inv_pos.sum_le_tsum sN (fun k _ => hf_nn k))
            (hf_inv_neg.sum_le_tsum sN (fun k _ => hf_nn (-↑k)))
  exact (le_of_tendsto_of_tendsto' hf_inv_s.hasSum tendsto_const_nhds h_fin).trans (by linarith)

lemma majorantM_sup_and_L1_bounds (θ : ℝ) (hθ : |θ| < Real.pi / 2) :
    ∃ (Δ₃ C_sup C_L1 : ℝ), Δ₃ ≥ 2 ∧ C_sup > 0 ∧ C_L1 > 0 ∧
      ∀ (Δ α : ℝ), Δ ≥ Δ₃ → α ∈ Set.Ioo (0 : ℝ) 1 →
        |α - (1 / 2 - θ / Real.pi)| ≤ (min ((1 / 2 - θ / Real.pi) / 2) ((1 - (1 / 2 - θ / Real.pi)) / 2)) / 2 →
        Summable (fun n : ℤ => rescaledFDeriv θ Δ (n + α)) →
        ∑' n : ℤ, rescaledFDeriv θ Δ (n + α) = 0 →
        (∀ x : ℝ, (1 + x ^ 2) * |majorantM θ Δ α x| ≤ C_sup * Real.log Δ) ∧
        Integrable (fun x : ℝ => majorantM θ Δ α x) ∧
        (∫ x : ℝ, |majorantM θ Δ α x|) ≤ C_L1 := by
  obtain ⟨Δ₂, C_err1, hΔ₂, hC_err1, h_diff_bd⟩ := majorant_contour_diff_bounds θ hθ
  obtain ⟨C_up, hC_up, hJ_up⟩ := limitingJ_upper_bound θ hθ
  let α_star : ℝ := 1 / 2 - θ / Real.pi
  have hα_star : α_star ∈ Set.Ioo (0 : ℝ) 1 := by
    have := abs_lt.mp hθ
    constructor
    · dsimp only [α_star]; rw [sub_pos, div_lt_iff₀ Real.pi_pos]; linarith
    · dsimp only [α_star]; rw [sub_lt_iff_lt_add]; linarith [show -(1 / 2 : ℝ) < θ / Real.pi by rw [lt_div_iff₀ Real.pi_pos]; linarith]
  let δ_star : ℝ := min (α_star / 2) ((1 - α_star) / 2)
  let δ : ℝ := min (δ_star / 2) (1 / 2)
  have hδ0 : 0 < δ := lt_min (div_pos (lt_min (div_pos hα_star.1 (by norm_num)) (div_pos (sub_pos.mpr hα_star.2) (by norm_num))) (by norm_num)) (by norm_num)
  let C_mid : ℝ := C_up + C_err1 * (1 + δ_star / 2)
  let C_z : ℝ := ∑' k : ℕ, (1 : ℝ) / (k + 1 : ℝ) ^ 2
  have hCz_pos : 0 < C_z := tsum_pos summable_one_div_sq_nat (fun _ => by positivity) 0 (by positivity)
  let C_small_0 : ℝ := 5 * (4 + Real.log (1 / δ) + 1 / δ + 2) +
    (1 / Real.pi ^ 2) * ((4 + Real.log (1 / δ)) * 72 * C_z + 192 * C_z + 4) + 1
  let C_small_1 : ℝ := 5 + 72 * C_z / Real.pi ^ 2 + 1
  let C_small : ℝ := C_small_0 / Real.log 2 + C_small_1
  let C_sup : ℝ := max (2 * C_small) ((2 * C_mid + 8) / Real.log 2 + 2)
  let C_L1 : ℝ := 2 * C_small + 2 * C_mid + (∫ x in Set.Ioo (-1 : ℝ) 1, |kernelK θ x|) + (2 * C_mid + 8) * Real.pi
  let Δ₃ : ℝ := max Δ₂ 2
  have hΔ₃ : Δ₃ ≥ 2 := le_max_right _ _
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Δ₃, C_sup, C_L1, hΔ₃, by positivity, ?_, fun Δ α hΔ hα hα_near hsumm_b hsum0 => ?_⟩
  · have : 0 ≤ ∫ x in Set.Ioo (-1 : ℝ) 1, |kernelK θ x| := setIntegral_nonneg measurableSet_Ioo (fun _ _ => abs_nonneg _)
    positivity
  have hΔ_ge_Δ₂ : Δ ≥ Δ₂ := le_trans (le_max_left _ _) hΔ
  have hΔ_ge_2 : Δ ≥ 2 := le_trans (le_max_right _ _) hΔ
  have hΔ_ge_1 : Δ ≥ 1 := by linarith
  have hΔ_pos : 0 < Δ := by linarith
  have hlogΔ_ge : Real.log 2 ≤ Real.log Δ := Real.log_le_log (by norm_num) hΔ_ge_2
  have hlogΔ_pos : 0 < Real.log Δ := lt_of_lt_of_le hlog2_pos hlogΔ_ge
  have h_na_lb : ∀ n : ℤ, δ ≤ |(n : ℝ) + α| := by
    intro n
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
    rcases le_or_gt (0 : ℤ) n with hn | hn
    · have : (0 : ℝ) ≤ n := by exact_mod_cast hn
      rw [abs_of_pos (by linarith [hα.1])]; linarith
    · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hn
      rw [abs_of_neg (by linarith [hα.2])]; linarith
  have h_small_y : ∀ y : ℝ, |y| ≤ 1 → |vaalerInterpolant θ Δ α y| ≤ C_small * Real.log Δ := by
    intro y hy
    have hF_unif : ∀ n : ℤ, |rescaledF θ Δ (n + α)| ≤ 4 + Real.log (1 / δ) + Real.log Δ := by
      intro n
      unfold rescaledF
      rcases le_or_gt 1 (|((n : ℝ) + α) / Δ|) with h | h
      · have hbd := kernelK_bound_large θ h
        have h1 : 4 / (((n : ℝ) + α) / Δ) ^ 2 ≤ 4 := by
          have : 1 ≤ (((n : ℝ) + α) / Δ) ^ 2 := by rw [← sq_abs]; nlinarith
          exact div_le_self (by norm_num) this
        have hlog1 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg ((one_le_div hδ0).mpr (by linarith [min_le_right (δ_star / 2) (1 / 2)]))
        linarith
      · have h_abs_pos : 0 < |(n : ℝ) + α| := lt_of_lt_of_le hδ0 (h_na_lb n)
        have hu0 : 0 < |((n : ℝ) + α) / Δ| := by rw [abs_div, abs_of_pos hΔ_pos]; exact div_pos h_abs_pos hΔ_pos
        have hbd := kernelK_bound_small θ hu0 h.le
        have h_log_le : Real.log (1 / |((n : ℝ) + α) / Δ|) ≤ Real.log (1 / δ) + Real.log Δ := by
          have heq : 1 / |((n : ℝ) + α) / Δ| = (1 / |(n : ℝ) + α|) * Δ := by
            rw [abs_div, abs_of_pos hΔ_pos]; field_simp [h_abs_pos.ne', hΔ_pos.ne']
          rw [heq, Real.log_mul (by positivity) hΔ_pos.ne']
          gcongr; exact div_le_div_of_nonneg_left zero_le_one hδ0 (h_na_lb n)
        linarith
    have hFd_bd : ∀ n : ℤ, |rescaledFDeriv θ Δ (n + α)| ≤ 1 / |(n : ℝ) + α| + 2 / Δ := by
      intro n
      have hne : (n : ℝ) + α ≠ 0 := abs_pos.mp (lt_of_lt_of_le hδ0 (h_na_lb n))
      unfold rescaledFDeriv
      have heq : Real.cos θ * (1 / ((n : ℝ) + α) - ((n : ℝ) + α) / (((n : ℝ) + α) ^ 2 + Δ ^ 2)) =
          Real.cos θ * (Δ ^ 2 / (((n : ℝ) + α) * (((n : ℝ) + α) ^ 2 + Δ ^ 2))) := by
        field_simp [hne, (by positivity : (0 : ℝ) < ((n : ℝ) + α) ^ 2 + Δ ^ 2)]; ring
      rw [heq]
      calc |Real.cos θ * (Δ ^ 2 / (((n : ℝ) + α) * (((n : ℝ) + α) ^ 2 + Δ ^ 2))) -
            Real.sin θ * (2 * Δ ^ 3 / (((n : ℝ) + α) ^ 2 + Δ ^ 2) ^ 2)|
          ≤ |Real.cos θ * (Δ ^ 2 / (((n : ℝ) + α) * (((n : ℝ) + α) ^ 2 + Δ ^ 2)))| +
            |Real.sin θ * (2 * Δ ^ 3 / (((n : ℝ) + α) ^ 2 + Δ ^ 2) ^ 2)| := abs_sub _ _
        _ = |Real.cos θ| * (Δ ^ 2 / (|(n : ℝ) + α| * (((n : ℝ) + α) ^ 2 + Δ ^ 2))) +
            |Real.sin θ| * (2 * Δ ^ 3 / (((n : ℝ) + α) ^ 2 + Δ ^ 2) ^ 2) := by
            rw [abs_mul, abs_mul, abs_div, abs_div, abs_mul, abs_of_pos (sq_pos_of_pos hΔ_pos),
              abs_of_pos (by positivity : 0 < ((n : ℝ) + α) ^ 2 + Δ ^ 2),
              abs_of_pos (by positivity : 0 < 2 * Δ ^ 3),
              abs_of_pos (by positivity : 0 < (((n : ℝ) + α) ^ 2 + Δ ^ 2) ^ 2)]
        _ ≤ 1 * (1 / |(n : ℝ) + α|) + 1 * (2 / Δ) := by
            gcongr
            · exact Real.abs_cos_le_one θ
            · rw [div_le_div_iff₀ (by positivity) (lt_of_lt_of_le hδ0 (h_na_lb n))]
              nlinarith [sq_nonneg ((n : ℝ) + α)]
            · exact Real.abs_sin_le_one θ
            · rw [div_le_div_iff₀ (by positivity) hΔ_pos]
              have h1 : Δ ^ 2 ≤ ((n : ℝ) + α) ^ 2 + Δ ^ 2 := by linarith [sq_nonneg ((n : ℝ) + α)]
              nlinarith [sq_nonneg Δ]
        _ = 1 / |(n : ℝ) + α| + 2 / Δ := by ring
    have h_to_Csmall : ∀ A B : ℝ, A ≤ C_small_0 → B ≤ C_small_1 → A + B * Real.log Δ ≤ C_small * Real.log Δ := by
      intro A B hA hB
      have h1 : A + B * Real.log Δ ≤ C_small_0 + C_small_1 * Real.log Δ := by gcongr
      refine h1.trans ?_
      dsimp only [C_small]
      rw [add_mul, div_mul_eq_mul_div, le_div_iff₀ hlog2_pos]
      nlinarith [mul_le_mul_of_nonneg_left hlogΔ_ge (by positivity : 0 ≤ C_small_0)]
    by_cases hlat : ∃ n : ℤ, y = n + α
    · obtain ⟨n, rfl⟩ := hlat
      unfold vaalerInterpolant
      simp only [if_pos ⟨n, rfl⟩]
      have h_le_c0 : 4 + Real.log (1 / δ) ≤ C_small_0 := by
        have hlog1 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg ((one_le_div hδ0).mpr (by linarith [min_le_right (δ_star / 2) (1 / 2)]))
        dsimp only [C_small_0]; linarith [show 0 ≤ (4 + Real.log (1 / δ)) * 72 * C_z by positivity]
      have h_le_c1 : (1 : ℝ) ≤ C_small_1 := by
        dsimp only [C_small_1]; linarith [show 0 ≤ 72 * C_z / Real.pi ^ 2 by positivity]
      exact (hF_unif n).trans (by
        rw [show 4 + Real.log (1 / δ) + Real.log Δ = (4 + Real.log (1 / δ)) + 1 * Real.log Δ by ring]
        exact h_to_Csmall _ _ h_le_c0 h_le_c1)
    · unfold vaalerInterpolant
      simp only [if_neg hlat]
      have ha_s : Summable (fun n : ℤ => rescaledF θ Δ (n + α) / (y - n - α) ^ 2) := by
        have h_inv := summable_inv_add_sq_of_ne_zero (α - y) (fun n h0 => hlat ⟨n, by linarith⟩)
        refine (h_inv.mul_left (4 + Real.log (1 / δ) + Real.log Δ)).of_norm_bounded fun n => ?_
        rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg _), div_eq_mul_one_div]
        have h_nonneg : 0 ≤ 4 + Real.log (1 / δ) + Real.log Δ := by
          have := Real.log_nonneg ((one_le_div hδ0).mpr (by linarith [min_le_right (δ_star / 2) (1 / 2)]))
          linarith
        calc |rescaledF θ Δ (n + α)| * (1 / (y - n - α) ^ 2)
            ≤ (4 + Real.log (1 / δ) + Real.log Δ) * (1 / (y - n - α) ^ 2) := by gcongr; exact hF_unif n
          _ = (4 + Real.log (1 / δ) + Real.log Δ) * (1 / ((n : ℝ) + (α - y)) ^ 2) := by congr 2; ring
      have hb_s : Summable (fun n : ℤ => rescaledFDeriv θ Δ (n + α) / (y - n - α)) := by
        have h_inv_sq : Summable (fun n : ℤ => 1 / ((n : ℝ) + α) ^ 2) :=
          summable_inv_add_sq_of_ne_zero α (fun n h0 => by have := h_na_lb n; rw [h0, abs_zero] at this; linarith)
        let k0 : ℤ := ⌊y - α⌋
        have hk0_le : (k0 : ℝ) ≤ y - α := Int.floor_le (y - α)
        have hk0_lt : y - α < (k0 : ℝ) + 1 := Int.lt_floor_add_one (y - α)
        let d_min : ℝ := min |y - k0 - α| |y - (k0 + 1 : ℤ) - α|
        have hd_pos : 0 < d_min := lt_min (abs_pos.mpr (fun h => hlat ⟨k0, by linarith⟩))
          (abs_pos.mpr (fun h => hlat ⟨k0 + 1, by push_cast at h ⊢; linarith⟩))
        have h_dlb : ∀ n : ℤ, d_min ≤ |y - n - α| := by
          intro n
          rcases le_or_gt n k0 with hn | hn
          · have hn' : (n : ℝ) ≤ k0 := by exact_mod_cast hn
            have h1 : |y - k0 - α| ≤ |y - n - α| := by
              rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
            exact (min_le_left _ _).trans h1
          · have hn' : (k0 : ℝ) + 1 ≤ n := by exact_mod_cast hn
            have h1 : |y - (k0 + 1 : ℤ) - α| ≤ |y - n - α| := by
              push_cast; rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]; linarith
            exact (min_le_right _ _).trans h1
        refine ((h_inv_sq.mul_left (2 * Δ ^ 2 / (δ * d_min)))).of_norm_bounded fun n => ?_
        rw [Real.norm_eq_abs, abs_div]
        have hne : (n : ℝ) + α ≠ 0 := abs_pos.mp (lt_of_lt_of_le hδ0 (h_na_lb n))
        have hbm := rescaledFDeriv_mul_bound θ Δ (n + α) hΔ_pos hne
        rw [abs_mul] at hbm
        have hb_le : |rescaledFDeriv θ Δ (n + α)| ≤ (2 * Δ ^ 2 / δ) / ((n : ℝ) + α) ^ 2 := by
          rw [← le_div_iff₀' (lt_of_lt_of_le hδ0 (h_na_lb n))] at hbm
          calc |rescaledFDeriv θ Δ (n + α)| ≤ (2 * Δ ^ 2 / ((n : ℝ) + α) ^ 2) / |(n : ℝ) + α| := hbm
            _ ≤ (2 * Δ ^ 2 / ((n : ℝ) + α) ^ 2) / δ := div_le_div_of_nonneg_left (by positivity) hδ0 (h_na_lb n)
            _ = (2 * Δ ^ 2 / δ) / ((n : ℝ) + α) ^ 2 := by ring
        calc |rescaledFDeriv θ Δ (n + α)| / |y - n - α|
            ≤ ((2 * Δ ^ 2 / δ) / ((n : ℝ) + α) ^ 2) / d_min := div_le_div₀ (by positivity) hb_le hd_pos (h_dlb n)
          _ = (2 * Δ ^ 2 / (δ * d_min)) * (1 / ((n : ℝ) + α) ^ 2) := by ring
      let F5 : Finset ℤ := Finset.Icc (-2) 2
      let term : ℤ → ℝ := fun n =>
        (Real.sin (Real.pi * (y - α)) ^ 2 / Real.pi ^ 2) *
          (rescaledF θ Δ (n + α) / (y - n - α) ^ 2 + rescaledFDeriv θ Δ (n + α) / (y - n - α))
      have hterm_s : Summable term := (ha_s.add hb_s).mul_left _
      have h_eq_sum : (Real.sin (Real.pi * (y - α)) ^ 2 / Real.pi ^ 2) *
          ∑' n : ℤ, (rescaledF θ Δ (n + α) / (y - n - α) ^ 2 + rescaledFDeriv θ Δ (n + α) / (y - n - α)) =
          ∑' n : ℤ, term n := by
        rw [← tsum_mul_left]
      rw [h_eq_sum]
      have h_split : ∑' n : ℤ, term n = (∑ n ∈ F5, term n) + ∑' n : ℤ, (if n ∈ F5 then 0 else term n) := by
        have h_fin_s : Summable (fun n : ℤ => if n ∈ F5 then term n else 0) :=
          summable_of_ne_finset_zero (s := F5) (fun n hn => by simp [hn])
        have h_cofin_s : Summable (fun n : ℤ => if n ∈ F5 then 0 else term n) := by
          have : (fun n : ℤ => if n ∈ F5 then 0 else term n) = fun n => term n - (if n ∈ F5 then term n else 0) := by
            ext n; split_ifs <;> ring
          rw [this]; exact hterm_s.sub h_fin_s
        have h_add : (fun n : ℤ => (if n ∈ F5 then term n else 0) + (if n ∈ F5 then 0 else term n)) = term := by
          ext n; split_ifs <;> ring
        rw [← h_add, h_fin_s.tsum_add h_cofin_s]
        have h_t1 : ∑' n : ℤ, (if n ∈ F5 then term n else 0) = ∑ n ∈ F5, term n :=
          tsum_eq_sum (s := F5) (fun n hn => by simp [hn])
        rw [← h_t1]
        congr 1; ext n; split_ifs <;> ring
      have h_F5_bd : |∑ n ∈ F5, term n| ≤ 5 * (4 + Real.log (1 / δ) + Real.log Δ + 1 / δ + 2) := by
        have h_each : ∀ n ∈ F5, |term n| ≤ 4 + Real.log (1 / δ) + Real.log Δ + 1 / δ + 2 := by
          intro n _
          dsimp only [term]
          have h_sin_div : |Real.sin (Real.pi * (y - α)) / (Real.pi * (y - n - α))| ≤ 1 := by
            have heq : Real.sin (Real.pi * (y - α)) = (-1 : ℝ) ^ n * Real.sin (Real.pi * (y - n - α)) := by
              have h1 : Real.pi * (y - α) = Real.pi * (y - n - α) + (n : ℝ) * Real.pi := by ring
              rw [h1, Real.sin_add_int_mul_pi]
            rw [heq, abs_div, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul,
              abs_mul, abs_of_pos Real.pi_pos]
            have hyna_ne : y - n - α ≠ 0 := fun h => hlat ⟨n, by linarith⟩
            have hne : Real.pi * |y - n - α| ≠ 0 := mul_ne_zero Real.pi_ne_zero (abs_pos.mpr hyna_ne)
            rw [div_le_one (lt_of_le_of_ne (by positivity) hne.symm)]
            exact Real.abs_sin_le_abs
          have h_t1 : |(Real.sin (Real.pi * (y - α)) ^ 2 / Real.pi ^ 2) * (rescaledF θ Δ (n + α) / (y - n - α) ^ 2)| ≤
              4 + Real.log (1 / δ) + Real.log Δ := by
            have heq : (Real.sin (Real.pi * (y - α)) ^ 2 / Real.pi ^ 2) * (rescaledF θ Δ (n + α) / (y - n - α) ^ 2) =
                (Real.sin (Real.pi * (y - α)) / (Real.pi * (y - n - α))) ^ 2 * rescaledF θ Δ (n + α) := by field_simp [Real.pi_ne_zero]; ring
            rw [heq, abs_mul, abs_pow]
            have hsq : |Real.sin (Real.pi * (y - α)) / (Real.pi * (y - n - α))| ^ 2 ≤ 1 := by
              nlinarith [abs_nonneg (Real.sin (Real.pi * (y - α)) / (Real.pi * (y - n - α)))]
            calc |Real.sin (Real.pi * (y - α)) / (Real.pi * (y - n - α))| ^ 2 * |rescaledF θ Δ (n + α)|
                ≤ 1 * (4 + Real.log (1 / δ) + Real.log Δ) := by gcongr; exact hF_unif n
              _ = 4 + Real.log (1 / δ) + Real.log Δ := one_mul _
          have h_t2 : |(Real.sin (Real.pi * (y - α)) ^ 2 / Real.pi ^ 2) * (rescaledFDeriv θ Δ (n + α) / (y - n - α))| ≤
              1 / δ + 2 := by
            have heq : (Real.sin (Real.pi * (y - α)) ^ 2 / Real.pi ^ 2) * (rescaledFDeriv θ Δ (n + α) / (y - n - α)) =
                (Real.sin (Real.pi * (y - α)) / (Real.pi * (y - n - α))) *
                (Real.sin (Real.pi * (y - α)) / Real.pi) * rescaledFDeriv θ Δ (n + α) := by field_simp [Real.pi_ne_zero]; ring
            rw [heq, abs_mul, abs_mul]
            have h_s2 : |Real.sin (Real.pi * (y - α)) / Real.pi| ≤ 1 := by
              rw [abs_div, abs_of_pos Real.pi_pos, div_le_one Real.pi_pos]
              exact (Real.abs_sin_le_one _).trans (by linarith [Real.two_le_pi])
            have hFd_n : |rescaledFDeriv θ Δ (n + α)| ≤ 1 / δ + 2 := by
              have h1 := hFd_bd n
              have h2 : 1 / |(n : ℝ) + α| ≤ 1 / δ := div_le_div_of_nonneg_left zero_le_one hδ0 (h_na_lb n)
              have h3 : 2 / Δ ≤ 2 := div_le_self (by norm_num) hΔ_ge_1
              linarith
            calc |Real.sin (Real.pi * (y - α)) / (Real.pi * (y - n - α))| *
                  |Real.sin (Real.pi * (y - α)) / Real.pi| * |rescaledFDeriv θ Δ (n + α)|
                ≤ 1 * 1 * (1 / δ + 2) := by gcongr
              _ = 1 / δ + 2 := by ring
          calc |term n| ≤ |(Real.sin (Real.pi * (y - α)) ^ 2 / Real.pi ^ 2) * (rescaledF θ Δ (n + α) / (y - n - α) ^ 2)| +
                |(Real.sin (Real.pi * (y - α)) ^ 2 / Real.pi ^ 2) * (rescaledFDeriv θ Δ (n + α) / (y - n - α))| := by
                  dsimp only [term]; rw [mul_add]; exact abs_add_le _ _
            _ ≤ 4 + Real.log (1 / δ) + Real.log Δ + (1 / δ + 2) := add_le_add h_t1 h_t2
            _ = 4 + Real.log (1 / δ) + Real.log Δ + 1 / δ + 2 := by ring
        calc |∑ n ∈ F5, term n| ≤ ∑ n ∈ F5, |term n| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _n ∈ F5, (4 + Real.log (1 / δ) + Real.log Δ + 1 / δ + 2) := Finset.sum_le_sum h_each
          _ = 5 * (4 + Real.log (1 / δ) + Real.log Δ + 1 / δ + 2) := by
              rw [Finset.sum_const, show F5.card = 5 by decide, nsmul_eq_mul]; ring
      let F_mid : Finset ℤ := (Finset.Icc (-Int.floor Δ) (Int.floor Δ)).filter (fun n => n ∉ F5)
      let f_inv_sq : ℤ → ℝ := fun n => if n ∈ F5 then 0 else 1 / (n : ℝ) ^ 2
      obtain ⟨hf_inv_s, hf_inv_sum⟩ := diffB_f_inv_sum F5 rfl C_z rfl
      let f_mid : ℤ → ℝ := fun n => if n ∈ F_mid then 2 / Δ else 0
      have hf_mid_s : Summable f_mid := summable_of_ne_finset_zero (s := F_mid) (fun n hn => if_neg hn)
      have hf_mid_sum : ∑' n : ℤ, f_mid n ≤ 4 := by
        rw [tsum_eq_sum (s := F_mid) (fun n hn => by simp [f_mid, hn])]
        have h_sum_eq : ∑ n ∈ F_mid, f_mid n = ∑ _n ∈ F_mid, (2 / Δ) :=
          Finset.sum_congr rfl (fun n hn => if_pos hn)
        rw [h_sum_eq, Finset.sum_const, nsmul_eq_mul]
        have h_card : (F_mid.card : ℝ) ≤ 2 * Δ := by
          have h1 : F_mid ⊆ (Finset.Icc (-Int.floor Δ) (Int.floor Δ)).erase 0 := by
            intro n hn
            simp only [F_mid, Finset.mem_filter, Finset.mem_Icc] at hn
            refine Finset.mem_erase.mpr ⟨fun h0 => hn.2 (by subst h0; decide), Finset.mem_Icc.mpr hn.1⟩
          have h2 : F_mid.card ≤ (Finset.Icc (-Int.floor Δ) (Int.floor Δ)).card - 1 := by
            have h0_mem : (0 : ℤ) ∈ Finset.Icc (-Int.floor Δ) (Int.floor Δ) := by
              rw [Finset.mem_Icc]
              have : (0 : ℤ) ≤ Int.floor Δ := Int.floor_nonneg.mpr hΔ_pos.le
              omega
            rw [← Finset.card_erase_of_mem h0_mem]
            exact Finset.card_le_card h1
          have h3 : (Finset.Icc (-Int.floor Δ) (Int.floor Δ)).card = (Int.floor Δ + 1 - -Int.floor Δ).toNat := Int.card_Icc _ _
          have h4 : (F_mid.card : ℝ) ≤ 2 * (Int.floor Δ : ℝ) := by
            have : (0 : ℤ) ≤ Int.floor Δ := Int.floor_nonneg.mpr hΔ_pos.le
            exact_mod_cast (by omega : (F_mid.card : ℤ) ≤ 2 * Int.floor Δ)
          exact h4.trans (by linarith [Int.floor_le Δ])
        calc (F_mid.card : ℝ) * (2 / Δ) ≤ (2 * Δ) * (2 / Δ) := by gcongr
          _ = 4 := by field_simp [hΔ_pos.ne']; ring
      let K_tail : ℝ := (4 + Real.log (1 / δ) + Real.log Δ) * 9 + 24
      have h_tail_bd : ∀ n : ℤ, |if n ∈ F5 then 0 else term n| ≤
          (1 / Real.pi ^ 2) * (K_tail * f_inv_sq n + f_mid n) := by
        have hF_mid : ∀ n : ℤ, n ∉ F5 → |(n : ℝ)| ≤ Δ → n ∈ F_mid := by
          intro n hn h_leΔ
          simp only [F_mid, Finset.mem_filter, Finset.mem_Icc]
          refine ⟨⟨?_, ?_⟩, hn⟩
          · have : -Δ ≤ (n : ℝ) := by linarith [(abs_le.mp h_leΔ).1]
            have := Int.floor_le Δ
            exact_mod_cast (by linarith : (-Int.floor Δ : ℝ) - 1 < n) |> fun h' => Int.le_of_lt_add_one (by omega)
          · exact Int.le_floor.mpr (abs_le.mp h_leΔ).2
        exact diffB_tail_bound θ Δ α δ y hΔ_ge_1 hα hy hδ0 (min_le_right _ _) h_na_lb hF_unif hFd_bd
          F5 F_mid rfl hF_mid f_mid f_inv_sq (fun n hn => if_pos hn)
          (fun n => by dsimp only [f_mid]; split_ifs <;> positivity)
          (fun n hn => if_neg hn)
          (fun n => by dsimp only [f_inv_sq]; split_ifs <;> positivity)
      have h_cofin_s : Summable (fun n : ℤ => if n ∈ F5 then 0 else term n) := by
        have : (fun n : ℤ => if n ∈ F5 then 0 else term n) = fun n => term n - (if n ∈ F5 then term n else 0) := by
          ext n; split_ifs <;> ring
        rw [this]; exact hterm_s.sub (summable_of_ne_finset_zero (s := F5) (fun n hn => by simp [hn]))
      have h_tail_sum : |∑' n : ℤ, (if n ∈ F5 then 0 else term n)| ≤
          (1 / Real.pi ^ 2) * (((4 + Real.log (1 / δ) + Real.log Δ) * 9 + 24) * 8 * C_z + 4) := by
        have h_s_b : Summable (fun n : ℤ => (1 / Real.pi ^ 2) * (K_tail * f_inv_sq n + f_mid n)) :=
          ((hf_inv_s.mul_left K_tail).add hf_mid_s).mul_left _
        calc |∑' n : ℤ, (if n ∈ F5 then 0 else term n)|
            ≤ ∑' n : ℤ, |if n ∈ F5 then 0 else term n| := abs_tsum_le_tsum_abs h_cofin_s
          _ ≤ ∑' n : ℤ, (1 / Real.pi ^ 2) * (K_tail * f_inv_sq n + f_mid n) :=
              Summable.tsum_le_tsum h_tail_bd h_cofin_s.abs h_s_b
          _ = (1 / Real.pi ^ 2) * (K_tail * ∑' n : ℤ, f_inv_sq n + ∑' n : ℤ, f_mid n) := by
              rw [tsum_mul_left, Summable.tsum_add (hf_inv_s.mul_left K_tail) hf_mid_s, tsum_mul_left]
          _ ≤ (1 / Real.pi ^ 2) * (K_tail * (8 * C_z) + 4) := by
              gcongr
              dsimp only [K_tail]
              have := Real.log_nonneg ((one_le_div hδ0).mpr (by linarith [min_le_right (δ_star / 2) (1 / 2)]))
              positivity
          _ = (1 / Real.pi ^ 2) * (((4 + Real.log (1 / δ) + Real.log Δ) * 9 + 24) * 8 * C_z + 4) := by
              dsimp only [K_tail]; ring
      rw [h_split]
      refine (abs_add_le _ _).trans ?_
      have h_tot_le : 5 * (4 + Real.log (1 / δ) + Real.log Δ + 1 / δ + 2) +
          (1 / Real.pi ^ 2) * (((4 + Real.log (1 / δ) + Real.log Δ) * 9 + 24) * 8 * C_z + 4) ≤
          C_small_0 + C_small_1 * Real.log Δ := by
        dsimp only [C_small_0, C_small_1]; linarith
      exact (add_le_add h_F5_bd h_tail_sum).trans (h_tot_le.trans (h_to_Csmall C_small_0 C_small_1 le_rfl le_rfl))
  have h_large_x : ∀ x : ℝ, 1 ≤ |Δ * x| →
      |majorantM θ Δ α x - kernelK θ x| ≤ C_mid / (Δ * x) ^ 2 := by
    intro x hx1
    unfold majorantM
    have h_diff := (h_diff_bd Δ α hΔ_ge_Δ₂ hα hα_near hsumm_b hsum0).2 (Δ * x) hx1
    have h_j := hJ_up (Δ * x) hx1
    have h_sin1 : Real.sin (Real.pi * (Δ * x - α)) ^ 2 ≤ 1 := by
      have := Real.abs_sin_le_one (Real.pi * (Δ * x - α))
      nlinarith [sq_abs (Real.sin (Real.pi * (Δ * x - α)))]
    have h_exp_le : Δ ^ 2 * Real.exp (-2 * Real.pi * Δ) ≤ 1 := by
      have he := Real.pow_div_factorial_le_exp (2 * Real.pi * Δ) (by positivity) 2
      have hpi : 4 ≤ (2 * Real.pi) ^ 2 / 2 := by nlinarith [Real.two_le_pi]
      have h2 : Δ ^ 2 ≤ Real.exp (2 * Real.pi * Δ) := by nlinarith [sq_nonneg Δ]
      rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
      linarith
    have h_res : rescaledF θ Δ (Δ * x) = kernelK θ x := by
      unfold rescaledF; congr 1; field_simp [hΔ_pos.ne']
    rw [h_res] at h_diff
    calc |vaalerInterpolant θ Δ α (Δ * x) - kernelK θ x|
        ≤ |vaalerInterpolant θ Δ α (Δ * x) - kernelK θ x -
            Real.sin (Real.pi * (Δ * x - α)) ^ 2 * limitingJ (Δ * x) θ| +
          |Real.sin (Real.pi * (Δ * x - α)) ^ 2 * limitingJ (Δ * x) θ| := by
            simpa using abs_add_le (vaalerInterpolant θ Δ α (Δ * x) - kernelK θ x -
              Real.sin (Real.pi * (Δ * x - α)) ^ 2 * limitingJ (Δ * x) θ)
              (Real.sin (Real.pi * (Δ * x - α)) ^ 2 * limitingJ (Δ * x) θ)
      _ ≤ Real.sin (Real.pi * (Δ * x - α)) ^ 2 * (C_err1 * (Δ ^ 2 * Real.exp (-2 * Real.pi * Δ) + |α - α_star|) / (Δ * x) ^ 2) +
          Real.sin (Real.pi * (Δ * x - α)) ^ 2 * |limitingJ (Δ * x) θ| := by
            gcongr; rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      _ ≤ 1 * (C_err1 * (1 + δ_star / 2) / (Δ * x) ^ 2) + 1 * (C_up / (Δ * x) ^ 2) := by gcongr
      _ = C_mid / (Δ * x) ^ 2 := by dsimp only [C_mid]; ring
  have h_sup : ∀ x : ℝ, (1 + x ^ 2) * |majorantM θ Δ α x| ≤ C_sup * Real.log Δ := by
    intro x
    rcases le_or_gt |Δ * x| 1 with hx | hx
    · have hx_x : |x| ≤ 1 := by rw [abs_mul, abs_of_pos hΔ_pos] at hx; nlinarith [abs_nonneg x]
      have hx2 : 1 + x ^ 2 ≤ 2 := by rw [← sq_abs x]; nlinarith [abs_nonneg x]
      have hm := h_small_y (Δ * x) hx
      unfold majorantM
      calc (1 + x ^ 2) * |vaalerInterpolant θ Δ α (Δ * x)|
          ≤ 2 * (C_small * Real.log Δ) := mul_le_mul hx2 hm (abs_nonneg _) zero_le_two
        _ = (2 * C_small) * Real.log Δ := by ring
        _ ≤ C_sup * Real.log Δ := by gcongr; exact le_max_left _ _
    · have h_m_diff := h_large_x x hx.le
      have hx_ne : x ≠ 0 := by intro h0; subst h0; simp at hx; linarith
      rcases le_or_gt 1 |x| with hx1 | hx1
      · have hK := kernelK_bound_large θ hx1
        have hM : |majorantM θ Δ α x| ≤ (C_mid + 4) / x ^ 2 := by
          have htri : |majorantM θ Δ α x| ≤ |majorantM θ Δ α x - kernelK θ x| + |kernelK θ x| := by
            simpa using abs_add_le (majorantM θ Δ α x - kernelK θ x) (kernelK θ x)
          have h_dx : C_mid / (Δ * x) ^ 2 ≤ C_mid / x ^ 2 := by gcongr; nlinarith [sq_nonneg x]
          linarith [show (C_mid + 4) / x ^ 2 = C_mid / x ^ 2 + 4 / x ^ 2 by ring]
        have hx2 : 1 + x ^ 2 ≤ 2 * x ^ 2 := by rw [← sq_abs x]; nlinarith
        calc (1 + x ^ 2) * |majorantM θ Δ α x|
            ≤ (2 * x ^ 2) * ((C_mid + 4) / x ^ 2) := mul_le_mul hx2 hM (abs_nonneg _) (by positivity)
          _ = 2 * C_mid + 8 := by field_simp [hx_ne]; ring
          _ ≤ ((2 * C_mid + 8) / Real.log 2 + 2) * Real.log Δ := by
              have h1 : 1 ≤ Real.log Δ / Real.log 2 := (one_le_div hlog2_pos).mpr hlogΔ_ge
              calc 2 * C_mid + 8 = (2 * C_mid + 8) * 1 := (mul_one _).symm
                _ ≤ (2 * C_mid + 8) * (Real.log Δ / Real.log 2) := by gcongr; positivity
                _ = ((2 * C_mid + 8) / Real.log 2) * Real.log Δ := by ring
                _ ≤ ((2 * C_mid + 8) / Real.log 2 + 2) * Real.log Δ := by gcongr; linarith
          _ ≤ C_sup * Real.log Δ := by gcongr; exact le_max_right _ _
      · have h_abs_pos : 0 < |x| := abs_pos.mpr hx_ne
        have hK := kernelK_bound_small θ h_abs_pos hx1.le
        have h_log_x : Real.log (1 / |x|) ≤ Real.log Δ := by
          rw [abs_mul, abs_of_pos hΔ_pos] at hx
          have h1 : 1 / |x| < Δ := by rw [div_lt_iff₀ h_abs_pos]; linarith
          exact Real.log_le_log (by positivity) h1.le
        have h_dx : 1 ≤ (Δ * x) ^ 2 := by rw [← sq_abs (Δ * x)]; nlinarith
        have hM : |majorantM θ Δ α x| ≤ C_mid + 4 + Real.log Δ := by
          have htri : |majorantM θ Δ α x| ≤ |majorantM θ Δ α x - kernelK θ x| + |kernelK θ x| := by
            simpa using abs_add_le (majorantM θ Δ α x - kernelK θ x) (kernelK θ x)
          have h1 : C_mid / (Δ * x) ^ 2 ≤ C_mid := div_le_self (by positivity) h_dx
          linarith
        have hx2 : 1 + x ^ 2 ≤ 2 := by rw [← sq_abs x]; nlinarith [abs_nonneg x]
        calc (1 + x ^ 2) * |majorantM θ Δ α x|
            ≤ 2 * (C_mid + 4 + Real.log Δ) := mul_le_mul hx2 hM (abs_nonneg _) zero_le_two
          _ = (2 * C_mid + 8) + 2 * Real.log Δ := by ring
          _ ≤ ((2 * C_mid + 8) / Real.log 2 + 2) * Real.log Δ := by
              have h1 : 1 ≤ Real.log Δ / Real.log 2 := (one_le_div hlog2_pos).mpr hlogΔ_ge
              have h2 : 2 * C_mid + 8 ≤ ((2 * C_mid + 8) / Real.log 2) * Real.log Δ := by
                calc 2 * C_mid + 8 = (2 * C_mid + 8) * 1 := (mul_one _).symm
                  _ ≤ (2 * C_mid + 8) * (Real.log Δ / Real.log 2) := by gcongr; positivity
                  _ = ((2 * C_mid + 8) / Real.log 2) * Real.log Δ := by ring
              linarith
          _ ≤ C_sup * Real.log Δ := by gcongr; exact le_max_right _ _
  have h_cont : Continuous (fun x : ℝ => majorantM θ Δ α x) := by
    obtain ⟨⟨h_diff, _⟩, h_re⟩ := majorantEntire_props θ Δ α hΔ_ge_1 hα hsumm_b
    have h_eq : (fun x : ℝ => majorantM θ Δ α x) = fun x : ℝ => (majorantEntire θ Δ α x).re := by
      ext x; exact (h_re x).2.symm
    rw [h_eq]
    exact Complex.continuous_re.comp (h_diff.continuous.comp Complex.continuous_ofReal)
  have h_int : Integrable (fun x : ℝ => majorantM θ Δ α x) := by
    refine (integrable_inv_one_add_sq.const_mul (C_sup * Real.log Δ)).mono' h_cont.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, ← le_div_iff₀' (by positivity : 0 < 1 + x ^ 2)]
    simpa [div_eq_mul_inv] using h_sup x
  refine ⟨h_sup, h_int, ?_⟩
  have h_abs_int : Integrable (fun x : ℝ => |majorantM θ Δ α x|) := h_int.abs
  let S1 : Set ℝ := Set.Icc (-1 / Δ) (1 / Δ)
  let S2 : Set ℝ := Set.Ioo (-1) (-1 / Δ) ∪ Set.Ioo (1 / Δ) 1
  let S3 : Set ℝ := (Set.Ioo (-1 : ℝ) 1)ᶜ
  have h_s12 : IntegrableOn (fun x => |majorantM θ Δ α x|) S1 := h_abs_int.integrableOn
  have h_s2 : IntegrableOn (fun x => |majorantM θ Δ α x|) S2 := h_abs_int.integrableOn
  have h_s3 : IntegrableOn (fun x => |majorantM θ Δ α x|) S3 := h_abs_int.integrableOn
  have h_int1 : ∫ x in S1, |majorantM θ Δ α x| ≤ 2 * C_small := by
    have h_c : ∫ _ in S1, C_small * Real.log Δ = (2 / Δ) * (C_small * Real.log Δ) := by
      dsimp only [S1]
      rw [setIntegral_const, Real.volume_real_Icc_of_le (by rw [neg_div]; linarith [show 0 < 1 / Δ by positivity]),
        smul_eq_mul]
      ring
    have h_mono : ∫ x in S1, |majorantM θ Δ α x| ≤ ∫ _ in S1, C_small * Real.log Δ := by
      refine setIntegral_mono_on h_s12 (continuousOn_const.integrableOn_Icc) measurableSet_Icc fun x hx => ?_
      have h_dx : |Δ * x| ≤ 1 := by
        rw [abs_mul, abs_of_pos hΔ_pos, abs_le]
        have h1 := hx.1; have h2 := hx.2
        rw [neg_div] at h1
        have h3 : -1 ≤ Δ * x := by rw [← div_le_iff₀' hΔ_pos]; linarith
        have h4 : Δ * x ≤ 1 := by rw [← le_div_iff₀' hΔ_pos]; linarith
        exact ⟨h3, h4⟩
      exact h_small_y (Δ * x) h_dx
    have h_log_le : Real.log Δ / Δ ≤ 1 := by
      rw [div_le_one hΔ_pos]
      linarith [Real.log_le_sub_one_of_pos hΔ_pos]
    calc ∫ x in S1, |majorantM θ Δ α x| ≤ (2 / Δ) * (C_small * Real.log Δ) := h_mono.trans_eq h_c
      _ = 2 * C_small * (Real.log Δ / Δ) := by ring
      _ ≤ 2 * C_small * 1 := by gcongr
      _ = 2 * C_small := mul_one _
  have h_int2 : ∫ x in S2, |majorantM θ Δ α x| ≤ 2 * C_mid + ∫ x in Set.Ioo (-1 : ℝ) 1, |kernelK θ x| := by
    let g2 : ℝ → ℝ := fun x => C_mid / (Δ * x) ^ 2 + |kernelK θ x|
    have hg2_1 : IntegrableOn (fun x => C_mid / (Δ * x) ^ 2) S2 := by
      refine ((continuousOn_const.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self).union (continuousOn_const.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self) : IntegrableOn (fun _ : ℝ => C_mid) S2 volume).mono'
        (by fun_prop) ?_
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.union measurableSet_Ioo)] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h_dx : 1 ≤ (Δ * x) ^ 2 := by
        rcases hx with hx | hx
        · have : Δ * x < -1 := by rw [← lt_div_iff₀' hΔ_pos]; linarith [hx.2]
          nlinarith
        · have : 1 < Δ * x := by rw [← div_lt_iff₀' hΔ_pos]; linarith [hx.1]
          nlinarith
      exact div_le_self (by positivity) h_dx
    have hg2_int : IntegrableOn g2 S2 := hg2_1.add (kernelK_integrable_sl θ).abs.integrableOn
    have h_mono : ∫ x in S2, |majorantM θ Δ α x| ≤ ∫ x in S2, g2 x := by
      refine setIntegral_mono_on h_s2 hg2_int (measurableSet_Ioo.union measurableSet_Ioo) fun x hx => ?_
      have h_dx : 1 ≤ |Δ * x| := by
        rcases hx with hx | hx
        · have : Δ * x < -1 := by rw [← lt_div_iff₀' hΔ_pos]; linarith [hx.2]
          rw [abs_of_neg (by linarith)]; linarith
        · have : 1 < Δ * x := by rw [← div_lt_iff₀' hΔ_pos]; linarith [hx.1]
          rw [abs_of_pos (by linarith)]; linarith
      have h_tri : |majorantM θ Δ α x| ≤ |majorantM θ Δ α x - kernelK θ x| + |kernelK θ x| := by
        simpa using abs_add_le (majorantM θ Δ α x - kernelK θ x) (kernelK θ x)
      exact h_tri.trans (add_le_add_right (h_large_x x h_dx) _)
    have h_1_div_le : 1 / Δ < 1 := by rw [div_lt_one hΔ_pos]; linarith
    have h_c_pos : ∫ x in Set.Ioo (1 / Δ) 1, C_mid / (Δ * x) ^ 2 ≤ C_mid := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le h_1_div_le.le]
      have h_eq : ∫ x in (1 / Δ)..1, C_mid / (Δ * x) ^ 2 = (C_mid / Δ ^ 2) * ∫ x in (1 / Δ)..1, 1 / x ^ 2 := by
        rw [← intervalIntegral.integral_const_mul]; congr 1; ext x; ring
      have h_ftc : ∫ x in (1 / Δ)..1, (1 : ℝ) / x ^ 2 = Δ - 1 := by
        have hd : ∀ x ∈ Set.uIcc (1 / Δ) 1, HasDerivAt (fun t : ℝ => -1 / t) (1 / x ^ 2) x := by
          intro x hx
          have hx_ne : x ≠ 0 := by
            rw [Set.uIcc_of_le h_1_div_le.le] at hx
            linarith [hx.1, show 0 < 1 / Δ by positivity]
          have h := (hasDerivAt_const x (-1 : ℝ)).div (hasDerivAt_id x) hx_ne
          refine h.congr_deriv ?_; ring
        have hc : ContinuousOn (fun x : ℝ => (1 : ℝ) / x ^ 2) (Set.uIcc (1 / Δ) 1) := by
          refine continuousOn_const.div (continuousOn_id.pow 2) fun x hx => ?_
          rw [Set.uIcc_of_le h_1_div_le.le] at hx
          exact pow_ne_zero 2 (by linarith [hx.1, show 0 < 1 / Δ by positivity])
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
        field_simp [hΔ_pos.ne']; ring
      rw [h_eq, h_ftc]
      calc (C_mid / Δ ^ 2) * (Δ - 1) ≤ (C_mid / Δ ^ 2) * Δ := by gcongr; linarith
        _ = C_mid / Δ := by field_simp [hΔ_pos.ne']
        _ ≤ C_mid := div_le_self (by positivity) hΔ_ge_1
    have h_c_neg : ∫ x in Set.Ioo (-1) (-1 / Δ), C_mid / (Δ * x) ^ 2 ≤ C_mid := by
      have h_emb := (Homeomorph.neg ℝ).measurableEmbedding
      have h_pre : (Homeomorph.neg ℝ) ⁻¹' Set.Ioo (-1) (-1 / Δ) = Set.Ioo (1 / Δ) 1 := by
        ext x; simp only [Set.mem_preimage, Homeomorph.neg_apply, Set.mem_Ioo]; rw [neg_div]; constructor <;> intro ⟨a, b⟩ <;> exact ⟨by linarith, by linarith⟩
      rw [← (Measure.measurePreserving_neg volume).setIntegral_preimage_emb h_emb (fun x => C_mid / (Δ * x) ^ 2) (Set.Ioo (-1) (-1 / Δ)), h_pre]
      simpa [mul_neg, neg_sq] using h_c_pos
    have h_s2_c : ∫ x in S2, C_mid / (Δ * x) ^ 2 ≤ 2 * C_mid := by
      dsimp only [S2]
      rw [setIntegral_union ((Set.disjoint_iff.mpr fun x ⟨hx1, hx2⟩ => by rw [neg_div] at hx1; linarith only [hx1.2, hx2.1, hΔ_pos]))
        measurableSet_Ioo (hg2_1.mono_set Set.subset_union_left) (hg2_1.mono_set Set.subset_union_right)]
      linarith
    have h_s2_k : ∫ x in S2, |kernelK θ x| ≤ ∫ x in Set.Ioo (-1 : ℝ) 1, |kernelK θ x| := by
      refine setIntegral_mono_set (kernelK_integrable_sl θ).abs.integrableOn (Eventually.of_forall fun _ => abs_nonneg _) ?_
      refine Eventually.of_forall fun x hx => ?_
      rcases hx with hx | hx
      · exact ⟨hx.1, by linarith [hx.2, show 0 < 1 / Δ by positivity]⟩
      · exact ⟨by linarith [hx.1, show 0 < 1 / Δ by positivity], hx.2⟩
    calc ∫ x in S2, |majorantM θ Δ α x| ≤ ∫ x in S2, g2 x := h_mono
      _ = (∫ x in S2, C_mid / (Δ * x) ^ 2) + (∫ x in S2, |kernelK θ x|) :=
          integral_add hg2_1 ((kernelK_integrable_sl θ).abs.integrableOn)
      _ ≤ 2 * C_mid + ∫ x in Set.Ioo (-1 : ℝ) 1, |kernelK θ x| := add_le_add h_s2_c h_s2_k
  have h_int3 : ∫ x in S3, |majorantM θ Δ α x| ≤ (2 * C_mid + 8) * Real.pi := by
    have h_univ : ∫ x : ℝ, (2 * C_mid + 8) * (1 / (1 + x ^ 2)) = (2 * C_mid + 8) * Real.pi := by
      rw [integral_const_mul, integral_inv_one_add_sq]
    have h_mono1 : ∫ x in S3, |majorantM θ Δ α x| ≤ ∫ x in S3, (2 * C_mid + 8) * (1 / (1 + x ^ 2)) := by
      refine setIntegral_mono_on h_s3 ((integrable_inv_one_add_sq.const_mul (2 * C_mid + 8)).integrableOn)
        measurableSet_Ioo.compl fun x hx => ?_
      have hx1 : 1 ≤ |x| := by
        by_contra h; rw [not_le, abs_lt] at h; exact hx h
      have h_dx : 1 ≤ |Δ * x| := by rw [abs_mul, abs_of_pos hΔ_pos]; nlinarith
      have h_m_diff := h_large_x x h_dx
      have hK := kernelK_bound_large θ hx1
      have hM : |majorantM θ Δ α x| ≤ (C_mid + 4) / x ^ 2 := by
        have htri : |majorantM θ Δ α x| ≤ |majorantM θ Δ α x - kernelK θ x| + |kernelK θ x| := by
          simpa using abs_add_le (majorantM θ Δ α x - kernelK θ x) (kernelK θ x)
        have h_dx2 : C_mid / (Δ * x) ^ 2 ≤ C_mid / x ^ 2 := by gcongr; nlinarith [sq_nonneg x]
        linarith [show (C_mid + 4) / x ^ 2 = C_mid / x ^ 2 + 4 / x ^ 2 by ring]
      have hx2 : 1 + x ^ 2 ≤ 2 * x ^ 2 := by rw [← sq_abs x]; nlinarith
      calc |majorantM θ Δ α x| ≤ (C_mid + 4) / x ^ 2 := hM
        _ = (2 * C_mid + 8) / (2 * x ^ 2) := by ring
        _ ≤ (2 * C_mid + 8) / (1 + x ^ 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hx2
        _ = (2 * C_mid + 8) * (1 / (1 + x ^ 2)) := by ring
    have h_mono2 : ∫ x in S3, (2 * C_mid + 8) * (1 / (1 + x ^ 2)) ≤ ∫ x : ℝ, (2 * C_mid + 8) * (1 / (1 + x ^ 2)) :=
      setIntegral_le_integral (integrable_inv_one_add_sq.const_mul (2 * C_mid + 8)) (Eventually.of_forall fun _ => by positivity)
    linarith
  have h_tot_split : ∫ x : ℝ, |majorantM θ Δ α x| ≤
      (∫ x in S1, |majorantM θ Δ α x|) + (∫ x in S2, |majorantM θ Δ α x|) + (∫ x in S3, |majorantM θ Δ α x|) := by
    have h_u : Set.univ ⊆ S1 ∪ S2 ∪ S3 := by
      intro x _
      by_cases hx1 : |x| < 1
      · by_cases hx2 : |x| ≤ 1 / Δ
        · exact Or.inl (Or.inl ⟨by rw [neg_div]; linarith [(abs_le.mp hx2).1], (abs_le.mp hx2).2⟩)
        · have hx2' : 1 / Δ < |x| := not_le.mp hx2
          rcases lt_or_gt_of_ne (abs_pos.mp (by linarith [show 0 < 1 / Δ by positivity])) with h | h
          · exact Or.inl (Or.inr (Or.inl ⟨(abs_lt.mp hx1).1, by rw [neg_div, abs_of_neg h] at hx2'; linarith⟩))
          · exact Or.inl (Or.inr (Or.inr ⟨by rw [abs_of_pos h] at hx2'; exact hx2', (abs_lt.mp hx1).2⟩))
      · exact Or.inr (fun h => hx1 (abs_lt.mpr h))
    have h_disj12 : Disjoint S1 S2 := by
      rw [Set.disjoint_iff]
      intro x ⟨hx1, hx2⟩
      simp only [S1, S2, Set.mem_Icc, Set.mem_union, Set.mem_Ioo] at hx1 hx2
      rcases hx2 with hx2 | hx2
      · rw [neg_div] at hx1; linarith only [hx1.1, hx2.2]
      · linarith only [hx1.2, hx2.1]
    have h_disj123 : Disjoint (S1 ∪ S2) S3 := by
      rw [Set.disjoint_iff]
      intro x ⟨hx12, hx3⟩
      apply hx3
      simp only [S1, S2, Set.mem_union, Set.mem_Icc, Set.mem_Ioo] at hx12
      have h_1_div_lt : 1 / Δ < 1 := by rw [div_lt_one hΔ_pos]; linarith
      rcases hx12 with hx1 | (hx2 | hx2)
      · rw [neg_div] at hx1; exact ⟨by linarith only [hx1.1, h_1_div_lt], by linarith only [hx1.2, h_1_div_lt]⟩
      · exact ⟨hx2.1, by linarith only [hx2.2, h_1_div_lt]⟩
      · exact ⟨by linarith only [hx2.1, h_1_div_lt], hx2.2⟩
    have h123 := setIntegral_mono_set h_abs_int (Eventually.of_forall fun _ => abs_nonneg _) (Eventually.of_forall fun x _ => h_u (Set.mem_univ x))
    calc ∫ x : ℝ, |majorantM θ Δ α x| = ∫ x in Set.univ, |majorantM θ Δ α x| := setIntegral_univ.symm
      _ ≤ ∫ x in S1 ∪ S2 ∪ S3, |majorantM θ Δ α x| := h123
      _ = (∫ x in S1 ∪ S2, |majorantM θ Δ α x|) + ∫ x in S3, |majorantM θ Δ α x| :=
          setIntegral_union h_disj123 measurableSet_Ioo.compl (h_s12.union h_s2) h_s3
      _ = (∫ x in S1, |majorantM θ Δ α x|) + (∫ x in S2, |majorantM θ Δ α x|) + ∫ x in S3, |majorantM θ Δ α x| := by
          rw [setIntegral_union h_disj12 (measurableSet_Ioo.union measurableSet_Ioo) h_s12 h_s2]
  linarith


end PolarEvaluation
