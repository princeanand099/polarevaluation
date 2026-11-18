import PolarEvaluation.ShiftedLatticePositivityB

noncomputable section

open Complex Real MeasureTheory Filter Topology
open scoped FourierTransform

namespace PolarEvaluation

noncomputable def sincPi (u : ℂ) : ℂ :=
  if u = 0 then 1 else Complex.sin (Real.pi * u) / (Real.pi * u)

lemma sincPi_ofReal (x : ℝ) :
    sincPi x = ((if x = 0 then 1 else Real.sin (Real.pi * x) / (Real.pi * x) : ℝ) : ℂ) := by
  dsimp only [sincPi]
  split_ifs with h0 h1
  · simp
  · exfalso; exact h0 (by exact_mod_cast h1)
  · exfalso; exact h1 (by exact_mod_cast h0)
  · rw [show (Real.pi : ℂ) * (x : ℂ) = ((Real.pi * x : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_sin]
    push_cast; ring

lemma complex_cos_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖Complex.cos w - 1‖ ≤ Real.exp 1 * ‖w‖ := by
  let f : ℝ → ℂ := fun t => Complex.cos (t * w) - 1
  have hf_d : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (-w * Complex.sin (t * w)) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * w) w t := by
      simpa using (hasDerivAt_id t).ofReal_comp.mul_const w
    exact ((h1.cos).sub_const 1).congr_deriv (by ring)
  have hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖-w * Complex.sin (t * w)‖ ≤ Real.exp 1 * ‖w‖ := by
    intro t ht
    rw [norm_mul, norm_neg]
    have hsin : ‖Complex.sin (t * w)‖ ≤ Real.exp 1 := by
      have hsin_def : ∀ z : ℂ, Complex.sin z = (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * Complex.I / 2 := by intro z; unfold Complex.sin; ring_nf
      rw [hsin_def]
      have h1 : ‖Complex.exp (-(t * w) * Complex.I)‖ ≤ Real.exp 1 := by
        rw [Complex.norm_exp]
        refine Real.exp_le_exp.mpr ?_
        calc (-(t * w) * Complex.I).re ≤ ‖-(t * w) * Complex.I‖ := Complex.re_le_norm _
          _ = t * ‖w‖ := by rw [norm_mul, norm_neg, Complex.norm_I, mul_one, norm_mul,
              Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
          _ ≤ 1 * 1 := mul_le_mul ht.2 hw (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      have h2 : ‖Complex.exp ((t * w) * Complex.I)‖ ≤ Real.exp 1 := by
        rw [Complex.norm_exp]
        refine Real.exp_le_exp.mpr ?_
        calc ((t * w) * Complex.I).re ≤ ‖(t * w) * Complex.I‖ := Complex.re_le_norm _
          _ = t * ‖w‖ := by rw [norm_mul, Complex.norm_I, mul_one, norm_mul,
              Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
          _ ≤ 1 * 1 := mul_le_mul ht.2 hw (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      calc ‖(Complex.exp (-(t * w) * Complex.I) - Complex.exp (t * w * Complex.I)) * Complex.I / 2‖
          = ‖Complex.exp (-(t * w) * Complex.I) - Complex.exp (t * w * Complex.I)‖ / 2 := by
            rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
        _ ≤ (‖Complex.exp (-(t * w) * Complex.I)‖ + ‖Complex.exp (t * w * Complex.I)‖) / 2 := by
            gcongr; exact norm_sub_le _ _
        _ ≤ (Real.exp 1 + Real.exp 1) / 2 := by gcongr
        _ = Real.exp 1 := by ring
    calc ‖w‖ * ‖Complex.sin (t * w)‖ ≤ ‖w‖ * Real.exp 1 := by gcongr
      _ = Real.exp 1 * ‖w‖ := mul_comm _ _
  have hmvt := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun t ht => hf_d t ht) hbd (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
  simpa [f] using hmvt

lemma complex_sin_sub_id_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖Complex.sin w - w‖ ≤ Real.exp 1 * ‖w‖ ^ 2 := by
  let f : ℝ → ℂ := fun t => Complex.sin (t * w) - t * w
  have hf_d : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (w * (Complex.cos (t * w) - 1)) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * w) w t := by
      simpa using (hasDerivAt_id t).ofReal_comp.mul_const w
    exact ((h1.sin).sub h1).congr_deriv (by ring)
  have hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖w * (Complex.cos (t * w) - 1)‖ ≤ Real.exp 1 * ‖w‖ ^ 2 := by
    intro t ht
    rw [norm_mul]
    have htw : ‖(t : ℂ) * w‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_one₀ ht.2 (norm_nonneg _) hw
    have hcos := complex_cos_sub_one_le htw
    have htw_le : ‖(t : ℂ) * w‖ ≤ ‖w‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    calc ‖w‖ * ‖Complex.cos (t * w) - 1‖ ≤ ‖w‖ * (Real.exp 1 * ‖(t : ℂ) * w‖) := by gcongr
      _ ≤ ‖w‖ * (Real.exp 1 * ‖w‖) := by gcongr
      _ = Real.exp 1 * ‖w‖ ^ 2 := by ring
  have hmvt := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun t ht => hf_d t ht) hbd (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
  simpa [f] using hmvt

lemma differentiable_sincPi : Differentiable ℂ sincPi := by
  intro u
  by_cases hu : u = 0
  · subst hu
    have h_deriv : HasDerivAt sincPi 0 0 := by
      rw [hasDerivAt_iff_tendsto_slope_zero, tendsto_zero_iff_norm_tendsto_zero]
      have h_bnd : ∀ᶠ t : ℂ in 𝓝[≠] 0, ‖t⁻¹ • (sincPi t - sincPi 0)‖ ≤ Real.pi * Real.exp 1 * ‖t‖ := by
        filter_upwards [eventually_nhdsWithin_of_forall fun t (ht : t ≠ 0) => ht,
          nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) (by positivity : (0 : ℝ) < 1 / Real.pi))] with t ht hball
        have ht_norm : ‖Real.pi * t‖ ≤ 1 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
          rw [Metric.mem_ball, dist_zero_right] at hball
          nlinarith [Real.pi_pos]
        have hs0 : sincPi 0 = 1 := by simp [sincPi]
        have hst : sincPi t = Complex.sin (Real.pi * t) / (Real.pi * t) := by
          dsimp only [sincPi]; simp [ht]
        rw [hs0, hst, smul_eq_mul, norm_mul, norm_inv]
        have h_eq : Complex.sin (Real.pi * t) / (Real.pi * t) - 1 =
            (Complex.sin (Real.pi * t) - Real.pi * t) / (Real.pi * t) := by
          have hpt : (Real.pi : ℂ) * t ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) ht
          field_simp [hpt]
        rw [h_eq, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        have hsin := complex_sin_sub_id_le ht_norm
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at hsin
        calc ‖t‖⁻¹ * (‖Complex.sin (Real.pi * t) - Real.pi * t‖ / (Real.pi * ‖t‖))
            ≤ ‖t‖⁻¹ * ((Real.exp 1 * (Real.pi * ‖t‖) ^ 2) / (Real.pi * ‖t‖)) := by gcongr
          _ = Real.pi * Real.exp 1 * ‖t‖ := by
              have htn : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
              field_simp [htn, Real.pi_ne_zero]; ring
      have h_lim : Tendsto (fun t : ℂ => Real.pi * Real.exp 1 * ‖t‖) (𝓝[≠] 0) (nhds 0) := by
        have h1 : Tendsto (fun t : ℂ => Real.pi * Real.exp 1 * ‖t‖) (𝓝 0) (nhds (Real.pi * Real.exp 1 * 0)) :=
          tendsto_const_nhds.mul continuous_norm.continuousAt
        simpa using h1.mono_left nhdsWithin_le_nhds
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim
        (Eventually.of_forall fun _ => norm_nonneg _) h_bnd
    exact h_deriv.differentiableAt
  · have h_ev : sincPi =ᶠ[𝓝 u] fun w => Complex.sin (Real.pi * w) / (Real.pi * w) := by
      filter_upwards [isOpen_ne.mem_nhds hu] with w hw
      dsimp only [sincPi]; simp [hw]
    refine DifferentiableAt.congr_of_eventuallyEq ?_ h_ev
    refine (Complex.differentiableAt_sin.comp u (differentiableAt_id.const_mul _)).div
      (differentiableAt_id.const_mul _) (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) hu)

lemma sincPi_bound (u : ℂ) :
    ‖sincPi u‖ ≤ Real.exp (Real.pi * |u.im| + 2) ∧
    ‖u * sincPi u ^ 2‖ ≤ Real.exp (2 * Real.pi * |u.im| + 4) := by
  have hsin_bd : ∀ w : ℂ, ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
    intro w
    have hsin_def : ∀ z : ℂ, Complex.sin z = (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * Complex.I / 2 := by intro z; unfold Complex.sin; ring_nf
    rw [hsin_def]
    have h1 : ‖Complex.exp (-w * Complex.I)‖ ≤ Real.exp |w.im| := by
      rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (by
        simp [Complex.mul_re]; exact le_abs_self _)
    have h2 : ‖Complex.exp (w * Complex.I)‖ ≤ Real.exp |w.im| := by
      rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (by
        simp [Complex.mul_re]; exact neg_le_abs _)
    calc ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2‖
        = ‖Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)‖ / 2 := by
          rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
      _ ≤ (‖Complex.exp (-w * Complex.I)‖ + ‖Complex.exp (w * Complex.I)‖) / 2 := by
          gcongr; exact norm_sub_le _ _
      _ ≤ (Real.exp |w.im| + Real.exp |w.im|) / 2 := by gcongr
      _ = Real.exp |w.im| := by ring
  have hpi_im : |(Real.pi * u).im| = Real.pi * |u.im| := by
    simp [abs_mul, abs_of_pos Real.pi_pos]
  have h1 : ‖sincPi u‖ ≤ Real.exp (Real.pi * |u.im| + 2) := by
    by_cases h0 : u = 0
    · subst h0; simp [sincPi]; exact Real.one_le_exp (by norm_num)
    · have hpiu : ‖Real.pi * u‖ = Real.pi * ‖u‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      by_cases hpi1 : Real.pi * ‖u‖ ≤ 1
      · have hs := complex_sin_sub_id_le (by rwa [hpiu])
        have h_eq : sincPi u = 1 + (Complex.sin (Real.pi * u) - Real.pi * u) / (Real.pi * u) := by
          dsimp only [sincPi]; simp only [if_neg h0]
          have hne : (Real.pi : ℂ) * u ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) h0
          field_simp [hne]; ring
        rw [h_eq]
        refine (norm_add_le _ _).trans ?_
        rw [norm_one, norm_div, hpiu]
        have h_pos : 0 < Real.pi * ‖u‖ := mul_pos Real.pi_pos (norm_pos_iff.mpr h0)
        have hexp2 : 1 + Real.exp 1 ≤ Real.exp 2 := by
          have he : Real.exp 1 ≥ 2 := by linarith [Real.exp_one_gt_d9]
          have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
          nlinarith
        calc 1 + ‖Complex.sin (Real.pi * u) - Real.pi * u‖ / (Real.pi * ‖u‖)
            ≤ 1 + (Real.exp 1 * (Real.pi * ‖u‖) ^ 2) / (Real.pi * ‖u‖) := by gcongr
          _ = 1 + Real.exp 1 * (Real.pi * ‖u‖) := by field_simp [h_pos.ne']; ring
          _ ≤ 1 + Real.exp 1 * 1 := by gcongr
          _ ≤ Real.exp 2 := by linarith
          _ ≤ Real.exp (Real.pi * |u.im| + 2) := Real.exp_le_exp.mpr (by linarith [abs_nonneg u.im, Real.pi_pos])
      · have hpi1' : 1 < Real.pi * ‖u‖ := not_le.mp hpi1
        dsimp only [sincPi]; simp only [if_neg h0]
        rw [norm_div, hpiu]
        calc ‖Complex.sin (Real.pi * u)‖ / (Real.pi * ‖u‖)
            ≤ Real.exp (Real.pi * |u.im|) / 1 :=
              div_le_div₀ (by positivity) (by rw [← hpi_im]; exact hsin_bd _) zero_lt_one hpi1'.le
          _ = Real.exp (Real.pi * |u.im|) := div_one _
          _ ≤ Real.exp (Real.pi * |u.im| + 2) := Real.exp_le_exp.mpr (by linarith)
  refine ⟨h1, ?_⟩
  by_cases hu : ‖u‖ ≤ 1
  · calc ‖u * sincPi u ^ 2‖ = ‖u‖ * ‖sincPi u‖ ^ 2 := by rw [norm_mul, norm_pow]
      _ ≤ 1 * (Real.exp (Real.pi * |u.im| + 2)) ^ 2 := by gcongr; exact h1
      _ = Real.exp (2 * Real.pi * |u.im| + 4) := by rw [one_mul, ← Real.exp_nat_mul]; ring_nf
  · have hu' : 1 < ‖u‖ := not_le.mp hu
    have h0 : u ≠ 0 := norm_ne_zero_iff.mp (by linarith)
    dsimp only [sincPi]; simp only [if_neg h0]
    have heq : u * (Complex.sin (Real.pi * u) / (Real.pi * u)) ^ 2 =
        Complex.sin (Real.pi * u) ^ 2 / ((Real.pi ^ 2 : ℂ) * u) := by
      have hne : (Real.pi : ℂ) * u ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) h0
      field_simp [hne]; ring
    rw [heq, norm_div, norm_pow, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hden : 1 ≤ Real.pi ^ 2 * ‖u‖ := by
      have hpi2 : 2 ≤ Real.pi := Real.two_le_pi
      nlinarith
    calc ‖Complex.sin (Real.pi * u)‖ ^ 2 / (Real.pi ^ 2 * ‖u‖)
        ≤ (Real.exp (Real.pi * |u.im|)) ^ 2 / 1 := by
          gcongr; rw [← hpi_im]; exact hsin_bd _
      _ = Real.exp (2 * Real.pi * |u.im|) := by rw [div_one, ← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (2 * Real.pi * |u.im| + 4) := Real.exp_le_exp.mpr (by linarith)

lemma envelopeC_pos {θ : ℝ} (hθ : |θ| < Real.pi / 2) : 0 < envelopeC θ := by
  have heven : envelopeC (-θ) = envelopeC θ := by
    unfold envelopeC; rw [Real.cos_neg, Real.sin_neg]; ring
  wlog hθ_nonneg : 0 ≤ θ
  · rw [← heven]; exact this (by rwa [abs_neg]) (by linarith)
  have hθ_lt : θ < Real.pi / 2 := (abs_lt.mp hθ).2
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  unfold envelopeC
  by_cases hle : θ ≤ Real.pi / 3
  · have hcos_ge : 1 / 2 ≤ Real.cos θ := by
      rw [← Real.cos_pi_div_three]
      exact Real.cos_le_cos_of_nonneg_of_le_pi hθ_nonneg (by linarith [Real.pi_pos]) hle
    have hlog_nonneg : 0 ≤ Real.log (2 * Real.cos θ) := Real.log_nonneg (by linarith)
    by_cases h0 : θ = 0
    · subst h0; simp only [Real.cos_zero, mul_one, Real.sin_zero, mul_zero, add_zero]
      have : 0 < Real.log 2 := Real.log_pos (by norm_num)
      linarith
    · have hθ_pos : 0 < θ := lt_of_le_of_ne hθ_nonneg (Ne.symm h0)
      have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ_pos (by linarith [Real.pi_pos])
      have h1 : 0 ≤ Real.cos θ * Real.log (2 * Real.cos θ) := mul_nonneg hcos_pos.le hlog_nonneg
      have h2 : 0 < θ * Real.sin θ := mul_pos hθ_pos hsin_pos
      linarith
  · have hgt : Real.pi / 3 < θ := not_le.mp hle
    let f : ℝ → ℝ := fun t => Real.cos t * Real.log (2 * Real.cos t) + t * Real.sin t
    have hf_at : 0 < f (Real.pi / 3) := by
      dsimp only [f]
      rw [Real.cos_pi_div_three, show 2 * (1 / 2 : ℝ) = 1 by norm_num, Real.log_one, mul_zero, zero_add]
      have hsin : 0 < Real.sin (Real.pi / 3) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
      exact mul_pos (by positivity) hsin
    have hf_mono : StrictMonoOn f (Set.Ico (Real.pi / 3) (Real.pi / 2)) := by
      apply strictMonoOn_of_deriv_pos (convex_Ico _ _)
      · refine ContinuousOn.add ?_ (by fun_prop)
        refine ContinuousOn.mul (Real.continuous_cos.continuousOn) (Real.continuousOn_log.comp (by fun_prop) fun t ht => ?_)
        have hct : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
        linarith
      · intro t ht
        rw [interior_Ico] at ht
        have hct : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
        have hst : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1, Real.pi_pos]) (by linarith [ht.2, Real.pi_pos])
        have hct_lt : Real.cos t < 1 / 2 := by
          rw [← Real.cos_pi_div_three]
          exact Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith [ht.2, Real.pi_pos]) ht.1
        have hlog_neg : Real.log (2 * Real.cos t) < 0 := Real.log_neg (by positivity) (by linarith)
        have hd1 : HasDerivAt (fun s => Real.cos s * Real.log (2 * Real.cos s))
            (-Real.sin t * Real.log (2 * Real.cos t) + Real.cos t * ((2 * (-Real.sin t)) / (2 * Real.cos t))) t := by
          have hc := Real.hasDerivAt_cos t
          have hl := (hc.const_mul 2).log (by linarith)
          exact hc.mul hl
        have hd2 : HasDerivAt (fun s => s * Real.sin s) (1 * Real.sin t + t * Real.cos t) t :=
          (hasDerivAt_id t).mul (Real.hasDerivAt_sin t)
        have hd := hd1.add hd2
        rw [hd.deriv]
        have hsimp : -Real.sin t * Real.log (2 * Real.cos t) + Real.cos t * (2 * -Real.sin t / (2 * Real.cos t)) +
            (1 * Real.sin t + t * Real.cos t) = -Real.sin t * Real.log (2 * Real.cos t) + t * Real.cos t := by
          field_simp [hct.ne']; ring
        rw [hsimp]
        have h1 : 0 < -Real.sin t * Real.log (2 * Real.cos t) := by nlinarith
        have h2 : 0 < t * Real.cos t := by nlinarith [ht.1, Real.pi_pos]
        linarith
    have h_gt := hf_mono ⟨le_rfl, by linarith [Real.pi_pos]⟩ ⟨hgt.le, hθ_lt⟩ hgt
    dsimp only [f] at h_gt hf_at
    linarith

lemma kernelK_bound_large (θ : ℝ) {u : ℝ} (hu : 1 ≤ |u|) :
    |kernelK θ u| ≤ 4 / u ^ 2 := by
  have hu_pos : 0 < |u| := by linarith
  have hu_ne : u ≠ 0 := abs_pos.mp hu_pos
  have hu2 : 1 ≤ u ^ 2 := by rw [← sq_abs]; nlinarith
  have hlog : |Real.log ((u ^ 2 + 1) / u ^ 2)| ≤ 1 / u ^ 2 := by
    have h_eq : (u ^ 2 + 1) / u ^ 2 = 1 + 1 / u ^ 2 := by field_simp [hu_ne]
    rw [h_eq, abs_of_nonneg (Real.log_nonneg (by positivity))]
    exact (Real.log_le_sub_one_of_pos (by positivity)).trans_eq (by ring)
  have harctan : |Real.arctan (1 / u) - u / (u ^ 2 + 1)| ≤ 2 / u ^ 2 := by
    let x : ℝ := 1 / u
    have hx_le : |x| ≤ 1 := by
      dsimp only [x]; rw [abs_div, abs_one, div_le_one hu_pos]; exact hu
    have h_diff1 : |Real.arctan x - x| ≤ |x| ^ 2 := by
      let f : ℝ → ℝ := fun t => Real.arctan t - t
      have hf_d : ∀ t ∈ Set.Icc (-|x|) |x|, HasDerivAt f (1 / (1 + t ^ 2) - 1) t := by
        intro t _
        simpa [f] using (Real.hasDerivAt_arctan t).sub (hasDerivAt_id t)
      have hbd : ∀ t ∈ Set.Icc (-|x|) |x|, ‖1 / (1 + t ^ 2) - 1‖ ≤ |x| ^ 2 := by
        intro t ht
        rw [Real.norm_eq_abs]
        have h_eq : 1 / (1 + t ^ 2) - 1 = -t ^ 2 / (1 + t ^ 2) := by
          field_simp [(by positivity : (0 : ℝ) < 1 + t ^ 2)]; ring
        rw [h_eq, abs_div, abs_neg, abs_of_nonneg (sq_nonneg t), abs_of_pos (by positivity)]
        have ht2 : t ^ 2 ≤ |x| ^ 2 := by
          rw [← sq_abs t]
          exact sq_le_sq' (by linarith [ht.1, ht.2]) (abs_le.mpr ⟨ht.1, ht.2⟩)
        calc t ^ 2 / (1 + t ^ 2) ≤ t ^ 2 / 1 :=
              div_le_div_of_nonneg_left (sq_nonneg t) zero_lt_one (by linarith [sq_nonneg t])
          _ = t ^ 2 := div_one _
          _ ≤ |x| ^ 2 := ht2
      rcases le_total 0 x with hx0 | hx0
      · have hmvt := (convex_Icc (-|x|) |x|).norm_image_sub_le_of_norm_deriv_le
          hf_d hbd ⟨by linarith [abs_nonneg x], abs_nonneg x⟩ ⟨by linarith [abs_nonneg x], le_abs_self x⟩
        simpa [f] using hmvt
      · have hmvt := (convex_Icc (-|x|) |x|).norm_image_sub_le_of_norm_deriv_le
          hf_d hbd ⟨neg_le_self x, by linarith [abs_nonneg x]⟩ ⟨by linarith [abs_nonneg x], abs_nonneg x⟩
        simpa [f, Real.norm_eq_abs, abs_sub_comm] using hmvt
    have h_diff2 : |x - u / (u ^ 2 + 1)| ≤ |x| ^ 2 := by
      have heq : x - u / (u ^ 2 + 1) = x ^ 3 / (1 + x ^ 2) := by
        dsimp only [x]; field_simp [hu_ne, (by positivity : (0 : ℝ) < u ^ 2 + 1)]; ring
      rw [heq, abs_div, abs_pow, abs_of_pos (by positivity)]
      calc |x| ^ 3 / (1 + x ^ 2) ≤ |x| ^ 3 / 1 :=
            div_le_div_of_nonneg_left (by positivity) zero_lt_one (by linarith [sq_nonneg x])
        _ = |x| * |x| ^ 2 := by ring
        _ ≤ 1 * |x| ^ 2 := mul_le_mul_of_nonneg_right hx_le (sq_nonneg _)
        _ = |x| ^ 2 := one_mul _
    have hx2_eq : |x| ^ 2 = 1 / u ^ 2 := by
      dsimp only [x]; rw [abs_div, abs_one, div_pow, one_pow, sq_abs]
    calc |Real.arctan x - u / (u ^ 2 + 1)|
        ≤ |Real.arctan x - x| + |x - u / (u ^ 2 + 1)| := abs_sub_le _ _ _
      _ ≤ |x| ^ 2 + |x| ^ 2 := add_le_add h_diff1 h_diff2
      _ = 2 / u ^ 2 := by rw [hx2_eq]; ring
  unfold kernelK
  calc |-(Real.cos θ / 2) * Real.log ((u ^ 2 + 1) / u ^ 2) +
        Real.sin θ * (Real.arctan (1 / u) - u / (u ^ 2 + 1))|
      ≤ |-(Real.cos θ / 2) * Real.log ((u ^ 2 + 1) / u ^ 2)| +
        |Real.sin θ * (Real.arctan (1 / u) - u / (u ^ 2 + 1))| := abs_add_le _ _
    _ = (|Real.cos θ| / 2) * |Real.log ((u ^ 2 + 1) / u ^ 2)| +
        |Real.sin θ| * |Real.arctan (1 / u) - u / (u ^ 2 + 1)| := by
        rw [abs_mul, abs_neg, abs_div, abs_two, abs_mul]
    _ ≤ (1 / 2) * (1 / u ^ 2) + 1 * (2 / u ^ 2) := by
        gcongr
        · exact Real.abs_cos_le_one θ
        · exact Real.abs_sin_le_one θ
    _ ≤ 4 / u ^ 2 := by
        have : 0 ≤ 1 / u ^ 2 := by positivity
        linarith

lemma kernelK_bound_small (θ : ℝ) {u : ℝ} (hu0 : 0 < |u|) (hu1 : |u| ≤ 1) :
    |kernelK θ u| ≤ 4 + Real.log (1 / |u|) := by
  have hu_ne : u ≠ 0 := abs_pos.mp hu0
  have hu2 : u ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg u]
  have hlog : |Real.log ((u ^ 2 + 1) / u ^ 2)| ≤ Real.log 2 + 2 * Real.log (1 / |u|) := by
    have h_eq : (u ^ 2 + 1) / u ^ 2 = (u ^ 2 + 1) * (1 / |u|) ^ 2 := by
      rw [sq_abs]; field_simp [hu_ne]
    rw [abs_of_nonneg (Real.log_nonneg (by
      rw [le_div_iff₀ (sq_pos_of_ne_zero hu_ne)]; linarith)), h_eq,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    have h1 : Real.log (u ^ 2 + 1) ≤ Real.log 2 := Real.log_le_log (by positivity) (by linarith)
    linarith
  have harctan : |Real.arctan (1 / u) - u / (u ^ 2 + 1)| ≤ Real.pi / 2 + 1 := by
    have h1 : |Real.arctan (1 / u)| ≤ Real.pi / 2 := (Real.abs_arctan_lt_pi_div_two _).le
    have h2 : |u / (u ^ 2 + 1)| ≤ 1 := by
      rw [abs_div, abs_of_pos (by positivity : 0 < u ^ 2 + 1)]
      exact div_le_one_of_le₀ (by linarith [sq_nonneg u]) (by positivity)
    exact (abs_sub _ _).trans (add_le_add h1 h2)
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpi : Real.pi / 2 + 1 ≤ 3 := by linarith [Real.pi_lt_four]
  unfold kernelK
  calc |-(Real.cos θ / 2) * Real.log ((u ^ 2 + 1) / u ^ 2) +
        Real.sin θ * (Real.arctan (1 / u) - u / (u ^ 2 + 1))|
      ≤ |-(Real.cos θ / 2) * Real.log ((u ^ 2 + 1) / u ^ 2)| +
        |Real.sin θ * (Real.arctan (1 / u) - u / (u ^ 2 + 1))| := abs_add_le _ _
    _ = (|Real.cos θ| / 2) * |Real.log ((u ^ 2 + 1) / u ^ 2)| +
        |Real.sin θ| * |Real.arctan (1 / u) - u / (u ^ 2 + 1)| := by
        rw [abs_mul, abs_neg, abs_div, abs_two, abs_mul]
    _ ≤ (1 / 2) * (Real.log 2 + 2 * Real.log (1 / |u|)) + 1 * (Real.pi / 2 + 1) := by
        gcongr
        · exact Real.abs_cos_le_one θ
        · exact Real.abs_sin_le_one θ
    _ ≤ (1 / 2) * (1 + 2 * Real.log (1 / |u|)) + 3 := by linarith
    _ ≤ 4 + Real.log (1 / |u|) := by linarith

lemma integrable_log_inv_Ioo : IntegrableOn (fun x : ℝ => Real.log (1 / |x|)) (Set.Ioo (-1 : ℝ) 1) := by
  have h_half : IntegrableOn (fun x : ℝ => Real.log (1 / x)) (Set.Ioo (0 : ℝ) 1) := by
    have h_int : IntegrableOn (fun x : ℝ => -Real.log x) (Set.Ioo (0 : ℝ) 1) := by
      have h1 := intervalIntegral.intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
      rw [← h1]
      exact intervalIntegral.intervalIntegrable_log.neg
    refine h_int.congr_fun (fun x hx => ?_) measurableSet_Ioo
    rw [one_div, Real.log_inv]
  have h_neg : IntegrableOn (fun x : ℝ => Real.log (1 / |x|)) (Set.Ioo (-1 : ℝ) 0) := by
    have h_emb := (Homeomorph.neg ℝ).measurableEmbedding
    have h_pre : (Homeomorph.neg ℝ) ⁻¹' Set.Ioo (-1 : ℝ) 0 = Set.Ioo 0 1 := by
      ext x; simp only [Set.mem_preimage, Homeomorph.neg_apply, Set.mem_Ioo]; constructor <;> intro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
    rw [← (Measure.measurePreserving_neg volume).integrableOn_comp_preimage h_emb, h_pre]
    refine h_half.congr_fun (fun x hx => ?_) measurableSet_Ioo
    simp [abs_of_pos hx.1]
  have h_pos : IntegrableOn (fun x : ℝ => Real.log (1 / |x|)) (Set.Ioo (0 : ℝ) 1) := by
    refine h_half.congr_fun (fun x hx => ?_) measurableSet_Ioo
    rw [abs_of_pos hx.1]
  have h_sub : Set.Ioo (-1 : ℝ) 1 =ᵐ[volume] Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1 := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun x hx => ?_) (measure_singleton (0 : ℝ))
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    by_contra hx0
    apply hx
    simp only [Set.mem_Ioo, Set.mem_union]
    rcases lt_or_gt_of_ne hx0 with h | h
    · exact ⟨fun h' => Or.inl ⟨h'.1, h⟩, fun h' => h'.elim (fun a => ⟨a.1, by linarith⟩) (fun a => by linarith [a.1])⟩
    · exact ⟨fun h' => Or.inr ⟨h, h'.2⟩, fun h' => h'.elim (fun a => by linarith [a.2]) (fun a => ⟨by linarith, a.2⟩)⟩
  rw [integrableOn_congr_set_ae h_sub]
  exact h_neg.union h_pos

lemma kernelK_integrable_sl (θ : ℝ) : Integrable (kernelK θ) := by
  have h_meas : AEStronglyMeasurable (kernelK θ) := by
    refine (ContinuousOn.aestronglyMeasurable (f := kernelK θ) (s := ({(0 : ℝ)}ᶜ : Set ℝ)) ?_
      (isOpen_compl_singleton.measurableSet)).mono_measure ?_
    · intro x hx
      have hx0 : x ≠ 0 := hx
      unfold kernelK
      refine ContinuousAt.continuousWithinAt ?_
      refine ContinuousAt.add ?_ ?_
      · refine ContinuousAt.const_mul ?_ _
        exact (Real.continuousAt_log (by positivity)).comp
          (((continuousAt_id.pow 2).add continuousAt_const).div (continuousAt_id.pow 2) (pow_ne_zero 2 hx0))
      · refine ContinuousAt.const_mul ?_ _
        exact (Real.continuousAt_arctan.comp (continuousAt_const.div continuousAt_id hx0)).sub
          (continuousAt_id.div ((continuousAt_id.pow 2).add continuousAt_const) (by positivity))
    · have h_compl : ({(0 : ℝ)}ᶜ : Set ℝ) =ᵐ[volume] Set.univ := by
        rw [Filter.EventuallyEq, ae_iff]
        refine measure_mono_null (fun x hx => ?_) (measure_singleton (0 : ℝ))
        simpa using hx
      rw [Measure.restrict_congr_set h_compl, Measure.restrict_univ]
  have h_small : IntegrableOn (kernelK θ) (Set.Ioo (-1 : ℝ) 1) := by
    refine ((integrableOn_const (by positivity) : IntegrableOn (fun _ : ℝ => (4 : ℝ)) (Set.Ioo (-1 : ℝ) 1)).add
      integrable_log_inv_Ioo).mono' h_meas.restrict ?_
    have h_ne0 : ∀ᵐ x : ℝ ∂volume.restrict (Set.Ioo (-1 : ℝ) 1), x ≠ 0 := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [ae_iff.mpr (by simp : volume {x : ℝ | ¬x ≠ 0} = 0)] with x hx _ using hx
    filter_upwards [h_ne0, ae_restrict_mem measurableSet_Ioo] with x hx0 hx
    rw [Real.norm_eq_abs]
    exact kernelK_bound_small θ (abs_pos.mpr hx0) (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)
  have h_large : IntegrableOn (kernelK θ) (Set.Ioo (-1 : ℝ) 1)ᶜ := by
    have h_inv_sq : IntegrableOn (fun x : ℝ => 4 / x ^ 2) (Set.Ioo (-1 : ℝ) 1)ᶜ := by
      have h1 : IntegrableOn (fun x : ℝ => (8 : ℝ) / (1 + x ^ 2)) Set.univ := by
        simpa using (integrable_inv_one_add_sq.const_mul 8).integrableOn
      refine (h1.mono_set (Set.subset_univ _)).mono' (by fun_prop) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo.compl] with x hx
      have hx1 : 1 ≤ |x| := by
        by_contra h
        rw [not_le, abs_lt] at h
        exact hx h
      have hx2 : 1 ≤ x ^ 2 := by rw [← sq_abs]; nlinarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    refine h_inv_sq.mono' h_meas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo.compl] with x hx
    have hx1 : 1 ≤ |x| := by
      by_contra h
      rw [not_le, abs_lt] at h
      exact hx h
    rw [Real.norm_eq_abs]
    exact kernelK_bound_large θ hx1
  rw [← integrableOn_univ, ← Set.union_compl_self (Set.Ioo (-1 : ℝ) 1)]
  exact h_small.union h_large

lemma kernelK_integral_eq (θ : ℝ) :
    (∫ x : ℝ, kernelK θ x) = -Real.pi * Real.cos θ := by
  let f1 : ℝ → ℝ := fun x => -(Real.cos θ / 2) * Real.log ((x ^ 2 + 1) / x ^ 2)
  let f2 : ℝ → ℝ := fun x => Real.sin θ * (Real.arctan (1 / x) - x / (x ^ 2 + 1))
  have hf1_int : Integrable f1 := by
    have h_eq : f1 = fun x => Real.cos θ * kernelK 0 x := by
      ext x; dsimp only [f1]; unfold kernelK; simp; ring
    rw [h_eq]; exact (kernelK_integrable_sl 0).const_mul _
  have hf2_int : Integrable f2 := by
    have h_eq : f2 = fun x => kernelK θ x - f1 x := by
      ext x; dsimp only [f1, f2]; unfold kernelK; ring
    rw [h_eq]; exact (kernelK_integrable_sl θ).sub hf1_int
  have hf2_zero : ∫ x : ℝ, f2 x = 0 := by
    have h_odd : ∀ x : ℝ, f2 (-x) = -f2 x := by
      intro x; dsimp only [f2]
      rw [neg_sq, div_neg, Real.arctan_neg, neg_div]
      ring
    have h_neg : (∫ x : ℝ, f2 x) = ∫ x : ℝ, f2 (-x) :=
      ((Measure.measurePreserving_neg volume).integral_comp (Homeomorph.neg ℝ).measurableEmbedding f2).symm
    simp_rw [h_odd, integral_neg] at h_neg
    linarith
  have h_log_int : ∫ x : ℝ, Real.log ((x ^ 2 + 1) / x ^ 2) = 2 * Real.pi := by
    let L : ℝ → ℝ := fun x => Real.log ((x ^ 2 + 1) / x ^ 2)
    have hL_int : Integrable L := by
      have h_eq : L = fun x => -2 * kernelK 0 x := by
        ext x; dsimp only [L]; unfold kernelK; simp; ring
      rw [h_eq]; exact (kernelK_integrable_sl 0).const_mul _
    have hL_even : ∀ x : ℝ, L (-x) = L x := by
      intro x; dsimp only [L]; rw [neg_sq]
    have h_split : ∫ x : ℝ, L x = (∫ x in Set.Iio (0 : ℝ), L x) + (∫ x in Set.Ioi (0 : ℝ), L x) := by
      have h1 : (∫ x : ℝ, L x) = (∫ x in Set.Iic (0 : ℝ), L x) + (∫ x in Set.Ioi (0 : ℝ), L x) := by
        rw [← setIntegral_univ, ← Set.Iic_union_Ioi,
          setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hL_int.integrableOn hL_int.integrableOn]
      rw [h1, integral_Iic_eq_integral_Iio]
    have h_neg_eq : ∫ x in Set.Iio (0 : ℝ), L x = ∫ x in Set.Ioi (0 : ℝ), L x := by
      have h_emb := (Homeomorph.neg ℝ).measurableEmbedding
      have h_pre : (Homeomorph.neg ℝ) ⁻¹' Set.Iio 0 = Set.Ioi 0 := by ext x; simp
      have h_eq := (Measure.measurePreserving_neg volume).setIntegral_preimage_emb h_emb L (Set.Iio 0)
      rw [h_pre] at h_eq
      simp_rw [hL_even] at h_eq
      exact h_eq.symm
    have h_Ioi : ∫ x in Set.Ioi (0 : ℝ), L x = Real.pi := by
      let G : ℝ → ℝ := fun x => x * Real.log ((x ^ 2 + 1) / x ^ 2) + 2 * Real.arctan x
      have hG_deriv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt G (L x) x := by
        intro x hx
        have hx0 : x ≠ 0 := hx.ne'
        have h_num : HasDerivAt (fun t : ℝ => (t ^ 2 + 1) / t ^ 2) (-2 / x ^ 3) x := by
          have hd := ((hasDerivAt_pow 2 x).add (hasDerivAt_const x 1)).div (hasDerivAt_pow 2 x) (pow_ne_zero 2 hx0)
          refine hd.congr_deriv ?_
          field_simp [hx0]; ring
        have hd_log : HasDerivAt (fun t : ℝ => Real.log ((t ^ 2 + 1) / t ^ 2)) ((-2 / x ^ 3) / ((x ^ 2 + 1) / x ^ 2)) x :=
          h_num.log (by positivity)
        have hd1 : HasDerivAt (fun t : ℝ => t * Real.log ((t ^ 2 + 1) / t ^ 2))
            (1 * Real.log ((x ^ 2 + 1) / x ^ 2) + x * ((-2 / x ^ 3) / ((x ^ 2 + 1) / x ^ 2))) x :=
          (hasDerivAt_id x).mul hd_log
        have hd2 : HasDerivAt (fun t : ℝ => 2 * Real.arctan t) (2 * (1 + x ^ 2)⁻¹) x :=
          (Real.hasDerivAt_arctan x).const_mul 2
        refine (hd1.add hd2).congr_deriv ?_
        dsimp only [L]
        field_simp [hx0, (by positivity : (0 : ℝ) < x ^ 2 + 1)]
        ring
      have h_lim_0 : Tendsto G (𝓝[>] 0) (nhds 0) := by
        have h1 : Tendsto (fun x : ℝ => x * Real.log (x ^ 2 + 1)) (𝓝[>] 0) (nhds 0) := by
          have hc : ContinuousAt (fun x : ℝ => x * Real.log (x ^ 2 + 1)) 0 :=
            continuousAt_id.mul ((Real.continuousAt_log (by norm_num)).comp ((continuousAt_id.pow 2).add continuousAt_const))
          simpa using hc.continuousWithinAt.tendsto
        have h2 : Tendsto (fun x : ℝ => 2 * (x * Real.log x)) (𝓝[>] 0) (nhds 0) := by
          simpa using Real.tendsto_mul_log_nhdsGT_zero.const_mul 2
        have h3 : Tendsto (fun x : ℝ => 2 * Real.arctan x) (𝓝[>] 0) (nhds 0) := by
          have hc : ContinuousAt (fun x : ℝ => 2 * Real.arctan x) 0 :=
            continuousAt_const.mul Real.continuousAt_arctan
          simpa using hc.continuousWithinAt.tendsto
        have h_eq : ∀ᶠ x in 𝓝[>] (0 : ℝ), G x = x * Real.log (x ^ 2 + 1) - 2 * (x * Real.log x) + 2 * Real.arctan x := by
          filter_upwards [self_mem_nhdsWithin] with x hx
          have hx0 : 0 < x := hx
          dsimp only [G]
          rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
          push_cast; ring
        have h_lim := (h1.sub h2).add h3
        rw [sub_zero, add_zero] at h_lim
        exact h_lim.congr' (h_eq.mono fun x hx => hx.symm)
      have h_lim_inf : Tendsto G atTop (nhds Real.pi) := by
        have h1 : Tendsto (fun x : ℝ => x * Real.log ((x ^ 2 + 1) / x ^ 2)) atTop (nhds 0) := by
          have h_bnd : ∀ᶠ x : ℝ in atTop, ‖x * Real.log ((x ^ 2 + 1) / x ^ 2)‖ ≤ 1 / x := by
            filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
            have hx0 : 0 < x := by linarith
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx0.le (Real.log_nonneg (by
              rw [le_div_iff₀ (sq_pos_of_ne_zero hx0.ne')]; linarith)))]
            have h_eq : (x ^ 2 + 1) / x ^ 2 = 1 + 1 / x ^ 2 := by field_simp [hx0.ne']
            rw [h_eq]
            have hle := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / x ^ 2)
            calc x * Real.log (1 + 1 / x ^ 2) ≤ x * (1 + 1 / x ^ 2 - 1) := by gcongr
              _ = 1 / x := by field_simp [hx0.ne']; ring
          have h_inv : Tendsto (fun x : ℝ => (1 : ℝ) / x) atTop (nhds 0) :=
            tendsto_const_nhds.div_atTop tendsto_id
          exact tendsto_zero_iff_norm_tendsto_zero.mpr (tendsto_of_tendsto_of_tendsto_of_le_of_le'
            tendsto_const_nhds h_inv (Eventually.of_forall fun _ => norm_nonneg _) h_bnd)
        have h2 : Tendsto (fun x : ℝ => 2 * Real.arctan x) atTop (nhds Real.pi) := by
          simpa [mul_div_cancel₀ _ two_ne_zero] using Real.tendsto_arctan_atTop.const_mul 2
        simpa using h1.add h2
      have hres := integral_Ioi_of_hasDerivAt_of_tendsto' hG_deriv hL_int.integrableOn h_lim_0 h_lim_inf
      linarith
    rw [h_split, h_neg_eq, h_Ioi]; ring
  have h_eq : kernelK θ = fun x => f1 x + f2 x := by
    ext x; dsimp only [f1, f2]; unfold kernelK; ring
  rw [h_eq, integral_add hf1_int hf2_int, hf2_zero, add_zero]
  dsimp only [f1]
  rw [integral_const_mul, h_log_int]; ring

lemma rescaledF_summable (θ Δ α : ℝ) (hΔ : 1 ≤ Δ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    Summable (fun n : ℤ => |rescaledF θ Δ (n + α)|) := by
  have hx_ne : ∀ n : ℤ, (n : ℝ) + α ≠ 0 := by
    intro n h0
    have h2 : (-1 : ℤ) < n := by exact_mod_cast (by linarith [hα.2] : (-1 : ℝ) < (n : ℝ))
    have h3 : n < (0 : ℤ) := by exact_mod_cast (by linarith [hα.1] : (n : ℝ) < 0)
    omega
  have h_inv_sq : Summable (fun n : ℤ => 1 / ((n : ℝ) + α) ^ 2) :=
    summable_inv_add_sq_of_ne_zero α hx_ne
  let δ : ℝ := min α (1 - α)
  have hδ_pos : 0 < δ := lt_min hα.1 (by linarith [hα.2])
  have h_lb : ∀ n : ℤ, δ ≤ |(n : ℝ) + α| := by
    intro n
    rcases le_or_gt (0 : ℤ) n with hn | hn
    · have : (0 : ℝ) ≤ n := by exact_mod_cast hn
      rw [abs_of_pos (by linarith [hα.1])]
      exact (min_le_left _ _).trans (by linarith)
    · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hn
      rw [abs_of_neg (by linarith [hα.2])]
      exact (min_le_right _ _).trans (by linarith)
  let C : ℝ := (4 + Real.log (Δ / δ)) * Δ ^ 2
  refine (h_inv_sq.mul_left C).of_nonneg_of_le (fun _ => abs_nonneg _) (fun n => ?_)
  have hΔ_pos : 0 < Δ := by linarith
  have h_abs_pos : 0 < |(n : ℝ) + α| := lt_of_lt_of_le hδ_pos (h_lb n)
  have hlog_nonneg : 0 ≤ Real.log (Δ / δ) := Real.log_nonneg (by
    rw [one_le_div hδ_pos]
    have : δ ≤ 1 := (min_le_left _ _).trans hα.2.le
    linarith)
  unfold rescaledF
  rcases le_or_gt 1 (|((n : ℝ) + α) / Δ|) with h | h
  · have hbd := kernelK_bound_large θ h
    have heq : 4 / (((n : ℝ) + α) / Δ) ^ 2 = 4 * Δ ^ 2 * (1 / ((n : ℝ) + α) ^ 2) := by
      field_simp [hΔ_pos.ne', hx_ne n]; ring
    rw [heq] at hbd
    refine hbd.trans ?_
    have h4 : 4 * Δ ^ 2 ≤ C := by dsimp only [C]; nlinarith
    exact mul_le_mul_of_nonneg_right h4 (by positivity)
  · have hu0 : 0 < |((n : ℝ) + α) / Δ| := by
      rw [abs_div, abs_of_pos hΔ_pos]; exact div_pos h_abs_pos hΔ_pos
    have hbd := kernelK_bound_small θ hu0 h.le
    have h_u_lt : |(n : ℝ) + α| < Δ := by
      rw [abs_div, abs_of_pos hΔ_pos, div_lt_one hΔ_pos] at h; exact h
    have h_1_le : 1 ≤ Δ ^ 2 / ((n : ℝ) + α) ^ 2 := by
      rw [one_le_div (sq_pos_of_ne_zero (hx_ne n)), ← sq_abs ((n : ℝ) + α)]
      exact sq_le_sq' (by linarith [h_abs_pos]) h_u_lt.le
    have h_log_le : Real.log (1 / |((n : ℝ) + α) / Δ|) ≤ Real.log (Δ / δ) := by
      have heq : 1 / |((n : ℝ) + α) / Δ| = Δ / |(n : ℝ) + α| := by
        rw [abs_div, abs_of_pos hΔ_pos, one_div_div]
      rw [heq]
      exact Real.log_le_log (div_pos hΔ_pos h_abs_pos) (div_le_div_of_nonneg_left hΔ_pos.le hδ_pos (h_lb n))
    calc |kernelK θ (((n : ℝ) + α) / Δ)|
        ≤ 4 + Real.log (Δ / δ) := by linarith
      _ = (4 + Real.log (Δ / δ)) * 1 := (mul_one _).symm
      _ ≤ (4 + Real.log (Δ / δ)) * (Δ ^ 2 / ((n : ℝ) + α) ^ 2) :=
          mul_le_mul_of_nonneg_left h_1_le (by linarith)
      _ = C * (1 / ((n : ℝ) + α) ^ 2) := by dsimp only [C]; ring

lemma rescaledFDeriv_mul_bound (θ Δ y : ℝ) (hΔ : 0 < Δ) (hy : y ≠ 0) :
    |y * rescaledFDeriv θ Δ y| ≤ 2 * Δ ^ 2 / y ^ 2 := by
  unfold rescaledFDeriv
  have heq : y * (Real.cos θ * (1 / y - y / (y ^ 2 + Δ ^ 2)) - Real.sin θ * (2 * Δ ^ 3 / (y ^ 2 + Δ ^ 2) ^ 2)) =
      Real.cos θ * (Δ ^ 2 / (y ^ 2 + Δ ^ 2)) - Real.sin θ * (2 * Δ ^ 3 * y / (y ^ 2 + Δ ^ 2) ^ 2) := by
    field_simp [hy, (by positivity : (0 : ℝ) < y ^ 2 + Δ ^ 2)]
    ring
  rw [heq]
  have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
  have hden : y ^ 2 ≤ y ^ 2 + Δ ^ 2 := by linarith [sq_nonneg Δ]
  have h1 : |Δ ^ 2 / (y ^ 2 + Δ ^ 2)| ≤ Δ ^ 2 / y ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_left (sq_nonneg Δ) hy2 hden
  have h2 : |2 * Δ ^ 3 * y / (y ^ 2 + Δ ^ 2) ^ 2| ≤ Δ ^ 2 / y ^ 2 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < (y ^ 2 + Δ ^ 2) ^ 2), abs_mul, abs_mul,
      abs_of_pos (by positivity : 0 < 2 * Δ ^ 3)]
    have h_amgm : 2 * Δ * |y| ≤ y ^ 2 + Δ ^ 2 := by
      have : (|y| - Δ) ^ 2 ≥ 0 := sq_nonneg _
      nlinarith [sq_abs y]
    calc 2 * Δ ^ 3 * |y| / (y ^ 2 + Δ ^ 2) ^ 2
        = Δ ^ 2 * (2 * Δ * |y|) / (y ^ 2 + Δ ^ 2) ^ 2 := by ring
      _ ≤ Δ ^ 2 * (y ^ 2 + Δ ^ 2) / (y ^ 2 + Δ ^ 2) ^ 2 := by gcongr
      _ = Δ ^ 2 / (y ^ 2 + Δ ^ 2) := by field_simp [(by positivity : (0 : ℝ) < y ^ 2 + Δ ^ 2)]
      _ ≤ Δ ^ 2 / y ^ 2 := div_le_div_of_nonneg_left (sq_nonneg Δ) hy2 hden
  calc |Real.cos θ * (Δ ^ 2 / (y ^ 2 + Δ ^ 2)) - Real.sin θ * (2 * Δ ^ 3 * y / (y ^ 2 + Δ ^ 2) ^ 2)|
      ≤ |Real.cos θ * (Δ ^ 2 / (y ^ 2 + Δ ^ 2))| + |Real.sin θ * (2 * Δ ^ 3 * y / (y ^ 2 + Δ ^ 2) ^ 2)| :=
        abs_sub _ _
    _ = |Real.cos θ| * |Δ ^ 2 / (y ^ 2 + Δ ^ 2)| + |Real.sin θ| * |2 * Δ ^ 3 * y / (y ^ 2 + Δ ^ 2) ^ 2| := by
        rw [abs_mul, abs_mul]
    _ ≤ 1 * (Δ ^ 2 / y ^ 2) + 1 * (Δ ^ 2 / y ^ 2) := by
        gcongr
        · exact Real.abs_cos_le_one θ
        · exact Real.abs_sin_le_one θ
    _ = 2 * Δ ^ 2 / y ^ 2 := by ring

lemma rescaledFDeriv_mul_summable (θ Δ α : ℝ) (hΔ : 1 ≤ Δ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    Summable (fun n : ℤ => |(n + α) * rescaledFDeriv θ Δ (n + α)|) := by
  have hx_ne : ∀ n : ℤ, (n : ℝ) + α ≠ 0 := by
    intro n h0
    have h2 : (-1 : ℤ) < n := by exact_mod_cast (by linarith [hα.2] : (-1 : ℝ) < (n : ℝ))
    have h3 : n < (0 : ℤ) := by exact_mod_cast (by linarith [hα.1] : (n : ℝ) < 0)
    omega
  have h_inv_sq : Summable (fun n : ℤ => 1 / ((n : ℝ) + α) ^ 2) :=
    summable_inv_add_sq_of_ne_zero α hx_ne
  refine (h_inv_sq.mul_left (2 * Δ ^ 2)).of_nonneg_of_le (fun _ => abs_nonneg _) (fun n => ?_)
  have hbd := rescaledFDeriv_mul_bound θ Δ (n + α) (by linarith) (hx_ne n)
  simpa [mul_one_div] using hbd

lemma limitingJ_continuousOn_Icc (θ : ℝ) (hθ : |θ| < Real.pi / 2)
    {a b : ℝ} (hab : a ≤ b) (h0 : (0 : ℝ) ∉ Set.Icc a b) :
    ContinuousOn (fun y : ℝ => limitingJ y θ) (Set.Icc a b) := by
  have h_pos_min : ∃ δ > 0, ∀ y ∈ Set.Icc a b, δ ≤ |y| := by
    by_cases ha : 0 < a
    · exact ⟨a, ha, fun y hy => by rw [abs_of_pos (lt_of_lt_of_le ha hy.1)]; exact hy.1⟩
    · have hb : b < 0 := by
        by_contra hb'; push_neg at hb'
        exact h0 ⟨not_lt.mp ha, hb'⟩
      exact ⟨-b, by linarith, fun y hy => by rw [abs_of_neg (lt_of_le_of_lt hy.2 hb)]; linarith [hy.2]⟩
  obtain ⟨δ, hδ_pos, hδ_lb⟩ := h_pos_min
  rw [continuousOn_iff_continuous_restrict]
  refine Complex.continuous_im.comp ?_ |>.congr ?_
  · refine continuous_of_dominated (F := fun (y : Set.Icc a b) (v : ℝ) =>
        cTheta θ v / ((y : ℝ) - Complex.I * v))
      (bound := fun v : ℝ => ‖cTheta θ v‖ / δ) ?_ ?_ ?_ ?_
    · intro ⟨y, hy⟩
      refine Continuous.aestronglyMeasurable ?_
      refine Continuous.div ?_ (by fun_prop) (fun v => ?_)
      · exact continuous_const.div (Continuous.pow (Complex.continuous_cos.comp (by fun_prop)) 2)
          (fun v => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ))
      · intro h; have hre := congr_arg Complex.re h; simp at hre
        have := hδ_lb y hy; rw [hre, abs_zero] at this; linarith
    · intro ⟨y, hy⟩
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
      rw [norm_div]
      have hden : δ ≤ ‖(y : ℂ) - Complex.I * v‖ := by
        have h1 : δ ≤ |y| := hδ_lb y hy
        have h2 : |y| ≤ ‖(y : ℂ) - Complex.I * v‖ := by
          have hsq : |y| ^ 2 ≤ ‖(y : ℂ) - Complex.I * v‖ ^ 2 := by
            rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq_abs]
            simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
              Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.sub_im, Complex.mul_im,
              zero_sub, neg_mul]
            nlinarith [sq_nonneg v]
          exact (sq_le_sq₀ (abs_nonneg y) (norm_nonneg _)).mp hsq
        linarith
      exact div_le_div_of_nonneg_left (norm_nonneg _) hδ_pos hden
    · exact (cTheta_integrableOn hθ).norm.div_const δ
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
      refine Continuous.continuousAt ?_
      refine Continuous.div continuous_const ((continuous_subtype_val.ofReal_comp).sub continuous_const) ?_
      intro ⟨y, hy⟩ h
      have hre := congr_arg Complex.re h; simp at hre
      have := hδ_lb y hy; rw [hre, abs_zero] at this; linarith
  · intro ⟨y, hy⟩
    unfold limitingJ cTheta
    have h_int : IntegrableOn (fun v : ℝ =>
        Complex.exp (-Complex.I * θ) / (Complex.cos (θ + Complex.I * Real.pi * v) ^ 2 * (y - Complex.I * v))) (Set.Ioi 0) := by
      refine ((cTheta_integrableOn hθ).norm.div_const δ).mono' ?_ ?_
      · refine Continuous.aestronglyMeasurable ?_
        refine continuous_const.div (Continuous.mul (Continuous.pow (Complex.continuous_cos.comp (by fun_prop)) 2) (by fun_prop)) fun v => ?_
        refine mul_ne_zero (pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ)) ?_
        intro h; have hre := congr_arg Complex.re h; simp at hre
        have := hδ_lb y hy; rw [hre, abs_zero] at this; linarith
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
        have h_eq : Complex.exp (-Complex.I * θ) / (Complex.cos (θ + Complex.I * Real.pi * v) ^ 2 * (y - Complex.I * v)) =
            cTheta θ v / ((y : ℂ) - Complex.I * v) := by dsimp only [cTheta]; ring
        rw [h_eq, norm_div]
        have hden : δ ≤ ‖(y : ℂ) - Complex.I * v‖ := by
          have h1 : δ ≤ |y| := hδ_lb y hy
          have hsq : |y| ^ 2 ≤ ‖(y : ℂ) - Complex.I * v‖ ^ 2 := by
            rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq_abs]
            simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
              Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.sub_im, Complex.mul_im,
              zero_sub, neg_mul]
            nlinarith [sq_nonneg v]
          exact h1.trans ((sq_le_sq₀ (abs_nonneg y) (norm_nonneg _)).mp hsq)
        exact div_le_div_of_nonneg_left (norm_nonneg _) hδ_pos hden
    have h_re := Complex.imCLM.integral_comp_comm h_int
    dsimp only [Complex.imCLM_apply] at h_re
    rw [← h_re]
    congr 1; ext v; dsimp only [cTheta]; ring

lemma limitingJ_lower_bounds (θ : ℝ) (hθ : |θ| < Real.pi / 2) :
    (∃ c_J > 0, ∀ y : ℝ, y ≠ 0 → limitingJ y θ ≥ c_J / (1 + y ^ 2)) ∧
    (∃ c'_J > 0, ∀ y : ℝ, 0 < |y| → |y| ≤ 1 → limitingJ y θ ≥ c'_J * (1 + Real.log (1 / |y|))) := by
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  obtain ⟨C_0, hC_0, h_near⟩ := limitingJ_near_zero θ hθ
  obtain ⟨Y₀, C_inf, hY₀, hC_inf, h_asymp⟩ := limitingJ_asymptotic θ hθ
  have hC_env : 0 < envelopeC θ := envelopeC_pos hθ
  let δ₀ : ℝ := min 1 (Real.exp (-(2 * C_0 + 2) * Real.cos θ))
  have hδ₀_pos : 0 < δ₀ := lt_min zero_lt_one (Real.exp_pos _)
  have hδ₀_le : δ₀ ≤ 1 := min_le_left _ _
  let Y₁ : ℝ := max Y₀ (C_inf * Real.pi ^ 2 / envelopeC θ)
  have hY₁_ge : Y₀ ≤ Y₁ := le_max_left _ _
  have hY₁_ge1 : 1 ≤ Y₁ := le_trans hY₀ hY₁_ge
  have hδ₀_le_Y₁ : δ₀ ≤ Y₁ := le_trans hδ₀_le hY₁_ge1
  have hcont_pos : ContinuousOn (fun y : ℝ => limitingJ y θ) (Set.Icc δ₀ Y₁) :=
    limitingJ_continuousOn_Icc θ hθ hδ₀_le_Y₁ (fun h => by linarith [h.1])
  obtain ⟨y_plus, hy_plus_mem, hy_plus_min⟩ := isCompact_Icc.exists_isMinOn ⟨δ₀, left_mem_Icc.mpr hδ₀_le_Y₁⟩ hcont_pos
  have hcont_neg : ContinuousOn (fun y : ℝ => limitingJ y θ) (Set.Icc (-Y₁) (-δ₀)) :=
    limitingJ_continuousOn_Icc θ hθ (by linarith) (fun h => by linarith [h.2])
  obtain ⟨y_minus, hy_minus_mem, hy_minus_min⟩ := isCompact_Icc.exists_isMinOn ⟨-δ₀, right_mem_Icc.mpr (by linarith)⟩ hcont_neg
  have hy_plus_pos : 0 < limitingJ y_plus θ := limitingJ_pos θ hθ y_plus (by linarith [hy_plus_mem.1])
  have hy_minus_pos : 0 < limitingJ y_minus θ := limitingJ_pos θ hθ y_minus (by linarith [hy_minus_mem.2])
  let m : ℝ := min (limitingJ y_plus θ) (limitingJ y_minus θ)
  have hm_pos : 0 < m := lt_min hy_plus_pos hy_minus_pos
  have h_mid : ∀ y : ℝ, δ₀ ≤ |y| → |y| ≤ Y₁ → m ≤ limitingJ y θ := by
    intro y hy1 hy2
    rcases le_total 0 y with hy0 | hy0
    · rw [abs_of_nonneg hy0] at hy1 hy2
      exact (min_le_left _ _).trans (hy_plus_min ⟨hy1, hy2⟩)
    · rw [abs_of_nonpos hy0] at hy1 hy2
      exact (min_le_right _ _).trans (hy_minus_min ⟨by linarith, by linarith⟩)
  have h_small : ∀ y : ℝ, 0 < |y| → |y| ≤ δ₀ →
      min (1 / (2 * Real.cos θ)) 1 * (1 + Real.log (1 / |y|)) ≤ limitingJ y θ := by
    intro y hy0 hy_le
    have hy1 : |y| ≤ 1 := hy_le.trans hδ₀_le
    have h_nr := (abs_le.mp (h_near y hy0 hy1)).1
    have h_log_ge : (2 * C_0 + 2) * Real.cos θ ≤ Real.log (1 / |y|) := by
      have h1 : |y| ≤ Real.exp (-(2 * C_0 + 2) * Real.cos θ) := hy_le.trans (min_le_right _ _)
      have h2 : Real.exp ((2 * C_0 + 2) * Real.cos θ) ≤ 1 / |y| := by
        rw [le_div_iff₀ hy0, ← Real.exp_neg]
        calc Real.exp ((2 * C_0 + 2) * Real.cos θ) * |y|
            ≤ Real.exp ((2 * C_0 + 2) * Real.cos θ) * Real.exp (-(2 * C_0 + 2) * Real.cos θ) := by gcongr
          _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      calc (2 * C_0 + 2) * Real.cos θ = Real.log (Real.exp ((2 * C_0 + 2) * Real.cos θ)) := (Real.log_exp _).symm
        _ ≤ Real.log (1 / |y|) := Real.log_le_log (Real.exp_pos _) h2
    have h_half : C_0 + 1 ≤ (1 / (2 * Real.cos θ)) * Real.log (1 / |y|) := by
      rw [← mul_le_mul_iff_of_pos_left (by positivity : 0 < 2 * Real.cos θ)]
      calc 2 * Real.cos θ * (C_0 + 1) = (2 * C_0 + 2) * Real.cos θ := by ring
        _ ≤ Real.log (1 / |y|) := h_log_ge
        _ = 2 * Real.cos θ * ((1 / (2 * Real.cos θ)) * Real.log (1 / |y|)) := by field_simp [hcos_pos.ne']
    have h_j : (1 / (2 * Real.cos θ)) * Real.log (1 / |y|) + 1 ≤ limitingJ y θ := by
      have h_eq : (1 / Real.cos θ) * Real.log (1 / |y|) =
          (1 / (2 * Real.cos θ)) * Real.log (1 / |y|) + (1 / (2 * Real.cos θ)) * Real.log (1 / |y|) := by ring
      linarith
    have h_nonneg : 0 ≤ Real.log (1 / |y|) := Real.log_nonneg ((one_le_div hy0).mpr hy1)
    let c_s : ℝ := min (1 / (2 * Real.cos θ)) 1
    calc c_s * (1 + Real.log (1 / |y|)) = c_s + c_s * Real.log (1 / |y|) := by ring
      _ ≤ 1 + (1 / (2 * Real.cos θ)) * Real.log (1 / |y|) := by
          gcongr
          · exact min_le_right _ _
          · exact min_le_left _ _
      _ ≤ limitingJ y θ := by linarith
  let c'_J : ℝ := min (min (1 / (2 * Real.cos θ)) 1) (m / (1 + Real.log (1 / δ₀)))
  have hlog_δ_nonneg : 0 ≤ Real.log (1 / δ₀) := Real.log_nonneg ((one_le_div hδ₀_pos).mpr hδ₀_le)
  have hc'_J_pos : 0 < c'_J := by
    refine lt_min (lt_min (by positivity) zero_lt_one) (div_pos hm_pos (by linarith))
  let c_J : ℝ := min (min c'_J m) (envelopeC θ / Real.pi ^ 2)
  have hc_J_pos : 0 < c_J := lt_min (lt_min hc'_J_pos hm_pos) (div_pos hC_env (sq_pos_of_pos Real.pi_pos))
  refine ⟨⟨c_J, hc_J_pos, fun y hy => ?_⟩, ⟨c'_J, hc'_J_pos, fun y hy0 hy1 => ?_⟩⟩
  · have hy0 : 0 < |y| := abs_pos.mpr hy
    rcases le_or_gt |y| δ₀ with h_s | h_m
    · have h1 := h_small y hy0 h_s
      have h_log_nonneg : 0 ≤ Real.log (1 / |y|) := Real.log_nonneg ((one_le_div hy0).mpr (h_s.trans hδ₀_le))
      have h2 : c_J ≤ min (1 / (2 * Real.cos θ)) 1 :=
        (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
      have h3 : c_J / (1 + y ^ 2) ≤ c_J := div_le_self hc_J_pos.le (by linarith [sq_nonneg y])
      calc c_J / (1 + y ^ 2) ≤ c_J := h3
        _ ≤ min (1 / (2 * Real.cos θ)) 1 * (1 + Real.log (1 / |y|)) := by
            calc c_J = c_J * 1 := (mul_one _).symm
              _ ≤ min (1 / (2 * Real.cos θ)) 1 * (1 + Real.log (1 / |y|)) :=
                  mul_le_mul h2 (by linarith) zero_le_one (by positivity)
        _ ≤ limitingJ y θ := h1
    · rcases le_or_gt |y| Y₁ with h_mid' | h_l
      · have h1 := h_mid y h_m.le h_mid'
        have h2 : c_J ≤ m := (min_le_left _ _).trans (min_le_right _ _)
        calc c_J / (1 + y ^ 2) ≤ c_J := div_le_self hc_J_pos.le (by linarith [sq_nonneg y])
          _ ≤ m := h2
          _ ≤ limitingJ y θ := h1
      · have h_as := (abs_le.mp (h_asymp y (le_trans hY₁_ge h_l.le))).1
        have h_cinf : C_inf / |y| ^ 3 ≤ (envelopeC θ / Real.pi ^ 2) / y ^ 2 := by
          have hy_pos : 0 < |y| := by linarith
          have h_y1 : C_inf * Real.pi ^ 2 / envelopeC θ ≤ |y| := le_trans (le_max_right _ _) h_l.le
          have h_div : C_inf / |y| ≤ envelopeC θ / Real.pi ^ 2 := by
            rw [div_le_div_iff₀ hy_pos (sq_pos_of_pos Real.pi_pos), ← div_le_iff₀ hC_env]
            exact h_y1
          calc C_inf / |y| ^ 3 = (C_inf / |y|) / y ^ 2 := by rw [← sq_abs y]; ring
            _ ≤ (envelopeC θ / Real.pi ^ 2) / y ^ 2 := div_le_div_of_nonneg_right h_div (sq_nonneg y)
        have h_lim : (envelopeC θ / Real.pi ^ 2) / y ^ 2 ≤ limitingJ y θ := by
          have heq : 2 * envelopeC θ / (Real.pi ^ 2 * y ^ 2) - (envelopeC θ / Real.pi ^ 2) / y ^ 2 =
              (envelopeC θ / Real.pi ^ 2) / y ^ 2 := by ring
          linarith
        have h_1y : (envelopeC θ / Real.pi ^ 2) / (1 + y ^ 2) ≤ (envelopeC θ / Real.pi ^ 2) / y ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (sq_pos_of_ne_zero hy) (by linarith)
        have h_cj : c_J ≤ envelopeC θ / Real.pi ^ 2 := min_le_right _ _
        calc c_J / (1 + y ^ 2) ≤ (envelopeC θ / Real.pi ^ 2) / (1 + y ^ 2) :=
              div_le_div_of_nonneg_right h_cj (by positivity)
          _ ≤ limitingJ y θ := le_trans h_1y h_lim
  · rcases le_or_gt |y| δ₀ with h_s | h_m
    · have h1 := h_small y hy0 h_s
      have h_log_nonneg : 0 ≤ Real.log (1 / |y|) := Real.log_nonneg ((one_le_div hy0).mpr hy1)
      have h2 : c'_J ≤ min (1 / (2 * Real.cos θ)) 1 := min_le_left _ _
      exact le_trans (mul_le_mul_of_nonneg_right h2 (by linarith)) h1
    · have h1 := h_mid y h_m.le (hy1.trans hY₁_ge1)
      have h_log_le : 1 + Real.log (1 / |y|) ≤ 1 + Real.log (1 / δ₀) := by
        gcongr; exact div_le_div_of_nonneg_left zero_le_one hδ₀_pos h_m.le
      have h2 : c'_J ≤ m / (1 + Real.log (1 / δ₀)) := min_le_right _ _
      calc c'_J * (1 + Real.log (1 / |y|))
          ≤ (m / (1 + Real.log (1 / δ₀))) * (1 + Real.log (1 / δ₀)) :=
            mul_le_mul h2 h_log_le (by linarith [Real.log_nonneg ((one_le_div hy0).mpr hy1)]) (by positivity)
        _ = m := by field_simp [(by linarith : (0 : ℝ) < 1 + Real.log (1 / δ₀))]
        _ ≤ limitingJ y θ := h1

lemma sin_pi_iv_beta_lb {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    {β : ℝ} (hβ1 : δ ≤ β) (hβ2 : β ≤ 1 - δ) (v : ℝ) (hv : 0 ≤ v) :
    (Real.sin (Real.pi * δ) / Real.exp Real.pi) * Real.exp (Real.pi * v) ≤
      ‖Complex.sin (Real.pi * (Complex.I * v - β))‖ := by
  have heq : (Real.pi : ℂ) * (Complex.I * v - β) = ((-Real.pi * β : ℝ) : ℂ) + Complex.I * (Real.pi * v) := by
    push_cast; ring
  rw [heq]
  have h_re_im : ‖Complex.sin (((-Real.pi * β : ℝ) : ℂ) + Complex.I * (Real.pi * v))‖ ^ 2 =
      Real.sin (-Real.pi * β) ^ 2 + Real.sinh (Real.pi * v) ^ 2 := by
    have hs := Complex.sin_add ((-Real.pi * β : ℝ) : ℂ) (Complex.I * (Real.pi * v))
    rw [← Complex.ofReal_sin, ← Complex.ofReal_cos, Complex.sin_mul_I, Complex.cos_mul_I,
      ← Complex.ofReal_sinh, ← Complex.ofReal_cosh] at hs
    have h_split : Complex.sin (((-Real.pi * β : ℝ) : ℂ) + Complex.I * (Real.pi * v)) =
        ((Real.sin (-Real.pi * β) * Real.cosh (Real.pi * v) : ℝ) : ℂ) +
        ((Real.cos (-Real.pi * β) * Real.sinh (Real.pi * v) : ℝ) : ℂ) * Complex.I := by
      rw [hs]; push_cast; ring
    rw [h_split, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
      zero_add]
    have h_ch := Real.cosh_sq (Real.pi * v)
    have h_cs := Real.cos_sq_add_sin_sq (-Real.pi * β)
    nlinarith
  have hsin_lb : Real.sin (Real.pi * δ) ≤ |Real.sin (-Real.pi * β)| := by
    rw [Real.sin_neg, abs_neg, abs_of_pos (Real.sin_pos_of_pos_of_lt_pi (by positivity)
      (by nlinarith [Real.pi_pos]))]
    rcases le_total β (1 / 2) with hβ | hβ
    · exact Real.strictMonoOn_sin.monotoneOn ⟨by linarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩ ⟨by linarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩ (by nlinarith [Real.pi_pos])
    · rw [← Real.sin_pi_sub (Real.pi * β)]
      exact Real.strictMonoOn_sin.monotoneOn ⟨by linarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩ ⟨by linarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩ (by nlinarith [Real.pi_pos])
  have hsin_δ_pos : 0 < Real.sin (Real.pi * δ) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  rcases le_or_gt v 1 with hv1 | hv1
  · have hsq : ((Real.sin (Real.pi * δ) / Real.exp Real.pi) * Real.exp (Real.pi * v)) ^ 2 ≤
        ‖Complex.sin (((-Real.pi * β : ℝ) : ℂ) + Complex.I * (Real.pi * v))‖ ^ 2 := by
      rw [h_re_im]
      have h1 : Real.exp (Real.pi * v) / Real.exp Real.pi ≤ 1 := by
        rw [div_le_one (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      have h2 : (Real.sin (Real.pi * δ) / Real.exp Real.pi) * Real.exp (Real.pi * v) ≤ Real.sin (Real.pi * δ) := by
        calc (Real.sin (Real.pi * δ) / Real.exp Real.pi) * Real.exp (Real.pi * v)
            = Real.sin (Real.pi * δ) * (Real.exp (Real.pi * v) / Real.exp Real.pi) := by ring
          _ ≤ Real.sin (Real.pi * δ) * 1 := mul_le_mul_of_nonneg_left h1 hsin_δ_pos.le
          _ = Real.sin (Real.pi * δ) := mul_one _
      have h3 : Real.sin (Real.pi * δ) ^ 2 ≤ Real.sin (-Real.pi * β) ^ 2 := by
        rw [← sq_abs (Real.sin (-Real.pi * β))]
        exact sq_le_sq' (by linarith [hsin_δ_pos]) hsin_lb
      have h4 : ((Real.sin (Real.pi * δ) / Real.exp Real.pi) * Real.exp (Real.pi * v)) ^ 2 ≤ Real.sin (Real.pi * δ) ^ 2 :=
        sq_le_sq' (by positivity) h2
      nlinarith [sq_nonneg (Real.sinh (Real.pi * v))]
    exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hsq
  · have h_sinh := sin_norm_ge_sinh (-Real.pi * β) (Real.pi * v)
    rw [abs_of_pos (by positivity)] at h_sinh
    have h_sh := (sinh_ge_mul_exp (by nlinarith [Real.pi_pos])).trans h_sinh
    have h_c_le : Real.sin (Real.pi * δ) / Real.exp Real.pi ≤ (1 - Real.exp (-2 * Real.pi)) / 2 := by
      have h1 : Real.sin (Real.pi * δ) ≤ 1 := Real.sin_le_one _
      have h2 : 1 / Real.exp Real.pi ≤ (1 - Real.exp (-2 * Real.pi)) / 2 := by
        have hpi3 : 3 ≤ Real.pi := Real.pi_gt_three.le
        have hep : Real.exp Real.pi ≥ 4 := by
          have := Real.add_one_le_exp Real.pi
          linarith
        have hep2 : Real.exp (-2 * Real.pi) ≤ 1 / 16 := by
          rw [show -2 * Real.pi = -(Real.pi + Real.pi) by ring, Real.exp_neg, Real.exp_add]
          rw [inv_le_iff₀ (by positivity)]
          nlinarith
        rw [div_le_div_iff₀ (Real.exp_pos _) zero_lt_two]
        nlinarith
      calc Real.sin (Real.pi * δ) / Real.exp Real.pi
          ≤ 1 / Real.exp Real.pi := div_le_div_of_nonneg_right h1 (Real.exp_pos _).le
        _ ≤ (1 - Real.exp (-2 * Real.pi)) / 2 := h2
    simpa [Complex.ofReal_mul] using le_trans (mul_le_mul_of_nonneg_right h_c_le (Real.exp_pos _).le) h_sh

lemma sin_pi_iv_alpha_diff {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    {α β : ℝ} (hα1 : δ ≤ α) (hα2 : α ≤ 1 - δ) (hβ1 : δ ≤ β) (hβ2 : β ≤ 1 - δ)
    (v : ℝ) (hv : 0 ≤ v) :
    ‖1 / Complex.sin (Real.pi * (Complex.I * v - α)) ^ 2 -
      1 / Complex.sin (Real.pi * (Complex.I * v - β)) ^ 2‖ ≤
      (2 * Real.pi / (Real.sin (Real.pi * δ) / Real.exp Real.pi) ^ 4) * |α - β| * Real.exp (-2 * Real.pi * v) := by
  let c_sin : ℝ := Real.sin (Real.pi * δ) / Real.exp Real.pi
  have hsin_δ_pos : 0 < Real.sin (Real.pi * δ) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hc_pos : 0 < c_sin := div_pos hsin_δ_pos (Real.exp_pos _)
  let z₁ : ℂ := Real.pi * (Complex.I * v - α)
  let z₂ : ℂ := Real.pi * (Complex.I * v - β)
  have hz₁_lb : c_sin * Real.exp (Real.pi * v) ≤ ‖Complex.sin z₁‖ :=
    sin_pi_iv_beta_lb hδ0 hδ1 hα1 hα2 v hv
  have hz₂_lb : c_sin * Real.exp (Real.pi * v) ≤ ‖Complex.sin z₂‖ :=
    sin_pi_iv_beta_lb hδ0 hδ1 hβ1 hβ2 v hv
  have hz₁_ne : Complex.sin z₁ ≠ 0 := norm_ne_zero_iff.mp (by linarith [mul_pos hc_pos (Real.exp_pos (Real.pi * v))])
  have hz₂_ne : Complex.sin z₂ ≠ 0 := norm_ne_zero_iff.mp (by linarith [mul_pos hc_pos (Real.exp_pos (Real.pi * v))])
  have h_sin_bd : ∀ w : ℂ, ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
    intro w
    have hsin_def : ∀ z : ℂ, Complex.sin z = (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * Complex.I / 2 := by intro z; unfold Complex.sin; ring_nf
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
  have hz₁_im : |z₁.im| = Real.pi * v := by
    dsimp only [z₁]; simp [Complex.mul_im, abs_of_nonneg (mul_nonneg Real.pi_pos.le hv)]
  have hz₂_im : |z₂.im| = Real.pi * v := by
    dsimp only [z₂]; simp [Complex.mul_im, abs_of_nonneg (mul_nonneg Real.pi_pos.le hv)]
  have h_diff_sin : ‖Complex.sin z₂ - Complex.sin z₁‖ ≤ Real.pi * |α - β| * Real.exp (Real.pi * v) := by
    let f : ℝ → ℂ := fun t => Complex.sin (z₁ + t * (z₂ - z₁))
    have hf_d : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f ((z₂ - z₁) * Complex.cos (z₁ + t * (z₂ - z₁))) t := by
      intro t _
      have h1 : HasDerivAt (fun s : ℝ => z₁ + (s : ℂ) * (z₂ - z₁)) (z₂ - z₁) t := by
        simpa using (hasDerivAt_const t z₁).add ((hasDerivAt_id t).ofReal_comp.mul_const (z₂ - z₁))
      exact h1.sin.congr_deriv (by ring)
    have h_zdiff : ‖z₂ - z₁‖ = Real.pi * |α - β| := by
      have heq : z₂ - z₁ = ((Real.pi * (α - β) : ℝ) : ℂ) := by dsimp only [z₁, z₂]; push_cast; ring
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos]
    have hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(z₂ - z₁) * Complex.cos (z₁ + t * (z₂ - z₁))‖ ≤
        Real.pi * |α - β| * Real.exp (Real.pi * v) := by
      intro t _
      rw [norm_mul, h_zdiff]
      have him : |(z₁ + (t : ℂ) * (z₂ - z₁)).im| = Real.pi * v := by
        have heq : z₂ - z₁ = ((Real.pi * (α - β) : ℝ) : ℂ) := by dsimp only [z₁, z₂]; push_cast; ring
        rw [heq]
        simp [z₁, Complex.mul_im, abs_of_nonneg (mul_nonneg Real.pi_pos.le hv)]
      calc Real.pi * |α - β| * ‖Complex.cos (z₁ + t * (z₂ - z₁))‖
          ≤ Real.pi * |α - β| * Real.exp |(z₁ + (t : ℂ) * (z₂ - z₁)).im| :=
            mul_le_mul_of_nonneg_left (h_cos_bd _) (by positivity)
        _ = Real.pi * |α - β| * Real.exp (Real.pi * v) := by rw [him]
    have hmvt := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      hf_d hbd (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    simpa [f] using hmvt
  have h_sum_sin : ‖Complex.sin z₂ + Complex.sin z₁‖ ≤ 2 * Real.exp (Real.pi * v) := by
    calc ‖Complex.sin z₂ + Complex.sin z₁‖
        ≤ ‖Complex.sin z₂‖ + ‖Complex.sin z₁‖ := norm_add_le _ _
      _ ≤ Real.exp |z₂.im| + Real.exp |z₁.im| := add_le_add (h_sin_bd _) (h_sin_bd _)
      _ = 2 * Real.exp (Real.pi * v) := by rw [hz₁_im, hz₂_im]; ring
  have h_eq : 1 / Complex.sin z₁ ^ 2 - 1 / Complex.sin z₂ ^ 2 =
      ((Complex.sin z₂ - Complex.sin z₁) * (Complex.sin z₂ + Complex.sin z₁)) /
        (Complex.sin z₁ ^ 2 * Complex.sin z₂ ^ 2) := by
    field_simp [hz₁_ne, hz₂_ne]; ring
  rw [h_eq, norm_div, norm_mul, norm_mul, norm_pow, norm_pow]
  have hden : (c_sin * Real.exp (Real.pi * v)) ^ 2 * (c_sin * Real.exp (Real.pi * v)) ^ 2 ≤
      ‖Complex.sin z₁‖ ^ 2 * ‖Complex.sin z₂‖ ^ 2 := by
    gcongr
  have hden_eq : (c_sin * Real.exp (Real.pi * v)) ^ 2 * (c_sin * Real.exp (Real.pi * v)) ^ 2 =
      c_sin ^ 4 * Real.exp (4 * Real.pi * v) := by
    rw [← Real.exp_nat_mul]
    calc c_sin ^ 2 * Real.exp (↑2 * (Real.pi * v)) * (c_sin ^ 2 * Real.exp (↑2 * (Real.pi * v)))
        = c_sin ^ 4 * (Real.exp (2 * Real.pi * v) * Real.exp (2 * Real.pi * v)) := by push_cast; ring
      _ = c_sin ^ 4 * Real.exp (4 * Real.pi * v) := by rw [← Real.exp_add]; ring_nf
  calc ‖Complex.sin z₂ - Complex.sin z₁‖ * ‖Complex.sin z₂ + Complex.sin z₁‖ /
        (‖Complex.sin z₁‖ ^ 2 * ‖Complex.sin z₂‖ ^ 2)
      ≤ (Real.pi * |α - β| * Real.exp (Real.pi * v)) * (2 * Real.exp (Real.pi * v)) /
          (c_sin ^ 4 * Real.exp (4 * Real.pi * v)) := by
        refine div_le_div₀ (by positivity) (mul_le_mul h_diff_sin h_sum_sin (norm_nonneg _) (by positivity))
          (by positivity) (by rw [← hden_eq]; exact hden)
    _ = (2 * Real.pi / c_sin ^ 4) * |α - β| * Real.exp (-2 * Real.pi * v) := by
        rw [show -2 * Real.pi * v = 2 * Real.pi * v - 4 * Real.pi * v by ring, Real.exp_sub,
          show 2 * Real.pi * v = Real.pi * v + Real.pi * v by ring, Real.exp_add]
        field_simp [hc_pos.ne']
        ring

set_option maxHeartbeats 800000 in
lemma contour_c0_eq_zero (θ Δ α : ℝ) (hθ : |θ| < Real.pi / 2)
    (hΔ : Δ ≥ 1) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hsumm_b : Summable (fun n : ℤ => rescaledFDeriv θ Δ (n + α)))
    (hsum0 : ∑' n : ℤ, rescaledFDeriv θ Δ (n + α) = 0) :
    (∫ v in Set.Ioo (0 : ℝ) Δ,
      (Complex.exp (-Complex.I * θ) / Complex.sin (Real.pi * (Complex.I * v - α)) ^ 2).im) +
      (Δ * Real.sin θ / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2).re = 0 := by
  let c₀ : ℝ :=
    (∫ v in Set.Ioo (0 : ℝ) Δ,
      (Complex.exp (-Complex.I * θ) / Complex.sin (Real.pi * (Complex.I * v - α)) ^ 2).im) +
      (Δ * Real.sin θ / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2).re
  have h_δ : 0 < min α (1 - α) := lt_min hα.1 (by linarith [hα.2])
  let δ : ℝ := min (min α (1 - α)) (1 / 2)
  have hδ0 : 0 < δ := lt_min h_δ (by norm_num)
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  have hα1 : δ ≤ α := (min_le_left _ _).trans (min_le_left _ _)
  have hα2 : α ≤ 1 - δ := by
    have : δ ≤ 1 - α := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  let c_sin : ℝ := Real.sin (Real.pi * δ) / Real.exp Real.pi
  have hc_pos : 0 < c_sin := div_pos (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])) (Real.exp_pos _)
  have h_rhs_bd : ∀ m : ℕ, m ≥ 1 →
      let y : ℝ := (m : ℝ) + α + 1 / 2
      |y * (vaalerInterpolant θ Δ α y - rescaledF θ Δ y) - c₀| ≤
        (2 * Δ ^ 2 / c_sin ^ 2) / (m : ℝ) := by
    intro m hm y
    have hy_pos : (m : ℝ) ≤ y := by dsimp only [y]; linarith [hα.1]
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hy_ne : y ≠ 0 := by linarith
    have hcr := contour_representation θ Δ α hθ hΔ hα y hy_ne
    have hsin_eq : Real.sin (Real.pi * (y - α)) ^ 2 = 1 := by
      have heq : Real.pi * (y - α) = (m : ℝ) * Real.pi + Real.pi / 2 := by dsimp only [y]; ring
      rw [heq, Real.sin_add, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi, Real.sin_pi_div_two, zero_mul, zero_add]
      rw [mul_one, ← pow_mul, mul_comm m 2, pow_mul]
      norm_num
    rw [hsin_eq, one_mul] at hcr
    rw [hcr]
    let Φ : ℝ → ℂ := fun v => Complex.exp (-Complex.I * θ) / Complex.sin (Real.pi * (Complex.I * v - α)) ^ 2
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
          ≤ 1 / (c_sin * Real.exp (Real.pi * v)) ^ 2 :=
            div_le_div_of_nonneg_left zero_le_one (by positivity) hden
        _ = 1 / c_sin ^ 2 * Real.exp (-2 * Real.pi * v) := by
            rw [mul_pow, ← Real.exp_nat_mul, show -2 * Real.pi * v = -((2 : ℕ) * (Real.pi * v)) by push_cast; ring, Real.exp_neg]; ring
    have hΦ_int : IntegrableOn (fun v : ℝ => (Φ v).im) (Set.Ioo 0 Δ) := by
      refine ((continuousOn_const (c := 1 / c_sin ^ 2)).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self).mono' ?_ ?_
      · refine Complex.continuous_im.comp_continuousOn ?_ |>.aestronglyMeasurable measurableSet_Ioo
        refine continuousOn_const.div (ContinuousOn.pow (Complex.continuous_sin.continuousOn.comp (by fun_prop) (fun _ _ => Set.mem_univ _)) 2) ?_
        intro v hv
        have hlb := sin_pi_iv_beta_lb hδ0 hδ1 hα1 hα2 v hv.1.le
        exact pow_ne_zero 2 (norm_ne_zero_iff.mp (by linarith [mul_pos hc_pos (Real.exp_pos (Real.pi * v))]))
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
        rw [Real.norm_eq_abs]
        exact (Complex.abs_im_le_norm _).trans ((hΦ_bd v hv.1.le).trans
          (mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hv.1]))))
    have hΦy_int : IntegrableOn (fun v : ℝ => (Φ v / ((y : ℂ) - Complex.I * v)).im) (Set.Ioo 0 Δ) := by
      refine ((continuousOn_const (c := (1 / c_sin ^ 2) / |y|)).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self).mono' ?_ ?_
      · refine Complex.continuous_im.comp_continuousOn ?_ |>.aestronglyMeasurable measurableSet_Ioo
        refine ContinuousOn.div (continuousOn_const.div (ContinuousOn.pow (Complex.continuous_sin.continuousOn.comp (by fun_prop) (fun _ _ => Set.mem_univ _)) 2) ?_) (by fun_prop) ?_
        · intro v hv; have hlb := sin_pi_iv_beta_lb hδ0 hδ1 hα1 hα2 v hv.1.le
          exact pow_ne_zero 2 (norm_ne_zero_iff.mp (by linarith [mul_pos hc_pos (Real.exp_pos (Real.pi * v))]))
        · intro v _ h; have hre := congr_arg Complex.re h; simp at hre; exact hy_ne hre
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
        rw [Real.norm_eq_abs]
        refine (Complex.abs_im_le_norm _).trans ?_
        rw [norm_div]
        have hy_norm : |y| ≤ ‖(y : ℂ) - Complex.I * v‖ := by
          have hsq : |y| ^ 2 ≤ ‖(y : ℂ) - Complex.I * v‖ ^ 2 := by
            rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq_abs]
            simp [Complex.sub_re, Complex.sub_im]; nlinarith [sq_nonneg v]
          exact (sq_le_sq₀ (abs_nonneg y) (norm_nonneg _)).mp hsq
        exact div_le_div₀ (by positivity) ((hΦ_bd v hv.1.le).trans
          (mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hv.1]))))
          (abs_pos.mpr hy_ne) hy_norm
    have h_eq_I : y * (∫ v in Set.Ioo (0 : ℝ) Δ,
        (Complex.exp (-Complex.I * θ) / (Complex.sin (Real.pi * (Complex.I * v - α)) ^ 2 * (y - Complex.I * v))).im) -
        (∫ v in Set.Ioo (0 : ℝ) Δ, (Φ v).im) =
        ∫ v in Set.Ioo (0 : ℝ) Δ, (Φ v * (Complex.I * v / (y - Complex.I * v))).im := by
      have h_mul : y * (∫ v in Set.Ioo (0 : ℝ) Δ,
          (Complex.exp (-Complex.I * θ) / (Complex.sin (Real.pi * (Complex.I * v - α)) ^ 2 * (y - Complex.I * v))).im) =
          ∫ v in Set.Ioo (0 : ℝ) Δ, (y * (Φ v / ((y : ℂ) - Complex.I * v))).im := by
        rw [← MeasureTheory.integral_const_mul]
        congr 1; ext v
        rw [← Complex.im_ofReal_mul]
        congr 1; dsimp only [Φ]; rw [div_div]; ring
      rw [h_mul, ← integral_sub (by simpa using hΦy_int.const_mul y) hΦ_int]
      congr 1; ext v
      rw [← Complex.sub_im]
      congr 1
      have hne : (y : ℂ) - Complex.I * v ≠ 0 := by intro h; have hre := congr_arg Complex.re h; simp at hre; exact hy_ne hre
      field_simp [hne]; ring
    have h_eq_R : -y * (Δ * Real.sin θ / (Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ - y))).re -
        (Δ * Real.sin θ / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2).re =
        -(Δ * Real.sin θ / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ / (Complex.I * Δ - y))).re := by
      have h_id : -((y : ℂ) * (Δ * Real.sin θ / (Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ - y)))) -
          (Δ * Real.sin θ / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2) =
          -(Δ * Real.sin θ / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ / (Complex.I * Δ - y))) := by
        have hne : Complex.I * (Δ : ℂ) - y ≠ 0 := by intro h; have hre := congr_arg Complex.re h; simp at hre; exact hy_ne hre
        have h_alg : -((y : ℂ) / (Complex.I * Δ - y)) - 1 = -(Complex.I * Δ / (Complex.I * Δ - y)) := by
          field_simp [hne]; ring
        calc -((y : ℂ) * (Δ * Real.sin θ / (Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ - y)))) -
              (Δ * Real.sin θ / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2)
            = (Δ * Real.sin θ / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2) * (-((y : ℂ) / (Complex.I * Δ - y)) - 1) := by rw [div_div]; ring
          _ = (Δ * Real.sin θ / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2) * (-(Complex.I * Δ / (Complex.I * Δ - y))) := by rw [h_alg]
          _ = -(Δ * Real.sin θ / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ / (Complex.I * Δ - y))) := by ring
      have hre := congr_arg Complex.re h_id
      simpa [Complex.re_ofReal_mul] using hre
    have h_tot : y * ((∫ v in Set.Ioo (0 : ℝ) Δ,
        (Complex.exp (-Complex.I * θ) / (Complex.sin (Real.pi * (Complex.I * v - α)) ^ 2 * (y - Complex.I * v))).im) -
        (Δ * Real.sin θ / (Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ - y))).re) - c₀ =
        (∫ v in Set.Ioo (0 : ℝ) Δ, (Φ v * (Complex.I * v / (y - Complex.I * v))).im) -
        (Δ * Real.sin θ / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ / (Complex.I * Δ - y))).re := by
      dsimp only [c₀]; linarith [h_eq_I, h_eq_R]
    rw [h_tot]
    have hI_bd : |∫ v in Set.Ioo (0 : ℝ) Δ, (Φ v * (Complex.I * v / (y - Complex.I * v))).im| ≤ (Δ ^ 2 / c_sin ^ 2) / m := by
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_integral_norm _).trans ?_
      have h_c : ∫ _ in Set.Ioo (0 : ℝ) Δ, (1 / c_sin ^ 2) * (Δ / m) = (Δ ^ 2 / c_sin ^ 2) / m := by
        rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith), sub_zero, smul_eq_mul]; ring
      rw [← h_c]
      refine setIntegral_mono_on ?_ (continuousOn_const.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self) measurableSet_Ioo fun v hv => ?_
      · refine (continuousOn_const.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self :
          IntegrableOn (fun _ => (1 / c_sin ^ 2) * (Δ / m)) (Set.Ioo 0 Δ)).mono' ?_ ?_
        · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
          refine ContinuousOn.norm (Complex.continuous_im.comp_continuousOn ?_)
          refine ContinuousOn.mul ?_ (ContinuousOn.div (by fun_prop) (by fun_prop) fun v _ h => ?_)
          · refine continuousOn_const.div (ContinuousOn.pow (Complex.continuous_sin.continuousOn.comp (by fun_prop) (fun _ _ => Set.mem_univ _)) 2) ?_
            intro v hv; have hlb := sin_pi_iv_beta_lb hδ0 hδ1 hα1 hα2 v hv.1.le
            exact pow_ne_zero 2 (norm_ne_zero_iff.mp (by linarith [mul_pos hc_pos (Real.exp_pos (Real.pi * v))]))
          · have hre := congr_arg Complex.re h; simp at hre; exact hy_ne hre
        · filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
          rw [Real.norm_eq_abs, abs_norm, Real.norm_eq_abs]
          refine (Complex.abs_im_le_norm _).trans ?_
          rw [norm_mul]
          have hΦ' : ‖Φ v‖ ≤ 1 / c_sin ^ 2 := (hΦ_bd v hv.1.le).trans
            (mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hv.1])))
          have hy_n : (m : ℝ) ≤ ‖(y : ℂ) - Complex.I * v‖ := by
            have hsq : (m : ℝ) ^ 2 ≤ ‖(y : ℂ) - Complex.I * v‖ ^ 2 := by
              rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; nlinarith [sq_nonneg v]
            exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hsq
          have h_rhs : ‖Complex.I * v / ((y : ℂ) - Complex.I * v)‖ ≤ Δ / m := by
            rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv.1]
            exact div_le_div₀ (by positivity) hv.2.le hm_pos hy_n
          exact mul_le_mul hΦ' h_rhs (norm_nonneg _) (by positivity)
      · rw [Real.norm_eq_abs]
        refine (Complex.abs_im_le_norm _).trans ?_
        rw [norm_mul]
        have hΦ' : ‖Φ v‖ ≤ 1 / c_sin ^ 2 := (hΦ_bd v hv.1.le).trans
          (mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hv.1])))
        have hy_n : (m : ℝ) ≤ ‖(y : ℂ) - Complex.I * v‖ := by
          have hsq : (m : ℝ) ^ 2 ≤ ‖(y : ℂ) - Complex.I * v‖ ^ 2 := by
            rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; nlinarith [sq_nonneg v]
          exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hsq
        have h_rhs : ‖Complex.I * v / ((y : ℂ) - Complex.I * v)‖ ≤ Δ / m := by
          rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv.1]
          exact div_le_div₀ (by positivity) hv.2.le hm_pos hy_n
        exact mul_le_mul hΦ' h_rhs (norm_nonneg _) (by positivity)
    have hR_bd : |(Δ * Real.sin θ / Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ / (Complex.I * Δ - y))).re| ≤
        (Δ ^ 2 / c_sin ^ 2) / m := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by linarith : 0 < Δ), norm_pow, norm_div, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < Δ)]
      have hlb := sin_pi_iv_beta_lb hδ0 hδ1 hα1 hα2 Δ (by linarith)
      have hden : c_sin ^ 2 ≤ ‖Complex.sin (Real.pi * (Complex.I * Δ - α))‖ ^ 2 := by
        have h1 : 1 ≤ Real.exp (Real.pi * Δ) := Real.one_le_exp (by positivity)
        have h2 : c_sin ≤ c_sin * Real.exp (Real.pi * Δ) := le_mul_of_one_le_right hc_pos.le h1
        exact sq_le_sq' (by linarith) (h2.trans hlb)
      have hy_n : (m : ℝ) ≤ ‖Complex.I * Δ - y‖ := by
        have hsq : (m : ℝ) ^ 2 ≤ ‖Complex.I * Δ - y‖ ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; nlinarith [sq_nonneg Δ]
        exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hsq
      calc Δ * |Real.sin θ| / ‖Complex.sin (Real.pi * (Complex.I * Δ - α))‖ ^ 2 * (Δ / ‖Complex.I * Δ - y‖)
          ≤ Δ * 1 / c_sin ^ 2 * (Δ / m) := by
            gcongr
            exact Real.abs_sin_le_one θ
        _ = (Δ ^ 2 / c_sin ^ 2) / m := by ring
    calc |(_ : ℝ) - _| ≤ |∫ v in Set.Ioo (0 : ℝ) Δ, _| + |(_ : ℝ)| := abs_sub _ _
      _ ≤ (Δ ^ 2 / c_sin ^ 2) / m + (Δ ^ 2 / c_sin ^ 2) / m := add_le_add hI_bd hR_bd
      _ = (2 * Δ ^ 2 / c_sin ^ 2) / m := by ring
  have ha_summ : Summable (fun n : ℤ => |rescaledF θ Δ (n + α)|) := rescaledF_summable θ Δ α hΔ hα
  have hb_mul_summ : Summable (fun n : ℤ => |(n + α) * rescaledFDeriv θ Δ (n + α)|) :=
    rescaledFDeriv_mul_summable θ Δ α hΔ hα
  let S_a : ℝ := ∑' n : ℤ, |rescaledF θ Δ (n + α)|
  let S_b : ℝ := ∑' n : ℤ, |(n + α) * rescaledFDeriv θ Δ (n + α)|
  let C_half : ℝ := ∑' k : ℤ, 1 / ((k : ℝ) + 1 / 2) ^ 2
  have hC_half_summ : Summable (fun k : ℤ => 1 / ((k : ℝ) + 1 / 2) ^ 2) :=
    summable_inv_add_sq_of_ne_zero (1 / 2) (fun k h0 => by
      have h1 : (k : ℝ) * 2 + 1 = 0 := by linarith
      have h2 : k * 2 + 1 = 0 := by exact_mod_cast h1
      omega)
  let C_lhs : ℝ := 4 * Δ ^ 2 + (4 * S_a + 16 * Δ ^ 2 * C_half + 2 * S_b + 48 * Δ ^ 2) / Real.pi ^ 2
  have h_lhs_bd : ∀ m : ℕ, m ≥ Nat.ceil (2 * Δ) + 2 →
      let y : ℝ := (m : ℝ) + α + 1 / 2
      |y * (vaalerInterpolant θ Δ α y - rescaledF θ Δ y)| ≤ C_lhs / (m : ℝ) := by
    intro m hm y
    have hm_ge2 : (2 : ℝ) * Δ + 2 ≤ m := by
      have h1 : (Nat.ceil (2 * Δ) + 2 : ℝ) ≤ m := by exact_mod_cast hm
      linarith [Nat.le_ceil (2 * Δ)]
    have hm_pos : (0 : ℝ) < m := by linarith
    have hy_ge_m : (m : ℝ) ≤ y := by dsimp only [y]; linarith [hα.1]
    have hy_ge_Δ : Δ ≤ y := by linarith
    have hF_bd : |y * rescaledF θ Δ y| ≤ 4 * Δ ^ 2 / m := by
      have h1 : 1 ≤ |y / Δ| := by
        rw [abs_div, abs_of_pos (by linarith : 0 < Δ), one_le_div (by linarith), abs_of_pos (by linarith : 0 < y)]
        exact hy_ge_Δ
      have hbd := kernelK_bound_large θ h1
      unfold rescaledF
      rw [abs_mul, abs_of_pos (by linarith)]
      calc y * |kernelK θ (y / Δ)| ≤ y * (4 / (y / Δ) ^ 2) := mul_le_mul_of_nonneg_left hbd (by linarith)
        _ = 4 * Δ ^ 2 / y := by field_simp [(by linarith : y ≠ 0), (by linarith : Δ ≠ 0)]
        _ ≤ 4 * Δ ^ 2 / m := div_le_div_of_nonneg_left (by positivity) hm_pos hy_ge_m
    have hlat : ¬∃ n : ℤ, y = n + α := by
      rintro ⟨n, hn⟩
      have h1 : (m : ℝ) + 1 / 2 = n := by dsimp only [y] at hn; linarith
      have h2 : (2 * m + 1 : ℤ) = 2 * n := by exact_mod_cast (by linarith : (2 * (m : ℝ) + 1) = 2 * (n : ℝ))
      omega
    have hM_eq : vaalerInterpolant θ Δ α y = (1 / Real.pi ^ 2) *
        ∑' n : ℤ, (rescaledF θ Δ (n + α) / (y - n - α) ^ 2 + rescaledFDeriv θ Δ (n + α) / (y - n - α)) := by
      unfold vaalerInterpolant
      simp only [if_neg hlat]
      have hsin_eq : Real.sin (Real.pi * (y - α)) ^ 2 = 1 := by
        have heq : Real.pi * (y - α) = (m : ℝ) * Real.pi + Real.pi / 2 := by dsimp only [y]; ring
        rw [heq, Real.sin_add, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi, Real.sin_pi_div_two, zero_mul, zero_add]
        rw [mul_one, ← pow_mul, mul_comm m 2, pow_mul]
      rw [hsin_eq]; ring
    have ha_s : Summable (fun n : ℤ => rescaledF θ Δ (n + α) / (y - n - α) ^ 2) := by
      refine (ha_summ.mul_left 4).of_norm_bounded fun n => ?_
      have h_half : (1 / 2 : ℝ) ≤ |y - n - α| := by
        have heq : y - n - α = ((m - n : ℤ) : ℝ) + 1 / 2 := by dsimp only [y]; push_cast; ring
        rw [heq]
        rcases le_or_gt (0 : ℤ) (m - n) with h | h
        · have : (0 : ℝ) ≤ (m - n : ℤ) := by exact_mod_cast h
          rw [abs_of_pos (by linarith)]; linarith
        · have : ((m - n : ℤ) : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h
          rw [abs_of_neg (by linarith)]; linarith
      have h_inv : 1 / (y - n - α) ^ 2 ≤ 4 := by
        have hsq : (1 / 4 : ℝ) ≤ (y - n - α) ^ 2 := by rw [← sq_abs]; nlinarith
        rw [div_le_iff₀ (by linarith)]
        linarith
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg (y - n - α)), div_eq_mul_one_div]
      calc |rescaledF θ Δ (n + α)| * (1 / (y - n - α) ^ 2) ≤ |rescaledF θ Δ (n + α)| * 4 := by gcongr
        _ = 4 * |rescaledF θ Δ (n + α)| := mul_comm _ _
    have hb_s : Summable (fun n : ℤ => rescaledFDeriv θ Δ (n + α) / (y - n - α)) := by
      refine (hsumm_b.abs.mul_left 2).of_norm_bounded fun n => ?_
      have h_half : (1 / 2 : ℝ) ≤ |y - n - α| := by
        have heq : y - n - α = ((m - n : ℤ) : ℝ) + 1 / 2 := by dsimp only [y]; push_cast; ring
        rw [heq]
        rcases le_or_gt (0 : ℤ) (m - n) with h | h
        · have : (0 : ℝ) ≤ (m - n : ℤ) := by exact_mod_cast h
          rw [abs_of_pos (by linarith)]; linarith
        · have : ((m - n : ℤ) : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h
          rw [abs_of_neg (by linarith)]; linarith
      rw [Real.norm_eq_abs, abs_div, div_eq_mul_one_div]
      have h_inv : 1 / |y - n - α| ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
      calc |rescaledFDeriv θ Δ (n + α)| * (1 / |y - n - α|) ≤ |rescaledFDeriv θ Δ (n + α)| * 2 := by gcongr
        _ = 2 * |rescaledFDeriv θ Δ (n + α)| := mul_comm _ _
    have hb_eq : ∑' n : ℤ, y * (rescaledFDeriv θ Δ (n + α) / (y - n - α)) =
        ∑' n : ℤ, (n + α) * rescaledFDeriv θ Δ (n + α) / (y - n - α) := by
      have h_id : ∀ n : ℤ, y * (rescaledFDeriv θ Δ (n + α) / (y - n - α)) =
          rescaledFDeriv θ Δ (n + α) + (n + α) * rescaledFDeriv θ Δ (n + α) / (y - n - α) := by
        intro n
        have hne : y - n - α ≠ 0 := fun h => hlat ⟨n, by linarith⟩
        field_simp [hne]; ring
      have h_bm_s : Summable (fun n : ℤ => (n + α) * rescaledFDeriv θ Δ (n + α) / (y - n - α)) := by
        refine (hb_mul_summ.mul_left 2).of_norm_bounded fun n => ?_
        have h_half : (1 / 2 : ℝ) ≤ |y - n - α| := by
          have heq : y - n - α = ((m - n : ℤ) : ℝ) + 1 / 2 := by dsimp only [y]; push_cast; ring
          rw [heq]
          rcases le_or_gt (0 : ℤ) (m - n) with h | h
          · have : (0 : ℝ) ≤ (m - n : ℤ) := by exact_mod_cast h
            rw [abs_of_pos (by linarith)]; linarith
          · have : ((m - n : ℤ) : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h
            rw [abs_of_neg (by linarith)]; linarith
        rw [Real.norm_eq_abs, abs_div, div_eq_mul_one_div]
        have h_inv : 1 / |y - n - α| ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
        calc |(n + α) * rescaledFDeriv θ Δ (n + α)| * (1 / |y - n - α|) ≤ _ * 2 := by gcongr
          _ = 2 * |(n + α) * rescaledFDeriv θ Δ (n + α)| := mul_comm _ _
      simp_rw [h_id, Summable.tsum_add hsumm_b h_bm_s, hsum0, zero_add]
    have ha_bd : |∑' n : ℤ, y * (rescaledF θ Δ (n + α) / (y - n - α) ^ 2)| ≤
        (4 * S_a + 16 * Δ ^ 2 * C_half) / m := by
      have h_term : ∀ n : ℤ, |y * (rescaledF θ Δ (n + α) / (y - n - α) ^ 2)| ≤
          4 * |rescaledF θ Δ (n + α)| / y + 16 * Δ ^ 2 / y * (1 / (y - n - α) ^ 2) := by
        intro n
        rw [abs_mul, abs_div, abs_of_pos (by linarith), abs_of_nonneg (sq_nonneg (y - n - α))]
        rcases le_or_gt (y / 2) |y - n - α| with h | h
        · have hy_pos : 0 < y := by linarith
          have h_sq_pos : 0 < (y - n - α) ^ 2 := by
            have hsq : y ^ 2 / 4 ≤ (y - n - α) ^ 2 := by rw [← sq_abs (y - n - α)]; nlinarith
            nlinarith
          have h1 : y / (y - n - α) ^ 2 ≤ 4 / y := by
            have hsq : y ^ 2 / 4 ≤ (y - n - α) ^ 2 := by rw [← sq_abs (y - n - α)]; nlinarith
            rw [div_le_div_iff₀ h_sq_pos hy_pos]
            nlinarith
          calc y * (|rescaledF θ Δ (n + α)| / (y - n - α) ^ 2)
              = |rescaledF θ Δ (n + α)| * (y / (y - n - α) ^ 2) := by ring
            _ ≤ |rescaledF θ Δ (n + α)| * (4 / y) := by gcongr
            _ = 4 * |rescaledF θ Δ (n + α)| / y := by ring
            _ ≤ 4 * |rescaledF θ Δ (n + α)| / y + 16 * Δ ^ 2 / y * (1 / (y - n - α) ^ 2) := by
                linarith [show (0 : ℝ) ≤ 16 * Δ ^ 2 / y * (1 / (y - n - α) ^ 2) by positivity]
        · have hy_pos : 0 < y := by linarith
          have hna : y / 2 < |(n : ℝ) + α| := by
            have := abs_sub_abs_le_abs_sub y (n + α)
            rw [abs_of_pos hy_pos] at this
            linarith [show |y - ((n : ℝ) + α)| = |y - n - α| by ring_nf]
          have hna_ge_Δ : 1 ≤ |((n : ℝ) + α) / Δ| := by
            rw [abs_div, abs_of_pos (by linarith : 0 < Δ), one_le_div (by linarith : 0 < Δ)]
            linarith
          have hF_n := kernelK_bound_large θ hna_ge_Δ
          have hF_n' : |rescaledF θ Δ (n + α)| ≤ 16 * Δ ^ 2 / y ^ 2 := by
            unfold rescaledF
            have heq : 4 / (((n : ℝ) + α) / Δ) ^ 2 = 4 * Δ ^ 2 / ((n : ℝ) + α) ^ 2 := by
              have hne : (n : ℝ) + α ≠ 0 := by intro h0; rw [h0, abs_zero] at hna; linarith
              field_simp [hne, (by linarith : Δ ≠ 0)]
            rw [heq] at hF_n
            have hsq : y ^ 2 / 4 ≤ ((n : ℝ) + α) ^ 2 := by rw [← sq_abs ((n : ℝ) + α)]; nlinarith
            calc |kernelK θ (((n : ℝ) + α) / Δ)| ≤ 4 * Δ ^ 2 / ((n : ℝ) + α) ^ 2 := hF_n
              _ ≤ 4 * Δ ^ 2 / (y ^ 2 / 4) := div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
              _ = 16 * Δ ^ 2 / y ^ 2 := by ring
          calc y * (|rescaledF θ Δ (n + α)| / (y - n - α) ^ 2)
              ≤ y * ((16 * Δ ^ 2 / y ^ 2) / (y - n - α) ^ 2) :=
                mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hF_n' (sq_nonneg _)) hy_pos.le
            _ = 16 * Δ ^ 2 / y * (1 / (y - n - α) ^ 2) := by field_simp [hy_pos.ne']
            _ ≤ 4 * |rescaledF θ Δ (n + α)| / y + 16 * Δ ^ 2 / y * (1 / (y - n - α) ^ 2) := by
                linarith [show (0 : ℝ) ≤ 4 * |rescaledF θ Δ (n + α)| / y by positivity]
      have h_c_eq : ∑' n : ℤ, (1 : ℝ) / (y - n - α) ^ 2 = C_half := by
        have h_shift : (fun n : ℤ => (1 : ℝ) / (y - n - α) ^ 2) = fun n : ℤ => 1 / (((m - n : ℤ) : ℝ) + 1 / 2) ^ 2 := by
          ext n; congr 1; dsimp only [y]; push_cast; ring
        rw [h_shift]
        exact Equiv.tsum_eq (Equiv.subLeft (m : ℤ)) (fun k => 1 / ((k : ℝ) + 1 / 2) ^ 2)
      have h_s_inv : Summable (fun n : ℤ => 1 / (y - n - α) ^ 2) := by
        have h_shift : (fun n : ℤ => (1 : ℝ) / (y - n - α) ^ 2) =
            (fun k : ℤ => 1 / ((k : ℝ) + 1 / 2) ^ 2) ∘ Equiv.subLeft (m : ℤ) := by
          ext n; dsimp only [y, Function.comp_apply, Equiv.subLeft_apply]; push_cast; ring
        rw [h_shift, (Equiv.subLeft (m : ℤ)).summable_iff]
        exact hC_half_summ
      have h_sum_term : Summable (fun n : ℤ => 4 * |rescaledF θ Δ (n + α)| / y + 16 * Δ ^ 2 / y * (1 / (y - n - α) ^ 2)) :=
        ((ha_summ.mul_left (4 / y)).congr (fun n => by ring)).add (h_s_inv.mul_left (16 * Δ ^ 2 / y))
      calc |∑' n : ℤ, y * (rescaledF θ Δ (n + α) / (y - n - α) ^ 2)|
          ≤ ∑' n : ℤ, |y * (rescaledF θ Δ (n + α) / (y - n - α) ^ 2)| :=
            by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (ha_s.mul_left y)
        _ ≤ ∑' n : ℤ, (4 * |rescaledF θ Δ (n + α)| / y + 16 * Δ ^ 2 / y * (1 / (y - n - α) ^ 2)) :=
            Summable.tsum_le_tsum h_term (ha_s.mul_left y).abs h_sum_term
        _ = 4 * S_a / y + 16 * Δ ^ 2 * C_half / y := by
            rw [Summable.tsum_add ((ha_summ.mul_left (4 / y)).congr (fun n => by ring)) (h_s_inv.mul_left (16 * Δ ^ 2 / y))]
            rw [show (fun n : ℤ => 4 * |rescaledF θ Δ (n + α)| / y) = fun n : ℤ => (4 / y) * |rescaledF θ Δ (n + α)| by ext n; ring,
              tsum_mul_left, tsum_mul_left, h_c_eq]
            dsimp only [S_a]; ring
        _ ≤ (4 * S_a + 16 * Δ ^ 2 * C_half) / m := by
            rw [← add_div]
            exact div_le_div_of_nonneg_left (by positivity) hm_pos hy_ge_m
    have hb_bd : |∑' n : ℤ, (n + α) * rescaledFDeriv θ Δ (n + α) / (y - n - α)| ≤
        (2 * S_b + 48 * Δ ^ 2) / m := by
      let F_fin : Finset ℤ := Finset.Icc 0 (2 * (m : ℤ))
      let g_fin : ℤ → ℝ := fun n => if n ∈ F_fin then 16 * Δ ^ 2 / (m : ℝ) ^ 2 else 0
      have hg_summ : Summable g_fin := summable_of_ne_finset_zero (s := F_fin) (fun n hn => by simp [g_fin, hn])
      have h_term : ∀ n : ℤ, |(n + α) * rescaledFDeriv θ Δ (n + α) / (y - n - α)| ≤
          2 * |(n + α) * rescaledFDeriv θ Δ (n + α)| / y + g_fin n := by
        intro n
        rw [abs_div]
        rcases le_or_gt (y / 2) |y - n - α| with h | h
        · calc |(n + α) * rescaledFDeriv θ Δ (n + α)| / |y - n - α|
              ≤ |(n + α) * rescaledFDeriv θ Δ (n + α)| / (y / 2) :=
                div_le_div_of_nonneg_left (abs_nonneg _) (by linarith) h
            _ = 2 * |(n + α) * rescaledFDeriv θ Δ (n + α)| / y := by ring
            _ ≤ _ := by
                have : 0 ≤ g_fin n := by dsimp only [g_fin]; split_ifs <;> positivity
                linarith
        · have h_mem : n ∈ F_fin := by
            have hlt := abs_lt.mp h
            have hn0 : (0 : ℝ) ≤ n := by dsimp only [y] at hlt; linarith [hα.1, hα.2]
            have hn2 : (n : ℝ) ≤ 2 * m := by dsimp only [y] at hlt; linarith [hα.1, hα.2]
            refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
            · have h' : (-1 : ℤ) < n := by exact_mod_cast (by linarith : (-1 : ℝ) < n)
              omega
            · have h' : n < 2 * (m : ℤ) + 1 := by exact_mod_cast (by linarith : (n : ℝ) < 2 * (m : ℝ) + 1)
              omega
          have hna : y / 2 < |(n : ℝ) + α| := by
            have := abs_sub_abs_le_abs_sub y (n + α)
            rw [abs_of_pos (by linarith)] at this
            linarith [show |y - ((n : ℝ) + α)| = |y - n - α| by ring_nf]
          have hne : (n : ℝ) + α ≠ 0 := by intro h0; rw [h0, abs_zero] at hna; linarith
          have hFd := rescaledFDeriv_mul_bound θ Δ (n + α) (by linarith) hne
          have hsq : y ^ 2 / 4 ≤ ((n : ℝ) + α) ^ 2 := by rw [← sq_abs ((n : ℝ) + α)]; nlinarith
          have hFd' : |(n + α) * rescaledFDeriv θ Δ (n + α)| ≤ 8 * Δ ^ 2 / y ^ 2 := by
            calc |(n + α) * rescaledFDeriv θ Δ (n + α)| ≤ 2 * Δ ^ 2 / ((n : ℝ) + α) ^ 2 := hFd
              _ ≤ 2 * Δ ^ 2 / (y ^ 2 / 4) := div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
              _ = 8 * Δ ^ 2 / y ^ 2 := by ring
          have h_half : (1 / 2 : ℝ) ≤ |y - n - α| := by
            have heq : y - n - α = ((m - n : ℤ) : ℝ) + 1 / 2 := by dsimp only [y]; push_cast; ring
            rw [heq]
            rcases le_or_gt (0 : ℤ) (m - n) with h1 | h1
            · have : (0 : ℝ) ≤ (m - n : ℤ) := by exact_mod_cast h1
              rw [abs_of_pos (by linarith)]; linarith
            · have : ((m - n : ℤ) : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h1
              rw [abs_of_neg (by linarith)]; linarith
          have hg_eq : g_fin n = 16 * Δ ^ 2 / (m : ℝ) ^ 2 := by simp [g_fin, h_mem]
          rw [hg_eq]
          have h_my : (m : ℝ) ^ 2 ≤ y ^ 2 := sq_le_sq' (by linarith) hy_ge_m
          calc |(n + α) * rescaledFDeriv θ Δ (n + α)| / |y - n - α|
              ≤ (8 * Δ ^ 2 / y ^ 2) / (1 / 2) := div_le_div₀ (by positivity) hFd' (by norm_num) h_half
            _ = 16 * Δ ^ 2 / y ^ 2 := by ring
            _ ≤ 16 * Δ ^ 2 / (m : ℝ) ^ 2 := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hm_pos) h_my
            _ ≤ _ := by linarith [show (0 : ℝ) ≤ 2 * |(n + α) * rescaledFDeriv θ Δ (n + α)| / y by positivity]
      have h_bm_s : Summable (fun n : ℤ => (n + α) * rescaledFDeriv θ Δ (n + α) / (y - n - α)) := by
        refine (hb_mul_summ.mul_left 2).of_norm_bounded fun n => ?_
        have h_half : (1 / 2 : ℝ) ≤ |y - n - α| := by
          have heq : y - n - α = ((m - n : ℤ) : ℝ) + 1 / 2 := by dsimp only [y]; push_cast; ring
          rw [heq]
          rcases le_or_gt (0 : ℤ) (m - n) with h1 | h1
          · have : (0 : ℝ) ≤ (m - n : ℤ) := by exact_mod_cast h1
            rw [abs_of_pos (by linarith)]; linarith
          · have : ((m - n : ℤ) : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h1
            rw [abs_of_neg (by linarith)]; linarith
        rw [Real.norm_eq_abs, abs_div, div_eq_mul_one_div]
        have h_inv : 1 / |y - n - α| ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
        calc |(n + α) * rescaledFDeriv θ Δ (n + α)| * (1 / |y - n - α|) ≤ _ * 2 := by gcongr
          _ = 2 * |(n + α) * rescaledFDeriv θ Δ (n + α)| := mul_comm _ _
      have hg_sum : ∑' n : ℤ, g_fin n ≤ 48 * Δ ^ 2 / m := by
        rw [tsum_eq_sum (s := F_fin) (fun n hn => by simp [g_fin, hn])]
        have h_eq : ∑ n ∈ F_fin, g_fin n = (F_fin.card : ℝ) * (16 * Δ ^ 2 / (m : ℝ) ^ 2) := by
          rw [Finset.sum_congr rfl (fun n hn => by simp [g_fin, hn]), Finset.sum_const, nsmul_eq_mul]
        rw [h_eq]
        have hcard : (F_fin.card : ℝ) ≤ 3 * m := by
          have h1 : F_fin.card = (2 * m + 1 : ℕ) := by
            dsimp only [F_fin]; rw [Int.card_Icc]; omega
          rw [h1]; push_cast
          have : (1 : ℝ) ≤ m := by linarith
          linarith
        calc (F_fin.card : ℝ) * (16 * Δ ^ 2 / (m : ℝ) ^ 2)
            ≤ (3 * m) * (16 * Δ ^ 2 / (m : ℝ) ^ 2) := by gcongr
          _ = 48 * Δ ^ 2 / m := by field_simp [hm_pos.ne']; ring
      have h_sum_term : Summable (fun n : ℤ => 2 * |(n + α) * rescaledFDeriv θ Δ (n + α)| / y + g_fin n) :=
        ((hb_mul_summ.mul_left (2 / y)).congr (fun n => by ring)).add hg_summ
      calc |∑' n : ℤ, (n + α) * rescaledFDeriv θ Δ (n + α) / (y - n - α)|
          ≤ ∑' n : ℤ, |(n + α) * rescaledFDeriv θ Δ (n + α) / (y - n - α)| :=
            by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm h_bm_s
        _ ≤ ∑' n : ℤ, (2 * |(n + α) * rescaledFDeriv θ Δ (n + α)| / y + g_fin n) :=
            Summable.tsum_le_tsum h_term h_bm_s.abs h_sum_term
        _ = 2 * S_b / y + ∑' n : ℤ, g_fin n := by
            rw [Summable.tsum_add ((hb_mul_summ.mul_left (2 / y)).congr (fun n => by ring)) hg_summ,
              show (fun n : ℤ => 2 * |(n + α) * rescaledFDeriv θ Δ (n + α)| / y) =
                fun n : ℤ => (2 / y) * |(n + α) * rescaledFDeriv θ Δ (n + α)| by ext n; ring,
              tsum_mul_left]
            dsimp only [S_b]; ring
        _ ≤ 2 * S_b / m + 48 * Δ ^ 2 / m := by
            gcongr; exact div_le_div_of_nonneg_left (by positivity) hm_pos hy_ge_m
        _ = (2 * S_b + 48 * Δ ^ 2) / m := by ring
    have h_yM : |y * vaalerInterpolant θ Δ α y| ≤
        (4 * S_a + 16 * Δ ^ 2 * C_half + 2 * S_b + 48 * Δ ^ 2) / Real.pi ^ 2 / m := by
      rw [hM_eq, show y * ((1 / Real.pi ^ 2) *
          ∑' n : ℤ, (rescaledF θ Δ (n + α) / (y - n - α) ^ 2 + rescaledFDeriv θ Δ (n + α) / (y - n - α))) =
          (1 / Real.pi ^ 2) * (∑' n : ℤ, y * (rescaledF θ Δ (n + α) / (y - n - α) ^ 2) +
            ∑' n : ℤ, y * (rescaledFDeriv θ Δ (n + α) / (y - n - α))) by
        rw [← tsum_mul_left, Summable.tsum_add ha_s hb_s, mul_add, tsum_mul_left, tsum_mul_left]; ring]
      rw [hb_eq, abs_mul, abs_of_pos (by positivity : 0 < 1 / Real.pi ^ 2)]
      calc (1 / Real.pi ^ 2) * |∑' n : ℤ, y * (rescaledF θ Δ (n + α) / (y - n - α) ^ 2) +
            ∑' n : ℤ, (n + α) * rescaledFDeriv θ Δ (n + α) / (y - n - α)|
          ≤ (1 / Real.pi ^ 2) * (|∑' n : ℤ, y * (rescaledF θ Δ (n + α) / (y - n - α) ^ 2)| +
            |∑' n : ℤ, (n + α) * rescaledFDeriv θ Δ (n + α) / (y - n - α)|) := by
            gcongr; exact abs_add_le _ _
        _ ≤ (1 / Real.pi ^ 2) * ((4 * S_a + 16 * Δ ^ 2 * C_half) / m + (2 * S_b + 48 * Δ ^ 2) / m) := by gcongr
        _ = (4 * S_a + 16 * Δ ^ 2 * C_half + 2 * S_b + 48 * Δ ^ 2) / Real.pi ^ 2 / m := by ring
    calc |y * (vaalerInterpolant θ Δ α y - rescaledF θ Δ y)|
        = |y * vaalerInterpolant θ Δ α y - y * rescaledF θ Δ y| := by ring_nf
      _ ≤ |y * vaalerInterpolant θ Δ α y| + |y * rescaledF θ Δ y| := abs_sub _ _
      _ ≤ (4 * S_a + 16 * Δ ^ 2 * C_half + 2 * S_b + 48 * Δ ^ 2) / Real.pi ^ 2 / m + 4 * Δ ^ 2 / m :=
          add_le_add h_yM hF_bd
      _ = C_lhs / m := by dsimp only [C_lhs]; ring
  by_contra hc0
  have h_pos : 0 < |c₀| := abs_pos.mpr hc0
  let M : ℕ := max (Nat.ceil (2 * Δ) + 2) (Nat.ceil ((2 * Δ ^ 2 / c_sin ^ 2 + C_lhs) / |c₀|) + 1)
  have hM1 : M ≥ 1 := by omega
  have hM2 : M ≥ Nat.ceil (2 * Δ) + 2 := le_max_left _ _
  have h1 := h_rhs_bd M hM1
  have h2 := h_lhs_bd M hM2
  have hc_le : |c₀| ≤ (2 * Δ ^ 2 / c_sin ^ 2 + C_lhs) / (M : ℝ) := by
    have h_tri : |c₀| ≤ |((M : ℝ) + α + 1 / 2) * (vaalerInterpolant θ Δ α ((M : ℝ) + α + 1 / 2) -
        rescaledF θ Δ ((M : ℝ) + α + 1 / 2)) - c₀| +
        |((M : ℝ) + α + 1 / 2) * (vaalerInterpolant θ Δ α ((M : ℝ) + α + 1 / 2) -
        rescaledF θ Δ ((M : ℝ) + α + 1 / 2))| := by
      have := abs_sub c₀ (((M : ℝ) + α + 1 / 2) * (vaalerInterpolant θ Δ α ((M : ℝ) + α + 1 / 2) -
        rescaledF θ Δ ((M : ℝ) + α + 1 / 2)))
      rw [abs_sub_comm] at h1
      linarith [abs_sub_le (0 : ℝ) (((M : ℝ) + α + 1 / 2) * (vaalerInterpolant θ Δ α ((M : ℝ) + α + 1 / 2) -
        rescaledF θ Δ ((M : ℝ) + α + 1 / 2))) c₀]
    linarith [show (2 * Δ ^ 2 / c_sin ^ 2) / (M : ℝ) + C_lhs / (M : ℝ) = (2 * Δ ^ 2 / c_sin ^ 2 + C_lhs) / (M : ℝ) by ring]
  have hM_gt : (2 * Δ ^ 2 / c_sin ^ 2 + C_lhs) / |c₀| < (M : ℝ) := by
    have h1 : (Nat.ceil ((2 * Δ ^ 2 / c_sin ^ 2 + C_lhs) / |c₀|) + 1 : ℝ) ≤ M := by
      exact_mod_cast le_max_right (Nat.ceil (2 * Δ) + 2) (Nat.ceil ((2 * Δ ^ 2 / c_sin ^ 2 + C_lhs) / |c₀|) + 1)
    linarith [Nat.le_ceil ((2 * Δ ^ 2 / c_sin ^ 2 + C_lhs) / |c₀|)]
  have hM_pos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  rw [div_lt_iff₀ h_pos] at hM_gt
  rw [le_div_iff₀ hM_pos] at hc_le
  linarith


end PolarEvaluation
