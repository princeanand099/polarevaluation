import PolarEvaluation.Basic
import PolarEvaluation.ExplicitFormulae
import PolarEvaluation.ShiftedLatticeCoreA

noncomputable section

open Complex Real MeasureTheory Filter Topology
open scoped FourierTransform

namespace PolarEvaluation

/-! ### Helper Lemmas for `J(y, θ)` (Lemma 3.3) -/

def cTheta (θ v : ℝ) : ℂ :=
  Complex.exp (-Complex.I * θ) / Complex.cos (θ + Complex.I * Real.pi * v) ^ 2

def uTheta (θ v : ℝ) : ℂ :=
  Real.exp (-Real.pi * v) / (Real.pi * Complex.cos (θ + Complex.I * Real.pi * v))

lemma cos_normSq_eq (θ v : ℝ) :
    ‖Complex.cos (θ + Complex.I * Real.pi * v)‖ ^ 2 = Real.sinh (Real.pi * v) ^ 2 + Real.cos θ ^ 2 := by
  have hcos : Complex.cos (θ + Complex.I * Real.pi * v) =
      ((Real.cos θ * Real.cosh (Real.pi * v) : ℝ) : ℂ) -
        ((Real.sin θ * Real.sinh (Real.pi * v) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.cos_add]
    have h1 : Complex.cos (Complex.I * Real.pi * v) = Real.cosh (Real.pi * v) := by
      rw [show Complex.I * ↑π * ↑v = ↑(π * v) * Complex.I by push_cast; ring, Complex.cos_mul_I]
      simp [Complex.ofReal_cosh]
    have h2 : Complex.sin (Complex.I * Real.pi * v) = Complex.I * Real.sinh (Real.pi * v) := by
      rw [show Complex.I * ↑π * ↑v = ↑(π * v) * Complex.I by push_cast; ring, Complex.sin_mul_I]
      simp [Complex.ofReal_sinh]; ring
    rw [h1, h2]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast; ring
  rw [← Complex.normSq_eq_norm_sq, hcos, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.sub_im, Complex.mul_im,
    zero_sub, neg_mul]
  have hch := Real.cosh_sq (Real.pi * v)
  have hcs := Real.cos_sq_add_sin_sq θ
  nlinarith

lemma cos_ne_zero_of_abs_lt {θ v : ℝ} (hθ : |θ| < Real.pi / 2) :
    Complex.cos (θ + Complex.I * Real.pi * v) ≠ 0 := by
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  intro h
  have hsq := cos_normSq_eq θ v
  rw [h, norm_zero, zero_pow two_ne_zero] at hsq
  nlinarith [sq_nonneg (Real.sinh (Real.pi * v)), sq_pos_of_pos hcos_pos]

lemma cTheta_norm_le {θ v : ℝ} (hθ : |θ| < Real.pi / 2) (hv : 0 ≤ v) :
    ‖cTheta θ v‖ ≤ (4 / Real.cos θ ^ 2) * Real.exp (-2 * Real.pi * v) := by
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  have hnorm_cos : (Real.cos θ ^ 2 / 4) * Real.exp (2 * Real.pi * v) ≤
      ‖Complex.cos (θ + Complex.I * Real.pi * v)‖ ^ 2 := by
    have hch : Real.exp (Real.pi * v) / 2 ≤ Real.cosh (Real.pi * v) := by
      rw [Real.cosh_eq]
      have : Real.exp (-(Real.pi * v)) ≥ 0 := (Real.exp_pos _).le
      linarith
    have hch_sq : Real.exp (2 * Real.pi * v) / 4 ≤ Real.cosh (Real.pi * v) ^ 2 := by
      have h1 : (Real.exp (Real.pi * v) / 2) ^ 2 = Real.exp (2 * Real.pi * v) / 4 := by
        rw [div_pow, ← Real.exp_nat_mul]; ring_nf
      rw [← h1]
      exact sq_le_sq' (by linarith [Real.exp_pos (Real.pi * v)]) hch
    have hsh : Real.sinh (Real.pi * v) ^ 2 + Real.cos θ ^ 2 =
        Real.cos θ ^ 2 * Real.cosh (Real.pi * v) ^ 2 + Real.sin θ ^ 2 * Real.sinh (Real.pi * v) ^ 2 := by
      have h1 := Real.cosh_sq (Real.pi * v)
      have h2 := Real.cos_sq_add_sin_sq θ
      nlinarith
    rw [cos_normSq_eq, hsh]
    nlinarith [sq_nonneg (Real.sin θ), sq_nonneg (Real.sinh (Real.pi * v)), sq_pos_of_pos hcos_pos]
  dsimp only [cTheta]
  rw [norm_div, norm_pow]
  have hnum : ‖Complex.exp (-Complex.I * θ)‖ = 1 := by
    rw [show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  rw [hnum, one_div]
  calc (‖Complex.cos (↑θ + Complex.I * ↑π * ↑v)‖ ^ 2)⁻¹
      ≤ ((Real.cos θ ^ 2 / 4) * Real.exp (2 * Real.pi * v))⁻¹ :=
        inv_anti₀ (by positivity) hnorm_cos
    _ = (4 / Real.cos θ ^ 2) * Real.exp (-2 * Real.pi * v) := by
        rw [show -2 * Real.pi * v = -(2 * Real.pi * v) by ring, Real.exp_neg]
        field_simp [hcos_pos.ne', (Real.exp_pos (2 * Real.pi * v)).ne']

lemma uTheta_deriv {θ v : ℝ} (hθ : |θ| < Real.pi / 2) :
    HasDerivAt (fun t : ℝ => -uTheta θ t) (cTheta θ v) v := by
  have hcos_ne := cos_ne_zero_of_abs_lt (v := v) hθ
  have hw : HasDerivAt (fun t : ℝ => (θ : ℂ) + Complex.I * Real.pi * t) (Complex.I * Real.pi) v := by
    have h := (hasDerivAt_id v).ofReal_comp.const_mul (Complex.I * Real.pi)
    simpa using h.const_add (θ : ℂ)
  have hcos_d := (Complex.hasDerivAt_cos _).comp v hw
  have hexp_d : HasDerivAt (fun t : ℝ => (Real.exp (-Real.pi * t) : ℂ))
      ((-Real.pi : ℂ) * Real.exp (-Real.pi * v)) v := by
    have hr := ((hasDerivAt_id v).const_mul (-Real.pi)).exp
    convert hr.ofReal_comp using 1
    · ext t; simp
    · push_cast; ring
  have hden_d := hcos_d.const_mul (Real.pi : ℂ)
  have hden_ne : (Real.pi : ℂ) * Complex.cos (θ + Complex.I * Real.pi * v) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) hcos_ne
  have hq := (hexp_d.div hden_d hden_ne).neg
  refine hq.congr_deriv ?_
  have hcexp : Complex.exp (-Complex.I * (θ : ℂ)) =
      (Real.exp (-Real.pi * v) : ℂ) * (Complex.cos (θ + Complex.I * Real.pi * v) -
        Complex.I * Complex.sin (θ + Complex.I * Real.pi * v)) := by
    have h1 : Complex.cos (θ + Complex.I * Real.pi * v) - Complex.I * Complex.sin (θ + Complex.I * Real.pi * v) =
        Complex.exp (-Complex.I * (θ + Complex.I * Real.pi * v)) := by
      unfold Complex.cos Complex.sin
      have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
      have hneg : -Complex.I * ((θ : ℂ) + Complex.I * Real.pi * v) =
          -(Complex.I * ((θ : ℂ) + Complex.I * Real.pi * v)) := by ring
      rw [hneg]
      ring_nf
      rw [hI2]
      ring
    rw [h1, show -Complex.I * ((θ : ℂ) + Complex.I * Real.pi * v) =
        -Complex.I * θ + ((Real.pi * v : ℝ) : ℂ) by push_cast; ring_nf; simp [Complex.I_sq],
      Complex.exp_add, Complex.ofReal_exp, ← mul_assoc, ← Complex.ofReal_exp, ← Real.exp_add]
    simp
  dsimp only [cTheta]
  rw [hcexp]
  field_simp [Real.pi_ne_zero, hcos_ne]
  simp only [Complex.I_sq]
  ring

lemma cTheta_integrableOn {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    IntegrableOn (fun v : ℝ => cTheta θ v) (Set.Ioi 0) := by
  have h_exp : IntegrableOn (fun v : ℝ => Real.exp (-2 * Real.pi * v)) (Set.Ioi 0) := by
    have h_c : IntegrableOn (fun v : ℝ => Complex.exp ((-2 * Real.pi : ℂ) * v)) (Set.Ioi 0) :=
      integrableOn_exp_mul_complex_Ioi (by simp; positivity) 0
    refine IntegrableOn.congr_fun h_c.norm (fun v _ => ?_) measurableSet_Ioi
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.norm_exp]
    congr 1; simp [Complex.mul_re]; ring
  have hmeas : AEStronglyMeasurable (fun v : ℝ => cTheta θ v) (volume.restrict (Set.Ioi 0)) := by
    refine Continuous.aestronglyMeasurable ?_
    refine continuous_const.div (Continuous.pow ((Complex.continuous_cos.comp (by fun_prop))) 2) (fun v => ?_)
    exact pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ)
  refine (h_exp.const_mul (4 / Real.cos θ ^ 2)).mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact cTheta_norm_le hθ hv.le

lemma cTheta_integral_eq {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    (∫ v in Set.Ioi (0 : ℝ), cTheta θ v) = 1 / (Real.pi * Real.cos θ) := by
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  have htend : Tendsto (fun v : ℝ => -uTheta θ v) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h_bnd : ∀ᶠ v : ℝ in atTop, ‖-uTheta θ v‖ ≤ (2 / (Real.pi * Real.cos θ)) * Real.exp (-2 * Real.pi * v) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
      rw [norm_neg]
      dsimp only [uTheta]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      have hcos_lb : (Real.cos θ / 2) * Real.exp (Real.pi * v) ≤
          ‖Complex.cos (θ + Complex.I * Real.pi * v)‖ := by
        have hsq : (Real.cos θ / 2 * Real.exp (Real.pi * v)) ^ 2 ≤
            ‖Complex.cos (θ + Complex.I * Real.pi * v)‖ ^ 2 := by
          have hch : Real.exp (Real.pi * v) / 2 ≤ Real.cosh (Real.pi * v) := by
            rw [Real.cosh_eq]; linarith [Real.exp_pos (-(Real.pi * v))]
          have h1 : Real.cos θ ^ 2 * Real.cosh (Real.pi * v) ^ 2 ≤ Real.sinh (Real.pi * v) ^ 2 + Real.cos θ ^ 2 := by
            have := Real.cosh_sq (Real.pi * v)
            have := Real.cos_sq_add_sin_sq θ
            nlinarith [sq_nonneg (Real.sin θ), sq_nonneg (Real.sinh (Real.pi * v))]
          rw [cos_normSq_eq]
          nlinarith [sq_le_sq' (by linarith [Real.exp_pos (Real.pi * v)]) hch]
        exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hsq
      calc Real.exp (-Real.pi * v) / (Real.pi * ‖Complex.cos (↑θ + Complex.I * ↑π * ↑v)‖)
          ≤ Real.exp (-Real.pi * v) / (Real.pi * ((Real.cos θ / 2) * Real.exp (Real.pi * v))) := by
            exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) (mul_le_mul_of_nonneg_left hcos_lb Real.pi_pos.le)
        _ = (2 / (Real.pi * Real.cos θ)) * Real.exp (-2 * Real.pi * v) := by
            rw [show -2 * Real.pi * v = -Real.pi * v - Real.pi * v by ring, Real.exp_sub]
            field_simp [Real.pi_ne_zero, hcos_pos.ne']
    have h_lim : Tendsto (fun v : ℝ => (2 / (Real.pi * Real.cos θ)) * Real.exp (-2 * Real.pi * v)) atTop (nhds 0) := by
      have h1 : Tendsto (fun v : ℝ => Real.exp (-(2 * Real.pi) * v)) atTop (nhds 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by positivity : -(2 * Real.pi) < 0))
      simpa using h1.const_mul (2 / (Real.pi * Real.cos θ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim
      (Eventually.of_forall fun _ => norm_nonneg _) h_bnd
  have hres := integral_Ioi_of_hasDerivAt_of_tendsto' (fun v _ => uTheta_deriv hθ) (cTheta_integrableOn hθ) htend
  rw [hres, zero_sub, neg_neg]
  simp [uTheta]

lemma cTheta_im_integral_zero {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    (∫ v in Set.Ioi (0 : ℝ), (cTheta θ v).im) = 0 := by
  have him : (∫ v in Set.Ioi (0 : ℝ), (cTheta θ v).im) = (∫ v in Set.Ioi (0 : ℝ), cTheta θ v).im :=
    (Complex.imCLM.integral_comp_comm (cTheta_integrableOn hθ)).symm
  rw [him, cTheta_integral_eq hθ]
  simp [show (1 / (Real.pi * Real.cos θ) : ℂ) = ((1 / (Real.pi * Real.cos θ) : ℝ) : ℂ) by push_cast; ring]

lemma limitingJ_neg_neg (y θ : ℝ) : limitingJ (-y) (-θ) = limitingJ y θ := by
  unfold limitingJ
  congr 1; ext v
  have hconj : Complex.exp (-Complex.I * (-θ : ℝ)) /
      (Complex.cos ((-θ : ℝ) + Complex.I * Real.pi * v) ^ 2 * ((-y : ℝ) - Complex.I * v)) =
      -starRingEnd ℂ (Complex.exp (-Complex.I * θ) /
        (Complex.cos (θ + Complex.I * Real.pi * v) ^ 2 * (y - Complex.I * v))) := by
    have h1 : starRingEnd ℂ (Complex.exp (-Complex.I * θ)) = Complex.exp (-Complex.I * (-θ : ℝ)) := by
      rw [← Complex.exp_conj]
      congr 1; simp [map_mul, Complex.conj_I]
    have h2' : starRingEnd ℂ (Complex.cos (θ + Complex.I * Real.pi * v)) =
        Complex.cos ((-θ : ℝ) + Complex.I * Real.pi * v) := by
      rw [← Complex.cos_conj, ← Complex.cos_neg]
      congr 1
      simp [map_add, map_mul, Complex.conj_I]
      ring
    have h3 : starRingEnd ℂ ((y : ℂ) - Complex.I * v) = -((-y : ℝ) - Complex.I * v) := by
      simp [map_sub, map_mul, Complex.conj_I]
      ring
    rw [map_div₀, map_mul, map_pow, h1, h2', h3, mul_neg, div_neg]
    congr 1; congr 1
    · push_cast; ring
    · rw [show ((-y : ℝ) : ℂ) = -(y : ℂ) by push_cast; ring]; ring_nf
  rw [hconj, Complex.neg_im, Complex.conj_im, neg_neg]

/-- **Lemma 3.3 (Part 2)**: Near-zero asymptotic `J(y, θ) = (1/cos θ) log(1/|y|) + O_θ(1)`. -/
theorem limitingJ_near_zero (θ : ℝ) (hθ : |θ| < Real.pi / 2) :
    ∃ C_0 > 0, ∀ y : ℝ, 0 < |y| → |y| ≤ 1 →
      |limitingJ y θ - (1 / Real.cos θ) * Real.log (1 / |y|)| ≤ C_0 := by
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  -- Bound |A_θ(v) - A_θ(0)| ≤ C_A * v on [0, 1] using derivative of cTheta
  have hc_int := cTheta_integrableOn hθ
  have hB_bound : ∃ C_B > 0, ∀ v : ℝ, 0 ≤ v → |(cTheta θ v).im| ≤ C_B := by
    refine ⟨4 / Real.cos θ ^ 2, by positivity, fun v hv => ?_⟩
    exact (Complex.abs_im_le_norm _).trans ((cTheta_norm_le hθ hv).trans
      (mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos]))))
  obtain ⟨C_B, hC_B, hB_bd⟩ := hB_bound
  have hA_bound : ∃ C_A > 0, ∀ v : ℝ, 0 ≤ v → v ≤ 1 → |(cTheta θ v).re - 1 / Real.cos θ| ≤ C_A * v := by
    have hderiv_bd : ∃ C_A > 0, ∀ v ∈ Set.Icc (0 : ℝ) 1,
        ‖deriv (fun t : ℝ => (cTheta θ t).re) v‖ ≤ C_A := by
      let f : ℝ → ℝ := fun t => ‖deriv (fun s : ℝ => (cTheta θ s).re) t‖
      have hc_diff : Differentiable ℝ (fun t : ℝ => cTheta θ t) := by
        intro t
        have hw : HasDerivAt (fun s : ℝ => (θ : ℂ) + Complex.I * Real.pi * s) (Complex.I * Real.pi) t := by
          simpa using ((hasDerivAt_id t).ofReal_comp.const_mul (Complex.I * Real.pi)).const_add (θ : ℂ)
        exact (differentiableAt_const _).div ((((Complex.hasDerivAt_cos _).comp t hw).differentiableAt).pow 2) (pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ))
      have hc_re_diff : Differentiable ℝ (fun t : ℝ => (cTheta θ t).re) :=
        fun t => Complex.reCLM.differentiableAt.comp t (hc_diff t)
      have hf_cont : Continuous f := by
        dsimp only [f]
        have hderiv_eq : ∀ t : ℝ, deriv (fun s : ℝ => (cTheta θ s).re) t = (deriv (fun s : ℝ => cTheta θ s) t).re := fun t =>
          (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hc_diff t).hasDerivAt).deriv
        have hc_c1 : ContDiff ℝ 1 (fun t : ℝ => cTheta θ t) := by
          have hw_c : ContDiff ℝ 1 (fun t : ℝ => (θ : ℂ) + Complex.I * Real.pi * t) :=
            (contDiff_const (𝕜 := ℝ)).add ((contDiff_const (𝕜 := ℝ)).mul Complex.ofRealCLM.contDiff)
          exact (contDiff_const (𝕜 := ℝ)).div (((Complex.contDiff_cos.restrict_scalars ℝ).comp hw_c).pow 2) (fun t => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ))
        exact (hc_c1.continuous_deriv (by norm_num) |> fun h => (Complex.continuous_re.comp h).norm).congr fun t => by
          dsimp only [Function.comp_def]; rw [hderiv_eq t]
      obtain ⟨v₀, _, hv₀⟩ := isCompact_Icc.exists_isMaxOn (⟨0, by norm_num, by norm_num⟩ : (Set.Icc (0 : ℝ) 1).Nonempty) hf_cont.continuousOn
      refine ⟨max 1 (f v₀), by positivity, fun v hv => (hv₀ hv).trans (le_max_right _ _)⟩
    obtain ⟨C_A, hC_A, hbd⟩ := hderiv_bd
    refine ⟨C_A, hC_A, fun v hv0 hv1 => ?_⟩
    have h0 : (cTheta θ 0).re = 1 / Real.cos θ := by
      simp only [cTheta, Complex.ofReal_zero, mul_zero, add_zero]
      rw [show Complex.cos (θ : ℂ) = (Real.cos θ : ℂ) from (Complex.ofReal_cos θ).symm,
        show Complex.exp (-Complex.I * (θ : ℂ)) = (Real.cos θ : ℂ) - Complex.I * (Real.sin θ : ℂ) by
          rw [show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
          simp [Complex.cos_neg, Complex.sin_neg]; ring]
      have hsq : (Real.cos θ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast (sq_pos_of_pos hcos_pos).ne'
      rw [sub_div, Complex.sub_re]
      have hre1 : ((Real.cos θ : ℂ) / (Real.cos θ : ℂ) ^ 2).re = 1 / Real.cos θ := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]
        field_simp [hcos_pos.ne']
      have him1 : (Complex.I * (Real.sin θ : ℂ) / (Real.cos θ : ℂ) ^ 2).re = 0 := by
        rw [mul_div_assoc, ← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.I_mul_re, Complex.ofReal_im, neg_zero]
      rw [hre1, him1, sub_zero]
    rw [← h0]
    have hdiff_on : ∀ t ∈ Set.Icc (0 : ℝ) v,
        HasDerivWithinAt (fun s : ℝ => (cTheta θ s).re) (deriv (fun s : ℝ => (cTheta θ s).re) t) (Set.Icc 0 v) t := by
      intro t _
      have hc_diff : DifferentiableAt ℝ (fun s : ℝ => cTheta θ s) t := by
        have hw : HasDerivAt (fun s : ℝ => (θ : ℂ) + Complex.I * Real.pi * s) (Complex.I * Real.pi) t := by
          simpa using ((hasDerivAt_id t).ofReal_comp.const_mul (Complex.I * Real.pi)).const_add (θ : ℂ)
        exact (differentiableAt_const _).div ((((Complex.hasDerivAt_cos _).comp t hw).differentiableAt).pow 2) (pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ))
      exact (Complex.reCLM.differentiableAt.comp t hc_diff).hasDerivAt.hasDerivWithinAt
    have hdiff_at : ∀ t ∈ Set.Icc (0 : ℝ) v, DifferentiableAt ℝ (fun s : ℝ => (cTheta θ s).re) t := by
      intro t _
      have hw : HasDerivAt (fun s : ℝ => (θ : ℂ) + Complex.I * Real.pi * s) (Complex.I * Real.pi) t := by
        simpa using ((hasDerivAt_id t).ofReal_comp.const_mul (Complex.I * Real.pi)).const_add (θ : ℂ)
      have hc_diff : DifferentiableAt ℝ (fun s : ℝ => cTheta θ s) t :=
        (differentiableAt_const _).div ((((Complex.hasDerivAt_cos _).comp t hw).differentiableAt).pow 2) (pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ))
      exact Complex.reCLM.differentiableAt.comp t hc_diff
    have hmvt := (convex_Icc 0 v).norm_image_sub_le_of_norm_deriv_le
      hdiff_at (fun t ht => hbd t ⟨ht.1, ht.2.trans hv1⟩)
      (Set.left_mem_Icc.mpr hv0) (Set.right_mem_Icc.mpr hv0)
    simpa [Real.norm_eq_abs, sub_zero, abs_of_nonneg hv0] using hmvt
  obtain ⟨C_A, hC_A, hA_bd⟩ := hA_bound
  set I_tail := ∫ v in Set.Ioi (1 : ℝ), ‖cTheta θ v‖
  refine ⟨C_A + I_tail + C_B * (Real.pi / 2) + Real.log 2 / (2 * Real.cos θ) + 1, by positivity,
    fun y hy0 hy1 => ?_⟩
  have hy_ne : y ≠ 0 := abs_pos.mp hy0
  have h_integrand : ∀ v : ℝ, 0 ≤ v →
      (Complex.exp (-Complex.I * θ) /
        (Complex.cos (θ + Complex.I * Real.pi * v) ^ 2 * (y - Complex.I * v))).im =
      (v * (cTheta θ v).re + y * (cTheta θ v).im) / (y ^ 2 + v ^ 2) := by
    intro v hv
    rw [div_mul_eq_div_div]
    change (cTheta θ v / ((y : ℂ) - Complex.I * v)).im = _
    have hinv : (1 / ((y : ℂ) - Complex.I * v)) = ((y : ℂ) + Complex.I * v) / ((y ^ 2 + v ^ 2 : ℝ) : ℂ) := by
      have h1 : (y : ℂ) - Complex.I * v ≠ 0 := by
        intro h; have := congr_arg Complex.re h; simp at this; exact hy_ne this
      have h2 : ((y ^ 2 + v ^ 2 : ℝ) : ℂ) ≠ 0 := by norm_cast; positivity
      field_simp [h1, h2]; ring_nf; simp [Complex.I_sq]
    rw [div_eq_mul_inv, ← one_div, hinv, ← mul_div_assoc, Complex.div_ofReal_im]
    have hre_im : (cTheta θ v * ((y : ℂ) + Complex.I * v)).im =
        v * (cTheta θ v).re + y * (cTheta θ v).im := by
      simp [Complex.mul_im]; ring
    rw [hre_im]
  have hJ_eq : limitingJ y θ =
      (∫ v in Set.Ioi (0 : ℝ), v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) +
      (∫ v in Set.Ioi (0 : ℝ), y * (cTheta θ v).im / (y ^ 2 + v ^ 2)) := by
    unfold limitingJ
    have h1 : IntegrableOn (fun v : ℝ => v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) (Set.Ioi 0) := by
      have h_v : IntegrableOn (fun v : ℝ => ‖cTheta θ v‖ * (1 / |y|)) (Set.Ioi 0) :=
        hc_int.norm.mul_const _
      refine h_v.mono' (Continuous.aestronglyMeasurable (by
        refine (continuous_id.mul (Complex.continuous_re.comp ?_)).div (by fun_prop) (fun v => by positivity)
        refine continuous_const.div (Continuous.pow ((Complex.continuous_cos.comp (by fun_prop))) 2) (fun v => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ)))) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < y ^ 2 + v ^ 2), abs_mul, abs_of_pos hv]
      have h2 : v / (y ^ 2 + v ^ 2) ≤ 1 / |y| := by
        rw [div_le_div_iff₀ (by positivity) hy0]
        nlinarith [sq_nonneg (v - |y|), sq_abs y]
      calc v * |(cTheta θ v).re| / (y ^ 2 + v ^ 2)
          = |(cTheta θ v).re| * (v / (y ^ 2 + v ^ 2)) := by ring
        _ ≤ ‖cTheta θ v‖ * (1 / |y|) := mul_le_mul (Complex.abs_re_le_norm _) h2 (div_nonneg hv.le (by positivity)) (norm_nonneg _)
    have h2 : IntegrableOn (fun v : ℝ => y * (cTheta θ v).im / (y ^ 2 + v ^ 2)) (Set.Ioi 0) := by
      have h_y : IntegrableOn (fun v : ℝ => ‖cTheta θ v‖ * (1 / |y|)) (Set.Ioi 0) :=
        hc_int.norm.mul_const _
      refine h_y.mono' (Continuous.aestronglyMeasurable (by
        refine (continuous_const.mul (Complex.continuous_im.comp ?_)).div (by fun_prop) (fun v => by positivity)
        refine continuous_const.div (Continuous.pow ((Complex.continuous_cos.comp (by fun_prop))) 2) (fun v => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ)))) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < y ^ 2 + v ^ 2), abs_mul]
      have h3 : |y| / (y ^ 2 + v ^ 2) ≤ 1 / |y| := by
        rw [div_le_div_iff₀ (by positivity) hy0]
        nlinarith [sq_nonneg v, sq_abs y]
      calc |y| * |(cTheta θ v).im| / (y ^ 2 + v ^ 2)
          = |(cTheta θ v).im| * (|y| / (y ^ 2 + v ^ 2)) := by ring
        _ ≤ ‖cTheta θ v‖ * (1 / |y|) := mul_le_mul (Complex.abs_im_le_norm _) h3 (div_nonneg (abs_nonneg y) (by positivity)) (norm_nonneg _)
    rw [← integral_add h1 h2]
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    rw [h_integrand v hv.le]
    ring
  -- Bound the B part
  have hB_int_le : |∫ v in Set.Ioi (0 : ℝ), y * (cTheta θ v).im / (y ^ 2 + v ^ 2)| ≤ C_B * (Real.pi / 2) := by
    have h_abs : |∫ v in Set.Ioi (0 : ℝ), y * (cTheta θ v).im / (y ^ 2 + v ^ 2)| ≤
        ∫ v in Set.Ioi (0 : ℝ), C_B * (|y| / (y ^ 2 + v ^ 2)) := by
      have h_int_abs : IntegrableOn (fun v : ℝ => C_B * (|y| / (y ^ 2 + v ^ 2))) (Set.Ioi 0) := by
        have hr : (1 / |y| : ℝ) ≠ 0 := by positivity
        have h1 := ((integrable_inv_one_add_mul_sq hr).integrableOn : IntegrableOn _ (Set.Ioi (0 : ℝ)) volume).const_mul (C_B / |y|)
        refine IntegrableOn.congr_fun h1 (fun v _ => ?_) measurableSet_Ioi
        field_simp [hy0.ne']; rw [sq_abs]
      calc |∫ v in Set.Ioi (0 : ℝ), y * (cTheta θ v).im / (y ^ 2 + v ^ 2)|
          ≤ ∫ v in Set.Ioi (0 : ℝ), ‖y * (cTheta θ v).im / (y ^ 2 + v ^ 2)‖ := by rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
        _ ≤ ∫ v in Set.Ioi (0 : ℝ), C_B * (|y| / (y ^ 2 + v ^ 2)) := by
            refine setIntegral_mono_on (by
              -- integrableOn norm
              have hmeas_im : AEStronglyMeasurable (fun v : ℝ => ‖y * (cTheta θ v).im / (y ^ 2 + v ^ 2)‖) (volume.restrict (Set.Ioi 0)) := by
                refine Continuous.aestronglyMeasurable (Continuous.norm ?_)
                refine (continuous_const.mul (Complex.continuous_im.comp ?_)).div (by fun_prop) (fun v => by positivity)
                exact continuous_const.div (Continuous.pow (Complex.continuous_cos.comp (by fun_prop)) 2) (fun v => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ))
              exact (h_int_abs).mono' hmeas_im (by
                filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
                simp only [Real.norm_eq_abs, abs_abs, abs_div, abs_of_pos (by positivity : 0 < y ^ 2 + v ^ 2), abs_mul]
                calc |y| * |(cTheta θ v).im| / (y ^ 2 + v ^ 2)
                    ≤ |y| * C_B / (y ^ 2 + v ^ 2) := by gcongr; exact hB_bd v hv.le
                  _ = C_B * (|y| / (y ^ 2 + v ^ 2)) := by ring)) h_int_abs measurableSet_Ioi fun v hv => ?_
            rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < y ^ 2 + v ^ 2), abs_mul]
            calc |y| * |(cTheta θ v).im| / (y ^ 2 + v ^ 2)
                ≤ |y| * C_B / (y ^ 2 + v ^ 2) := by gcongr; exact hB_bd v hv.le
              _ = C_B * (|y| / (y ^ 2 + v ^ 2)) := by ring
    have h_arctan_int : (∫ v in Set.Ioi (0 : ℝ), |y| / (y ^ 2 + v ^ 2)) = Real.pi / 2 := by
      have h_int_l : IntegrableOn (fun v : ℝ => |y| / (y ^ 2 + v ^ 2)) (Set.Ioi 0) := by
        have hr : (1 / |y| : ℝ) ≠ 0 := by positivity
        refine IntegrableOn.congr_fun (((integrable_inv_one_add_mul_sq hr).const_mul (1 / |y|)).integrableOn : IntegrableOn _ (Set.Ioi (0 : ℝ)) volume) (fun v _ => ?_) measurableSet_Ioi
        field_simp [hy0.ne']; rw [sq_abs]
      have hderiv : ∀ v ∈ Set.Ici (0 : ℝ), HasDerivAt (fun t : ℝ => Real.arctan (t / |y|)) (|y| / (y ^ 2 + v ^ 2)) v := by
        intro v _
        have hd := ((hasDerivAt_id v).div_const |y|).arctan
        refine hd.congr_deriv ?_
        dsimp only [id_eq]
        field_simp [hy0.ne']; rw [sq_abs]
      have htend : Tendsto (fun t : ℝ => Real.arctan (t / |y|)) atTop (nhds (Real.pi / 2)) :=
        (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp (tendsto_id.atTop_div_const hy0)
      rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv h_int_l htend]
      simp [Real.arctan_zero]
    rw [integral_const_mul, h_arctan_int] at h_abs
    exact h_abs
  -- Split A part on (0, 1] and (1, ∞)
  have hA_split : (∫ v in Set.Ioi (0 : ℝ), v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) =
      (∫ v in Set.Ioc (0 : ℝ) 1, v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) +
      (∫ v in Set.Ioi (1 : ℝ), v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) := by
    have hun : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi (by norm_num)
    have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) := Set.Ioc_disjoint_Ioi_same
    have h_int_A : IntegrableOn (fun v : ℝ => v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) (Set.Ioi 0) := by
      have h_v : IntegrableOn (fun v : ℝ => ‖cTheta θ v‖ * (1 / |y|)) (Set.Ioi 0) := hc_int.norm.mul_const _
      refine h_v.mono' (Continuous.aestronglyMeasurable (by
        refine (continuous_id.mul (Complex.continuous_re.comp ?_)).div (by fun_prop) (fun v => by positivity)
        refine continuous_const.div (Continuous.pow ((Complex.continuous_cos.comp (by fun_prop))) 2) (fun v => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ)))) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < y ^ 2 + v ^ 2), abs_mul, abs_of_pos hv]
      have h2 : v / (y ^ 2 + v ^ 2) ≤ 1 / |y| := by
        rw [div_le_div_iff₀ (by positivity) hy0]; nlinarith [sq_nonneg (v - |y|), sq_abs y]
      calc v * |(cTheta θ v).re| / (y ^ 2 + v ^ 2) = |(cTheta θ v).re| * (v / (y ^ 2 + v ^ 2)) := by ring
        _ ≤ ‖cTheta θ v‖ * (1 / |y|) := mul_le_mul (Complex.abs_re_le_norm _) h2 (div_nonneg hv.le (by positivity)) (norm_nonneg _)
    rw [← hun] at h_int_A
    rw [← hun, setIntegral_union hdisj measurableSet_Ioi (h_int_A.mono_set Set.subset_union_left)
      (h_int_A.mono_set Set.subset_union_right)]
  have hA_tail : |∫ v in Set.Ioi (1 : ℝ), v * (cTheta θ v).re / (y ^ 2 + v ^ 2)| ≤ I_tail := by
    calc |∫ v in Set.Ioi (1 : ℝ), v * (cTheta θ v).re / (y ^ 2 + v ^ 2)|
        ≤ ∫ v in Set.Ioi (1 : ℝ), ‖v * (cTheta θ v).re / (y ^ 2 + v ^ 2)‖ := by rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
      _ ≤ ∫ v in Set.Ioi (1 : ℝ), ‖cTheta θ v‖ := by
          refine setIntegral_mono_on (by
            exact (hc_int.mono_set (Set.Ioi_subset_Ioi (by norm_num))).norm.mono' (Continuous.aestronglyMeasurable (Continuous.norm (by
              refine (continuous_id.mul (Complex.continuous_re.comp ?_)).div (by fun_prop) (fun v => by positivity)
              exact continuous_const.div (Continuous.pow (Complex.continuous_cos.comp (by fun_prop)) 2) (fun v => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ))))) (by
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
              have hv1 : 1 < v := hv
              simp only [Real.norm_eq_abs, abs_abs, abs_div, abs_of_pos (by positivity : 0 < y ^ 2 + v ^ 2),
                abs_mul, abs_of_pos (by linarith : 0 < v)]
              have hle : v / (y ^ 2 + v ^ 2) ≤ 1 := by
                rw [div_le_one (by positivity)]; nlinarith [sq_nonneg y]
              calc v * |(cTheta θ v).re| / (y ^ 2 + v ^ 2) = |(cTheta θ v).re| * (v / (y ^ 2 + v ^ 2)) := by ring
                _ ≤ ‖cTheta θ v‖ * 1 := mul_le_mul (Complex.abs_re_le_norm _) hle (by positivity) (norm_nonneg _)
                _ = ‖cTheta θ v‖ := mul_one _))
            (hc_int.mono_set (Set.Ioi_subset_Ioi (by norm_num))).norm measurableSet_Ioi fun v hv => ?_
          have hv1 : 1 < v := hv
          rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < y ^ 2 + v ^ 2),
            abs_mul, abs_of_pos (by linarith)]
          have hle : v / (y ^ 2 + v ^ 2) ≤ 1 := by
            rw [div_le_one (by positivity)]; nlinarith [sq_nonneg y]
          calc v * |(cTheta θ v).re| / (y ^ 2 + v ^ 2) = |(cTheta θ v).re| * (v / (y ^ 2 + v ^ 2)) := by ring
            _ ≤ ‖cTheta θ v‖ * 1 := mul_le_mul (Complex.abs_re_le_norm _) hle (by positivity) (norm_nonneg _)
            _ = ‖cTheta θ v‖ := mul_one _
  have hA_main : (∫ v in Set.Ioc (0 : ℝ) 1, v * (1 / Real.cos θ) / (y ^ 2 + v ^ 2)) =
      (1 / Real.cos θ) * Real.log (1 / |y|) + (1 / (2 * Real.cos θ)) * Real.log (y ^ 2 + 1) := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hderiv : ∀ v ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => (1 / (2 * Real.cos θ)) * Real.log (y ^ 2 + t ^ 2))
          (v * (1 / Real.cos θ) / (y ^ 2 + v ^ 2)) v := by
      intro v _
      have hpos : y ^ 2 + v ^ 2 ≠ 0 := by positivity
      have hd := ((hasDerivAt_pow 2 v).const_add (y ^ 2)).log hpos
      convert hd.const_mul (1 / (2 * Real.cos θ)) using 1
      field_simp [hpos, hcos_pos.ne']; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (Continuous.continuousOn (by
      refine (continuous_id.mul continuous_const).div (by fun_prop) (fun v => by positivity))).intervalIntegrable]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, one_pow]
    have hy2 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
    rw [hy2, Real.log_pow, Nat.cast_ofNat, Real.log_div one_ne_zero hy0.ne', Real.log_one, zero_sub]
    rw [← hy2]; ring
  have hA_diff : |(∫ v in Set.Ioc (0 : ℝ) 1, v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) -
      (∫ v in Set.Ioc (0 : ℝ) 1, v * (1 / Real.cos θ) / (y ^ 2 + v ^ 2))| ≤ C_A := by
    have h1 : IntegrableOn (fun v : ℝ => v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) (Set.Ioc 0 1) :=
      (Continuous.continuousOn (by
        refine (continuous_id.mul (Complex.continuous_re.comp ?_)).div (by fun_prop) (fun v => by positivity)
        refine continuous_const.div (Continuous.pow ((Complex.continuous_cos.comp (by fun_prop))) 2) (fun v => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ)))).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    have h2 : IntegrableOn (fun v : ℝ => v * (1 / Real.cos θ) / (y ^ 2 + v ^ 2)) (Set.Ioc 0 1) :=
      (Continuous.continuousOn ((continuous_id.mul continuous_const).div (by fun_prop) (fun v => by positivity))).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    rw [← integral_sub h1 h2]
    calc |∫ v in Set.Ioc (0 : ℝ) 1, (v * (cTheta θ v).re / (y ^ 2 + v ^ 2) - v * (1 / Real.cos θ) / (y ^ 2 + v ^ 2))|
        ≤ ∫ v in Set.Ioc (0 : ℝ) 1, ‖v * (cTheta θ v).re / (y ^ 2 + v ^ 2) - v * (1 / Real.cos θ) / (y ^ 2 + v ^ 2)‖ :=
          by rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
      _ ≤ ∫ v in Set.Ioc (0 : ℝ) 1, C_A := by
          refine setIntegral_mono_on (h1.sub h2).norm (continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self) measurableSet_Ioc fun v hv => ?_
          rw [Real.norm_eq_abs, show v * (cTheta θ v).re / (y ^ 2 + v ^ 2) - v * (1 / Real.cos θ) / (y ^ 2 + v ^ 2) =
            (v / (y ^ 2 + v ^ 2)) * ((cTheta θ v).re - 1 / Real.cos θ) by ring,
            abs_mul, abs_div, abs_of_pos hv.1, abs_of_pos (by positivity : 0 < y ^ 2 + v ^ 2)]
          have hle1 : v ^ 2 / (y ^ 2 + v ^ 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith [sq_nonneg y]
          calc (v / (y ^ 2 + v ^ 2)) * |(cTheta θ v).re - 1 / Real.cos θ|
              ≤ (v / (y ^ 2 + v ^ 2)) * (C_A * v) := mul_le_mul_of_nonneg_left (hA_bd v hv.1.le hv.2) (div_nonneg hv.1.le (by positivity))
            _ = C_A * (v ^ 2 / (y ^ 2 + v ^ 2)) := by ring
            _ ≤ C_A * 1 := by gcongr
            _ = C_A := mul_one _
      _ = C_A := by simp [setIntegral_const, Real.volume_real_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hlog2 : |1 / (2 * Real.cos θ) * Real.log (y ^ 2 + 1)| ≤ Real.log 2 / (2 * Real.cos θ) := by
    have hlog_nonneg : 0 ≤ Real.log (y ^ 2 + 1) := Real.log_nonneg (by linarith [sq_nonneg y])
    have hlog_le : Real.log (y ^ 2 + 1) ≤ Real.log 2 := by
      apply Real.log_le_log (by positivity)
      have : y ^ 2 ≤ 1 := by nlinarith [sq_abs y]
      linarith
    rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.cos θ)), abs_of_nonneg hlog_nonneg]
    calc (1 / (2 * Real.cos θ)) * Real.log (y ^ 2 + 1)
        ≤ (1 / (2 * Real.cos θ)) * Real.log 2 := by gcongr
      _ = Real.log 2 / (2 * Real.cos θ) := by ring
  have h_tri : limitingJ y θ - (1 / Real.cos θ) * Real.log (1 / |y|) =
      ((∫ v in Set.Ioc (0 : ℝ) 1, v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) -
        (∫ v in Set.Ioc (0 : ℝ) 1, v * (1 / Real.cos θ) / (y ^ 2 + v ^ 2))) +
      (1 / (2 * Real.cos θ)) * Real.log (y ^ 2 + 1) +
      (∫ v in Set.Ioi (1 : ℝ), v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) +
      (∫ v in Set.Ioi (0 : ℝ), y * (cTheta θ v).im / (y ^ 2 + v ^ 2)) := by
    rw [hJ_eq, hA_split, hA_main]; ring
  rw [h_tri]
  calc |((∫ v in Set.Ioc (0 : ℝ) 1, v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) -
        (∫ v in Set.Ioc (0 : ℝ) 1, v * (1 / Real.cos θ) / (y ^ 2 + v ^ 2))) +
      (1 / (2 * Real.cos θ)) * Real.log (y ^ 2 + 1) +
      (∫ v in Set.Ioi (1 : ℝ), v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) +
      (∫ v in Set.Ioi (0 : ℝ), y * (cTheta θ v).im / (y ^ 2 + v ^ 2))|
      ≤ |(∫ v in Set.Ioc (0 : ℝ) 1, v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) -
          (∫ v in Set.Ioc (0 : ℝ) 1, v * (1 / Real.cos θ) / (y ^ 2 + v ^ 2))| +
        |(1 / (2 * Real.cos θ)) * Real.log (y ^ 2 + 1)| +
        |∫ v in Set.Ioi (1 : ℝ), v * (cTheta θ v).re / (y ^ 2 + v ^ 2)| +
        |∫ v in Set.Ioi (0 : ℝ), y * (cTheta θ v).im / (y ^ 2 + v ^ 2)| := by
          linarith [abs_add_le ((∫ v in Set.Ioc (0 : ℝ) 1, v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) -
            (∫ v in Set.Ioc (0 : ℝ) 1, v * (1 / Real.cos θ) / (y ^ 2 + v ^ 2)))
            ((1 / (2 * Real.cos θ)) * Real.log (y ^ 2 + 1)),
            abs_add_le (((∫ v in Set.Ioc (0 : ℝ) 1, v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) -
            (∫ v in Set.Ioc (0 : ℝ) 1, v * (1 / Real.cos θ) / (y ^ 2 + v ^ 2))) +
            (1 / (2 * Real.cos θ)) * Real.log (y ^ 2 + 1))
            (∫ v in Set.Ioi (1 : ℝ), v * (cTheta θ v).re / (y ^ 2 + v ^ 2)),
            abs_add_le ((((∫ v in Set.Ioc (0 : ℝ) 1, v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) -
            (∫ v in Set.Ioc (0 : ℝ) 1, v * (1 / Real.cos θ) / (y ^ 2 + v ^ 2))) +
            (1 / (2 * Real.cos θ)) * Real.log (y ^ 2 + 1)) +
            (∫ v in Set.Ioi (1 : ℝ), v * (cTheta θ v).re / (y ^ 2 + v ^ 2)))
            (∫ v in Set.Ioi (0 : ℝ), y * (cTheta θ v).im / (y ^ 2 + v ^ 2))]
    _ ≤ C_A + Real.log 2 / (2 * Real.cos θ) + I_tail + C_B * (Real.pi / 2) := by
          gcongr
    _ ≤ C_A + I_tail + C_B * (Real.pi / 2) + Real.log 2 / (2 * Real.cos θ) + 1 := by linarith

/-- **Lemma 3.3 (Part 3)**: Large-`|y|` asymptotic `J(y, θ) = 2C(θ)/(π^2 y^2) + O_θ(|y|^{-3})`. -/
theorem limitingJ_asymptotic (θ : ℝ) (hθ : |θ| < Real.pi / 2) :
    ∃ (Y₀ C_inf : ℝ), Y₀ ≥ 1 ∧ C_inf > 0 ∧
      ∀ y : ℝ, |y| ≥ Y₀ →
        |limitingJ y θ - (2 * envelopeC θ) / (Real.pi ^ 2 * y ^ 2)| ≤ C_inf / |y| ^ 3 := by
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  have h_u_int : IntegrableOn (fun v : ℝ => uTheta θ v) (Set.Ioi 0) := by
    have h_exp : IntegrableOn (fun v : ℝ => Real.exp (-2 * Real.pi * v)) (Set.Ioi 0) := by
      have h_c : IntegrableOn (fun v : ℝ => Complex.exp ((-2 * Real.pi : ℂ) * v)) (Set.Ioi 0) :=
        integrableOn_exp_mul_complex_Ioi (by simp; positivity) 0
      have h_n : IntegrableOn (fun v : ℝ => ‖Complex.exp ((-2 * Real.pi : ℂ) * v)‖) (Set.Ioi 0) := h_c.norm
      refine IntegrableOn.congr_fun h_n (fun v _ => ?_) measurableSet_Ioi
      rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]; ring
    have hmeas : AEStronglyMeasurable (fun v : ℝ => uTheta θ v) (volume.restrict (Set.Ioi 0)) := by
      refine Continuous.aestronglyMeasurable ?_
      exact Continuous.div (by fun_prop) (continuous_const.mul ((Complex.continuous_cos.comp (by fun_prop))))
        (fun v => mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (cos_ne_zero_of_abs_lt hθ))
    refine (h_exp.const_mul (2 / (Real.pi * Real.cos θ))).mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    dsimp only [uTheta]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hcos_lb : (Real.cos θ / 2) * Real.exp (Real.pi * v) ≤
        ‖Complex.cos (θ + Complex.I * Real.pi * v)‖ := by
      have hsq : (Real.cos θ / 2 * Real.exp (Real.pi * v)) ^ 2 ≤
          ‖Complex.cos (θ + Complex.I * Real.pi * v)‖ ^ 2 := by
        have hch : Real.exp (Real.pi * v) / 2 ≤ Real.cosh (Real.pi * v) := by
          rw [Real.cosh_eq]; linarith [Real.exp_pos (-(Real.pi * v))]
        have h1 : Real.cos θ ^ 2 * Real.cosh (Real.pi * v) ^ 2 ≤ Real.sinh (Real.pi * v) ^ 2 + Real.cos θ ^ 2 := by
          have := Real.cosh_sq (Real.pi * v)
          have := Real.cos_sq_add_sin_sq θ
          nlinarith [sq_nonneg (Real.sin θ), sq_nonneg (Real.sinh (Real.pi * v))]
        rw [cos_normSq_eq]
        nlinarith [sq_le_sq' (by linarith [Real.exp_pos (Real.pi * v)]) hch]
      exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hsq
    calc Real.exp (-Real.pi * v) / (Real.pi * ‖Complex.cos (↑θ + Complex.I * ↑π * ↑v)‖)
        ≤ Real.exp (-Real.pi * v) / (Real.pi * ((Real.cos θ / 2) * Real.exp (Real.pi * v))) := by gcongr
      _ = (2 / (Real.pi * Real.cos θ)) * Real.exp (-2 * Real.pi * v) := by
          rw [show -2 * Real.pi * v = -Real.pi * v - Real.pi * v by ring, Real.exp_sub]
          field_simp [Real.pi_ne_zero, hcos_pos.ne']
  have h_vc_int : IntegrableOn (fun v : ℝ => (v : ℂ) * cTheta θ v) (Set.Ioi 0) := by
    have h_exp : IntegrableOn (fun v : ℝ => Real.exp (-Real.pi * v)) (Set.Ioi 0) := by
      have h_c : IntegrableOn (fun v : ℝ => Complex.exp ((-Real.pi : ℂ) * v)) (Set.Ioi 0) :=
        integrableOn_exp_mul_complex_Ioi (by simp; positivity) 0
      have h_n : IntegrableOn (fun v : ℝ => ‖Complex.exp ((-Real.pi : ℂ) * v)‖) (Set.Ioi 0) := h_c.norm
      refine IntegrableOn.congr_fun h_n (fun v _ => ?_) measurableSet_Ioi
      rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]; ring
    have hmeas : AEStronglyMeasurable (fun v : ℝ => (v : ℂ) * cTheta θ v) (volume.restrict (Set.Ioi 0)) := by
      refine Continuous.aestronglyMeasurable ?_
      exact Complex.continuous_ofReal.mul (continuous_const.div (Continuous.pow ((Complex.continuous_cos.comp (by fun_prop))) 2)
        (fun v => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ)))
    refine (h_exp.const_mul (4 / (Real.pi * Real.cos θ ^ 2))).mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv]
    have h1 : v ≤ Real.exp (Real.pi * v) / Real.pi := by
      have := Real.add_one_le_exp (Real.pi * v)
      rw [le_div_iff₀ Real.pi_pos]; linarith
    have h2 : v * Real.exp (-2 * Real.pi * v) ≤ (1 / Real.pi) * Real.exp (-Real.pi * v) := by
      rw [show -2 * Real.pi * v = -Real.pi * v - Real.pi * v by ring, Real.exp_sub]
      calc v * (Real.exp (-Real.pi * v) / Real.exp (Real.pi * v))
          ≤ (Real.exp (Real.pi * v) / Real.pi) * (Real.exp (-Real.pi * v) / Real.exp (Real.pi * v)) := by gcongr
        _ = (1 / Real.pi) * Real.exp (-Real.pi * v) := by field_simp [(Real.exp_pos _).ne', Real.pi_ne_zero]
    calc v * ‖cTheta θ v‖ ≤ v * ((4 / Real.cos θ ^ 2) * Real.exp (-2 * Real.pi * v)) :=
          mul_le_mul_of_nonneg_left (cTheta_norm_le hθ hv.le) hv.le
      _ = (4 / Real.cos θ ^ 2) * (v * Real.exp (-2 * Real.pi * v)) := by ring
      _ ≤ (4 / Real.cos θ ^ 2) * ((1 / Real.pi) * Real.exp (-Real.pi * v)) := by gcongr
      _ = (4 / (Real.pi * Real.cos θ ^ 2)) * Real.exp (-Real.pi * v) := by ring
  have h_v2c_int : IntegrableOn (fun v : ℝ => v ^ 2 * ‖cTheta θ v‖) (Set.Ioi 0) := by
    have h_exp : IntegrableOn (fun v : ℝ => Real.exp (-Real.pi * v)) (Set.Ioi 0) := by
      have h_c : IntegrableOn (fun v : ℝ => Complex.exp ((-Real.pi : ℂ) * v)) (Set.Ioi 0) :=
        integrableOn_exp_mul_complex_Ioi (by simp; positivity) 0
      have h_n : IntegrableOn (fun v : ℝ => ‖Complex.exp ((-Real.pi : ℂ) * v)‖) (Set.Ioi 0) := h_c.norm
      refine IntegrableOn.congr_fun h_n (fun v _ => ?_) measurableSet_Ioi
      rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]; ring
    have hmeas : AEStronglyMeasurable (fun v : ℝ => v ^ 2 * ‖cTheta θ v‖) (volume.restrict (Set.Ioi 0)) := by
      refine Continuous.aestronglyMeasurable ?_
      exact (continuous_pow 2).mul (Continuous.norm (continuous_const.div (Continuous.pow ((Complex.continuous_cos.comp (by fun_prop))) 2)
        (fun v => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ))))
    refine (h_exp.const_mul (32 / (Real.pi ^ 2 * Real.cos θ ^ 2))).mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 < v := hv
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : (Real.pi * v / 2) ^ 2 / 2 ≤ Real.exp (Real.pi * v / 2) := by
      have h_s := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ Real.pi * v / 2) 3
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
        pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one,
        Nat.factorial_two, Nat.cast_ofNat] at h_s
      linarith [hv0.le, Real.pi_pos, (by positivity : 0 ≤ Real.pi * v / 2)]
    have h2 : v ^ 2 * Real.exp (-2 * Real.pi * v) ≤ (8 / Real.pi ^ 2) * Real.exp (-Real.pi * v) := by
      have hsq : v ^ 2 ≤ (8 / Real.pi ^ 2) * Real.exp (Real.pi * v / 2) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos Real.pi_pos)]
        have : (Real.pi * v / 2) ^ 2 / 2 = Real.pi ^ 2 * v ^ 2 / 8 := by ring
        linarith
      have hexp : Real.exp (Real.pi * v / 2) * Real.exp (-2 * Real.pi * v) ≤ Real.exp (-Real.pi * v) := by
        rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos, hv0]
      calc v ^ 2 * Real.exp (-2 * Real.pi * v)
          ≤ (8 / Real.pi ^ 2) * Real.exp (Real.pi * v / 2) * Real.exp (-2 * Real.pi * v) := by gcongr
        _ = (8 / Real.pi ^ 2) * (Real.exp (Real.pi * v / 2) * Real.exp (-2 * Real.pi * v)) := by ring
        _ ≤ (8 / Real.pi ^ 2) * Real.exp (-Real.pi * v) := by gcongr
    calc v ^ 2 * ‖cTheta θ v‖ ≤ v ^ 2 * ((4 / Real.cos θ ^ 2) * Real.exp (-2 * Real.pi * v)) :=
          mul_le_mul_of_nonneg_left (cTheta_norm_le hθ hv.le) (sq_nonneg v)
      _ = (4 / Real.cos θ ^ 2) * (v ^ 2 * Real.exp (-2 * Real.pi * v)) := by ring
      _ ≤ (4 / Real.cos θ ^ 2) * ((8 / Real.pi ^ 2) * Real.exp (-Real.pi * v)) := by gcongr
      _ = (32 / (Real.pi ^ 2 * Real.cos θ ^ 2)) * Real.exp (-Real.pi * v) := by ring
  have h_ibp : (∫ v in Set.Ioi (0 : ℝ), (v : ℂ) * cTheta θ v) = ∫ v in Set.Ioi (0 : ℝ), uTheta θ v := by
    have hderiv : ∀ v ∈ Set.Ici (0 : ℝ),
        HasDerivAt (fun t : ℝ => -(t : ℂ) * uTheta θ t) (-uTheta θ v + (v : ℂ) * cTheta θ v) v := by
      intro v _
      have hd1 := (hasDerivAt_id v).ofReal_comp
      have hd2 := uTheta_deriv (v := v) hθ
      convert hd1.mul hd2 using 1
      · ext t; simp
      · simp; try ring
    have htend : Tendsto (fun t : ℝ => -(t : ℂ) * uTheta θ t) atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h_bnd : ∀ᶠ v : ℝ in atTop, ‖-(v : ℂ) * uTheta θ v‖ ≤ (2 / (Real.pi * Real.cos θ)) * v * Real.exp (-2 * Real.pi * v) := by
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
        rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv]
        dsimp only [uTheta]
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        have hcos_lb : (Real.cos θ / 2) * Real.exp (Real.pi * v) ≤
            ‖Complex.cos (θ + Complex.I * Real.pi * v)‖ := by
          have hsq : (Real.cos θ / 2 * Real.exp (Real.pi * v)) ^ 2 ≤
              ‖Complex.cos (θ + Complex.I * Real.pi * v)‖ ^ 2 := by
            have hch : Real.exp (Real.pi * v) / 2 ≤ Real.cosh (Real.pi * v) := by
              rw [Real.cosh_eq]; linarith [Real.exp_pos (-(Real.pi * v))]
            have h1 : Real.cos θ ^ 2 * Real.cosh (Real.pi * v) ^ 2 ≤ Real.sinh (Real.pi * v) ^ 2 + Real.cos θ ^ 2 := by
              have := Real.cosh_sq (Real.pi * v); have := Real.cos_sq_add_sin_sq θ
              nlinarith [sq_nonneg (Real.sin θ), sq_nonneg (Real.sinh (Real.pi * v))]
            rw [cos_normSq_eq]
            nlinarith [sq_le_sq' (by linarith [Real.exp_pos (Real.pi * v)]) hch]
          exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hsq
        calc v * (Real.exp (-Real.pi * v) / (Real.pi * ‖Complex.cos (↑θ + Complex.I * ↑π * ↑v)‖))
            ≤ v * (Real.exp (-Real.pi * v) / (Real.pi * ((Real.cos θ / 2) * Real.exp (Real.pi * v)))) := by gcongr
          _ = (2 / (Real.pi * Real.cos θ)) * v * Real.exp (-2 * Real.pi * v) := by
              rw [show -2 * Real.pi * v = -Real.pi * v - Real.pi * v by ring, Real.exp_sub]
              field_simp [Real.pi_ne_zero, hcos_pos.ne']
      have h_lim : Tendsto (fun v : ℝ => (2 / (Real.pi * Real.cos θ)) * v * Real.exp (-2 * Real.pi * v)) atTop (nhds 0) := by
        have h1 : Tendsto (fun v : ℝ => v * Real.exp (-(2 * Real.pi) * v)) atTop (nhds 0) := by
          have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
            (tendsto_id.const_mul_atTop (by positivity : 0 < 2 * Real.pi))
          have h0' := h0.const_mul (1 / (2 * Real.pi))
          simp only [Function.comp_def, id_eq, pow_one, mul_zero] at h0'
          refine h0'.congr (fun v => ?_)
          field_simp [Real.pi_ne_zero]
        simpa [mul_assoc] using h1.const_mul (2 / (Real.pi * Real.cos θ))
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim
        (Eventually.of_forall fun _ => norm_nonneg _) h_bnd
    have hres := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (h_u_int.neg.add h_vc_int) htend
    simp only [Complex.ofReal_zero, neg_zero, zero_mul, sub_zero] at hres
    have h1 : (∫ v in Set.Ioi (0 : ℝ), (-uTheta θ v + (v : ℂ) * cTheta θ v)) =
        -(∫ v in Set.Ioi (0 : ℝ), uTheta θ v) + ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) * cTheta θ v := by
      have ha : (∫ v in Set.Ioi (0 : ℝ), (-uTheta θ v + (v : ℂ) * cTheta θ v)) =
          (∫ v in Set.Ioi (0 : ℝ), -uTheta θ v) + ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) * cTheta θ v :=
        integral_add h_u_int.neg h_vc_int
      rw [ha, integral_neg]
    rw [h1] at hres
    linear_combination hres
  have h_u_eval : (∫ v in Set.Ioi (0 : ℝ), uTheta θ v) =
      Complex.exp (-Complex.I * θ) / Real.pi ^ 2 * Complex.log (1 + Complex.exp (2 * Complex.I * θ)) := by
    let W : ℝ → ℂ := fun v => -(1 / Real.pi ^ 2) * Complex.exp (-Complex.I * θ) *
      Complex.log (1 + Complex.exp (2 * Complex.I * θ - 2 * Real.pi * v))
    have h_slit : ∀ v ≥ (0 : ℝ), 1 + Complex.exp (2 * Complex.I * θ - 2 * Real.pi * v) ∈ Complex.slitPlane := by
      intro v hv
      left
      have hre : (1 + Complex.exp (2 * Complex.I * θ - 2 * Real.pi * v)).re =
          1 + Real.exp (-2 * Real.pi * v) * Real.cos (2 * θ) := by
        rw [Complex.add_re, Complex.one_re, show 2 * Complex.I * (θ : ℂ) - 2 * Real.pi * v =
          ((-2 * Real.pi * v : ℝ) : ℂ) + ((2 * θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
        simp [Complex.mul_re]
      rw [hre]
      have hcos2 : -1 < Real.cos (2 * θ) := by
        have h2θ : 2 * θ ∈ Set.Ioo (-Real.pi) Real.pi := by
          have := abs_lt.mp hθ; constructor <;> linarith
        have hsin : Real.sin θ ^ 2 < 1 := by
          have := Real.cos_sq_add_sin_sq θ
          nlinarith [sq_pos_of_pos hcos_pos]
        rw [Real.cos_two_mul]
        nlinarith [sq_pos_of_pos hcos_pos]
      have hexp_le : Real.exp (-2 * Real.pi * v) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
      have hexp_pos : 0 < Real.exp (-2 * Real.pi * v) := Real.exp_pos _
      nlinarith
    have hderiv : ∀ v ∈ Set.Ici (0 : ℝ), HasDerivAt W (uTheta θ v) v := by
      intro v hv
      have hd1 : HasDerivAt (fun t : ℝ => 1 + Complex.exp (2 * Complex.I * θ - 2 * Real.pi * t))
          (Complex.exp (2 * Complex.I * θ - 2 * Real.pi * v) * (-2 * Real.pi)) v := by
        have h := ((hasDerivAt_id v).ofReal_comp.const_mul (-2 * (Real.pi : ℂ))).const_add (2 * Complex.I * θ)
        simpa [sub_eq_add_neg] using h.cexp.const_add (1 : ℂ)
      have hlog := (Complex.hasDerivAt_log (h_slit v hv)).comp v hd1
      have hW := hlog.const_mul (-(1 / (Real.pi : ℂ) ^ 2) * Complex.exp (-Complex.I * θ))
      refine hW.congr_deriv ?_
      have hden_ne : 1 + Complex.exp (2 * Complex.I * θ - 2 * Real.pi * v) ≠ 0 :=
        Complex.slitPlane_ne_zero (h_slit v hv)
      have hcos_eq : Complex.cos (θ + Complex.I * Real.pi * v) =
          (Complex.exp (-Complex.I * θ + Real.pi * v) * (1 + Complex.exp (2 * Complex.I * θ - 2 * Real.pi * v))) / 2 := by
        unfold Complex.cos
        have he1 : Complex.exp ((θ + Complex.I * Real.pi * v) * Complex.I) =
            Complex.exp (-Complex.I * θ + Real.pi * v) * Complex.exp (2 * Complex.I * θ - 2 * Real.pi * v) := by
          rw [← Complex.exp_add]; congr 1; push_cast; ring_nf; simp [Complex.I_sq]; ring
        have he2 : Complex.exp (-(θ + Complex.I * Real.pi * v) * Complex.I) =
            Complex.exp (-Complex.I * θ + Real.pi * v) := by
          congr 1; push_cast; ring_nf; simp [Complex.I_sq]; ring
        rw [he1, he2]; ring
      dsimp only [uTheta]
      rw [hcos_eq]
      have he_ne : Complex.exp (-Complex.I * θ + Real.pi * v) ≠ 0 := Complex.exp_ne_zero _
      field_simp [Real.pi_ne_zero, hden_ne, he_ne]
      have hexp_prod : Complex.exp (-(Complex.I * θ)) * Complex.exp (2 * (Complex.I * θ - Real.pi * v)) *
          Complex.exp (-(Complex.I * θ) + Real.pi * v) = Complex.exp (-Real.pi * v) := by
        rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
      rw [hexp_prod, show (-Real.pi * (v : ℂ)) = ((-Real.pi * v : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_exp]
    have htend : Tendsto W atTop (nhds 0) := by
      have h_lim_exp : Tendsto (fun v : ℝ => 1 + Complex.exp (2 * Complex.I * θ - 2 * Real.pi * v)) atTop (nhds 1) := by
        have h_zero : Tendsto (fun v : ℝ => Complex.exp (2 * Complex.I * θ - 2 * Real.pi * v)) atTop (nhds 0) := by
          rw [tendsto_zero_iff_norm_tendsto_zero]
          have heq : (fun v : ℝ => ‖Complex.exp (2 * Complex.I * θ - 2 * Real.pi * v)‖) =
              fun v => Real.exp (-(2 * Real.pi) * v) := by
            ext v
            rw [Complex.norm_exp]; simp
          rw [heq]
          exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith [Real.pi_pos] : -(2 * Real.pi) < 0))
        simpa using tendsto_const_nhds.add h_zero
      have h_log : Tendsto (fun v : ℝ => Complex.log (1 + Complex.exp (2 * Complex.I * θ - 2 * Real.pi * v))) atTop (nhds 0) := by
        have hcont : ContinuousAt Complex.log 1 :=
          (Complex.hasDerivAt_log (by simp : (1 : ℂ) ∈ Complex.slitPlane)).continuousAt
        have hcomp : Tendsto (Complex.log ∘ fun v : ℝ => 1 + Complex.exp (2 * Complex.I * θ - 2 * Real.pi * v)) atTop (nhds 0) := by
          simpa [Complex.log_one] using hcont.tendsto.comp h_lim_exp
        exact hcomp
      have h_mul := (tendsto_const_nhds (x := -(1 / (Real.pi : ℂ) ^ 2) * Complex.exp (-Complex.I * θ))).mul h_log
      rw [mul_zero] at h_mul
      exact h_mul.congr fun v => by dsimp only [W]; ring
    have hres := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv h_u_int htend
    rw [hres, zero_sub]
    dsimp only [W]; simp only [Complex.ofReal_zero, mul_zero, sub_zero]; ring
  have h_main_re : (∫ v in Set.Ioi (0 : ℝ), (v : ℂ) * cTheta θ v).re = 2 * envelopeC θ / Real.pi ^ 2 := by
    rw [h_ibp, h_u_eval]
    have h_sum_exp' : 1 + Complex.exp (2 * Complex.I * θ) = (2 * Real.cos θ : ℂ) * Complex.exp (Complex.I * θ) := by
      push_cast; unfold Complex.cos
      have h1 : Complex.exp (Complex.I * θ) * Complex.exp (-Complex.I * θ) = 1 := by
        rw [← Complex.exp_add, show Complex.I * θ + -Complex.I * θ = 0 by ring, Complex.exp_zero]
      have h2 : Complex.exp (2 * Complex.I * θ) = Complex.exp (Complex.I * θ) * Complex.exp (Complex.I * θ) := by
        rw [← Complex.exp_add]; congr 1; ring
      rw [h2, show (θ : ℂ) * Complex.I = Complex.I * θ by ring, show -(θ : ℂ) * Complex.I = -Complex.I * θ by ring]
      linear_combination -h1
    rw [h_sum_exp']
    have h_log_eq : Complex.log ((2 * Real.cos θ : ℂ) * Complex.exp (Complex.I * θ)) =
        (Real.log (2 * Real.cos θ) : ℂ) + Complex.I * θ := by
      have hpos_c : 0 < 2 * Real.cos θ := by positivity
      have hexp_eq : (2 * Real.cos θ : ℂ) * Complex.exp (Complex.I * θ) =
          Complex.exp ((Real.log (2 * Real.cos θ) : ℂ) + Complex.I * θ) := by
        rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hpos_c]
        push_cast; ring
      rw [hexp_eq, Complex.log_exp]
      · have := abs_lt.mp hθ; simp; linarith [Real.pi_pos]
      · have := abs_lt.mp hθ; simp; linarith [Real.pi_pos]
    rw [h_log_eq]
    have hexp_re_im : Complex.exp (-Complex.I * θ) = (Real.cos θ : ℂ) - Complex.I * (Real.sin θ : ℂ) := by
      rw [show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
      simp [Complex.cos_neg, Complex.sin_neg]; ring
    rw [hexp_re_im]
    simp only [div_mul_eq_mul_div, Complex.div_ofReal_re, Complex.mul_re, Complex.sub_re,
      Complex.ofReal_re, Complex.mul_im, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
      mul_one, sub_zero, zero_add, Complex.add_re, Complex.add_im, Complex.sub_im,
      zero_sub, neg_mul, sub_neg_eq_add]
    unfold envelopeC
    ring_nf; rw [Complex.I_sq]; ring
  set C_inf := max 1 (∫ v in Set.Ioi (0 : ℝ), v ^ 2 * ‖cTheta θ v‖)
  refine ⟨1, C_inf, le_rfl, by positivity, fun y hy => ?_⟩
  have hy1 : 1 ≤ |y| := hy
  have hy_ne : y ≠ 0 := abs_pos.mp (by linarith)
  have h_id : ∀ v : ℝ, cTheta θ v / ((y : ℂ) - Complex.I * v) =
      cTheta θ v / (y : ℂ) + Complex.I * ((v : ℂ) * cTheta θ v) / (y : ℂ) ^ 2 -
      (cTheta θ v * (v : ℂ) ^ 2) / ((y : ℂ) ^ 2 * ((y : ℂ) - Complex.I * v)) := by
    intro v
    have h1 : (y : ℂ) - Complex.I * v ≠ 0 := by
      intro h; have := congr_arg Complex.re h; simp at this; exact hy_ne this
    have h2 : (y : ℂ) ≠ 0 := by exact_mod_cast hy_ne
    field_simp [h1, h2]
    rw [Complex.I_sq]; ring
  have h_int_1 : IntegrableOn (fun v : ℝ => (cTheta θ v / (y : ℂ)).im) (Set.Ioi 0) :=
    (IntegrableOn.congr_fun (Integrable.const_mul hc_int ((1 : ℂ) / y)) (fun v _ => by ring) measurableSet_Ioi).im
  have h_int_2 : IntegrableOn (fun v : ℝ => (Complex.I * ((v : ℂ) * cTheta θ v) / (y : ℂ) ^ 2).im) (Set.Ioi 0) :=
    (IntegrableOn.congr_fun (Integrable.const_mul h_vc_int (Complex.I / (y : ℂ) ^ 2)) (fun v _ => by ring) measurableSet_Ioi).im
  have h_int_3 : IntegrableOn (fun v : ℝ => ((cTheta θ v * (v : ℂ) ^ 2) / ((y : ℂ) ^ 2 * ((y : ℂ) - Complex.I * v))).im) (Set.Ioi 0) := by
    refine (h_v2c_int.div_const (|y| ^ 3)).mono' (Continuous.aestronglyMeasurable (Complex.continuous_im.comp (by
      refine Continuous.div ?_ ?_ (fun v => ?_)
      · exact (continuous_const.div (Continuous.pow ((Complex.continuous_cos.comp (by fun_prop))) 2)
          (fun v => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ))).mul (by fun_prop)
      · exact continuous_const.mul (continuous_const.sub (continuous_const.mul Complex.continuous_ofReal))
      · refine mul_ne_zero (pow_ne_zero 2 (by exact_mod_cast hy_ne)) ?_
        intro h; have := congr_arg Complex.re h; simp at this; exact hy_ne this))) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
    rw [Real.norm_eq_abs]
    refine (Complex.abs_im_le_norm _).trans ?_
    rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs]
    have hden : |y| ≤ ‖(y : ℂ) - Complex.I * v‖ := by
      have : |y| = ‖((y : ℂ) - Complex.I * v).re‖ := by simp [Real.norm_eq_abs]
      rw [this]; exact Complex.abs_re_le_norm _
    calc ‖cTheta θ v‖ * |v| ^ 2 / (|y| ^ 2 * ‖(y : ℂ) - Complex.I * v‖)
        ≤ ‖cTheta θ v‖ * v ^ 2 / (|y| ^ 2 * |y|) := by
          rw [sq_abs]; gcongr
      _ = v ^ 2 * ‖cTheta θ v‖ / |y| ^ 3 := by ring
  have hJ_split : limitingJ y θ =
      (∫ v in Set.Ioi (0 : ℝ), (cTheta θ v / (y : ℂ)).im) +
      (∫ v in Set.Ioi (0 : ℝ), (Complex.I * ((v : ℂ) * cTheta θ v) / (y : ℂ) ^ 2).im) -
      (∫ v in Set.Ioi (0 : ℝ), ((cTheta θ v * (v : ℂ) ^ 2) / ((y : ℂ) ^ 2 * ((y : ℂ) - Complex.I * v))).im) := by
    unfold limitingJ
    have hadd : (∫ v in Set.Ioi (0 : ℝ), (cTheta θ v / (y : ℂ)).im) +
        (∫ v in Set.Ioi (0 : ℝ), (Complex.I * ((v : ℂ) * cTheta θ v) / (y : ℂ) ^ 2).im) =
        ∫ v in Set.Ioi (0 : ℝ), ((cTheta θ v / (y : ℂ)).im +
          (Complex.I * ((v : ℂ) * cTheta θ v) / (y : ℂ) ^ 2).im) := (integral_add h_int_1 h_int_2).symm
    have h_int_12 : IntegrableOn (fun v : ℝ => (cTheta θ v / (y : ℂ)).im +
        (Complex.I * ((v : ℂ) * cTheta θ v) / (y : ℂ) ^ 2).im) (Set.Ioi 0) := h_int_1.add h_int_2
    rw [hadd, ← integral_sub h_int_12 h_int_3]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    change (cTheta θ v / ((y : ℂ) - Complex.I * v)).im = _
    rw [h_id v, Complex.sub_im, Complex.add_im]
  have hterm1 : (∫ v in Set.Ioi (0 : ℝ), (cTheta θ v / (y : ℂ)).im) = 0 := by
    have : (fun v : ℝ => (cTheta θ v / (y : ℂ)).im) = fun v => (cTheta θ v).im / y := by
      ext v; rw [Complex.div_ofReal_im]
    rw [this, integral_div, cTheta_im_integral_zero hθ, zero_div]
  have hterm2 : (∫ v in Set.Ioi (0 : ℝ), (Complex.I * ((v : ℂ) * cTheta θ v) / (y : ℂ) ^ 2).im) =
      (2 * envelopeC θ) / (Real.pi ^ 2 * y ^ 2) := by
    have : (fun v : ℝ => (Complex.I * ((v : ℂ) * cTheta θ v) / (y : ℂ) ^ 2).im) =
        fun v : ℝ => ((v : ℂ) * cTheta θ v).re / y ^ 2 := by
      ext v
      rw [← Complex.ofReal_pow, Complex.div_ofReal_im, Complex.I_mul_im]
    rw [this, integral_div, ← Complex.reCLM.integral_comp_comm h_vc_int, h_main_re]
    ring
  have hcancel : (2 * envelopeC θ) / (Real.pi ^ 2 * y ^ 2) -
      (∫ v in Set.Ioi (0 : ℝ), ((cTheta θ v * (v : ℂ) ^ 2) / ((y : ℂ) ^ 2 * ((y : ℂ) - Complex.I * v))).im) -
      (2 * envelopeC θ) / (Real.pi ^ 2 * y ^ 2) =
      -(∫ v in Set.Ioi (0 : ℝ), ((cTheta θ v * (v : ℂ) ^ 2) / ((y : ℂ) ^ 2 * ((y : ℂ) - Complex.I * v))).im) := by ring
  rw [hJ_split, hterm1, hterm2, zero_add, hcancel, abs_neg]
  calc |∫ v in Set.Ioi (0 : ℝ), ((cTheta θ v * (v : ℂ) ^ 2) / ((y : ℂ) ^ 2 * ((y : ℂ) - Complex.I * v))).im|
      ≤ ∫ v in Set.Ioi (0 : ℝ), ‖((cTheta θ v * (v : ℂ) ^ 2) / ((y : ℂ) ^ 2 * ((y : ℂ) - Complex.I * v))).im‖ :=
        by rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
    _ ≤ ∫ v in Set.Ioi (0 : ℝ), v ^ 2 * ‖cTheta θ v‖ / |y| ^ 3 := by
        refine setIntegral_mono_on h_int_3.norm (h_v2c_int.div_const (|y| ^ 3)) measurableSet_Ioi fun v _ => ?_
        rw [Real.norm_eq_abs]
        refine (Complex.abs_im_le_norm _).trans ?_
        rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, sq_abs]
        have hden : |y| ≤ ‖(y : ℂ) - Complex.I * v‖ := by
          have : |y| = ‖((y : ℂ) - Complex.I * v).re‖ := by simp [Real.norm_eq_abs]
          rw [this]; exact Complex.abs_re_le_norm _
        calc ‖cTheta θ v‖ * v ^ 2 / (|y| ^ 2 * ‖(y : ℂ) - Complex.I * v‖)
            ≤ ‖cTheta θ v‖ * v ^ 2 / (|y| ^ 2 * |y|) := by gcongr
          _ = v ^ 2 * ‖cTheta θ v‖ / |y| ^ 3 := by ring
    _ = (∫ v in Set.Ioi (0 : ℝ), v ^ 2 * ‖cTheta θ v‖) / |y| ^ 3 := integral_div _ _
    _ ≤ C_inf / |y| ^ 3 := by gcongr; exact le_max_right _ _


end PolarEvaluation
