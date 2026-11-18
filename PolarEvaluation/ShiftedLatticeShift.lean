import PolarEvaluation.ShiftedLatticeCore

noncomputable section

open Complex Real MeasureTheory Filter Topology
open scoped FourierTransform

namespace PolarEvaluation

lemma sin_norm_ge_sinh (x y : ℝ) :
    Real.sinh |y| ≤ ‖Complex.sin ((x : ℂ) + Complex.I * y)‖ := by
  have hsin : Complex.sin ((x : ℂ) + Complex.I * y) =
      ((Real.sin x * Real.cosh y : ℝ) : ℂ) + ((Real.cos x * Real.sinh y : ℝ) : ℂ) * Complex.I := by
    rw [Complex.sin_add]
    have h1 : Complex.cos (Complex.I * y) = Real.cosh y := by
      rw [mul_comm, Complex.cos_mul_I]; simp [Complex.ofReal_cosh]
    have h2 : Complex.sin (Complex.I * y) = Complex.I * Real.sinh y := by
      rw [mul_comm, Complex.sin_mul_I]; simp [Complex.ofReal_sinh]; ring
    rw [h1, h2]
    simp only [Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.ofReal_sin, Complex.ofReal_cos]
    push_cast; ring
  have hsq : Real.sinh |y| ^ 2 ≤ ‖Complex.sin ((x : ℂ) + Complex.I * y)‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hsin, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
      Complex.mul_im, zero_add]
    have h1 : Real.cosh y ^ 2 = Real.sinh y ^ 2 + 1 := by
      have := Real.cosh_sq_sub_sinh_sq y; linarith
    have h2 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    have h3 : Real.sinh |y| ^ 2 = Real.sinh y ^ 2 := by
      rcases le_or_gt 0 y with hy | hy
      · rw [abs_of_nonneg hy]
      · rw [abs_of_neg hy, Real.sinh_neg, neg_sq]
    nlinarith [sq_nonneg (Real.sin x), sq_nonneg (Real.sinh y)]
  exact (sq_le_sq₀ (Real.sinh_nonneg_iff.mpr (abs_nonneg y)) (norm_nonneg _)).mp hsq

lemma sinh_ge_mul_exp {y : ℝ} (hy : Real.pi ≤ y) :
    ((1 - Real.exp (-2 * Real.pi)) / 2) * Real.exp y ≤ Real.sinh y := by
  rw [Real.sinh_eq]
  have h1 : Real.exp (-y) ≤ Real.exp (-2 * Real.pi) * Real.exp y := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  linarith

lemma complex_inv_sin_sq_bound (Δ : ℝ) (hΔ : Δ ≥ 1) (t : ℝ) :
    ‖(Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 2‖ ≤
      (4 * Real.pi ^ 2 / (1 - Real.exp (-2 * Real.pi)) ^ 2) * Real.exp (-2 * Real.pi * Δ) := by
  have h1m : 0 < 1 - Real.exp (-2 * Real.pi) := by
    linarith [Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos] : -2 * Real.pi < 0)]
  have hsinh : ((1 - Real.exp (-2 * Real.pi)) / 2) * Real.exp (Real.pi * Δ) ≤
      ‖Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ))‖ := by
    have heq : (Real.pi : ℂ) * ((-t : ℂ) + Complex.I * Δ) =
        ((-Real.pi * t : ℝ) : ℂ) + Complex.I * (Real.pi * Δ) := by
      push_cast; ring
    rw [heq]
    have hs1 := sin_norm_ge_sinh (-Real.pi * t) (Real.pi * Δ)
    rw [abs_of_pos (by positivity)] at hs1
    exact (sinh_ge_mul_exp (by nlinarith [Real.pi_pos])).trans hs1
  have hpos_lb : 0 < ((1 - Real.exp (-2 * Real.pi)) / 2) * Real.exp (Real.pi * Δ) := by positivity
  rw [norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc Real.pi ^ 2 / ‖Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ))‖ ^ 2
      ≤ Real.pi ^ 2 / (((1 - Real.exp (-2 * Real.pi)) / 2) * Real.exp (Real.pi * Δ)) ^ 2 := by
        gcongr
    _ = (4 * Real.pi ^ 2 / (1 - Real.exp (-2 * Real.pi)) ^ 2) * Real.exp (-2 * Real.pi * Δ) := by
        rw [mul_pow, ← Real.exp_nat_mul, show (2 : ℕ) * (Real.pi * Δ) = 2 * Real.pi * Δ by push_cast; ring,
          show -2 * Real.pi * Δ = -(2 * Real.pi * Δ) by ring, Real.exp_neg]
        field_simp [h1m.ne']; ring

lemma complex_inv_sin_sq_lipschitz (Δ : ℝ) (hΔ : Δ ≥ 1) {α β : ℝ} (hαβ : α ≤ β) :
    ‖(Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-β : ℂ) + Complex.I * Δ)) ^ 2 -
      (Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-α : ℂ) + Complex.I * Δ)) ^ 2‖ ≤
      (16 * Real.pi ^ 3 / (1 - Real.exp (-2 * Real.pi)) ^ 3) * Real.exp (-2 * Real.pi * Δ) * (β - α) := by
  let h : ℝ → ℂ := fun t => (Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 2
  have h1m : 0 < 1 - Real.exp (-2 * Real.pi) := by
    linarith [Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos] : -2 * Real.pi < 0)]
  have hsin_ne : ∀ t : ℝ, Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ≠ 0 := by
    intro t
    rw [← norm_ne_zero_iff]
    have hs1 : 0 < ((1 - Real.exp (-2 * Real.pi)) / 2) * Real.exp (Real.pi * Δ) := by positivity
    have heq : (Real.pi : ℂ) * ((-t : ℂ) + Complex.I * Δ) =
        ((-Real.pi * t : ℝ) : ℂ) + Complex.I * (Real.pi * Δ) := by
      push_cast; ring
    have hs2 := sin_norm_ge_sinh (-Real.pi * t) (Real.pi * Δ)
    rw [abs_of_pos (by positivity)] at hs2
    have hs3 := (sinh_ge_mul_exp (by nlinarith [Real.pi_pos])).trans hs2
    rw [← heq] at hs3
    linarith
  have hderiv : ∀ t ∈ Set.Icc α β, HasDerivWithinAt h
      (2 * (Real.pi : ℂ) ^ 3 * Complex.cos (Real.pi * ((-t : ℂ) + Complex.I * Δ)) /
        Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 3) (Set.Icc α β) t := by
    intro t _
    have h_in : HasDerivAt (fun s : ℝ => (Real.pi : ℂ) * ((-s : ℂ) + Complex.I * Δ)) (-Real.pi) t := by
      have h1 := ((hasDerivAt_id t).ofReal_comp.neg.add_const (Complex.I * Δ)).const_mul (Real.pi : ℂ)
      convert h1 using 1; simp
    have h_sin : HasDerivAt (fun s : ℝ => Complex.sin (Real.pi * ((-s : ℂ) + Complex.I * Δ)))
        (Complex.cos (Real.pi * ((-t : ℂ) + Complex.I * Δ)) * (-Real.pi)) t :=
      (Complex.hasDerivAt_sin _).comp t h_in
    have h_sq : HasDerivAt (fun s : ℝ => Complex.sin (Real.pi * ((-s : ℂ) + Complex.I * Δ)) ^ 2)
        (2 * Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 1 *
          (Complex.cos (Real.pi * ((-t : ℂ) + Complex.I * Δ)) * (-Real.pi))) t :=
      h_sin.pow 2
    have h_div := (hasDerivAt_const t ((Real.pi : ℂ) ^ 2)).div h_sq (pow_ne_zero 2 (hsin_ne t))
    refine (h_div.congr_deriv ?_).hasDerivWithinAt
    have hne := hsin_ne t
    field_simp [hne]; ring
  have hnorm_bd : ∀ t ∈ Set.Icc α β,
      ‖2 * (Real.pi : ℂ) ^ 3 * Complex.cos (Real.pi * ((-t : ℂ) + Complex.I * Δ)) /
        Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 3‖ ≤
        (16 * Real.pi ^ 3 / (1 - Real.exp (-2 * Real.pi)) ^ 3) * Real.exp (-2 * Real.pi * Δ) := by
    intro t _
    have heq : (Real.pi : ℂ) * ((-t : ℂ) + Complex.I * Δ) =
        ((-Real.pi * t : ℝ) : ℂ) + Complex.I * (Real.pi * Δ) := by
      push_cast; ring
    have hcos_bd : ‖Complex.cos (Real.pi * ((-t : ℂ) + Complex.I * Δ))‖ ≤ Real.exp (Real.pi * Δ) := by
      rw [heq, Complex.cos_add]
      have h1 : Complex.cos (Complex.I * (Real.pi * Δ)) = Real.cosh (Real.pi * Δ) := by
        rw [mul_comm, Complex.cos_mul_I]; simp [Complex.ofReal_cosh]
      have h2 : Complex.sin (Complex.I * (Real.pi * Δ)) = Complex.I * Real.sinh (Real.pi * Δ) := by
        rw [mul_comm, Complex.sin_mul_I]; simp [Complex.ofReal_sinh]; ring
      rw [h1, h2]
      calc ‖Complex.cos ((-Real.pi * t : ℝ) : ℂ) * Real.cosh (Real.pi * Δ) -
            Complex.sin ((-Real.pi * t : ℝ) : ℂ) * (Complex.I * Real.sinh (Real.pi * Δ))‖
          ≤ ‖Complex.cos ((-Real.pi * t : ℝ) : ℂ) * Real.cosh (Real.pi * Δ)‖ +
            ‖Complex.sin ((-Real.pi * t : ℝ) : ℂ) * (Complex.I * Real.sinh (Real.pi * Δ))‖ := norm_sub_le _ _
        _ ≤ 1 * Real.cosh (Real.pi * Δ) + 1 * |Real.sinh (Real.pi * Δ)| := by
            gcongr
            · rw [← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one _
            · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]
            · rw [← Complex.ofReal_sin, Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one _
            · rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        _ = Real.cosh (Real.pi * Δ) + Real.sinh (Real.pi * Δ) := by
            rw [one_mul, one_mul, abs_of_nonneg (Real.sinh_nonneg_iff.mpr (by positivity))]
        _ = Real.exp (Real.pi * Δ) := by rw [Real.cosh_eq, Real.sinh_eq]; ring
    have hsin_lb : ((1 - Real.exp (-2 * Real.pi)) / 2) * Real.exp (Real.pi * Δ) ≤
        ‖Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ))‖ := by
      rw [heq]
      have hs1 := sin_norm_ge_sinh (-Real.pi * t) (Real.pi * Δ)
      rw [abs_of_pos (by positivity)] at hs1
      exact (sinh_ge_mul_exp (by nlinarith [Real.pi_pos])).trans hs1
    rw [norm_div, norm_mul, norm_mul, norm_ofNat, norm_pow, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    calc 2 * Real.pi ^ 3 * ‖Complex.cos (Real.pi * ((-t : ℂ) + Complex.I * Δ))‖ /
          ‖Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ))‖ ^ 3
        ≤ 2 * Real.pi ^ 3 * Real.exp (Real.pi * Δ) /
            (((1 - Real.exp (-2 * Real.pi)) / 2) * Real.exp (Real.pi * Δ)) ^ 3 := by
          gcongr
      _ = (16 * Real.pi ^ 3 / (1 - Real.exp (-2 * Real.pi)) ^ 3) * Real.exp (-2 * Real.pi * Δ) := by
          rw [mul_pow, ← Real.exp_nat_mul, show (3 : ℕ) * (Real.pi * Δ) = 3 * Real.pi * Δ by push_cast; ring,
            show -2 * Real.pi * Δ = -(2 * Real.pi * Δ) by ring, Real.exp_neg,
            show 3 * Real.pi * Δ = 2 * Real.pi * Δ + Real.pi * Δ by ring, Real.exp_add]
          field_simp [h1m.ne', (Real.exp_pos (Real.pi * Δ)).ne', (Real.exp_pos (2 * Real.pi * Δ)).ne']
          ring
  have hmvt := (convex_Icc α β).norm_image_sub_le_of_norm_deriv_le hderiv hnorm_bd
    (Set.left_mem_Icc.mpr hαβ) (Set.right_mem_Icc.mpr hαβ)
  simpa [h, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hαβ)] using hmvt

lemma intervalIntegral_tsum_of_dominated {a b : ℝ} (hab : a ≤ b)
    (d : ℤ → ℝ → ℝ) (M : ℤ → ℝ) (hM_summ : Summable M)
    (hd_cont : ∀ n : ℤ, ContinuousOn (d n) (Set.Icc a b))
    (hd_bd : ∀ (n : ℤ) (t : ℝ), t ∈ Set.Icc a b → ‖d n t‖ ≤ M n) :
    ∫ t in a..b, (∑' n : ℤ, d n t) = ∑' n : ℤ, ∫ t in a..b, d n t := by
  have hd_summ_t : ∀ t ∈ Set.Icc a b, Summable (fun n : ℤ => d n t) := fun t ht =>
    Summable.of_norm_bounded hM_summ (fun n => hd_bd n t ht)
  let S : ℕ → ℝ → ℝ := fun N t => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), d n t
  have hS_meas : ∀ N : ℕ, AEStronglyMeasurable (S N) (volume.restrict (Set.Ioc a b)) := by
    intro N
    refine Finset.aestronglyMeasurable_sum _ fun n _ => ?_
    exact ((hd_cont n).mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hM_nonneg : ∀ n : ℤ, 0 ≤ M n := fun n => (norm_nonneg (d n a)).trans (hd_bd n a (Set.left_mem_Icc.mpr hab))
  have hS_bd : ∀ N : ℕ, ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖S N t‖ ≤ ∑' n : ℤ, M n := by
    intro N
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    calc ‖S N t‖ ≤ ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖d n t‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), M n :=
          Finset.sum_le_sum fun n _ => hd_bd n t (Set.Ioc_subset_Icc_self ht)
      _ ≤ ∑' n : ℤ, M n := hM_summ.sum_le_tsum _ (fun n _ => hM_nonneg n)
  have h_lim_t : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), Tendsto (fun N : ℕ => S N t) atTop (nhds (∑' n : ℤ, d n t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have h_has : HasSum (fun n : ℤ => d n t) (∑' n : ℤ, d n t) :=
      (hd_summ_t t (Set.Ioc_subset_Icc_self ht)).hasSum
    rw [HasSum, tendsto_atTop_nhds] at h_has ⊢
    intro U hU_mem hU_open
    obtain ⟨s, hs⟩ := h_has U hU_mem hU_open
    let M₀ : ℕ := s.sup (fun n : ℤ => n.natAbs)
    refine ⟨M₀, fun N hN => hs (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun n hn => ?_)⟩
    have h1 : n.natAbs ≤ M₀ := Finset.le_sup (f := fun n : ℤ => n.natAbs) hn
    simp only [Finset.mem_Icc] at *; omega
  have h_dom := tendsto_integral_of_dominated_convergence (fun _ => ∑' n : ℤ, M n)
    hS_meas (continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self) hS_bd h_lim_t
  have h_eq_N : ∀ N : ℕ, (∫ t in Set.Ioc a b, S N t) =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ∫ t in a..b, d n t := by
    intro N
    rw [← intervalIntegral.integral_of_le hab]
    exact intervalIntegral.integral_finset_sum fun n _ =>
      ((hd_cont n).mono (by rw [Set.uIcc_of_le hab])).intervalIntegrable
  have h_summ_int : Summable (fun n : ℤ => ∫ t in a..b, d n t) := by
    refine (hM_summ.mul_right (b - a)).of_norm_bounded fun n => ?_
    rw [intervalIntegral.integral_of_le hab]
    calc ‖∫ t in Set.Ioc a b, d n t‖ ≤ ∫ t in Set.Ioc a b, ‖d n t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Set.Ioc a b, M n := setIntegral_mono_on
          (((hd_cont n).mono Set.Ioc_subset_Icc_self).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self |>.norm)
          (continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self) measurableSet_Ioc
          (fun t ht => hd_bd n t (Set.Ioc_subset_Icc_self ht))
      _ = M n * (b - a) := by
          rw [setIntegral_const, Real.volume_real_Ioc_of_le hab, smul_eq_mul, mul_comm]
  have h_lim_sum : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ∫ t in a..b, d n t)
      atTop (nhds (∑' n : ℤ, ∫ t in a..b, d n t)) := by
    have h_has := h_summ_int.hasSum
    rw [HasSum, tendsto_atTop_nhds] at h_has ⊢
    intro U hU_mem hU_open
    obtain ⟨s, hs⟩ := h_has U hU_mem hU_open
    let M₀ : ℕ := s.sup (fun n : ℤ => n.natAbs)
    refine ⟨M₀, fun N hN => hs (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun n hn => ?_)⟩
    have h1 : n.natAbs ≤ M₀ := Finset.le_sup (f := fun n : ℤ => n.natAbs) hn
    simp only [Finset.mem_Icc] at *; omega
  simp_rw [h_eq_N] at h_dom
  rw [intervalIntegral.integral_of_le hab]
  exact tendsto_nhds_unique h_dom h_lim_sum

/-- **Lemma 3.1** (Optimal lattice shift `α_Δ ∈ (0, 1)`). -/
set_option maxHeartbeats 800000 in
theorem optimal_lattice_shift (θ : ℝ) (hθ : |θ| < Real.pi / 2) :
    ∃ (Δ₁ C_α : ℝ), Δ₁ ≥ 1 ∧ C_α > 0 ∧
      ∀ Δ ≥ Δ₁, ∃! α : ℝ, α ∈ Set.Ioo (0 : ℝ) 1 ∧
        Summable (fun n : ℤ => rescaledFDeriv θ Δ (n + α)) ∧
        ∑' n : ℤ, rescaledFDeriv θ Δ (n + α) = 0 ∧
        |α - (1 / 2 - θ / Real.pi)| ≤ C_α * Δ * Real.exp (-2 * Real.pi * Δ) := by
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  let α_star : ℝ := 1 / 2 - θ / Real.pi
  have hα_star : α_star ∈ Set.Ioo (0 : ℝ) 1 := by
    have := abs_lt.mp hθ
    constructor
    · dsimp only [α_star]; rw [sub_pos, div_lt_iff₀ Real.pi_pos]; linarith
    · dsimp only [α_star]; rw [sub_lt_iff_lt_add]; linarith [show -(1 / 2 : ℝ) < θ / Real.pi by rw [lt_div_iff₀ Real.pi_pos]; linarith]
  let δ_star : ℝ := min (α_star / 2) ((1 - α_star) / 2)
  have hδ_pos : 0 < δ_star := lt_min (by linarith [hα_star.1]) (by linarith [hα_star.2])
  let C_sin : ℝ := 4 * Real.pi ^ 2 / (1 - Real.exp (-2 * Real.pi)) ^ 2
  let C_lip : ℝ := 16 * Real.pi ^ 3 / (1 - Real.exp (-2 * Real.pi)) ^ 3
  let C_lor : ℝ := 2 * Real.pi / (1 - Real.exp (-2 * Real.pi))
  let C_tot : ℝ := C_sin + C_lor + C_sin + 1
  let C_α : ℝ := C_tot / (2 * Real.pi) + 1
  have hC_sin_pos : 0 < C_sin := by
    have : 0 < 1 - Real.exp (-2 * Real.pi) := by linarith [Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos] : -2 * Real.pi < 0)]
    positivity
  have hC_lip_pos : 0 < C_lip := by
    have : 0 < 1 - Real.exp (-2 * Real.pi) := by linarith [Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos] : -2 * Real.pi < 0)]
    positivity
  have hC_lor_pos : 0 < C_lor := by
    have : 0 < 1 - Real.exp (-2 * Real.pi) := by linarith [Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos] : -2 * Real.pi < 0)]
    positivity
  have hC_tot_pos : 0 < C_tot := by positivity
  have hC_α_pos : 0 < C_α := by positivity
  let K_big : ℝ := max ((C_sin + C_lip) / (Real.cos θ * Real.pi ^ 2 / 2))
    (max (C_α / min δ_star (1 / 4)) 1)
  let Δ₁ : ℝ := max 1 (K_big / Real.pi + 1)
  have hΔ₁_ge_1 : 1 ≤ Δ₁ := le_max_left _ _
  refine ⟨Δ₁, C_α, hΔ₁_ge_1, hC_α_pos, fun Δ hΔ => ?_⟩
  have hΔ_ge_1 : 1 ≤ Δ := le_trans hΔ₁_ge_1 hΔ
  have hΔ_pos : 0 < Δ := by linarith
  have h_small_exp : Δ * Real.exp (-2 * Real.pi * Δ) < 1 / K_big := by
    have h2 : K_big * Δ < Real.exp (Real.pi * Δ) := by
      have hK_lt : K_big < Real.pi * Δ := by
        have h1 : K_big / Real.pi + 1 ≤ Δ := le_trans (le_max_right _ _) hΔ
        have h3 := (div_le_iff₀ Real.pi_pos).mp (by linarith : K_big / Real.pi ≤ Δ - 1)
        linarith [Real.pi_pos]
      have h_lin : Real.pi * Δ ≤ Real.exp (Real.pi * Δ) := by linarith [Real.add_one_le_exp (Real.pi * Δ)]
      nlinarith
    have h_exp2 : Real.exp (-2 * Real.pi * Δ) = (Real.exp (Real.pi * Δ) * Real.exp (Real.pi * Δ))⁻¹ := by
      rw [← Real.exp_add, show Real.pi * Δ + Real.pi * Δ = 2 * Real.pi * Δ by ring, ← Real.exp_neg]
      congr 1; ring
    have hK_pos : 0 < K_big := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) (le_max_right _ _))
    rw [h_exp2, ← div_eq_mul_inv, div_lt_div_iff₀ (by positivity) hK_pos, one_mul]
    have h_pi_1 : 1 < Real.exp (Real.pi * Δ) := Real.one_lt_exp_iff.mpr (by positivity)
    nlinarith
  have h_r_le : C_α * Δ * Real.exp (-2 * Real.pi * Δ) ≤ min δ_star (1 / 4) := by
    have hK : C_α / min δ_star (1 / 4) ≤ K_big := le_trans (le_max_left _ _) (le_max_right _ _)
    have hmin_pos : 0 < min δ_star (1 / 4) := lt_min hδ_pos (by norm_num)
    have hK_pos : 0 < K_big := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) (le_max_right _ _))
    calc C_α * Δ * Real.exp (-2 * Real.pi * Δ)
        = C_α * (Δ * Real.exp (-2 * Real.pi * Δ)) := by ring
      _ ≤ C_α * (1 / K_big) := by gcongr; exact h_small_exp.le
      _ ≤ min δ_star (1 / 4) := by
          rw [mul_one_div, div_le_iff₀ hK_pos]
          exact (div_le_iff₀ hmin_pos).mp hK
  have h_mono_bd : (C_sin + C_lip * Δ) * Real.exp (-2 * Real.pi * Δ) < Real.cos θ * Real.pi ^ 2 / 2 := by
    have hK : (C_sin + C_lip) / (Real.cos θ * Real.pi ^ 2 / 2) ≤ K_big := le_max_left _ _
    have hK_pos : 0 < K_big := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) (le_max_right _ _))
    calc (C_sin + C_lip * Δ) * Real.exp (-2 * Real.pi * Δ)
        ≤ (C_sin + C_lip) * (Δ * Real.exp (-2 * Real.pi * Δ)) := by nlinarith [Real.exp_pos (-2 * Real.pi * Δ)]
      _ < (C_sin + C_lip) * (1 / K_big) := by gcongr
      _ ≤ Real.cos θ * Real.pi ^ 2 / 2 := by
          rw [mul_one_div, div_le_iff₀ hK_pos]
          exact (div_le_iff₀ (by positivity : 0 < Real.cos θ * Real.pi ^ 2 / 2)).mp hK
  let f₁ : ℝ → ℝ := fun y => 1 / y - y / (y ^ 2 + Δ ^ 2)
  let f₂ : ℝ → ℝ := fun y => 2 * Δ ^ 3 / (y ^ 2 + Δ ^ 2) ^ 2
  let g₁ : ℝ → ℝ := fun α => ∑' n : ℤ, f₁ (n + α)
  let g₂ : ℝ → ℝ := fun α => ∑' n : ℤ, f₂ (n + α)
  let g : ℝ → ℝ := fun α => Real.cos θ * g₁ α - Real.sin θ * g₂ α
  have h_sin_ne : ∀ α ∈ Set.Ioo (0 : ℝ) 1, Real.sin (Real.pi * α) ≠ 0 := by
    intro α hα
    exact (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos, hα.2])).ne'
  have h_summ_1 : ∀ α ∈ Set.Ioo (0 : ℝ) 1, Summable (fun n : ℤ => f₁ (n + α)) := by
    intro α hα
    have hs := (tsum_inv_sub_real_sq (-α) (by rw [mul_neg, Real.sin_neg, neg_ne_zero]; exact h_sin_ne α hα)).1
    have hmin_pos : 0 < min α (1 - α) := lt_min hα.1 (by linarith [hα.2])
    refine (hs.mul_left (Δ ^ 2 / min α (1 - α))).of_norm_bounded (fun n => ?_)
    have hne : (n : ℝ) + α ≠ 0 := by
      intro h
      rcases le_or_gt n (-1) with hn | hn
      · have : (n : ℝ) ≤ -1 := by exact_mod_cast hn; linarith [hα.2]
      · have : (0 : ℝ) ≤ n := by exact_mod_cast (by omega : 0 ≤ n); linarith [hα.1]
    have h_abs_ge : min α (1 - α) ≤ |(n : ℝ) + α| := by
      rcases le_or_gt n (-1) with hn | hn
      · have : (n : ℝ) ≤ -1 := by exact_mod_cast hn
        rw [abs_of_neg (by linarith [hα.2])]; exact le_trans (min_le_right _ _) (by linarith)
      · have : (0 : ℝ) ≤ n := by exact_mod_cast (by omega : 0 ≤ n)
        rw [abs_of_pos (by linarith [hα.1])]; exact le_trans (min_le_left _ _) (by linarith)
    have hf1_eq : f₁ (n + α) = Δ ^ 2 / ((n + α) * ((n + α) ^ 2 + Δ ^ 2)) := by
      dsimp only [f₁]; field_simp [hne]; ring
    rw [hf1_eq, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (sq_pos_of_pos hΔ_pos),
      abs_of_pos (by positivity : 0 < (n + α) ^ 2 + Δ ^ 2)]
    have h_eq_inv : 1 / (-α - n) ^ 2 = 1 / ((n : ℝ) + α) ^ 2 := by congr 1; ring
    calc Δ ^ 2 / (|(n : ℝ) + α| * ((n + α) ^ 2 + Δ ^ 2))
        ≤ Δ ^ 2 / (min α (1 - α) * (n + α) ^ 2) := by
          gcongr
          exact mul_le_mul_of_nonneg_left (by linarith [sq_pos_of_pos hΔ_pos]) hmin_pos.le
      _ = Δ ^ 2 / min α (1 - α) * (1 / (-α - n) ^ 2) := by
          rw [h_eq_inv]; ring
  have h_summ_2 : ∀ α : ℝ, Summable (fun n : ℤ => f₂ (n + α)) := by
    intro α
    have hs := (lorentz_tsum_bound Δ α hΔ_ge_1).1
    refine (hs.mul_left 2).of_norm_bounded (fun n => ?_)
    dsimp only [f₂]
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h1 : Δ ^ 2 ≤ (n + α) ^ 2 + Δ ^ 2 := by linarith [sq_nonneg ((n : ℝ) + α)]
    calc 2 * Δ ^ 3 / ((n + α) ^ 2 + Δ ^ 2) ^ 2
        = (2 * Δ / ((n + α) ^ 2 + Δ ^ 2)) * (Δ ^ 2 / ((n + α) ^ 2 + Δ ^ 2)) := by ring
      _ ≤ (2 * Δ / ((n + α) ^ 2 + Δ ^ 2)) * 1 := by
          gcongr; exact div_le_one_of_le₀ h1 (by positivity)
      _ = 2 * (Δ / ((n + α) ^ 2 + Δ ^ 2)) := by ring
  have h_summ_all : ∀ α ∈ Set.Ioo (0 : ℝ) 1, Summable (fun n : ℤ => rescaledFDeriv θ Δ (n + α)) := by
    intro α hα
    have heq : (fun n : ℤ => rescaledFDeriv θ Δ (n + α)) =
        fun n => Real.cos θ * f₁ (n + α) - Real.sin θ * f₂ (n + α) := by
      ext n; unfold rescaledFDeriv; dsimp only [f₁, f₂]; ring
    rw [heq]
    exact ((h_summ_1 α hα).mul_left _).sub ((h_summ_2 α).mul_left _)
  have hg_eq : ∀ α ∈ Set.Ioo (0 : ℝ) 1, ∑' n : ℤ, rescaledFDeriv θ Δ (n + α) = g α := by
    intro α hα
    have heq : (fun n : ℤ => rescaledFDeriv θ Δ (n + α)) =
        fun n => Real.cos θ * f₁ (n + α) - Real.sin θ * f₂ (n + α) := by
      ext n; unfold rescaledFDeriv; dsimp only [f₁, f₂]; ring
    rw [heq, ((h_summ_1 α hα).mul_left _).tsum_sub ((h_summ_2 α).mul_left _),
      tsum_mul_left, tsum_mul_left]
  have hg1_half : g₁ (1 / 2) = 0 := by
    dsimp only [g₁]
    let e : ℤ ≃ ℤ :=
      { toFun := fun n => -n - 1
        invFun := fun n => -n - 1
        left_inv := fun n => by omega
        right_inv := fun n => by omega }
    have heq : g₁ (1 / 2) = -g₁ (1 / 2) := by
      calc g₁ (1 / 2) = ∑' n : ℤ, f₁ ((e n : ℝ) + 1 / 2) := (e.tsum_eq (fun n : ℤ => f₁ (n + 1 / 2))).symm
        _ = ∑' n : ℤ, -f₁ (n + 1 / 2) := by
            congr 1; ext n; dsimp only [e, f₁]; push_cast
            have : -(n : ℝ) - 1 + 1 / 2 = -((n : ℝ) + 1 / 2) := by ring
            rw [this]; ring
        _ = -g₁ (1 / 2) := tsum_neg
    linarith
  have hg1_diff : ∀ {a b : ℝ}, a ∈ Set.Ioo (0 : ℝ) 1 → b ∈ Set.Ioo (0 : ℝ) 1 → a ≤ b →
      g₁ b - g₁ a = -(Real.pi ^ 2 * ∫ t in a..b, 1 / Real.sin (Real.pi * t) ^ 2) +
        ∫ t in a..b, ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 2).re := by
    intro a b ha hb hab
    have h_ab_sub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) 1 :=
      fun t ht => ⟨lt_of_lt_of_le ha.1 ht.1, lt_of_le_of_lt ht.2 hb.2⟩
    let d₁ : ℤ → ℝ → ℝ := fun n t => -1 / ((n : ℝ) + t) ^ 2 + (((n : ℝ) + t) ^ 2 - Δ ^ 2) / (((n : ℝ) + t) ^ 2 + Δ ^ 2) ^ 2
    have hd_cont : ∀ n : ℤ, ContinuousOn (d₁ n) (Set.Icc a b) := by
      intro n
      refine ContinuousOn.add ?_ ?_
      · refine continuousOn_const.div (ContinuousOn.pow (continuousOn_const.add continuousOn_id) 2) ?_
        intro t ht
        have ht_mem := h_ab_sub ht
        have hne : (n : ℝ) + t ≠ 0 := by
          intro h
          rcases le_or_gt n (-1) with hn | hn
          · have : (n : ℝ) ≤ -1 := by exact_mod_cast hn; linarith [ht_mem.2]
          · have : (0 : ℝ) ≤ n := by exact_mod_cast (by omega : 0 ≤ n); linarith [ht_mem.1]
        exact pow_ne_zero 2 hne
      · refine ContinuousOn.div ?_ (ContinuousOn.pow ?_ 2) (fun t _ => by positivity)
        · exact (ContinuousOn.pow (continuousOn_const.add continuousOn_id) 2).sub continuousOn_const
        · exact (ContinuousOn.pow (continuousOn_const.add continuousOn_id) 2).add continuousOn_const
    have hd_ftc : ∀ n : ℤ, ∫ t in a..b, d₁ n t = f₁ (n + b) - f₁ (n + a) := by
      intro n
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => f₁ (n + t))
      · intro t ht
        have ht_mem := h_ab_sub (Set.uIcc_of_le hab ▸ ht)
        have hne : (n : ℝ) + t ≠ 0 := by
          intro h
          rcases le_or_gt n (-1) with hn | hn
          · have : (n : ℝ) ≤ -1 := by exact_mod_cast hn; linarith [ht_mem.2]
          · have : (0 : ℝ) ≤ n := by exact_mod_cast (by omega : 0 ≤ n); linarith [ht_mem.1]
        have h1 : HasDerivAt (fun s : ℝ => 1 / ((n : ℝ) + s)) (-1 / ((n : ℝ) + t) ^ 2) t := by
          have := ((hasDerivAt_id t).const_add (n : ℝ)).inv hne
          convert this using 1; · ext s; simp [one_div]
          · ring
        have h2 : HasDerivAt (fun s : ℝ => ((n : ℝ) + s) / (((n : ℝ) + s) ^ 2 + Δ ^ 2))
            ((((n : ℝ) + t) ^ 2 + Δ ^ 2 - 2 * ((n : ℝ) + t) ^ 2) / (((n : ℝ) + t) ^ 2 + Δ ^ 2) ^ 2) t := by
          have ha' : HasDerivAt (fun s : ℝ => (n : ℝ) + s) 1 t := by
            simpa using (hasDerivAt_id t).const_add (n : ℝ)
          have hb' : HasDerivAt (fun s : ℝ => ((n : ℝ) + s) ^ 2 + Δ ^ 2) (2 * ((n : ℝ) + t)) t := by
            simpa using (ha'.pow 2).add_const (Δ ^ 2)
          convert ha'.div hb' (by positivity : ((n : ℝ) + t) ^ 2 + Δ ^ 2 ≠ 0) using 1
          ring
        convert h1.sub h2 using 1; dsimp only [d₁]; ring
      · exact (hd_cont n).mono (by rw [Set.uIcc_of_le hab]) |>.intervalIntegrable
    have h_min_pos : 0 < min a (1 - b) := lt_min ha.1 (by linarith [hb.2])
    let δ₀ := min a (1 - b)
    have h_int_u : ∀ n : ℤ, ∀ t ∈ Set.Icc a b, δ₀ ≤ |(n : ℝ) + t| := by
      intro n t ht
      rcases le_or_gt n (-1) with hn | hn
      · have : (n : ℝ) ≤ -1 := by exact_mod_cast hn
        rw [abs_of_neg (by linarith [ht.2, hb.2])]; exact le_trans (min_le_right _ _) (by linarith [ht.2])
      · have : (0 : ℝ) ≤ n := by exact_mod_cast (by omega : 0 ≤ n)
        rw [abs_of_pos (by linarith [ht.1, ha.1])]; exact le_trans (min_le_left _ _) (by linarith [ht.1])
    let M : ℤ → ℝ := fun n => (1 / δ₀ ^ 2 + 2) * 8 * (1 + |(n : ℝ)|) ^ (-2 : ℝ)
    have hM_summ : Summable M := summable_inv_one_add_sq_int.mul_left ((1 / δ₀ ^ 2 + 2) * 8)
    have hM_bd : ∀ (n : ℤ) (t : ℝ), t ∈ Set.Icc a b → ‖d₁ n t‖ ≤ M n := by
      intro n t ht
      have h1 : 1 + |(n : ℝ)| ≤ 2 * (1 + |(n : ℝ) + t|) := by
        have ht_le : |t| ≤ 1 := by
          have := h_ab_sub ht
          rw [abs_le]; constructor <;> linarith [this.1, this.2]
        have : |(n : ℝ)| ≤ |(n : ℝ) + t| + |t| := by
          have h := abs_sub ((n : ℝ) + t) t
          simpa using h
        linarith [abs_nonneg ((n : ℝ) + t)]
      have h2 : (1 + |(n : ℝ) + t|) ^ 2 ≤ 2 * (1 + ((n : ℝ) + t) ^ 2) := by
        have : (1 - |(n : ℝ) + t|) ^ 2 ≥ 0 := sq_nonneg _; nlinarith [sq_abs ((n : ℝ) + t)]
      have h3 : 1 / ((n : ℝ) + t) ^ 2 ≤ (1 / δ₀ ^ 2 + 1) / (1 + ((n : ℝ) + t) ^ 2) := by
        have hdt : δ₀ ^ 2 ≤ ((n : ℝ) + t) ^ 2 := by
          rw [← sq_abs ((n : ℝ) + t)]; exact sq_le_sq' (by linarith [h_min_pos, abs_nonneg ((n : ℝ) + t)]) (h_int_u n t ht)
        have hpos : 0 < ((n : ℝ) + t) ^ 2 := lt_of_lt_of_le (sq_pos_of_pos h_min_pos) hdt
        rw [div_le_div_iff₀ hpos (by positivity)]
        have : 1 ≤ (1 / δ₀ ^ 2) * ((n : ℝ) + t) ^ 2 := by
          rw [one_div_mul_eq_div, one_le_div (sq_pos_of_pos h_min_pos)]; exact hdt
        nlinarith
      have h4 : |(((n : ℝ) + t) ^ 2 - Δ ^ 2) / (((n : ℝ) + t) ^ 2 + Δ ^ 2) ^ 2| ≤ 1 / (1 + ((n : ℝ) + t) ^ 2) := by
        rw [abs_div, abs_of_pos (by positivity : 0 < (((n : ℝ) + t) ^ 2 + Δ ^ 2) ^ 2)]
        have hnum : |((n : ℝ) + t) ^ 2 - Δ ^ 2| ≤ ((n : ℝ) + t) ^ 2 + Δ ^ 2 := by
          rw [abs_le]; constructor <;> linarith [sq_nonneg ((n : ℝ) + t), sq_nonneg Δ]
        have hden : 1 + ((n : ℝ) + t) ^ 2 ≤ ((n : ℝ) + t) ^ 2 + Δ ^ 2 := by nlinarith
        calc |((n : ℝ) + t) ^ 2 - Δ ^ 2| / (((n : ℝ) + t) ^ 2 + Δ ^ 2) ^ 2
            ≤ (((n : ℝ) + t) ^ 2 + Δ ^ 2) / (((n : ℝ) + t) ^ 2 + Δ ^ 2) ^ 2 := by gcongr
          _ = 1 / (((n : ℝ) + t) ^ 2 + Δ ^ 2) := by
              have hp : ((n : ℝ) + t) ^ 2 + Δ ^ 2 ≠ 0 := by positivity
              field_simp [hp]
          _ ≤ 1 / (1 + ((n : ℝ) + t) ^ 2) := one_div_le_one_div_of_le (by positivity) hden
      have hd_norm : ‖d₁ n t‖ ≤ (1 / δ₀ ^ 2 + 2) / (1 + ((n : ℝ) + t) ^ 2) := by
        dsimp only [d₁]; rw [Real.norm_eq_abs]
        refine (abs_add_le _ _).trans ?_
        have hneg : |-1 / ((n : ℝ) + t) ^ 2| = 1 / ((n : ℝ) + t) ^ 2 := by
          rw [abs_div, abs_neg, abs_one, abs_of_nonneg (sq_nonneg _)]
        linarith [show (1 / δ₀ ^ 2 + 1) / (1 + ((n : ℝ) + t) ^ 2) + 1 / (1 + ((n : ℝ) + t) ^ 2) = (1 / δ₀ ^ 2 + 2) / (1 + ((n : ℝ) + t) ^ 2) by ring]
      have hpow_eq : (1 + |(n : ℝ)|) ^ (-2 : ℝ) = 1 / (1 + |(n : ℝ)|) ^ 2 := by
        have hpos : 0 < 1 + |(n : ℝ)| := by positivity
        rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hpos.le, Real.rpow_natCast, one_div]
      dsimp only [M]
      rw [hpow_eq]
      have h_inv_le : 1 / (1 + ((n : ℝ) + t) ^ 2) ≤ 8 / (1 + |(n : ℝ)|) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hsq_le : (1 + |(n : ℝ)|) ^ 2 ≤ (2 * (1 + |(n : ℝ) + t|)) ^ 2 := sq_le_sq' (by linarith [abs_nonneg (n : ℝ), abs_nonneg ((n : ℝ) + t)]) h1
        have : (1 + |(n : ℝ)|) ^ 2 ≤ 4 * (1 + |(n : ℝ) + t|) ^ 2 := by linarith
        linarith
      calc ‖d₁ n t‖ ≤ (1 / δ₀ ^ 2 + 2) * (1 / (1 + ((n : ℝ) + t) ^ 2)) := by
            rw [← mul_div_assoc, mul_one]; exact hd_norm
        _ ≤ (1 / δ₀ ^ 2 + 2) * (8 / (1 + |(n : ℝ)|) ^ 2) := by gcongr
        _ = (1 / δ₀ ^ 2 + 2) * 8 * (1 / (1 + |(n : ℝ)|) ^ 2) := by ring
    have h_tsum_eq := intervalIntegral_tsum_of_dominated hab d₁ M hM_summ hd_cont hM_bd
    have h_rhs : ∑' n : ℤ, ∫ t in a..b, d₁ n t = g₁ b - g₁ a := by
      simp_rw [hd_ftc]
      exact (h_summ_1 b hb).tsum_sub (h_summ_1 a ha)
    rw [h_rhs] at h_tsum_eq
    rw [← h_tsum_eq]
    have h_inner : ∀ t ∈ Set.Icc a b, ∑' n : ℤ, d₁ n t =
        -(Real.pi ^ 2 * (1 / Real.sin (Real.pi * t) ^ 2)) +
          ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 2).re := by
      intro t ht
      have ht_mem := h_ab_sub ht
      have hs1 := tsum_inv_sub_real_sq (-t) (by rw [mul_neg, Real.sin_neg, neg_ne_zero]; exact h_sin_ne t ht_mem)
      have hs1' : Summable (fun n : ℤ => -1 / ((n : ℝ) + t) ^ 2) := by
        refine (hs1.1.neg).congr fun n => ?_; ring
      have hs2 := tsum_inv_sub_I_sq ((-t : ℂ) + Complex.I * Δ) (by simp; positivity)
      have hs2' : Summable (fun n : ℤ => (((n : ℝ) + t) ^ 2 - Δ ^ 2) / (((n : ℝ) + t) ^ 2 + Δ ^ 2) ^ 2) := by
        refine (Complex.reCLM.summable hs2.1).congr fun n => ?_
        have heq : ((-t : ℂ) + Complex.I * Δ) - n = -((n + t : ℝ) : ℂ) + Complex.I * Δ := by
          push_cast; ring
        dsimp only [Complex.reCLM_apply]
        rw [heq, one_div, Complex.inv_re, Complex.normSq_apply]
        have hsq : (-((n + t : ℝ) : ℂ) + Complex.I * Δ) ^ 2 =
            (((n + t : ℝ) ^ 2 - Δ ^ 2 : ℝ) : ℂ) - ((2 * (n + t : ℝ) * Δ : ℝ) : ℂ) * Complex.I := by
          push_cast; ring_nf; simp [Complex.I_sq]; ring
        rw [hsq]
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.sub_im, Complex.mul_im, zero_sub]
        have hden : ((n + t : ℝ) ^ 2 - Δ ^ 2) ^ 2 + (-(2 * (n + t : ℝ) * Δ)) ^ 2 =
            ((n + t : ℝ) ^ 2 + Δ ^ 2) ^ 2 := by ring
        rw [hden]
      rw [hs1'.tsum_add hs2']
      have h_t1 : (∑' n : ℤ, -1 / ((n : ℝ) + t) ^ 2) = -(Real.pi ^ 2 * (1 / Real.sin (Real.pi * t) ^ 2)) := by
        have heq : (fun n : ℤ => -1 / ((n : ℝ) + t) ^ 2) = fun n => -(1 / (-t - n) ^ 2) := by
          ext n; ring
        rw [heq, tsum_neg, hs1.2]
        rw [mul_neg, Real.sin_neg, neg_sq]; ring
      have h_t2 : (∑' n : ℤ, (((n : ℝ) + t) ^ 2 - Δ ^ 2) / (((n : ℝ) + t) ^ 2 + Δ ^ 2) ^ 2) =
          ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 2).re := by
        rw [← hs2.2, Complex.re_tsum hs2.1]
        congr 1; ext n
        have heq : ((-t : ℂ) + Complex.I * Δ) - n = -((n + t : ℝ) : ℂ) + Complex.I * Δ := by
          push_cast; ring
        rw [heq, one_div, Complex.inv_re, Complex.normSq_apply]
        have hsq : (-((n + t : ℝ) : ℂ) + Complex.I * Δ) ^ 2 =
            (((n + t : ℝ) ^ 2 - Δ ^ 2 : ℝ) : ℂ) - ((2 * (n + t : ℝ) * Δ : ℝ) : ℂ) * Complex.I := by
          push_cast; ring_nf; simp [Complex.I_sq]; ring
        rw [hsq]
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.sub_im, Complex.mul_im, zero_sub]
        have hden : ((n + t : ℝ) ^ 2 - Δ ^ 2) ^ 2 + (-(2 * (n + t : ℝ) * Δ)) ^ 2 =
            ((n + t : ℝ) ^ 2 + Δ ^ 2) ^ 2 := by ring
        rw [hden]
      rw [h_t1, h_t2]
    have h_int_congr : (∫ t in a..b, ∑' n : ℤ, d₁ n t) =
        ∫ t in a..b, (-(Real.pi ^ 2 * (1 / Real.sin (Real.pi * t) ^ 2)) +
          ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 2).re) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      exact h_inner t (Set.uIcc_of_le hab ▸ ht)
    have h_int1 : IntervalIntegrable (fun t => -(Real.pi ^ 2 * (1 / Real.sin (Real.pi * t) ^ 2))) volume a b := by
      apply ContinuousOn.intervalIntegrable
      refine (continuousOn_const.mul (continuousOn_const.div (ContinuousOn.pow (Real.continuous_sin.continuousOn.comp
        (continuousOn_const.mul continuousOn_id) (fun _ _ => Set.mem_univ _)) 2) ?_)).neg
      intro t ht; exact pow_ne_zero 2 (h_sin_ne t (h_ab_sub (Set.uIcc_of_le hab ▸ ht)))
    have h_int2 : IntervalIntegrable (fun t => ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 2).re) volume a b := by
      apply ContinuousOn.intervalIntegrable
      refine Complex.continuous_re.continuousOn.comp ?_ (fun _ _ => Set.mem_univ _)
      refine continuousOn_const.div (ContinuousOn.pow (Complex.continuous_sin.continuousOn.comp ?_ (fun _ _ => Set.mem_univ _)) 2) ?_
      · exact continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.neg.add continuousOn_const)
      · intro t _
        have hs1 : 0 < ((1 - Real.exp (-2 * Real.pi)) / 2) * Real.exp (Real.pi * Δ) := by positivity
        have heq : (Real.pi : ℂ) * ((-t : ℂ) + Complex.I * Δ) = ((-Real.pi * t : ℝ) : ℂ) + Complex.I * (Real.pi * Δ) := by
          push_cast; ring
        have hs2 := sin_norm_ge_sinh (-Real.pi * t) (Real.pi * Δ)
        rw [abs_of_pos (by positivity)] at hs2
        have hs3 := (sinh_ge_mul_exp (by nlinarith [Real.pi_pos])).trans hs2
        rw [← heq] at hs3
        exact pow_ne_zero 2 (norm_ne_zero_iff.mp (by linarith))
    rw [h_int_congr, intervalIntegral.integral_add h_int1 h_int2, intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul]
  have hg1_approx : ∀ α ∈ Set.Ioo (0 : ℝ) 1,
      |g₁ α - Real.pi * Real.cos (Real.pi * α) / Real.sin (Real.pi * α)| ≤ C_sin * Real.exp (-2 * Real.pi * Δ) := by
    intro α hα
    have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have h_cot_int : ∀ {a b : ℝ}, a ∈ Set.Ioo (0 : ℝ) 1 → b ∈ Set.Ioo (0 : ℝ) 1 → a ≤ b →
        -(Real.pi ^ 2 * ∫ t in a..b, 1 / Real.sin (Real.pi * t) ^ 2) =
          Real.pi * Real.cos (Real.pi * b) / Real.sin (Real.pi * b) -
            Real.pi * Real.cos (Real.pi * a) / Real.sin (Real.pi * a) := by
      intro a b ha hb hab
      have h_ab_sub : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) 1 := by
        rw [Set.uIcc_of_le hab]; exact fun t ht => ⟨lt_of_lt_of_le ha.1 ht.1, lt_of_le_of_lt ht.2 hb.2⟩
      have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt
          (fun s => Real.pi * Real.cos (Real.pi * s) / Real.sin (Real.pi * s))
          (-(Real.pi ^ 2 * (1 / Real.sin (Real.pi * t) ^ 2))) t := by
        intro t ht
        have hne := h_sin_ne t (h_ab_sub ht)
        have h1 : HasDerivAt (fun s => Real.pi * Real.cos (Real.pi * s))
            (Real.pi * (-Real.sin (Real.pi * t) * Real.pi)) t := by
          have := ((Real.hasDerivAt_cos (Real.pi * t)).comp t ((hasDerivAt_id t).const_mul Real.pi)).const_mul Real.pi
          convert this using 1; ring
        have h2 : HasDerivAt (fun s => Real.sin (Real.pi * s)) (Real.cos (Real.pi * t) * Real.pi) t :=
          (Real.hasDerivAt_sin (Real.pi * t)).comp t ((hasDerivAt_id t).const_mul Real.pi)
        convert h1.div h2 hne using 1
        have hsc := Real.sin_sq_add_cos_sq (Real.pi * t)
        field_simp [hne]; nlinarith
      have h_int : IntervalIntegrable (fun t => -(Real.pi ^ 2 * (1 / Real.sin (Real.pi * t) ^ 2))) volume a b := by
        apply ContinuousOn.intervalIntegrable
        refine (continuousOn_const.mul (continuousOn_const.div (ContinuousOn.pow (Real.continuous_sin.continuousOn.comp
          (continuousOn_const.mul continuousOn_id) (fun _ _ => Set.mem_univ _)) 2) ?_)).neg
        intro t ht; exact pow_ne_zero 2 (h_sin_ne t (h_ab_sub ht))
      have hres := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv h_int
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hres
      exact hres
    have h_bd_int : ∀ {a b : ℝ}, a ≤ b → b - a ≤ 1 →
        |∫ t in a..b, ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 2).re| ≤
          C_sin * Real.exp (-2 * Real.pi * Δ) := by
      intro a b hab hba
      rw [intervalIntegral.integral_of_le hab, ← Real.norm_eq_abs]
      calc ‖∫ t in Set.Ioc a b, ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 2).re‖
          ≤ ∫ t in Set.Ioc a b, ‖((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 2).re‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ t in Set.Ioc a b, C_sin * Real.exp (-2 * Real.pi * Δ) := by
            refine setIntegral_mono_on ?_ (continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
              measurableSet_Ioc fun t _ => ?_
            · refine ((continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self) :
                IntegrableOn (fun _ => C_sin * Real.exp (-2 * Real.pi * Δ)) (Set.Ioc a b)).mono' ?_ ?_
              · refine Continuous.aestronglyMeasurable (Continuous.norm (Complex.continuous_re.comp ?_))
                refine continuous_const.div (Continuous.pow (Complex.continuous_sin.comp (by fun_prop)) 2) fun t => ?_
                have h1m : 0 < 1 - Real.exp (-2 * Real.pi) := by
                  linarith [Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos] : -2 * Real.pi < 0)]
                have hs1 : 0 < ((1 - Real.exp (-2 * Real.pi)) / 2) * Real.exp (Real.pi * Δ) := by positivity
                have hs2 := sin_norm_ge_sinh (-Real.pi * t) (Real.pi * Δ)
                rw [abs_of_pos (by positivity)] at hs2
                have hs3 := (sinh_ge_mul_exp (by nlinarith [Real.pi_pos])).trans hs2
                have hnorm_pos : 0 < ‖Complex.sin ((Real.pi : ℂ) * ((-t : ℂ) + Complex.I * Δ))‖ := by
                  rw [show (Real.pi : ℂ) * ((-t : ℂ) + Complex.I * Δ) = ((-Real.pi * t : ℝ) : ℂ) + Complex.I * ((Real.pi * Δ : ℝ) : ℂ) by push_cast; ring]
                  linarith
                exact pow_ne_zero 2 (norm_ne_zero_iff.mp hnorm_pos.ne')
              · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t _
                rw [Real.norm_eq_abs, abs_norm, Real.norm_eq_abs]
                exact (Complex.abs_re_le_norm _).trans (complex_inv_sin_sq_bound Δ hΔ_ge_1 t)
            · rw [Real.norm_eq_abs]
              exact (Complex.abs_re_le_norm _).trans (complex_inv_sin_sq_bound Δ hΔ_ge_1 t)
        _ = C_sin * Real.exp (-2 * Real.pi * Δ) * (b - a) := by
            rw [setIntegral_const, Real.volume_real_Ioc_of_le hab, smul_eq_mul, mul_comm]
        _ ≤ C_sin * Real.exp (-2 * Real.pi * Δ) * 1 := by gcongr
        _ = C_sin * Real.exp (-2 * Real.pi * Δ) := mul_one _
    rcases le_total (1 / 2 : ℝ) α with hle | hle
    · have hd := hg1_diff hhalf hα hle
      rw [hg1_half, sub_zero, h_cot_int hhalf hα hle, show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring,
        Real.cos_pi_div_two, mul_zero, zero_div, sub_zero] at hd
      rw [hd, add_sub_cancel_left]
      exact h_bd_int hle (by linarith [hα.2])
    · have hd := hg1_diff hα hhalf hle
      rw [hg1_half, zero_sub, h_cot_int hα hhalf hle, show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring,
        Real.cos_pi_div_two, mul_zero, zero_div, zero_sub] at hd
      have heq : g₁ α - Real.pi * Real.cos (Real.pi * α) / Real.sin (Real.pi * α) =
          -(∫ t in α..(1 / 2), ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 2).re) := by
        linarith
      rw [heq, abs_neg]
      exact h_bd_int hle (by linarith [hα.1])
  have hg2_approx : ∀ α : ℝ, |g₂ α - Real.pi| ≤ (C_lor + C_sin * Δ) * Real.exp (-2 * Real.pi * Δ) := by
    intro α
    have hlor := lorentz_tsum_bound Δ α hΔ_ge_1
    have hs2 := tsum_inv_sub_I_sq ((-α : ℂ) + Complex.I * Δ) (by simp; positivity)
    have hre_summ : Summable (fun n : ℤ => Δ * (Δ ^ 2 - (n + α) ^ 2) / ((n + α) ^ 2 + Δ ^ 2) ^ 2) := by
      refine ((Complex.reCLM.summable hs2.1).mul_left (-Δ)).congr fun n => ?_
      have heq : ((-α : ℂ) + Complex.I * Δ) - n = -((n + α : ℝ) : ℂ) + Complex.I * Δ := by
        push_cast; ring
      dsimp only [Complex.reCLM_apply]
      rw [heq, one_div, Complex.inv_re, Complex.normSq_apply]
      have hsq : (-((n + α : ℝ) : ℂ) + Complex.I * Δ) ^ 2 =
          (((n + α : ℝ) ^ 2 - Δ ^ 2 : ℝ) : ℂ) - ((2 * (n + α : ℝ) * Δ : ℝ) : ℂ) * Complex.I := by
        push_cast; ring_nf; simp [Complex.I_sq]; ring
      rw [hsq]
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.sub_im, Complex.mul_im, zero_sub]
      have hden : ((n + α : ℝ) ^ 2 - Δ ^ 2) ^ 2 + (-(2 * (n + α : ℝ) * Δ)) ^ 2 =
          ((n + α : ℝ) ^ 2 + Δ ^ 2) ^ 2 := by ring
      rw [hden]; ring
    have hg2_split : g₂ α = (∑' n : ℤ, Δ / ((n + α) ^ 2 + Δ ^ 2)) +
        ∑' n : ℤ, Δ * (Δ ^ 2 - (n + α) ^ 2) / ((n + α) ^ 2 + Δ ^ 2) ^ 2 := by
      dsimp only [g₂, f₂]
      rw [← hlor.1.tsum_add hre_summ]
      congr 1; ext n
      have hne : (n + α) ^ 2 + Δ ^ 2 ≠ 0 := by positivity
      field_simp [hne]; ring
    have h_re_bd : |∑' n : ℤ, Δ * (Δ ^ 2 - (n + α) ^ 2) / ((n + α) ^ 2 + Δ ^ 2) ^ 2| ≤
        C_sin * Δ * Real.exp (-2 * Real.pi * Δ) := by
      have h_eq : (∑' n : ℤ, Δ * (Δ ^ 2 - (n + α) ^ 2) / ((n + α) ^ 2 + Δ ^ 2) ^ 2) =
          -Δ * ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-α : ℂ) + Complex.I * Δ)) ^ 2).re := by
        rw [← hs2.2, Complex.re_tsum hs2.1, ← tsum_mul_left]
        dsimp only [h_rem]
        congr 1; ext n
        have heq : ((-α : ℂ) + Complex.I * Δ) - n = -((n + α : ℝ) : ℂ) + Complex.I * Δ := by
          push_cast; ring
        rw [heq, one_div, Complex.inv_re, Complex.normSq_apply]
        have hsq : (-((n + α : ℝ) : ℂ) + Complex.I * Δ) ^ 2 =
            (((n + α : ℝ) ^ 2 - Δ ^ 2 : ℝ) : ℂ) - ((2 * (n + α : ℝ) * Δ : ℝ) : ℂ) * Complex.I := by
          push_cast; ring_nf; simp [Complex.I_sq]; ring
        rw [hsq]
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.sub_im, Complex.mul_im, zero_sub]
        have hden : ((n + α : ℝ) ^ 2 - Δ ^ 2) ^ 2 + (-(2 * (n + α : ℝ) * Δ)) ^ 2 =
            ((n + α : ℝ) ^ 2 + Δ ^ 2) ^ 2 := by ring
        rw [hden]; ring
      rw [h_eq, abs_mul, abs_neg, abs_of_pos hΔ_pos]
      calc Δ * |((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-α : ℂ) + Complex.I * Δ)) ^ 2).re|
          ≤ Δ * ‖(Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-α : ℂ) + Complex.I * Δ)) ^ 2‖ := by
            gcongr; exact Complex.abs_re_le_norm _
        _ ≤ Δ * (C_sin * Real.exp (-2 * Real.pi * Δ)) := by
            gcongr; exact complex_inv_sin_sq_bound Δ hΔ_ge_1 α
        _ = C_sin * Δ * Real.exp (-2 * Real.pi * Δ) := by ring
    rw [hg2_split, add_sub_assoc']
    calc |(∑' n : ℤ, Δ / ((n + α) ^ 2 + Δ ^ 2) - Real.pi) +
          ∑' n : ℤ, Δ * (Δ ^ 2 - (n + α) ^ 2) / ((n + α) ^ 2 + Δ ^ 2) ^ 2|
        ≤ |∑' n : ℤ, Δ / ((n + α) ^ 2 + Δ ^ 2) - Real.pi| +
          |∑' n : ℤ, Δ * (Δ ^ 2 - (n + α) ^ 2) / ((n + α) ^ 2 + Δ ^ 2) ^ 2| := abs_add_le _ _
      _ ≤ C_lor * Real.exp (-2 * Real.pi * Δ) + C_sin * Δ * Real.exp (-2 * Real.pi * Δ) := by
          gcongr
          simpa [C_lor, mul_comm, mul_div_assoc] using hlor.2
      _ = (C_lor + C_sin * Δ) * Real.exp (-2 * Real.pi * Δ) := by ring
  have hg2_diff : ∀ {a b : ℝ}, a ≤ b →
      |g₂ b - g₂ a| ≤ (C_sin + C_lip * Δ) * Real.exp (-2 * Real.pi * Δ) * (b - a) := by
    intro a b hab
    let h_lor : ℝ → ℝ := fun α => ∑' n : ℤ, Δ / ((n + α) ^ 2 + Δ ^ 2)
    let h_rem : ℝ → ℝ := fun α => ∑' n : ℤ, Δ * (Δ ^ 2 - (n + α) ^ 2) / ((n + α) ^ 2 + Δ ^ 2) ^ 2
    have hg2_eq : ∀ α : ℝ, g₂ α = h_lor α + h_rem α := by
      intro α
      have hlor := (lorentz_tsum_bound Δ α hΔ_ge_1).1
      have hs2 := tsum_inv_sub_I_sq ((-α : ℂ) + Complex.I * Δ) (by simp; positivity)
      have hre_summ : Summable (fun n : ℤ => Δ * (Δ ^ 2 - (n + α) ^ 2) / ((n + α) ^ 2 + Δ ^ 2) ^ 2) := by
        refine ((Complex.reCLM.summable hs2.1).mul_left (-Δ)).congr fun n => ?_
        have heq : ((-α : ℂ) + Complex.I * Δ) - n = -((n + α : ℝ) : ℂ) + Complex.I * Δ := by push_cast; ring
        dsimp only [Complex.reCLM_apply]
        rw [heq, one_div, Complex.inv_re, Complex.normSq_apply]
        have hsq : (-((n + α : ℝ) : ℂ) + Complex.I * Δ) ^ 2 =
            (((n + α : ℝ) ^ 2 - Δ ^ 2 : ℝ) : ℂ) - ((2 * (n + α : ℝ) * Δ : ℝ) : ℂ) * Complex.I := by
          push_cast; ring_nf; simp [Complex.I_sq]; ring
        rw [hsq]
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.sub_im, Complex.mul_im, zero_sub]
        have hden : ((n + α : ℝ) ^ 2 - Δ ^ 2) ^ 2 + (-(2 * (n + α : ℝ) * Δ)) ^ 2 = ((n + α : ℝ) ^ 2 + Δ ^ 2) ^ 2 := by ring
        rw [hden]; ring
      dsimp only [g₂, f₂, h_lor, h_rem]
      rw [← hlor.tsum_add hre_summ]
      congr 1; ext n; have hne : (n + α) ^ 2 + Δ ^ 2 ≠ 0 := by positivity
      field_simp [hne]; ring
    have hlor_diff : |h_lor b - h_lor a| ≤ C_sin * Real.exp (-2 * Real.pi * Δ) * (b - a) := by
      let d₂ : ℤ → ℝ → ℝ := fun n t => -2 * Δ * (n + t) / ((n + t) ^ 2 + Δ ^ 2) ^ 2
      have hd₂_cont : ∀ n : ℤ, ContinuousOn (d₂ n) (Set.Icc a b) := fun n =>
        Continuous.continuousOn ((continuous_const.mul (continuous_const.add continuous_id)).div
          (Continuous.pow ((Continuous.pow (continuous_const.add continuous_id) 2).add continuous_const) 2)
          (fun t => by positivity))
      have hd₂_ftc : ∀ n : ℤ, ∫ t in a..b, d₂ n t = Δ / ((n + b) ^ 2 + Δ ^ 2) - Δ / ((n + a) ^ 2 + Δ ^ 2) := by
        intro n
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => Δ / ((n + t) ^ 2 + Δ ^ 2))
        · intro t _
          have hb' := ((hasDerivAt_pow 2 ((n : ℝ) + t)).comp t ((hasDerivAt_id t).const_add (n : ℝ))).add_const (Δ ^ 2)
          convert (hasDerivAt_const t Δ).div hb' (by positivity) using 1
          dsimp only [d₂]; ring
        · exact (hd₂_cont n).mono (by rw [Set.uIcc_of_le hab]) |>.intervalIntegrable
      let M₂ : ℤ → ℝ := fun n => 4 * (1 + (|a| + |b|)) ^ 2 * Δ * (1 + |(n : ℝ)|) ^ (-2 : ℝ)
      have hM₂_summ : Summable M₂ := summable_inv_one_add_sq_int.mul_left (4 * (1 + (|a| + |b|)) ^ 2 * Δ)
      have hM₂_bd : ∀ (n : ℤ) (t : ℝ), t ∈ Set.Icc a b → ‖d₂ n t‖ ≤ M₂ n := by
        intro n t ht
        have ht_le : |t| ≤ |a| + |b| := by
          rw [abs_le]; constructor <;> linarith [ht.1, ht.2, neg_abs_le a, le_abs_self b]
        have h1 : 1 + |(n : ℝ)| ≤ (1 + (|a| + |b|)) * (1 + |(n : ℝ) + t|) := by
          have : |(n : ℝ)| ≤ |(n : ℝ) + t| + |t| := by simpa using abs_sub ((n : ℝ) + t) t
          nlinarith [abs_nonneg ((n : ℝ) + t), abs_nonneg a, abs_nonneg b]
        have h2 : (1 + |(n : ℝ) + t|) ^ 2 ≤ 2 * (1 + ((n : ℝ) + t) ^ 2) := by
          have : (1 - |(n : ℝ) + t|) ^ 2 ≥ 0 := sq_nonneg _; nlinarith [sq_abs ((n : ℝ) + t)]
        have h_den : 1 + ((n : ℝ) + t) ^ 2 ≤ ((n : ℝ) + t) ^ 2 + Δ ^ 2 := by nlinarith
        have h_num : 2 * |(n : ℝ) + t| ≤ 1 + ((n : ℝ) + t) ^ 2 := by
          nlinarith [sq_nonneg (1 - |(n : ℝ) + t|), sq_abs ((n : ℝ) + t)]
        dsimp only [d₂, M₂]
        rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_neg, abs_two, abs_of_pos hΔ_pos,
          abs_of_pos (by positivity : 0 < ((n + t) ^ 2 + Δ ^ 2) ^ 2)]
        have hpow_eq : (1 + |(n : ℝ)|) ^ (-2 : ℝ) = 1 / (1 + |(n : ℝ)|) ^ 2 := by
          have hpos : 0 < 1 + |(n : ℝ)| := by positivity
          rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hpos.le, Real.rpow_natCast, one_div]
        rw [hpow_eq]
        calc 2 * Δ * |(n : ℝ) + t| / ((n + t) ^ 2 + Δ ^ 2) ^ 2
            ≤ Δ * (1 + ((n : ℝ) + t) ^ 2) / (1 + ((n : ℝ) + t) ^ 2) ^ 2 := by
              gcongr; nlinarith
          _ = Δ / (1 + ((n : ℝ) + t) ^ 2) := by
              have hp : 1 + ((n : ℝ) + t) ^ 2 ≠ 0 := by positivity
              field_simp [hp]
          _ ≤ Δ / ((1 + |(n : ℝ)|) ^ 2 / (2 * (1 + (|a| + |b|)) ^ 2)) := by
              gcongr
              rw [div_le_iff₀ (by positivity)]
              have : (1 + |(n : ℝ)|) ^ 2 ≤ (1 + (|a| + |b|)) ^ 2 * (1 + |(n : ℝ) + t|) ^ 2 := by gcongr
              linarith
          _ = 2 * (1 + (|a| + |b|)) ^ 2 * Δ * (1 / (1 + |(n : ℝ)|) ^ 2) := by ring
          _ ≤ 4 * (1 + (|a| + |b|)) ^ 2 * Δ * (1 / (1 + |(n : ℝ)|) ^ 2) := by
              gcongr; norm_num
      have h_tsum_eq := intervalIntegral_tsum_of_dominated hab d₂ M₂ hM₂_summ hd₂_cont hM₂_bd
      simp_rw [hd₂_ftc] at h_tsum_eq
      rw [(lorentz_tsum_bound Δ b hΔ_ge_1).1.tsum_sub (lorentz_tsum_bound Δ a hΔ_ge_1).1] at h_tsum_eq
      rw [← h_tsum_eq, intervalIntegral.integral_of_le hab, ← Real.norm_eq_abs]
      have h_inner_eq : ∀ t : ℝ, ∑' n : ℤ, d₂ n t =
          -((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 2).im := by
        intro t
        have hs2 := tsum_inv_sub_I_sq ((-t : ℂ) + Complex.I * Δ) (by simp; positivity)
        rw [← hs2.2, Complex.im_tsum hs2.1, ← tsum_neg]
        congr 1; ext n
        have heq : ((-t : ℂ) + Complex.I * Δ) - n = -((n + t : ℝ) : ℂ) + Complex.I * Δ := by push_cast; ring
        rw [heq, one_div, Complex.inv_im, Complex.normSq_apply]
        have hsq : (-((n + t : ℝ) : ℂ) + Complex.I * Δ) ^ 2 =
            (((n + t : ℝ) ^ 2 - Δ ^ 2 : ℝ) : ℂ) - ((2 * (n + t : ℝ) * Δ : ℝ) : ℂ) * Complex.I := by
          push_cast; ring_nf; simp [Complex.I_sq]; ring
        rw [hsq]
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.sub_im, Complex.mul_im, zero_sub]
        have hden : ((n + t : ℝ) ^ 2 - Δ ^ 2) * ((n + t : ℝ) ^ 2 - Δ ^ 2) +
            -(2 * (n + t : ℝ) * Δ + 0) * -(2 * (n + t : ℝ) * Δ + 0) = ((n + t : ℝ) ^ 2 + Δ ^ 2) ^ 2 := by ring
        rw [hden]; dsimp only [d₂]; ring
      simp_rw [h_inner_eq]
      calc ‖∫ t in Set.Ioc a b, -((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 2).im‖
          ≤ ∫ t in Set.Ioc a b, ‖-((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 2).im‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ t in Set.Ioc a b, C_sin * Real.exp (-2 * Real.pi * Δ) := by
            refine setIntegral_mono_on ?_ (continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
              measurableSet_Ioc fun t _ => ?_
            · refine ((continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self) :
                IntegrableOn (fun _ => C_sin * Real.exp (-2 * Real.pi * Δ)) (Set.Ioc a b)).mono' ?_ ?_
              · refine Continuous.aestronglyMeasurable (Continuous.norm (Continuous.neg (Complex.continuous_im.comp ?_)))
                refine continuous_const.div (Continuous.pow (Complex.continuous_sin.comp (by fun_prop)) 2) fun t => ?_
                have h1m : 0 < 1 - Real.exp (-2 * Real.pi) := by
                  linarith [Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos] : -2 * Real.pi < 0)]
                have hs1 : 0 < ((1 - Real.exp (-2 * Real.pi)) / 2) * Real.exp (Real.pi * Δ) := by positivity
                have hs2 := sin_norm_ge_sinh (-Real.pi * t) (Real.pi * Δ)
                rw [abs_of_pos (by positivity)] at hs2
                have hs3 := (sinh_ge_mul_exp (by nlinarith [Real.pi_pos])).trans hs2
                have hnorm_pos : 0 < ‖Complex.sin ((Real.pi : ℂ) * ((-t : ℂ) + Complex.I * Δ))‖ := by
                  rw [show (Real.pi : ℂ) * ((-t : ℂ) + Complex.I * Δ) = ((-Real.pi * t : ℝ) : ℂ) + Complex.I * ((Real.pi * Δ : ℝ) : ℂ) by push_cast; ring]
                  linarith
                exact pow_ne_zero 2 (norm_ne_zero_iff.mp hnorm_pos.ne')
              · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t _
                rw [Real.norm_eq_abs, abs_norm, Real.norm_eq_abs, abs_neg]
                exact (Complex.abs_im_le_norm _).trans (complex_inv_sin_sq_bound Δ hΔ_ge_1 t)
            · rw [Real.norm_eq_abs, abs_neg]
              exact (Complex.abs_im_le_norm _).trans (complex_inv_sin_sq_bound Δ hΔ_ge_1 t)
        _ = C_sin * Real.exp (-2 * Real.pi * Δ) * (b - a) := by
            rw [setIntegral_const, Real.volume_real_Ioc_of_le hab, smul_eq_mul, mul_comm]
    have hrem_diff : |h_rem b - h_rem a| ≤ C_lip * Δ * Real.exp (-2 * Real.pi * Δ) * (b - a) := by
      have h_eq : ∀ α : ℝ, h_rem α = -Δ * ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-α : ℂ) + Complex.I * Δ)) ^ 2).re := by
        intro α
        have hs2 := tsum_inv_sub_I_sq ((-α : ℂ) + Complex.I * Δ) (by simp; positivity)
        rw [← hs2.2, Complex.re_tsum hs2.1, ← tsum_mul_left]
        congr 1; ext n
        have heq : ((-α : ℂ) + Complex.I * Δ) - n = -((n + α : ℝ) : ℂ) + Complex.I * Δ := by push_cast; ring
        rw [heq, one_div, Complex.inv_re, Complex.normSq_apply]
        have hsq : (-((n + α : ℝ) : ℂ) + Complex.I * Δ) ^ 2 =
            (((n + α : ℝ) ^ 2 - Δ ^ 2 : ℝ) : ℂ) - ((2 * (n + α : ℝ) * Δ : ℝ) : ℂ) * Complex.I := by
          push_cast; ring_nf; simp [Complex.I_sq]; ring
        rw [hsq]
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.sub_im, Complex.mul_im, zero_sub]
        have hden : ((n + α : ℝ) ^ 2 - Δ ^ 2) ^ 2 + (-(2 * (n + α : ℝ) * Δ)) ^ 2 = ((n + α : ℝ) ^ 2 + Δ ^ 2) ^ 2 := by ring
        rw [hden]; ring
      rw [h_eq b, h_eq a, show -Δ * ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-b : ℂ) + Complex.I * Δ)) ^ 2).re -
          -Δ * ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-a : ℂ) + Complex.I * Δ)) ^ 2).re =
          -Δ * (((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-b : ℂ) + Complex.I * Δ)) ^ 2 -
            (Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-a : ℂ) + Complex.I * Δ)) ^ 2).re) by simp; ring]
      rw [abs_mul, abs_neg, abs_of_pos hΔ_pos]
      calc Δ * |((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-b : ℂ) + Complex.I * Δ)) ^ 2 -
              (Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-a : ℂ) + Complex.I * Δ)) ^ 2).re|
          ≤ Δ * ‖(Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-b : ℂ) + Complex.I * Δ)) ^ 2 -
              (Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-a : ℂ) + Complex.I * Δ)) ^ 2‖ := by
            gcongr; exact Complex.abs_re_le_norm _
        _ ≤ Δ * (C_lip * Real.exp (-2 * Real.pi * Δ) * (b - a)) := by
            gcongr; exact complex_inv_sin_sq_lipschitz Δ hΔ_ge_1 hab
        _ = C_lip * Δ * Real.exp (-2 * Real.pi * Δ) * (b - a) := by ring
    rw [hg2_eq b, hg2_eq a, show (h_lor b + h_rem b) - (h_lor a + h_rem a) =
        (h_lor b - h_lor a) + (h_rem b - h_rem a) by ring]
    calc |(h_lor b - h_lor a) + (h_rem b - h_rem a)|
        ≤ |h_lor b - h_lor a| + |h_rem b - h_rem a| := abs_add_le _ _
      _ ≤ C_sin * Real.exp (-2 * Real.pi * Δ) * (b - a) +
            C_lip * Δ * Real.exp (-2 * Real.pi * Δ) * (b - a) := add_le_add hlor_diff hrem_diff
      _ = (C_sin + C_lip * Δ) * Real.exp (-2 * Real.pi * Δ) * (b - a) := by ring
  -- Strict anti-monotonicity of g on (0, 1)
  have hg_strict_anti : StrictAntiOn g (Set.Ioo (0 : ℝ) 1) := by
    intro a ha b hb hab
    have hd1 := hg1_diff ha hb hab.le
    have h_sin_int : b - a ≤ ∫ t in a..b, 1 / Real.sin (Real.pi * t) ^ 2 := by
      rw [intervalIntegral.integral_of_le hab.le]
      calc b - a = ∫ _t in Set.Ioc a b, (1 : ℝ) := by
            rw [setIntegral_const, Real.volume_real_Ioc_of_le hab.le, smul_eq_mul, mul_one]
        _ ≤ ∫ t in Set.Ioc a b, 1 / Real.sin (Real.pi * t) ^ 2 := by
            refine setIntegral_mono_on (continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self) ?_
              measurableSet_Ioc fun t ht => ?_
            · refine ContinuousOn.integrableOn_Icc ?_ |>.mono_set Set.Ioc_subset_Icc_self
              refine continuousOn_const.div (ContinuousOn.pow (Real.continuous_sin.continuousOn.comp
                (continuousOn_const.mul continuousOn_id) (fun _ _ => Set.mem_univ _)) 2) ?_
              intro t ht; exact pow_ne_zero 2 (h_sin_ne t ⟨lt_of_lt_of_le ha.1 ht.1, lt_of_le_of_lt ht.2 hb.2⟩)
            · have hpos : 0 < Real.sin (Real.pi * t) ^ 2 := sq_pos_of_ne_zero (h_sin_ne t ⟨lt_of_lt_of_le ha.1 ht.1.le, lt_of_le_of_lt ht.2 hb.2⟩)
              exact one_le_one_div hpos (Real.sin_sq_le_one _)
    have h_rem_bd : ∫ t in a..b, ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 2).re ≤
        C_sin * Real.exp (-2 * Real.pi * Δ) * (b - a) := by
      rw [intervalIntegral.integral_of_le hab.le]
      calc ∫ t in Set.Ioc a b, ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 2).re
          ≤ ∫ t in Set.Ioc a b, C_sin * Real.exp (-2 * Real.pi * Δ) := by
            refine setIntegral_mono_on ?_ (continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
              measurableSet_Ioc fun t _ => ?_
            · refine ((continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self) :
                IntegrableOn (fun _ => C_sin * Real.exp (-2 * Real.pi * Δ)) (Set.Ioc a b)).mono' ?_ ?_
              · refine Continuous.aestronglyMeasurable (Complex.continuous_re.comp ?_)
                refine continuous_const.div (Continuous.pow (Complex.continuous_sin.comp (by fun_prop)) 2) fun t => ?_
                have h1m : 0 < 1 - Real.exp (-2 * Real.pi) := by
                  linarith [Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos] : -2 * Real.pi < 0)]
                have hs1 : 0 < ((1 - Real.exp (-2 * Real.pi)) / 2) * Real.exp (Real.pi * Δ) := by positivity
                have hs2 := sin_norm_ge_sinh (-Real.pi * t) (Real.pi * Δ)
                rw [abs_of_pos (by positivity)] at hs2
                have hs3 := (sinh_ge_mul_exp (by nlinarith [Real.pi_pos])).trans hs2
                have hnorm_pos : 0 < ‖Complex.sin ((Real.pi : ℂ) * ((-t : ℂ) + Complex.I * Δ))‖ := by
                  rw [show (Real.pi : ℂ) * ((-t : ℂ) + Complex.I * Δ) = ((-Real.pi * t : ℝ) : ℂ) + Complex.I * ((Real.pi * Δ : ℝ) : ℂ) by push_cast; ring]
                  linarith
                exact pow_ne_zero 2 (norm_ne_zero_iff.mp hnorm_pos.ne')
              · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t _
                rw [Real.norm_eq_abs]
                exact (Complex.abs_re_le_norm _).trans (complex_inv_sin_sq_bound Δ hΔ_ge_1 t)
            · exact (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans (complex_inv_sin_sq_bound Δ hΔ_ge_1 t))
        _ = C_sin * Real.exp (-2 * Real.pi * Δ) * (b - a) := by
            rw [setIntegral_const, Real.volume_real_Ioc_of_le hab.le, smul_eq_mul, mul_comm]
    have hg1_le : g₁ b - g₁ a ≤ -(Real.pi ^ 2 * (b - a)) + C_sin * Real.exp (-2 * Real.pi * Δ) * (b - a) := by
      have hpi2 : Real.pi ^ 2 * (b - a) ≤ Real.pi ^ 2 * ∫ t in a..b, 1 / Real.sin (Real.pi * t) ^ 2 :=
        mul_le_mul_of_nonneg_left h_sin_int (sq_nonneg _)
      rw [hd1]; linarith
    have hg2_le : -Real.sin θ * (g₂ b - g₂ a) ≤ (C_sin + C_lip * Δ) * Real.exp (-2 * Real.pi * Δ) * (b - a) := by
      have h1 := hg2_diff hab.le
      have hsin_le : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
      calc -Real.sin θ * (g₂ b - g₂ a) ≤ |-Real.sin θ * (g₂ b - g₂ a)| := le_abs_self _
        _ = |Real.sin θ| * |g₂ b - g₂ a| := by rw [abs_mul, abs_neg]
        _ ≤ 1 * ((C_sin + C_lip * Δ) * Real.exp (-2 * Real.pi * Δ) * (b - a)) :=
            mul_le_mul hsin_le h1 (abs_nonneg _) zero_le_one
        _ = (C_sin + C_lip * Δ) * Real.exp (-2 * Real.pi * Δ) * (b - a) := one_mul _
    have h_diff_neg : g b - g a < 0 := by
      have h_eq : g b - g a = Real.cos θ * (g₁ b - g₁ a) + (-Real.sin θ * (g₂ b - g₂ a)) := by
        dsimp only [g]; ring
      rw [h_eq]
      have h_t1 : Real.cos θ * (g₁ b - g₁ a) ≤
          (-Real.cos θ * Real.pi ^ 2 + Real.cos θ * C_sin * Real.exp (-2 * Real.pi * Δ)) * (b - a) := by
        have := mul_le_mul_of_nonneg_left hg1_le hcos_pos.le
        linarith
      have h_strict : (-Real.cos θ * Real.pi ^ 2 + Real.cos θ * C_sin * Real.exp (-2 * Real.pi * Δ) +
          (C_sin + C_lip * Δ) * Real.exp (-2 * Real.pi * Δ)) < 0 := by
        have hcos_le : Real.cos θ ≤ 1 := Real.cos_le_one θ
        have h1 : Real.cos θ * C_sin * Real.exp (-2 * Real.pi * Δ) ≤ C_sin * Real.exp (-2 * Real.pi * Δ) := by
          rw [mul_assoc]; exact mul_le_of_le_one_left (by positivity) hcos_le
        have h_nn : 0 ≤ C_lip * Δ * Real.exp (-2 * Real.pi * Δ) := by positivity
        have h2 : C_sin * Real.exp (-2 * Real.pi * Δ) ≤ (C_sin + C_lip * Δ) * Real.exp (-2 * Real.pi * Δ) := by
          linarith [show (C_sin + C_lip * Δ) * Real.exp (-2 * Real.pi * Δ) = C_sin * Real.exp (-2 * Real.pi * Δ) + C_lip * Δ * Real.exp (-2 * Real.pi * Δ) by ring]
        linarith [h_mono_bd]
      have hba_pos : 0 < b - a := sub_pos.mpr hab
      exact lt_of_le_of_lt (by linarith) (mul_neg_of_neg_of_pos h_strict hba_pos)
    linarith
  -- Continuity of g on (0, 1)
  have hg_cont : ContinuousOn g (Set.Ioo (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    rw [continuous_iff_continuousAt]
    intro ⟨α, hα⟩
    rw [Metric.continuousAt_iff]
    intro ε hε
    let δ₁ := min (α / 2) ((1 - α) / 2)
    have hδ₁_pos : 0 < δ₁ := lt_min (by linarith [hα.1]) (by linarith [hα.2])
    let K_loc : ℝ := Real.pi ^ 2 / Real.sin (Real.pi * δ₁) ^ 2 +
      C_sin * Real.exp (-2 * Real.pi * Δ) + (C_sin + C_lip * Δ) * Real.exp (-2 * Real.pi * Δ) + 1
    have hsin_δ₁ : 0 < Real.sin (Real.pi * δ₁) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos, hα.1, hα.2, min_le_left (α / 2) ((1 - α) / 2)])
    have hK_loc_pos : 0 < K_loc := by positivity
    refine ⟨min δ₁ (ε / (2 * K_loc)), lt_min hδ₁_pos (by positivity), fun ⟨β, hβ⟩ hdist => ?_⟩
    have hdist' : |β - α| < min δ₁ (ε / (2 * K_loc)) := by simpa [Subtype.dist_eq, Real.dist_eq] using hdist
    have hβ_sub : |β - α| < δ₁ := lt_of_lt_of_le hdist' (min_le_left _ _)
    have hβ_eps : |β - α| < ε / (2 * K_loc) := lt_of_lt_of_le hdist' (min_le_right _ _)
    have h_lip_g : ∀ {u v : ℝ}, u ∈ Set.Icc δ₁ (1 - δ₁) → v ∈ Set.Icc δ₁ (1 - δ₁) → u ≤ v →
        |g v - g u| ≤ K_loc * (v - u) := by
      intro u v hu hv huv
      have hu_ioo : u ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_lt_of_le hδ₁_pos hu.1, lt_of_le_of_lt hu.2 (by linarith)⟩
      have hv_ioo : v ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_lt_of_le hδ₁_pos hv.1, lt_of_le_of_lt hv.2 (by linarith)⟩
      have hd1 := hg1_diff hu_ioo hv_ioo huv
      have h_sin_bd : ∫ t in u..v, 1 / Real.sin (Real.pi * t) ^ 2 ≤ (v - u) / Real.sin (Real.pi * δ₁) ^ 2 := by
        rw [intervalIntegral.integral_of_le huv]
        calc ∫ t in Set.Ioc u v, 1 / Real.sin (Real.pi * t) ^ 2
            ≤ ∫ _t in Set.Ioc u v, 1 / Real.sin (Real.pi * δ₁) ^ 2 := by
              refine setIntegral_mono_on ?_ (continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
                measurableSet_Ioc fun t ht => ?_
              · refine ContinuousOn.integrableOn_Icc ?_ |>.mono_set Set.Ioc_subset_Icc_self
                refine continuousOn_const.div (ContinuousOn.pow (Real.continuous_sin.continuousOn.comp
                  (continuousOn_const.mul continuousOn_id) (fun _ _ => Set.mem_univ _)) 2) ?_
                intro t ht; exact pow_ne_zero 2 (h_sin_ne t ⟨lt_of_lt_of_le hu_ioo.1 ht.1, lt_of_le_of_lt ht.2 hv_ioo.2⟩)
              · have ht_icc : t ∈ Set.Icc δ₁ (1 - δ₁) := ⟨le_trans hu.1 ht.1.le, le_trans ht.2 hv.2⟩
                have hsin_t : Real.sin (Real.pi * δ₁) ≤ Real.sin (Real.pi * t) := by
                  rcases le_total t (1 / 2) with ht12 | ht12
                  · exact Real.strictMonoOn_sin.monotoneOn
                      ⟨by nlinarith [Real.pi_pos, hδ₁_pos], by nlinarith [Real.pi_pos, ht_icc.1, ht12]⟩
                      ⟨by nlinarith [Real.pi_pos, hδ₁_pos, ht_icc.1], by nlinarith [Real.pi_pos, ht12]⟩
                      (by nlinarith [Real.pi_pos, ht_icc.1])
                  · rw [← Real.sin_pi_sub (Real.pi * t)]
                    exact Real.strictMonoOn_sin.monotoneOn
                      ⟨by nlinarith [Real.pi_pos, hδ₁_pos], by nlinarith [Real.pi_pos, ht_icc.2, ht12]⟩
                      ⟨by nlinarith [Real.pi_pos, ht_icc.2, hδ₁_pos], by nlinarith [Real.pi_pos, ht12]⟩
                      (by nlinarith [Real.pi_pos, ht_icc.2])
                exact one_div_le_one_div_of_le (sq_pos_of_pos hsin_δ₁) (sq_le_sq' (by linarith) hsin_t)
          _ = (v - u) / Real.sin (Real.pi * δ₁) ^ 2 := by
              rw [setIntegral_const, Real.volume_real_Ioc_of_le huv, smul_eq_mul]; ring
      have h_rem_bd : |∫ t in u..v, ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 2).re| ≤
          C_sin * Real.exp (-2 * Real.pi * Δ) * (v - u) := by
        rw [intervalIntegral.integral_of_le huv, ← Real.norm_eq_abs]
        calc ‖∫ t in Set.Ioc u v, ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 2).re‖
            ≤ ∫ t in Set.Ioc u v, ‖((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 2).re‖ :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ _t in Set.Ioc u v, C_sin * Real.exp (-2 * Real.pi * Δ) := by
              refine setIntegral_mono_on ?_ (continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
                measurableSet_Ioc fun t _ => ?_
              · refine ((continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self) :
                  IntegrableOn (fun _ => C_sin * Real.exp (-2 * Real.pi * Δ)) (Set.Ioc u v)).mono' ?_ ?_
                · refine Continuous.aestronglyMeasurable (Continuous.norm (Complex.continuous_re.comp ?_))
                  refine continuous_const.div (Continuous.pow (Complex.continuous_sin.comp (by fun_prop)) 2) fun t => ?_
                  have heq : (Real.pi : ℂ) * ((-t : ℂ) + Complex.I * Δ) = ((-Real.pi * t : ℝ) : ℂ) + Complex.I * ((Real.pi * Δ : ℝ) : ℂ) := by
                    push_cast; ring
                  have h1m : 0 < 1 - Real.exp (-2 * Real.pi) := by
                    linarith [Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos] : -2 * Real.pi < 0)]
                  have hs1 : 0 < ((1 - Real.exp (-2 * Real.pi)) / 2) * Real.exp (Real.pi * Δ) := by positivity
                  have hs2 := sin_norm_ge_sinh (-Real.pi * t) (Real.pi * Δ)
                  rw [abs_of_pos (by positivity)] at hs2
                  have hs3 := (sinh_ge_mul_exp (by nlinarith [Real.pi_pos])).trans hs2
                  rw [← heq] at hs3
                  exact pow_ne_zero 2 (norm_ne_zero_iff.mp (by linarith))
                · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t _
                  rw [Real.norm_eq_abs, abs_norm, Real.norm_eq_abs]
                  exact (Complex.abs_re_le_norm _).trans (complex_inv_sin_sq_bound Δ hΔ_ge_1 t)
              · rw [Real.norm_eq_abs]
                exact (Complex.abs_re_le_norm _).trans (complex_inv_sin_sq_bound Δ hΔ_ge_1 t)
          _ = C_sin * Real.exp (-2 * Real.pi * Δ) * (v - u) := by
              rw [setIntegral_const, Real.volume_real_Ioc_of_le huv, smul_eq_mul, mul_comm]
      have hg1_bd : |g₁ v - g₁ u| ≤ (Real.pi ^ 2 / Real.sin (Real.pi * δ₁) ^ 2 + C_sin * Real.exp (-2 * Real.pi * Δ)) * (v - u) := by
        rw [hd1]
        have h_nonneg : 0 ≤ ∫ t in u..v, 1 / Real.sin (Real.pi * t) ^ 2 := by
          rw [intervalIntegral.integral_of_le huv]
          exact setIntegral_nonneg measurableSet_Ioc fun t _ => by positivity
        calc |-(Real.pi ^ 2 * ∫ t in u..v, 1 / Real.sin (Real.pi * t) ^ 2) +
              ∫ t in u..v, ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 2).re|
            ≤ |-(Real.pi ^ 2 * ∫ t in u..v, 1 / Real.sin (Real.pi * t) ^ 2)| +
              |∫ t in u..v, ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 2).re| := abs_add_le _ _
          _ = Real.pi ^ 2 * (∫ t in u..v, 1 / Real.sin (Real.pi * t) ^ 2) +
              |∫ t in u..v, ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * ((-t : ℂ) + Complex.I * Δ)) ^ 2).re| := by
              rw [abs_neg, abs_of_nonneg (mul_nonneg (sq_nonneg _) h_nonneg)]
          _ ≤ Real.pi ^ 2 * ((v - u) / Real.sin (Real.pi * δ₁) ^ 2) + C_sin * Real.exp (-2 * Real.pi * Δ) * (v - u) := by
              gcongr
          _ = (Real.pi ^ 2 / Real.sin (Real.pi * δ₁) ^ 2 + C_sin * Real.exp (-2 * Real.pi * Δ)) * (v - u) := by ring
      have hg2_bd := hg2_diff huv
      calc |g v - g u| = |Real.cos θ * (g₁ v - g₁ u) - Real.sin θ * (g₂ v - g₂ u)| := by dsimp only [g]; ring_nf
        _ ≤ |Real.cos θ * (g₁ v - g₁ u)| + |Real.sin θ * (g₂ v - g₂ u)| := abs_sub _ _
        _ = |Real.cos θ| * |g₁ v - g₁ u| + |Real.sin θ| * |g₂ v - g₂ u| := by rw [abs_mul, abs_mul]
        _ ≤ 1 * |g₁ v - g₁ u| + 1 * |g₂ v - g₂ u| := by gcongr; exact Real.abs_cos_le_one _; exact Real.abs_sin_le_one _
        _ ≤ K_loc * (v - u) := by
            have h1 := add_le_add hg1_bd hg2_bd
            have h2 : (Real.pi ^ 2 / Real.sin (Real.pi * δ₁) ^ 2 + C_sin * Real.exp (-2 * Real.pi * Δ)) * (v - u) +
                (C_sin + C_lip * Δ) * Real.exp (-2 * Real.pi * Δ) * (v - u) ≤ K_loc * (v - u) := by
              rw [← add_mul]
              exact mul_le_mul_of_nonneg_right (by dsimp only [K_loc]; linarith) (sub_nonneg.mpr huv)
            linarith
    have hα_icc : α ∈ Set.Icc δ₁ (1 - δ₁) := by
      constructor
      · exact le_trans (min_le_left _ _) (by linarith [hα.1])
      · have : δ₁ ≤ (1 - α) / 2 := min_le_right _ _
        linarith [hα.2]
    have hβ_icc : β ∈ Set.Icc δ₁ (1 - δ₁) := by
      have := abs_lt.mp hβ_sub
      constructor
      · have : δ₁ ≤ α / 2 := min_le_left _ _
        linarith
      · have : δ₁ ≤ (1 - α) / 2 := min_le_right _ _
        linarith
    rcases le_total α β with hab | hab
    · calc dist (g β) (g α) = |g β - g α| := Real.dist_eq _ _
        _ ≤ K_loc * (β - α) := h_lip_g hα_icc hβ_icc hab
        _ = K_loc * |β - α| := by rw [abs_of_nonneg (sub_nonneg.mpr hab)]
        _ < K_loc * (ε / (2 * K_loc)) := mul_lt_mul_of_pos_left hβ_eps hK_loc_pos
        _ = ε / 2 := by field_simp [hK_loc_pos.ne']
        _ < ε := by linarith
    · calc dist (g β) (g α) = |g α - g β| := by rw [Real.dist_eq, abs_sub_comm]
        _ ≤ K_loc * (α - β) := h_lip_g hβ_icc hα_icc hab
        _ = K_loc * |β - α| := by rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)]
        _ < K_loc * (ε / (2 * K_loc)) := mul_lt_mul_of_pos_left hβ_eps hK_loc_pos
        _ = ε / 2 := by field_simp [hK_loc_pos.ne']
        _ < ε := by linarith
  -- Existence and error bound via IVT on [α_star - r, α_star + r]
  let r : ℝ := C_α * Δ * Real.exp (-2 * Real.pi * Δ)
  have hr_pos : 0 < r := by positivity
  have hr_le_δ : r ≤ δ_star := le_trans h_r_le (min_le_left _ _)
  have hr_le_14 : r ≤ 1 / 4 := le_trans h_r_le (min_le_right _ _)
  let alpha_minus : ℝ := α_star - r
  let alpha_plus : ℝ := α_star + r
  have hIcc_sub : Set.Icc alpha_minus alpha_plus ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro α hα
    have h1 : δ_star ≤ α_star / 2 := min_le_left _ _
    have h2 : δ_star ≤ (1 - α_star) / 2 := min_le_right _ _
    constructor <;> linarith [hα.1, hα.2, hα_star.1, hα_star.2]
  have halpha_minus_mem : alpha_minus ∈ Set.Ioo (0 : ℝ) 1 := hIcc_sub (Set.left_mem_Icc.mpr (by linarith))
  have halpha_plus_mem : alpha_plus ∈ Set.Ioo (0 : ℝ) 1 := hIcc_sub (Set.right_mem_Icc.mpr (by linarith))
  have hg_approx : ∀ (s : ℝ), |s| ≤ r →
      |g (α_star + s) - (-Real.pi * Real.sin (Real.pi * s) / Real.sin (Real.pi * (α_star + s)))| ≤
        C_tot * Δ * Real.exp (-2 * Real.pi * Δ) := by
    intro s hs
    have hαs : α_star + s ∈ Set.Ioo (0 : ℝ) 1 :=
      hIcc_sub ⟨by linarith [(abs_le.mp hs).1], by linarith [(abs_le.mp hs).2]⟩
    have hsin_αs : 0 < Real.sin (Real.pi * (α_star + s)) :=
      Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hαs.1) (by nlinarith [Real.pi_pos, hαs.2])
    have h_trig : Real.cos θ * (Real.pi * Real.cos (Real.pi * (α_star + s)) / Real.sin (Real.pi * (α_star + s))) -
        Real.sin θ * Real.pi = -Real.pi * Real.sin (Real.pi * s) / Real.sin (Real.pi * (α_star + s)) := by
      have h_ang : Real.pi * (α_star + s) = Real.pi / 2 + (Real.pi * s - θ) := by
        dsimp only [α_star]; field_simp [Real.pi_ne_zero]; ring
      have h_num : Real.cos θ * Real.cos (Real.pi * (α_star + s)) - Real.sin θ * Real.sin (Real.pi * (α_star + s)) =
          -Real.sin (Real.pi * s) := by
        rw [← Real.cos_add]
        have heq : θ + Real.pi * (α_star + s) = Real.pi / 2 + Real.pi * s := by
          rw [h_ang]; ring
        rw [heq, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
      field_simp [hsin_αs.ne']
      nlinarith
    have h1 := hg1_approx (α_star + s) hαs
    have h2 := hg2_approx (α_star + s)
    have h_diff : g (α_star + s) - (-Real.pi * Real.sin (Real.pi * s) / Real.sin (Real.pi * (α_star + s))) =
        Real.cos θ * (g₁ (α_star + s) - Real.pi * Real.cos (Real.pi * (α_star + s)) / Real.sin (Real.pi * (α_star + s))) -
        Real.sin θ * (g₂ (α_star + s) - Real.pi) := by
      dsimp only [g]; linarith
    rw [h_diff]
    calc |Real.cos θ * _ - Real.sin θ * _|
        ≤ |Real.cos θ * _| + |Real.sin θ * _| := abs_sub _ _
      _ = |Real.cos θ| * |_ | + |Real.sin θ| * |_ | := by rw [abs_mul, abs_mul]
      _ ≤ 1 * (C_sin * Real.exp (-2 * Real.pi * Δ)) + 1 * ((C_lor + C_sin * Δ) * Real.exp (-2 * Real.pi * Δ)) := by
          gcongr
          · exact Real.abs_cos_le_one _
          · exact Real.abs_sin_le_one _
      _ = (C_sin + C_lor + C_sin * Δ) * Real.exp (-2 * Real.pi * Δ) := by ring
      _ ≤ C_tot * Δ * Real.exp (-2 * Real.pi * Δ) := by
          have : C_sin + C_lor + C_sin * Δ ≤ C_tot * Δ := by
            dsimp only [C_tot]; nlinarith
          exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  have hsin_r_ge : 2 * r ≤ Real.sin (Real.pi * r) := by
    have h1 : 0 ≤ Real.pi * r := by positivity
    have h2 : Real.pi * r ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
    have h3 := Real.mul_le_sin h1 h2
    linarith
  have h_gap : C_tot * Δ * Real.exp (-2 * Real.pi * Δ) < Real.pi * (2 * r) := by
    dsimp only [r, C_α]
    have : C_tot < Real.pi * (2 * (C_tot / (2 * Real.pi) + 1)) := by
      field_simp [Real.pi_ne_zero]; linarith [Real.pi_pos]
    nlinarith [Real.exp_pos (-2 * Real.pi * Δ)]
  have hg_pos_neg : g alpha_plus < 0 ∧ 0 < g alpha_minus := by
    have hsin_p : 0 < Real.sin (Real.pi * alpha_plus) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos, halpha_plus_mem.2])
    have hsin_p_le : Real.sin (Real.pi * alpha_plus) ≤ 1 := Real.sin_le_one _
    have h_p := hg_approx r (by rw [abs_of_pos hr_pos])
    have h_p_main : Real.pi * Real.sin (Real.pi * r) / Real.sin (Real.pi * alpha_plus) ≥ Real.pi * (2 * r) := by
      calc Real.pi * Real.sin (Real.pi * r) / Real.sin (Real.pi * alpha_plus)
          ≥ Real.pi * (2 * r) / 1 := div_le_div₀ (by positivity) (by gcongr) zero_lt_one hsin_p_le
        _ = Real.pi * (2 * r) := div_one _
    have hg_p_lt : g alpha_plus < 0 := by
      have := (abs_le.mp h_p).2
      dsimp only [alpha_plus]
      linarith
    have hsin_m : 0 < Real.sin (Real.pi * alpha_minus) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos, halpha_minus_mem.2])
    have hsin_m_le : Real.sin (Real.pi * alpha_minus) ≤ 1 := Real.sin_le_one _
    have h_m := hg_approx (-r) (by rw [abs_neg, abs_of_pos hr_pos])
    have h_m_main : -Real.pi * Real.sin (Real.pi * (-r)) / Real.sin (Real.pi * alpha_minus) ≥ Real.pi * (2 * r) := by
      rw [mul_neg, Real.sin_neg, neg_mul, neg_neg]
      calc Real.pi * Real.sin (Real.pi * r) / Real.sin (Real.pi * alpha_minus)
          ≥ Real.pi * (2 * r) / 1 := div_le_div₀ (by positivity) (by gcongr) zero_lt_one hsin_m_le
        _ = Real.pi * (2 * r) := div_one _
    have hg_m_gt : 0 < g alpha_minus := by
      have := (abs_le.mp h_m).1
      dsimp only [alpha_minus]
      rw [sub_eq_add_neg]
      linarith
    exact ⟨hg_p_lt, hg_m_gt⟩
  have h_ivt := intermediate_value_Icc' (by linarith : alpha_minus ≤ alpha_plus) (hg_cont.mono hIcc_sub)
  have h0_mem : (0 : ℝ) ∈ Set.Icc (g alpha_plus) (g alpha_minus) := ⟨hg_pos_neg.1.le, hg_pos_neg.2.le⟩
  obtain ⟨α, hα_icc, hα_zero⟩ := h_ivt h0_mem
  have hα_mem : α ∈ Set.Ioo (0 : ℝ) 1 := hIcc_sub hα_icc
  refine ⟨α, ⟨hα_mem, h_summ_all α hα_mem, by rw [hg_eq α hα_mem]; exact hα_zero, ?_⟩, ?_⟩
  · rw [abs_le]
    constructor <;> linarith [hα_icc.1, hα_icc.2]
  · intro β ⟨hβ_mem, _, hβ_sum, _⟩
    rw [hg_eq β hβ_mem] at hβ_sum
    rcases lt_trichotomy β α with hlt | rfl | hgt
    · have := hg_strict_anti hβ_mem hα_mem hlt; linarith
    · rfl
    · have := hg_strict_anti hα_mem hβ_mem hgt; linarith


end PolarEvaluation
