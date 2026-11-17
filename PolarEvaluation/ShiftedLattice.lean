import PolarEvaluation.Basic
import PolarEvaluation.ExplicitFormulae

/-!
# The Asymmetric Mixed Beurling–Selberg Problem (Section 3 & Theorem 1.6)

Formalizes Lemma 3.1 (`optimal_lattice_shift`), Lemma 3.2 (`contour_representation`),
Lemma 3.3 (`limitingJ_pos`, `limitingJ_near_zero`, `limitingJ_asymptotic`),
and Theorem 1.6 (`asymmetric_majorant`).
-/

noncomputable section

open Complex Real MeasureTheory Filter Topology
open scoped FourierTransform

namespace PolarEvaluation

/-! ### Helper Lemmas: Poisson Summation for Lorentzian and Cauchy-Squared Kernels -/

lemma exp_neg_le_inv_one_add_sq {a x : ℝ} (ha : 2 ≤ a) :
    Real.exp (-a * |x|) ≤ (1 + |x|) ^ (-2 : ℝ) := by
  have h1 : 0 ≤ a * |x| := by positivity
  have h_sum := Real.sum_le_exp_of_nonneg h1 3
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one,
    Nat.factorial_two, Nat.cast_ofNat] at h_sum
  have h_sq : (1 + |x|) ^ 2 ≤ Real.exp (a * |x|) := by
    have h2 : 2 * |x| ≤ a * |x| := mul_le_mul_of_nonneg_right ha (abs_nonneg x)
    have h3 : |x| ^ 2 ≤ (a * |x|) ^ 2 / 2 := by
      have : 2 ≤ a ^ 2 := by nlinarith
      nlinarith [sq_nonneg x]
    linarith [show (1 + |x|) ^ 2 = 1 + 2 * |x| + |x| ^ 2 by ring]
  have hpos : 0 < 1 + |x| := by positivity
  rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hpos.le, Real.rpow_natCast,
    show -a * |x| = -(a * |x|) by ring, Real.exp_neg]
  exact inv_anti₀ (by positivity) h_sq

lemma summable_inv_one_add_sq_int :
    Summable (fun n : ℤ => (1 + |(n : ℝ)|) ^ (-2 : ℝ)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  have hnat : Summable (fun n : ℕ => (1 + |(n : ℝ)|) ^ (-2 : ℝ)) := by
    have h1 : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
      simpa using Real.summable_one_div_nat_pow_two.comp_injective Nat.succ_injective
    refine h1.congr fun n => ?_
    have hpos : (0 : ℝ) < 1 + (n : ℝ) := by positivity
    rw [abs_of_nonneg (Nat.cast_nonneg n), show (-2 : ℝ) = -(2 : ℕ) by norm_num,
      Real.rpow_neg hpos.le, Real.rpow_natCast, one_div]
    push_cast; ring_nf
  exact ⟨hnat, by simpa [abs_neg] using hnat⟩

lemma summable_inv_one_add_sq_shift (α : ℝ) :
    Summable (fun n : ℤ => (1 + |α + n|) ^ (-2 : ℝ)) := by
  refine (summable_inv_one_add_sq_int.mul_left ((1 + |α|) ^ 2)).of_nonneg_of_le
    (fun _ => by positivity) (fun n => ?_)
  have h1 : 1 + |(n : ℝ)| ≤ (1 + |α|) * (1 + |α + n|) := by
    have htri : |(n : ℝ)| ≤ |α| + |α + n| := by
      have : (n : ℝ) = (α + n) - α := by ring
      rw [this]
      calc |(α + n) - α| ≤ |α + n| + |α| := abs_sub _ _
        _ = |α| + |α + n| := add_comm _ _
    nlinarith [abs_nonneg α, abs_nonneg (α + n)]
  have hpos1 : 0 < 1 + |(n : ℝ)| := by positivity
  have hpos2 : 0 < 1 + |α + n| := by positivity
  rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hpos2.le, Real.rpow_natCast,
    Real.rpow_neg hpos1.le, Real.rpow_natCast, inv_eq_one_div, inv_eq_one_div,
    mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  calc (1 + |(n : ℝ)|) ^ 2 ≤ ((1 + |α|) * (1 + |α + n|)) ^ 2 := by gcongr
    _ = (1 + |α|) ^ 2 * (1 + |α + n|) ^ 2 := by ring

lemma lorentz_tsum_bound (Δ α : ℝ) (hΔ : Δ ≥ 1) :
    Summable (fun n : ℤ => Δ / ((n + α) ^ 2 + Δ ^ 2)) ∧
    |∑' n : ℤ, Δ / ((n + α) ^ 2 + Δ ^ 2) - Real.pi| ≤
      2 * Real.pi * Real.exp (-2 * Real.pi * Δ) / (1 - Real.exp (-2 * Real.pi)) := by
  let f : ℝ → ℂ := fun u => ((Δ / (u ^ 2 + Δ ^ 2) : ℝ) : ℂ)
  have hf_cont : Continuous f := by
    dsimp only [f]
    refine Complex.continuous_ofReal.comp ?_
    exact continuous_const.div (by fun_prop) (fun u => by positivity)
  have hf_decay : ∃ C, ∀ x : ℝ, ‖f x‖ ≤ C * (1 + |x|) ^ (-2 : ℝ) := by
    refine ⟨2 * Δ, fun x => ?_⟩
    dsimp only [f]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos (by positivity) (by positivity))]
    have hpos : 0 < 1 + |x| := by positivity
    rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hpos.le, Real.rpow_natCast,
      mul_inv_le_iff₀ (by positivity)]
    have h1 : (1 + |x|) ^ 2 ≤ 2 * (1 + x ^ 2) := by
      have : (1 - |x|) ^ 2 ≥ 0 := sq_nonneg _
      nlinarith [sq_abs x]
    have h2 : 1 + x ^ 2 ≤ x ^ 2 + Δ ^ 2 := by nlinarith
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hFf : ∀ ξ : ℝ, 𝓕 f ξ = (Real.pi : ℂ) * Complex.exp (-2 * Real.pi * Δ * |ξ|) := by
    intro ξ
    rw [← fourierHat_eq_fourier]
    exact kernelK_zero_lorentz_fourier Δ (by linarith) ξ
  have hf'_decay : ∃ C, ∀ ξ : ℝ, ‖𝓕 f ξ‖ ≤ C * (1 + |ξ|) ^ (-2 : ℝ) := by
    refine ⟨Real.pi, fun ξ => ?_⟩
    rw [hFf ξ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hcexp : Complex.exp (-2 * Real.pi * Δ * |ξ|) = (Real.exp (-2 * Real.pi * Δ * |ξ|) : ℂ) := by
      have : (-2 * (Real.pi : ℂ) * ↑Δ * ↑|ξ| : ℂ) = ((-2 * Real.pi * Δ * |ξ| : ℝ) : ℂ) := by
        push_cast; ring
      rw [this, ← Complex.ofReal_exp]
    rw [hcexp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have ha : 2 ≤ 2 * Real.pi * Δ := by nlinarith [Real.two_le_pi]
    exact mul_le_mul_of_nonneg_left (exp_neg_le_inv_one_add_sq ha) Real.pi_pos.le
  have hpois := Real.tsum_eq_tsum_fourierIntegral_of_rpow_decay hf_cont (by norm_num : (1 : ℝ) < 2) hf_decay hf'_decay α
  have hsumm_real : Summable (fun n : ℤ => Δ / ((n + α) ^ 2 + Δ ^ 2)) := by
    refine ((summable_inv_one_add_sq_shift α).mul_left (2 * Δ)).of_nonneg_of_le
      (fun _ => by positivity) (fun n => ?_)
    have hpos : 0 < 1 + |α + n| := by positivity
    rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hpos.le, Real.rpow_natCast,
      mul_inv_le_iff₀ (by positivity)]
    have h1 : (1 + |α + n|) ^ 2 ≤ 2 * (1 + (α + n) ^ 2) := by
      have : (1 - |α + n|) ^ 2 ≥ 0 := sq_nonneg _
      nlinarith [sq_abs (α + n)]
    have h2 : 1 + (α + n) ^ 2 ≤ (n + α) ^ 2 + Δ ^ 2 := by nlinarith [show (n : ℝ) + α = α + n by ring]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨hsumm_real, ?_⟩
  have hre_lhs : (∑' n : ℤ, f (α + n)).re = ∑' n : ℤ, Δ / ((n + α) ^ 2 + Δ ^ 2) := by
    have hsc : Summable (fun n : ℤ => f (α + n)) := by
      simpa [f, add_comm] using hsumm_real.ofReal
    rw [Complex.re_tsum hsc]
    congr 1; ext n; simp [f, add_comm]
  rw [← hre_lhs, hpois]
  let g : ℤ → ℂ := fun k => 𝐞 (k * α) • 𝓕 f k
  have hg_summ : Summable g := by
    refine Summable.of_norm_bounded (g := fun k : ℤ => Real.pi * (1 + |(k : ℝ)|) ^ (-2 : ℝ))
      (summable_inv_one_add_sq_int.mul_left Real.pi) (fun k => ?_)
    dsimp only [g]
    rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, norm_mul]
    have h1 : ‖Complex.exp (↑(2 * Real.pi * ((k : ℝ) * α)) * Complex.I)‖ = 1 :=
      Complex.norm_exp_ofReal_mul_I _
    rw [h1, one_mul, hFf k, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hcexp : Complex.exp (-2 * Real.pi * Δ * |↑k|) = (Real.exp (-2 * Real.pi * Δ * |↑k|) : ℂ) := by
      have : (-2 * (Real.pi : ℂ) * ↑Δ * ↑|(k : ℝ)| : ℂ) = ((-2 * Real.pi * Δ * |(k : ℝ)| : ℝ) : ℂ) := by
        push_cast; ring
      rw [this, ← Complex.ofReal_exp]
    rw [hcexp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (exp_neg_le_inv_one_add_sq (by nlinarith [Real.two_le_pi])) Real.pi_pos.le
  have hg0 : g 0 = (Real.pi : ℂ) := by simp [g, hFf 0]
  have hsplit : (∑' k : ℤ, g k) - (Real.pi : ℂ) = ∑' k : ℤ, if k = 0 then (0 : ℂ) else g k := by
    rw [hg_summ.tsum_eq_add_tsum_ite (0 : ℤ), hg0, add_sub_cancel_left]
  have hre_bound : |(∑' k : ℤ, g k).re - Real.pi| ≤ ‖(∑' k : ℤ, g k) - (Real.pi : ℂ)‖ := by
    simpa [Complex.sub_re, Complex.ofReal_re] using Complex.abs_re_le_norm ((∑' k : ℤ, g k) - (Real.pi : ℂ))
  refine hre_bound.trans ?_
  rw [hsplit]
  have hnorm_sum : ‖∑' k : ℤ, (if k = 0 then (0 : ℂ) else g k)‖ ≤
      ∑' k : ℤ, ‖if k = 0 then (0 : ℂ) else g k‖ :=
    norm_tsum_le_tsum_norm (by
      refine hg_summ.norm.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
      split_ifs <;> simp)
  refine hnorm_sum.trans ?_
  have hnorm_g : ∀ k : ℤ, ‖g k‖ = Real.pi * Real.exp (-2 * Real.pi * Δ * |↑k|) := by
    intro k
    dsimp only [g]
    rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, norm_mul,
      Complex.norm_exp_ofReal_mul_I, one_mul, hFf k, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hcexp : Complex.exp (-2 * Real.pi * Δ * |↑k|) = (Real.exp (-2 * Real.pi * Δ * |↑k|) : ℂ) := by
      have : (-2 * (Real.pi : ℂ) * ↑Δ * ↑|(k : ℝ)| : ℂ) = ((-2 * Real.pi * Δ * |(k : ℝ)| : ℝ) : ℂ) := by
        push_cast; ring
      rw [this, ← Complex.ofReal_exp]
    rw [hcexp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hsumm_exp : Summable (fun k : ℤ => if k = 0 then (0 : ℝ) else Real.pi * Real.exp (-2 * Real.pi * Δ * |↑k|)) := by
    refine Summable.of_norm_bounded (g := fun k : ℤ => Real.pi * (1 + |(k : ℝ)|) ^ (-2 : ℝ))
      (summable_inv_one_add_sq_int.mul_left Real.pi) (fun k => ?_)
    split_ifs
    · simp; positivity
    · rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left (exp_neg_le_inv_one_add_sq (by nlinarith [Real.two_le_pi])) Real.pi_pos.le
  have heq_f : (fun k : ℤ => ‖if k = 0 then (0 : ℂ) else g k‖) =
      fun k : ℤ => if k = 0 then (0 : ℝ) else Real.pi * Real.exp (-2 * Real.pi * Δ * |↑k|) := by
    ext k; split_ifs <;> simp [hnorm_g]
  rw [heq_f, tsum_int_eq_zero_add_pos_add_neg hsumm_exp]
  sorry

lemma cauchy_sq_fourier (v : ℝ) (hv : 0 < v) (ξ : ℝ) :
    fourierHat (fun u : ℝ => 1 / ((u : ℂ) - Complex.I * v) ^ 2) ξ =
      if ξ < 0 then 4 * Real.pi ^ 2 * ξ * Complex.exp (2 * Real.pi * v * ξ) else 0 := by
  let g : ℝ → ℂ := fun y => if y < 0 then 4 * Real.pi ^ 2 * y * Complex.exp (2 * Real.pi * v * y) else 0
  have hg_cont : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro y
    rcases lt_trichotomy y 0 with hy | rfl | hy
    · have hev : g =ᶠ[nhds y] fun z => 4 * Real.pi ^ 2 * z * Complex.exp (2 * Real.pi * v * z) := by
        filter_upwards [eventually_lt_nhds hy] with z hz
        simp [g, hz]
      exact (ContinuousAt.congr (by fun_prop) hev.symm)
    · rw [ContinuousAt]
      have h0 : g 0 = 0 := by simp [g]
      rw [h0, Metric.tendsto_nhds_nhds]
      intro ε hε
      have hcont0 : ContinuousAt (fun z : ℝ => 4 * Real.pi ^ 2 * z * Complex.exp (2 * Real.pi * v * z)) 0 := by
        fun_prop
      rw [ContinuousAt, show (4 * (Real.pi : ℂ) ^ 2 * (0 : ℝ) * Complex.exp (2 * Real.pi * v * (0 : ℝ))) = 0 by simp,
        Metric.tendsto_nhds_nhds] at hcont0
      obtain ⟨δ, hδ, hδ_bd⟩ := hcont0 ε hε
      refine ⟨δ, hδ, fun z hz => ?_⟩
      by_cases hzn : z < 0
      · simpa [g, hzn] using hδ_bd hz
      · simpa [g, hzn] using hε
    · have hev : g =ᶠ[nhds y] fun _ => 0 := by
        filter_upwards [eventually_gt_nhds hy] with z hz
        simp [g, not_lt.mpr hz.le]
      exact (ContinuousAt.congr continuousAt_const hev.symm)
  have hg_int_Ioi_neg : IntegrableOn (fun t : ℝ => (t : ℂ) * Complex.exp (-2 * Real.pi * v * t)) (Set.Ioi (0 : ℝ)) := by
    have h1 : IntegrableOn (fun t : ℝ => Real.exp (-Real.pi * v * t)) (Set.Ioi (0 : ℝ)) := by
      have h_c : IntegrableOn (fun t : ℝ => Complex.exp ((-Real.pi * v : ℂ) * t)) (Set.Ioi (0 : ℝ)) :=
        integrableOn_exp_mul_complex_Ioi (by simp; positivity) 0
      refine h_c.norm.congr_fun (fun t _ => ?_) measurableSet_Ioi
      have : (-Real.pi * v * t : ℂ) = ((-Real.pi * v * t : ℝ) : ℂ) := by push_cast; ring
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), this, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine (h1.const_mul (1 / (Real.pi * v))).mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hcexp : Complex.exp (-2 * Real.pi * v * t) = (Real.exp (-2 * Real.pi * v * t) : ℂ) := by
      have : (-2 * (Real.pi : ℂ) * ↑v * ↑t : ℂ) = ((-2 * Real.pi * v * t : ℝ) : ℂ) := by push_cast; ring
      rw [this, ← Complex.ofReal_exp]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0, hcexp, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h_lin : Real.pi * v * t ≤ Real.exp (Real.pi * v * t) := by
      linarith [Real.add_one_le_exp (Real.pi * v * t)]
    have h_mul : Real.exp (-2 * Real.pi * v * t) = Real.exp (-Real.pi * v * t) * Real.exp (-Real.pi * v * t) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h_mul]
    calc t * (Real.exp (-Real.pi * v * t) * Real.exp (-Real.pi * v * t))
        = (Real.pi * v * t) * (1 / (Real.pi * v)) * Real.exp (-Real.pi * v * t) * Real.exp (-Real.pi * v * t) := by
          field_simp [Real.pi_ne_zero, hv.ne']
      _ ≤ Real.exp (Real.pi * v * t) * (1 / (Real.pi * v)) * Real.exp (-Real.pi * v * t) * Real.exp (-Real.pi * v * t) := by
          gcongr
      _ = 1 / (Real.pi * v) * Real.exp (-Real.pi * v * t) := by
          rw [mul_assoc (Real.exp (Real.pi * v * t)), mul_comm (1 / (Real.pi * v)), ← mul_assoc,
            ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul, mul_comm]
  have hg_int_Iio : IntegrableOn g (Set.Iio (0 : ℝ)) := by
    have hpre : (fun t : ℝ => -t) ⁻¹' Set.Ioi (0 : ℝ) = Set.Iio (0 : ℝ) := by ext t; simp
    have hcomp : IntegrableOn (fun t : ℝ => (-4 * Real.pi ^ 2 : ℂ) * ((-t : ℝ) * Complex.exp (-2 * Real.pi * v * (-t)))) (Set.Iio (0 : ℝ)) := by
      simpa [hpre] using (hg_int_Ioi_neg.const_mul (-4 * Real.pi ^ 2 : ℂ)).comp_neg
    refine hcomp.congr_fun (fun t ht => ?_) measurableSet_Iio
    have ht0 : t < 0 := ht
    dsimp only [g]
    rw [if_pos ht0]
    push_cast; ring
  have hg_int_Ioi : IntegrableOn g (Set.Ioi (0 : ℝ)) := by
    refine (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℂ)) (Set.Ioi 0)).congr_fun ?_ measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := ht
    simp [g, not_lt.mpr ht0.le]
  have hg_int : Integrable g := by
    rw [← integrableOn_univ]
    have hIic : IntegrableOn g (Set.Iic (0 : ℝ)) := hg_int_Iio.congr_set_ae Iio_ae_eq_Iic.symm
    have huniv : Set.Iic (0 : ℝ) ∪ Set.Ioi (0 : ℝ) = Set.univ := by ext t; simp [le_or_gt]
    rw [← huniv]
    exact hIic.union hg_int_Ioi
  have hFg : ∀ x : ℝ, 𝓕 g x = 1 / ((x : ℂ) + Complex.I * v) ^ 2 := by
    intro x
    rw [← fourierHat_eq_fourier]
    unfold fourierHat
    have h_int_exp : Integrable (fun y : ℝ => g y * Complex.exp (-2 * Real.pi * Complex.I * x * y)) := by
      refine hg_int.norm.mono (by fun_prop) ?_
      filter_upwards with y
      have hn : ‖Complex.exp (-2 * Real.pi * Complex.I * x * y)‖ = 1 := by
        have : -2 * (Real.pi : ℂ) * Complex.I * ↑x * ↑y = ((-2 * Real.pi * x * y : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I]
      rw [norm_mul, hn, mul_one, norm_norm]
    have hIic_eq : (∫ y in Set.Iic (0 : ℝ), g y * Complex.exp (-2 * Real.pi * Complex.I * x * y)) =
        ∫ y in Set.Iio (0 : ℝ), g y * Complex.exp (-2 * Real.pi * Complex.I * x * y) :=
      setIntegral_congr_set Iio_ae_eq_Iic.symm
    have hIoi_zero : (∫ y in Set.Ioi (0 : ℝ), g y * Complex.exp (-2 * Real.pi * Complex.I * x * y)) = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
      simp [g, not_lt.mpr (Set.mem_Ioi.mp hy).le]
    have hsplit : (∫ y : ℝ, g y * Complex.exp (-2 * Real.pi * Complex.I * x * y)) =
        (∫ y in Set.Iic (0 : ℝ), g y * Complex.exp (-2 * Real.pi * Complex.I * x * y)) +
        (∫ y in Set.Ioi (0 : ℝ), g y * Complex.exp (-2 * Real.pi * Complex.I * x * y)) := by
      have hc : (Set.Ioi (0 : ℝ))ᶜ = Set.Iic (0 : ℝ) := by ext y; simp
      rw [← hc]
      exact (integral_add_compl measurableSet_Ioi h_int_exp).symm.trans (add_comm _ _)
    rw [hsplit, hIic_eq, hIoi_zero, add_zero, integral_Iio_zero_eq_Ioi]
    set c : ℂ := 2 * Real.pi * (v - Complex.I * x)
    have hc_re : 0 < c.re := by simp [c]; positivity
    have hc_ne : c ≠ 0 := by intro h; rw [h] at hc_re; simp at hc_re
    have heq_Ioi : Set.EqOn (fun t : ℝ => g (-t) * Complex.exp (-2 * Real.pi * Complex.I * x * ((-t : ℝ) : ℂ)))
        (fun t : ℝ => (-4 * Real.pi ^ 2 : ℂ) * ((t : ℂ) * Complex.exp (-c * t))) (Set.Ioi 0) := by
      intro t ht
      have ht0 : 0 < t := ht
      dsimp only [g, c]
      rw [if_pos (neg_lt_zero.mpr ht0), mul_assoc, mul_assoc, ← Complex.exp_add]
      congr 2
      · push_cast; ring
      · congr 1; push_cast; ring
    rw [setIntegral_congr_fun measurableSet_Ioi heq_Ioi, integral_const_mul]
    have h_int_tc : IntegrableOn (fun t : ℝ => (t : ℂ) * Complex.exp (-c * t)) (Set.Ioi 0) := by
      refine hg_int_Ioi_neg.norm.mono (by fun_prop) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hnorm_c : ‖Complex.exp (-c * t)‖ = Real.exp (-2 * Real.pi * v * t) := by
        rw [Complex.norm_exp]
        congr 1
        simp [c]
        ring
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, hnorm_c,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
        show Complex.exp (-2 * Real.pi * v * t) = (Real.exp (-2 * Real.pi * v * t) : ℂ) by
          have : (-2 * (Real.pi : ℂ) * ↑v * ↑t : ℂ) = ((-2 * Real.pi * v * t : ℝ) : ℂ) := by push_cast; ring
          rw [this, ← Complex.ofReal_exp],
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    let G : ℝ → ℂ := fun t => -(t / c + 1 / c ^ 2) * Complex.exp (-c * t)
    have hG_deriv : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt G ((t : ℂ) * Complex.exp (-c * t)) t := by
      intro t _
      have hd1 : HasDerivAt (fun s : ℝ => -(s / c + 1 / c ^ 2)) (-(1 / c)) t := by
        have h := ((hasDerivAt_id t).ofReal_comp.div_const c).add_const (1 / c ^ 2)
        simpa using h.neg
      have hd2 : HasDerivAt (fun s : ℝ => Complex.exp (-c * s)) (Complex.exp (-c * t) * (-c)) t :=
        ((hasDerivAt_id t).ofReal_comp.const_mul (-c)).cexp
      convert hd1.mul hd2 using 1
      field_simp [hc_ne]
      ring
    have hG_tend : Tendsto G atTop (nhds 0) := by
      have h_norm : Tendsto (fun t : ℝ => ‖G t‖) atTop (nhds 0) := by
        have h_bnd : ∀ᶠ t : ℝ in atTop, ‖G t‖ ≤ (t / ‖c‖ + 1 / ‖c‖ ^ 2) * Real.exp (-2 * Real.pi * v * t) := by
          filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
          dsimp only [G]
          have hnorm_c : ‖Complex.exp (-c * t)‖ = Real.exp (-2 * Real.pi * v * t) := by
            rw [Complex.norm_exp]
            congr 1; simp [c]; ring
          rw [norm_mul, norm_neg, hnorm_c]
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          calc ‖(t : ℂ) / c + 1 / c ^ 2‖
              ≤ ‖(t : ℂ) / c‖ + ‖1 / c ^ 2‖ := norm_add_le _ _
            _ = t / ‖c‖ + 1 / ‖c‖ ^ 2 := by
                rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht,
                  norm_div, norm_one, norm_pow]
        have h_lim : Tendsto (fun t : ℝ => (t / ‖c‖ + 1 / ‖c‖ ^ 2) * Real.exp (-2 * Real.pi * v * t)) atTop (nhds 0) := by
          have h1 : Tendsto (fun t : ℝ => t * Real.exp (-(2 * Real.pi * v) * t)) atTop (nhds 0) := by
            simpa [mul_comm] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 |>.comp
              (tendsto_id.const_mul_atTop (by positivity : 0 < 2 * Real.pi * v)) |>.const_mul (1 / (2 * Real.pi * v))
          have h2 : Tendsto (fun t : ℝ => Real.exp (-(2 * Real.pi * v) * t)) atTop (nhds 0) :=
            Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by positivity : -(2 * Real.pi * v) < 0))
          have heq : (fun t : ℝ => (t / ‖c‖ + 1 / ‖c‖ ^ 2) * Real.exp (-2 * Real.pi * v * t)) =
              (fun t : ℝ => (1 / ‖c‖) * (t * Real.exp (-(2 * Real.pi * v) * t)) +
                (1 / ‖c‖ ^ 2) * Real.exp (-(2 * Real.pi * v) * t)) := by
            ext t; ring
          rw [heq]
          simpa using ((h1.const_mul (1 / ‖c‖)).add (h2.const_mul (1 / ‖c‖ ^ 2)))
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim
          (Eventually.of_forall fun _ => norm_nonneg _) h_bnd
      exact tendsto_zero_iff_norm_tendsto_zero.mpr h_norm
    have h_res := integral_Ioi_of_hasDerivAt_of_tendsto' hG_deriv h_int_tc hG_tend
    have hG0 : G 0 = -(1 / c ^ 2) := by simp [G]
    rw [h_res, hG0, zero_sub, neg_neg]
    have h_den : (x : ℂ) + Complex.I * v ≠ 0 := by
      intro h; have := congr_arg Complex.im h; simp at this; linarith
    dsimp only [c]
    field_simp [Real.pi_ne_zero, hc_ne, h_den]
    simp only [Complex.I_sq]
    ring
  have hFg_int : Integrable (𝓕 g) := by
    rw [show 𝓕 g = fun x : ℝ => 1 / ((x : ℂ) + Complex.I * v) ^ 2 from funext hFg]
    have hreal : Integrable (fun x : ℝ => 1 / (x ^ 2 + v ^ 2)) := by
      have hr : (1 / v : ℝ) ≠ 0 := by positivity
      refine ((integrable_inv_one_add_mul_sq hr).const_mul (1 / v ^ 2)).congr (ae_of_all _ fun x => ?_)
      field_simp [hv.ne']; ring
    refine hreal.norm.mono (by fun_prop) ?_
    filter_upwards with x
    rw [norm_div, norm_one, norm_pow]
    have hsq : ‖(x : ℂ) + Complex.I * v‖ ^ 2 = x ^ 2 + v ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp; ring
    rw [hsq, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hinv := congr_fun (Continuous.fourierInv_fourier_eq hg_cont hg_int hFg_int) ξ
  rw [fourierInv_eq_fourierHat_neg] at hinv
  have heq_f : fourierHat (𝓕 g) (-ξ) = fourierHat (fun u : ℝ => 1 / ((u : ℂ) - Complex.I * v) ^ 2) ξ := by
    unfold fourierHat
    rw [← integral_neg_eq_self (μ := volume)]
    congr 1; ext u
    rw [hFg (-u)]
    have : ((-u : ℝ) : ℂ) + Complex.I * v = -((u : ℂ) - Complex.I * v) := by push_cast; ring
    rw [this, neg_sq]
    congr 2; push_cast; ring
  rw [← heq_f, hinv]

/-! ### Helper Lemmas for `J(y, θ)` (Lemma 3.3) -/

private def cTheta (θ v : ℝ) : ℂ :=
  Complex.exp (-Complex.I * θ) / Complex.cos (θ + Complex.I * Real.pi * v) ^ 2

private def uTheta (θ v : ℝ) : ℂ :=
  Real.exp (-Real.pi * v) / (Real.pi * Complex.cos (θ + Complex.I * Real.pi * v))

private lemma cos_normSq_eq (θ v : ℝ) :
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
    simp only [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.ofReal_cos, Complex.ofReal_sin]
    push_cast; ring
  rw [← Complex.normSq_eq_norm_sq, hcos, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.sub_im, Complex.mul_im,
    zero_sub, neg_mul]
  have hch := Real.cosh_sq (Real.pi * v)
  have hcs := Real.cos_sq_add_sin_sq θ
  nlinarith

private lemma cos_ne_zero_of_abs_lt {θ v : ℝ} (hθ : |θ| < Real.pi / 2) :
    Complex.cos (θ + Complex.I * Real.pi * v) ≠ 0 := by
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  intro h
  have hsq := cos_normSq_eq θ v
  rw [h, norm_zero, zero_pow two_ne_zero] at hsq
  nlinarith [sq_nonneg (Real.sinh (Real.pi * v)), sq_pos_of_pos hcos_pos]

private lemma cTheta_norm_le {θ v : ℝ} (hθ : |θ| < Real.pi / 2) (hv : 0 ≤ v) :
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
        rw [Real.exp_neg]; field_simp [hcos_pos.ne']

private lemma uTheta_deriv {θ v : ℝ} (hθ : |θ| < Real.pi / 2) :
    HasDerivAt (fun t : ℝ => -uTheta θ t) (cTheta θ v) v := by
  have hcos_ne := cos_ne_zero_of_abs_lt (v := v) hθ
  have hw : HasDerivAt (fun t : ℝ => (θ : ℂ) + Complex.I * Real.pi * t) (Complex.I * Real.pi) v := by
    have h := (hasDerivAt_id v).ofReal_comp.const_mul (Complex.I * Real.pi)
    simpa using h.const_add (θ : ℂ)
  have hcos_d := hw.cos
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
      rw [Complex.exp_neg, ← Complex.cos_sub_I_sin]
      ring_nf
    rw [h1, show -Complex.I * ((θ : ℂ) + Complex.I * Real.pi * v) =
        -Complex.I * θ + ((Real.pi * v : ℝ) : ℂ) by push_cast; ring_nf; simp [Complex.I_sq],
      Complex.exp_add, Complex.ofReal_exp, ← mul_assoc, ← Complex.ofReal_exp, ← Real.exp_add]
    simp
  dsimp only [cTheta]
  rw [hcexp]
  field_simp [Real.pi_ne_zero, hcos_ne]
  simp only [Complex.I_sq]
  ring

private lemma cTheta_integrableOn {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    IntegrableOn (fun v : ℝ => cTheta θ v) (Set.Ioi 0) := by
  have h_exp : IntegrableOn (fun v : ℝ => Real.exp (-2 * Real.pi * v)) (Set.Ioi 0) := by
    have h_c : IntegrableOn (fun v : ℝ => Complex.exp ((-2 * Real.pi : ℂ) * v)) (Set.Ioi 0) :=
      integrableOn_exp_mul_complex_Ioi (by simp; positivity) 0
    refine h_c.norm.congr_fun (fun v _ => ?_) measurableSet_Ioi
    have : (-2 * (Real.pi : ℂ) * ↑v : ℂ) = ((-2 * Real.pi * v : ℝ) : ℂ) := by push_cast; ring
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), this, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hmeas : AEStronglyMeasurable (fun v : ℝ => cTheta θ v) (volume.restrict (Set.Ioi 0)) := by
    refine Continuous.aestronglyMeasurable ?_
    refine continuous_const.div (Continuous.pow (Continuous.cos (by fun_prop)) 2) (fun v => ?_)
    exact pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ)
  refine (h_exp.const_mul (4 / Real.cos θ ^ 2)).mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact cTheta_norm_le hθ hv.le

private lemma cTheta_integral_eq {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
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
            gcongr
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

private lemma cTheta_im_integral_zero {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    (∫ v in Set.Ioi (0 : ℝ), (cTheta θ v).im) = 0 := by
  have him : (∫ v in Set.Ioi (0 : ℝ), (cTheta θ v).im) = (∫ v in Set.Ioi (0 : ℝ), cTheta θ v).im :=
    (Complex.im_integral (cTheta_integrableOn hθ)).symm
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
    have h2 : starRingEnd ℂ (Complex.cos (θ + Complex.I * Real.pi * v)) =
        Complex.cos ((-θ : ℝ) + Complex.I * Real.pi * v) := by
      rw [← Complex.cos_conj, ← Complex.cos_neg]
      congr 1
      simp [map_add, map_mul, Complex.conj_I]
      ring
    have h3 : starRingEnd ℂ ((y : ℂ) - Complex.I * v) = -((-y : ℝ) - Complex.I * v) := by
      simp [map_sub, map_mul, Complex.conj_I]
      ring
    rw [map_div₀, map_mul, map_pow, h1, h2, h3]
    push_cast; ring
  rw [hconj, Complex.neg_im, Complex.conj_im, neg_neg]

/-- **Lemma 3.3 (Part 2)**: Near-zero asymptotic `J(y, θ) = (1/cos θ) log(1/|y|) + O_θ(1)`. -/
theorem limitingJ_near_zero (θ : ℝ) (hθ : |θ| < Real.pi / 2) :
    ∃ C_0 > 0, ∀ y : ℝ, 0 < |y| → |y| ≤ 1 →
      |limitingJ y θ - (1 / Real.cos θ) * Real.log (1 / |y|)| ≤ C_0 := by
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  have hc_int := cTheta_integrableOn hθ
  have hB_bound : ∃ C_B > 0, ∀ v : ℝ, 0 ≤ v → |(cTheta θ v).im| ≤ C_B := by
    refine ⟨4 / Real.cos θ ^ 2, by positivity, fun v hv => ?_⟩
    exact (Complex.abs_im_le_abs _).trans ((cTheta_norm_le hθ hv).trans
      (mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos]))))
  obtain ⟨C_B, hC_B, hB_bd⟩ := hB_bound
  have hA_bound : ∃ C_A > 0, ∀ v : ℝ, 0 ≤ v → v ≤ 1 → |(cTheta θ v).re - 1 / Real.cos θ| ≤ C_A * v := by
    have hderiv_bd : ∃ C_A > 0, ∀ v ∈ Set.Icc (0 : ℝ) 1,
        ‖deriv (fun t : ℝ => (cTheta θ t).re) v‖ ≤ C_A := by
      let f : ℝ → ℝ := fun t => ‖deriv (fun s : ℝ => (cTheta θ s).re) t‖
      have hc_diff : Differentiable ℝ (fun t : ℝ => cTheta θ t) := by
        intro t
        have hw : DifferentiableAt ℝ (fun s : ℝ => (θ : ℂ) + Complex.I * Real.pi * s) t :=
          (differentiableAt_id.ofReal_comp.const_mul _).const_add _
        exact (differentiableAt_const _).div (hw.cos.pow 2) (pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ))
      have hf_cont : Continuous f := by
        dsimp only [f]
        have hc_c1 : ContDiff ℝ 1 (fun t : ℝ => cTheta θ t) := by
          refine ContDiff.div contDiff_const (ContDiff.pow (ContDiff.cos ?_) 2) (fun t => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ))
          exact contDiff_const.add (contDiff_const.mul Complex.ofRealCLM.contDiff)
        exact (hc_c1.continuous_deriv (by norm_num) |> fun h => (Complex.continuous_re.comp h).norm).congr fun t => by
          rw [show (deriv (fun s : ℝ => (cTheta θ s).re) t) = (deriv (fun s : ℝ => cTheta θ s) t).re from
            (Complex.reCLM.hasFDerivAt.comp t (hc_diff t).hasDerivAt.hasFDerivAt).deriv]
      obtain ⟨v₀, _, hv₀⟩ := isCompact_Icc.exists_isMaxOn (⟨0, by norm_num, by norm_num⟩ : (Set.Icc (0 : ℝ) 1).Nonempty) hf_cont.continuousOn
      refine ⟨max 1 (f v₀), by positivity, fun v hv => (hv₀ hv).trans (le_max_right _ _)⟩
    obtain ⟨C_A, hC_A, hbd⟩ := hderiv_bd
    refine ⟨C_A, hC_A, fun v hv0 hv1 => ?_⟩
    have h0 : (cTheta θ 0).re = 1 / Real.cos θ := by
      simp only [cTheta, mul_zero, add_zero, Complex.exp_neg, Complex.cos_ofReal_re]
      rw [show Complex.cos (θ : ℂ) = (Real.cos θ : ℂ) from (Complex.ofReal_cos θ).symm,
        show Complex.exp (-(Complex.I * (θ : ℂ))) = Complex.cos θ - Complex.I * Complex.sin θ by
          rw [Complex.exp_neg, ← Complex.cos_sub_I_sin]; simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]]
      rw [sub_div, Complex.sub_re]
      have hre1 : ((Real.cos θ : ℂ) / (Real.cos θ : ℂ) ^ 2).re = 1 / Real.cos θ := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]
        field_simp [hcos_pos.ne']
      have him1 : (Complex.I * (Real.sin θ : ℂ) / (Real.cos θ : ℂ) ^ 2).re = 0 := by
        rw [mul_div_assoc, ← Complex.ofReal_pow, ← Complex.ofReal_div]
        simp
      rw [hre1, him1, sub_zero]
    rw [← h0]
    have hdiff_on : ∀ t ∈ Set.Icc (0 : ℝ) v,
        HasDerivWithinAt (fun s : ℝ => (cTheta θ s).re) (deriv (fun s : ℝ => (cTheta θ s).re) t) (Set.Icc 0 v) t := by
      intro t _
      have hc_diff : DifferentiableAt ℝ (fun s : ℝ => cTheta θ s) t := by
        have hw : DifferentiableAt ℝ (fun s : ℝ => (θ : ℂ) + Complex.I * Real.pi * s) t :=
          (differentiableAt_id.ofReal_comp.const_mul _).const_add _
        exact (differentiableAt_const _).div (hw.cos.pow 2) (pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ))
      exact (Complex.reCLM.hasFDerivAt.comp t hc_diff.hasDerivAt.hasFDerivAt).hasDerivAt.hasDerivWithinAt
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => hdiff_on t ht) (fun t ht => hbd t ⟨ht.1, ht.2.trans hv1⟩) (convex_Icc 0 v)
      (by simp [hv0]) (by simp [hv0])
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
      field_simp [h1, h2]; simp only [Complex.I_sq]; push_cast; ring
    rw [div_eq_mul_inv, ← one_div, hinv, mul_div_assoc', ← Complex.ofReal_div]
    have hre_im : (cTheta θ v * ((y : ℂ) + Complex.I * v)).im =
        v * (cTheta θ v).re + y * (cTheta θ v).im := by
      simp [Complex.mul_im]; ring
    rw [Complex.div_ofReal_im, hre_im]
  have hJ_eq : limitingJ y θ =
      (∫ v in Set.Ioi (0 : ℝ), v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) +
      (∫ v in Set.Ioi (0 : ℝ), y * (cTheta θ v).im / (y ^ 2 + v ^ 2)) := by
    unfold limitingJ
    have h1 : IntegrableOn (fun v : ℝ => v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) (Set.Ioi 0) := by
      have h_v : IntegrableOn (fun v : ℝ => ‖cTheta θ v‖ * (1 / |y|)) (Set.Ioi 0) :=
        hc_int.norm.mul_const _
      refine h_v.mono' (Continuous.aestronglyMeasurable (by
        refine (continuous_id.mul (Complex.continuous_re.comp ?_)).div (by fun_prop) (fun v => by positivity)
        refine continuous_const.div (Continuous.pow (Continuous.cos (by fun_prop)) 2) (fun v => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ)))) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < y ^ 2 + v ^ 2), abs_mul, abs_of_pos hv]
      have h2 : v / (y ^ 2 + v ^ 2) ≤ 1 / |y| := by
        rw [div_le_div_iff₀ (by positivity) hy0]
        nlinarith [sq_nonneg (v - |y|), sq_abs y]
      calc v * |(cTheta θ v).re| / (y ^ 2 + v ^ 2)
          = |(cTheta θ v).re| * (v / (y ^ 2 + v ^ 2)) := by ring
        _ ≤ ‖cTheta θ v‖ * (1 / |y|) := mul_le_mul (Complex.abs_re_le_abs _) h2 (by positivity) (norm_nonneg _)
    have h2 : IntegrableOn (fun v : ℝ => y * (cTheta θ v).im / (y ^ 2 + v ^ 2)) (Set.Ioi 0) := by
      have h_y : IntegrableOn (fun v : ℝ => ‖cTheta θ v‖ * (1 / |y|)) (Set.Ioi 0) :=
        hc_int.norm.mul_const _
      refine h_y.mono' (Continuous.aestronglyMeasurable (by
        refine (continuous_const.mul (Complex.continuous_im.comp ?_)).div (by fun_prop) (fun v => by positivity)
        refine continuous_const.div (Continuous.pow (Continuous.cos (by fun_prop)) 2) (fun v => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ)))) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < y ^ 2 + v ^ 2), abs_mul]
      have h3 : |y| / (y ^ 2 + v ^ 2) ≤ 1 / |y| := by
        rw [div_le_div_iff₀ (by positivity) hy0]
        nlinarith [sq_nonneg v, sq_abs y]
      calc |y| * |(cTheta θ v).im| / (y ^ 2 + v ^ 2)
          = |(cTheta θ v).im| * (|y| / (y ^ 2 + v ^ 2)) := by ring
        _ ≤ ‖cTheta θ v‖ * (1 / |y|) := mul_le_mul (Complex.abs_im_le_abs _) h3 (by positivity) (norm_nonneg _)
    rw [← integral_add h1 h2]
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    rw [h_integrand v hv.le]
    ring
  have hB_int_le : |∫ v in Set.Ioi (0 : ℝ), y * (cTheta θ v).im / (y ^ 2 + v ^ 2)| ≤ C_B * (Real.pi / 2) := by
    have h_abs : |∫ v in Set.Ioi (0 : ℝ), y * (cTheta θ v).im / (y ^ 2 + v ^ 2)| ≤
        ∫ v in Set.Ioi (0 : ℝ), C_B * (|y| / (y ^ 2 + v ^ 2)) := by
      have h_int_abs : IntegrableOn (fun v : ℝ => C_B * (|y| / (y ^ 2 + v ^ 2))) (Set.Ioi 0) := by
        have hr : (1 / |y| : ℝ) ≠ 0 := by positivity
        have h1 := ((integrable_inv_one_add_mul_sq hr).integrableOn : IntegrableOn _ (Set.Ioi 0)).const_mul C_B
        refine h1.congr_fun (fun v _ => ?_) measurableSet_Ioi
        field_simp [hy0.ne']; rw [sq_abs]
      calc |∫ v in Set.Ioi (0 : ℝ), y * (cTheta θ v).im / (y ^ 2 + v ^ 2)|
          ≤ ∫ v in Set.Ioi (0 : ℝ), ‖y * (cTheta θ v).im / (y ^ 2 + v ^ 2)‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ v in Set.Ioi (0 : ℝ), C_B * (|y| / (y ^ 2 + v ^ 2)) := by
            refine setIntegral_mono_on (by
              exact h_int_abs.mono' (by fun_prop) (by
                filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
                rw [Real.norm_eq_abs, abs_norm, abs_div, abs_of_pos (by positivity : 0 < y ^ 2 + v ^ 2), abs_mul]
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
        refine ((integrable_inv_one_add_mul_sq hr).integrableOn : IntegrableOn _ (Set.Ioi 0)).congr_fun (fun v _ => ?_) measurableSet_Ioi
        field_simp [hy0.ne']; rw [sq_abs]
      have hderiv : ∀ v ∈ Set.Ici (0 : ℝ), HasDerivAt (fun t : ℝ => Real.arctan (t / |y|)) (|y| / (y ^ 2 + v ^ 2)) v := by
        intro v _
        have hd := ((hasDerivAt_id v).div_const |y|).arctan
        refine hd.congr_deriv ?_
        dsimp only [id_eq]
        field_simp [hy0.ne']; rw [sq_abs]
      have htend : Tendsto (fun t : ℝ => Real.arctan (t / |y|)) atTop (nhds (Real.pi / 2)) :=
        Real.tendsto_arctan_atTop.comp (tendsto_id.atTop_div_const hy0)
      rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv h_int_l htend]
      simp [Real.arctan_zero]
    rw [integral_const_mul, h_arctan_int] at h_abs
    exact h_abs
  have hA_split : (∫ v in Set.Ioi (0 : ℝ), v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) =
      (∫ v in Set.Ioc (0 : ℝ) 1, v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) +
      (∫ v in Set.Ioi (1 : ℝ), v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) := by
    have hun : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi (by norm_num)
    have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) := Set.Ioc_disjoint_Ioi_same
    have h_int_A : IntegrableOn (fun v : ℝ => v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) (Set.Ioi 0) := by
      have h_v : IntegrableOn (fun v : ℝ => ‖cTheta θ v‖ * (1 / |y|)) (Set.Ioi 0) := hc_int.norm.mul_const _
      refine h_v.mono' (Continuous.aestronglyMeasurable (by
        refine (continuous_id.mul (Complex.continuous_re.comp ?_)).div (by fun_prop) (fun v => by positivity)
        refine continuous_const.div (Continuous.pow (Continuous.cos (by fun_prop)) 2) (fun v => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ)))) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < y ^ 2 + v ^ 2), abs_mul, abs_of_pos hv]
      have h2 : v / (y ^ 2 + v ^ 2) ≤ 1 / |y| := by
        rw [div_le_div_iff₀ (by positivity) hy0]; nlinarith [sq_nonneg (v - |y|), sq_abs y]
      calc v * |(cTheta θ v).re| / (y ^ 2 + v ^ 2) = |(cTheta θ v).re| * (v / (y ^ 2 + v ^ 2)) := by ring
        _ ≤ ‖cTheta θ v‖ * (1 / |y|) := mul_le_mul (Complex.abs_re_le_abs _) h2 (by positivity) (norm_nonneg _)
    rw [← hun] at h_int_A
    rw [← hun, setIntegral_union hdisj measurableSet_Ioi (h_int_A.mono_set Set.subset_union_left)
      (h_int_A.mono_set Set.subset_union_right)]
  have hA_tail : |∫ v in Set.Ioi (1 : ℝ), v * (cTheta θ v).re / (y ^ 2 + v ^ 2)| ≤ I_tail := by
    calc |∫ v in Set.Ioi (1 : ℝ), v * (cTheta θ v).re / (y ^ 2 + v ^ 2)|
        ≤ ∫ v in Set.Ioi (1 : ℝ), ‖v * (cTheta θ v).re / (y ^ 2 + v ^ 2)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ v in Set.Ioi (1 : ℝ), ‖cTheta θ v‖ := by
          refine setIntegral_mono_on (by
            exact (hc_int.mono_set (Set.Ioi_subset_Ioi (by norm_num))).norm.mono' (by fun_prop) (by
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
              have hv1 : 1 < v := hv
              rw [Real.norm_eq_abs, abs_norm, abs_div, abs_of_pos (by positivity : 0 < y ^ 2 + v ^ 2),
                abs_mul, abs_of_pos (by linarith)]
              have hle : v / (y ^ 2 + v ^ 2) ≤ 1 := by
                rw [div_le_one (by positivity)]; nlinarith [sq_nonneg y]
              calc v * |(cTheta θ v).re| / (y ^ 2 + v ^ 2) = |(cTheta θ v).re| * (v / (y ^ 2 + v ^ 2)) := by ring
                _ ≤ ‖cTheta θ v‖ * 1 := mul_le_mul (Complex.abs_re_le_abs _) hle (by positivity) (norm_nonneg _)
                _ = ‖cTheta θ v‖ := mul_one _))
            (hc_int.mono_set (Set.Ioi_subset_Ioi (by norm_num))).norm measurableSet_Ioi fun v hv => ?_
          have hv1 : 1 < v := hv
          rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < y ^ 2 + v ^ 2),
            abs_mul, abs_of_pos (by linarith)]
          have hle : v / (y ^ 2 + v ^ 2) ≤ 1 := by
            rw [div_le_one (by positivity)]; nlinarith [sq_nonneg y]
          calc v * |(cTheta θ v).re| / (y ^ 2 + v ^ 2) = |(cTheta θ v).re| * (v / (y ^ 2 + v ^ 2)) := by ring
            _ ≤ ‖cTheta θ v‖ * 1 := mul_le_mul (Complex.abs_re_le_abs _) hle (by positivity) (norm_nonneg _)
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
        refine continuous_const.div (Continuous.pow (Continuous.cos (by fun_prop)) 2) (fun v => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ)))).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    have h2 : IntegrableOn (fun v : ℝ => v * (1 / Real.cos θ) / (y ^ 2 + v ^ 2)) (Set.Ioc 0 1) :=
      (Continuous.continuousOn ((continuous_id.mul continuous_const).div (by fun_prop) (fun v => by positivity))).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    rw [← integral_sub h1 h2]
    calc |∫ v in Set.Ioc (0 : ℝ) 1, (v * (cTheta θ v).re / (y ^ 2 + v ^ 2) - v * (1 / Real.cos θ) / (y ^ 2 + v ^ 2))|
        ≤ ∫ v in Set.Ioc (0 : ℝ) 1, ‖v * (cTheta θ v).re / (y ^ 2 + v ^ 2) - v * (1 / Real.cos θ) / (y ^ 2 + v ^ 2)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ v in Set.Ioc (0 : ℝ) 1, C_A := by
          refine setIntegral_mono_on (h1.sub h2).norm continuousOn_const.integrableOn_Ioc measurableSet_Ioc fun v hv => ?_
          rw [Real.norm_eq_abs, show v * (cTheta θ v).re / (y ^ 2 + v ^ 2) - v * (1 / Real.cos θ) / (y ^ 2 + v ^ 2) =
            (v / (y ^ 2 + v ^ 2)) * ((cTheta θ v).re - 1 / Real.cos θ) by ring,
            abs_mul, abs_div, abs_of_pos hv.1, abs_of_pos (by positivity : 0 < y ^ 2 + v ^ 2)]
          have hle1 : v ^ 2 / (y ^ 2 + v ^ 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith [sq_nonneg y]
          calc (v / (y ^ 2 + v ^ 2)) * |(cTheta θ v).re - 1 / Real.cos θ|
              ≤ (v / (y ^ 2 + v ^ 2)) * (C_A * v) := by gcongr; exact hA_bd v hv.1.le hv.2
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
  rw [hJ_eq, hA_split]
  have h_tri : limitingJ y θ - (1 / Real.cos θ) * Real.log (1 / |y|) =
      ((∫ v in Set.Ioc (0 : ℝ) 1, v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) -
        (∫ v in Set.Ioc (0 : ℝ) 1, v * (1 / Real.cos θ) / (y ^ 2 + v ^ 2))) +
      (1 / (2 * Real.cos θ)) * Real.log (y ^ 2 + 1) +
      (∫ v in Set.Ioi (1 : ℝ), v * (cTheta θ v).re / (y ^ 2 + v ^ 2)) +
      (∫ v in Set.Ioi (0 : ℝ), y * (cTheta θ v).im / (y ^ 2 + v ^ 2)) := by
    rw [← hJ_eq, ← hA_split, hJ_eq, hA_split, hA_main]; ring
  calc |limitingJ y θ - (1 / Real.cos θ) * Real.log (1 / |y|)|
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
  have hc_int := cTheta_integrableOn hθ
  have h_u_int : IntegrableOn (fun v : ℝ => uTheta θ v) (Set.Ioi 0) := by
    have h_exp : IntegrableOn (fun v : ℝ => Real.exp (-2 * Real.pi * v)) (Set.Ioi 0) := by
      have h_c : IntegrableOn (fun v : ℝ => Complex.exp ((-2 * Real.pi : ℂ) * v)) (Set.Ioi 0) :=
        integrableOn_exp_mul_complex_Ioi (by simp; positivity) 0
      refine h_c.norm.congr_fun (fun v _ => ?_) measurableSet_Ioi
      have : (-2 * (Real.pi : ℂ) * ↑v : ℂ) = ((-2 * Real.pi * v : ℝ) : ℂ) := by push_cast; ring
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), this, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hmeas : AEStronglyMeasurable (fun v : ℝ => uTheta θ v) (volume.restrict (Set.Ioi 0)) := by
      refine Continuous.aestronglyMeasurable ?_
      exact Continuous.div (by fun_prop) (continuous_const.mul (Continuous.cos (by fun_prop)))
        (fun v => mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (cos_ne_zero_of_abs_lt hθ))
    refine (h_exp.const_mul (2 / (Real.pi * Real.cos θ))).mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
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
    calc Real.exp (-Real.pi * v) / (Real.pi * ‖Complex.cos (↑θ + Complex.I * ↑π * ↑v)‖)
        ≤ Real.exp (-Real.pi * v) / (Real.pi * ((Real.cos θ / 2) * Real.exp (Real.pi * v))) := by gcongr
      _ = (2 / (Real.pi * Real.cos θ)) * Real.exp (-2 * Real.pi * v) := by
          rw [show -2 * Real.pi * v = -Real.pi * v - Real.pi * v by ring, Real.exp_sub]
          field_simp [Real.pi_ne_zero, hcos_pos.ne']
  have h_vc_int : IntegrableOn (fun v : ℝ => (v : ℂ) * cTheta θ v) (Set.Ioi 0) := by
    have h_exp : IntegrableOn (fun v : ℝ => Real.exp (-Real.pi * v)) (Set.Ioi 0) := by
      have h_c : IntegrableOn (fun v : ℝ => Complex.exp ((-Real.pi : ℂ) * v)) (Set.Ioi 0) :=
        integrableOn_exp_mul_complex_Ioi (by simp; positivity) 0
      refine h_c.norm.congr_fun (fun v _ => ?_) measurableSet_Ioi
      have : (-Real.pi * ↑v : ℂ) = ((-Real.pi * v : ℝ) : ℂ) := by push_cast; ring
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), this, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hmeas : AEStronglyMeasurable (fun v : ℝ => (v : ℂ) * cTheta θ v) (volume.restrict (Set.Ioi 0)) := by
      refine Continuous.aestronglyMeasurable ?_
      exact Complex.continuous_ofReal.mul (continuous_const.div (Continuous.pow (Continuous.cos (by fun_prop)) 2)
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
      refine h_c.norm.congr_fun (fun v _ => ?_) measurableSet_Ioi
      have : (-Real.pi * ↑v : ℂ) = ((-Real.pi * v : ℝ) : ℂ) := by push_cast; ring
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), this, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hmeas : AEStronglyMeasurable (fun v : ℝ => v ^ 2 * ‖cTheta θ v‖) (volume.restrict (Set.Ioi 0)) := by
      refine Continuous.aestronglyMeasurable ?_
      exact (continuous_pow 2).mul (Continuous.norm (continuous_const.div (Continuous.pow (Continuous.cos (by fun_prop)) 2)
        (fun v => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ))))
    refine (h_exp.const_mul (32 / (Real.pi ^ 2 * Real.cos θ ^ 2))).mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : (Real.pi * v / 2) ^ 2 / 2 ≤ Real.exp (Real.pi * v / 2) := by
      have h_s := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ Real.pi * v / 2) 3
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
        pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one,
        Nat.factorial_two, Nat.cast_ofNat] at h_s
      linarith
    have h2 : v ^ 2 * Real.exp (-2 * Real.pi * v) ≤ (8 / Real.pi ^ 2) * Real.exp (-Real.pi * v) := by
      have hsq : v ^ 2 ≤ (8 / Real.pi ^ 2) * Real.exp (Real.pi * v / 2) := by
        rw [le_div_iff₀ (by positivity)] at *; nlinarith
      have hexp : Real.exp (Real.pi * v / 2) * Real.exp (-2 * Real.pi * v) ≤ Real.exp (-Real.pi * v) := by
        rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith [Real.pi_pos]
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
      convert (hd1.mul hd2).congr_deriv ?_ using 1
      · ext t; simp; ring
      · simp; ring
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
          simpa [mul_comm] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 |>.comp
            (tendsto_id.const_mul_atTop (by positivity : 0 < 2 * Real.pi)) |>.const_mul (1 / (2 * Real.pi))
        simpa [mul_assoc] using h1.const_mul (2 / (Real.pi * Real.cos θ))
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim
        (Eventually.of_forall fun _ => norm_nonneg _) h_bnd
    have hres := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (h_u_int.neg.add h_vc_int) htend
    simp only [Complex.ofReal_zero, neg_zero, zero_mul, sub_zero] at hres
    rw [integral_add h_u_int.neg h_vc_int, integral_neg] at hres
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
          Complex.exp_add_mul_I]
        simp [Complex.exp_ofReal_re, Complex.cos_ofReal_re, Complex.sin_ofReal_im]
      rw [hre]
      have hcos2 : -1 < Real.cos (2 * θ) := by
        rw [Real.cos_two_mul]
        nlinarith [sq_pos_of_pos hcos_pos, Real.cos_sq_add_sin_sq θ]
      have hexp_le : Real.exp (-2 * Real.pi * v) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
      have hexp_pos : 0 < Real.exp (-2 * Real.pi * v) := Real.exp_pos _
      nlinarith
    have hderiv : ∀ v ∈ Set.Ici (0 : ℝ), HasDerivAt W (uTheta θ v) v := by
      intro v hv
      have hd1 : HasDerivAt (fun t : ℝ => 1 + Complex.exp (2 * Complex.I * θ - 2 * Real.pi * t))
          (Complex.exp (2 * Complex.I * θ - 2 * Real.pi * v) * (-2 * Real.pi)) v := by
        have h := ((hasDerivAt_id v).ofReal_comp.const_mul (-2 * (Real.pi : ℂ))).const_add (2 * Complex.I * θ)
        simpa [sub_eq_add_neg] using h.cexp.const_add (1 : ℂ)
      have hlog := hd1.clog (h_slit v hv)
      have hW := hlog.const_mul (-(1 / (Real.pi : ℂ) ^ 2) * Complex.exp (-Complex.I * θ))
      refine hW.congr_deriv ?_
      have hden_ne : 1 + Complex.exp (2 * Complex.I * θ - 2 * Real.pi * v) ≠ 0 :=
        Complex.slitPlane_ne_zero (h_slit v hv)
      have hcos_eq : Complex.cos (θ + Complex.I * Real.pi * v) =
          (Complex.exp (-Complex.I * θ + Real.pi * v) * (1 + Complex.exp (2 * Complex.I * θ - 2 * Real.pi * v))) / 2 := by
        rw [Complex.cos_eq_exp]
        have he1 : Complex.exp (Complex.I * (θ + Complex.I * Real.pi * v)) =
            Complex.exp (-Complex.I * θ + Real.pi * v) * Complex.exp (2 * Complex.I * θ - 2 * Real.pi * v) := by
          rw [← Complex.exp_add]; congr 1; push_cast; ring_nf; simp [Complex.I_sq]; ring
        have he2 : Complex.exp (-Complex.I * (θ + Complex.I * Real.pi * v)) =
            Complex.exp (-Complex.I * θ + Real.pi * v) := by
          congr 1; push_cast; ring_nf; simp [Complex.I_sq]; ring
        rw [he1, he2]; ring
      dsimp only [uTheta]
      rw [hcos_eq]
      have he_ne : Complex.exp (-Complex.I * θ + Real.pi * v) ≠ 0 := Complex.exp_ne_zero _
      field_simp [Real.pi_ne_zero, hden_ne, he_ne]
      have hexp_id : Complex.exp (-Complex.I * θ) * Complex.exp (2 * Complex.I * θ - 2 * Real.pi * v) *
          Complex.exp (-Complex.I * θ + Real.pi * v) = (Real.exp (-Real.pi * v) : ℂ) := by
        rw [← Complex.exp_add, ← Complex.exp_add, Complex.ofReal_exp]
        congr 1; push_cast; ring
      linear_combination -2 * Real.pi * hexp_id
    have htend : Tendsto W atTop (nhds 0) := by
      have h_lim_exp : Tendsto (fun v : ℝ => 1 + Complex.exp (2 * Complex.I * θ - 2 * Real.pi * v)) atTop (nhds 1) := by
        have h_zero : Tendsto (fun v : ℝ => Complex.exp (2 * Complex.I * θ - 2 * Real.pi * v)) atTop (nhds 0) := by
          rw [tendsto_zero_iff_norm_tendsto_zero]
          have heq : (fun v : ℝ => ‖Complex.exp (2 * Complex.I * θ - 2 * Real.pi * v)‖) =
              fun v => Real.exp (-(2 * Real.pi) * v) := by
            ext v
            rw [Complex.norm_exp]; congr 1; simp; ring
          rw [heq]
          exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by positivity : -(2 * Real.pi) < 0))
        simpa using tendsto_const_nhds.add h_zero
      have h_log := (Complex.continuousAt_clog (by simp : (1 : ℂ) ∈ Complex.slitPlane)).tendsto.comp h_lim_exp
      simpa [W, Complex.log_one] using tendsto_const_nhds.mul h_log
    have hres := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv h_u_int htend
    rw [hres, zero_sub]
    simp [W]; ring
  have h_main_re : (∫ v in Set.Ioi (0 : ℝ), (v : ℂ) * cTheta θ v).re = 2 * envelopeC θ / Real.pi ^ 2 := by
    rw [h_ibp, h_u_eval]
    have h_sum_exp : 1 + Complex.exp (2 * Complex.I * θ) = (2 * Real.cos θ : ℂ) * Complex.exp (Complex.I * θ) := by
      rw [Complex.cos_eq_exp]
      have h1 : Complex.exp (Complex.I * θ) * Complex.exp (-Complex.I * θ) = 1 := by
        rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      have h2 : Complex.exp (2 * Complex.I * θ) = Complex.exp (Complex.I * θ) * Complex.exp (Complex.I * θ) := by
        rw [← Complex.exp_add]; congr 1; ring
      rw [h2]; linear_combination -h1
    rw [h_sum_exp]
    have h_log_eq : Complex.log ((2 * Real.cos θ : ℂ) * Complex.exp (Complex.I * θ)) =
        (Real.log (2 * Real.cos θ) : ℂ) + Complex.I * θ := by
      have hpos_c : 0 < 2 * Real.cos θ := by positivity
      have harg1 : ((2 * Real.cos θ : ℝ) : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg hpos_c.le
      have harg2 : (Complex.exp (Complex.I * θ)).arg = θ := by
        rw [mul_comm, Complex.arg_exp_mul_I_eq_iff.mpr]
        have := abs_lt.mp hθ; constructor <;> linarith [Real.pi_pos]
      have hadd : ((2 * Real.cos θ : ℝ) : ℂ).arg + (Complex.exp (Complex.I * θ)).arg ∈ Set.Ioc (-Real.pi) Real.pi := by
        rw [harg1, harg2, zero_add]
        have := abs_lt.mp hθ; constructor <;> linarith [Real.pi_pos]
      rw [Complex.log_mul (by exact_mod_cast hpos_c.ne') (Complex.exp_ne_zero _) hadd,
        ← Complex.ofReal_log hpos_c.le, Complex.log_exp]
      · simp [mul_comm]
      · have := abs_lt.mp hθ; simp; constructor <;> linarith [Real.pi_pos]
      · have := abs_lt.mp hθ; simp; constructor <;> linarith [Real.pi_pos]
    rw [h_log_eq]
    have hexp_re_im : Complex.exp (-Complex.I * θ) = (Real.cos θ : ℂ) - Complex.I * (Real.sin θ : ℂ) := by
      rw [Complex.exp_neg, ← Complex.cos_sub_I_sin]; simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    rw [hexp_re_im]
    simp only [div_mul_eq_mul_div, Complex.div_ofReal_re, Complex.mul_re, Complex.sub_re,
      Complex.ofReal_re, Complex.mul_im, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
      mul_one, sub_zero, zero_add, Complex.add_re, Complex.add_im, Complex.sub_im,
      zero_sub, neg_mul, sub_neg_eq_add]
    unfold envelopeC
    ring
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
    ring
  have h_int_1 : IntegrableOn (fun v : ℝ => (cTheta θ v / (y : ℂ)).im) (Set.Ioi 0) :=
    (hc_int.div_const (y : ℂ)).im
  have h_int_2 : IntegrableOn (fun v : ℝ => (Complex.I * ((v : ℂ) * cTheta θ v) / (y : ℂ) ^ 2).im) (Set.Ioi 0) :=
    ((h_vc_int.const_mul Complex.I).div_const ((y : ℂ) ^ 2)).im
  have h_int_3 : IntegrableOn (fun v : ℝ => ((cTheta θ v * (v : ℂ) ^ 2) / ((y : ℂ) ^ 2 * ((y : ℂ) - Complex.I * v))).im) (Set.Ioi 0) := by
    refine (h_v2c_int.div_const (|y| ^ 3)).mono' (Continuous.aestronglyMeasurable (Complex.continuous_im.comp (by
      refine Continuous.div ?_ ?_ (fun v => ?_)
      · exact (continuous_const.div (Continuous.pow (Continuous.cos (by fun_prop)) 2)
          (fun v => pow_ne_zero 2 (cos_ne_zero_of_abs_lt hθ))).mul (by fun_prop)
      · exact continuous_const.mul (continuous_const.sub (continuous_const.mul Complex.continuous_ofReal))
      · refine mul_ne_zero (pow_ne_zero 2 (by exact_mod_cast hy_ne)) ?_
        intro h; have := congr_arg Complex.re h; simp at this; exact hy_ne this))) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
    rw [Real.norm_eq_abs, abs_norm]
    refine (Complex.abs_im_le_abs _).trans ?_
    rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have hden : |y| ≤ ‖(y : ℂ) - Complex.I * v‖ := by
      have : |y| = ‖((y : ℂ) - Complex.I * v).re‖ := by simp [Real.norm_eq_abs]
      rw [this]; exact Complex.abs_re_le_abs _
    calc ‖cTheta θ v‖ * |v| ^ 2 / (|y| ^ 2 * ‖(y : ℂ) - Complex.I * v‖)
        ≤ ‖cTheta θ v‖ * v ^ 2 / (|y| ^ 2 * |y|) := by rw [sq_abs]; gcongr
      _ = v ^ 2 * ‖cTheta θ v‖ / |y| ^ 3 := by ring
  have hJ_split : limitingJ y θ =
      (∫ v in Set.Ioi (0 : ℝ), (cTheta θ v / (y : ℂ)).im) +
      (∫ v in Set.Ioi (0 : ℝ), (Complex.I * ((v : ℂ) * cTheta θ v) / (y : ℂ) ^ 2).im) -
      (∫ v in Set.Ioi (0 : ℝ), ((cTheta θ v * (v : ℂ) ^ 2) / ((y : ℂ) ^ 2 * ((y : ℂ) - Complex.I * v))).im) := by
    unfold limitingJ
    rw [← integral_add h_int_1 h_int_2, ← integral_sub (h_int_1.add h_int_2) h_int_3]
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
        fun v => ((v : ℂ) * cTheta θ v).re / y ^ 2 := by
      ext v
      rw [← Complex.ofReal_pow, Complex.div_ofReal_im]
      simp [Complex.mul_im]
    rw [this, integral_div, ← Complex.re_integral h_vc_int, h_main_re]
    ring
  rw [hJ_split, hterm1, hterm2, zero_add, sub_eq_add_neg, add_sub_cancel_left, abs_neg]
  calc |∫ v in Set.Ioi (0 : ℝ), ((cTheta θ v * (v : ℂ) ^ 2) / ((y : ℂ) ^ 2 * ((y : ℂ) - Complex.I * v))).im|
      ≤ ∫ v in Set.Ioi (0 : ℝ), ‖((cTheta θ v * (v : ℂ) ^ 2) / ((y : ℂ) ^ 2 * ((y : ℂ) - Complex.I * v))).im‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ v in Set.Ioi (0 : ℝ), v ^ 2 * ‖cTheta θ v‖ / |y| ^ 3 := by
        refine setIntegral_mono_on h_int_3.norm (h_v2c_int.div_const (|y| ^ 3)) measurableSet_Ioi fun v _ => ?_
        rw [Real.norm_eq_abs, abs_norm]
        refine (Complex.abs_im_le_abs _).trans ?_
        rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
        have hden : |y| ≤ ‖(y : ℂ) - Complex.I * v‖ := by
          have : |y| = ‖((y : ℂ) - Complex.I * v).re‖ := by simp [Real.norm_eq_abs]
          rw [this]; exact Complex.abs_re_le_abs _
        calc ‖cTheta θ v‖ * v ^ 2 / (|y| ^ 2 * ‖(y : ℂ) - Complex.I * v‖)
            ≤ ‖cTheta θ v‖ * v ^ 2 / (|y| ^ 2 * |y|) := by gcongr
          _ = v ^ 2 * ‖cTheta θ v‖ / |y| ^ 3 := by ring
    _ = (∫ v in Set.Ioi (0 : ℝ), v ^ 2 * ‖cTheta θ v‖) / |y| ^ 3 := integral_div _ _
    _ ≤ C_inf / |y| ^ 3 := by gcongr; exact le_max_right _ _

/-- **Lemma 3.1** (Optimal lattice shift `α_Δ ∈ (0, 1)`). -/
theorem optimal_lattice_shift (θ : ℝ) (hθ : |θ| < Real.pi / 2) :
    ∃ (Δ₁ C_α : ℝ), Δ₁ ≥ 1 ∧ C_α > 0 ∧
      ∀ Δ ≥ Δ₁, ∃! α : ℝ, α ∈ Set.Ioo (0 : ℝ) 1 ∧
        Summable (fun n : ℤ => rescaledFDeriv θ Δ (n + α)) ∧
        ∑' n : ℤ, rescaledFDeriv θ Δ (n + α) = 0 ∧
        |α - (1 / 2 - θ / Real.pi)| ≤ C_α * Δ * Real.exp (-2 * Real.pi * Δ) := by
  sorry

/-- **Lemma 3.2** (Contour integral representation for `M_α(y) - F_{θ,Δ}(y)`). -/
theorem contour_representation (θ Δ α : ℝ) (hθ : |θ| < Real.pi / 2)
    (hΔ : Δ ≥ 1) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ y : ℝ, y ≠ 0 →
      vaalerInterpolant θ Δ α y - rescaledF θ Δ y =
        (Real.sin (Real.pi * (y - α))) ^ 2 *
          ((∫ v in Set.Ioo (0 : ℝ) Δ,
            (Complex.exp (-Complex.I * θ) /
              (Complex.sin (Real.pi * (Complex.I * v - α)) ^ 2 * (y - Complex.I * v))).im) -
            (Δ * Real.sin θ /
              (Complex.sin (Real.pi * (Complex.I * Δ - α)) ^ 2 * (Complex.I * Δ - y))).re) := by
  sorry

/-- **Lemma 3.3 (Part 1)**: Positivity `J(y, θ) > 0` for all `y ≠ 0`. -/
theorem limitingJ_pos (θ : ℝ) (hθ : |θ| < Real.pi / 2) :
    ∀ y : ℝ, y ≠ 0 → limitingJ y θ > 0 := by
  sorry

/-- **Theorem 1.6** (Asymmetric Beurling–Selberg majorant `M_{θ,Δ}`). -/
theorem asymmetric_majorant (θ : ℝ) (hθ : |θ| < Real.pi / 2) :
    ∃ (Δ₀ C_sup C_L1 C_err : ℝ), Δ₀ ≥ 1 ∧ C_sup > 0 ∧ C_L1 > 0 ∧ C_err > 0 ∧
      ∀ Δ ≥ Δ₀, ∃ (α : ℝ) (M_entire : ℂ → ℂ),
        α ∈ Set.Ioo (0 : ℝ) 1 ∧
        HasExponentialType M_entire (2 * Real.pi * Δ) ∧
        (∀ x : ℝ, (M_entire x).im = 0 ∧ (M_entire x).re = majorantM θ Δ α x) ∧
        Integrable (fun x : ℝ => majorantM θ Δ α x - kernelK θ x) ∧
        (∀ x : ℝ, (1 + x ^ 2) * |majorantM θ Δ α x| ≤ C_sup * Real.log Δ) ∧
        (∫ x : ℝ, |majorantM θ Δ α x|) ≤ C_L1 ∧
        (∀ x : ℝ, x ≠ 0 → majorantM θ Δ α x ≥ kernelK θ x) ∧
        |(∫ x : ℝ, majorantM θ Δ α x - kernelK θ x) - 2 * envelopeC θ / Δ| ≤
          C_err * Real.exp (-2 * Real.pi * Δ) := by
  sorry

end PolarEvaluation
