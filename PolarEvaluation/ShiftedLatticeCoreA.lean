import PolarEvaluation.Basic
import PolarEvaluation.ExplicitFormulae

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
    have h := hf_decay.choose_spec (α + n)
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
    rw [h1, one_mul]
    exact (hf'_decay.choose_spec k).trans (by
      rw [hFf k, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      have hcexp : Complex.exp (-2 * Real.pi * Δ * |↑k|) = (Real.exp (-2 * Real.pi * Δ * |↑k|) : ℂ) := by
        have : (-2 * (Real.pi : ℂ) * ↑Δ * ↑|(k : ℝ)| : ℂ) = ((-2 * Real.pi * Δ * |(k : ℝ)| : ℝ) : ℂ) := by
          push_cast; ring
        rw [this, ← Complex.ofReal_exp]
      rw [hcexp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (exp_neg_le_inv_one_add_sq (by nlinarith [Real.two_le_pi])) Real.pi_pos.le)
  have hg0 : g 0 = (Real.pi : ℂ) := by
    simp [g, hFf 0]
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
  have h_eval : (∑' k : ℤ, ‖if k = 0 then (0 : ℂ) else g k‖) =
      2 * Real.pi * ∑' m : ℕ, (Real.exp (-2 * Real.pi * Δ)) ^ (m + 1) := by
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
    let e : ℕ ⊕ ℕ ⊕ Unit ≃ ℤ :=
      { toFun := Sum.elim (fun n : ℕ => (n : ℤ) + 1)
          (Sum.elim (fun n : ℕ => -((n : ℤ) + 1)) (fun _ => 0))
        invFun := fun k =>
          if 0 < k then Sum.inl (k.toNat - 1)
          else if k < 0 then Sum.inr (Sum.inl ((-k).toNat - 1))
          else Sum.inr (Sum.inr ())
        left_inv := fun x => by
          rcases x with n | (n | ⟨⟩)
          · simp; omega
          · simp; omega
          · simp
        right_inv := fun k => by
          rcases lt_trichotomy k 0 with hk | rfl | hk
          · simp [not_lt.mpr hk.le, hk]; omega
          · simp
          · simp [hk]; omega }
    rw [heq_f, ← e.tsum_eq]
    have hsumm_e : Summable (fun x : ℕ ⊕ ℕ ⊕ Unit =>
        if e x = 0 then (0 : ℝ) else Real.pi * Real.exp (-2 * Real.pi * Δ * |↑(e x)|)) :=
      (e.summable_iff).mpr hsumm_exp
    rw [hsumm_e.tsum_sum, (hsumm_e.comp_injective Sum.inr_injective).tsum_sum]
    have hpos_sum : (∑' n : ℕ, if e (Sum.inl n) = 0 then (0 : ℝ) else Real.pi * Real.exp (-2 * Real.pi * Δ * |↑(e (Sum.inl n))|)) =
        Real.pi * ∑' m : ℕ, (Real.exp (-2 * Real.pi * Δ)) ^ (m + 1) := by
      rw [← tsum_mul_left]
      congr 1; ext m
      have hne : (m : ℤ) + 1 ≠ 0 := by omega
      simp only [e, Sum.elim_inl, hne, ↓reduceIte]
      have hnonneg : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
      push_cast
      rw [abs_of_nonneg hnonneg, ← Real.exp_nat_mul]
      congr 1; push_cast; ring
    have hneg_sum : (∑' n : ℕ, if e (Sum.inr (Sum.inl n)) = 0 then (0 : ℝ) else Real.pi * Real.exp (-2 * Real.pi * Δ * |↑(e (Sum.inr (Sum.inl n)))|)) =
        Real.pi * ∑' m : ℕ, (Real.exp (-2 * Real.pi * Δ)) ^ (m + 1) := by
      rw [← tsum_mul_left]
      congr 1; ext m
      have hne : -((m : ℤ) + 1) ≠ 0 := by omega
      simp only [e, Sum.elim_inr, Sum.elim_inl, hne, ↓reduceIte]
      have hnonneg : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
      push_cast
      rw [abs_neg, abs_of_nonneg hnonneg, ← Real.exp_nat_mul]
      congr 1; push_cast; ring
    have hzero_sum : (∑' u : Unit, if e (Sum.inr (Sum.inr u)) = 0 then (0 : ℝ) else Real.pi * Real.exp (-2 * Real.pi * Δ * |↑(e (Sum.inr (Sum.inr u)))|)) = 0 := by
      simp [e]
    rw [hpos_sum, hneg_sum, hzero_sum, add_zero]
    ring
  rw [h_eval]
  have hr_nonneg : 0 ≤ Real.exp (-2 * Real.pi * Δ) := (Real.exp_pos _).le
  have hr_lt : Real.exp (-2 * Real.pi * Δ) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hgeom : ∑' m : ℕ, (Real.exp (-2 * Real.pi * Δ)) ^ (m + 1) =
      Real.exp (-2 * Real.pi * Δ) / (1 - Real.exp (-2 * Real.pi * Δ)) := by
    simp_rw [pow_succ']
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr_nonneg hr_lt]
    ring
  rw [hgeom]
  have hden_le : 1 - Real.exp (-2 * Real.pi) ≤ 1 - Real.exp (-2 * Real.pi * Δ) := by
    have : Real.exp (-2 * Real.pi * Δ) ≤ Real.exp (-2 * Real.pi) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    linarith
  have hden_pos : 0 < 1 - Real.exp (-2 * Real.pi) := by
    linarith [Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos] : -2 * Real.pi < 0)]
  rw [show 2 * Real.pi * (Real.exp (-2 * Real.pi * Δ) / (1 - Real.exp (-2 * Real.pi * Δ))) =
      2 * Real.pi * Real.exp (-2 * Real.pi * Δ) / (1 - Real.exp (-2 * Real.pi * Δ)) by ring]
  exact div_le_div_of_nonneg_left (by positivity) hden_pos hden_le

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

lemma tsum_succ_mul_pow (w : ℂ) (hw : ‖w‖ < 1) :
    Summable (fun m : ℕ => ((m : ℂ) + 1) * w ^ m) ∧
    ∑' m : ℕ, ((m : ℂ) + 1) * w ^ m = 1 / (1 - w) ^ 2 := by
  have hs1 : Summable (fun m : ℕ => (m : ℂ) * w ^ m) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one 1 hw
    simpa [pow_one] using h
  have hs2 : Summable (fun m : ℕ => w ^ m) := summable_geometric_of_norm_lt_one hw
  have hs : Summable (fun m : ℕ => ((m : ℂ) + 1) * w ^ m) := by
    refine (hs1.add hs2).congr fun m => by ring
  refine ⟨hs, ?_⟩
  have h1w : 1 - w ≠ 0 := by
    intro h
    have : w = 1 := by linear_combination -h
    rw [this, norm_one] at hw
    linarith
  have h_shift : ∑' m : ℕ, ((m : ℂ) + 1) * w ^ m =
      1 + ∑' m : ℕ, ((m : ℂ) + 2) * w ^ (m + 1) := by
    rw [hs.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_add, pow_zero, mul_one]
    congr 1; ext m; push_cast; ring
  have h_mul : (1 - w) * ∑' m : ℕ, ((m : ℂ) + 1) * w ^ m =
      ∑' m : ℕ, w ^ m := by
    have hs_w : Summable (fun m : ℕ => ((m : ℂ) + 1) * w ^ (m + 1)) := by
      refine (hs.mul_left w).congr fun m => by ring
    rw [sub_mul, one_mul, ← tsum_mul_left]
    have heq : (fun m : ℕ => w * (((m : ℂ) + 1) * w ^ m)) =
        fun m : ℕ => ((m : ℂ) + 1) * w ^ (m + 1) := by ext m; ring
    rw [heq, h_shift, add_sub_assoc]
    have h_sub : (∑' m : ℕ, ((m : ℂ) + 2) * w ^ (m + 1)) -
        ∑' m : ℕ, ((m : ℂ) + 1) * w ^ (m + 1) = ∑' m : ℕ, w ^ (m + 1) := by
      have hs_2 : Summable (fun m : ℕ => ((m : ℂ) + 2) * w ^ (m + 1)) := by
        refine (hs_w.add (hs2.mul_left w)).congr fun m => by ring
      rw [← hs_2.tsum_sub hs_w]
      congr 1; ext m; ring
    rw [h_sub, hs2.tsum_eq_zero_add]
    simp only [pow_zero]
    congr 1; ext m; ring
  rw [tsum_geometric_of_norm_lt_one hw] at h_mul
  have h_res : ∑' m : ℕ, ((m : ℂ) + 1) * w ^ m = (1 - w)⁻¹ / (1 - w) := by
    rw [eq_div_iff h1w]
    linear_combination h_mul
  rw [h_res, inv_eq_one_div, div_div, sq]

lemma tsum_inv_sub_I_sq (z : ℂ) (hz : 0 < z.im) :
    Summable (fun n : ℤ => 1 / (z - n) ^ 2) ∧
    ∑' n : ℤ, 1 / (z - n) ^ 2 = (Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * z) ^ 2 := by
  set x : ℝ := z.re
  set v : ℝ := z.im
  have hv : 0 < v := hz
  let f : ℝ → ℂ := fun u => 1 / ((u : ℂ) - Complex.I * v) ^ 2
  have hf_ne : ∀ u : ℝ, (u : ℂ) - Complex.I * v ≠ 0 := by
    intro u h; have := congr_arg Complex.im h; simp at this; linarith
  have hf_cont : Continuous f := by
    refine continuous_const.div (Continuous.pow ?_ 2) (fun u => pow_ne_zero 2 (hf_ne u))
    exact Complex.continuous_ofReal.sub continuous_const
  set m_v : ℝ := min 1 (v ^ 2)
  have hm_v_pos : 0 < m_v := lt_min one_pos (sq_pos_of_pos hv)
  have hf_norm : ∀ u : ℝ, ‖f u‖ ≤ (2 / m_v) * (1 + |u|) ^ (-2 : ℝ) := by
    intro u
    dsimp only [f]
    rw [norm_div, norm_one, norm_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have hnsq : ((u : ℂ) - Complex.I * v).re * ((u : ℂ) - Complex.I * v).re +
        ((u : ℂ) - Complex.I * v).im * ((u : ℂ) - Complex.I * v).im = u ^ 2 + v ^ 2 := by
      simp; ring
    rw [hnsq]
    have hpos : 0 < 1 + |u| := by positivity
    rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hpos.le, Real.rpow_natCast,
      one_div, div_le_iff₀ (by positivity : 0 < u ^ 2 + v ^ 2)]
    have h1 : (1 + |u|) ^ 2 ≤ 2 * (1 + u ^ 2) := by
      have : (1 - |u|) ^ 2 ≥ 0 := sq_nonneg _
      nlinarith [sq_abs u]
    have h2 : m_v * (1 + u ^ 2) ≤ u ^ 2 + v ^ 2 := by
      have hm1 : m_v ≤ 1 := min_le_left _ _
      have hm2 : m_v ≤ v ^ 2 := min_le_right _ _
      nlinarith [sq_nonneg u]
    rw [mul_assoc, mul_inv_le_iff₀ (by positivity)]
    calc (1 + |u|) ^ 2 * 1 = (1 + |u|) ^ 2 := mul_one _
      _ ≤ 2 * (1 + u ^ 2) := h1
      _ = (2 / m_v) * (m_v * (1 + u ^ 2)) := by field_simp [hm_v_pos.ne']
      _ ≤ (2 / m_v) * (u ^ 2 + v ^ 2) := by gcongr
  have hf_decay : ∃ C, ∀ u : ℝ, ‖f u‖ ≤ C * (1 + |u|) ^ (-2 : ℝ) := ⟨2 / m_v, hf_norm⟩
  have hFf : ∀ ξ : ℝ, 𝓕 f ξ =
      if ξ < 0 then 4 * Real.pi ^ 2 * ξ * Complex.exp (2 * Real.pi * v * ξ) else 0 := by
    intro ξ
    rw [← fourierHat_eq_fourier]
    exact cauchy_sq_fourier v hv ξ
  set C_f' : ℝ := 4 * Real.pi ^ 2 * (2 / (2 * Real.pi * v) + 12 / (2 * Real.pi * v) ^ 3)
  have hf'_decay : ∃ C, ∀ ξ : ℝ, ‖𝓕 f ξ‖ ≤ C * (1 + |ξ|) ^ (-2 : ℝ) := by
    refine ⟨C_f', fun ξ => ?_⟩
    rw [hFf ξ]
    split_ifs with hξ
    · have hξ_neg : 0 < -ξ := neg_pos.mpr hξ
      have habs : |ξ| = -ξ := abs_of_neg hξ
      have ha_pos : 0 < 2 * Real.pi * v := by positivity
      have hcexp : Complex.exp (2 * Real.pi * v * ξ) = (Real.exp (-2 * Real.pi * v * |ξ|) : ℂ) := by
        rw [habs, ← Complex.ofReal_exp]; congr 1; push_cast; ring
      rw [hcexp, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), norm_ofNat, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, Complex.norm_real, Real.norm_eq_abs]
      have h_s := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * v * |ξ|) 4
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
        pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one,
        Nat.factorial_two, Nat.cast_ofNat] at h_s
      have h3f : (Nat.factorial 3 : ℝ) = 6 := by norm_num
      rw [h3f] at h_s
      have h_lin : 2 * Real.pi * v * |ξ| ≤ Real.exp (2 * Real.pi * v * |ξ|) := by
        linarith [sq_nonneg (2 * Real.pi * v * |ξ|), pow_nonneg (by positivity : 0 ≤ 2 * Real.pi * v * |ξ|) 3]
      have h_cub : (2 * Real.pi * v * |ξ|) ^ 3 / 6 ≤ Real.exp (2 * Real.pi * v * |ξ|) := by
        linarith [sq_nonneg (2 * Real.pi * v * |ξ|)]
      have h1 : |ξ| ≤ (1 / (2 * Real.pi * v)) * Real.exp (2 * Real.pi * v * |ξ|) := by
        rw [one_div_mul_eq_div, le_div_iff₀ ha_pos]; linarith
      have h3 : |ξ| ^ 3 ≤ (6 / (2 * Real.pi * v) ^ 3) * Real.exp (2 * Real.pi * v * |ξ|) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos ha_pos 3)]
        nlinarith [show (2 * Real.pi * v * |ξ|) ^ 3 = (2 * Real.pi * v) ^ 3 * |ξ| ^ 3 by ring]
      have h_1u : |ξ| * (1 + |ξ|) ^ 2 ≤ (2 / (2 * Real.pi * v) + 12 / (2 * Real.pi * v) ^ 3) *
          Real.exp (2 * Real.pi * v * |ξ|) := by
        have hsq : (1 + |ξ|) ^ 2 ≤ 2 + 2 * |ξ| ^ 2 := by
          have : (1 - |ξ|) ^ 2 ≥ 0 := sq_nonneg _; nlinarith [sq_abs ξ]
        calc |ξ| * (1 + |ξ|) ^ 2 ≤ |ξ| * (2 + 2 * |ξ| ^ 2) := by gcongr
          _ = 2 * |ξ| + 2 * |ξ| ^ 3 := by ring
          _ ≤ 2 * ((1 / (2 * Real.pi * v)) * Real.exp (2 * Real.pi * v * |ξ|)) +
              2 * ((6 / (2 * Real.pi * v) ^ 3) * Real.exp (2 * Real.pi * v * |ξ|)) := by gcongr
          _ = (2 / (2 * Real.pi * v) + 12 / (2 * Real.pi * v) ^ 3) * Real.exp (2 * Real.pi * v * |ξ|) := by ring
      have hpos : 0 < 1 + |ξ| := by positivity
      rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hpos.le, Real.rpow_natCast,
        mul_inv_le_iff₀ (by positivity)]
      rw [show -2 * Real.pi * v * |ξ| = -(2 * Real.pi * v * |ξ|) by ring, Real.exp_neg,
        mul_assoc, mul_inv_le_iff₀ (Real.exp_pos _)]
      calc 4 * Real.pi ^ 2 * |ξ| * (1 + |ξ|) ^ 2
          = 4 * Real.pi ^ 2 * (|ξ| * (1 + |ξ|) ^ 2) := by ring
        _ ≤ 4 * Real.pi ^ 2 * ((2 / (2 * Real.pi * v) + 12 / (2 * Real.pi * v) ^ 3) *
            Real.exp (2 * Real.pi * v * |ξ|)) := by gcongr
        _ = C_f' * Real.exp (2 * Real.pi * v * |ξ|) := by dsimp only [C_f']; ring
    · simp only [norm_zero]; positivity
  have hpois := Real.tsum_eq_tsum_fourierIntegral_of_rpow_decay hf_cont (by norm_num : (1 : ℝ) < 2) hf_decay hf'_decay (-x)
  have h_eq_lhs : (fun n : ℤ => f (-x + n)) = fun n : ℤ => 1 / (z - n) ^ 2 := by
    ext n
    dsimp only [f]
    have hz_eq : z = (x : ℂ) + Complex.I * v := by apply Complex.ext <;> simp [x, v]
    rw [hz_eq]
    have hsub : ((x : ℂ) + Complex.I * v) - n = -(((-x + n : ℝ) : ℂ) - Complex.I * v) := by
      push_cast; ring
    rw [hsub, neg_sq]
  have hsumm_lhs : Summable (fun n : ℤ => 1 / (z - n) ^ 2) := by
    rw [← h_eq_lhs]
    exact Summable.of_norm_bounded (g := fun n : ℤ => (2 / m_v) * (1 + |(-x) + n|) ^ (-2 : ℝ))
      ((summable_inv_one_add_sq_shift (-x)).mul_left (2 / m_v)) (fun n => hf_norm (-x + n))
  refine ⟨hsumm_lhs, ?_⟩
  rw [← h_eq_lhs, hpois]
  set w : ℂ := Complex.exp (2 * Real.pi * Complex.I * z)
  have hw_norm : ‖w‖ = Real.exp (-2 * Real.pi * v) := by
    dsimp only [w]
    rw [Complex.norm_exp]
    congr 1
    have hz_eq : z = (x : ℂ) + Complex.I * v := by apply Complex.ext <;> simp [x, v]
    rw [hz_eq]; simp; ring
  have hw_lt : ‖w‖ < 1 := by
    rw [hw_norm, Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  let e : ℕ ⊕ ℕ ≃ ℤ :=
    { toFun := Sum.elim (fun m : ℕ => (m : ℤ)) (fun m : ℕ => -((m : ℤ) + 1))
      invFun := fun k => if 0 ≤ k then Sum.inl k.toNat else Sum.inr ((-k).toNat - 1)
      left_inv := fun s => by
        rcases s with m | m
        · simp
        · simp; omega
      right_inv := fun k => by
        by_cases hk : 0 ≤ k
        · simp [hk]
        · simp [hk]; omega }
  let g_k : ℤ → ℂ := fun k => 𝐞 (k * (-x)) • 𝓕 f k
  have hg_k_eq : ∀ m : ℕ, g_k (-((m : ℤ) + 1)) = -4 * Real.pi ^ 2 * ((m : ℂ) + 1) * w ^ (m + 1) := by
    intro m
    dsimp only [g_k]
    rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, hFf (-((m : ℤ) + 1))]
    have hneg : ((-((m : ℤ) + 1) : ℤ) : ℝ) < 0 := by push_cast; linarith
    rw [if_pos hneg]
    have hw_pow : w ^ (m + 1) = Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) + 1) * z) := by
      dsimp only [w]
      rw [← Complex.exp_nat_mul]
      congr 1; push_cast; ring
    have hz_eq : z = (x : ℂ) + Complex.I * v := by apply Complex.ext <;> simp [x, v]
    rw [hw_pow, hz_eq]
    have hexp_split : Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) + 1) * (x + Complex.I * v)) =
        Complex.exp (↑(2 * Real.pi * ((-((m : ℤ) + 1) : ℤ) : ℝ) * (-x)) * Complex.I) *
          Complex.exp (2 * Real.pi * v * ((-((m : ℤ) + 1) : ℤ) : ℝ)) := by
      rw [← Complex.exp_add]
      congr 1; push_cast; ring_nf; simp [Complex.I_sq]; ring
    rw [hexp_split]
    push_cast; ring
  have hg_k_nonneg : ∀ m : ℕ, g_k (m : ℤ) = 0 := by
    intro m
    dsimp only [g_k]
    rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, hFf (m : ℤ)]
    have hnn : ¬ ((m : ℝ) < 0) := not_lt.mpr (Nat.cast_nonneg m)
    rw [if_neg hnn, mul_zero]
  obtain ⟨hs_w, h_tsum_w⟩ := tsum_succ_mul_pow w hw_lt
  have hs_e : Summable (fun s : ℕ ⊕ ℕ => g_k (e s)) := by
    rw [summable_sum_iff]
    refine ⟨?_, ?_⟩
    · simp only [e, Sum.elim_inl, hg_k_nonneg]; exact summable_zero
    · simp only [e, Sum.elim_inr, hg_k_eq]
      exact (hs_w.mul_left (-4 * Real.pi ^ 2 * w)).congr fun m => by ring
  rw [← e.tsum_eq, hs_e.tsum_sum]
  simp only [e, Sum.elim_inl, Sum.elim_inr, hg_k_nonneg, tsum_zero, zero_add]
  have heq_w : (∑' m : ℕ, g_k (-((m : ℤ) + 1))) = (-4 * Real.pi ^ 2 * w) * ∑' m : ℕ, ((m : ℂ) + 1) * w ^ m := by
    rw [← tsum_mul_left]
    congr 1; ext m; rw [hg_k_eq m]; ring
  rw [heq_w, h_tsum_w]
  have h1w : 1 - w ≠ 0 := by
    intro h
    have : w = 1 := by linear_combination -h
    rw [this, norm_one] at hw_lt
    linarith
  have hsin_eq : Complex.sin (Real.pi * z) =
      (Complex.exp (Complex.I * Real.pi * z) - Complex.exp (-Complex.I * Real.pi * z)) / (2 * Complex.I) := by
    rw [Complex.sin_eq_exp]
    congr 1; ring
  have hsin_sq : Complex.sin (Real.pi * z) ^ 2 =
      -Complex.exp (-2 * Complex.I * Real.pi * z) * (1 - w) ^ 2 / 4 := by
    rw [hsin_eq, div_pow, mul_pow, show (2 : ℂ) ^ 2 = 4 by norm_num, Complex.I_sq]
    have he1 : Complex.exp (Complex.I * Real.pi * z) =
        Complex.exp (-Complex.I * Real.pi * z) * w := by
      dsimp only [w]; rw [← Complex.exp_add]; congr 1; ring
    have he2 : Complex.exp (-Complex.I * Real.pi * z) ^ 2 = Complex.exp (-2 * Complex.I * Real.pi * z) := by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    rw [he1, show Complex.exp (-Complex.I * Real.pi * z) * w - Complex.exp (-Complex.I * Real.pi * z) =
        -Complex.exp (-Complex.I * Real.pi * z) * (1 - w) by ring, mul_pow, neg_sq, he2]
    ring
  have hw_inv : w = Complex.exp (-2 * Complex.I * Real.pi * z)⁻¹ := by
    dsimp only [w]; rw [← Complex.exp_neg]; congr 1; ring
  have hexp_ne : Complex.exp (-2 * Complex.I * Real.pi * z) ≠ 0 := Complex.exp_ne_zero _
  rw [hsin_sq]
  have hw_prod : w * Complex.exp (-2 * Complex.I * Real.pi * z) = 1 := by
    dsimp only [w]; rw [← Complex.exp_add]; convert Complex.exp_zero using 2; ring
  field_simp [h1w, hexp_ne]
  linear_combination -4 * (Real.pi : ℂ) ^ 2 * hw_prod

lemma tsum_inv_sub_real_sq (y : ℝ) (hy : Real.sin (Real.pi * y) ≠ 0) :
    Summable (fun n : ℤ => 1 / (y - n) ^ 2) ∧
    ∑' n : ℤ, 1 / (y - n) ^ 2 = Real.pi ^ 2 / Real.sin (Real.pi * y) ^ 2 := by
  have hy_ne : ∀ n : ℤ, y - n ≠ 0 := by
    intro n h
    have hyn : y = n := sub_eq_zero.mp h
    apply hy
    rw [hyn, mul_comm, Real.sin_int_mul_pi]
  have hsumm : Summable (fun n : ℤ => 1 / (y - n) ^ 2) := by
    have hpos_d : ∃ d > 0, ∀ n : ℤ, d ≤ |y - n| := by
      let m := Int.floor y
      refine ⟨min (y - m) (m + 1 - y) / 2, ?_, fun n => ?_⟩
      · have h1 : (m : ℝ) < y := lt_of_le_of_ne (Int.floor_le y) (fun h => hy_ne m (by linarith))
        have h2 : y < (m : ℝ) + 1 := Int.lt_floor_add_one y
        positivity
      · rcases le_or_gt n m with hnm | hnm
        · have : (n : ℝ) ≤ m := by exact_mod_cast hnm
          have h1 : y - m ≤ y - n := by linarith
          have h0 : 0 ≤ y - m := sub_nonneg.mpr (Int.floor_le y)
          rw [abs_of_nonneg (by linarith)]
          exact le_trans (div_le_self (by positivity) (by norm_num)) (le_trans (min_le_left _ _) h1)
        · have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hnm
          have h1 : m + 1 - y ≤ n - y := by linarith
          have h0 : 0 ≤ m + 1 - y := by linarith [Int.lt_floor_add_one y]
          rw [abs_of_neg (by linarith), neg_sub]
          exact le_trans (div_le_self (by positivity) (by norm_num)) (le_trans (min_le_right _ _) h1)
    obtain ⟨d, hd_pos, hd⟩ := hpos_d
    refine ((summable_inv_one_add_sq_shift (-y)).mul_left (2 * (1 + 1 / d ^ 2))).of_nonneg_of_le
      (fun _ => by positivity) (fun n => ?_)
    have hpos : 0 < 1 + |-y + n| := by positivity
    rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hpos.le, Real.rpow_natCast,
      one_div, one_div, mul_inv_le_iff₀ (by positivity)]
    have h1 : (1 + |-y + n|) ^ 2 ≤ 2 * (1 + (y - n) ^ 2) := by
      have : (1 - |-y + n|) ^ 2 ≥ 0 := sq_nonneg _
      have heq : (-y + n) ^ 2 = (y - n) ^ 2 := by ring
      nlinarith [sq_abs (-y + n)]
    have h2 : 1 + (y - n) ^ 2 ≤ (1 + 1 / d ^ 2) * (y - n) ^ 2 := by
      have hdn : d ^ 2 ≤ (y - n) ^ 2 := by
        rw [← sq_abs (y - n)]; exact sq_le_sq' (by linarith) (hd n)
      have h1d : 1 ≤ (1 / d ^ 2) * (y - n) ^ 2 := by
        rw [one_div_mul_eq_div, one_le_div (sq_pos_of_pos hd_pos)]; exact hdn
      linarith
    rw [div_le_iff₀ (by positivity)]
    calc (1 + |-y + n|) ^ 2 * 1 = (1 + |-y + n|) ^ 2 := mul_one _
      _ ≤ 2 * (1 + (y - n) ^ 2) := h1
      _ ≤ 2 * ((1 + 1 / d ^ 2) * (y - n) ^ 2) := by gcongr
      _ = 2 * (1 + 1 / d ^ 2) * (y - n) ^ 2 := by ring
  refine ⟨hsumm, ?_⟩
  let z_seq : ℕ → ℂ := fun k => (y : ℂ) + Complex.I * (1 / ((k : ℝ) + 1))
  have hz_im : ∀ k : ℕ, 0 < (z_seq k).im := fun k => by simp [z_seq]; positivity
  have htend_z : Tendsto z_seq atTop (nhds (y : ℂ)) := by
    have h0 : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have h1 : Tendsto (fun k : ℕ => Complex.I * ((1 / ((k : ℝ) + 1) : ℝ) : ℂ)) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp h0)
    simpa [z_seq] using tendsto_const_nhds.add h1
  have h_dom : Tendsto (fun k : ℕ => ∑' n : ℤ, 1 / (z_seq k - n) ^ 2) atTop
      (nhds (∑' n : ℤ, 1 / ((y : ℂ) - n) ^ 2)) := by
    refine tendsto_tsum_of_dominated_convergence hsumm (fun n => ?_) (fun k n => ?_)
    · have hne : (y : ℂ) - n ≠ 0 := by
        intro h; have := congr_arg Complex.re h; simp at this; exact hy_ne n this
      exact (tendsto_const_nhds.div ((htend_z.sub tendsto_const_nhds).pow 2) (pow_ne_zero 2 hne))
    · rw [norm_div, norm_one, norm_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      have hnsq : (z_seq k - n).re * (z_seq k - n).re + (z_seq k - n).im * (z_seq k - n).im =
          (y - n) ^ 2 + (1 / ((k : ℝ) + 1)) ^ 2 := by
        simp [z_seq]; ring
      rw [hnsq]
      exact one_div_le_one_div_of_le (sq_pos_of_ne_zero (hy_ne n)) (by linarith [sq_nonneg (1 / ((k : ℝ) + 1))])
  have h_rhs : Tendsto (fun k : ℕ => (Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * z_seq k) ^ 2) atTop
      (nhds ((Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * y) ^ 2)) := by
    have hsin_ne : Complex.sin (Real.pi * (y : ℂ)) ≠ 0 := by
      rw [show (Real.pi : ℂ) * (y : ℂ) = ((Real.pi * y : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_sin]
      exact_mod_cast hy
    exact tendsto_const_nhds.div ((Complex.continuous_sin.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul htend_z)).pow 2) (pow_ne_zero 2 hsin_ne)
  have h_eq_k : (fun k : ℕ => ∑' n : ℤ, 1 / (z_seq k - n) ^ 2) =
      fun k : ℕ => (Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * z_seq k) ^ 2 := by
    ext k; exact (tsum_inv_sub_I_sq (z_seq k) (hz_im k)).2
  rw [h_eq_k] at h_dom
  have h_lim := tendsto_nhds_unique h_dom h_rhs
  have h_ofReal : (∑' n : ℤ, 1 / ((y : ℂ) - n) ^ 2) = ((∑' n : ℤ, 1 / (y - n) ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_tsum]
    congr 1; ext n; push_cast; ring
  have h_rhs_real : (Real.pi : ℂ) ^ 2 / Complex.sin (Real.pi * y) ^ 2 =
      ((Real.pi ^ 2 / Real.sin (Real.pi * y) ^ 2 : ℝ) : ℂ) := by
    rw [show (Real.pi : ℂ) * (y : ℂ) = ((Real.pi * y : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_sin]
    push_cast; ring
  rw [h_ofReal, h_rhs_real] at h_lim
  exact Complex.ofReal_injective h_lim


end PolarEvaluation
