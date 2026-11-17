import PolarEvaluation.Basic
import PolarEvaluation.ExternalResults

/-!
# Explicit Formulae and Fourier Analysis of the Kernel (Section 2)

Formalizes Lemma 2.1 (`horizontal_zero_sum`), Lemma 2.2 (`guinand_weil_bandlimited`),
and Lemma 2.3 (`kernelK_fourier` and `majorant_fourier_decay`).
-/

noncomputable section

open Complex Real MeasureTheory Filter Topology

namespace PolarEvaluation

/-- **Lemma 2.1** (Horizontal zero-sum representation). -/
theorem horizontal_zero_sum (D : LFunctionData) :
    ∃ C₀ : ℝ, C₀ > 0 ∧
      ∀ (q : ℕ) (hq : q ≥ 1) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive),
        D.GRH q hq χ hχ →
        ∀ (θ : ℝ), |θ| < Real.pi / 2 →
        ∀ (t : ℝ), D.nonvanishing q χ t → (q = 1 → |t| ≥ 10) →
          Summable (fun n : ℕ => kernelK θ (t - D.zeros q χ n)) ∧
          |polarLogL D q χ t θ -
            ((Real.cos θ / 2) * Real.log (analyticConductor q t) +
              ∑' n : ℕ, kernelK θ (t - D.zeros q χ n))| ≤ C₀ :=
  horizontal_zero_sum_external D

/-- **Lemma 2.2** (Guinand–Weil Explicit Formula for bandlimited test functions). -/
theorem guinand_weil_bandlimited (D : LFunctionData) :
    ∃ C₁ : ℝ, C₁ > 0 ∧
      ∀ (q : ℕ) (hq : q ≥ 1) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive),
        D.GRH q hq χ hχ →
        ∀ (h : ℂ → ℂ) (Δ M_sup : ℝ), Δ ≥ 1 → M_sup ≥ 0 →
          HasExponentialType h (2 * Real.pi * Δ) →
          (∀ x : ℝ, ‖h x‖ ≤ M_sup / (1 + x ^ 2)) →
          (∀ x : ℝ, (h x).im = 0) →
          ∀ (t : ℝ), (q = 1 → |t| ≥ 10) →
            Summable (fun n : ℕ => (h (t - D.zeros q χ n)).re) ∧
            |∑' n : ℕ, (h (t - D.zeros q χ n)).re -
              ((Real.log (analyticConductor q t) / (2 * Real.pi)) * (∫ x : ℝ, (h x).re) -
                primePowerSum q χ (fourierHat (fun x : ℝ => h x)) (Real.exp (2 * Real.pi * Δ)) t)| ≤
              C₁ * (M_sup + (if q = 1 then Real.exp (Real.pi * Δ) / t ^ 2 * M_sup else 0)) :=
  guinand_weil_external D

lemma kernelK_integrable_zero : Integrable (fun x : ℝ => kernelK 0 x) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => kernelK 0 x) volume := by
    unfold kernelK
    fun_prop
  have h_Ioi : IntegrableOn (fun x : ℝ => kernelK 0 x) (Set.Ioi (1 : ℝ)) := by
    have hpow : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
    refine hpow.mono' hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 < x := hx
    have hx_pos : 0 < x := by linarith
    have hx2_pos : 0 < x ^ 2 := sq_pos_of_pos hx_pos
    unfold kernelK
    simp only [Real.cos_zero, Real.sin_zero, zero_mul, add_zero]
    have hlog_nonneg : 0 ≤ Real.log ((x ^ 2 + 1) / x ^ 2) := by
      apply Real.log_nonneg
      rw [one_le_div hx2_pos]
      linarith
    have hlog_le : Real.log ((x ^ 2 + 1) / x ^ 2) ≤ 1 / x ^ 2 := by
      calc Real.log ((x ^ 2 + 1) / x ^ 2)
          ≤ (x ^ 2 + 1) / x ^ 2 - 1 := Real.log_le_sub_one_of_pos (div_pos (by positivity) hx2_pos)
        _ = 1 / x ^ 2 := by field_simp; ring
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2),
      abs_of_nonneg hlog_nonneg]
    have hrpow : x ^ (-2 : ℝ) = 1 / x ^ 2 := by
      rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hx_pos.le, Real.rpow_natCast, one_div]
    rw [hrpow]
    linarith
  have h_Iio : IntegrableOn (fun x : ℝ => kernelK 0 x) (Set.Iio (-1 : ℝ)) := by
    have h_even : ∀ x : ℝ, kernelK 0 (-x) = kernelK 0 x := by
      intro x; unfold kernelK; simp [Real.cos_zero, Real.sin_zero]
    have hcomp : IntegrableOn (fun x : ℝ => kernelK 0 (-x)) (Set.Ioi (1 : ℝ)) := by
      simpa [h_even] using h_Ioi
    have hpre : (fun x : ℝ => -x) ⁻¹' Set.Ioi (1 : ℝ) = Set.Iio (-1 : ℝ) := by
      ext x; simp
    simpa [hpre] using hcomp.comp_neg
  have h_Icc : IntegrableOn (fun x : ℝ => kernelK 0 x) (Set.Icc (-1 : ℝ) 1) := by
    have h_log_abs : IntegrableOn (fun x : ℝ => Real.log |x|) (Set.Icc (-1 : ℝ) 1) := by
      have h01 : IntegrableOn (fun x : ℝ => Real.log |x|) (Set.Icc (0 : ℝ) 1) := by
        have hrpow : IntegrableOn (fun x : ℝ => 2 * x ^ (-1 / 2 : ℝ)) (Set.Icc (0 : ℝ) 1) := by
          refine ((intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -1 / 2)).1.mono_set
            Set.Ioc_subset_Ioc_self).integrableOn_Icc.const_mul 2
        refine hrpow.mono' (AEStronglyMeasurable.restrict (by fun_prop)) ?_
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        by_cases hx0 : x = 0
        · subst hx0; simp
        · have hx_pos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
          have h_inv : 0 < x ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hx_pos _
          have hlog_neg : Real.log x ≤ 0 := Real.log_nonpos hx_pos.le hx.2
          have hbound : -Real.log x ≤ 2 * x ^ (-1 / 2 : ℝ) := by
            have h1 : Real.log (x ^ (-1 / 2 : ℝ)) ≤ x ^ (-1 / 2 : ℝ) - 1 :=
              Real.log_le_sub_one_of_pos h_inv
            rw [Real.log_rpow hx_pos] at h1
            linarith
          rw [Real.norm_eq_abs, abs_of_pos hx_pos, abs_of_nonpos hlog_neg]
          exact hbound
      have h_neg : IntegrableOn (fun x : ℝ => Real.log |x|) (Set.Icc (-1 : ℝ) 0) := by
        have hpre : (fun x : ℝ => -x) ⁻¹' Set.Icc (0 : ℝ) 1 = Set.Icc (-1 : ℝ) 0 := by
          ext x; simp; constructor <;> intro h <;> linarith
        simpa [abs_neg, hpre] using h01.comp_neg
      simpa [Set.Icc_union_Icc_eq_Icc (by norm_num : (-1 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1)] using
        h_neg.union h01
    have h_log_sq : IntegrableOn (fun x : ℝ => Real.log (x ^ 2 + 1)) (Set.Icc (-1 : ℝ) 1) :=
      (Continuous.continuousOn (Continuous.log (by fun_prop) (fun x => by positivity))).integrableOn_Icc
    have h_comb : IntegrableOn (fun x : ℝ => -(1 / 2 : ℝ) * (Real.log (x ^ 2 + 1) - 2 * Real.log |x|))
        (Set.Icc (-1 : ℝ) 1) :=
      (h_log_sq.sub (h_log_abs.const_mul 2)).const_mul (-(1 / 2 : ℝ))
    refine h_comb.congr_fun_ae ?_
    have hne : ∀ᵐ x ∂(volume.restrict (Set.Icc (-1 : ℝ) 1)), x ≠ 0 := by
      rw [ae_restrict_iff' measurableSet_Icc]
      have hzero : volume ({0} : Set ℝ) = 0 := volume_singleton
      filter_upwards [ae_iff.mpr (by simpa using hzero)] with x hx _
      exact hx
    filter_upwards [hne] with x hx
    unfold kernelK
    simp only [Real.cos_zero, Real.sin_zero, zero_mul, add_zero]
    have hx2 : x ^ 2 > 0 := sq_pos_of_ne_zero hx
    rw [Real.log_div (by positivity) hx2.ne', show x ^ 2 = |x| ^ 2 by rw [sq_abs],
      Real.log_pow, Nat.cast_ofNat]
    ring
  have huniv : Set.Iio (-1 : ℝ) ∪ Set.Icc (-1 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.univ := by
    ext x; simp; by_cases h1 : x < -1 <;> by_cases h2 : x ≤ 1 <;> simp_all <;> linarith
  rw [← integrableOn_univ, ← huniv]
  exact (h_Iio.union h_Icc).union h_Ioi

lemma kernelK_integrable_pi_half : Integrable (fun x : ℝ => kernelK (Real.pi / 2) x) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => kernelK (Real.pi / 2) x) volume := by
    unfold kernelK
    fun_prop
  have h_Icc : IntegrableOn (fun x : ℝ => kernelK (Real.pi / 2) x) (Set.Icc (-1 : ℝ) 1) := by
    have hconst : IntegrableOn (fun _ : ℝ => Real.pi / 2 + 1) (Set.Icc (-1 : ℝ) 1) :=
      continuousOn_const.integrableOn_Icc
    refine hconst.mono' hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    unfold kernelK
    simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, zero_div, zero_mul, neg_zero, zero_add,
      one_mul, Real.norm_eq_abs]
    have harctan : |Real.arctan (1 / x)| ≤ Real.pi / 2 :=
      abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
    have hfrac : |x / (x ^ 2 + 1)| ≤ 1 := by
      rw [abs_div, abs_of_pos (by positivity : 0 < x ^ 2 + 1)]
      have hx_le : |x| ≤ 1 := abs_le.mpr ⟨hx.1, hx.2⟩
      have hden : 1 ≤ x ^ 2 + 1 := by linarith [sq_nonneg x]
      exact div_le_one_of_le₀ (hx_le.trans hden) (by positivity)
    calc |Real.arctan (1 / x) - x / (x ^ 2 + 1)|
        ≤ |Real.arctan (1 / x)| + |x / (x ^ 2 + 1)| := abs_sub _ _
      _ ≤ Real.pi / 2 + 1 := add_le_add harctan hfrac
  have h_Ioi : IntegrableOn (fun x : ℝ => kernelK (Real.pi / 2) x) (Set.Ioi (1 : ℝ)) := by
    have hpow : IntegrableOn (fun x : ℝ => 2 * x ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul 2
    refine hpow.mono' hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 < x := hx
    have hx_pos : 0 < x := by linarith
    have hu_pos : 0 < 1 / x := div_pos one_pos hx_pos
    have harctan_le : Real.arctan (1 / x) ≤ 1 / x := by
      have hmono : MonotoneOn (fun t : ℝ => t - Real.arctan t) (Set.Ici 0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
        · exact (continuous_id.sub Real.continuous_arctan).continuousOn
        · exact fun t _ => (differentiableAt_id.sub (Real.differentiableAt_arctan t)).differentiableWithinAt
        · intro t _
          have h1 : HasDerivAt (fun s : ℝ => s - Real.arctan s) (1 - (1 + t ^ 2)⁻¹) t := by
            simpa [inv_eq_one_div] using (hasDerivAt_id t).sub (Real.hasDerivAt_arctan t)
          rw [h1.deriv]
          have hle : (1 + t ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [sq_nonneg t])
          linarith
      have := hmono (by simp : (0 : ℝ) ∈ Set.Ici 0) hu_pos.le hu_pos.le
      simp only [sub_zero, Real.arctan_zero] at this
      linarith
    have harctan_ge : 1 / x - (1 / x) ^ 2 / 2 ≤ Real.arctan (1 / x) := by
      have hmono : MonotoneOn (fun t : ℝ => Real.arctan t - (t - t ^ 2 / 2)) (Set.Ici 0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
        · exact (Real.continuous_arctan.sub (continuous_id.sub ((continuous_pow 2).div_const 2))).continuousOn
        · intro t _
          exact ((Real.differentiableAt_arctan t).sub
            (differentiableAt_id.sub ((differentiableAt_pow 2).div_const 2))).differentiableWithinAt
        · intro t ht
          have ht0 : 0 ≤ t := interior_subset ht
          have h1 : HasDerivAt (fun s : ℝ => Real.arctan s - (s - s ^ 2 / 2))
              (1 / (1 + t ^ 2) - (1 - t)) t := by
            have ha := Real.hasDerivAt_arctan t
            have hb := (hasDerivAt_id t).sub ((hasDerivAt_pow 2 t).div_const 2)
            convert ha.sub hb using 1
            ring
          rw [h1.deriv]
          have hpos : 0 ≤ t * (t ^ 2 - t + 1) := by
            have : t ^ 2 - t + 1 = (t - 1 / 2) ^ 2 + 3 / 4 := by ring
            nlinarith [sq_nonneg (t - 1 / 2)]
          have heq : 1 / (1 + t ^ 2) - (1 - t) = t * (t ^ 2 - t + 1) / (1 + t ^ 2) := by
            field_simp; ring
          rw [heq]
          exact div_nonneg hpos (by positivity)
      have := hmono (by simp : (0 : ℝ) ∈ Set.Ici 0) hu_pos.le hu_pos.le
      simp only [Real.arctan_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, zero_div] at this
      linarith
    have hdiff1 : |Real.arctan (1 / x) - 1 / x| ≤ 1 / x ^ 2 := by
      rw [abs_le]
      have hhalf : (1 / x) ^ 2 / 2 ≤ 1 / x ^ 2 := by
        rw [div_pow, one_pow, div_div]
        exact div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith [sq_pos_of_pos hx_pos])
      constructor <;> linarith
    have hdiff2 : |1 / x - x / (x ^ 2 + 1)| ≤ 1 / x ^ 2 := by
      have heq : 1 / x - x / (x ^ 2 + 1) = 1 / (x * (x ^ 2 + 1)) := by field_simp; ring
      rw [heq, abs_of_pos (div_pos one_pos (mul_pos hx_pos (by positivity)))]
      have hden : x ^ 2 ≤ x * (x ^ 2 + 1) := by nlinarith
      exact one_div_le_one_div_of_le (sq_pos_of_pos hx_pos) hden
    unfold kernelK
    simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, zero_div, zero_mul, neg_zero, zero_add,
      one_mul, Real.norm_eq_abs]
    have hrpow : 2 * x ^ (-2 : ℝ) = 2 * (1 / x ^ 2) := by
      rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hx_pos.le, Real.rpow_natCast, one_div]
    rw [hrpow]
    calc |Real.arctan (1 / x) - x / (x ^ 2 + 1)|
        = |(Real.arctan (1 / x) - 1 / x) + (1 / x - x / (x ^ 2 + 1))| := by ring_nf
      _ ≤ |Real.arctan (1 / x) - 1 / x| + |1 / x - x / (x ^ 2 + 1)| := abs_add_le _ _
      _ ≤ 1 / x ^ 2 + 1 / x ^ 2 := add_le_add hdiff1 hdiff2
      _ = 2 * (1 / x ^ 2) := by ring
  have h_Iio : IntegrableOn (fun x : ℝ => kernelK (Real.pi / 2) x) (Set.Iio (-1 : ℝ)) := by
    have h_odd : ∀ x : ℝ, kernelK (Real.pi / 2) (-x) = -kernelK (Real.pi / 2) x := by
      intro x; unfold kernelK
      simp [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.arctan_neg, div_neg, neg_div]
      ring
    have hcomp : IntegrableOn (fun x : ℝ => -kernelK (Real.pi / 2) (-x)) (Set.Ioi (1 : ℝ)) := by
      simpa [h_odd] using h_Ioi
    have hpre : (fun x : ℝ => -x) ⁻¹' Set.Ioi (1 : ℝ) = Set.Iio (-1 : ℝ) := by
      ext x; simp
    simpa [hpre] using hcomp.neg.comp_neg
  have huniv : Set.Iio (-1 : ℝ) ∪ Set.Icc (-1 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.univ := by
    ext x; simp; by_cases h1 : x < -1 <;> by_cases h2 : x ≤ 1 <;> simp_all <;> linarith
  rw [← integrableOn_univ, ← huniv]
  exact (h_Iio.union h_Icc).union h_Ioi

lemma kernelK_integrable (θ : ℝ) : Integrable (fun x : ℝ => kernelK θ x) := by
  have h : (fun x : ℝ => kernelK θ x) =
      (fun x : ℝ => Real.cos θ * kernelK 0 x + Real.sin θ * kernelK (Real.pi / 2) x) := by
    ext x
    unfold kernelK
    simp [Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  rw [h]
  exact (kernelK_integrable_zero.const_mul _).add (kernelK_integrable_pi_half.const_mul _)

/-- **Lemma 2.3 (Part 1)**: Explicit Fourier transform `K̂_θ(ξ)` for `θ ∈ [-π/2, π/2]` and `ξ ≠ 0`,
together with `K̂_θ(0) = -π cos θ`. -/
theorem kernelK_fourier (θ : ℝ) (hθ : |θ| ≤ Real.pi / 2) :
    fourierHat (fun x : ℝ => (kernelK θ x : ℂ)) 0 = (-Real.pi * Real.cos θ : ℂ) ∧
    ∀ ξ : ℝ, ξ ≠ 0 →
      fourierHat (fun x : ℝ => (kernelK θ x : ℂ)) ξ =
        -(Real.cos θ : ℂ) * ((1 - Complex.exp (-2 * Real.pi * |ξ|)) / (2 * |ξ|)) -
          Complex.I * (Real.sin θ : ℂ) *
            ((1 - Complex.exp (-2 * Real.pi * |ξ|)) / (2 * ξ) -
              Real.pi * (if 0 < ξ then (1 : ℂ) else -1) * Complex.exp (-2 * Real.pi * |ξ|)) := by
  sorry

/-- **Lemma 2.3 (Part 2)**: Fourier decay of any bandlimited `L^1`-close majorant `M_{θ,Δ}`
at `ξ = ± log p / (2π)`. -/
theorem majorant_fourier_decay (θ C_L1 Δ₀ : ℝ) (hθ : |θ| ≤ Real.pi / 2) (hΔ₀ : Δ₀ ≥ 1) :
    ∃ C_dec > 0, ∀ (Δ : ℝ) (M : ℝ → ℝ), Δ ≥ Δ₀ →
      Integrable (fun x : ℝ => M x - kernelK θ x) →
      (∫ x : ℝ, |M x - kernelK θ x|) ≤ C_L1 / Δ →
      ∀ (p : ℕ), Nat.Prime p →
        ‖fourierHat (fun x : ℝ => (M x : ℂ)) (Real.log p / (2 * Real.pi))‖ ≤
          C_dec * (1 / Real.log p + 1 / Δ) ∧
        ‖fourierHat (fun x : ℝ => (M x : ℂ)) (-(Real.log p / (2 * Real.pi)))‖ ≤
          C_dec * (1 / Real.log p + 1 / Δ) := by
  refine ⟨max (4 * Real.pi) (max C_L1 1), by positivity, fun Δ M hΔ hInt hL1 p hp => ?_⟩
  set C_dec := max (4 * Real.pi) (max C_L1 1)
  have hK_int : Integrable (fun x : ℝ => kernelK θ x) := kernelK_integrable θ
  have hM_int : Integrable (fun x : ℝ => M x) := by
    have : (fun x : ℝ => M x) = (fun x : ℝ => (M x - kernelK θ x) + kernelK θ x) := by
      ext x; ring
    rw [this]
    exact hInt.add hK_int
  have h_bound_ξ : ∀ ξ : ℝ, ξ ≠ 0 → 1 / |ξ| = 2 * Real.pi / Real.log p →
      ‖fourierHat (fun x : ℝ => (M x : ℂ)) ξ‖ ≤ C_dec * (1 / Real.log p + 1 / Δ) := by
    intro ξ hξ hξ_abs
    have hK_four := (kernelK_fourier θ hθ).2 ξ hξ
    have h_exp_le : Real.exp (-2 * Real.pi * |ξ|) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ 2 * Real.pi * |ξ| := by positivity
      linarith
    have h_exp_pos : 0 < Real.exp (-2 * Real.pi * |ξ|) := Real.exp_pos _
    have h_cexp_eq : Complex.exp (-2 * Real.pi * |ξ|) = (Real.exp (-2 * Real.pi * |ξ|) : ℂ) := by
      have : (-2 * (Real.pi : ℂ) * ↑|ξ| : ℂ) = ((-2 * Real.pi * |ξ| : ℝ) : ℂ) := by
        push_cast; ring
      rw [this, ← Complex.ofReal_exp]
    have h_one_sub : ‖(1 : ℂ) - Complex.exp (-2 * Real.pi * |ξ|)‖ ≤ 1 := by
      rw [h_cexp_eq, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    have h_pi_exp : Real.pi * Real.exp (-2 * Real.pi * |ξ|) ≤ 1 / (2 * |ξ|) := by
      have h_lin : 2 * Real.pi * |ξ| ≤ Real.exp (2 * Real.pi * |ξ|) := by
        linarith [Real.add_one_le_exp (2 * Real.pi * |ξ|)]
      have h_pos : 0 < 2 * Real.pi * |ξ| := by positivity
      calc Real.pi * Real.exp (-2 * Real.pi * |ξ|)
          = Real.pi / Real.exp (2 * Real.pi * |ξ|) := by
            rw [show -2 * Real.pi * |ξ| = -(2 * Real.pi * |ξ|) by ring, Real.exp_neg, div_eq_mul_inv]
        _ ≤ Real.pi / (2 * Real.pi * |ξ|) := by gcongr
        _ = 1 / (2 * |ξ|) := by field_simp [Real.pi_ne_zero]
    have hK_norm : ‖fourierHat (fun x : ℝ => (kernelK θ x : ℂ)) ξ‖ ≤ 3 / (2 * |ξ|) := by
      rw [hK_four]
      have h1 : ‖-(Real.cos θ : ℂ) * ((1 - Complex.exp (-2 * Real.pi * |ξ|)) / (2 * |ξ|))‖ ≤
          1 / (2 * |ξ|) := by
        rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
        calc |Real.cos θ| * ‖(1 - Complex.exp (-2 * Real.pi * |ξ|)) / (2 * |ξ|)‖
            ≤ 1 * (1 / (2 * |ξ|)) := by
              gcongr
              · exact Real.abs_cos_le_one θ
              · rw [norm_div, show (2 : ℂ) * ↑|ξ| = ((2 * |ξ| : ℝ) : ℂ) by push_cast; ring,
                  Complex.norm_real, Real.norm_eq_abs,
                  abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * |ξ|)]
                exact div_le_div_of_nonneg_right h_one_sub (by positivity)
          _ = 1 / (2 * |ξ|) := one_mul _
      have h2 : ‖Complex.I * (Real.sin θ : ℂ) *
            ((1 - Complex.exp (-2 * Real.pi * |ξ|)) / (2 * ξ) -
              Real.pi * (if 0 < ξ then (1 : ℂ) else -1) * Complex.exp (-2 * Real.pi * |ξ|))‖ ≤
          2 / (2 * |ξ|) := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        have hsin : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
        have h2a : ‖(1 - Complex.exp (-2 * Real.pi * |ξ|)) / (2 * ξ)‖ ≤ 1 / (2 * |ξ|) := by
          rw [norm_div, show (2 : ℂ) * ↑ξ = ((2 * ξ : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs, abs_mul,
            abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          exact div_le_div_of_nonneg_right h_one_sub (by positivity)
        have h2b : ‖(Real.pi : ℂ) * (if 0 < ξ then (1 : ℂ) else -1) * Complex.exp (-2 * Real.pi * |ξ|)‖ ≤
            1 / (2 * |ξ|) := by
          have hsgn : ‖if 0 < ξ then (1 : ℂ) else -1‖ = 1 := by split_ifs <;> simp
          rw [norm_mul, norm_mul, hsgn, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos Real.pi_pos, h_cexp_eq, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos h_exp_pos]
          exact h_pi_exp
        have h2c : ‖(1 - Complex.exp (-2 * Real.pi * |ξ|)) / (2 * ξ) -
            Real.pi * (if 0 < ξ then (1 : ℂ) else -1) * Complex.exp (-2 * Real.pi * |ξ|)‖ ≤
            2 / (2 * |ξ|) := by
          calc _ ≤ _ + _ := norm_sub_le _ _
            _ ≤ 1 / (2 * |ξ|) + 1 / (2 * |ξ|) := add_le_add h2a h2b
            _ = 2 / (2 * |ξ|) := by ring
        calc |Real.sin θ| * ‖_‖ ≤ 1 * (2 / (2 * |ξ|)) := mul_le_mul hsin h2c (norm_nonneg _) zero_le_one
          _ = 2 / (2 * |ξ|) := one_mul _
      calc ‖_ - _‖ ≤ ‖_‖ + ‖_‖ := norm_sub_le _ _
        _ ≤ 1 / (2 * |ξ|) + 2 / (2 * |ξ|) := add_le_add h1 h2
        _ = 3 / (2 * |ξ|) := by ring
    have hexp_norm : ∀ x : ℝ, ‖Complex.exp (-2 * Real.pi * Complex.I * ξ * x)‖ = 1 := by
      intro x
      have : -2 * (Real.pi : ℂ) * Complex.I * ↑ξ * ↑x = ((-2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have hdiff_norm : ‖fourierHat (fun x : ℝ => (M x : ℂ)) ξ -
        fourierHat (fun x : ℝ => (kernelK θ x : ℂ)) ξ‖ ≤ C_L1 / Δ := by
      have hM_c : Integrable (fun x : ℝ => (M x : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * ξ * x)) := by
        refine (hM_int.norm).mono (by fun_prop) ?_
        filter_upwards with x
        rw [norm_mul, Complex.norm_real, hexp_norm x, mul_one, norm_norm]
      have hK_c : Integrable (fun x : ℝ => (kernelK θ x : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * ξ * x)) := by
        refine (hK_int.norm).mono (by fun_prop) ?_
        filter_upwards with x
        rw [norm_mul, Complex.norm_real, hexp_norm x, mul_one, norm_norm]
      unfold fourierHat
      rw [← integral_sub hM_c hK_c]
      calc ‖∫ x : ℝ, ((M x : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * ξ * x) -
            (kernelK θ x : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * ξ * x))‖
          ≤ ∫ x : ℝ, ‖(M x : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * ξ * x) -
            (kernelK θ x : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * ξ * x)‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ x : ℝ, |M x - kernelK θ x| := by
            congr 1; ext x
            rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
              hexp_norm x, mul_one]
        _ ≤ C_L1 / Δ := hL1
    have hK_p : 3 / (2 * |ξ|) ≤ C_dec * (1 / Real.log p) := by
      rw [show 3 / (2 * |ξ|) = (3 / 2) * (1 / |ξ|) by ring, hξ_abs]
      have hlogp_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
      have h3pi : 3 * Real.pi ≤ C_dec := le_trans (by linarith [Real.pi_pos]) (le_max_left _ _)
      calc (3 / 2) * (2 * Real.pi / Real.log p) = (3 * Real.pi) * (1 / Real.log p) := by ring
        _ ≤ C_dec * (1 / Real.log p) := by gcongr
    have hCL1_le : C_L1 / Δ ≤ C_dec * (1 / Δ) := by
      have hCL1 : C_L1 ≤ C_dec := le_trans (le_max_left _ _) (le_max_right _ _)
      have hΔ_pos : 0 < Δ := by linarith
      calc C_L1 / Δ = C_L1 * (1 / Δ) := by ring
        _ ≤ C_dec * (1 / Δ) := by gcongr
    calc ‖fourierHat (fun x : ℝ => (M x : ℂ)) ξ‖
        ≤ ‖fourierHat (fun x : ℝ => (kernelK θ x : ℂ)) ξ‖ +
          ‖fourierHat (fun x : ℝ => (M x : ℂ)) ξ - fourierHat (fun x : ℝ => (kernelK θ x : ℂ)) ξ‖ := by
          simpa [add_comm] using norm_le_norm_add_norm_sub' (fourierHat (fun x : ℝ => (M x : ℂ)) ξ)
            (fourierHat (fun x : ℝ => (kernelK θ x : ℂ)) ξ)
      _ ≤ 3 / (2 * |ξ|) + C_L1 / Δ := add_le_add hK_norm hdiff_norm
      _ ≤ C_dec * (1 / Real.log p) + C_dec * (1 / Δ) := add_le_add hK_p hCL1_le
      _ = C_dec * (1 / Real.log p + 1 / Δ) := by ring
  have hlogp_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hξ_pos : 0 < Real.log p / (2 * Real.pi) := div_pos hlogp_pos (by positivity)
  refine ⟨h_bound_ξ _ hξ_pos.ne' ?_, h_bound_ξ _ (neg_ne_zero.mpr hξ_pos.ne') ?_⟩
  · rw [abs_of_pos hξ_pos, one_div_div]
  · rw [abs_neg, abs_of_pos hξ_pos, one_div_div]

end PolarEvaluation
