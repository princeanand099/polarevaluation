import PolarEvaluation.Basic
import PolarEvaluation.ExternalResults
import PolarEvaluation.ExplicitFormulae

/-!
# High-Moment Estimates for Prime Sums (Section 6 & Lemmas 4.1–4.2)
-/

noncomputable section

open Complex Real MeasureTheory Filter Topology

namespace PolarEvaluation

lemma dirichletChar_norm_eq_one {q : ℕ} (χ : DirichletCharacter ℂ q) {n : ℕ} (h0 : χ n ≠ 0) :
    ‖χ n‖ = 1 := by
  by_cases hq0 : q = 0
  · subst hq0
    have hu : IsUnit (n : ZMod 0) := by
      by_contra hnu
      exact h0 (MulChar.map_nonunit χ hnu)
    have h1 : (n : ℤ) = 1 ∨ (n : ℤ) = -1 := Int.isUnit_iff.mp hu
    rcases h1 with h | h
    · have : (n : ZMod 0) = 1 := h
      rw [this, map_one, norm_one]
    · have : (n : ZMod 0) = -1 := h
      have hsq : χ n * χ n = 1 := by rw [← map_mul, this]; norm_num
      have hnsq : ‖χ n‖ ^ 2 = 1 := by
        rw [sq, ← norm_mul, hsq, norm_one]
      nlinarith [norm_nonneg (χ n)]
  · haveI : NeZero q := ⟨hq0⟩
    have hu : IsUnit (n : ZMod q) := by
      by_contra hnu
      exact h0 (MulChar.map_nonunit χ hnu)
    set m := Fintype.card (ZMod q)ˣ
    have hm : 0 < m := Fintype.card_pos
    have hpow : (χ n) ^ m = 1 := by
      rw [← map_pow, ← hu.unit_spec]
      push_cast
      rw [← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
    have hnorm_pow : ‖χ n‖ ^ m = 1 := by rw [← norm_pow, hpow, norm_one]
    have h1 : ‖χ n‖ ^ m = 1 ^ m := by rw [hnorm_pow, one_pow]
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one hm.ne').mp h1

lemma dirichletChar_norm_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ‖χ n‖ ≤ 1 := by
  by_cases h0 : χ n = 0
  · simp [h0]
  · exact (dirichletChar_norm_eq_one χ h0).le

/-- Helper: general Fourier decay of any `L^1`-close majorant `M` for `K_θ` at any `ξ ≠ 0`. -/
lemma majorant_fourier_decay_any (θ C_L1 Δ₀ : ℝ) (hθ : |θ| ≤ Real.pi / 2) (hΔ₀ : Δ₀ ≥ 1) :
    ∃ C_dec > 0, ∀ (Δ : ℝ) (M : ℝ → ℝ), Δ ≥ Δ₀ →
      Integrable (fun x : ℝ => M x - kernelK θ x) →
      (∫ x : ℝ, |M x - kernelK θ x|) ≤ C_L1 / Δ →
      ∀ ξ : ℝ, ξ ≠ 0 →
        ‖fourierHat (fun x : ℝ => (M x : ℂ)) ξ‖ ≤
          C_dec * (1 / (2 * Real.pi * |ξ|) + 1 / Δ) := by
  refine ⟨max (4 * Real.pi) (max C_L1 1), by positivity, fun Δ M hΔ hInt hL1 ξ hξ => ?_⟩
  set C_dec := max (4 * Real.pi) (max C_L1 1)
  have hK_int : Integrable (fun x : ℝ => kernelK θ x) := kernelK_integrable θ
  have hM_int : Integrable (fun x : ℝ => M x) := by
    have : (fun x : ℝ => M x) = (fun x : ℝ => (M x - kernelK θ x) + kernelK θ x) := by
      ext x; ring
    rw [this]
    exact hInt.add hK_int
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
  have hK_p : 3 / (2 * |ξ|) ≤ C_dec * (1 / (2 * Real.pi * |ξ|)) := by
    have h3pi : 3 * Real.pi ≤ C_dec := le_trans (by linarith [Real.pi_pos]) (le_max_left _ _)
    have h_abs_pos : 0 < |ξ| := abs_pos.mpr hξ
    calc 3 / (2 * |ξ|) = (3 * Real.pi) * (1 / (2 * Real.pi * |ξ|)) := by
          field_simp [Real.pi_ne_zero, h_abs_pos.ne']
      _ ≤ C_dec * (1 / (2 * Real.pi * |ξ|)) := by gcongr
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
    _ ≤ C_dec * (1 / (2 * Real.pi * |ξ|)) + C_dec * (1 / Δ) := add_le_add hK_p hCL1_le
    _ = C_dec * (1 / (2 * Real.pi * |ξ|) + 1 / Δ) := by ring

/-- Chebyshev's bound: `∑_{p ≤ N, p prime} log p ≤ N * log 4`. -/
lemma chebyshev_theta_le : ∀ N : ℕ,
    ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, Real.log p ≤ (N : ℝ) * Real.log 4 := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    rcases le_or_gt N 1 with hN1 | hN2
    · have hemp : (Finset.Icc 2 N).filter Nat.Prime = ∅ := by
        ext p; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]
        omega
      rw [hemp, Finset.sum_empty]
      positivity
    · by_cases hN_eq2 : N = 2
      · subst hN_eq2
        have hset : (Finset.Icc 2 2).filter Nat.Prime = {2} := by
          ext p; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
          constructor
          · intro h; omega
          · rintro rfl; exact ⟨⟨le_rfl, le_rfl⟩, Nat.prime_two⟩
        rw [hset, Finset.sum_singleton]
        have : Real.log (4 : ℕ) = 2 * Real.log 2 := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.cast_pow, Real.log_pow]; norm_num
        push_cast
        have hlog4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
      · rcases Nat.even_or_odd N with ⟨m, hm⟩ | ⟨m, hm⟩
        · -- N = m + m = 2 * m, N > 2 so m ≥ 2 and N is not prime
          have hm2 : m ≥ 2 := by omega
          have hN_not_prime : ¬ Nat.Prime N := by
            intro hp
            have h2dvd : 2 ∣ N := ⟨m, by omega⟩
            rcases hp.eq_one_or_self_of_dvd 2 h2dvd with h21 | h2N
            · omega
            · omega
          have hset : (Finset.Icc 2 N).filter Nat.Prime = (Finset.Icc 2 (N - 1)).filter Nat.Prime := by
            ext p
            simp only [Finset.mem_filter, Finset.mem_Icc]
            constructor
            · rintro ⟨⟨hp2, hpN⟩, hp⟩
              refine ⟨⟨hp2, ?_⟩, hp⟩
              by_contra hlt
              have : p = N := by omega
              subst this; exact hN_not_prime hp
            · rintro ⟨⟨hp2, hpN⟩, hp⟩
              exact ⟨⟨hp2, by omega⟩, hp⟩
          rw [hset]
          have h_ih := ih (N - 1) (by omega)
          have hN_le : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : N - 1 ≤ N)
          have hlog4_pos : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
          exact h_ih.trans (mul_le_mul_of_nonneg_right hN_le hlog4_pos)
        · -- N = 2 * m + 1
          have hm1 : m ≥ 1 := by omega
          have hsplit : (Finset.Icc 2 N).filter Nat.Prime =
              (Finset.Icc 2 (m + 1)).filter Nat.Prime ∪ (Finset.Icc (m + 2) (2 * m + 1)).filter Nat.Prime := by
            ext p
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
            omega
          have hdisj : Disjoint ((Finset.Icc 2 (m + 1)).filter Nat.Prime)
              ((Finset.Icc (m + 2) (2 * m + 1)).filter Nat.Prime) := by
            rw [Finset.disjoint_left]
            intro p hp1 hp2
            simp only [Finset.mem_filter, Finset.mem_Icc] at hp1 hp2
            omega
          rw [hsplit, Finset.sum_union hdisj]
          have h_ih := ih (m + 1) (by omega)
          -- Now bound ∑_{m+2 ≤ p ≤ 2m+1} log p ≤ m * log 4
          set s := (Finset.Icc (m + 2) (2 * m + 1)).filter Nat.Prime
          have hdvd : ∏ p ∈ s, p ∣ Nat.choose (2 * m + 1) m := by
            apply Finset.prod_dvd_of_coprime
            · intro p hp q hq hpq
              simp only [s, Finset.mem_filter] at hp hq
              exact (Nat.coprime_primes hp.2 hq.2).mpr hpq
            · intro p hp
              simp only [s, Finset.mem_filter, Finset.mem_Icc] at hp
              have hchoose := Nat.choose_mul_factorial_mul_factorial (by omega : m ≤ 2 * m + 1)
              have hsub : 2 * m + 1 - m = m + 1 := by omega
              rw [hsub] at hchoose
              have hp_dvd_fac : p ∣ (2 * m + 1)! := hp.2.dvd_factorial.mpr hp.1.2
              rw [← hchoose] at hp_dvd_fac
              have hp_not_m : ¬ p ∣ m ! := by
                rw [hp.2.dvd_factorial]; omega
              have hp_not_m1 : ¬ p ∣ (m + 1)! := by
                rw [hp.2.dvd_factorial]; omega
              rcases hp.2.dvd_mul.mp hp_dvd_fac with h1 | h2
              · rcases hp.2.dvd_mul.mp h1 with h1a | h1b
                · exact h1a
                · exact absurd h1b hp_not_m
              · exact absurd h2 hp_not_m1
          have hchoose_pos : 0 < Nat.choose (2 * m + 1) m := Nat.choose_pos (by omega)
          have hprod_le_choose : ∏ p ∈ s, p ≤ Nat.choose (2 * m + 1) m := Nat.le_of_dvd hchoose_pos hdvd
          have hchoose_le : Nat.choose (2 * m + 1) m ≤ 4 ^ m := by
            have hsum := Nat.sum_range_choose (2 * m + 1)
            have hm_mem : m ∈ Finset.range (2 * m + 2) := Finset.mem_range.mpr (by omega)
            have hm1_mem : m + 1 ∈ Finset.range (2 * m + 2) := Finset.mem_range.mpr (by omega)
            have hpair : Nat.choose (2 * m + 1) m + Nat.choose (2 * m + 1) (m + 1) ≤
                ∑ k ∈ Finset.range (2 * m + 2), Nat.choose (2 * m + 1) k := by
              have h1 := Finset.add_sum_erase (Finset.range (2 * m + 2)) (fun k => Nat.choose (2 * m + 1) k) hm_mem
              have hm1_mem' : m + 1 ∈ (Finset.range (2 * m + 2)).erase m :=
                Finset.mem_erase.mpr ⟨by omega, hm1_mem⟩
              have h2 := Finset.add_sum_erase ((Finset.range (2 * m + 2)).erase m)
                (fun k => Nat.choose (2 * m + 1) k) hm1_mem'
              omega
            have hsymm : Nat.choose (2 * m + 1) (m + 1) = Nat.choose (2 * m + 1) m := by
              have := Nat.choose_symm_add m (m + 1)
              simpa [show m + (m + 1) = 2 * m + 1 by omega] using this.symm
            rw [hsymm, hsum] at hpair
            have hpow : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by
              rw [pow_succ, show 2 * m = 2 * m from rfl, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
              ring
            omega
          have hprod_le : (∏ p ∈ s, (p : ℝ)) ≤ (4 : ℝ) ^ m := by
            exact_mod_cast (hprod_le_choose.trans hchoose_le)
          have hprod_pos : (0 : ℝ) < ∏ p ∈ s, (p : ℝ) := by
            apply Finset.prod_pos
            intro p hp
            simp only [s, Finset.mem_filter] at hp
            exact_mod_cast hp.2.pos
          have hsum_log : ∑ p ∈ s, Real.log p ≤ (m : ℝ) * Real.log 4 := by
            have hlog_prod : ∑ p ∈ s, Real.log p = Real.log (∏ p ∈ s, (p : ℝ)) := by
              rw [Real.log_prod]
              intro p hp
              simp only [s, Finset.mem_filter] at hp
              exact_mod_cast hp.2.ne_zero
            rw [hlog_prod]
            calc Real.log (∏ p ∈ s, (p : ℝ))
                ≤ Real.log ((4 : ℝ) ^ m) := Real.log_le_log hprod_pos hprod_le
              _ = (m : ℝ) * Real.log 4 := by rw [Real.log_pow]
          have hN_cast : (N : ℝ) = ((m + 1 : ℕ) : ℝ) + (m : ℝ) := by
            push_cast [hm]; ring
          rw [hN_cast, add_mul]
          exact add_le_add h_ih hsum_log

/-- Abel summation for sums over primes `2 ≤ p ≤ N`. -/
lemma abel_sum_primes (f g : ℕ → ℝ) : ∀ N : ℕ, N ≥ 2 →
    ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, f p * g p =
      (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, f p) * g N +
        ∑ k ∈ Finset.Ico 2 N, (∑ p ∈ (Finset.Icc 2 k).filter Nat.Prime, f p) * (g k - g (k + 1)) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    have hIcc : (Finset.Icc 2 (N + 1)).filter Nat.Prime =
        if Nat.Prime (N + 1) then insert (N + 1) ((Finset.Icc 2 N).filter Nat.Prime)
        else (Finset.Icc 2 N).filter Nat.Prime := by
      ext p
      split_ifs with hp
      · simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨h1, h2⟩, hp'⟩
          rcases eq_or_lt_of_le h2 with rfl | hlt
          · left; rfl
          · right; exact ⟨⟨h1, by omega⟩, hp'⟩
        · rintro (rfl | ⟨⟨h1, h2⟩, hp'⟩)
          · exact ⟨⟨by omega, le_rfl⟩, hp⟩
          · exact ⟨⟨h1, by omega⟩, hp'⟩
      · simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨h1, h2⟩, hp'⟩
          refine ⟨⟨h1, ?_⟩, hp'⟩
          by_contra hlt
          have : p = N + 1 := by omega
          subst this; exact hp hp'
        · rintro ⟨⟨h1, h2⟩, hp'⟩
          exact ⟨⟨h1, by omega⟩, hp'⟩
    have hnot_mem : N + 1 ∉ (Finset.Icc 2 N).filter Nat.Prime := by
      simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    have hIco : Finset.Ico 2 (N + 1) = insert N (Finset.Ico 2 N) := by
      rw [← Finset.Ico_insert_right (by omega : 2 ≤ N + 1)]
      simp
    have hN_not_Ico : N ∉ Finset.Ico 2 N := by simp
    rw [Finset.sum_Ico_succ_top hN]
    by_cases hp : Nat.Prime (N + 1)
    · rw [hIcc, if_pos hp, Finset.sum_insert hnot_mem, Finset.sum_insert hnot_mem, ih]
      ring
    · rw [hIcc, if_neg hp, ih]
      ring

/-- Mertens' 1st Theorem (upper bound): `∑_{p ≤ N} log p / p ≤ log 4 * (log N + 1)`. -/
lemma mertens_first (N : ℕ) (hN : N ≥ 2) :
    ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, Real.log p / p ≤ Real.log 4 * (Real.log N + 1) := by
  have h_abel := abel_sum_primes (fun p => Real.log p) (fun k => 1 / (k : ℝ)) N hN
  simp_rw [div_eq_mul_one_div]
  rw [h_abel]
  have h1 : (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, Real.log p) * (1 / (N : ℝ)) ≤ Real.log 4 := by
    have hN_pos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    calc (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, Real.log p) * (1 / (N : ℝ))
        ≤ ((N : ℝ) * Real.log 4) * (1 / (N : ℝ)) := by
          gcongr
          exact chebyshev_theta_le N
      _ = Real.log 4 := by field_simp [hN_pos.ne']
  have h2 : ∑ k ∈ Finset.Ico 2 N, (∑ p ∈ (Finset.Icc 2 k).filter Nat.Prime, Real.log p) *
        (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) ≤
      Real.log 4 * Real.log N := by
    have hterm : ∀ k ∈ Finset.Ico 2 N,
        (∑ p ∈ (Finset.Icc 2 k).filter Nat.Prime, Real.log p) *
          (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) ≤
        Real.log 4 * (Real.log (k + 1 : ℕ) - Real.log k) := by
      intro k hk
      simp only [Finset.mem_Ico] at hk
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      have hdiff_nonneg : 0 ≤ 1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) := by
        rw [sub_nonneg]
        apply one_div_le_one_div_of_le hk_pos
        exact_mod_cast (by omega : k ≤ k + 1)
      have hcheb : (∑ p ∈ (Finset.Icc 2 k).filter Nat.Prime, Real.log p) *
          (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) ≤
          ((k : ℝ) * Real.log 4) * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right (chebyshev_theta_le k) hdiff_nonneg
      have hsimp : ((k : ℝ) * Real.log 4) * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) =
          Real.log 4 * (1 / ((k + 1 : ℕ) : ℝ)) := by
        push_cast; field_simp [hk_pos.ne', (by positivity : (k : ℝ) + 1 ≠ 0)]; ring
      have hlog_step : 1 / ((k + 1 : ℕ) : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log k := by
        have h_ineq := Real.log_le_sub_one_of_pos (div_pos hk_pos hk1_pos)
        rw [Real.log_div hk_pos.ne' hk1_pos.ne'] at h_ineq
        have heq : 1 - (k : ℝ) / ((k + 1 : ℕ) : ℝ) = 1 / ((k + 1 : ℕ) : ℝ) := by
          push_cast; field_simp [(by positivity : (k : ℝ) + 1 ≠ 0)]; ring
        linarith
      rw [hsimp] at hcheb
      exact hcheb.trans (mul_le_mul_of_nonneg_left hlog_step (Real.log_nonneg (by norm_num)))
    calc ∑ k ∈ Finset.Ico 2 N, (∑ p ∈ (Finset.Icc 2 k).filter Nat.Prime, Real.log p) *
          (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))
        ≤ ∑ k ∈ Finset.Ico 2 N, Real.log 4 * (Real.log (k + 1 : ℕ) - Real.log k) :=
          Finset.sum_le_sum hterm
      _ = Real.log 4 * ∑ k ∈ Finset.Ico 2 N, (Real.log (k + 1 : ℕ) - Real.log k) := by
          rw [← Finset.mul_sum]
      _ = Real.log 4 * (Real.log N - Real.log 2) := by
          congr 1
          exact Finset.sum_Ico_sub' (fun k : ℕ => Real.log k) hN
      _ ≤ Real.log 4 * Real.log N := by
          gcongr
          linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  linarith

/-- Mertens' 2nd Theorem (upper bound): `∑_{p ≤ N} 1 / p ≤ 10 * (log (log N) + 2)` for `N ≥ 3`. -/
lemma mertens_second (N : ℕ) (hN : N ≥ 3) :
    ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, (1 : ℝ) / p ≤ 10 * (Real.log (Real.log N) + 2) := by
  have hN2 : N ≥ 2 := by omega
  have h_abel := abel_sum_primes (fun p => Real.log p / p) (fun k => 1 / Real.log k) N hN2
  have h_lhs : ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, (1 : ℝ) / p =
      ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, (Real.log p / p) * (1 / Real.log p) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    have hlogp : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < p))).ne'
    field_simp [hlogp]
  rw [h_lhs, h_abel]
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN_pos : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogN_ge : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN2)
  have h1 : (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, Real.log p / p) * (1 / Real.log N) ≤
      Real.log 4 * (1 + 1 / Real.log 2) := by
    have hm1 := mertens_first N hN2
    calc (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, Real.log p / p) * (1 / Real.log N)
        ≤ (Real.log 4 * (Real.log N + 1)) * (1 / Real.log N) := by
          gcongr
      _ = Real.log 4 * (1 + 1 / Real.log N) := by field_simp [hlogN_pos.ne']
      _ ≤ Real.log 4 * (1 + 1 / Real.log 2) := by
          gcongr
  have h_Ico_split : ∑ k ∈ Finset.Ico 2 N,
        (∑ p ∈ (Finset.Icc 2 k).filter Nat.Prime, Real.log p / p) *
          (1 / Real.log k - 1 / Real.log (k + 1 : ℕ)) =
      (∑ p ∈ (Finset.Icc 2 2).filter Nat.Prime, Real.log p / p) * (1 / Real.log 2 - 1 / Real.log 3) +
      ∑ k ∈ Finset.Ico 3 N,
        (∑ p ∈ (Finset.Icc 2 k).filter Nat.Prime, Real.log p / p) *
          (1 / Real.log k - 1 / Real.log (k + 1 : ℕ)) := by
    rw [Finset.sum_eq_sum_Ico_succ_bot hN]
    simp
  rw [h_Ico_split]
  have h2_bot : (∑ p ∈ (Finset.Icc 2 2).filter Nat.Prime, Real.log p / p) * (1 / Real.log 2 - 1 / Real.log 3) ≤
      Real.log 4 * (1 + 1 / Real.log 2) := by
    have hset : (Finset.Icc 2 2).filter Nat.Prime = {2} := by
      ext p; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      exact ⟨fun h => by omega, fun h => h ▸ ⟨⟨le_rfl, le_rfl⟩, Nat.prime_two⟩⟩
    rw [hset, Finset.sum_singleton]
    have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hle : 1 / Real.log 2 - 1 / Real.log 3 ≤ 1 / Real.log 2 := by linarith [div_pos one_pos hlog3_pos]
    have hdiff_nonneg : 0 ≤ 1 / Real.log 2 - 1 / Real.log 3 := by
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le hlog2_pos (Real.log_le_log (by norm_num) (by norm_num))
    calc (Real.log 2 / 2) * (1 / Real.log 2 - 1 / Real.log 3)
        ≤ (Real.log 2 / 2) * (1 / Real.log 2) := by gcongr
      _ = 1 / 2 := by field_simp [hlog2_pos.ne']
      _ ≤ Real.log 4 * (1 + 1 / Real.log 2) := by
          have hlog4_ge : (1 : ℝ) ≤ Real.log 4 := by
            have he : Real.exp 1 < 4 := Real.exp_one_lt_d9.trans (by norm_num)
            rw [← Real.log_exp 1]
            exact Real.log_le_log (Real.exp_pos 1) he.le
          nlinarith [div_pos one_pos hlog2_pos]
  have h2_tail : ∑ k ∈ Finset.Ico 3 N,
        (∑ p ∈ (Finset.Icc 2 k).filter Nat.Prime, Real.log p / p) *
          (1 / Real.log k - 1 / Real.log (k + 1 : ℕ)) ≤
      Real.log 4 * (Real.log (Real.log N) + 1 / Real.log 3 + 1) := by
    have hterm : ∀ k ∈ Finset.Ico 3 N,
        (∑ p ∈ (Finset.Icc 2 k).filter Nat.Prime, Real.log p / p) *
          (1 / Real.log k - 1 / Real.log (k + 1 : ℕ)) ≤
        Real.log 4 * ((Real.log (Real.log (k + 1 : ℕ)) - Real.log (Real.log k)) +
          (1 / Real.log k - 1 / Real.log (k + 1 : ℕ))) := by
      intro k hk
      simp only [Finset.mem_Ico] at hk
      have hk2 : k ≥ 2 := by omega
      have hlogk_pos : 0 < Real.log k := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
      have hlogk1_pos : 0 < Real.log (k + 1 : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k + 1))
      have hdiff_nonneg : 0 ≤ 1 / Real.log k - 1 / Real.log (k + 1 : ℕ) := by
        rw [sub_nonneg]
        apply one_div_le_one_div_of_le hlogk_pos
        exact Real.log_le_log (by exact_mod_cast (by omega : 0 < k)) (by exact_mod_cast (by omega : k ≤ k + 1))
      have hm1 := mul_le_mul_of_nonneg_right (mertens_first k hk2) hdiff_nonneg
      have h_eq : Real.log 4 * (Real.log k + 1) * (1 / Real.log k - 1 / Real.log (k + 1 : ℕ)) =
          Real.log 4 * (Real.log k * (1 / Real.log k - 1 / Real.log (k + 1 : ℕ)) +
            (1 / Real.log k - 1 / Real.log (k + 1 : ℕ))) := by ring
      have h_loglog : Real.log k * (1 / Real.log k - 1 / Real.log (k + 1 : ℕ)) ≤
          Real.log (Real.log (k + 1 : ℕ)) - Real.log (Real.log k) := by
        have h_ineq := Real.log_le_sub_one_of_pos (div_pos hlogk_pos hlogk1_pos)
        rw [Real.log_div hlogk_pos.ne' hlogk1_pos.ne'] at h_ineq
        have heq : 1 - Real.log k / Real.log (k + 1 : ℕ) =
            Real.log k * (1 / Real.log k - 1 / Real.log (k + 1 : ℕ)) := by
          field_simp [hlogk_pos.ne', hlogk1_pos.ne']
        linarith
      rw [h_eq] at hm1
      exact hm1.trans (mul_le_mul_of_nonneg_left (add_le_add_right h_loglog _) (Real.log_nonneg (by norm_num)))
    calc ∑ k ∈ Finset.Ico 3 N,
          (∑ p ∈ (Finset.Icc 2 k).filter Nat.Prime, Real.log p / p) *
            (1 / Real.log k - 1 / Real.log (k + 1 : ℕ))
        ≤ ∑ k ∈ Finset.Ico 3 N, Real.log 4 * ((Real.log (Real.log (k + 1 : ℕ)) - Real.log (Real.log k)) +
            (1 / Real.log k - 1 / Real.log (k + 1 : ℕ))) := Finset.sum_le_sum hterm
      _ = Real.log 4 * ((∑ k ∈ Finset.Ico 3 N, (Real.log (Real.log (k + 1 : ℕ)) - Real.log (Real.log k))) +
            (∑ k ∈ Finset.Ico 3 N, (1 / Real.log k - 1 / Real.log (k + 1 : ℕ)))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ = Real.log 4 * ((Real.log (Real.log N) - Real.log (Real.log 3)) +
            (1 / Real.log 3 - 1 / Real.log N)) := by
          congr 2
          · exact Finset.sum_Ico_sub' (fun k : ℕ => Real.log (Real.log k)) hN
          · have := Finset.sum_Ico_sub' (fun k : ℕ => -(1 / Real.log k)) hN
            simpa [sub_neg_eq_add, add_comm] using this
      _ ≤ Real.log 4 * (Real.log (Real.log N) + 1 / Real.log 3 + 1) := by
          have hlog3_gt1 : 1 < Real.log 3 := by
            have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
            rw [← Real.log_exp 1]
            exact Real.log_lt_log (Real.exp_pos 1) he
          have hloglog3_nonneg : 0 ≤ Real.log (Real.log 3) := Real.log_nonneg hlog3_gt1.le
          gcongr
          linarith [div_pos one_pos hlogN_pos]
  have hlog4_le : Real.log 4 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    rw [one_div, Real.log_inv] at h
    linarith
  have hlog3_ge : (1 : ℝ) ≤ Real.log 3 := by
    have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) he.le
  have hloglogN_nonneg : 0 ≤ Real.log (Real.log N) := by
    apply Real.log_nonneg
    exact hlog3_ge.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hN))
  have h_inv2 : 1 / Real.log 2 ≤ 2 := by
    rw [div_le_iff₀ hlog2_pos]; linarith
  have h_inv3 : 1 / Real.log 3 ≤ 1 := by
    exact div_le_one_of_le₀ hlog3_ge (by positivity)
  nlinarith

/-- **Lemma 4.1** (Prime-square and higher-power tail bounds). -/
theorem prime_power_tail_bounds (θ C_L1 Δ₀ : ℝ) (hθ : |θ| ≤ Real.pi / 2) (hΔ₀ : Δ₀ ≥ 1) :
    ∃ C_tail > 0, ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (Δ : ℝ) (M : ℝ → ℝ),
      Δ ≥ Δ₀ →
      Integrable (fun x : ℝ => M x - kernelK θ x) →
      (∫ x : ℝ, |M x - kernelK θ x|) ≤ C_L1 / Δ →
      (∫ x : ℝ, |M x|) ≤ C_L1 →
      ∀ t : ℝ,
        let X := Real.exp (2 * Real.pi * Δ)
        let h_hat := fourierHat (fun x : ℝ => (M x : ℂ))
        |primeSum2 q χ h_hat X t| ≤ C_tail * Real.log (Real.log X) ∧
        |primeSumGe3 q χ h_hat X t| ≤ C_tail := by
  obtain ⟨C_dec, hC_dec, h_dec⟩ := majorant_fourier_decay_any θ C_L1 Δ₀ hθ hΔ₀
  have hsumm_54 : Summable (fun n : ℕ => (n : ℝ) ^ (-5 / 4 : ℝ)) := by
    rw [Real.summable_nat_rpow_inv.symm]
    norm_num
  set S_54 := ∑' n : ℕ, (n : ℝ) ^ (-5 / 4 : ℝ)
  have hS_54_nonneg : 0 ≤ S_54 := tsum_nonneg (fun n => by positivity)
  refine ⟨max (100 * C_dec) (100 * max C_L1 1 * (S_54 + 1)), by positivity,
    fun q χ Δ M hΔ hInt hL1 hL1_M t => ?_⟩
  set C_tail := max (100 * C_dec) (100 * max C_L1 1 * (S_54 + 1))
  set X := Real.exp (2 * Real.pi * Δ)
  set h_hat := fourierHat (fun x : ℝ => (M x : ℂ))
  have hX_gt : Real.exp (2 * Real.pi) ≤ X := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hlogX_eq : Real.log X = 2 * Real.pi * Δ := Real.log_exp _
  have hloglogX_ge : 1 ≤ Real.log (Real.log X) := by
    rw [hlogX_eq]
    have h2pi_ge : Real.exp 1 ≤ 2 * Real.pi := by
      have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
      linarith [Real.two_le_pi]
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by nlinarith)
  have hK_int : Integrable (fun x : ℝ => kernelK θ x) := kernelK_integrable θ
  have hM_int : Integrable (fun x : ℝ => M x) := by
    have : (fun x : ℝ => M x) = (fun x : ℝ => (M x - kernelK θ x) + kernelK θ x) := by ext x; ring
    rw [this]; exact hInt.add hK_int
  have h_hat_L1 : ∀ ξ : ℝ, ‖h_hat ξ‖ ≤ C_L1 := by
    intro ξ
    have h_int : Integrable (fun x : ℝ => (M x : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * ξ * x)) := by
      refine hM_int.norm.mono (by fun_prop) ?_
      filter_upwards with x
      have hn : ‖Complex.exp (-2 * Real.pi * Complex.I * ξ * x)‖ = 1 := by
        have : -2 * (Real.pi : ℂ) * Complex.I * ↑ξ * ↑x = ((-2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I]
      rw [norm_mul, Complex.norm_real, hn, mul_one, norm_norm]
    calc ‖h_hat ξ‖ ≤ ∫ x : ℝ, ‖(M x : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * ξ * x)‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ x : ℝ, |M x| := by
          congr 1; ext x
          have hn : ‖Complex.exp (-2 * Real.pi * Complex.I * ξ * x)‖ = 1 := by
            have : -2 * (Real.pi : ℂ) * Complex.I * ↑ξ * ↑x = ((-2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I := by
              push_cast; ring
            rw [this, Complex.norm_exp_ofReal_mul_I]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hn, mul_one]
      _ ≤ C_L1 := hL1_M
  have hchi_le : ∀ n : ℕ, ‖χ n‖ ≤ 1 := by
    intro n
    by_cases h0 : χ n = 0
    · simp [h0]
    · exact (dirichletChar_norm_eq_one χ h0).le
  have hX_ge_16 : (16 : ℝ) ≤ X := by
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h4 : (4 : ℝ) ≤ 2 * Real.pi * Δ := by nlinarith [Real.two_le_pi]
    calc (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := by gcongr
      _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ X := Real.exp_le_exp.mpr h4
  have hsqrtX_ge_4 : 4 ≤ Real.sqrt X := by
    rw [Real.le_sqrt' (by norm_num)]
    linarith
  have hN₂_ge_3 : Nat.floor (Real.sqrt X) ≥ 3 := by
    have : (3 : ℕ) ≤ Nat.floor (Real.sqrt X) := Nat.le_floor (by norm_num; linarith)
    exact this
  constructor
  · -- Bound |primeSum2|
    unfold primeSum2
    set N₂ := Nat.floor (Real.sqrt X)
    have h_term : ∀ p ∈ (Finset.Icc 2 N₂).filter Nat.Prime,
        |(Real.log p / (p : ℝ)) *
          (χ (p ^ 2) * h_hat (-(Real.log (p ^ 2) / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log (p ^ 2)) +
           star (χ (p ^ 2)) * h_hat (Real.log (p ^ 2) / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log (p ^ 2))).re| ≤
        2 * C_dec * (1 / (p : ℝ) + (1 / Δ) * (Real.log p / (p : ℝ))) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
      have hlogp_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.2.one_lt)
      have hξ_pos : 0 < Real.log (p ^ 2) / (2 * Real.pi) := by
        have : Real.log ((p : ℝ) ^ 2) = 2 * Real.log p := by rw [Real.log_pow]; norm_num
        rw [Nat.cast_pow, this]
        positivity
      have hdec1 := h_dec Δ M hΔ hInt hL1 (Real.log (p ^ 2) / (2 * Real.pi)) hξ_pos.ne'
      have hdec2 := h_dec Δ M hΔ hInt hL1 (-(Real.log (p ^ 2) / (2 * Real.pi))) (neg_ne_zero.mpr hξ_pos.ne')
      have h_abs_ξ : 1 / (2 * Real.pi * |Real.log (p ^ 2) / (2 * Real.pi)|) ≤ 1 / Real.log p := by
        rw [abs_of_pos hξ_pos]
        have heq : 2 * Real.pi * (Real.log (p ^ 2) / (2 * Real.pi)) = 2 * Real.log p := by
          field_simp [Real.pi_ne_zero]
          rw [Nat.cast_pow, Real.log_pow]; norm_num
        rw [heq]
        exact one_div_le_one_div_of_le hlogp_pos (by linarith)
      have h_abs_nξ : 1 / (2 * Real.pi * |-(Real.log (p ^ 2) / (2 * Real.pi))|) ≤ 1 / Real.log p := by
        rw [abs_neg]; exact h_abs_ξ
      have hbd1 : ‖h_hat (Real.log (p ^ 2) / (2 * Real.pi))‖ ≤ C_dec * (1 / Real.log p + 1 / Δ) :=
        hdec1.trans (mul_le_mul_of_nonneg_left (add_le_add h_abs_ξ le_rfl) hC_dec.le)
      have hbd2 : ‖h_hat (-(Real.log (p ^ 2) / (2 * Real.pi)))‖ ≤ C_dec * (1 / Real.log p + 1 / Δ) :=
        hdec2.trans (mul_le_mul_of_nonneg_left (add_le_add h_abs_nξ le_rfl) hC_dec.le)
      have he1 : ‖Complex.exp (-Complex.I * t * Real.log (p ^ 2))‖ = 1 := by
        have : -Complex.I * ↑t * ↑(Real.log (p ^ 2)) = ((-t * Real.log (p ^ 2) : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I]
      have he2 : ‖Complex.exp (Complex.I * t * Real.log (p ^ 2))‖ = 1 := by
        have : Complex.I * ↑t * ↑(Real.log (p ^ 2)) = ((t * Real.log (p ^ 2) : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I]
      have hre_bd : |(χ (p ^ 2) * h_hat (-(Real.log (p ^ 2) / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log (p ^ 2)) +
           star (χ (p ^ 2)) * h_hat (Real.log (p ^ 2) / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log (p ^ 2))).re| ≤
          2 * C_dec * (1 / Real.log p + 1 / Δ) := by
        calc |(_).re| ≤ ‖_‖ := Complex.abs_re_le_norm _
          _ ≤ ‖χ (p ^ 2) * h_hat (-(Real.log (p ^ 2) / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log (p ^ 2))‖ +
              ‖star (χ (p ^ 2)) * h_hat (Real.log (p ^ 2) / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log (p ^ 2))‖ := norm_add_le _ _
          _ = ‖χ (p ^ 2)‖ * ‖h_hat (-(Real.log (p ^ 2) / (2 * Real.pi)))‖ * 1 +
              ‖χ (p ^ 2)‖ * ‖h_hat (Real.log (p ^ 2) / (2 * Real.pi))‖ * 1 := by
              rw [norm_mul, norm_mul, norm_mul, norm_mul, he1, he2, norm_star]
          _ ≤ 1 * (C_dec * (1 / Real.log p + 1 / Δ)) * 1 + 1 * (C_dec * (1 / Real.log p + 1 / Δ)) * 1 := by
              gcongr <;> exact hchi_le _
          _ = 2 * C_dec * (1 / Real.log p + 1 / Δ) := by ring
      rw [abs_mul, abs_of_nonneg (div_nonneg hlogp_pos.le hp_pos.le)]
      calc (Real.log p / (p : ℝ)) * |(_).re|
          ≤ (Real.log p / (p : ℝ)) * (2 * C_dec * (1 / Real.log p + 1 / Δ)) := by gcongr
        _ = 2 * C_dec * (1 / (p : ℝ) + (1 / Δ) * (Real.log p / (p : ℝ))) := by
            field_simp [hlogp_pos.ne', hp_pos.ne']; ring
    have hsum_bd : |∑ p ∈ (Finset.Icc 2 N₂).filter Nat.Prime,
          (Real.log p / (p : ℝ)) *
            (χ (p ^ 2) * h_hat (-(Real.log (p ^ 2) / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log (p ^ 2)) +
             star (χ (p ^ 2)) * h_hat (Real.log (p ^ 2) / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log (p ^ 2))).re| ≤
        2 * C_dec * (∑ p ∈ (Finset.Icc 2 N₂).filter Nat.Prime, (1 : ℝ) / p +
          (1 / Δ) * ∑ p ∈ (Finset.Icc 2 N₂).filter Nat.Prime, Real.log p / p) := by
      calc |∑ p ∈ _, _|
          ≤ ∑ p ∈ _, |_| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p ∈ _, 2 * C_dec * (1 / (p : ℝ) + (1 / Δ) * (Real.log p / (p : ℝ))) := Finset.sum_le_sum h_term
        _ = 2 * C_dec * (∑ p ∈ _, (1 : ℝ) / p + (1 / Δ) * ∑ p ∈ _, Real.log p / p) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hN₂_le_X : (N₂ : ℝ) ≤ X := by
      have h1 : (N₂ : ℝ) ≤ Real.sqrt X := Nat.floor_le (Real.sqrt_nonneg X)
      have h2 : Real.sqrt X ≤ X := by
        rw [Real.sqrt_le_left (by linarith)]
        nlinarith
      exact h1.trans h2
    have hm2 : ∑ p ∈ (Finset.Icc 2 N₂).filter Nat.Prime, (1 : ℝ) / p ≤ 30 * Real.log (Real.log X) := by
      have h1 := mertens_second N₂ hN₂_ge_3
      have hloglog : Real.log (Real.log N₂) ≤ Real.log (Real.log X) :=
        Real.log_le_log (Real.log_pos (by exact_mod_cast (by omega : 1 < N₂)))
          (Real.log_le_log (by exact_mod_cast (by omega : 0 < N₂)) hN₂_le_X)
      nlinarith
    have hm1 : (1 / Δ) * ∑ p ∈ (Finset.Icc 2 N₂).filter Nat.Prime, Real.log p / p ≤ 20 * Real.log (Real.log X) := by
      have h1 := mertens_first N₂ (by omega)
      have hlogN₂ : Real.log N₂ ≤ 2 * Real.pi * Δ := by
        rw [← hlogX_eq]
        exact Real.log_le_log (by exact_mod_cast (by omega : 0 < N₂)) hN₂_le_X
      have hlog4_le : Real.log 4 ≤ 2 := by
        have hlog2_le : Real.log 2 ≤ 1 := by
          have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          rw [← Real.log_exp 1]; exact Real.log_le_log (by norm_num) he
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; linarith
      have hΔ_pos : 0 < Δ := by linarith
      have hpi_lt : Real.pi < 4 := Real.pi_lt_four
      calc (1 / Δ) * ∑ p ∈ _, Real.log p / p
          ≤ (1 / Δ) * (Real.log 4 * (Real.log N₂ + 1)) := by gcongr
        _ ≤ (1 / Δ) * (2 * (2 * Real.pi * Δ + 1)) := by gcongr
        _ = 4 * Real.pi + 2 / Δ := by field_simp [hΔ_pos.ne']; ring
        _ ≤ 4 * 4 + 2 / 1 := by gcongr; linarith
        _ = 18 := by norm_num
        _ ≤ 20 * Real.log (Real.log X) := by nlinarith [hloglogX_ge]
    rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
    have h2pi_ge : 1 / (2 * Real.pi) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [Real.two_le_pi]
    calc (1 / (2 * Real.pi)) * |∑ p ∈ _, _|
        ≤ 1 * (2 * C_dec * (30 * Real.log (Real.log X) + 20 * Real.log (Real.log X))) := by
          gcongr
      _ = 100 * C_dec * Real.log (Real.log X) := by ring
      _ ≤ C_tail * Real.log (Real.log X) := by
          gcongr
          exact le_trans (by linarith) (le_max_left _ _)
  · -- Bound |primeSumGe3|
    unfold primeSumGe3 primePowerSum primeSum1 primeSum2
    set N := Nat.floor X
    set N₂ := Nat.floor (Real.sqrt X)
    let f : ℕ → ℝ := fun n =>
      (1 / (2 * Real.pi)) * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
        (χ n * h_hat (-(Real.log n / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log n) +
         star (χ n) * h_hat (Real.log n / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log n)).re
    have hP1 : (1 / (2 * Real.pi)) * ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
          (Real.log p / Real.sqrt p) *
            (χ p * h_hat (-(Real.log p / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log p) +
             star (χ p) * h_hat (Real.log p / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log p)).re =
        ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, f p := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      simp only [Finset.mem_filter] at hp
      dsimp only [f]
      rw [ArithmeticFunction.vonMangoldt_apply_prime hp.2]
      ring
    have hP2 : (1 / (2 * Real.pi)) * ∑ p ∈ (Finset.Icc 2 N₂).filter Nat.Prime,
          (Real.log p / (p : ℝ)) *
            (χ (p ^ 2) * h_hat (-(Real.log (p ^ 2) / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log (p ^ 2)) +
             star (χ (p ^ 2)) * h_hat (Real.log (p ^ 2) / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log (p ^ 2))).re =
        ∑ p ∈ (Finset.Icc 2 N₂).filter Nat.Prime, f (p ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      simp only [Finset.mem_filter] at hp
      dsimp only [f]
      have hv : ArithmeticFunction.vonMangoldt (p ^ 2) = Real.log p := by
        rw [ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : 2 ≠ 0),
          ArithmeticFunction.vonMangoldt_apply_prime hp.2]
      have hsq : Real.sqrt ((p ^ 2 : ℕ) : ℝ) = (p : ℝ) := by
        rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg p)]
      rw [hv, hsq]
      ring
    have hP_all : (1 / (2 * Real.pi)) * ∑ n ∈ Finset.Icc 2 N,
          ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
            (χ n * h_hat (-(Real.log n / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log n) +
             star (χ n) * h_hat (Real.log n / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log n)).re =
        ∑ n ∈ Finset.Icc 2 N, f n := by
      rw [Finset.mul_sum]; rfl
    rw [hP_all, hP1, hP2]
    have h_sub1 : (Finset.Icc 2 N).filter Nat.Prime ⊆ Finset.Icc 2 N := Finset.filter_subset _ _
    have h_sub2 : ((Finset.Icc 2 N₂).filter Nat.Prime).image (· ^ 2) ⊆
        Finset.Icc 2 N \ (Finset.Icc 2 N).filter Nat.Prime := by
      intro n hn
      rcases Finset.mem_image.mp hn with ⟨p, hp, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp
      rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · nlinarith [hp.1.1]
      · refine Nat.le_floor ?_
        have hp_le : (p : ℝ) ≤ Real.sqrt X := (Nat.le_floor_iff (Real.sqrt_nonneg X)).mp hp.1.2
        have hsq : (p : ℝ) ^ 2 ≤ Real.sqrt X ^ 2 := by nlinarith [Nat.cast_nonneg p]
        rwa [Nat.cast_pow, Real.sq_sqrt (by linarith)] at hsq
      · intro hmem
        exact (Nat.Prime.not_prime_pow (by norm_num : 2 ≠ 1) (p := p)) hmem.2
    have h_inj : ∀ p ∈ (Finset.Icc 2 N₂).filter Nat.Prime,
        ∀ q₁ ∈ (Finset.Icc 2 N₂).filter Nat.Prime, p ^ 2 = q₁ ^ 2 → p = q₁ := by
      intro p _ q₁ _ h
      nlinarith
    have hP2_img : ∑ p ∈ (Finset.Icc 2 N₂).filter Nat.Prime, f (p ^ 2) =
        ∑ n ∈ ((Finset.Icc 2 N₂).filter Nat.Prime).image (· ^ 2), f n :=
      (Finset.sum_image h_inj).symm
    rw [← Finset.sum_sdiff h_sub1, add_sub_cancel_right, hP2_img, ← Finset.sum_sdiff h_sub2,
      add_sub_cancel_right]
    set S_rest := (Finset.Icc 2 N \ (Finset.Icc 2 N).filter Nat.Prime) \
      ((Finset.Icc 2 N₂).filter Nat.Prime).image (· ^ 2)
    have hS_ge3_eq : ∑ n ∈ S_rest, f n =
        ∑ n ∈ S_rest.filter IsPrimePow, f n := by
      rw [← Finset.sum_filter_add_sum_filter_not S_rest IsPrimePow]
      have h0 : ∑ n ∈ S_rest.filter (fun n => ¬ IsPrimePow n), f n = 0 := by
        refine Finset.sum_eq_zero fun n hn => ?_
        simp only [Finset.mem_filter] at hn
        dsimp only [f]
        rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn.2]
        simp
      rw [h0, add_zero]
    rw [hS_ge3_eq]
    have h_f_bd : ∀ n : ℕ, n ≥ 2 →
        |f n| ≤ max C_L1 1 * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) := by
      intro n hn
      dsimp only [f]
      have h_vm_nonneg : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
        ArithmeticFunction.vonMangoldt_nonneg
      have h_re_bd : |(χ n * h_hat (-(Real.log n / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log n) +
           star (χ n) * h_hat (Real.log n / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log n)).re| ≤
          2 * max C_L1 1 := by
        have he1 : ‖Complex.exp (-Complex.I * t * Real.log n)‖ = 1 := by
          have : -Complex.I * ↑t * ↑(Real.log n) = ((-t * Real.log n : ℝ) : ℂ) * Complex.I := by
            push_cast; ring
          rw [this, Complex.norm_exp_ofReal_mul_I]
        have he2 : ‖Complex.exp (Complex.I * t * Real.log n)‖ = 1 := by
          have : Complex.I * ↑t * ↑(Real.log n) = ((t * Real.log n : ℝ) : ℂ) * Complex.I := by
            push_cast; ring
          rw [this, Complex.norm_exp_ofReal_mul_I]
        calc |(_).re| ≤ ‖_‖ := Complex.abs_re_le_norm _
          _ ≤ ‖χ n * h_hat (-(Real.log n / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log n)‖ +
              ‖star (χ n) * h_hat (Real.log n / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log n)‖ := norm_add_le _ _
          _ = ‖χ n‖ * ‖h_hat (-(Real.log n / (2 * Real.pi)))‖ * 1 +
              ‖χ n‖ * ‖h_hat (Real.log n / (2 * Real.pi))‖ * 1 := by
              rw [norm_mul, norm_mul, norm_mul, norm_mul, he1, he2, norm_star]
          _ ≤ 1 * max C_L1 1 * 1 + 1 * max C_L1 1 * 1 := by
              gcongr
              · exact hchi_le n
              · exact (h_hat_L1 _).trans (le_max_left _ _)
              · exact hchi_le n
              · exact (h_hat_L1 _).trans (le_max_left _ _)
          _ = 2 * max C_L1 1 := by ring
      have h2pi_le : (1 / (2 * Real.pi)) * 2 ≤ 1 := by
        rw [show (1 / (2 * Real.pi)) * 2 = 1 / Real.pi by ring, div_le_one Real.pi_pos]
        linarith [Real.two_le_pi]
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi)),
        abs_of_nonneg (div_nonneg h_vm_nonneg (Real.sqrt_nonneg n))]
      calc (1 / (2 * Real.pi)) * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) * |(_).re|
          ≤ (1 / (2 * Real.pi)) * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) * (2 * max C_L1 1) := by gcongr
        _ = ((1 / (2 * Real.pi)) * 2) * max C_L1 1 * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) := by ring
        _ ≤ 1 * max C_L1 1 * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) := by gcongr
        _ = max C_L1 1 * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) := one_mul _
    set S_pk := ((Finset.Icc 2 N).filter Nat.Prime) ×ˢ (Finset.Icc 3 N)
    have h_sub_img : S_rest.filter IsPrimePow ⊆ S_pk.image (fun pk : ℕ × ℕ => pk.1 ^ pk.2) := by
      intro n hn
      simp only [Finset.mem_filter, S_rest, Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_image] at hn
      rcases hn.2 with ⟨p, k, hp_nat, hk_pos, rfl⟩
      have hp : Nat.Prime p := Nat.prime_iff.mpr hp_nat
      have hk_ne1 : k ≠ 1 := by
        rintro rfl
        apply hn.1.1.2
        exact ⟨⟨hn.1.1.1.1, hn.1.1.1.2⟩, by simpa using hp⟩
      have hk_ne2 : k ≠ 2 := by
        rintro rfl
        apply hn.1.2
        refine ⟨p, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨hp.two_le, ?_⟩, hp⟩
        refine Nat.le_floor ?_
        rw [Real.le_sqrt' (Nat.cast_nonneg p)]
        have hp2_le : (p ^ 2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn.1.1.1.2
        exact hp2_le.trans (Nat.floor_le (by linarith))
      have hk3 : 3 ≤ k := by omega
      have hp_le_N : p ≤ N := by
        have : p ^ 1 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk_pos
        simp only [pow_one] at this
        exact this.trans hn.1.1.1.2
      have hk_le_N : k ≤ N := by
        have h1 : k ≤ 2 ^ k := Nat.lt_pow_self (by norm_num : 1 < 2) |>.le
        have h2 : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
        exact h1.trans (h2.trans hn.1.1.1.2)
      refine Finset.mem_image.mpr ⟨(p, k), ?_, rfl⟩
      simp only [S_pk, Finset.mem_product, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨⟨hp.two_le, hp_le_N⟩, hp⟩, ⟨hk3, hk_le_N⟩⟩
    have h_sum_img_le : ∀ {α β : Type*} [DecidableEq β] (s : Finset α) (φ : α → β) (g : β → ℝ),
        (∀ x ∈ s, 0 ≤ g (φ x)) → ∑ y ∈ s.image φ, g y ≤ ∑ x ∈ s, g (φ x) := by
      intro α β _ s φ g hg
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.image_insert, Finset.sum_insert ha]
        by_cases hmem : φ a ∈ s.image φ
        · rw [Finset.insert_eq_of_mem hmem]
          have h0 : 0 ≤ g (φ a) := hg a (Finset.mem_insert_self a s)
          linarith [ih (fun x hx => hg x (Finset.mem_insert_of_mem hx))]
        · rw [Finset.sum_insert hmem]
          linarith [ih (fun x hx => hg x (Finset.mem_insert_of_mem hx))]
    calc |∑ n ∈ S_rest.filter IsPrimePow, f n|
        ≤ ∑ n ∈ S_rest.filter IsPrimePow, |f n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ S_rest.filter IsPrimePow,
            max C_L1 1 * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) := by
          refine Finset.sum_le_sum fun n hn => h_f_bd n ?_
          simp only [Finset.mem_filter, S_rest, Finset.mem_sdiff, Finset.mem_Icc] at hn
          exact hn.1.1.1.1
      _ ≤ ∑ n ∈ S_pk.image (fun pk : ℕ × ℕ => pk.1 ^ pk.2),
            max C_L1 1 * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg h_sub_img (fun n _ _ => ?_)
          have : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
          positivity
      _ ≤ ∑ pk ∈ S_pk,
            max C_L1 1 * ((ArithmeticFunction.vonMangoldt (pk.1 ^ pk.2) : ℝ) / Real.sqrt (pk.1 ^ pk.2)) := by
          refine h_sum_img_le S_pk (fun pk : ℕ × ℕ => pk.1 ^ pk.2) _ (fun pk _ => ?_)
          have : 0 ≤ (ArithmeticFunction.vonMangoldt (pk.1 ^ pk.2) : ℝ) :=
            ArithmeticFunction.vonMangoldt_nonneg
          positivity
      _ = max C_L1 1 * ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
            Real.log p * ∑ k ∈ Finset.Icc 3 N, (1 / Real.sqrt p) ^ k := by
          rw [← Finset.mul_sum]
          congr 1
          dsimp only [S_pk]
          rw [Finset.sum_product]
          refine Finset.sum_congr rfl fun p hp => ?_
          simp only [Finset.mem_filter, Finset.mem_Icc] at hp
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k hk => ?_
          simp only [Finset.mem_Icc] at hk
          dsimp only
          rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega : k ≠ 0),
            ArithmeticFunction.vonMangoldt_apply_prime hp.2, Nat.cast_pow,
            Real.sqrt_pow (Nat.cast_nonneg p), one_div, inv_pow, div_eq_mul_inv]
      _ ≤ max C_L1 1 * ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, 16 * (p : ℝ) ^ (-5 / 4 : ℝ) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p hp => ?_) (by positivity)
          simp only [Finset.mem_filter, Finset.mem_Icc] at hp
          have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
          set r : ℝ := 1 / Real.sqrt p
          have hr_nonneg : 0 ≤ r := by positivity
          have hr_le : r ≤ 3 / 4 := by
            dsimp only [r]
            rw [div_le_iff₀ (Real.sqrt_pos.mpr hp_pos)]
            have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.2.two_le
            have hsq : (4 : ℝ) ≤ 3 * Real.sqrt p := by
              rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4),
                ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 3 * Real.sqrt p),
                mul_pow, Real.sq_sqrt hp_pos.le]
              exact Real.sqrt_le_sqrt (by norm_num; linarith)
            linarith
          have hr_lt1 : r < 1 := by linarith
          have h_k_sub : Finset.Icc 3 N ⊆ (Finset.range (N + 1)).image (· + 3) := by
            intro k hk
            simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range] at hk ⊢
            exact ⟨k - 3, by omega, by omega⟩
          have h_sum_k : ∑ k ∈ Finset.Icc 3 N, r ^ k ≤ 4 * (p : ℝ) ^ (-3 / 2 : ℝ) := by
            calc ∑ k ∈ Finset.Icc 3 N, r ^ k
                ≤ ∑ k ∈ (Finset.range (N + 1)).image (· + 3), r ^ k :=
                  Finset.sum_le_sum_of_subset_of_nonneg h_k_sub (fun k _ _ => pow_nonneg hr_nonneg k)
              _ = ∑ k ∈ Finset.range (N + 1), r ^ (k + 3) := by
                  rw [Finset.sum_image (fun a _ b _ h => by omega)]
              _ = r ^ 3 * ∑ k ∈ Finset.range (N + 1), r ^ k := by
                  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
              _ = r ^ 3 * ((1 - r ^ (N + 1)) / (1 - r)) := by
                  rw [geom_sum_eq hr_lt1.ne]
                  congr 1
                  rw [← neg_div_neg_eq, neg_sub, neg_sub]
              _ ≤ r ^ 3 * (1 / (1 - r)) := by
                  gcongr
                  linarith [pow_nonneg hr_nonneg (N + 1)]
              _ ≤ r ^ 3 * 4 := by
                  gcongr
                  rw [div_le_iff₀ (by linarith)]
                  linarith
              _ = 4 * (p : ℝ) ^ (-3 / 2 : ℝ) := by
                  dsimp only [r]
                  rw [one_div, inv_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
                    ← Real.rpow_mul hp_pos.le, ← Real.rpow_neg hp_pos.le]
                  norm_num; ring
          have h_log_bd : Real.log p ≤ 4 * (p : ℝ) ^ (1 / 4 : ℝ) := by
            have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hp_pos (1 / 4 : ℝ))
            rw [Real.log_rpow hp_pos] at h1
            linarith
          calc Real.log p * ∑ k ∈ Finset.Icc 3 N, r ^ k
              ≤ (4 * (p : ℝ) ^ (1 / 4 : ℝ)) * (4 * (p : ℝ) ^ (-3 / 2 : ℝ)) :=
                mul_le_mul h_log_bd h_sum_k (Finset.sum_nonneg fun k _ => pow_nonneg hr_nonneg k) (by positivity)
            _ = 16 * ((p : ℝ) ^ (1 / 4 : ℝ) * (p : ℝ) ^ (-3 / 2 : ℝ)) := by ring
            _ = 16 * (p : ℝ) ^ (-5 / 4 : ℝ) := by
                rw [← Real.rpow_add hp_pos]; norm_num
      _ ≤ max C_L1 1 * (16 * S_54) := by
          rw [← Finset.mul_sum]
          gcongr
          exact hsumm_54.sum_le_tsum _ (fun n _ => by positivity)
      _ ≤ C_tail := by
          have h1 : max C_L1 1 * (16 * S_54) ≤ 100 * max C_L1 1 * (S_54 + 1) := by nlinarith [le_max_right C_L1 1]
          exact h1.trans (le_max_right _ _)

lemma prime_tuple_fiber_card (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (k n : ℕ) :
    ((Fintype.piFinset (fun _ : Fin k => S)).filter (fun f => (∏ i, f i) = n)).card ≤ k.factorial := by
  induction k generalizing n with
  | zero =>
    have hsub : Subsingleton (Fin 0 → ℕ) := inferInstance
    exact (Finset.card_le_one_of_subsingleton _).trans (by simp)
  | succ k ih =>
    set F := (Fintype.piFinset (fun _ : Fin (k + 1) => S)).filter (fun f => (∏ i, f i) = n)
    by_cases h_emp : F = ∅
    · rw [h_emp, Finset.card_empty]; exact Nat.zero_le _
    · obtain ⟨f₀, hf₀⟩ := Finset.nonempty_iff_ne_empty.mpr h_emp
      simp only [F, Finset.mem_filter, Fintype.mem_piFinset] at hf₀
      have hn_pos : 0 < n := by
        rw [← hf₀.2]
        exact Finset.prod_pos (fun i _ => (hS _ (hf₀.1 i)).pos)
      have hpf_sub : n.primeFactors ⊆ Finset.image f₀ Finset.univ := by
        intro p hp
        have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
        have hp_dvd_n : p ∣ n := Nat.dvd_of_mem_primeFactors hp
        have hp_dvd : p ∣ ∏ i : Fin (k + 1), f₀ i := by rw [hf₀.2]; exact hp_dvd_n
        obtain ⟨i, _, hi⟩ := hp_prime.dvd_finset_prod_iff.mp hp_dvd
        have hpeq : p = f₀ i := (Nat.prime_dvd_prime_iff_eq hp_prime (hS _ (hf₀.1 i))).mp hi
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hpeq.symm⟩
      have hpf_card : n.primeFactors.card ≤ k + 1 :=
        (Finset.card_le_card hpf_sub).trans (Finset.card_image_le.trans (by simp))
      have hF_sub : F ⊆ n.primeFactors.biUnion (fun p => F.filter (fun f => f 0 = p)) := by
        intro f hf
        simp only [F, Finset.mem_filter, Fintype.mem_piFinset] at hf
        refine Finset.mem_biUnion.mpr ⟨f 0, ?_,
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr hf.1, hf.2⟩, rfl⟩⟩
        rw [Nat.mem_primeFactors]
        refine ⟨Nat.prime_iff.mp (hS _ (hf.1 0)), ?_, hn_pos.ne'⟩
        rw [← hf.2]
        exact Finset.dvd_prod_of_mem f (Finset.mem_univ 0)
      have h_fiber : ∀ p ∈ n.primeFactors, (F.filter (fun f => f 0 = p)).card ≤ k.factorial := by
        intro p hp
        set G := (Fintype.piFinset (fun _ : Fin k => S)).filter (fun g => (∏ i, g i) = n / p)
        have h_card_le : (F.filter (fun f => f 0 = p)).card ≤ G.card := by
          refine Finset.card_le_card_of_injOn (fun f i => f i.succ) ?_ ?_
          · intro f hf
            rw [Finset.mem_coe, Finset.mem_filter] at hf
            rw [Finset.mem_coe]
            dsimp only [G]
            rw [Finset.mem_filter, Fintype.mem_piFinset]
            have hf1 : ∀ i, f i ∈ S := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf.1).1
            have hf2 : (∏ i, f i) = n := (Finset.mem_filter.mp hf.1).2
            refine ⟨fun i => hf1 i.succ, ?_⟩
            have hprod : p * ∏ i : Fin k, f i.succ = n := by
              rw [← hf2, ← Fin.prod_univ_succ, hf.2]
            have hp_pos : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
            exact (Nat.eq_div_of_mul_eq_right hp_pos.ne' hprod).symm
          · intro f₁ hf₁ f₂ hf₂ heq
            rw [Finset.mem_coe, Finset.mem_filter] at hf₁ hf₂
            funext i
            refine Fin.cases ?_ (fun j => congr_fun heq j) i
            exact hf₁.2.trans hf₂.2.symm
        exact h_card_le.trans (ih (n / p))
      calc F.card ≤ (n.primeFactors.biUnion (fun p => F.filter (fun f => f 0 = p))).card :=
            Finset.card_le_card hF_sub
        _ ≤ ∑ p ∈ n.primeFactors, (F.filter (fun f => f 0 = p)).card := Finset.card_biUnion_le
        _ ≤ ∑ _p ∈ n.primeFactors, k.factorial := Finset.sum_le_sum h_fiber
        _ = n.primeFactors.card * k.factorial := by simp
        _ ≤ (k + 1) * k.factorial := Nat.mul_le_mul_right _ hpf_card
        _ = (k + 1).factorial := (Nat.factorial_succ k).symm

lemma factorial_le_pow (k : ℕ) : k.factorial ≤ k ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ, pow_succ']
    refine Nat.mul_le_mul_left (k + 1) (ih.trans (Nat.pow_le_pow_left (by omega) k))

lemma prime_l2_sum_bound (θ C_L1 Δ₀ : ℝ) (hθ : |θ| ≤ Real.pi / 2) (hΔ₀ : Δ₀ ≥ 1) :
    ∃ C_l2 > 0, ∀ (Δ : ℝ) (M : ℝ → ℝ), Δ ≥ Δ₀ →
      Integrable (fun x : ℝ => M x - kernelK θ x) →
      (∫ x : ℝ, |M x - kernelK θ x|) ≤ C_L1 / Δ →
      ∑ p ∈ (Finset.Icc 2 (Nat.floor (Real.exp (2 * Real.pi * Δ)))).filter Nat.Prime,
        ((Real.log p / Real.sqrt p) *
          max ‖fourierHat (fun x : ℝ => (M x : ℂ)) (-(Real.log p / (2 * Real.pi)))‖
              ‖fourierHat (fun x : ℝ => (M x : ℂ)) (Real.log p / (2 * Real.pi))‖) ^ 2 ≤
        C_l2 * Real.log (Real.log (Real.exp (2 * Real.pi * Δ))) := by
  obtain ⟨C_dec, hC_dec, h_dec⟩ := majorant_fourier_decay_any θ C_L1 Δ₀ hθ hΔ₀
  refine ⟨400 * C_dec ^ 2, by positivity, fun Δ M hΔ hInt hL1 => ?_⟩
  set X := Real.exp (2 * Real.pi * Δ)
  set P := Nat.floor X
  have hΔ_ge1 : 1 ≤ Δ := hΔ₀.trans hΔ
  have hlogX_eq : Real.log X = 2 * Real.pi * Δ := Real.log_exp _
  have hloglogX_ge : 1 ≤ Real.log (Real.log X) := by
    rw [hlogX_eq]
    have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by nlinarith [Real.two_le_pi])
  have hX_ge_16 : (16 : ℝ) ≤ X := by
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h4 : (4 : ℝ) ≤ 2 * Real.pi * Δ := by nlinarith [Real.two_le_pi]
    calc (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := by gcongr
      _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ X := Real.exp_le_exp.mpr h4
  have hP_ge_3 : P ≥ 3 := Nat.le_floor (by norm_num; linarith)
  have hP_le_X : (P : ℝ) ≤ X := Nat.floor_le (Real.exp_pos _).le
  have h_term : ∀ p ∈ (Finset.Icc 2 P).filter Nat.Prime,
      ((Real.log p / Real.sqrt p) *
        max ‖fourierHat (fun x : ℝ => (M x : ℂ)) (-(Real.log p / (2 * Real.pi)))‖
            ‖fourierHat (fun x : ℝ => (M x : ℂ)) (Real.log p / (2 * Real.pi))‖) ^ 2 ≤
      2 * C_dec ^ 2 * ((1 : ℝ) / p + (Real.log p) ^ 2 / (Δ ^ 2 * p)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
    have hlogp_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.2.one_lt)
    have hξ_pos : 0 < Real.log p / (2 * Real.pi) := by positivity
    have h_abs_eq : 1 / (2 * Real.pi * |Real.log p / (2 * Real.pi)|) = 1 / Real.log p := by
      rw [abs_of_pos hξ_pos]
      field_simp [Real.pi_ne_zero]
    have h_nabs_eq : 1 / (2 * Real.pi * |-(Real.log p / (2 * Real.pi))|) = 1 / Real.log p := by
      rw [abs_neg]; exact h_abs_eq
    have hs_bd : max ‖fourierHat (fun x : ℝ => (M x : ℂ)) (-(Real.log p / (2 * Real.pi)))‖
        ‖fourierHat (fun x : ℝ => (M x : ℂ)) (Real.log p / (2 * Real.pi))‖ ≤
        C_dec * (1 / Real.log p + 1 / Δ) := by
      refine max_le ?_ ?_
      · have hd := h_dec Δ M hΔ hInt hL1 (-(Real.log p / (2 * Real.pi))) (neg_ne_zero.mpr hξ_pos.ne')
        rwa [h_nabs_eq] at hd
      · have hd := h_dec Δ M hΔ hInt hL1 (Real.log p / (2 * Real.pi)) hξ_pos.ne'
        rwa [h_abs_eq] at hd
    have h_prod_bd : (Real.log p / Real.sqrt p) *
        max ‖fourierHat (fun x : ℝ => (M x : ℂ)) (-(Real.log p / (2 * Real.pi)))‖
            ‖fourierHat (fun x : ℝ => (M x : ℂ)) (Real.log p / (2 * Real.pi))‖ ≤
        C_dec * (1 / Real.sqrt p + Real.log p / (Δ * Real.sqrt p)) := by
      calc (Real.log p / Real.sqrt p) * max _ _
          ≤ (Real.log p / Real.sqrt p) * (C_dec * (1 / Real.log p + 1 / Δ)) := by gcongr
        _ = C_dec * (1 / Real.sqrt p + Real.log p / (Δ * Real.sqrt p)) := by
            field_simp [hlogp_pos.ne', (Real.sqrt_pos.mpr hp_pos).ne', (by linarith : Δ ≠ 0)]
            ring
    have h_sq_le : ∀ a b : ℝ, (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := fun a b => by
      nlinarith [sq_nonneg (a - b)]
    calc ((Real.log p / Real.sqrt p) * max _ _) ^ 2
        ≤ (C_dec * (1 / Real.sqrt p + Real.log p / (Δ * Real.sqrt p))) ^ 2 := by
          gcongr
      _ = C_dec ^ 2 * (1 / Real.sqrt p + Real.log p / (Δ * Real.sqrt p)) ^ 2 := by ring
      _ ≤ C_dec ^ 2 * (2 * ((1 / Real.sqrt p) ^ 2 + (Real.log p / (Δ * Real.sqrt p)) ^ 2)) := by
          gcongr; exact h_sq_le _ _
      _ = 2 * C_dec ^ 2 * ((1 : ℝ) / p + (Real.log p) ^ 2 / (Δ ^ 2 * p)) := by
          rw [div_pow, one_pow, div_pow, mul_pow, Real.sq_sqrt hp_pos.le]
          ring
  have hm2 : ∑ p ∈ (Finset.Icc 2 P).filter Nat.Prime, (1 : ℝ) / p ≤ 30 * Real.log (Real.log X) := by
    have h1 := mertens_second P hP_ge_3
    have hloglog : Real.log (Real.log P) ≤ Real.log (Real.log X) :=
      Real.log_le_log (Real.log_pos (by exact_mod_cast (by omega : 1 < P)))
        (Real.log_le_log (by exact_mod_cast (by omega : 0 < P)) hP_le_X)
    nlinarith
  have hm1 : ∑ p ∈ (Finset.Icc 2 P).filter Nat.Prime, (Real.log p) ^ 2 / (Δ ^ 2 * p) ≤
      170 * Real.log (Real.log X) := by
    have hlogP_le : Real.log P ≤ 2 * Real.pi * Δ := by
      rw [← hlogX_eq]
      exact Real.log_le_log (by exact_mod_cast (by omega : 0 < P)) hP_le_X
    have hterm1 : ∀ p ∈ (Finset.Icc 2 P).filter Nat.Prime,
        (Real.log p) ^ 2 / (Δ ^ 2 * p) ≤ (2 * Real.pi / Δ) * (Real.log p / p) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
      have hlogp_le : Real.log p ≤ 2 * Real.pi * Δ :=
        (Real.log_le_log hp_pos (by exact_mod_cast hp.1.2)).trans hlogP_le
      have hlogp_nonneg : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)
      have heq1 : (Real.log p) ^ 2 / (Δ ^ 2 * p) = (Real.log p / Δ ^ 2) * (Real.log p / p) := by ring
      have heq2 : Real.log p / Δ ^ 2 ≤ 2 * Real.pi / Δ := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [Real.pi_pos]
      rw [heq1]
      exact mul_le_mul_of_nonneg_right heq2 (div_nonneg hlogp_nonneg hp_pos.le)
    have hmf := mertens_first P (by omega)
    have hlog4_le : Real.log 4 ≤ 2 := by
      have hlog2_le : Real.log 2 ≤ 1 := by
        have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        rw [← Real.log_exp 1]; exact Real.log_le_log (by norm_num) he
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; linarith
    calc ∑ p ∈ (Finset.Icc 2 P).filter Nat.Prime, (Real.log p) ^ 2 / (Δ ^ 2 * p)
        ≤ ∑ p ∈ (Finset.Icc 2 P).filter Nat.Prime, (2 * Real.pi / Δ) * (Real.log p / p) :=
          Finset.sum_le_sum hterm1
      _ = (2 * Real.pi / Δ) * ∑ p ∈ (Finset.Icc 2 P).filter Nat.Prime, Real.log p / p := by
          rw [← Finset.mul_sum]
      _ ≤ (2 * Real.pi / Δ) * (Real.log 4 * (Real.log P + 1)) := by gcongr
      _ ≤ (2 * Real.pi / Δ) * (2 * (2 * Real.pi * Δ + 1)) := by gcongr
      _ = 8 * Real.pi ^ 2 + 4 * Real.pi / Δ := by field_simp [(by linarith : Δ ≠ 0)]; ring
      _ ≤ 8 * 4 ^ 2 + 4 * 4 / 1 := by
          have hpi := Real.pi_lt_four
          gcongr
      _ = 144 := by norm_num
      _ ≤ 170 * Real.log (Real.log X) := by nlinarith [hloglogX_ge]
  calc ∑ p ∈ (Finset.Icc 2 P).filter Nat.Prime,
        ((Real.log p / Real.sqrt p) * max _ _) ^ 2
      ≤ ∑ p ∈ (Finset.Icc 2 P).filter Nat.Prime,
          2 * C_dec ^ 2 * ((1 : ℝ) / p + (Real.log p) ^ 2 / (Δ ^ 2 * p)) :=
        Finset.sum_le_sum h_term
    _ = 2 * C_dec ^ 2 * (∑ p ∈ (Finset.Icc 2 P).filter Nat.Prime, (1 : ℝ) / p +
          ∑ p ∈ (Finset.Icc 2 P).filter Nat.Prime, (Real.log p) ^ 2 / (Δ ^ 2 * p)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 2 * C_dec ^ 2 * (30 * Real.log (Real.log X) + 170 * Real.log (Real.log X)) := by
        gcongr
    _ = 400 * C_dec ^ 2 * Real.log (Real.log X) := by ring

/-- **Lemma 4.2(i)** (`2k`-th moment bound in the `t`-aspect). -/
theorem prime_moment_t_aspect (θ C_L1 Δ₀ : ℝ) (hθ : |θ| ≤ Real.pi / 2) (hΔ₀ : Δ₀ ≥ 1) :
    ∃ B > 0, ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (Δ T : ℝ) (k : ℕ) (M : ℝ → ℝ),
      q ≥ 1 → Δ ≥ Δ₀ → T ≥ 10 →
      (Real.exp (2 * Real.pi * Δ)) ^ k ≤ T →
      Integrable (fun x : ℝ => M x - kernelK θ x) →
      (∫ x : ℝ, |M x - kernelK θ x|) ≤ C_L1 / Δ →
      (∫ x : ℝ, |M x|) ≤ C_L1 →
      (1 / T) * ∫ t in Set.Icc T (2 * T),
        |primeSum1 q χ (fourierHat (fun x : ℝ => (M x : ℂ))) (Real.exp (2 * Real.pi * Δ)) t| ^ (2 * k) ≤
        (B * k * Real.log (Real.log (Real.exp (2 * Real.pi * Δ)))) ^ k := by
  obtain ⟨C₂, hC₂, hmvt⟩ := montgomery_vaughan_mvt
  obtain ⟨C_l2, hC_l2, hl2⟩ := prime_l2_sum_bound θ C_L1 Δ₀ hθ hΔ₀
  refine ⟨max (8 * max C₂ 1 * C_l2) 1, by positivity,
    fun q χ Δ T k M hq hΔ hT hXk hInt hL1 hL1_M => ?_⟩
  set B := max (8 * max C₂ 1 * C_l2) 1
  set X := Real.exp (2 * Real.pi * Δ)
  set P := Nat.floor X
  set h_hat := fourierHat (fun x : ℝ => (M x : ℂ))
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · simp only [mul_zero, pow_zero, Nat.cast_zero]
    rw [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Icc_of_le (by linarith)]
    have : 2 * T - T = T := by ring
    rw [this, one_div_mul_cancel (by linarith)]
  · let primes := (Finset.Icc 2 P).filter Nat.Prime
    let b₁ : ℕ → ℂ := fun p =>
      ((Real.log p / Real.sqrt p : ℝ) : ℂ) * χ p * h_hat (-(Real.log p / (2 * Real.pi)))
    let b₂ : ℕ → ℂ := fun p =>
      ((Real.log p / Real.sqrt p : ℝ) : ℂ) * χ p * star (h_hat (Real.log p / (2 * Real.pi)))
    let D₁ : ℝ → ℂ := fun t => ∑ p ∈ primes, b₁ p * Complex.exp (-Complex.I * t * Real.log p)
    let D₂ : ℝ → ℂ := fun t => ∑ p ∈ primes, b₂ p * Complex.exp (-Complex.I * t * Real.log p)
    have h_ptwise : ∀ t : ℝ,
        |primeSum1 q χ h_hat X t| ^ (2 * k) ≤ 4 ^ k * (‖D₁ t‖ ^ (2 * k) + ‖D₂ t‖ ^ (2 * k)) := by
      intro t
      have h_le : |primeSum1 q χ h_hat X t| ≤ ‖D₁ t‖ + ‖D₂ t‖ := by
        unfold primeSum1
        have h_sum_eq : (∑ p ∈ primes, (Real.log p / Real.sqrt p) *
            (χ p * h_hat (-(Real.log p / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log p) +
             star (χ p) * h_hat (Real.log p / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log p)).re) =
            (D₁ t).re + (star (D₂ t)).re := by
          simp only [D₁, D₂, b₁, b₂, Complex.re_sum, star_sum, Complex.star_def, star_mul,
            Complex.conj_ofReal]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun p _ => ?_
          have hce : (starRingEnd ℂ) (Complex.exp (-Complex.I * ↑t * ↑(Real.log p))) =
              Complex.exp (Complex.I * ↑t * ↑(Real.log p)) := by
            rw [← Complex.exp_conj]
            congr 1
            simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
            ring
          rw [hce]
          have hstar2 : (starRingEnd ℂ) ((starRingEnd ℂ) (h_hat (Real.log ↑p / (2 * Real.pi)))) =
              h_hat (Real.log ↑p / (2 * Real.pi)) := star_star _
          rw [hstar2, ← Complex.add_re, ← Complex.re_ofReal_mul]
          congr 1
          ring
        rw [h_sum_eq]
        have h2pi_le : 1 / (2 * Real.pi) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith [Real.two_le_pi]
        rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
        calc (1 / (2 * Real.pi)) * |(D₁ t).re + (star (D₂ t)).re|
            ≤ 1 * (|(D₁ t).re| + |(star (D₂ t)).re|) := by
              gcongr; exact abs_add_le _ _
          _ ≤ ‖D₁ t‖ + ‖star (D₂ t)‖ := by
              rw [one_mul]
              exact add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _)
          _ = ‖D₁ t‖ + ‖D₂ t‖ := by rw [norm_star]
      have h_max : (‖D₁ t‖ + ‖D₂ t‖) ^ (2 * k) ≤ 4 ^ k * (‖D₁ t‖ ^ (2 * k) + ‖D₂ t‖ ^ (2 * k)) := by
        set m := max ‖D₁ t‖ ‖D₂ t‖
        calc (‖D₁ t‖ + ‖D₂ t‖) ^ (2 * k)
            ≤ (2 * m) ^ (2 * k) := by
              gcongr; linarith [le_max_left ‖D₁ t‖ ‖D₂ t‖, le_max_right ‖D₁ t‖ ‖D₂ t‖]
          _ = 4 ^ k * m ^ (2 * k) := by rw [mul_pow, pow_mul]; norm_num
          _ ≤ 4 ^ k * (‖D₁ t‖ ^ (2 * k) + ‖D₂ t‖ ^ (2 * k)) := by
              gcongr
              rcases le_total ‖D₁ t‖ ‖D₂ t‖ with h | h
              · simp only [m, max_eq_right h]; linarith [pow_nonneg (norm_nonneg (D₁ t)) (2 * k)]
              · simp only [m, max_eq_left h]; linarith [pow_nonneg (norm_nonneg (D₂ t)) (2 * k)]
      exact (pow_le_pow_left₀ (abs_nonneg _) h_le (2 * k)).trans h_max
    have h_poly_bound : ∀ (b : ℕ → ℂ),
        (∀ p ∈ primes, ‖b p‖ ≤ (Real.log p / Real.sqrt p) *
          max ‖h_hat (-(Real.log p / (2 * Real.pi)))‖ ‖h_hat (Real.log p / (2 * Real.pi))‖) →
        (1 / T) * ∫ t in Set.Icc T (2 * T),
          ‖∑ p ∈ primes, b p * Complex.exp (-Complex.I * t * Real.log p)‖ ^ (2 * k) ≤
        (max C₂ 1 * C_l2 * k * Real.log (Real.log X)) ^ k := by
      intro b hb
      set D : ℝ → ℂ := fun t => ∑ p ∈ primes, b p * Complex.exp (-Complex.I * t * Real.log p)
      let fiber : ℕ → Finset (Fin k → ℕ) := fun n =>
        (Fintype.piFinset (fun _ : Fin k => primes)).filter (fun f => (∏ i, f i) = n)
      let a : ℕ → ℂ := fun n => ∑ f ∈ fiber n, ∏ i, b (f i)
      have h_pow_eq : ∀ t : ℝ, (D t) ^ k = ∑ n ∈ Finset.Icc 1 (P ^ k), a n * Complex.exp (-Complex.I * t * Real.log n) := by
        intro t
        dsimp only [D]
        rw [Finset.sum_pow']
        have h_maps : ∀ f ∈ Fintype.piFinset (fun _ : Fin k => primes),
            (∏ i : Fin k, f i) ∈ Finset.Icc 1 (P ^ k) := by
          intro f hf
          rw [Fintype.mem_piFinset] at hf
          rw [Finset.mem_Icc]
          refine ⟨Nat.succ_le_of_lt (Finset.prod_pos (fun i _ => ?_)), ?_⟩
          · have hp := hf i
            simp only [primes, Finset.mem_filter] at hp
            exact hp.2.pos
          · calc ∏ i : Fin k, f i ≤ ∏ _i : Fin k, P := by
                  refine Finset.prod_le_prod' fun i _ => ?_
                  have hp := hf i
                  simp only [primes, Finset.mem_filter, Finset.mem_Icc] at hp
                  exact hp.1.2
              _ = P ^ k := by simp
        rw [← Finset.sum_fiberwise_of_maps_to h_maps]
        refine Finset.sum_congr rfl fun n _ => ?_
        dsimp only [a, fiber]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun f hf => ?_
        simp only [Finset.mem_filter, Fintype.mem_piFinset] at hf
        rw [Finset.prod_mul_distrib]
        congr 1
        have hpos : ∀ i : Fin k, (0 : ℝ) < f i := fun i => by
          have hp := hf.1 i
          simp only [primes, Finset.mem_filter] at hp
          exact_mod_cast hp.2.pos
        have hexp : ∏ i : Fin k, Complex.exp (-Complex.I * t * Real.log (f i)) =
            Complex.exp (∑ i : Fin k, (-Complex.I * t * Real.log (f i))) := by
          rw [← Complex.exp_sum]
        rw [hexp]
        congr 1
        rw [← hf.2, Nat.cast_prod, Real.log_prod (fun i _ => (hpos i).ne')]
        push_cast
        rw [Finset.mul_sum]
      have h_norm_eq : ∀ t : ℝ, ‖∑ p ∈ primes, b p * Complex.exp (-Complex.I * t * Real.log p)‖ ^ (2 * k) =
          ‖∑ n ∈ Finset.Icc 1 (P ^ k), a n * Complex.exp (-Complex.I * t * Real.log n)‖ ^ 2 := by
        intro t
        rw [mul_comm 2 k, pow_mul, ← norm_pow]
        change ‖(D t) ^ k‖ ^ 2 = _
        rw [h_pow_eq t]
      simp_rw [h_norm_eq]
      have hPk_le_T : ((P ^ k : ℕ) : ℝ) ≤ T := by
        have hP_le : (P : ℝ) ≤ X := Nat.floor_le (Real.exp_pos _).le
        calc ((P ^ k : ℕ) : ℝ) = (P : ℝ) ^ k := by push_cast; rfl
          _ ≤ X ^ k := pow_le_pow_left₀ (Nat.cast_nonneg P) hP_le k
          _ ≤ T := hXk
      have hmvt_bd := hmvt (P ^ k) a T (by linarith) hPk_le_T
      have h_cs : ∀ n ∈ Finset.Icc 1 (P ^ k), ‖a n‖ ^ 2 ≤ (k.factorial : ℝ) * ∑ f ∈ fiber n, ∏ i, ‖b (f i)‖ ^ 2 := by
        intro n _
        dsimp only [a]
        have h1 : ‖∑ f ∈ fiber n, ∏ i, b (f i)‖ ^ 2 ≤ (∑ f ∈ fiber n, ‖∏ i, b (f i)‖) ^ 2 := by
          gcongr; exact norm_sum_le _ _
        have h2 : (∑ f ∈ fiber n, ‖∏ i, b (f i)‖) ^ 2 ≤ (fiber n).card * ∑ f ∈ fiber n, ‖∏ i, b (f i)‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
        have h_card : (fiber n).card ≤ k.factorial :=
          prime_tuple_fiber_card primes (fun p hp => (Finset.mem_filter.mp hp).2) k n
        have h3 : ((fiber n).card : ℝ) * ∑ f ∈ fiber n, ‖∏ i, b (f i)‖ ^ 2 ≤
            (k.factorial : ℝ) * ∑ f ∈ fiber n, ∏ i, ‖b (f i)‖ ^ 2 := by
          have h_eq : ∑ f ∈ fiber n, ‖∏ i, b (f i)‖ ^ 2 = ∑ f ∈ fiber n, ∏ i, ‖b (f i)‖ ^ 2 := by
            refine Finset.sum_congr rfl fun f _ => ?_
            rw [norm_prod, Finset.prod_pow]
          rw [h_eq]
          gcongr
        exact h1.trans (h2.trans h3)
      have h_sum_a : ∑ n ∈ Finset.Icc 1 (P ^ k), ‖a n‖ ^ 2 ≤
          (k.factorial : ℝ) * (∑ p ∈ primes, ‖b p‖ ^ 2) ^ k := by
        calc ∑ n ∈ Finset.Icc 1 (P ^ k), ‖a n‖ ^ 2
            ≤ ∑ n ∈ Finset.Icc 1 (P ^ k), (k.factorial : ℝ) * ∑ f ∈ fiber n, ∏ i, ‖b (f i)‖ ^ 2 :=
              Finset.sum_le_sum h_cs
          _ = (k.factorial : ℝ) * ∑ n ∈ Finset.Icc 1 (P ^ k), ∑ f ∈ fiber n, ∏ i, ‖b (f i)‖ ^ 2 := by
              rw [← Finset.mul_sum]
          _ = (k.factorial : ℝ) * ∑ f ∈ Fintype.piFinset (fun _ : Fin k => primes), ∏ i, ‖b (f i)‖ ^ 2 := by
              congr 1
              refine Finset.sum_fiberwise_of_maps_to (fun f hf => ?_) _
              rw [Fintype.mem_piFinset] at hf
              rw [Finset.mem_Icc]
              refine ⟨Nat.succ_le_of_lt (Finset.prod_pos (fun i _ => (Finset.mem_filter.mp (hf i)).2.pos)), ?_⟩
              calc ∏ i : Fin k, f i ≤ ∏ _i : Fin k, P :=
                    Finset.prod_le_prod' fun i _ => (Finset.mem_Icc.mp (Finset.mem_filter.mp (hf i)).1).2
                _ = P ^ k := by simp
          _ = (k.factorial : ℝ) * (∑ p ∈ primes, ‖b p‖ ^ 2) ^ k := by
              rw [Finset.sum_pow']
      have h_l2_b : ∑ p ∈ primes, ‖b p‖ ^ 2 ≤ C_l2 * Real.log (Real.log X) := by
        calc ∑ p ∈ primes, ‖b p‖ ^ 2
            ≤ ∑ p ∈ primes, ((Real.log p / Real.sqrt p) *
                max ‖h_hat (-(Real.log p / (2 * Real.pi)))‖ ‖h_hat (Real.log p / (2 * Real.pi))‖) ^ 2 := by
              refine Finset.sum_le_sum fun p hp => ?_
              exact pow_le_pow_left₀ (norm_nonneg _) (hb p hp) 2
          _ ≤ C_l2 * Real.log (Real.log X) := hl2 Δ M hΔ hInt hL1
      have h_fac_le : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast factorial_le_pow k
      calc (1 / T) * ∫ t in Set.Icc T (2 * T),
            ‖∑ n ∈ Finset.Icc 1 (P ^ k), a n * Complex.exp (-Complex.I * t * Real.log n)‖ ^ 2
          ≤ (1 / T) * (C₂ * T * ∑ n ∈ Finset.Icc 1 (P ^ k), ‖a n‖ ^ 2) := by
            gcongr
        _ = C₂ * ∑ n ∈ Finset.Icc 1 (P ^ k), ‖a n‖ ^ 2 := by
            field_simp [(by linarith : T ≠ 0)]
        _ ≤ max C₂ 1 * ((k.factorial : ℝ) * (∑ p ∈ primes, ‖b p‖ ^ 2) ^ k) := by
            gcongr
            exact le_max_left _ _
        _ ≤ max C₂ 1 * ((k : ℝ) ^ k * (C_l2 * Real.log (Real.log X)) ^ k) := by
            gcongr
            exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        _ ≤ (max C₂ 1) ^ k * ((k : ℝ) ^ k * (C_l2 * Real.log (Real.log X)) ^ k) := by
            have hloglogX_nonneg : 0 ≤ Real.log (Real.log X) := by
              rw [show Real.log X = 2 * Real.pi * Δ from Real.log_exp _]
              apply Real.log_nonneg
              have : 1 ≤ Δ := hΔ₀.trans hΔ
              nlinarith [Real.two_le_pi]
            gcongr
            exact le_self_pow₀ (le_max_right C₂ 1) hk_pos.ne'
        _ = (max C₂ 1 * C_l2 * k * Real.log (Real.log X)) ^ k := by
            rw [← mul_pow, ← mul_pow]; ring_nf
    have hchi_le : ∀ p : ℕ, ‖χ p‖ ≤ 1 := fun p => by
      by_cases h0 : χ p = 0
      · simp [h0]
      · exact (dirichletChar_norm_eq_one χ h0).le
    have hb₁ : ∀ p ∈ primes, ‖b₁ p‖ ≤ (Real.log p / Real.sqrt p) *
        max ‖h_hat (-(Real.log p / (2 * Real.pi)))‖ ‖h_hat (Real.log p / (2 * Real.pi))‖ := by
      intro p hp
      dsimp only [b₁]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)) (Real.sqrt_nonneg p))]
      calc (Real.log p / Real.sqrt p) * ‖χ p‖ * ‖h_hat (-(Real.log p / (2 * Real.pi)))‖
          ≤ (Real.log p / Real.sqrt p) * 1 * max _ _ := by
            gcongr
            · exact hchi_le p
            · exact le_max_left _ _
        _ = (Real.log p / Real.sqrt p) * max _ _ := by ring
    have hb₂ : ∀ p ∈ primes, ‖b₂ p‖ ≤ (Real.log p / Real.sqrt p) *
        max ‖h_hat (-(Real.log p / (2 * Real.pi)))‖ ‖h_hat (Real.log p / (2 * Real.pi))‖ := by
      intro p hp
      dsimp only [b₂]
      rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)) (Real.sqrt_nonneg p))]
      calc (Real.log p / Real.sqrt p) * ‖χ p‖ * ‖h_hat (Real.log p / (2 * Real.pi))‖
          ≤ (Real.log p / Real.sqrt p) * 1 * max _ _ := by
            gcongr
            · exact hchi_le p
            · exact le_max_right _ _
        _ = (Real.log p / Real.sqrt p) * max _ _ := by ring
    have hD₁_int : IntegrableOn (fun t : ℝ => ‖D₁ t‖ ^ (2 * k)) (Set.Icc T (2 * T)) :=
      Continuous.continuousOn (by fun_prop) |>.integrableOn_Icc
    have hD₂_int : IntegrableOn (fun t : ℝ => ‖D₂ t‖ ^ (2 * k)) (Set.Icc T (2 * T)) :=
      Continuous.continuousOn (by fun_prop) |>.integrableOn_Icc
    have hRHS_int : IntegrableOn (fun t : ℝ => 4 ^ k * (‖D₁ t‖ ^ (2 * k) + ‖D₂ t‖ ^ (2 * k))) (Set.Icc T (2 * T)) :=
      Continuous.continuousOn (by fun_prop) |>.integrableOn_Icc
    have hP_int : IntegrableOn (fun t : ℝ => |primeSum1 q χ h_hat X t| ^ (2 * k)) (Set.Icc T (2 * T)) := by
      refine hRHS_int.mono' ?_ ?_
      · exact (Continuous.continuousOn (by unfold primeSum1; fun_prop)).aestronglyMeasurable measurableSet_Icc
      · filter_upwards with t
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
        exact h_ptwise t
    have hloglogX_ge : 0 ≤ Real.log (Real.log X) := by
      rw [show Real.log X = 2 * Real.pi * Δ from Real.log_exp _]
      apply Real.log_nonneg
      have : 1 ≤ Δ := hΔ₀.trans hΔ
      nlinarith [Real.two_le_pi]
    calc (1 / T) * ∫ t in Set.Icc T (2 * T), |primeSum1 q χ h_hat X t| ^ (2 * k)
        ≤ (1 / T) * ∫ t in Set.Icc T (2 * T), 4 ^ k * (‖D₁ t‖ ^ (2 * k) + ‖D₂ t‖ ^ (2 * k)) := by
          gcongr
          exact setIntegral_mono_on hP_int hRHS_int measurableSet_Icc.nullMeasurableSet (fun t _ => h_ptwise t)
      _ = 4 ^ k * ((1 / T) * (∫ t in Set.Icc T (2 * T), ‖D₁ t‖ ^ (2 * k)) +
            (1 / T) * (∫ t in Set.Icc T (2 * T), ‖D₂ t‖ ^ (2 * k))) := by
          have hint_add : ∫ t in Set.Icc T (2 * T), (‖D₁ t‖ ^ (2 * k) + ‖D₂ t‖ ^ (2 * k)) =
              (∫ t in Set.Icc T (2 * T), ‖D₁ t‖ ^ (2 * k)) +
              (∫ t in Set.Icc T (2 * T), ‖D₂ t‖ ^ (2 * k)) :=
            MeasureTheory.integral_add hD₁_int hD₂_int
          rw [MeasureTheory.integral_const_mul, hint_add]
          ring
      _ ≤ 4 ^ k * ((max C₂ 1 * C_l2 * k * Real.log (Real.log X)) ^ k +
            (max C₂ 1 * C_l2 * k * Real.log (Real.log X)) ^ k) := by
          have hb1_bd := h_poly_bound b₁ hb₁
          have hb2_bd := h_poly_bound b₂ hb₂
          change (1 / T) * (∫ t in Set.Icc T (2 * T), ‖D₁ t‖ ^ (2 * k)) ≤ _ at hb1_bd
          change (1 / T) * (∫ t in Set.Icc T (2 * T), ‖D₂ t‖ ^ (2 * k)) ≤ _ at hb2_bd
          exact mul_le_mul_of_nonneg_left (add_le_add hb1_bd hb2_bd) (by positivity)
      _ ≤ 4 ^ k * (2 ^ k * (max C₂ 1 * C_l2 * k * Real.log (Real.log X)) ^ k) := by
          have h2k : (2 : ℝ) ≤ 2 ^ k := by
            have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk_pos
            simpa using this
          have hnn : 0 ≤ (max C₂ 1 * C_l2 * k * Real.log (Real.log X)) ^ k := by positivity
          exact mul_le_mul_of_nonneg_left (by linarith [mul_le_mul_of_nonneg_right h2k hnn]) (by positivity)
      _ = (8 * max C₂ 1 * C_l2 * k * Real.log (Real.log X)) ^ k := by
          rw [← mul_pow, ← mul_pow]; ring_nf
      _ ≤ (B * k * Real.log (Real.log X)) ^ k := by
          gcongr
          exact le_max_left _ _

/-- **Lemma 4.2(ii)** (`2k`-th moment bound in the `q`-aspect). -/
theorem prime_moment_q_aspect (θ C_L1 Δ₀ : ℝ) (hθ : |θ| ≤ Real.pi / 2) (hΔ₀ : Δ₀ ≥ 1) :
    ∃ B > 0, ∀ (q : ℕ) (t₀ Δ : ℝ) (k : ℕ) (M : ℝ → ℝ),
      q ≥ 3 → totientStar q ≥ 1 → Δ ≥ Δ₀ →
      (Real.exp (2 * Real.pi * Δ)) ^ k < (q : ℝ) →
      Integrable (fun x : ℝ => M x - kernelK θ x) →
      (∫ x : ℝ, |M x - kernelK θ x|) ≤ C_L1 / Δ →
      (∫ x : ℝ, |M x|) ≤ C_L1 →
      letI := Classical.decPred (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)
      (1 / (totientStar q : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          |primeSum1 q χ (fourierHat (fun x : ℝ => (M x : ℂ))) (Real.exp (2 * Real.pi * Δ)) t₀| ^ (2 * k) ≤
        ((Nat.totient q : ℝ) / (totientStar q : ℝ)) *
          (B * k * Real.log (Real.log (Real.exp (2 * Real.pi * Δ)))) ^ k := by
  obtain ⟨C_l2, hC_l2, hl2⟩ := prime_l2_sum_bound θ C_L1 Δ₀ hθ hΔ₀
  refine ⟨max (8 * C_l2) 1, by positivity,
    fun q t₀ Δ k M hq hqstar hΔ hXk hInt hL1 hL1_M => ?_⟩
  classical
  set B := max (8 * C_l2) 1
  set X := Real.exp (2 * Real.pi * Δ)
  set P := Nat.floor X
  set h_hat := fourierHat (fun x : ℝ => (M x : ℂ))
  have hq_pos : 0 < q := by omega
  have hq_ne : q ≠ 0 := hq_pos.ne'
  haveI : NeZero q := ⟨hq_ne⟩
  have hqstar_pos : (0 : ℝ) < totientStar q := by exact_mod_cast hqstar
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · simp only [mul_zero, pow_zero, Nat.cast_zero, mul_one, Finset.sum_const, nsmul_eq_mul]
    have hcard_le : (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)).card ≤
        Nat.totient q := by
      calc (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)).card
          ≤ (Finset.univ : Finset (DirichletCharacter ℂ q)).card := Finset.card_filter_le _ _
        _ = Fintype.card (DirichletCharacter ℂ q) := Finset.card_univ
        _ = Nat.totient q := by rw [← Nat.card_eq_fintype_card]; exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    have h1 : (1 / (totientStar q : ℝ)) *
          ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)).card : ℝ) ≤
        (Nat.totient q : ℝ) / (totientStar q : ℝ) := by
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcard_le) hqstar_pos.le
    simpa [totientStar] using h1
  · let primes := (Finset.Icc 2 P).filter Nat.Prime
    let b₁ : ℕ → ℂ := fun p =>
      ((Real.log p / Real.sqrt p : ℝ) : ℂ) * h_hat (-(Real.log p / (2 * Real.pi))) *
        Complex.exp (-Complex.I * t₀ * Real.log p)
    let b₂ : ℕ → ℂ := fun p =>
      ((Real.log p / Real.sqrt p : ℝ) : ℂ) * star (h_hat (Real.log p / (2 * Real.pi))) *
        Complex.exp (-Complex.I * t₀ * Real.log p)
    let D₁ : DirichletCharacter ℂ q → ℂ := fun χ => ∑ p ∈ primes, b₁ p * χ p
    let D₂ : DirichletCharacter ℂ q → ℂ := fun χ => ∑ p ∈ primes, b₂ p * χ p
    have h_ptwise : ∀ χ : DirichletCharacter ℂ q,
        |primeSum1 q χ h_hat X t₀| ^ (2 * k) ≤ 4 ^ k * (‖D₁ χ‖ ^ (2 * k) + ‖D₂ χ‖ ^ (2 * k)) := by
      intro χ
      have h_le : |primeSum1 q χ h_hat X t₀| ≤ ‖D₁ χ‖ + ‖D₂ χ‖ := by
        unfold primeSum1
        have h_sum_eq : (∑ p ∈ primes, (Real.log p / Real.sqrt p) *
            (χ p * h_hat (-(Real.log p / (2 * Real.pi))) * Complex.exp (-Complex.I * t₀ * Real.log p) +
             star (χ p) * h_hat (Real.log p / (2 * Real.pi)) * Complex.exp (Complex.I * t₀ * Real.log p)).re) =
            (D₁ χ).re + (star (D₂ χ)).re := by
          simp only [D₁, D₂, b₁, b₂, Complex.re_sum, star_sum, Complex.star_def, star_mul,
            Complex.conj_ofReal]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun p _ => ?_
          have hce : (starRingEnd ℂ) (Complex.exp (-Complex.I * ↑t₀ * ↑(Real.log p))) =
              Complex.exp (Complex.I * ↑t₀ * ↑(Real.log p)) := by
            rw [← Complex.exp_conj]
            congr 1
            simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
            ring
          rw [hce]
          have hstar2 : (starRingEnd ℂ) ((starRingEnd ℂ) (h_hat (Real.log ↑p / (2 * Real.pi)))) =
              h_hat (Real.log ↑p / (2 * Real.pi)) := star_star _
          rw [hstar2, ← Complex.add_re]
          have h_rhs_eq : ((Real.log ↑p / Real.sqrt ↑p : ℝ) : ℂ) * h_hat (-(Real.log ↑p / (2 * Real.pi))) *
              Complex.exp (-Complex.I * ↑t₀ * ↑(Real.log p)) * χ ↑p +
              (starRingEnd ℂ) (χ ↑p) * (Complex.exp (Complex.I * ↑t₀ * ↑(Real.log p)) *
                (h_hat (Real.log ↑p / (2 * Real.pi)) * ((Real.log ↑p / Real.sqrt ↑p : ℝ) : ℂ))) =
              ((Real.log ↑p / Real.sqrt ↑p : ℝ) : ℂ) *
                (χ ↑p * h_hat (-(Real.log ↑p / (2 * Real.pi))) * Complex.exp (-Complex.I * ↑t₀ * ↑(Real.log p)) +
                 (starRingEnd ℂ) (χ ↑p) * h_hat (Real.log ↑p / (2 * Real.pi)) * Complex.exp (Complex.I * ↑t₀ * ↑(Real.log p))) := by ring
          rw [h_rhs_eq, Complex.re_ofReal_mul]
        rw [h_sum_eq]
        have h2pi_le : 1 / (2 * Real.pi) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith [Real.two_le_pi]
        rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
        calc (1 / (2 * Real.pi)) * |(D₁ χ).re + (star (D₂ χ)).re|
            ≤ 1 * (|(D₁ χ).re| + |(star (D₂ χ)).re|) := by
              gcongr; exact abs_add_le _ _
          _ ≤ ‖D₁ χ‖ + ‖star (D₂ χ)‖ := by
              rw [one_mul]
              exact add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _)
          _ = ‖D₁ χ‖ + ‖D₂ χ‖ := by rw [norm_star]
      have h_max : (‖D₁ χ‖ + ‖D₂ χ‖) ^ (2 * k) ≤ 4 ^ k * (‖D₁ χ‖ ^ (2 * k) + ‖D₂ χ‖ ^ (2 * k)) := by
        set m := max ‖D₁ χ‖ ‖D₂ χ‖
        calc (‖D₁ χ‖ + ‖D₂ χ‖) ^ (2 * k)
            ≤ (2 * m) ^ (2 * k) := by
              gcongr; linarith [le_max_left ‖D₁ χ‖ ‖D₂ χ‖, le_max_right ‖D₁ χ‖ ‖D₂ χ‖]
          _ = 4 ^ k * m ^ (2 * k) := by rw [mul_pow, pow_mul]; norm_num
          _ ≤ 4 ^ k * (‖D₁ χ‖ ^ (2 * k) + ‖D₂ χ‖ ^ (2 * k)) := by
              gcongr
              rcases le_total ‖D₁ χ‖ ‖D₂ χ‖ with h | h
              · simp only [m, max_eq_right h]; linarith [pow_nonneg (norm_nonneg (D₁ χ)) (2 * k)]
              · simp only [m, max_eq_left h]; linarith [pow_nonneg (norm_nonneg (D₂ χ)) (2 * k)]
      exact (pow_le_pow_left₀ (abs_nonneg _) h_le (2 * k)).trans h_max
    have h_poly_bound : ∀ (b : ℕ → ℂ),
        (∀ p ∈ primes, ‖b p‖ ≤ (Real.log p / Real.sqrt p) *
          max ‖h_hat (-(Real.log p / (2 * Real.pi)))‖ ‖h_hat (Real.log p / (2 * Real.pi))‖) →
        ∑ χ : DirichletCharacter ℂ q, ‖∑ p ∈ primes, b p * χ p‖ ^ (2 * k) ≤
          (Nat.totient q : ℝ) * (C_l2 * k * Real.log (Real.log X)) ^ k := by
      intro b hb
      set D : DirichletCharacter ℂ q → ℂ := fun χ => ∑ p ∈ primes, b p * χ p
      let fiber : ℕ → Finset (Fin k → ℕ) := fun n =>
        (Fintype.piFinset (fun _ : Fin k => primes)).filter (fun f => (∏ i, f i) = n)
      let a : ℕ → ℂ := fun n => ∑ f ∈ fiber n, ∏ i, b (f i)
      have h_pow_eq : ∀ χ : DirichletCharacter ℂ q, (D χ) ^ k = ∑ n ∈ Finset.Icc 1 (P ^ k), a n * χ n := by
        intro χ
        dsimp only [D]
        rw [Finset.sum_pow']
        have h_maps : ∀ f ∈ Fintype.piFinset (fun _ : Fin k => primes),
            (∏ i : Fin k, f i) ∈ Finset.Icc 1 (P ^ k) := by
          intro f hf
          rw [Fintype.mem_piFinset] at hf
          rw [Finset.mem_Icc]
          refine ⟨Nat.succ_le_of_lt (Finset.prod_pos (fun i _ => (Finset.mem_filter.mp (hf i)).2.pos)), ?_⟩
          calc ∏ i : Fin k, f i ≤ ∏ _i : Fin k, P :=
                Finset.prod_le_prod' fun i _ => (Finset.mem_Icc.mp (Finset.mem_filter.mp (hf i)).1).2
            _ = P ^ k := by simp
        rw [← Finset.sum_fiberwise_of_maps_to h_maps]
        refine Finset.sum_congr rfl fun n _ => ?_
        dsimp only [a, fiber]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun f hf => ?_
        simp only [Finset.mem_filter, Fintype.mem_piFinset] at hf
        rw [Finset.prod_mul_distrib, ← hf.2]
        congr 1
        push_cast
        rw [map_prod]
      have h_norm_eq : ∀ χ : DirichletCharacter ℂ q, ‖∑ p ∈ primes, b p * χ p‖ ^ (2 * k) =
          ‖∑ n ∈ Finset.Icc 1 (P ^ k), a n * χ n‖ ^ 2 := by
        intro χ
        rw [mul_comm 2 k, pow_mul, ← norm_pow]
        change ‖(D χ) ^ k‖ ^ 2 = _
        rw [h_pow_eq χ]
      simp_rw [h_norm_eq]
      have hPk_lt_q : P ^ k < q := by
        have h1 : ((P ^ k : ℕ) : ℝ) < (q : ℝ) := by
          have hP_le : (P : ℝ) ≤ X := Nat.floor_le (Real.exp_pos _).le
          calc ((P ^ k : ℕ) : ℝ) = (P : ℝ) ^ k := by push_cast; rfl
            _ ≤ X ^ k := pow_le_pow_left₀ (Nat.cast_nonneg P) hP_le k
            _ < q := hXk
        exact_mod_cast h1
      have h_orth : ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ Finset.Icc 1 (P ^ k), a n * χ n‖ ^ 2 ≤
          (Nat.totient q : ℝ) * ∑ n ∈ Finset.Icc 1 (P ^ k), ‖a n‖ ^ 2 := by
        have h_c_eq : ((∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ Finset.Icc 1 (P ^ k), a n * χ n‖ ^ 2 : ℝ) : ℂ) =
            ∑ m ∈ Finset.Icc 1 (P ^ k), ∑ n ∈ Finset.Icc 1 (P ^ k),
              a m * star (a n) * ∑ χ : DirichletCharacter ℂ q, χ m * star (χ n) := by
          push_cast
          have h_term : ∀ χ : DirichletCharacter ℂ q,
              (‖∑ n ∈ Finset.Icc 1 (P ^ k), a n * χ n‖ ^ 2 : ℂ) =
              ∑ m ∈ Finset.Icc 1 (P ^ k), ∑ n ∈ Finset.Icc 1 (P ^ k),
                a m * star (a n) * (χ m * star (χ n)) := by
            intro χ
            rw [← Complex.mul_conj', map_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [map_mul, Complex.star_def]; ring
          simp_rw [h_term]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.mul_sum]
        have h_inner : ∀ m ∈ Finset.Icc 1 (P ^ k), ∀ n ∈ Finset.Icc 1 (P ^ k), m ≠ n →
            ∑ χ : DirichletCharacter ℂ q, χ m * star (χ n) = 0 := by
          intro m hm n hn hmn
          simp only [Finset.mem_Icc] at hm hn
          by_cases hum : IsUnit (m : ZMod q)
          · by_cases hun : IsUnit (n : ZMod q)
            · have h_star : ∀ χ : DirichletCharacter ℂ q,
                  star (χ n) = χ ((hun.unit⁻¹ : (ZMod q)ˣ) : ZMod q) := by
                intro χ
                have hmul1 : χ n * χ ((hun.unit⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := by
                  have h_umul : (n : ZMod q) * ((hun.unit⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := by
                    calc (n : ZMod q) * ((hun.unit⁻¹ : (ZMod q)ˣ) : ZMod q)
                        = ((hun.unit : (ZMod q)ˣ) : ZMod q) * ((hun.unit⁻¹ : (ZMod q)ˣ) : ZMod q) := by
                          rw [hun.unit_spec]
                      _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
                  rw [← map_mul, h_umul, map_one]
                have hχn_ne : χ n ≠ 0 := fun h0 => by simp [h0] at hmul1
                have hnorm1 : ‖χ n‖ = 1 := dirichletChar_norm_eq_one χ hχn_ne
                have hmul2 : χ n * star (χ n) = 1 := by
                  rw [Complex.star_def, Complex.mul_conj', hnorm1]
                  norm_num
                exact mul_left_cancel₀ hχn_ne (hmul2.trans hmul1.symm)
              have h_prod : ∀ χ : DirichletCharacter ℂ q,
                  χ m * star (χ n) = χ (((hun.unit⁻¹ * hum.unit : (ZMod q)ˣ) : ZMod q)) := by
                intro χ
                rw [h_star χ, ← map_mul]
                congr 1
                push_cast
                rw [mul_comm, hum.unit_spec]
              simp_rw [h_prod]
              have ha_ne1 : (((hun.unit⁻¹ * hum.unit : (ZMod q)ˣ) : ZMod q)) ≠ 1 := by
                intro heq
                have hu_eq : hun.unit⁻¹ * hum.unit = 1 := Units.ext (by simpa using heq)
                have hum_eq : hum.unit = hun.unit := (eq_of_inv_mul_eq_one hu_eq).symm
                have hmn_zmod : (m : ZMod q) = (n : ZMod q) := by
                  rw [← hum.unit_spec, ← hun.unit_spec, hum_eq]
                have hm_lt : m < q := hm.2.trans_lt hPk_lt_q
                have hn_lt : n < q := hn.2.trans_lt hPk_lt_q
                have hval : m = n := by
                  have := congr_arg ZMod.val hmn_zmod
                  rwa [ZMod.val_natCast_of_lt hm_lt, ZMod.val_natCast_of_lt hn_lt] at this
                exact hmn hval
              haveI : NeZero q := ⟨hq_ne⟩
              exact DirichletCharacter.sum_characters_eq_zero (R := ℂ) ha_ne1
            · refine Finset.sum_eq_zero fun χ _ => ?_
              rw [MulChar.map_nonunit χ hun, star_zero, mul_zero]
          · refine Finset.sum_eq_zero fun χ _ => ?_
            rw [MulChar.map_nonunit χ hum, zero_mul]
        have h_diag : ((∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ Finset.Icc 1 (P ^ k), a n * χ n‖ ^ 2 : ℝ) : ℂ) =
            ∑ m ∈ Finset.Icc 1 (P ^ k), a m * star (a m) * ∑ χ : DirichletCharacter ℂ q, χ m * star (χ m) := by
          rw [h_c_eq]
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [Finset.sum_eq_single m (fun n hn hnm => by rw [h_inner m hm n hn hnm.symm, mul_zero])
            (fun hm' => absurd hm hm')]
        have h_re := congr_arg Complex.re h_diag
        simp only [Complex.ofReal_re, Complex.re_sum] at h_re
        rw [h_re]
        calc ∑ m ∈ Finset.Icc 1 (P ^ k), (a m * star (a m) * ∑ χ : DirichletCharacter ℂ q, χ m * star (χ m)).re
            = ∑ m ∈ Finset.Icc 1 (P ^ k), ‖a m‖ ^ 2 * ∑ χ : DirichletCharacter ℂ q, ‖χ m‖ ^ 2 := by
              refine Finset.sum_congr rfl fun m _ => ?_
              have h1 : a m * star (a m) = ((‖a m‖ ^ 2 : ℝ) : ℂ) := by
                rw [Complex.star_def, Complex.mul_conj']; push_cast; rfl
              have h2 : ∑ χ : DirichletCharacter ℂ q, χ m * star (χ m) =
                  ((∑ χ : DirichletCharacter ℂ q, ‖χ m‖ ^ 2 : ℝ) : ℂ) := by
                push_cast
                refine Finset.sum_congr rfl fun χ _ => ?_
                rw [Complex.star_def, Complex.mul_conj']
              rw [h1, h2, ← Complex.ofReal_mul, Complex.ofReal_re]
          _ ≤ ∑ m ∈ Finset.Icc 1 (P ^ k), ‖a m‖ ^ 2 * (Nat.totient q : ℝ) := by
              refine Finset.sum_le_sum fun m _ => ?_
              gcongr
              have hχ_le : ∑ χ : DirichletCharacter ℂ q, ‖χ m‖ ^ 2 ≤
                  ∑ _χ : DirichletCharacter ℂ q, (1 : ℝ) := by
                refine Finset.sum_le_sum fun χ _ => ?_
                by_cases h0 : χ m = 0
                · simp [h0]
                · rw [dirichletChar_norm_eq_one χ h0, one_pow]
              calc ∑ χ : DirichletCharacter ℂ q, ‖χ m‖ ^ 2
                  ≤ (Fintype.card (DirichletCharacter ℂ q) : ℝ) := by simpa using hχ_le
                _ = (Nat.totient q : ℝ) := by
                    rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
          _ = (Nat.totient q : ℝ) * ∑ m ∈ Finset.Icc 1 (P ^ k), ‖a m‖ ^ 2 := by
              rw [← Finset.sum_mul, mul_comm]
      have h_cs : ∀ n ∈ Finset.Icc 1 (P ^ k), ‖a n‖ ^ 2 ≤ (k.factorial : ℝ) * ∑ f ∈ fiber n, ∏ i, ‖b (f i)‖ ^ 2 := by
        intro n _
        dsimp only [a]
        have h1 : ‖∑ f ∈ fiber n, ∏ i, b (f i)‖ ^ 2 ≤ (∑ f ∈ fiber n, ‖∏ i, b (f i)‖) ^ 2 := by
          gcongr; exact norm_sum_le _ _
        have h2 : (∑ f ∈ fiber n, ‖∏ i, b (f i)‖) ^ 2 ≤ (fiber n).card * ∑ f ∈ fiber n, ‖∏ i, b (f i)‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
        have h_card : (fiber n).card ≤ k.factorial :=
          prime_tuple_fiber_card primes (fun p hp => (Finset.mem_filter.mp hp).2) k n
        have h3 : ((fiber n).card : ℝ) * ∑ f ∈ fiber n, ‖∏ i, b (f i)‖ ^ 2 ≤
            (k.factorial : ℝ) * ∑ f ∈ fiber n, ∏ i, ‖b (f i)‖ ^ 2 := by
          have h_eq : ∑ f ∈ fiber n, ‖∏ i, b (f i)‖ ^ 2 = ∑ f ∈ fiber n, ∏ i, ‖b (f i)‖ ^ 2 := by
            refine Finset.sum_congr rfl fun f _ => ?_
            rw [norm_prod, Finset.prod_pow]
          rw [h_eq]; gcongr
        exact h1.trans (h2.trans h3)
      have h_sum_a : ∑ n ∈ Finset.Icc 1 (P ^ k), ‖a n‖ ^ 2 ≤
          (k.factorial : ℝ) * (∑ p ∈ primes, ‖b p‖ ^ 2) ^ k := by
        calc ∑ n ∈ Finset.Icc 1 (P ^ k), ‖a n‖ ^ 2
            ≤ ∑ n ∈ Finset.Icc 1 (P ^ k), (k.factorial : ℝ) * ∑ f ∈ fiber n, ∏ i, ‖b (f i)‖ ^ 2 :=
              Finset.sum_le_sum h_cs
          _ = (k.factorial : ℝ) * ∑ n ∈ Finset.Icc 1 (P ^ k), ∑ f ∈ fiber n, ∏ i, ‖b (f i)‖ ^ 2 := by
              rw [← Finset.mul_sum]
          _ = (k.factorial : ℝ) * ∑ f ∈ Fintype.piFinset (fun _ : Fin k => primes), ∏ i, ‖b (f i)‖ ^ 2 := by
              congr 1
              refine Finset.sum_fiberwise_of_maps_to (fun f hf => ?_) _
              rw [Fintype.mem_piFinset] at hf
              rw [Finset.mem_Icc]
              refine ⟨Nat.succ_le_of_lt (Finset.prod_pos (fun i _ => (Finset.mem_filter.mp (hf i)).2.pos)), ?_⟩
              calc ∏ i : Fin k, f i ≤ ∏ _i : Fin k, P :=
                    Finset.prod_le_prod' fun i _ => (Finset.mem_Icc.mp (Finset.mem_filter.mp (hf i)).1).2
                _ = P ^ k := by simp
          _ = (k.factorial : ℝ) * (∑ p ∈ primes, ‖b p‖ ^ 2) ^ k := by
              rw [Finset.sum_pow']
      have h_l2_b : ∑ p ∈ primes, ‖b p‖ ^ 2 ≤ C_l2 * Real.log (Real.log X) := by
        calc ∑ p ∈ primes, ‖b p‖ ^ 2
            ≤ ∑ p ∈ primes, ((Real.log p / Real.sqrt p) *
                max ‖h_hat (-(Real.log p / (2 * Real.pi)))‖ ‖h_hat (Real.log p / (2 * Real.pi))‖) ^ 2 := by
              refine Finset.sum_le_sum fun p hp => ?_
              exact pow_le_pow_left₀ (norm_nonneg _) (hb p hp) 2
          _ ≤ C_l2 * Real.log (Real.log X) := hl2 Δ M hΔ hInt hL1
      have h_fac_le : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast factorial_le_pow k
      calc ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ Finset.Icc 1 (P ^ k), a n * χ n‖ ^ 2
          ≤ (Nat.totient q : ℝ) * ∑ n ∈ Finset.Icc 1 (P ^ k), ‖a n‖ ^ 2 := h_orth
        _ ≤ (Nat.totient q : ℝ) * ((k.factorial : ℝ) * (∑ p ∈ primes, ‖b p‖ ^ 2) ^ k) := by gcongr
        _ ≤ (Nat.totient q : ℝ) * ((k : ℝ) ^ k * (C_l2 * Real.log (Real.log X)) ^ k) := by
            gcongr
        _ = (Nat.totient q : ℝ) * (C_l2 * k * Real.log (Real.log X)) ^ k := by
            rw [← mul_pow]; ring_nf
    have hb₁ : ∀ p ∈ primes, ‖b₁ p‖ ≤ (Real.log p / Real.sqrt p) *
        max ‖h_hat (-(Real.log p / (2 * Real.pi)))‖ ‖h_hat (Real.log p / (2 * Real.pi))‖ := by
      intro p hp
      dsimp only [b₁]
      have he : ‖Complex.exp (-Complex.I * t₀ * Real.log p)‖ = 1 := by
        have : -Complex.I * ↑t₀ * ↑(Real.log p) = ((-t₀ * Real.log p : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I]
      rw [norm_mul, norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)) (Real.sqrt_nonneg p))]
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
    have hb₂ : ∀ p ∈ primes, ‖b₂ p‖ ≤ (Real.log p / Real.sqrt p) *
        max ‖h_hat (-(Real.log p / (2 * Real.pi)))‖ ‖h_hat (Real.log p / (2 * Real.pi))‖ := by
      intro p hp
      dsimp only [b₂]
      have he : ‖Complex.exp (-Complex.I * t₀ * Real.log p)‖ = 1 := by
        have : -Complex.I * ↑t₀ * ↑(Real.log p) = ((-t₀ * Real.log p : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I]
      rw [norm_mul, norm_mul, he, mul_one, norm_star, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)) (Real.sqrt_nonneg p))]
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
    have hloglogX_ge : 0 ≤ Real.log (Real.log X) := by
      rw [show Real.log X = 2 * Real.pi * Δ from Real.log_exp _]
      apply Real.log_nonneg
      have : 1 ≤ Δ := hΔ₀.trans hΔ
      nlinarith [Real.two_le_pi]
    calc (1 / (totientStar q : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
            |primeSum1 q χ h_hat X t₀| ^ (2 * k)
        ≤ (1 / (totientStar q : ℝ)) *
            ∑ χ : DirichletCharacter ℂ q, |primeSum1 q χ h_hat X t₀| ^ (2 * k) := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun χ _ _ => pow_nonneg (abs_nonneg _) _))
            (by positivity)
      _ ≤ (1 / (totientStar q : ℝ)) *
            ∑ χ : DirichletCharacter ℂ q, 4 ^ k * (‖D₁ χ‖ ^ (2 * k) + ‖D₂ χ‖ ^ (2 * k)) := by
          gcongr
          exact h_ptwise _
      _ = (1 / (totientStar q : ℝ)) *
            (4 ^ k * (∑ χ : DirichletCharacter ℂ q, ‖D₁ χ‖ ^ (2 * k) +
              ∑ χ : DirichletCharacter ℂ q, ‖D₂ χ‖ ^ (2 * k))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ (1 / (totientStar q : ℝ)) *
            (4 ^ k * ((Nat.totient q : ℝ) * (C_l2 * k * Real.log (Real.log X)) ^ k +
              (Nat.totient q : ℝ) * (C_l2 * k * Real.log (Real.log X)) ^ k)) := by
          have hb1_bd := h_poly_bound b₁ hb₁
          have hb2_bd := h_poly_bound b₂ hb₂
          change ∑ χ : DirichletCharacter ℂ q, ‖D₁ χ‖ ^ (2 * k) ≤ _ at hb1_bd
          change ∑ χ : DirichletCharacter ℂ q, ‖D₂ χ‖ ^ (2 * k) ≤ _ at hb2_bd
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (add_le_add hb1_bd hb2_bd) (by positivity))
            (by positivity)
      _ = ((Nat.totient q : ℝ) / (totientStar q : ℝ)) *
            (4 ^ k * (2 * (C_l2 * k * Real.log (Real.log X)) ^ k)) := by ring
      _ ≤ ((Nat.totient q : ℝ) / (totientStar q : ℝ)) *
            (4 ^ k * (2 ^ k * (C_l2 * k * Real.log (Real.log X)) ^ k)) := by
          gcongr
          have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk_pos
          simpa using this
      _ = ((Nat.totient q : ℝ) / (totientStar q : ℝ)) *
            (8 * C_l2 * k * Real.log (Real.log X)) ^ k := by
          rw [← mul_pow, ← mul_pow]; ring_nf
      _ ≤ ((Nat.totient q : ℝ) / (totientStar q : ℝ)) *
            (B * k * Real.log (Real.log X)) ^ k := by
          gcongr
          exact le_max_left _ _

end PolarEvaluation