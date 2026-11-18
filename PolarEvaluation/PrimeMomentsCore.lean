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
            by_cases hp : Nat.Prime p
            · simp only [hp, and_true]; omega
            · simp only [hp, and_false, or_self]
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
            have h_each : ∀ p ∈ s, p ∣ Nat.choose (2 * m + 1) m := by
              intro p hp
              simp only [s, Finset.mem_filter, Finset.mem_Icc] at hp
              have hchoose := Nat.choose_mul_factorial_mul_factorial (by omega : m ≤ 2 * m + 1)
              have hsub : 2 * m + 1 - m = m + 1 := by omega
              rw [hsub] at hchoose
              have hp_dvd_fac : p ∣ Nat.factorial (2 * m + 1) := hp.2.dvd_factorial.mpr hp.1.2
              rw [← hchoose] at hp_dvd_fac
              have hp_not_m : ¬ p ∣ Nat.factorial m := by
                rw [hp.2.dvd_factorial]; omega
              have hp_not_m1 : ¬ p ∣ Nat.factorial (m + 1) := by
                rw [hp.2.dvd_factorial]; omega
              rcases hp.2.dvd_mul.mp hp_dvd_fac with h1 | h2
              · rcases hp.2.dvd_mul.mp h1 with h1a | h1b
                · exact h1a
                · exact absurd h1b hp_not_m
              · exact absurd h2 hp_not_m1
            have h_ind : ∀ t : Finset ℕ, (∀ p ∈ t, Nat.Prime p) →
                (∀ p ∈ t, p ∣ Nat.choose (2 * m + 1) m) →
                ∏ p ∈ t, p ∣ Nat.choose (2 * m + 1) m := by
              intro t ht_p ht_d
              induction t using Finset.induction_on with
              | empty => simp
              | @insert a t ha ih =>
                rw [Finset.prod_insert ha]
                have ha_p : Nat.Prime a := ht_p a (Finset.mem_insert_self a t)
                have hcop : Nat.Coprime a (∏ p ∈ t, p) :=
                  Nat.Coprime.prod_right fun p hp =>
                    (Nat.coprime_primes ha_p (ht_p p (Finset.mem_insert_of_mem hp))).mpr (fun h => ha (h ▸ hp))
                exact hcop.mul_dvd_of_dvd_of_dvd (ht_d a (Finset.mem_insert_self a t))
                  (ih (fun p hp => ht_p p (Finset.mem_insert_of_mem hp))
                    (fun p hp => ht_d p (Finset.mem_insert_of_mem hp)))
            exact h_ind s (fun p hp => (Finset.mem_filter.mp hp).2) h_each
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
              simpa [show 2 * m + 1 - m = m + 1 by omega] using Nat.choose_symm (by omega : m ≤ 2 * m + 1)
            rw [hsymm, hsum] at hpair
            have hpow : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by
              rw [pow_succ, show 2 * m = 2 * m from rfl, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
              ring
            omega
          have hprod_le : (∏ p ∈ s, (p : ℝ)) ≤ (4 : ℝ) ^ m := by
            rw [← Nat.cast_prod]
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
  | base => simp [Finset.filter_singleton, Nat.prime_two]
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

    rw [Finset.sum_Ico_succ_top hN]
    by_cases hp : Nat.Prime (N + 1)
    · rw [hIcc, if_pos hp, Finset.sum_insert hnot_mem, Finset.sum_insert hnot_mem, ih]
      ring
    · rw [hIcc, if_neg hp, ih]
      ring

lemma sum_Ico_sub_telescope (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, (f (k + 1) - f k) = f b - f a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih => rw [Finset.sum_Ico_succ_top hab, ih]; ring

/-- Mertens' 1st Theorem (upper bound): `∑_{p ≤ N} log p / p ≤ log 4 * (log N + 1)`. -/
lemma mertens_first (N : ℕ) (hN : N ≥ 2) :
    ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, Real.log p / p ≤ Real.log 4 * (Real.log N + 1) := by
  have h_abel := abel_sum_primes (fun p => Real.log p) (fun k => 1 / (k : ℝ)) N hN
  have h_div_eq : ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, Real.log p / (p : ℝ) =
      ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, Real.log p * (1 / (p : ℝ)) :=
    Finset.sum_congr rfl fun p _ => div_eq_mul_one_div _ _
  rw [h_div_eq, h_abel]
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
          exact sum_Ico_sub_telescope (fun k : ℕ => Real.log k) hN
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
      exact ⟨fun h => by omega, by rintro rfl; exact ⟨⟨le_rfl, le_rfl⟩, Nat.prime_two⟩⟩
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
      exact hm1.trans (mul_le_mul_of_nonneg_left (add_le_add h_loglog le_rfl) (Real.log_nonneg (by norm_num)))
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
          · exact sum_Ico_sub_telescope (fun k : ℕ => Real.log (Real.log k)) hN
          · have hsub := sum_Ico_sub_telescope (fun k : ℕ => -(1 / Real.log k)) hN
            have h_lhs_sub : ∑ k ∈ Finset.Ico 3 N, (1 / Real.log k - 1 / Real.log (k + 1 : ℕ)) =
                ∑ k ∈ Finset.Ico 3 N, (-(1 / Real.log (k + 1 : ℕ)) - -(1 / Real.log k)) := by
              congr 1; ext k; ring
            rw [h_lhs_sub, hsub]; ring_nf
      _ ≤ Real.log 4 * (Real.log (Real.log N) + 1 / Real.log 3 + 1) := by
          have hlog3_gt1 : 1 < Real.log 3 := by
            have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
            rw [← Real.log_exp 1]
            exact Real.log_lt_log (Real.exp_pos 1) he
          have hloglog3_nonneg : 0 ≤ Real.log (Real.log 3) := Real.log_nonneg hlog3_gt1.le
          exact mul_le_mul_of_nonneg_left
            (by linarith [div_pos one_pos hlogN_pos, hloglog3_nonneg])
            (Real.log_nonneg (by norm_num))
  have hlog4_le : Real.log 4 ≤ 2 := by
    have hlog2_le : Real.log 2 ≤ 1 := by
      have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      rw [← Real.log_exp 1]; exact Real.log_le_log (by norm_num) he
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num; linarith
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
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h1' : (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, Real.log p / p) * (1 / Real.log N) ≤ 6 :=
    h1.trans (by nlinarith)
  have h2_bot' : (∑ p ∈ (Finset.Icc 2 2).filter Nat.Prime, Real.log p / p) * (1 / Real.log 2 - 1 / Real.log 3) ≤ 6 :=
    h2_bot.trans (by nlinarith)
  have h2_tail' : ∑ k ∈ Finset.Ico 3 N,
      (∑ p ∈ (Finset.Icc 2 k).filter Nat.Prime, Real.log p / p) *
        (1 / Real.log k - 1 / Real.log (k + 1 : ℕ)) ≤ 2 * (Real.log (Real.log N) + 2) :=
    h2_tail.trans (by nlinarith)
  linarith

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
    have h_eq : (fun n : ℕ => (n : ℝ) ^ (-5 / 4 : ℝ)) = fun n : ℕ => 1 / (n : ℝ) ^ (5 / 4 : ℝ) := by
      ext n
      rw [show (-5 / 4 : ℝ) = -(5 / 4 : ℝ) by norm_num, Real.rpow_neg (Nat.cast_nonneg n), one_div]
    rw [h_eq]
    exact (Real.summable_one_div_nat_rpow (p := (5 / 4 : ℝ))).mpr (by norm_num)
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
    exact Real.log_le_log (Real.exp_pos 1) (by nlinarith [h2pi_ge, hΔ₀.trans hΔ, Real.exp_pos 1])
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
        rw [this]
        positivity
      have hdec1 := h_dec Δ M hΔ hInt hL1 (Real.log (p ^ 2) / (2 * Real.pi)) hξ_pos.ne'
      have hdec2 := h_dec Δ M hΔ hInt hL1 (-(Real.log (p ^ 2) / (2 * Real.pi))) (neg_ne_zero.mpr hξ_pos.ne')
      have h_abs_ξ : 1 / (2 * Real.pi * |Real.log (p ^ 2) / (2 * Real.pi)|) ≤ 1 / Real.log p := by
        rw [abs_of_pos hξ_pos]
        have heq : 2 * Real.pi * (Real.log (p ^ 2) / (2 * Real.pi)) = 2 * Real.log p := by
          field_simp [Real.pi_ne_zero]
          rw [Real.log_pow]; norm_num
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
        calc |(χ (p ^ 2) * h_hat (-(Real.log (p ^ 2) / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log (p ^ 2)) +
                star (χ (p ^ 2)) * h_hat (Real.log (p ^ 2) / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log (p ^ 2))).re|
            ≤ ‖χ (p ^ 2) * h_hat (-(Real.log (p ^ 2) / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log (p ^ 2)) +
                star (χ (p ^ 2)) * h_hat (Real.log (p ^ 2) / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log (p ^ 2))‖ := Complex.abs_re_le_norm _
          _ ≤ ‖χ (p ^ 2) * h_hat (-(Real.log (p ^ 2) / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log (p ^ 2))‖ +
              ‖star (χ (p ^ 2)) * h_hat (Real.log (p ^ 2) / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log (p ^ 2))‖ := norm_add_le _ _
          _ = ‖χ (p ^ 2)‖ * ‖h_hat (-(Real.log (p ^ 2) / (2 * Real.pi)))‖ * 1 +
              ‖χ (p ^ 2)‖ * ‖h_hat (Real.log (p ^ 2) / (2 * Real.pi))‖ * 1 := by
              rw [norm_mul, norm_mul, norm_mul, norm_mul, he1, he2, norm_star]
          _ ≤ 1 * (C_dec * (1 / Real.log p + 1 / Δ)) * 1 + 1 * (C_dec * (1 / Real.log p + 1 / Δ)) * 1 := by
              have hp2 : ‖χ ((p : ZMod q) ^ 2)‖ ≤ 1 := by rw [← Nat.cast_pow]; exact hchi_le (p ^ 2)
              gcongr
          _ = 2 * C_dec * (1 / Real.log p + 1 / Δ) := by ring
      rw [abs_mul, abs_of_nonneg (div_nonneg hlogp_pos.le hp_pos.le)]
      calc (Real.log p / (p : ℝ)) *
            |(χ (p ^ 2) * h_hat (-(Real.log (p ^ 2) / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log (p ^ 2)) +
              star (χ (p ^ 2)) * h_hat (Real.log (p ^ 2) / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log (p ^ 2))).re|
          ≤ (Real.log p / (p : ℝ)) * (2 * C_dec * (1 / Real.log p + 1 / Δ)) := by gcongr
        _ = 2 * C_dec * (1 / (p : ℝ) + (1 / Δ) * (Real.log p / (p : ℝ))) := by
            field_simp [hlogp_pos.ne', hp_pos.ne']
    have hsum_bd : |∑ p ∈ (Finset.Icc 2 N₂).filter Nat.Prime,
          (Real.log p / (p : ℝ)) *
            (χ (p ^ 2) * h_hat (-(Real.log (p ^ 2) / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log (p ^ 2)) +
             star (χ (p ^ 2)) * h_hat (Real.log (p ^ 2) / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log (p ^ 2))).re| ≤
        2 * C_dec * (∑ p ∈ (Finset.Icc 2 N₂).filter Nat.Prime, (1 : ℝ) / p +
          (1 / Δ) * ∑ p ∈ (Finset.Icc 2 N₂).filter Nat.Prime, Real.log p / p) := by
      calc |∑ p ∈ (Finset.Icc 2 N₂).filter Nat.Prime,
              (Real.log p / (p : ℝ)) *
                (χ (p ^ 2) * h_hat (-(Real.log (p ^ 2) / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log (p ^ 2)) +
                 star (χ (p ^ 2)) * h_hat (Real.log (p ^ 2) / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log (p ^ 2))).re|
          ≤ ∑ p ∈ (Finset.Icc 2 N₂).filter Nat.Prime,
              |(Real.log p / (p : ℝ)) *
                (χ (p ^ 2) * h_hat (-(Real.log (p ^ 2) / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log (p ^ 2)) +
                 star (χ (p ^ 2)) * h_hat (Real.log (p ^ 2) / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log (p ^ 2))).re| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p ∈ (Finset.Icc 2 N₂).filter Nat.Prime,
              2 * C_dec * (1 / (p : ℝ) + (1 / Δ) * (Real.log p / (p : ℝ))) := Finset.sum_le_sum h_term
        _ = 2 * C_dec * (∑ p ∈ (Finset.Icc 2 N₂).filter Nat.Prime, (1 : ℝ) / p +
              (1 / Δ) * ∑ p ∈ (Finset.Icc 2 N₂).filter Nat.Prime, Real.log p / p) := by
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
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num; linarith
      have hΔ_pos : 0 < Δ := by linarith
      have hpi_lt : Real.pi < 4 := Real.pi_lt_four
      calc (1 / Δ) * ∑ p ∈ (Finset.Icc 2 N₂).filter Nat.Prime, Real.log p / p
          ≤ (1 / Δ) * (Real.log 4 * (Real.log N₂ + 1)) := by gcongr
        _ ≤ (1 / Δ) * (2 * (2 * Real.pi * Δ + 1)) := by gcongr
        _ = 4 * Real.pi + 2 / Δ := by field_simp [hΔ_pos.ne']; ring
        _ ≤ 4 * 4 + 2 / 1 := by gcongr; linarith
        _ = 18 := by norm_num
        _ ≤ 20 * Real.log (Real.log X) := by nlinarith [hloglogX_ge]
    rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
    have h2pi_ge : 1 / (2 * Real.pi) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [Real.two_le_pi]
    calc (1 / (2 * Real.pi)) * |∑ p ∈ (Finset.Icc 2 N₂).filter Nat.Prime,
          (Real.log p / (p : ℝ)) *
            (χ (p ^ 2) * h_hat (-(Real.log (p ^ 2) / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log (p ^ 2)) +
             star (χ (p ^ 2)) * h_hat (Real.log (p ^ 2) / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log (p ^ 2))).re|
        ≤ 1 * (2 * C_dec * (30 * Real.log (Real.log X) + 20 * Real.log (Real.log X))) := by
          refine mul_le_mul h2pi_ge ?_ (abs_nonneg _) zero_le_one
          exact hsum_bd.trans (mul_le_mul_of_nonneg_left (add_le_add hm2 hm1) (by positivity))
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
      rw [hv, hsq]; push_cast; ring
    have hP_all : (1 / (2 * Real.pi)) * ∑ n ∈ Finset.Icc 2 N,
          ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
            (χ n * h_hat (-(Real.log n / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log n) +
             star (χ n) * h_hat (Real.log n / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log n)).re =
        ∑ n ∈ Finset.Icc 2 N, f n := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => by dsimp only [f]; ring
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
        have hsq : (p : ℝ) ^ 2 ≤ Real.sqrt X ^ 2 := by nlinarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
        rw [Real.sq_sqrt (by linarith)] at hsq; push_cast; exact hsq
      · intro hmem
        rcases hmem.2.eq_one_or_self_of_dvd p (dvd_pow_self p two_ne_zero) with h1 | h2
        · linarith [hp.2.two_le]
        · nlinarith [hp.2.two_le]
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
        calc |(χ n * h_hat (-(Real.log n / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log n) +
                star (χ n) * h_hat (Real.log n / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log n)).re|
            ≤ ‖χ n * h_hat (-(Real.log n / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log n) +
                star (χ n) * h_hat (Real.log n / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log n)‖ := Complex.abs_re_le_norm _
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
      have h_mul_bd : (1 / (2 * Real.pi)) * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
          |(χ n * h_hat (-(Real.log n / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log n) +
            star (χ n) * h_hat (Real.log n / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log n)).re| ≤
          (1 / (2 * Real.pi)) * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) * (2 * max C_L1 1) :=
        mul_le_mul_of_nonneg_left h_re_bd (by positivity)
      calc (1 / (2 * Real.pi)) * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
            |(χ n * h_hat (-(Real.log n / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log n) +
              star (χ n) * h_hat (Real.log n / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log n)).re|
          ≤ (1 / (2 * Real.pi)) * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) * (2 * max C_L1 1) := h_mul_bd
        _ = ((1 / (2 * Real.pi)) * 2) * max C_L1 1 * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) := by ring
        _ ≤ 1 * max C_L1 1 * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) := by gcongr
        _ = max C_L1 1 * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) := by rw [one_mul]
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
        refine ⟨p, ⟨⟨hp.two_le, ?_⟩, hp⟩, rfl⟩
        refine Nat.le_floor ?_
        rw [Real.le_sqrt' (by exact_mod_cast hp.pos)]
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
    have h_sum_img_le : ∀ {α β : Type} [DecidableEq α] [DecidableEq β] (s : Finset α) (φ : α → β) (g : β → ℝ),
        (∀ x ∈ s, 0 ≤ g (φ x)) → ∑ y ∈ s.image φ, g y ≤ ∑ x ∈ s, g (φ x) := by
      intro α β _ _ s φ g hg
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
            max C_L1 1 * ((ArithmeticFunction.vonMangoldt (pk.1 ^ pk.2) : ℝ) / Real.sqrt ((pk.1 ^ pk.2 : ℕ) : ℝ)) := by
          refine h_sum_img_le S_pk (fun pk : ℕ × ℕ => pk.1 ^ pk.2)
            (fun n : ℕ => max C_L1 1 * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n)) (fun pk _ => ?_)
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
          have hsqrt_pow : Real.sqrt ((p : ℝ) ^ k) = (Real.sqrt p) ^ k := by
            rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
              ← Real.rpow_mul (Nat.cast_nonneg p), mul_comm (k : ℝ) (1 / 2 : ℝ),
              Real.rpow_mul (Nat.cast_nonneg p), Real.rpow_natCast]
          rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega : k ≠ 0),
            ArithmeticFunction.vonMangoldt_apply_prime hp.2,
            Nat.cast_pow, hsqrt_pow, one_div, inv_pow, div_eq_mul_inv]
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


end PolarEvaluation
