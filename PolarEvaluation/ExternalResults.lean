import PolarEvaluation.Basic

/-!
# External Mathematical Axioms

This module contains ONLY established external results from peer-reviewed mathematical
literature that are not yet formalized in Mathlib. Every axiom is documented in
`EXTERNAL_AXIOMS.md` with its exact published source and justification.
No manuscript-owned theorem, lemma, or corollary appears here.
-/

noncomputable section

open Real Complex MeasureTheory

namespace PolarEvaluation

/-- **External Axiom E1 (Davenport 2000, Ch. 12; CCM 2013/2015):**
Hadamard factorization and horizontal logarithmic representation of `L(1/2 + it, χ)`
under GRH. -/
axiom horizontal_zero_sum_external (D : LFunctionData) (q : ℕ) (hq : q ≥ 1)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hGRH : D.GRH q hq χ hχ)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2))
    (t : ℝ) (ht0 : D.L q χ (1 / 2 + Complex.I * t) ≠ 0) (ht1 : q = 1 → |t| ≥ 10) :
    ∃ C_abs : ℝ, C_abs ≥ 0 ∧
      |(Complex.exp (-Complex.I * θ) *
          Complex.log (D.L q χ (1 / 2 + Complex.I * t))).re -
        ((Real.cos θ / 2) * Real.log (analyticConductor q t) +
          ∑' γ : D.zeros q χ, kernelK θ (t - (γ : ℝ)))| ≤ C_abs

/-- **External Axiom E2 (Carneiro-Chandee-Milinovich 2013, Lemma 5; 2015):**
Guinand-Weil explicit formula for bandlimited test functions `h : ℂ → ℂ` of
exponential type `2πΔ` with `O((1 + x^2)^{-1})` decay on `ℝ`. -/
axiom guinand_weil_external (D : LFunctionData) (q : ℕ) (hq : q ≥ 1)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hGRH : D.GRH q hq χ hχ)
    (Δ : ℝ) (hΔ : Δ ≥ 1) (h : ℂ → ℂ) (hh_type : HasExponentialType h (2 * Real.pi * Δ))
    (M : ℝ) (hM : ∀ x : ℝ, (1 + x ^ 2) * ‖h x‖ ≤ M)
    (t : ℝ) (ht1 : q = 1 → |t| ≥ 10) :
    ∃ C_gw : ℝ, C_gw ≥ 0 ∧
      ‖(∑' γ : D.zeros q χ, h (t - (γ : ℝ))) -
        ((Real.log (analyticConductor q t) / (2 * Real.pi)) * (∫ x : ℝ, h x) -
          (1 / (2 * Real.pi)) *
            ∑' n : ℕ, if 2 ≤ n ∧ (n : ℝ) ≤ Real.exp (2 * Real.pi * Δ) then
              ((ArithmeticFunction.vonMangoldt n : ℂ) / Real.sqrt n) *
                (χ n * (fourierHat (fun x : ℝ => h x) (-Real.log n / (2 * Real.pi))) *
                    (n : ℂ) ^ (-Complex.I * t) +
                  starRingEnd ℂ (χ n) *
                    (fourierHat (fun x : ℝ => h x) (Real.log n / (2 * Real.pi))) *
                    (n : ℂ) ^ (Complex.I * t))
            else 0)‖ ≤
        C_gw * (M + (if q = 1 then Real.exp (Real.pi * Δ) / t ^ 2 * M else 0))

/-- **External Axiom E3 (Montgomery-Vaughan 1974, Hilbert's Inequality):**
Mean value theorem for Dirichlet polynomials over `[T, 2T]`. -/
axiom montgomery_vaughan_mvt (N : ℕ) (T : ℝ) (hT : T > 0) (a : ℕ → ℂ) :
    ∃ C_mv : ℝ, C_mv ≥ 0 ∧
      ∫ t in Set.Icc T (2 * T),
        ‖∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-Complex.I * t)‖ ^ 2 ≤
        (T + C_mv * N) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2

/-- **External Axiom E4 (Carneiro-Chandee-Milinovich 2013):**
Existence of the odd Beurling-Selberg majorant and minorant `M^±_{π/2,Δ}` of `K_{π/2}`
of exponential type `2πΔ` with `L^1` excess `π/(2Δ) + O(exp(-2πΔ))` and uniform
`(1+x^2)^{-1}` decay. -/
axiom ccm_odd_extremal (Δ : ℝ) (hΔ : Δ ≥ 1) :
    ∃ M_plus M_minus : ℝ → ℝ,
      (∀ x : ℝ, x ≠ 0 → M_minus x ≤ kernelK (Real.pi / 2) x ∧
        kernelK (Real.pi / 2) x ≤ M_plus x) ∧
      (∃ C_1 > 0, ∀ x : ℝ, (1 + x ^ 2) * |M_plus x| ≤ C_1 ∧
        (1 + x ^ 2) * |M_minus x| ≤ C_1) ∧
      (∃ C_2 > 0,
        |∫ x : ℝ, (M_plus x - kernelK (Real.pi / 2) x) - Real.pi / (2 * Δ)| ≤
          C_2 * Real.exp (-2 * Real.pi * Δ) ∧
        |∫ x : ℝ, (kernelK (Real.pi / 2) x - M_minus x) - Real.pi / (2 * Δ)| ≤
          C_2 * Real.exp (-2 * Real.pi * Δ))

end PolarEvaluation
