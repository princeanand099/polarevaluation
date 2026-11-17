# Manuscript-to-Lean Theorem Correspondence Record

| Manuscript Result | Location | Lean Module | Lean Declaration | Dependencies | Fidelity | Proof Status |
|---|---|---|---|---|---|---|
| Analytic conductor `q` | Sec. 1 | `PolarEvaluation.Basic` | `analyticConductor` | — | Exact | Defined |
| Mixed kernel `K_θ(x)` | Sec. 1, (1.6) | `PolarEvaluation.Basic` | `kernelK` | — | Exact | Defined |
| Envelope constant `C(θ)` | Sec. 1, (1.4) | `PolarEvaluation.Basic` | `envelopeC` | — | Exact | Defined |
| Convex domain `Ω` | Sec. 1, Thm. 1.2 | `PolarEvaluation.Basic` | `convexOmega` | — | Exact | Defined |
| Rescaled kernel `F_{θ,Δ}` | Sec. 3, (3.1) | `PolarEvaluation.Basic` | `rescaledF`, `rescaledFDeriv` | `kernelK` | Exact | Defined |
| Vaaler interpolant `M_α` | Sec. 3.1, (3.3) | `PolarEvaluation.Basic` | `vaalerInterpolant` | `rescaledF`, `rescaledFDeriv` | Exact | Defined |
| Limiting integral `J(y, θ)` | Sec. 3.3, (3.8) | `PolarEvaluation.Basic` | `limitingJ` | — | Exact | Defined |
| Lemma 2.1 (Horizontal zero-sum) | Sec. 2 | `PolarEvaluation.ExplicitFormulae` | `horizontal_zero_sum` | Axiom E1 | Exact | Proved from E1 |
| Lemma 2.2 (Guinand-Weil) | Sec. 2 | `PolarEvaluation.ExplicitFormulae` | `guinand_weil_bandlimited` | Axiom E2 | Exact | Proved from E2 |
| Lemma 2.3 (Fourier of `K_θ`) | Sec. 2 | `PolarEvaluation.ExplicitFormulae` | `kernelK_fourier`, `majorant_fourier_decay` | — | Exact | `sorry` (Stage 4) |
| Lemma 3.1 (Lattice shift `α_Δ`) | Sec. 3.1 | `PolarEvaluation.ShiftedLattice` | `optimal_lattice_shift` | — | Exact | `sorry` (Stage 4) |
| Lemma 3.2 (Contour rep.) | Sec. 3.2 | `PolarEvaluation.ShiftedLattice` | `contour_representation` | — | Exact | `sorry` (Stage 4) |
| Lemma 3.3 (`J(y, θ)` bounds) | Sec. 3.3 | `PolarEvaluation.ShiftedLattice` | `limitingJ_pos`, `limitingJ_near_zero`, `limitingJ_asymptotic` | — | Exact | `sorry` (Stage 4) |
| Theorem 1.7 (Majorant) | Sec. 1 & 3.4 | `PolarEvaluation.ShiftedLattice` | `asymmetric_majorant` | Lemmas 3.1–3.3 | Exact | `sorry` (Stage 4) |
| Theorem 1.1 (Directional bound) | Sec. 1 & 4 | `PolarEvaluation.PointwiseEnvelope` | `directional_envelope_bound` | Thm 1.7, Lemmas 2.1–2.2 | Exact | `sorry` (Stage 4) |
| Theorem 1.2 (Convex domain `Ω`) | Sec. 1 & 4 | `PolarEvaluation.PointwiseEnvelope` | `convex_domain_confinement`, `modulus_argument_tradeoff` | Thm 1.1, Eq. (1.2) | Exact | `sorry` (Stage 4) |
| Corollary 1.3 (Trade-off cases) | Sec. 1 & 4 | `PolarEvaluation.PointwiseEnvelope` | `corollary_1_3_i` | Thm 1.2 | Exact | `sorry` (Stage 4) |
| Lemma 5.1 (Prime-power tail) | Sec. 5 | `PolarEvaluation.PrimeMoments` | `prime_power_tail_bounds` | Lemma 2.3 | Exact | `sorry` (Stage 4) |
| Lemma 5.2 (`2k`-th moments) | Sec. 5 | `PolarEvaluation.PrimeMoments` | `prime_moment_t_aspect`, `prime_moment_q_aspect` | Lemma 2.3, Axiom E3 | Exact | `sorry` (Stage 4) |
| Theorem 1.4 (`t`-aspect LD) | Sec. 1 & 6 | `PolarEvaluation.LargeDeviations` | `t_aspect_large_deviation` | Thm 1.7, Lemmas 2.1–2.2, 5.1–5.2 | Exact | `sorry` (Stage 4) |
| Theorem 1.5 (`q`-aspect LD) | Sec. 1 & 6 | `PolarEvaluation.LargeDeviations` | `q_aspect_large_deviation` | Thm 1.7, Lemmas 2.1–2.2, 5.1–5.2 | Exact | `sorry` (Stage 4) |
| Corollary 1.6 (`|S|` LD) | Sec. 1 & 6 | `PolarEvaluation.LargeDeviations` | `S_large_deviation_t` | Axiom E4, Lemmas 2.3, 5.1–5.2 | Exact | `sorry` (Stage 4) |
