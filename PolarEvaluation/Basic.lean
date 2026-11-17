import Mathlib

/-!
# Foundational Definitions for the Polar Envelope and Large Deviations of log L(1/2 + it, χ)

This module defines the analytic conductor, the mixed logarithmic-argument kernel `K_θ`,
the directional envelope constant `C(θ)`, the universal convex domain `Ω`, the rescaled
kernel `F_{θ,Δ}`, the shifted-lattice Vaaler Hermite interpolant `M_{θ,Δ}`, the limiting
integral kernel `J(y, θ)`, and the abstract `LFunctionData` interface.
-/

noncomputable section

open Complex Real MeasureTheory Filter Topology

namespace PolarEvaluation

/-- Normalized Fourier transform: `\hat{f}(ξ) = ∫_{-∞}^∞ f(x) e^{-2π i ξ x} dx`. -/
def fourierHat (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ x : ℝ, f x * Complex.exp (-2 * Real.pi * Complex.I * ξ * x)

/-- Analytic conductor `q(|t| + 2)`. -/
def analyticConductor (q : ℕ) (t : ℝ) : ℝ :=
  (q : ℝ) * (|t| + 2)

/-- Mixed logarithmic-argument kernel `K_θ(x)` from (1.5). -/
def kernelK (θ x : ℝ) : ℝ :=
  -(Real.cos θ / 2) * Real.log ((x ^ 2 + 1) / x ^ 2) +
    Real.sin θ * (Real.arctan (1 / x) - x / (x ^ 2 + 1))

/-- Sharp directional envelope constant `C(θ) = \frac{1}{2}(cos(θ) log(2 cos θ) + θ sin θ)` from (1.4). -/
def envelopeC (θ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (Real.cos θ * Real.log (2 * Real.cos θ) + θ * Real.sin θ)

/-- Universal closed convex domain `Ω = {x + iy ∈ ℂ : |y| < π/4, e^{2x} ≤ 2 cos(2y)}`. -/
def convexOmega : Set ℂ :=
  { z : ℂ | |z.im| < Real.pi / 4 ∧ Real.exp (2 * z.re) ≤ 2 * Real.cos (2 * z.im) }

/-- Rescaled kernel `F_{θ,Δ}(y) = K_θ(y / Δ)` from (3.1). -/
def rescaledF (θ Δ y : ℝ) : ℝ :=
  kernelK θ (y / Δ)

/-- Derivative `F'_{θ,Δ}(y)` from Section 3.1. -/
def rescaledFDeriv (θ Δ y : ℝ) : ℝ :=
  Real.cos θ * (1 / y - y / (y ^ 2 + Δ ^ 2)) - Real.sin θ * (2 * Δ ^ 3 / (y ^ 2 + Δ ^ 2) ^ 2)

/-- An entire function `M : ℂ → ℂ` has exponential type at most `σ`. -/
def HasExponentialType (M : ℂ → ℂ) (σ : ℝ) : Prop :=
  Differentiable ℂ M ∧ ∀ ε > 0, ∃ C > 0, ∀ z : ℂ, ‖M z‖ ≤ C * Real.exp ((σ + ε) * ‖z‖)

/-- Shifted-lattice Vaaler Hermite interpolant `M_α(y)` on `ℤ + α` from (3.3). -/
def vaalerInterpolant (θ Δ α y : ℝ) : ℝ :=
  letI := Classical.propDecidable
  if ∃ n : ℤ, y = n + α then rescaledF θ Δ y
  else (Real.sin (Real.pi * (y - α))) ^ 2 / Real.pi ^ 2 *
    ∑' n : ℤ, (rescaledF θ Δ (n + α) / (y - n - α) ^ 2 +
      rescaledFDeriv θ Δ (n + α) / (y - n - α))

/-- Scaled majorant `M_{θ,Δ}(x) = M_{α_Δ}(Δ x)`. -/
def majorantM (θ Δ α x : ℝ) : ℝ :=
  vaalerInterpolant θ Δ α (Δ * x)

/-- Limiting integral kernel `J(y, θ)` from (3.6). -/
def limitingJ (y θ : ℝ) : ℝ :=
  ∫ v in Set.Ioi (0 : ℝ),
    (Complex.exp (-Complex.I * θ) /
      (Complex.cos (θ + Complex.I * Real.pi * v) ^ 2 * (y - Complex.I * v))).im

/-- Abstract interface for Dirichlet `L`-functions `L(s, χ)` and their nontrivial zeros. -/
structure LFunctionData where
  L_val : (q : ℕ) → DirichletCharacter ℂ q → ℂ → ℂ
  logAbsL : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℝ
  S_val : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℝ
  zeros : (q : ℕ) → DirichletCharacter ℂ q → ℕ → ℝ
  GRH : (q : ℕ) → q ≥ 1 → (χ : DirichletCharacter ℂ q) → χ.IsPrimitive → Prop
  nonvanishing : (q : ℕ) → DirichletCharacter ℂ q → ℝ → Prop
  nonvanishing_zeros : ∀ q χ t, nonvanishing q χ t → ∀ n : ℕ, t ≠ zeros q χ n

/-- Polar projection `Re(e^{-iθ} log L(1/2 + it, χ)) = cos(θ) log|L(1/2 + it, χ)| + sin(θ) π S(t, χ)`. -/
def polarLogL (D : LFunctionData) (q : ℕ) (χ : DirichletCharacter ℂ q) (t θ : ℝ) : ℝ :=
  Real.cos θ * D.logAbsL q χ t + Real.sin θ * (Real.pi * D.S_val q χ t)

/-- Normalized complex value `z(t, χ) = log L(1/2 + it, χ) / (log q / log log q)`. -/
def normalizedLogL (D : LFunctionData) (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  let scale := Real.log (analyticConductor q t) / Real.log (Real.log (analyticConductor q t))
  ⟨D.logAbsL q χ t / scale, (Real.pi * D.S_val q χ t) / scale⟩

/-- Number of primitive Dirichlet characters modulo `q`, `φ*(q)`. -/
noncomputable def totientStar (q : ℕ) : ℕ :=
  letI := Classical.decPred (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)
  (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)).card

/-- Prime-power sum `P_{θ,Δ}(t, χ)` from Section 4. -/
def primePowerSum (q : ℕ) (χ : DirichletCharacter ℂ q) (h_hat : ℝ → ℂ) (X t : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∑ n ∈ Finset.Icc 2 (Nat.floor X),
      ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
        (χ n * h_hat (-(Real.log n / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log n) +
         star (χ n) * h_hat (Real.log n / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log n)).re

/-- Prime-only part `P^{(1)}_{θ,Δ}(t, χ)` (`n = p` prime). -/
def primeSum1 (q : ℕ) (χ : DirichletCharacter ℂ q) (h_hat : ℝ → ℂ) (X t : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∑ p ∈ (Finset.Icc 2 (Nat.floor X)).filter Nat.Prime,
      (Real.log p / Real.sqrt p) *
        (χ p * h_hat (-(Real.log p / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log p) +
         star (χ p) * h_hat (Real.log p / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log p)).re

/-- Prime-square part `P^{(2)}_{θ,Δ}(t, χ)` (`n = p^2`). -/
def primeSum2 (q : ℕ) (χ : DirichletCharacter ℂ q) (h_hat : ℝ → ℂ) (X t : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∑ p ∈ (Finset.Icc 2 (Nat.floor (Real.sqrt X))).filter Nat.Prime,
      (Real.log p / (p : ℝ)) *
        (χ (p ^ 2) * h_hat (-(Real.log (p ^ 2) / (2 * Real.pi))) * Complex.exp (-Complex.I * t * Real.log (p ^ 2)) +
         star (χ (p ^ 2)) * h_hat (Real.log (p ^ 2) / (2 * Real.pi)) * Complex.exp (Complex.I * t * Real.log (p ^ 2))).re

/-- Higher prime-power part `P^{(≥ 3)}_{θ,Δ}(t, χ)` (`n = p^m`, `m ≥ 3`). -/
def primeSumGe3 (q : ℕ) (χ : DirichletCharacter ℂ q) (h_hat : ℝ → ℂ) (X t : ℝ) : ℝ :=
  primePowerSum q χ h_hat X t - primeSum1 q χ h_hat X t - primeSum2 q χ h_hat X t

end PolarEvaluation
