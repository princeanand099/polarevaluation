import Mathlib

/-!
# Foundational Definitions for the Polar Envelope and Large Deviations of `log L(1/2 + it, χ)`

This module defines the analytic conductor, the Fourier transform `fourierHat`,
the mixed logarithmic-argument kernel `K_θ`, the directional envelope constant `C(θ)`,
the universal convex domain `Ω`, the rescaled kernel `F_{θ,Δ}`, the shifted-lattice
Vaaler Hermite interpolant `M_α`, and the limiting integral `J(y, θ)`.
-/

noncomputable section

open Real Complex MeasureTheory

namespace PolarEvaluation

/-- Fourier transform `f̂(ξ) := ∫ f(x) exp(-2π i ξ x) dx`. -/
def fourierHat (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ x : ℝ, f x * Complex.exp (-2 * Real.pi * Complex.I * ξ * x)

/-- Analytic conductor `q(|t| + 2)` for a character modulo `q` at height `t`. -/
def analyticConductor (q : ℕ) (t : ℝ) : ℝ :=
  (q : ℝ) * (|t| + 2)

/-- The asymmetric mixed logarithmic-argument kernel `K_θ(x)` for `x ∈ ℝ \ {0}`. -/
def kernelK (θ x : ℝ) : ℝ :=
  -(Real.cos θ / 2) * Real.log ((x ^ 2 + 1) / x ^ 2) +
    Real.sin θ * (Real.arctan (1 / x) - x / (x ^ 2 + 1))

/-- The sharp directional envelope constant `C(θ) = (1/2) * (cos θ * log(2 cos θ) + θ sin θ)`. -/
def envelopeC (θ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (Real.cos θ * Real.log (2 * Real.cos θ) + θ * Real.sin θ)

/-- The universal convex domain `Ω = {x + iy ∈ ℂ : |y| < π/4, exp(2x) ≤ 2 cos(2y)}`. -/
def convexOmega : Set ℂ :=
  {z : ℂ | |z.im| < Real.pi / 4 ∧ Real.exp (2 * z.re) ≤ 2 * Real.cos (2 * z.im)}

/-- Rescaled kernel `F_{θ,Δ}(y) = K_θ(y / Δ)`. -/
def rescaledF (θ Δ y : ℝ) : ℝ :=
  kernelK θ (y / Δ)

/-- Derivative `F'_{θ,Δ}(y)` for `y ≠ 0`. -/
def rescaledFDeriv (θ Δ y : ℝ) : ℝ :=
  Real.cos θ * (1 / y - y / (y ^ 2 + Δ ^ 2)) -
    Real.sin θ * (2 * Δ ^ 3 / (y ^ 2 + Δ ^ 2) ^ 2)

/-- Entire function `M : ℂ → ℂ` has exponential type at most `T`. -/
def HasExponentialType (M : ℂ → ℂ) (T : ℝ) : Prop :=
  Differentiable ℂ M ∧
    ∀ ε > 0, ∃ C > 0, ∀ z : ℂ, ‖M z‖ ≤ C * Real.exp ((T + ε) * ‖z‖)

/-- Formal Vaaler Hermite interpolant `M_α(y)` of `F_{θ,Δ}` on `ℤ + α`. -/
def vaalerInterpolant (θ Δ α : ℝ) (y : ℝ) : ℝ :=
  (Real.sin (Real.pi * (y - α)) ^ 2 / Real.pi ^ 2) *
    ∑' n : ℤ,
      (rescaledF θ Δ (n + α) / (y - (n : ℝ) - α) ^ 2 +
        rescaledFDeriv θ Δ (n + α) / (y - (n : ℝ) - α))

/-- Rescaled Vaaler majorant `M_{θ,Δ}(x) = M_{α_Δ}(Δ x)`. -/
def majorantM (θ Δ α_Δ x : ℝ) : ℝ :=
  vaalerInterpolant θ Δ α_Δ (Δ * x)

/-- Limiting integral `J(y, θ)` for `y ∈ ℝ \ {0}`. -/
def limitingJ (y θ : ℝ) : ℝ :=
  ∫ v in Set.Ioi (0 : ℝ),
    (Complex.exp (-Complex.I * θ) /
      (Complex.cos (θ + Complex.I * Real.pi * v) ^ 2 * (y - Complex.I * v))).im

/-- Abstract interface for primitive Dirichlet `L`-functions and their zeros/arguments. -/
structure LFunctionData where
  L : (q : ℕ) → DirichletCharacter ℂ q → ℂ → ℂ
  S : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℝ
  zeros : (q : ℕ) → DirichletCharacter ℂ q → Set ℝ
  GRH : ∀ q ≥ 1, ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → Prop

end PolarEvaluation
