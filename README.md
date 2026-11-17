# Polar Evaluation: Lean 4 Formalization

Lean 4 + Mathlib formalization of *The Polar Envelope and Large Deviations of $\log L(\frac{1}{2}+it,\chi)$ on the Generalized Riemann Hypothesis* by Prince Anand.

## Build Instructions
```bash
lake build
```

## Module Organization
- `PolarEvaluation/Basic.lean`: Core definitions (`analyticConductor`, `kernelK`, `envelopeC`, `convexOmega`, `vaalerInterpolant`, `limitingJ`, `LFunctionData`).
- `PolarEvaluation/ExternalResults.lean`: Strictly governed external axioms (documented in `EXTERNAL_AXIOMS.md`).
- `PolarEvaluation/ExplicitFormulae.lean`: Horizontal representation, Guinand–Weil explicit formula, and Fourier decay of $K_\theta$.
- `PolarEvaluation/ShiftedLattice.lean`: Shifted-lattice Vaaler interpolant, contour representation, Plancherel positivity, and Theorem 1.7.
- `PolarEvaluation/PointwiseEnvelope.lean`: Pointwise directional envelope, convex domain $\Omega$, and modulus–argument trade-off.
- `PolarEvaluation/PrimeMoments.lean`: Prime-power tail and $2k$-th moment bounds in $t$- and $q$-aspects.
- `PolarEvaluation/LargeDeviations.lean`: Exponential large-deviation bounds in $t$- and $q$-aspects and for $|S(t,\chi)|$.

## Supporting Records
- `CORRESPONDENCE.md`: Manuscript-to-Lean correspondence table.
- `EXTERNAL_AXIOMS.md`: External axiom register.
- `CORRECTIONS_AUDIT.md`: Mathematical correction audit record.
- `PROGRESS.md`: Continuous formalization progress tracker.
