# External Axiom Register

All external axioms in `PolarEvaluation/ExternalResults.lean` represent established results from peer-reviewed mathematical literature that are not yet available in Mathlib. No manuscript-owned theorem, lemma, or corollary is axiomatized.

## E1: `horizontal_zero_sum_external`
- **Published Source:** H. Davenport, *Multiplicative Number Theory*, 3rd ed., Springer, 2000, Chapter 12; E. Carneiro, V. Chandee, and M. B. Milinovich, *Math. Ann.* 356 (2013), *Math. Z.* 281 (2015).
- **Content:** Hadamard factorization of the completed Dirichlet $L$-function and horizontal logarithmic representation of $\operatorname{Re}(e^{-i\theta}\log L(\frac{1}{2}+it,\chi))$ under GRH.
- **Dependent Declarations:** `horizontal_zero_sum`, `directional_envelope_bound`, `t_aspect_large_deviation`, `q_aspect_large_deviation`.

## E2: `guinand_weil_external`
- **Published Source:** E. Carneiro, V. Chandee, and M. B. Milinovich, *Bounding $S(t)$ and $S_1(t)$ on the Riemann hypothesis*, Math. Ann. 356 (2013), Lemma 5; *Math. Z.* 281 (2015).
- **Content:** Guinand–Weil explicit formula for primitive Dirichlet $L$-functions applied to bandlimited test functions of exponential type $2\pi\Delta$ with $O((1+x^2)^{-1})$ decay on $\R$.
- **Dependent Declarations:** `guinand_weil_bandlimited`, `directional_envelope_bound`, `t_aspect_large_deviation`, `q_aspect_large_deviation`.

## E3: `montgomery_vaughan_mvt`
- **Published Source:** H. L. Montgomery and R. C. Vaughan, *Hilbert's inequality*, J. London Math. Soc. (2) 8 (1974), 73–82.
- **Content:** Mean value theorem for Dirichlet polynomials $\int_T^{2T} |\sum_{n\le N} a_n n^{-it}|^2 dt \le (T + O(N))\sum_{n\le N} |a_n|^2$.
- **Dependent Declarations:** `prime_moment_t_aspect`.

## E4: `ccm_odd_extremal`
- **Published Source:** E. Carneiro, V. Chandee, and M. B. Milinovich, *Bounding $S(t)$ and $S_1(t)$ on the Riemann hypothesis*, Math. Ann. 356 (2013), 939–968.
- **Content:** Existence of the odd Beurling–Selberg majorant and minorant $M^\pm_{\pi/2,\Delta}$ for $K_{\pi/2}(x) = \arctan(1/x) - x/(x^2+1)$.
- **Dependent Declarations:** `S_large_deviation_t`.
