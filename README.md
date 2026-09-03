# Sp4 degree-four vanishing formalization

This workspace contains a Lean formalization of
`Sp4_Degree4_Vanishing_Word_Lifting_Patched.tex`, using
`Sp4_Degree4_Vanishing_Lean_Readiness_Specification.tex` as the formalization
specification.

## Pinned environment

- Lean: `v4.33.1`
- mathlib: tag `v4.33.1`
- mathlib commit: `0df444a360eaa60ab8c11dca51a86af692955474`

Run the environment check with:

```bash
scripts/check-formalization
```

The checker builds the complete import graph and the standalone scratch file;
runs guarded `#print axioms` checks on the top-level and proof-specific
declarations; rejects every `sorry`, `admit`,
`native_decide`, and `unsafe` declaration; rejects `axiom` declarations outside
the dedicated literature-interface module; and enforces the exact seven-name
allowlist recorded below.

## Main results

`Sp4/Main.lean` exposes:

- `ordinaryProjectiveActionH4Equiv`, the affine-cocycle description of ordinary
  measurable degree-four action cohomology;
- `boundedProjectiveActionH4_vanishes`;
- `pfaffianDegreeFour_exact` and its elementwise primitive form;
- `mainDegreeFourVanishing`, for the explicitly defined homogeneous continuous
  bounded cohomology of the standard matrix group `Sp(4, ℂ)`.

The standard block inclusion `SL(2, ℂ) → Sp(4, ℂ)`, cochain restriction,
the induced map on `H_cb^4`, and the final kernel argument are all defined and
checked in Lean.

## Formalization boundary

- The proof-specific `CORE` and finite `CERTIFICATE` obligations in the
  readiness specification must be checked by Lean and must not be replaced by
  axioms merely because they are difficult.
- Reusable infrastructure is developed locally or isolated behind a precisely
  typed interface when mathlib has no suitable theorem.
- Kernel-level external declarations are confined to
  `Sp4/Cohomology/ExternalInputs.lean`.  Higher cohomological literature
  results are visible typed arguments next to the concrete quotient types on
  which they act; each such interface records its source and the exact
  naturality or equivalence consumed downstream.
- The final assembly must depend only on named module theorems and external
  interfaces; it must contain no hidden matrix, measure, compactness, or
  spectral-sequence argument.

The remaining hypotheses of the main theorem are named, typed literature
interfaces for Burger--Monod alternation, the Moore/Austin--Moore/van Est
measurable resolution, Blatz's kernel identification, and rank-one vanishing.
They are visible arguments of the assembly theorem rather than hidden project
axioms.

The project-specific parts of the parabolic calculation are checked in
`Sp4/Cohomology/CentralPrism.lean` and
`Sp4/Cohomology/ParabolicWeights.lean`: these include the full prism identity,
the concrete unique factorization of the line parabolic as Heisenberg
nilradical times Levi, normality of that nilradical, the contact bracket, the
Levi weights, and invertibility in every positive exterior degree.  Only the
continuous Hochschild--Serre spectral sequence and its edge-map identification
remain in the literature interface (Hochschild--Mostow, *Illinois J. Math.* 6
(1962), 367--401; Borel--Wallach, Chapter II).

The only seven Lean `axiom` declarations are generic results from earlier
literature, all isolated in `Sp4/Cohomology/ExternalInputs.lean`:

1. Struble's Polish metrization theorem for second-countable locally compact
   groups.
2. Mityagin's analytic zero-set theorem in Gaussian coordinates.
3. The null-preimage consequence of Federer's coarea theorem for submersions.
4. The reverse absolute-continuity consequence for surjective submersions.
5. Projective change of variables for an invertible complex-linear map.
6. Haar-product measure-class decomposition in a free product coordinate.
7. Smooth properly supported fibre integration from partitions of unity and
   pushforward of densities.

None has an article-specific Pfaffian, boundedness, cohomology, or vanishing
conclusion.
