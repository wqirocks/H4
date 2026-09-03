# Sp(4, C) degree-four vanishing: Lean formalization report

Date: 2026-09-03

## Scope and outcome

The proof in `Sp4_Degree4_Vanishing_Word_Lifting_Patched.tex` has been
formalized against the obligations in
`Sp4_Degree4_Vanishing_Lean_Readiness_Specification.tex`.  Article-specific
algebra, measurable-coordinate arguments, dynamical estimates, period
obstructions, finite contractions, stabilizer calculations, and the
low-degree double-complex chase are kernel checked.  Earlier literature that
is not present in mathlib remains visible through precisely typed interfaces.

The final assembly proves, from those named literature inputs,

$$
H^4_{\mathrm{cb}}\bigl(\operatorname{Sp}(4,\mathbb C);\mathbb R\bigr)=0.
$$

No fatal mathematical gap in the article's original argument was found.

## Low-degree measurable resolution

The measurable projective double complex is implemented on actual $L^0$
almost-everywhere classes.  Horizontal deletion faces and the vertical Moore
differential commute face by face, and the horizontal rows are contracted by
Fubini.  The quotient-level cohomology data are converted into representative
coboundary witnesses, after which an explicit component chase constructs the
single surviving transgression

$$
\operatorname{Hom}_{\mathbb R}(\mathbb C,\mathbb R)
  \xrightarrow{\ \cong\ }
H^4_{\mathrm m}\bigl(
  \operatorname{Sp}(4,\mathbb C)\curvearrowright
  \mathbb P^3(\mathbb C);\mathbb R\bigr).
$$

The lift needed in this transgression is constructed internally from
next-column vanishing and projectivity; it is no longer an interface field.
Likewise, the source identification is constructed from Shapiro and the
explicit continuous-character calculation

$$
H^1_{\mathrm c}\bigl(
  \{\pm1\}\times(\mathbb C,+);\mathbb R\bigr)
  \cong \operatorname{Hom}_{\mathbb R}(\mathbb C,\mathbb R).
$$

## Stabilizers, face maps, and the parabolic calculation

Lean contains mutually inverse continuous group isomorphisms

$$
L\cong\mathbb C^\times\times\operatorname{SL}(2,\mathbb C),
\qquad
H\cong\{\pm1\}\times(\mathbb C,+).
$$

For all three deletion faces, the exact $\mathbb C^\times$ coordinate is a
sign or its inverse.  Therefore each pulled-back generator
$a\mapsto\log|a|$ is identically zero.  This is proved from matrices rather
than assumed as an alternating-sum conclusion.

The finite-stabilizer positive cohomology vanishing is proved using the
explicit homogeneous averaging homotopy

$$
ds+sd=\operatorname{id}.
$$

For the line-parabolic nilradical, the contact grading is represented as

$$
\mathfrak u=\mathfrak u_1\oplus\mathfrak u_2,
\qquad
\dim_{\mathbb C}\mathfrak u_1=2,
\quad
\dim_{\mathbb C}\mathfrak u_2=1,
\quad
[\mathfrak u_1,\mathfrak u_1]=\mathfrak u_2.
$$

The subgroup used here is proved to be the actual normal nilradical of the
line parabolic, not merely a subgroup lying inside it.  Lean constructs the
Levi embedding, proves it injective, and proves the unique matrix
factorization

$$
Q=U L
$$

together with normality of $U$ in $Q$.  Thus the semidirect-product hypothesis
fed to Hochschild--Serre is part of the kernel-checked certificate.

The split central element has weights $r,r,r^2$.  On the underlying real
dual the exponent list is $(1,1,1,1,2,2)$, so every basis vector in positive
exterior degree has eigenvalue $r^{-m}$ with $m>0$.  Lean constructs the
diagonal inverse of $T_r-1$ and combines it with the fully formalized central
prism

$$
dH+Hd=L_z^*-\operatorname{id}=T_z-\operatorname{id}.
$$

Only the existence/convergence and edge-map identification of the continuous
Hochschild--Serre spectral sequence remain a literature interface.

## Readiness-obligation traceability

The reverse audit against the final table of the readiness specification gives
the following coverage.  Each range below refers to the obligation IDs in that
table; the named files are the modules in which the corresponding definitions,
certificates, or assembly maps are checked.

| IDs | Kernel-checked implementation | External boundary, if any |
| --- | --- | --- |
| F1--F6 | `Symplectic/Model`, `Measure/Permutation`, `Measure/L0`, `Cohomology/MeasurableRows` | Generic analytic nullity is Mityagin/Federer.  The actual a.e. quotient, nonsingular pullback, contraction, and Fubini row exactness are internal.  The abstract Polish topology/exponential-law formulation used by Moore belongs to the Moore interface. |
| G1--G7 | `Symplectic/Gram`, `Symplectic/TwoFree`, `Measure/NaturalProjectiveOrbit`, `Measure/ProjectiveMeasureClass`, `Cohomology/NaturalProjectiveCoordinates` | Struble metrization, projective change of variables, and the generic Haar-class decomposition are the three visible older inputs used here. |
| P1--P5 | `Pfaffian/Coordinates`, `Pfaffian/Certificates`, `Chains/Normalized`, `Pfaffian/Operators`, `Cohomology/PfaffianComplex` | None beyond the generic nonsingularity theorem already listed under F. |
| A1--A3 | `Pfaffian/Permutation`, `Cohomology/CochainAlternation`, `Cohomology/FullAlternation`, `Cohomology/BoundedAlternation` | A3 is precisely the typed Burger--Monod interface. |
| D1--D3 | `Pfaffian/Certificates`, `Cohomology/AffineCocycle`, `Pfaffian/MeasurableRigidity` | None beyond the generic measure inputs under F/R. |
| W1--W9 | `Correspondence/Genericity`, `Correspondence/Word`, `Correspondence/ReturnScratch`, `Correspondence/Return` | None; the cover fibres, bad loci, word matrices, dyadic length bounds, compact return, and sharp bound are proved internally. |
| R1--R7 | `Symplectic/TwoFreeSubmersion`, `Measure/FibreKernel`, `Measure/FibreIntegration`, `Pfaffian/MeasurableRigidity`, `Cohomology/BoundedAlternation` | R3--R4 use the generic smooth fibre-integration input; R7 also consumes A3. |
| M1--M10 | `Measure/TranslationInvariant`, `Cohomology/MeasurableDoubleComplex`, `Cohomology/FiniteGroupContraction`, `Cohomology/Stabilizers`, `Cohomology/CentralPrism`, `Cohomology/ParabolicWeights`, `Cohomology/FirstPageFaces`, `Cohomology/DoubleComplex`, `Cohomology/MeasurableResolution` | M3 and the cited Shapiro/van Est/Hochschild--Serre portions of M4/M9 are explicit fields of the literature interface.  The representative chase, all face maps, finite contraction, parabolic factorization/weights, and single transgression are internal. |
| C1--C4 | `Cohomology/AffineCocycle`, `Cohomology/AffineCocycleCombinatorics`, `Cohomology/AffineCocycleIdentity` | None. |
| O1--O3 | `Chains/Orbit`, `Chains/Orientation`, `Chains/Presentation` | None. |
| S1--S7 | `Chains/Measure`, `Chains/FacePairing`, `Chains/TwoCone`, `Chains/ParametricTwoCone`, `Chains/Diffusion` | Only the generic submersion/change-of-measure inputs already listed under F/R. |
| Q1--Q6 | `Pfaffian/Certificates`, `Period/Pole`, `Cohomology/NoBoundedRepresentative` | None beyond the generic submersion input needed for the measurable period comparison. |
| E1--E6 | `Cohomology/ActionVanishing`, `Cohomology/GroupVanishing`, `Main` | E1 and E2 are the typed rank-one and Blatz inputs.  E3--E6 are internal assembly theorems. |

Thus all article-specific `CORE` and `CERTIFICATE` obligations remain on the
kernel-checked side of the boundary.  No such obligation is represented by an
axiom or by a field that merely repeats its desired conclusion.

## Explicit external boundary

The high-level theorem takes visible inputs for:

1. Burger--Monod bounded alternation (GAFA 12 (2002), Section 1.7 and
   Corollary 2.3.2).
2. Moore measurable cohomology and Eckmann--Shapiro (Trans. AMS 221 (1976),
   Theorems 2 and 6), Austin--Moore comparison (Math. Ann. 356 (2013),
   Theorem A), van Est naturality, and the continuous Hochschild--Serre edge
   theorem (Hochschild--Mostow, Illinois J. Math. 6 (1962), 367--401;
   Borel--Wallach, Chapter II).  The compact-dual degree calculations and
   the isomorphism induced by
   $\operatorname{Sp}(1)\hookrightarrow\operatorname{Sp}(2)$ use
   Mimura--Toda, *Topology of Lie Groups, I and II*, AMS, 1991.
3. Blatz's projective-action kernel identification (doctoral dissertation,
   2026, Lemma 6.2.8, DOI 10.5445/IR/1000194533).
4. Rank-one vanishing, obtained in the article from Bucher--Savini,
   arXiv:2510.05333, Theorem 5, compact-dual cohomology, and finite-central
   invariance.

There are exactly seven project-level Lean `axiom` declarations, all generic
and all in `Sp4/Cohomology/ExternalInputs.lean`:

1. Struble's Polish metrization theorem for second-countable locally compact
   groups (Compositio Math. 28 (1974), main theorem).
2. Mityagin's nullity theorem for a nontrivial real-analytic zero set
   (Mathematical Notes 107 (2020), Proposition 0; arXiv:1512.07276).
3. The null-preimage consequence of Federer's coarea theorem for submersions
   (*Geometric Measure Theory*, Theorem 3.2.22).
4. The reverse absolute-continuity consequence for a surjective submersion
   (the same coarea theorem plus the submersion normal form).
5. Projective change of variables for invertible complex-linear maps (the
   equal-dimensional area formula in projective affine charts).
6. Haar-product measure-class decomposition along a free group coordinate
   (Bourbaki, *Integration II*, Chapter VII, §2, no. 5, Theorem 1, plus
   Tonelli).
7. Properly supported smooth fibre integration, based on smooth partitions of
   unity and pushforward of densities (Lee, Theorem 2.23; Jago,
   Proposition 1.5.3).

None states an article-specific Pfaffian identity, boundedness theorem,
cohomology dimension, or final vanishing conclusion.

## Verification

- Lean and mathlib: `v4.33.1`.
- `scripts/check-formalization`: exit code 0.
- Complete build graph: 8781 jobs, successful.
- `AxiomAudit.lean`: guarded `#print axioms` expectations passed for the main
  theorem and three proof-specific boundary declarations.
- `Scratch.lean`: compiled successfully.
- No `sorry`, `admit`, `native_decide`, or `unsafe` occurs in a Lean source
  file.
- No Lean `axiom` declaration occurs outside
  `Sp4/Cohomology/ExternalInputs.lean`.
- The seven declarations in that file match an exact name-and-order allowlist;
  any addition, removal, rename, or reordering makes the checker fail.
- The top-level declarations are in `Sp4/Main.lean`, including
  `ordinaryProjectiveActionH4Equiv`, `boundedProjectiveActionH4_vanishes`,
  `pfaffianDegreeFour_exact`, `pfaffianDegreeFour_primitive`, and
  `mainDegreeFourVanishing`.
