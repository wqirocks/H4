import Sp4.Main

/-!
# Kernel dependency audit

These guarded `#print axioms` commands make the expected kernel dependency
boundary executable.  The four named literature arguments of the main theorem
are ordinary explicit parameters, so they do not appear in this list.  Apart
from Lean's standard quotient/classical principles, the top-level proof may use
exactly the seven generic results declared in `ExternalInputs.lean`.
-/

/--
info: 'Sp4.mainDegreeFourVanishing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Sp4.absolutelyContinuous_map_normalizedOpenGaussian_of_surjective_submersion,
 Sp4.exists_smoothFibreKernel_normalizedOpenGaussian_of_submersions,
 Sp4.measure_equivalent_haar_prod_of_left_quasiInvariant,
 Sp4.measure_zero_zeroSet_of_nontrivial_complex_analytic_piGaussian,
 Sp4.polishSpace_of_lcsc_topologicalGroup,
 Sp4.projectiveGaussian_linearEquiv_quasiMeasurePreserving,
 Sp4.quasiMeasurePreserving_normalizedOpenGaussian_of_submersion]
-/
#guard_msgs in
#print axioms Sp4.mainDegreeFourVanishing

/--
info: 'Sp4.Pfaffian.theta_not_mem_range_comparison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Sp4.quasiMeasurePreserving_normalizedOpenGaussian_of_submersion]
-/
#guard_msgs in
#print axioms Sp4.Pfaffian.theta_not_mem_range_comparison

/--
info: 'Sp4.ParabolicWeights.concreteLineParabolicWeightCertificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Sp4.ParabolicWeights.concreteLineParabolicWeightCertificate

/--
info: 'Sp4.MeasurableDoubleComplex.ShapiroNaturalityInterface.transgressionCohomologyInputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Sp4.MeasurableDoubleComplex.ShapiroNaturalityInterface.transgressionCohomologyInputs
