import Sp4.Symplectic.Model
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Algebra.Group.Units

/-!
# The natural lcsc topology on the linear symplectic group

The algebraic model `Sp4.SymplecticGroup` is a subgroup of complex linear
equivalences.  This file equips it with its matrix/operator-norm topology,
without postulating any Lie-group structure.  We embed it into the unit group
of the finite-dimensional algebra of continuous linear endomorphisms.  Its
image is the closed locus preserving `omega`; local compactness and second
countability then follow from standard mathlib topology.
-/

namespace Sp4

noncomputable section

/-- The quotient measurable structure on complex projective three-space, induced
from the Borel structure on nonzero vectors. -/
instance : MeasurableSpace ProjectivePoint := by
  exact Quotient.instMeasurableSpace

/-- A subset of projective space is measurable exactly when its pullback to
the nonzero-vector quotient presentation is measurable. -/
theorem measurableSet_projective_iff {s : Set ProjectivePoint} :
    MeasurableSet s ↔
      MeasurableSet
        ((fun v : {v : SymplecticVector // v ≠ 0} =>
          Projectivization.mk' ℂ v) ⁻¹' s) := by
  change MeasurableSet s ↔
    MeasurableSet (Quotient.mk'' ⁻¹' s)
  exact measurableSet_quotient

/-- Measurability out of projective space can be checked before passing to
the nonzero-vector quotient. -/
theorem measurable_from_projective {Y : Type*} [MeasurableSpace Y]
    {f : ProjectivePoint → Y} :
    Measurable f ↔ Measurable
      (f ∘ fun v : {v : SymplecticVector // v ≠ 0} =>
        Projectivization.mk' ℂ v) := by
  change Measurable f ↔ Measurable (f ∘ Quotient.mk'')
  exact measurable_from_quotient

/-- Projectivizing a measurable family of nonzero vectors is measurable for
the natural quotient measurable structure on projective space. -/
theorem measurable_projectivization_mk {A : Type*} [MeasurableSpace A]
    (f : A → SymplecticVector) (hf : Measurable f)
    (hne : ∀ a, f a ≠ 0) :
    Measurable (fun a => Projectivization.mk ℂ (f a) (hne a)) := by
  change Measurable (fun a => Quotient.mk''
    (⟨f a, hne a⟩ : {v : SymplecticVector // v ≠ 0}))
  exact measurable_quotient_mk''.comp hf.subtype_mk

/-- A symplectic linear equivalence, regarded as a continuous linear
equivalence. -/
def symplecticContinuousEquiv (g : SymplecticGroup) :
    SymplecticVector ≃L[ℂ] SymplecticVector :=
  g.1.toContinuousLinearEquiv

/-- The operator associated with a symplectic map, bundled as a unit of the
endomorphism algebra. -/
def symplecticOperatorUnit (g : SymplecticGroup) :
    (SymplecticVector →L[ℂ] SymplecticVector)ˣ :=
  (ContinuousLinearEquiv.unitsEquiv ℂ SymplecticVector).symm
    (symplecticContinuousEquiv g)

@[simp]
theorem symplecticOperatorUnit_val (g : SymplecticGroup) :
    (symplecticOperatorUnit g :
      SymplecticVector →L[ℂ] SymplecticVector) =
        (symplecticContinuousEquiv g).toContinuousLinearMap := by
  rfl

theorem symplecticOperatorUnit_injective :
    Function.Injective symplecticOperatorUnit := by
  intro g h hgh
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  exact congrArg
    (fun u : (SymplecticVector →L[ℂ] SymplecticVector)ˣ =>
      (u : SymplecticVector →L[ℂ] SymplecticVector) v) hgh

/-- The operator embedding is a group homomorphism. -/
def symplecticOperatorHom :
    SymplecticGroup →* (SymplecticVector →L[ℂ] SymplecticVector)ˣ where
  toFun := symplecticOperatorUnit
  map_one' := by
    apply Units.ext
    apply ContinuousLinearMap.ext
    intro v
    rfl
  map_mul' g h := by
    apply Units.ext
    apply ContinuousLinearMap.ext
    intro v
    rfl

/-- The closed locus of continuous linear maps preserving the fixed
symplectic form. -/
def PreservesOmega : Set (SymplecticVector →L[ℂ] SymplecticVector) :=
  {f | ∀ v w, omega (f v) (f w) = omega v w}

theorem preservesOmega_isClosed : IsClosed PreservesOmega := by
  rw [show PreservesOmega = ⋂ v, ⋂ w,
      {f | omega (f v) (f w) = omega v w} by
    ext f
    simp [PreservesOmega]]
  apply isClosed_iInter
  intro v
  apply isClosed_iInter
  intro w
  apply isClosed_eq
  · have h : Continuous
        (fun f : SymplecticVector →L[ℂ] SymplecticVector =>
          (f v) 0 * (f w) 1 - (f v) 1 * (f w) 0 +
            (f v) 2 * (f w) 3 - (f v) 3 * (f w) 2) := by
      fun_prop
    simpa only [omega_apply] using h
  · exact continuous_const

theorem range_symplecticOperatorUnit :
    Set.range symplecticOperatorUnit = Units.val ⁻¹' PreservesOmega := by
  ext u
  constructor
  · rintro ⟨g, rfl⟩
    exact g.2
  · intro hu
    let e : SymplecticVector ≃L[ℂ] SymplecticVector :=
      ContinuousLinearEquiv.unitsEquiv ℂ SymplecticVector u
    let g : SymplecticGroup := ⟨e.toLinearEquiv, hu⟩
    refine ⟨g, ?_⟩
    apply Units.ext
    apply ContinuousLinearMap.ext
    intro v
    rfl

theorem range_symplecticOperatorUnit_isClosed :
    IsClosed (Set.range symplecticOperatorUnit) := by
  rw [range_symplecticOperatorUnit]
  exact preservesOmega_isClosed.preimage Units.continuous_val

/- The topology on units is induced by the embedding into the product of an
operator and its inverse.  The target is second countable because the
endomorphism algebra is finite dimensional. -/
instance : SecondCountableTopology
    ((SymplecticVector →L[ℂ] SymplecticVector)ˣ) :=
  TopologicalSpace.secondCountableTopology_induced _ _
    (Units.embedProduct (SymplecticVector →L[ℂ] SymplecticVector))

/- The opposite endomorphism algebra is homeomorphic to the original Polish
space.  Consequently the unit group, which is a closed subspace of the
product of an operator and its inverse, is Polish as well. -/
instance : PolishSpace
    (SymplecticVector →L[ℂ] SymplecticVector)ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.isClosedEmbedding.polishSpace

instance : PolishSpace
    ((SymplecticVector →L[ℂ] SymplecticVector)ˣ) :=
  Units.isClosedEmbedding_embedProduct.polishSpace

/-- The usual operator topology on `Sp(4,ℂ)`. -/
instance : TopologicalSpace SymplecticGroup :=
  TopologicalSpace.induced symplecticOperatorUnit inferInstance

theorem symplecticOperatorUnit_isClosedEmbedding :
    Topology.IsClosedEmbedding symplecticOperatorUnit :=
  ⟨symplecticOperatorUnit_injective.isEmbedding_induced,
    range_symplecticOperatorUnit_isClosed⟩

instance : PolishSpace SymplecticGroup :=
  symplecticOperatorUnit_isClosedEmbedding.polishSpace

instance : LocallyCompactSpace SymplecticGroup :=
  symplecticOperatorUnit_isClosedEmbedding.locallyCompactSpace

instance : T2Space SymplecticGroup :=
  symplecticOperatorUnit_isClosedEmbedding.toIsEmbedding.t2Space

instance : SecondCountableTopology SymplecticGroup :=
  TopologicalSpace.secondCountableTopology_induced _ _
    symplecticOperatorUnit

/-- Multiplication and inversion are continuous in the operator topology. -/
instance : IsTopologicalGroup SymplecticGroup where
  continuous_mul := by
    rw [continuous_induced_rng]
    change Continuous (fun p : SymplecticGroup × SymplecticGroup =>
      symplecticOperatorUnit (p.1 * p.2))
    rw [show (fun p : SymplecticGroup × SymplecticGroup =>
        symplecticOperatorUnit (p.1 * p.2)) =
        fun p => symplecticOperatorUnit p.1 *
          symplecticOperatorUnit p.2 by
      funext p
      exact symplecticOperatorHom.map_mul p.1 p.2]
    fun_prop
  continuous_inv := by
    rw [continuous_induced_rng]
    change Continuous
      (fun g : SymplecticGroup => symplecticOperatorUnit g⁻¹)
    rw [show (fun g : SymplecticGroup => symplecticOperatorUnit g⁻¹) =
        fun g => (symplecticOperatorUnit g)⁻¹ by
      funext g
      exact symplecticOperatorHom.map_inv g]
    fun_prop

/-- The Borel measurable structure belonging to the operator topology. -/
instance : MeasurableSpace SymplecticGroup := borel _

instance : BorelSpace SymplecticGroup := ⟨rfl⟩

end

end Sp4
