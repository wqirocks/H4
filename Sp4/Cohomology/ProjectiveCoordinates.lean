import Sp4.Pfaffian.Permutation
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Projective-action cochains in normalized Pfaffian coordinates

This file proves the set-theoretic part of the Lebesgue-coordinate theorem.
For four, five, and six generic projective points, normalized Gram coordinates
classify `Sp(4,ℂ)`-orbits.  Consequently real functions on the corresponding
Pfaffian chart are linearly equivalent to invariant functions on generic
projective configurations.  The equivalences are proved to commute with the
homogeneous coboundary.

No measurable quotient or almost-everywhere representative is used here.
-/

namespace Sp4
namespace ProjectiveAction

noncomputable section

open scoped BigOperators
open OrbitChain Pfaffian

/-- Pointwise invariant real functions on generic `n`-configurations. -/
def InvariantCochains (n : ℕ) :
    Submodule ℝ (GenericConfig n → ℝ) where
  carrier f := ∀ g : SymplecticGroup, ∀ x,
    f (smulGeneric g x) = f x
  zero_mem' := fun _ _ ↦ rfl
  add_mem' := by
    intro f h hf hh
    exact fun g x ↦ by
      change f (smulGeneric g x) + h (smulGeneric g x) = f x + h x
      rw [hf g x, hh g x]
  smul_mem' := by
    intro c f hf
    exact fun g x ↦ by
      change c * f (smulGeneric g x) = c * f x
      rw [hf g x]

theorem mem_invariantCochains {n : ℕ} (f : GenericConfig n → ℝ) :
    f ∈ InvariantCochains n ↔
      ∀ g : SymplecticGroup, ∀ x, f (smulGeneric g x) = f x :=
  Iff.rfl

theorem invariant_apply {n : ℕ} (f : InvariantCochains n)
    (g : SymplecticGroup) (x : GenericConfig n) :
    f.1 (smulGeneric g x) = f.1 x := by
  exact (mem_invariantCochains f.1).1 f.2 g x

/-- A symplectic transformation fixing a generic configuration with at least
four vertices is central.  This is the freeness calculation for the effective
projective action: the four selected lifts form a basis, and preservation of
their six nonzero pairings forces all four projective eigenvalues to be the
same sign. -/
theorem generic_stabilizer {n : ℕ} (g : SymplecticGroup)
    (x : GenericConfig (4 + n)) (hg : smulGeneric g x = x) :
    g = 1 ∨ g = centralNeg := by
  let u := canonicalProjectiveLift x.1
  let e : Fin 4 → Fin (4 + n) := Fin.castAdd n
  have he : Function.Injective e := Fin.castAdd_injective 4 n
  let b := u.selectedBasis x.2 e he
  have hline (i : Fin 4) : g.1 • x.1 (e i) = x.1 (e i) := by
    exact congrFun (congrArg Subtype.val hg) (e i)
  have hscalar : ∀ i : Fin 4, ∃ c : ℂ,
      g.1 (u.vec (e i)) = c • u.vec (e i) := by
    intro i
    have hi := hline i
    rw [← u.projectivizes (e i), Projectivization.smul_mk,
      Projectivization.mk_eq_mk_iff'] at hi
    obtain ⟨c, hc⟩ := hi
    exact ⟨c, hc.symm⟩
  choose c hc using hscalar
  have hcne (i : Fin 4) : c i ≠ 0 := by
    intro hzero
    have hgu : g.1 (u.vec (e i)) = 0 := by simp [hc i, hzero]
    exact u.ne_zero (e i)
      (g.1.injective (hgu.trans (map_zero g.1).symm))
  have hpair (i j : Fin 4) (hij : i ≠ j) : c i * c j = 1 := by
    have hp := g.2 (u.vec (e i)) (u.vec (e j))
    rw [hc i, hc j] at hp
    simp only [map_smul] at hp
    have ht := x.2.pairwise_transverse (e i) (e j) (he.ne hij)
    have homega : omega (u.vec (e i)) (u.vec (e j)) ≠ 0 := by
      rw [← u.projectivizes (e i), ← u.projectivizes (e j),
        transverse_mk_iff] at ht
      exact ht
    apply mul_right_cancel₀ homega
    simpa [mul_assoc, mul_comm, mul_left_comm] using hp
  have hc01 := hpair 0 1 (by decide)
  have hc02 := hpair 0 2 (by decide)
  have hc03 := hpair 0 3 (by decide)
  have hc12 := hpair 1 2 (by decide)
  have hc10 : c 1 = c 0 := by
    apply mul_right_cancel₀ (hcne 2)
    exact hc12.trans hc02.symm
  have hc20 : c 2 = c 0 := by
    have h21 : c 2 = c 1 := by
      apply mul_left_cancel₀ (hcne 0)
      exact hc02.trans hc01.symm
    exact h21.trans hc10
  have hc30 : c 3 = c 0 := by
    have h31 : c 3 = c 1 := by
      apply mul_left_cancel₀ (hcne 0)
      exact hc03.trans hc01.symm
    exact h31.trans hc10
  have hc_eq (i : Fin 4) : c i = c 0 := by
    fin_cases i
    · rfl
    · exact hc10
    · exact hc20
    · exact hc30
  have hmap : g.1.toLinearMap = c 0 • LinearMap.id := by
    apply LinearMap.ext_on (Module.Basis.span_eq b)
    intro v hv
    obtain ⟨i, rfl⟩ := hv
    rw [show b i = u.vec (e i) by simp [b]]
    simp [hc i, hc_eq i]
  apply (symplectic_fixes_projective_iff g).1
  intro p
  induction p using Projectivization.ind with
  | h v hv =>
      change g.1 • Projectivization.mk ℂ v hv =
        Projectivization.mk ℂ v hv
      rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
      refine ⟨c 0, ?_⟩
      have hvmap := LinearMap.congr_fun hmap v
      simpa using hvmap.symm

/-! ## The effective projective symplectic group -/

/-- The kernel of the action of `Sp(4,ℂ)` on projective space. -/
noncomputable def projectiveKernel : Subgroup SymplecticGroup :=
  (MulAction.toPermHom SymplecticGroup ProjectivePoint).ker

noncomputable instance : projectiveKernel.Normal := by
  dsimp [projectiveKernel]
  infer_instance

theorem mem_projectiveKernel_iff (g : SymplecticGroup) :
    g ∈ projectiveKernel ↔ ∀ p : ProjectivePoint, g • p = p := by
  constructor
  · intro hg p
    have h := congrArg (fun e : Equiv.Perm ProjectivePoint => e p)
      (MonoidHom.mem_ker.mp hg)
    simpa using h
  · intro hg
    rw [projectiveKernel, MonoidHom.mem_ker]
    ext p
    simpa using hg p

/-- The projective kernel is precisely the two-element centre `{1,-1}`. -/
theorem projectiveKernel_eq :
    projectiveKernel = {g | g = 1 ∨ g = centralNeg} := by
  ext g
  change g ∈ projectiveKernel ↔ g = 1 ∨ g = centralNeg
  exact (mem_projectiveKernel_iff g).trans
    (symplectic_fixes_projective_iff g)

/-- The effective projective symplectic group `PSp(4,ℂ)`. -/
abbrev EffectiveSymplecticGroup := SymplecticGroup ⧸ projectiveKernel

/-- The faithful action of `PSp(4,ℂ)` on generic configurations. -/
noncomputable def effectiveActionHom (n : ℕ) :
    EffectiveSymplecticGroup →* Equiv.Perm (GenericConfig n) :=
  QuotientGroup.lift projectiveKernel
    (MulAction.toPermHom SymplecticGroup (GenericConfig n)) (by
      intro g hg
      apply Equiv.ext
      intro x
      change smulGeneric g x = x
      apply Subtype.ext
      funext i
      exact (mem_projectiveKernel_iff g).1 hg (x.1 i))

noncomputable instance effectiveMulAction (n : ℕ) :
    MulAction EffectiveSymplecticGroup (GenericConfig n) :=
  MulAction.compHom (GenericConfig n) (effectiveActionHom n)

@[simp]
theorem quotient_smul_generic (g : SymplecticGroup)
    {n : ℕ} (x : GenericConfig n) :
    (g : EffectiveSymplecticGroup) • x = smulGeneric g x := by
  rfl

/-- The effective action on a generic configuration of at least four points
is free. -/
theorem effective_action_free {n : ℕ} (g : EffectiveSymplecticGroup)
    (x : GenericConfig (4 + n))
    (hg : effectiveActionHom (4 + n) g x = x) : g = 1 := by
  induction g using Quotient.inductionOn' with
  | _ g =>
      change smulGeneric g x = x at hg
      rcases generic_stabilizer g x hg with h | h
      · subst g
        rfl
      · subst g
        apply QuotientGroup.eq.mpr
        have hz : centralNeg ∈ projectiveKernel :=
          (mem_projectiveKernel_iff centralNeg).2
            centralNeg_smul_projective
        simpa using hz

/-- Data exhibiting a concrete slice for every pointwise symplectic orbit. -/
structure OrbitChart (n : ℕ) (U : Type*) where
  coordinate : GenericConfig n → U
  slice : U → GenericConfig n
  coordinate_slice : ∀ q, coordinate (slice q) = q
  coordinate_invariant : ∀ g x, coordinate (smulGeneric g x) = coordinate x
  representative : ∀ x, ∃ g : SymplecticGroup,
    smulGeneric g (slice (coordinate x)) = x

/-- The action map from the effective group times a normalized slice. -/
def OrbitChart.productParam {n : ℕ} {U : Type*} (C : OrbitChart n U) :
    EffectiveSymplecticGroup × U → GenericConfig n :=
  fun p ↦ p.1 • C.slice p.2

@[simp]
theorem OrbitChart.coordinate_productParam {n : ℕ} {U : Type*}
    (C : OrbitChart n U) (a : EffectiveSymplecticGroup) (q : U) :
    C.coordinate (C.productParam (a, q)) = q := by
  induction a using Quotient.inductionOn' with
  | _ g =>
      change C.coordinate (smulGeneric g (C.slice q)) = q
      rw [C.coordinate_invariant, C.coordinate_slice]

theorem OrbitChart.productParam_surjective {n : ℕ} {U : Type*}
    (C : OrbitChart n U) : Function.Surjective C.productParam := by
  intro x
  obtain ⟨g, hg⟩ := C.representative x
  refine ⟨((g : EffectiveSymplecticGroup), C.coordinate x), ?_⟩
  simpa [OrbitChart.productParam] using hg

/-- For generic configurations with at least four points, the effective group
and the normalized orbit coordinate give unique global parameters. -/
theorem OrbitChart.productParam_injective {k : ℕ} {U : Type*}
    (C : OrbitChart (4 + k) U) : Function.Injective C.productParam := by
  rintro ⟨a, q⟩ ⟨b, r⟩ h
  have hqr : q = r := by
    have hc := congrArg C.coordinate h
    simpa using hc
  subst r
  change a • C.slice q = b • C.slice q at h
  have hfix : (a⁻¹ * b) • C.slice q = C.slice q := by
    rw [mul_smul, ← h, inv_smul_smul]
  have hab : a⁻¹ * b = 1 := effective_action_free (a⁻¹ * b)
    (C.slice q) hfix
  apply Prod.ext
  · exact inv_mul_eq_one.mp hab
  · rfl

/-- Global set-theoretic product coordinates on the generic configuration
space.  No choice of local sections remains in this equivalence. -/
noncomputable def OrbitChart.productEquiv {k : ℕ} {U : Type*}
    (C : OrbitChart (4 + k) U) :
    EffectiveSymplecticGroup × U ≃ GenericConfig (4 + k) :=
  Equiv.ofBijective C.productParam
    ⟨C.productParam_injective, C.productParam_surjective⟩

/-- Pullback along an orbit chart identifies functions on the slice with
pointwise invariant functions on the generic configuration space. -/
def OrbitChart.functionLinearEquiv {n : ℕ} {U : Type*}
    (C : OrbitChart n U) :
    (U → ℝ) ≃ₗ[ℝ] InvariantCochains n where
  toFun f := ⟨fun x ↦ f (C.coordinate x),
    (mem_invariantCochains _).2 fun g x ↦ by
      change f (C.coordinate (smulGeneric g x)) = f (C.coordinate x)
      rw [C.coordinate_invariant g x]⟩
  invFun F := fun q ↦ F.1 (C.slice q)
  left_inv f := by
    funext q
    change f (C.coordinate (C.slice q)) = f q
    rw [C.coordinate_slice]
  right_inv F := by
    apply Subtype.ext
    funext x
    obtain ⟨g, hg⟩ := C.representative x
    have hinv := invariant_apply F g (C.slice (C.coordinate x))
    rw [hg] at hinv
    exact hinv.symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The four-point normalized Gram slice. -/
def orbitChart4 : OrbitChart 4 U4 where
  coordinate := orbitCoord4
  slice := normalizedConfig4
  coordinate_slice := orbitCoord4_normalizedConfig4
  coordinate_invariant := orbitCoord4_smulGeneric
  representative := exists_smul_normalizedConfig4_orbitCoord4

/-- The five-point normalized Gram slice. -/
def orbitChart5 : OrbitChart 5 U5 where
  coordinate := orbitCoord5
  slice := normalizedConfig5
  coordinate_slice := orbitCoord5_normalizedConfig5
  coordinate_invariant := orbitCoord5_smulGeneric
  representative := exists_smul_normalizedConfig5_orbitCoord5

/-- The six-point normalized Gram slice. -/
def orbitChart6 : OrbitChart 6 U6 where
  coordinate := orbitCoord6
  slice := normalizedConfig6
  coordinate_slice := orbitCoord6_normalizedConfig6
  coordinate_invariant := orbitCoord6_smulGeneric
  representative := exists_smul_normalizedConfig6_orbitCoord6

/-- Global effective-group times Pfaffian-chart coordinates for four generic
projective points. -/
noncomputable def orbitProductEquiv4 :
    EffectiveSymplecticGroup × U4 ≃ GenericConfig 4 :=
  OrbitChart.productEquiv (k := 0) (U := U4) orbitChart4

/-- Global effective-group times Pfaffian-chart coordinates for five generic
projective points. -/
noncomputable def orbitProductEquiv5 :
    EffectiveSymplecticGroup × U5 ≃ GenericConfig 5 :=
  OrbitChart.productEquiv (k := 1) (U := U5) orbitChart5

/-- Global effective-group times Pfaffian-chart coordinates for six generic
projective points. -/
noncomputable def orbitProductEquiv6 :
    EffectiveSymplecticGroup × U6 ≃ GenericConfig 6 :=
  OrbitChart.productEquiv (k := 2) (U := U6) orbitChart6

@[simp]
theorem orbitProductEquiv4_apply (a : EffectiveSymplecticGroup) (q : U4) :
    orbitProductEquiv4 (a, q) = a • normalizedConfig4 q :=
  rfl

@[simp]
theorem orbitProductEquiv5_apply (a : EffectiveSymplecticGroup) (q : U5) :
    orbitProductEquiv5 (a, q) = a • normalizedConfig5 q :=
  rfl

@[simp]
theorem orbitProductEquiv6_apply (a : EffectiveSymplecticGroup) (q : U6) :
    orbitProductEquiv6 (a, q) = a • normalizedConfig6 q :=
  rfl

@[simp]
theorem orbitCoord4_orbitProductEquiv4
    (a : EffectiveSymplecticGroup) (q : U4) :
    orbitCoord4 (orbitProductEquiv4 (a, q)) = q :=
  orbitChart4.coordinate_productParam a q

@[simp]
theorem orbitCoord5_orbitProductEquiv5
    (a : EffectiveSymplecticGroup) (q : U5) :
    orbitCoord5 (orbitProductEquiv5 (a, q)) = q :=
  orbitChart5.coordinate_productParam a q

@[simp]
theorem orbitCoord6_orbitProductEquiv6
    (a : EffectiveSymplecticGroup) (q : U6) :
    orbitCoord6 (orbitProductEquiv6 (a, q)) = q :=
  orbitChart6.coordinate_productParam a q

/-- Pointwise coordinate equivalence in homogeneous degree three. -/
def coordinateEquiv4 : (U4 → ℝ) ≃ₗ[ℝ] InvariantCochains 4 :=
  orbitChart4.functionLinearEquiv

/-- Pointwise coordinate equivalence in homogeneous degree four. -/
def coordinateEquiv5 : (U5 → ℝ) ≃ₗ[ℝ] InvariantCochains 5 :=
  orbitChart5.functionLinearEquiv

/-- Pointwise coordinate equivalence in homogeneous degree five. -/
def coordinateEquiv6 : (U6 → ℝ) ≃ₗ[ℝ] InvariantCochains 6 :=
  orbitChart6.functionLinearEquiv

/-- The homogeneous alternating coboundary on pointwise invariant projective
cochains. -/
def coboundary (n : ℕ) :
    InvariantCochains n →ₗ[ℝ] InvariantCochains (n + 1) where
  toFun f := ⟨fun x ↦
      ∑ i : Fin (n + 1), faceSign i * f.1 (face i x),
    (mem_invariantCochains _).2 fun g x ↦ by
      apply Finset.sum_congr rfl
      intro i _
      rw [face_smulGeneric, invariant_apply f g (face i x)]⟩
  map_add' f h := by
    apply Subtype.ext
    funext x
    change (∑ i : Fin (n + 1),
        faceSign i * (f.1 (face i x) + h.1 (face i x))) =
      (∑ i : Fin (n + 1), faceSign i * f.1 (face i x)) +
        ∑ i : Fin (n + 1), faceSign i * h.1 (face i x)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  map_smul' c f := by
    apply Subtype.ext
    funext x
    change (∑ i : Fin (n + 1), faceSign i * (c * f.1 (face i x))) =
      c * ∑ i : Fin (n + 1), faceSign i * f.1 (face i x)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The four-to-five coordinate equivalence intertwines the projective-action
coboundary with the five-term Pfaffian operator. -/
theorem coordinateEquiv_D (f : U4 → ℝ) :
    coordinateEquiv5 (D f) = coboundary 4 (coordinateEquiv4 f) := by
  apply Subtype.ext
  funext x
  change D f (orbitCoord5 x) =
    ∑ i : Fin 5, faceSign i * f (orbitCoord4 (face i x))
  rw [D_eq_face_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [orbitCoord4_face]

/-- The five-to-six coordinate equivalence intertwines the projective-action
coboundary with the six-term Pfaffian operator. -/
theorem coordinateEquiv_E (f : U5 → ℝ) :
    coordinateEquiv6 (E f) = coboundary 5 (coordinateEquiv5 f) := by
  apply Subtype.ext
  funext x
  change E f (orbitCoord6 x) =
    ∑ i : Fin 6, faceSign i * f (orbitCoord5 (face i x))
  rw [E_eq_face_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [orbitCoord5_face]

end
end ProjectiveAction
end Sp4
