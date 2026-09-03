import Sp4.Cohomology.ExternalInputs
import Sp4.Pfaffian.Permutation

/-!
# Nonsingularity of the five-point permutation maps

The alternating measure-chain construction uses all vertex permutations of
the normalized five-point chart.  Here we prove that these rational maps are
smooth local diffeomorphisms on the generic locus and then invoke the general
coarea theorem from `ExternalInputs` to obtain preservation of null sets.
-/

namespace Sp4
namespace Pfaffian

noncomputable section

open MeasureTheory

/-- The rational formula underlying `permute5`, before restriction to the
open generic subtype. -/
def ambientPermute5 (sigma : Equiv.Perm (Fin 5)) (q : Coord5) : Coord5 :=
  chi5 (reindexGram sigma (matrix5 q))

@[simp]
theorem ambientPermute5_restrict (sigma : Equiv.Perm (Fin 5)) (q : U5) :
    ambientPermute5 sigma q.1 = (permute5 sigma q).1 :=
  rfl

theorem ambientPermute5_mem (sigma : Equiv.Perm (Fin 5)) (q : U5) :
    IsU5 (ambientPermute5 sigma q.1) := by
  rw [ambientPermute5_restrict]
  exact (permute5 sigma q).2

@[fun_prop] theorem differentiable_matrix5_entry (i j : Fin 5) :
    Differentiable ℂ (fun q : Coord5 ↦ matrix5 q i j) := by
  fin_cases i <;> fin_cases j <;> simp [matrix5] <;> fun_prop

theorem differentiableAt_normalizedEntry_reindex_matrix5
    (sigma : Equiv.Perm (Fin 5)) (i j : Fin 5)
    (hi : i ≠ 0) (hj : j ≠ 0) (q : U5) :
    DifferentiableAt ℂ
      (fun z : Coord5 ↦
        normalizedEntry (reindexGram sigma (matrix5 z)) i j) q.1 := by
  let hentry (a b : Fin 5) : DifferentiableAt ℂ
      (fun z : Coord5 ↦ reindexGram sigma (matrix5 z) a b) q.1 :=
    (differentiable_matrix5_entry (sigma a) (sigma b)).differentiableAt
  have hoff := (OrbitChain.matrix5_isAdmissible q).offDiagonal_ne
  have hden :
      reindexGram sigma (matrix5 q.1) 1 2 *
          reindexGram sigma (matrix5 q.1) 0 i *
            reindexGram sigma (matrix5 q.1) 0 j ≠ 0 := mul_ne_zero
    (mul_ne_zero
      (hoff (sigma 1) (sigma 2) (sigma.injective.ne (by decide)))
      (hoff (sigma 0) (sigma i) (sigma.injective.ne hi.symm)))
    (hoff (sigma 0) (sigma j) (sigma.injective.ne hj.symm))
  change DifferentiableAt ℂ (fun z : Coord5 ↦
    (reindexGram sigma (matrix5 z) i j *
        reindexGram sigma (matrix5 z) 0 1 *
          reindexGram sigma (matrix5 z) 0 2) /
      (reindexGram sigma (matrix5 z) 1 2 *
        reindexGram sigma (matrix5 z) 0 i *
          reindexGram sigma (matrix5 z) 0 j)) q.1
  fun_prop (disch := exact hden)

theorem differentiableAt_ambientPermute5
    (sigma : Equiv.Perm (Fin 5)) (q : U5) :
    DifferentiableAt ℂ (ambientPermute5 sigma) q.1 := by
  apply differentiableAt_coord5_mk
  · exact differentiableAt_normalizedEntry_reindex_matrix5 sigma 1 3
      (by decide) (by decide) q
  · exact differentiableAt_normalizedEntry_reindex_matrix5 sigma 1 4
      (by decide) (by decide) q
  · exact differentiableAt_normalizedEntry_reindex_matrix5 sigma 2 3
      (by decide) (by decide) q
  · exact differentiableAt_normalizedEntry_reindex_matrix5 sigma 2 4
      (by decide) (by decide) q
  · exact differentiableAt_normalizedEntry_reindex_matrix5 sigma 3 4
      (by decide) (by decide) q

theorem ambientPermute5_section_at
    (sigma : Equiv.Perm (Fin 5)) (q : U5) :
    ambientPermute5 sigma⁻¹ (ambientPermute5 sigma q.1) = q.1 := by
  have h := congrArg Subtype.val (permute5_mul sigma sigma⁻¹ q)
  simpa [ambientPermute5] using h

/-- The inverse permutation formula holds on a whole neighbourhood of the
image point, which is the precise local input needed to differentiate the
right-inverse identity. -/
theorem eventually_ambientPermute5_section
    (sigma : Equiv.Perm (Fin 5)) (q : U5) :
    ambientPermute5 sigma ∘ ambientPermute5 sigma⁻¹ =ᶠ[
      nhds (ambientPermute5 sigma q.1)] id := by
  have himage : IsU5 (ambientPermute5 sigma q.1) :=
    ambientPermute5_mem sigma q
  have hevent : ∀ᶠ z in nhds (ambientPermute5 sigma q.1), z ∈ u5Set :=
    isOpen_u5Set.mem_nhds himage
  filter_upwards [hevent] with z hz
  let r : U5 := ⟨z, hz⟩
  have h := ambientPermute5_section_at sigma⁻¹ r
  simpa only [inv_inv, Function.comp_apply, id_eq] using h

/-- Every vertex permutation has an onto complex derivative at every point
of the generic five-point chart. -/
theorem ambientPermute5_hasSurjectiveComplexFDerivAt
    (sigma : Equiv.Perm (Fin 5)) (q : U5) :
    HasSurjectiveComplexFDerivAt (ambientPermute5 sigma) q.1 := by
  refine ⟨differentiableAt_ambientPermute5 sigma q, ?_⟩
  let sec := ambientPermute5 sigma⁻¹
  let a := ambientPermute5 sigma q.1
  let qa : U5 := ⟨a, ambientPermute5_mem sigma q⟩
  have hs : DifferentiableAt ℂ sec a := by
    exact differentiableAt_ambientPermute5 sigma⁻¹ qa
  have hsa : sec a = q.1 := ambientPermute5_section_at sigma q
  have hf : DifferentiableAt ℂ (ambientPermute5 sigma) (sec a) := by
    rw [hsa]
    exact differentiableAt_ambientPermute5 sigma q
  have hcomp := fderiv_comp a hf hs
  rw [hsa] at hcomp
  have heq : fderiv ℂ (ambientPermute5 sigma ∘ sec) a = 1 := by
    rw [(eventually_ambientPermute5_section sigma q).fderiv_eq]
    exact fderiv_id
  have hright : Function.RightInverse (fderiv ℂ sec a)
      (fderiv ℂ (ambientPermute5 sigma) q.1) := by
    intro v
    have hc := congrArg (fun L : Coord5 →L[ℂ] Coord5 ↦ L v)
      (hcomp.symm.trans heq)
    simpa using hc
  exact hright.surjective

/-- Vertex permutations preserve the smooth measure class used on `U5`. -/
theorem permute5_quasiMeasurePreserving (sigma : Equiv.Perm (Fin 5)) :
    Measure.QuasiMeasurePreserving (permute5 sigma) measureU5 measureU5 := by
  have hmem : ∀ x, x ∈ u5Set → ambientPermute5 sigma x ∈ u5Set := by
    intro x hx
    exact ambientPermute5_mem sigma ⟨x, hx⟩
  have h := quasiMeasurePreserving_normalizedOpenGaussian_of_submersion
    coord5Gaussian coord5Gaussian
    coord5GaussianPresentation coord5GaussianPresentation
    u5Set isOpen_u5Set u5Set_nonempty
    u5Set isOpen_u5Set u5Set_nonempty
    (ambientPermute5 sigma) hmem
    (by
      intro x hx
      exact ambientPermute5_hasSurjectiveComplexFDerivAt sigma ⟨x, hx⟩)
  change Measure.QuasiMeasurePreserving (permute5 sigma)
    (normalizedOpenMeasure coord5Gaussian u5Set isOpen_u5Set u5Set_nonempty)
    (normalizedOpenMeasure coord5Gaussian u5Set isOpen_u5Set u5Set_nonempty)
  refine h.congr (continuous_permute5 sigma).measurable ?_
  filter_upwards with q
  apply Subtype.ext
  exact ambientPermute5_restrict sigma q

end
end Pfaffian
end Sp4
