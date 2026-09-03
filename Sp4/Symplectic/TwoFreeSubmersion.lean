import Sp4.Symplectic.TwoFree

/-!
# The affine chart on two literal free vectors

The two-cone diffusion varies literal nonzero vectors rather than points of
projective space.  This file proves that, on the chart where the last
coordinate of each vector is nonzero, the resulting six affine parameters
give a submersion onto the five-point Pfaffian quotient.  The proof is by an
explicit differentiable right inverse and contains no appeal to a dimension
count.
-/

namespace Sp4
namespace TwoFree

noncomputable section

abbrev VectorPair := SymplecticVector × SymplecticVector

/-- Divide each of two literal vectors by its fourth coordinate and retain
the first three coordinates. -/
def affineParamOfPair (v : VectorPair) : Param :=
  ![v.1 0 / v.1 3, v.1 1 / v.1 3, v.1 2 / v.1 3,
    v.2 0 / v.2 3, v.2 1 / v.2 3, v.2 2 / v.2 3]

/-- Lift affine parameters back to two vectors, retaining the two prescribed
nonzero fourth coordinates. -/
def affinePairSection (v : VectorPair) (p : Param) : VectorPair :=
  (v.1 3 • affineVector (a p) (b p) (c p),
    v.2 3 • affineVector (d p) (e p) (f p))

theorem affineParamOfPair_section (v : VectorPair)
    (hv : v.1 3 ≠ 0) (hw : v.2 3 ≠ 0) (p : Param) :
    affineParamOfPair (affinePairSection v p) = p := by
  funext i
  fin_cases i <;>
    simp [affineParamOfPair, affinePairSection, affineVector,
      a, b, c, d, e, f] <;>
    field_simp [hv, hw]

theorem affinePairSection_at (v : VectorPair)
    (hv : v.1 3 ≠ 0) (hw : v.2 3 ≠ 0) :
    affinePairSection v (affineParamOfPair v) = v := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [affineParamOfPair, affinePairSection, affineVector,
      a, b, c, d, e, f] <;>
    field_simp [hv, hw]

/-- The first projective point of the standard affine chart is the line of
the original first literal vector. -/
theorem standardFiveConfig_affineParam_zero (v : VectorPair)
    (hv : v.1 3 ≠ 0) (hw : v.2 3 ≠ 0) :
    standardFiveConfig (affineParamOfPair v) 0 =
      Projectivization.mk ℂ v.1 (fun h ↦ hv (congrFun h 3)) := by
  have hpair := affinePairSection_at v hv hw
  have hfirst := congrArg Prod.fst hpair
  symm
  apply (Projectivization.mk_eq_mk_iff' (K := ℂ)
    v.1 (standardFiveVectors (affineParamOfPair v) 0) _ _).2
  refine ⟨v.1 3, ?_⟩
  simpa [standardFiveVectors, affinePairSection] using hfirst

/-- The second projective point of the standard affine chart is the line of
the original second literal vector. -/
theorem standardFiveConfig_affineParam_one (v : VectorPair)
    (hv : v.1 3 ≠ 0) (hw : v.2 3 ≠ 0) :
    standardFiveConfig (affineParamOfPair v) 1 =
      Projectivization.mk ℂ v.2 (fun h ↦ hw (congrFun h 3)) := by
  have hpair := affinePairSection_at v hv hw
  have hsecond := congrArg Prod.snd hpair
  symm
  apply (Projectivization.mk_eq_mk_iff' (K := ℂ)
    v.2 (standardFiveVectors (affineParamOfPair v) 1) _ _).2
  refine ⟨v.2 3, ?_⟩
  simpa [standardFiveVectors, affinePairSection] using hsecond

theorem differentiableAt_affineParamOfPair (v : VectorPair)
    (hv : v.1 3 ≠ 0) (hw : v.2 3 ≠ 0) :
    DifferentiableAt ℂ affineParamOfPair v := by
  rw [differentiableAt_pi]
  intro i
  fin_cases i
  · change DifferentiableAt ℂ (fun x : VectorPair => x.1 0 / x.1 3) v
    fun_prop
  · change DifferentiableAt ℂ (fun x : VectorPair => x.1 1 / x.1 3) v
    fun_prop
  · change DifferentiableAt ℂ (fun x : VectorPair => x.1 2 / x.1 3) v
    fun_prop
  · change DifferentiableAt ℂ (fun x : VectorPair => x.2 0 / x.2 3) v
    fun_prop
  · change DifferentiableAt ℂ (fun x : VectorPair => x.2 1 / x.2 3) v
    fun_prop
  · change DifferentiableAt ℂ (fun x : VectorPair => x.2 2 / x.2 3) v
    fun_prop

theorem differentiableAt_affinePairSection (v : VectorPair) (p : Param) :
    DifferentiableAt ℂ (affinePairSection v) p := by
  apply DifferentiableAt.prodMk
  · rw [differentiableAt_pi]
    intro i
    fin_cases i
    · change DifferentiableAt ℂ (fun q : Param => v.1 3 * q 0) p
      fun_prop
    · change DifferentiableAt ℂ (fun q : Param => v.1 3 * q 1) p
      fun_prop
    · change DifferentiableAt ℂ (fun q : Param => v.1 3 * q 2) p
      fun_prop
    · simpa [affineVector] using
        (differentiableAt_const (c := v.1 3) :
          DifferentiableAt ℂ (fun _q : Param => v.1 3) p)
  · rw [differentiableAt_pi]
    intro i
    fin_cases i
    · change DifferentiableAt ℂ (fun q : Param => v.2 3 * q 3) p
      fun_prop
    · change DifferentiableAt ℂ (fun q : Param => v.2 3 * q 4) p
      fun_prop
    · change DifferentiableAt ℂ (fun q : Param => v.2 3 * q 5) p
      fun_prop
    · simpa [affineVector] using
        (differentiableAt_const (c := v.2 3) :
          DifferentiableAt ℂ (fun _q : Param => v.2 3) p)

/-- The normalization map from two literal vectors to six affine coordinates
has onto derivative everywhere in its chart. -/
theorem affineParamOfPair_hasSurjectiveComplexFDerivAt (v : VectorPair)
    (hv : v.1 3 ≠ 0) (hw : v.2 3 ≠ 0) :
    HasSurjectiveComplexFDerivAt affineParamOfPair v := by
  have hf := differentiableAt_affineParamOfPair v hv hw
  refine ⟨hf, ?_⟩
  let s : Param → VectorPair := affinePairSection v
  let p : Param := affineParamOfPair v
  have hs : DifferentiableAt ℂ s p :=
    differentiableAt_affinePairSection v p
  have hsp : s p = v := affinePairSection_at v hv hw
  have hf' : DifferentiableAt ℂ affineParamOfPair (s p) := by
    rw [hsp]
    exact hf
  have hcomp := fderiv_comp p hf' hs
  rw [hsp] at hcomp
  have heq : fderiv ℂ (affineParamOfPair ∘ s) p = 1 := by
    have hfun : affineParamOfPair ∘ s = id := by
      funext q
      exact affineParamOfPair_section v hv hw q
    rw [hfun]
    exact fderiv_id
  have hright : Function.RightInverse (fderiv ℂ s p)
      (fderiv ℂ affineParamOfPair v) := by
    intro u
    have hu := congrArg (fun L : Param →L[ℂ] Param => L u)
      (hcomp.symm.trans heq)
    simpa using hu
  exact hright.surjective

/-- The standard Pfaffian formula composed with literal-vector
normalization is a submersion whenever the projectivized five-tuple is
generic. -/
theorem betaFormula_comp_affineParam_hasSurjectiveComplexFDerivAt
    (v : VectorPair) (hv : v.1 3 ≠ 0) (hw : v.2 3 ≠ 0)
    (hgeneric : IsGeneric (standardFiveConfig (affineParamOfPair v))) :
    HasSurjectiveComplexFDerivAt
      (fun q : VectorPair => betaFormula (affineParamOfPair q)) v := by
  change HasSurjectiveComplexFDerivAt
    (betaFormula ∘ affineParamOfPair) v
  let p : Domain := ⟨affineParamOfPair v, hgeneric⟩
  have haff := affineParamOfPair_hasSurjectiveComplexFDerivAt v hv hw
  have hbeta := betaFormula_hasSurjectiveComplexFDerivAt p
  refine ⟨hbeta.1.comp v haff.1, ?_⟩
  have hchain := fderiv_comp v hbeta.1 haff.1
  change Function.Surjective
    (fderiv ℂ (betaFormula ∘ affineParamOfPair) v)
  rw [hchain]
  exact hbeta.2.comp haff.2

/-- Precomposition with any surjective continuous complex-linear parameter
projection preserves the submersion property. -/
theorem betaFormula_comp_affineParam_compCLM_hasSurjectiveComplexFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : E →L[ℂ] VectorPair) (hL : Function.Surjective L) (x : E)
    (hv : (L x).1 3 ≠ 0) (hw : (L x).2 3 ≠ 0)
    (hgeneric : IsGeneric (standardFiveConfig (affineParamOfPair (L x)))) :
    HasSurjectiveComplexFDerivAt
      (fun y : E => betaFormula (affineParamOfPair (L y))) x := by
  change HasSurjectiveComplexFDerivAt
    ((betaFormula ∘ affineParamOfPair) ∘ L) x
  have hout := betaFormula_comp_affineParam_hasSurjectiveComplexFDerivAt
    (L x) hv hw hgeneric
  have houter : DifferentiableAt ℂ
      (betaFormula ∘ affineParamOfPair) (L x) := by
    simpa [Function.comp_def] using hout.1
  have hLin : DifferentiableAt ℂ L x := L.differentiable.differentiableAt
  refine ⟨houter.comp x hLin, ?_⟩
  have hchain := fderiv_comp x houter hLin
  change Function.Surjective
    (fderiv ℂ ((betaFormula ∘ affineParamOfPair) ∘ L) x)
  rw [hchain, ContinuousLinearMap.fderiv]
  exact hout.2.comp hL

end
end TwoFree
end Sp4
