/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorHom
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorHom
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual neutral-module morphisms and postcomposition of mixed intertwiners. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorFusion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open scoped BigOperators
noncomputable section

/-- Linear maps commuting with every actual neutral state and mode. -/
def sectorHomSpace (D : LatticeData) (δ γ : Charge D) :
    Submodule ℂ (Sector D δ →ₗ[ℂ] Sector D γ) where
  carrier := {f | ∀ a n v, f (action D δ a n v) = action D γ a n (f v)}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg a n v; simp [hf a n v, hg a n v]
  smul_mem' := by intro c f hf a n v; simp [hf a n v]

abbrev SectorHom (D : LatticeData) (δ γ : Charge D) := sectorHomSpace D δ γ

/-- Scalar identity is an actual neutral-module morphism. -/
def scalarHom (D : LatticeData) (δ : Charge D) (c : ℂ) : SectorHom D δ δ :=
  ⟨c • LinearMap.id, by intro a n v; simp⟩

/-- Neutral-mode morphisms commute with actual translation under inverse Gram. -/
theorem hom_translation (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (δ γ : Charge D) (f : SectorHom D δ γ) (v : Sector D δ) :
    f.val (sectorT D δ v) = sectorT D γ (f.val v) := by
  rw [← conformal_translation D H hHG hGH δ, ← conformal_translation D H hHG hGH γ]
  exact f.property _ _ _

/-- Postcomposition acts on the full coefficient domain. -/
def postCoefficients (D : LatticeData) (α β δ γ : Charge D)
    (f : Sector D δ →ₗ[ℂ] Sector D γ) (I : Coefficients D α β δ) :
    Coefficients D α β γ where
  toFun u n := f.comp (I u n)
  map_add' u v := by ext n w; simp
  map_smul' c u := by ext n w; simp

/-- Every full IO law is preserved by actual module postcomposition. -/
theorem post_lawful (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β δ γ : Charge D) (f : SectorHom D δ γ) (I : IO D α β δ) :
    Lawful D α β γ (postCoefficients D α β δ γ f.val I.val) where
  truncation u v := by
    obtain ⟨N, hN⟩ := I.property.truncation u v
    exact ⟨N, fun n hn => by simp [postCoefficients, hN n hn]⟩
  source u n := by
    apply LinearMap.ext
    intro v
    have h := congrArg (fun g : Sector D β →ₗ[ℂ] Sector D δ => f.val (g v))
      (I.property.source u n)
    simpa [postCoefficients] using h
  target u n := by
    apply LinearMap.ext
    intro v
    have h := congrArg (fun g : Sector D β →ₗ[ℂ] Sector D δ => f.val (g v))
      (I.property.target u n)
    simpa [postCoefficients, ← hom_translation D H hHG hGH δ γ f] using h
  jacobi a u v p q r := by
    have hi := I.property.jacobi a u v p q r
    have hl (i : ℕ) : leftTerm D α β γ (postCoefficients D α β δ γ f.val I.val)
        a u v p q r i = f.val (leftTerm D α β δ I.val a u v p q r i) := by
      simp [leftTerm, postCoefficients]
    have hf (i : ℕ) : firstTerm D α β γ (postCoefficients D α β δ γ f.val I.val)
        a u v p q r i = f.val (firstTerm D α β δ I.val a u v p q r i) := by
      simp only [firstTerm, postCoefficients, LinearMap.coe_mk, LinearMap.comp_apply,
        map_smul, f.property a (p + r - i) _]
      rfl
    have hs (i : ℕ) : secondTerm D α β γ (postCoefficients D α β δ γ f.val I.val)
        a u v p q r i = f.val (secondTerm D α β δ I.val a u v p q r i) := by
      simp [secondTerm, postCoefficients]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [funext hl]; exact hi.1.fun_comp (map_zero f.val)
    · rw [funext hf]; exact hi.2.1.fun_comp (map_zero f.val)
    · rw [funext hs]; exact hi.2.2.1.fun_comp (map_zero f.val)
    · have h := congrArg f.val hi.2.2.2
      rw [map_sub, map_finsum f.val hi.1, map_finsum f.val hi.2.1,
        map_finsum f.val hi.2.2.1] at h
      simpa only [hl, hf, hs] using h

/-- The genuine linear postcomposition operation on lawful mixed IO. -/
def post (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β δ γ : Charge D) (f : SectorHom D δ γ) : IO D α β δ →ₗ[ℂ] IO D α β γ where
  toFun I := ⟨postCoefficients D α β δ γ f.val I.val, post_lawful D H hHG hGH α β δ γ f I⟩
  map_add' I K := by apply Subtype.ext; apply LinearMap.ext; intro u; funext n; ext v; simp [postCoefficients]
  map_smul' c I := by apply Subtype.ext; apply LinearMap.ext; intro u; funext n; ext v; simp [postCoefficients]

/-- The scalar of an arbitrary actual endomorphism is forced by IO classification. -/
theorem hom_scalar (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (δ : Charge D) (f : SectorHom D δ δ) : ∃ c : ℂ, f = scalarHom D δ c := by
  have hδ : (0 : Charge D) + δ = δ := by ext i; simp
  let J : IO D 0 δ δ := ⟨canonical D 0 δ, by
    have h := canonical_lawful D 0 δ
    rw [hδ] at h
    exact h⟩
  let I := post D H hHG hGH 0 δ δ δ f J
  have all : ∀ K : IO D 0 δ (0 + δ), ∃ c : ℂ, K.val = c • canonical D 0 δ := by
    intro K
    refine ⟨groundEvaluation D 0 δ K, ?_⟩
    exact congrArg Subtype.val ((classification D H hHG hGH 0 δ).symm_apply_apply K).symm
  rw [hδ] at all
  obtain ⟨c, hc⟩ := all I
  refine ⟨c, ?_⟩
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  have e := congrArg (fun K : Coefficients D 0 δ δ => K 1 (-1) v) hc
  dsimp [I, post, postCoefficients] at e
  have Jval : J.val = canonical D 0 δ := rfl
  rw [Jval] at e
  change f.val v = c • v
  have vac : canonical D 0 δ 1 (-1) v = v := by
    have hv := congrArg (fun k : Module.End ℂ (Sector D δ) => k v) (action_vacuum D δ (-1))
    simpa [action, Sector] using hv
  simpa only [vac] using e

/-- Wrong-charge module maps vanish, derived from the full IO charge selection. -/
theorem hom_wrong_charge (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (δ γ : Charge D) (hne : γ ≠ δ) (f : SectorHom D δ γ) : f = 0 := by
  have hδ : (0 : Charge D) + δ = δ := by ext i; simp
  let J : IO D 0 δ δ := ⟨canonical D 0 δ, by
    have h := canonical_lawful D 0 δ
    rw [hδ] at h
    exact h⟩
  let I := post D H hHG hGH 0 δ δ γ f J
  have h := wrong_charge_vanishing D H hHG 0 δ γ (by simpa using hne) I
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  have e := congrArg (fun K : IO D 0 δ γ => K.val 1 (-1) v) h
  dsimp [I, post, postCoefficients] at e
  have Jval : J.val = canonical D 0 δ := rfl
  rw [Jval] at e
  change f.val (canonical D 0 δ 1 (-1) v) = 0 at e
  change f.val v = 0
  have vac : canonical D 0 δ 1 (-1) v = v := by
    have hv := congrArg (fun k : Module.End ℂ (Sector D δ) => k v) (action_vacuum D δ (-1))
    simpa [action, Sector] using hv
  simpa only [vac] using e

end
end D5.S3.VertexAlgebra.LatticeSectorIntertwiner
