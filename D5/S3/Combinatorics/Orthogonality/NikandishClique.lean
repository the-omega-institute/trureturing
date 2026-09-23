/- GID: D5/S3/Combinatorics/Orthogonality/NikandishClique
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/NikandishClique
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The clique number of the standard binary subspace orthogonality graph. -/

import D5.S3.Fourier.CharacterSelection.BinaryCharacterCodeDuality
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.SetLike.Fintype
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Quotient.Bilinear

set_option autoImplicit false

namespace D5.S3.Combinatorics.Orthogonality.NikandishClique

open Module
open D5.S3.Fourier.CharacterSelection.BinaryCharacterCodeDuality

/-- The vertices in Nikandish's graph include every nonzero subspace. -/
abbrev Vertex (n : ℕ) := {U : Submodule (ZMod 2) (Fin n → ZMod 2) // U ≠ ⊥}

/-- The independent finite-lattice invariant in the clique formula. -/
noncomputable def nonzeroSubspaceCount (r : ℕ) : ℕ := Nat.card (Vertex r)

/-- Distinct subspaces are adjacent exactly when they are mutually orthogonal. -/
def orthogonalityGraph (n : ℕ) : SimpleGraph (Vertex n) where
  Adj U W := U ≠ W ∧ ∀ u ∈ U.1, ∀ w ∈ W.1,
    standardCoordinatePairing (ZMod 2) (Fin n) u w = 0
  symm := ⟨by
    intro U W h
    refine ⟨h.1.symm, fun w hw u hu => ?_⟩
    change dotProduct w u = 0
    rw [dotProduct_comm]
    exact h.2 u hu w hw⟩
  loopless := ⟨fun U h => h.1 rfl⟩

/-- The exact all-dimensional answer to Nikandish's Problem 4.2.
The count is the cardinality of the complete nonzero subspace lattice. -/
theorem result (n : ℕ) (_hn : 1 ≤ n) :
    (orthogonalityGraph n).cliqueNum =
      max n (nonzeroSubspaceCount (n / 2) + n % 2) := by
  classical
  have upper (n : ℕ) (C : Finset (Vertex n)) (hC : (orthogonalityGraph n).IsClique C) :
      ∃ r ≤ n / 2, C.card ≤ nonzeroSubspaceCount r + (n - 2 * r) := by
    classical
    let B := standardCoordinatePairing (ZMod 2) (Fin n)
    have bs : B.IsSymm := ⟨dotProduct_comm⟩
    have bn : B.Nondegenerate := bs.isRefl.nondegenerate_iff_separatingLeft.mpr
      (fun x hx => dotProduct_eq_zero x hx)
    let U : C → Submodule (ZMod 2) (Fin n → ZMod 2) := fun i => i.1.1
    let R := ⨆ i : C, U i ⊓ B.orthogonal (U i)
    have rad_le (i : C) : U i ⊓ B.orthogonal (U i) ≤ R :=
      le_iSup (fun i : C => U i ⊓ B.orthogonal (U i)) i
    have rorth (i : C) : R ≤ B.orthogonal (U i) := by
      refine iSup_le fun j => ?_
      by_cases h : j = i
      · subst j; exact inf_le_right
      · intro x hx y hy
        exact hC i.2 j.2 (fun e => h (Subtype.ext e.symm)) |>.2 y hy x hx.1
    have ur (i : C) : U i ≤ B.orthogonal R := by
      intro x hx y hy
      exact bs.eq_iff.mpr (rorth i hy x hx)
    have rr : R ≤ B.orthogonal R := iSup_le fun i => (inf_le_left.trans (ur i))
    have inter (i : C) : U i ⊓ R = U i ⊓ B.orthogonal (U i) :=
      le_antisymm (inf_le_inf_left _ (rorth i)) (le_inf inf_le_left (rad_le i))
    let r := finrank (ZMod 2) R
    have dimS : finrank (ZMod 2) (B.orthogonal R) = n - r := by
      simpa [r] using B.finrank_orthogonal bn R
    have hr : 2 * r ≤ n := by
      have := Submodule.finrank_mono rr
      rw [dimS] at this
      omega
    let S := B.orthogonal R
    let J := R.comap S.subtype
    let Q := S ⧸ J
    let f := B.restrict S
    have jk : J ≤ LinearMap.ker f := by
      intro x hx
      ext y
      exact y.2 x.1 hx
    have jf : J ≤ LinearMap.ker f.flip := by
      intro x hx
      ext y
      exact bs.eq_iff.mpr (y.2 x.1 hx)
    let b := f.liftQ₂ J J jk jf
    let W : C → Submodule (ZMod 2) Q := fun i => (U i |>.comap S.subtype).map J.mkQ
    have sep (i : C) (x : Q) (hx : x ∈ W i)
        (hz : ∀ y ∈ W i, b y x = 0) : x = 0 := by
      obtain ⟨v, hv, rfl⟩ := hx
      apply (Submodule.Quotient.mk_eq_zero J).mpr
      have hrad : v.1 ∈ U i ⊓ B.orthogonal (U i) :=
        ⟨hv, fun y hy => hz (J.mkQ ⟨y, ur i hy⟩) ⟨⟨y, ur i hy⟩, hy, rfl⟩⟩
      exact (show v.1 ∈ U i ⊓ R from inter i ▸ hrad).2
    have wo (i j : C) (h : i ≠ j) (x : Q) (hx : x ∈ W i)
        (y : Q) (hy : y ∈ W j) : b x y = 0 := by
      obtain ⟨v, hv, rfl⟩ := hx
      obtain ⟨w, hw, rfl⟩ := hy
      exact hC i.2 j.2 (fun e => h (Subtype.ext e)) |>.2 v.1 hv w.1 hw
    have wi : iSupIndep W := by
      rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
      intro t v hv hz i hi
      apply sep i _ (hv i hi)
      intro y hy
      have hs := congrArg (b y) hz
      rw [map_sum, map_zero] at hs
      rw [Finset.sum_eq_single i] at hs
      · exact hs
      · intro j hj hji
        exact wo i j hji.symm y hy (v j) (hv j hj)
      · exact fun h => (h hi).elim
    have wzero (i : C) : W i = ⊥ ↔ U i ≤ R := by
      change (U i |>.comap S.subtype).map J.mkQ = ⊥ ↔ _
      rw [eq_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot, Submodule.ker_mkQ]
      constructor
      · intro h x hx; exact h (show (⟨x, ur i hx⟩ : S) ∈ (U i).comap S.subtype from hx)
      · intro h x hx; exact h hx
    have qdim : finrank (ZMod 2) Q = n - 2 * r := by
      have hj : finrank (ZMod 2) J = r := (Submodule.comapSubtypeEquivOfLe rr).finrank_eq
      have hq := Submodule.finrank_quotient_add_finrank J
      change finrank (ZMod 2) Q + finrank (ZMod 2) J = finrank (ZMod 2) S at hq
      change finrank (ZMod 2) S = n - r at dimS
      omega
    have out : Fintype.card {i : C // ¬U i ≤ R} ≤ n - 2 * r := by
      have h := wi.subtype_ne_bot_le_finrank
      rw [qdim] at h
      simpa only [ne_eq, wzero] using h
    let e := Submodule.orderIsoMapComap (Module.finBasis (ZMod 2) R).equivFun
    have countR : Nat.card {P : Submodule (ZMod 2) R // P ≠ ⊥} = nonzeroSubspaceCount r :=
      Nat.card_congr (e.toEquiv.subtypeEquiv (fun P => by simp))
    have nz (i : {i : C // U i ≤ R}) : (U i.1).comap R.subtype ≠ ⊥ := by
      intro h
      apply i.1.1.2
      have he := congrArg (Submodule.map R.subtype) h
      simpa [Submodule.map_comap_subtype, inf_eq_right.mpr i.2] using he
    let g : {i : C // U i ≤ R} → {P : Submodule (ZMod 2) R // P ≠ ⊥} :=
      fun i => ⟨(U i.1).comap R.subtype, nz i⟩
    have gi : Function.Injective g := by
      intro i j h
      have he := congrArg (fun P => P.1.map R.subtype) h
      have huv : U i.1 = U j.1 := by
        simpa [g, Submodule.map_comap_subtype, inf_eq_right.mpr i.2,
          inf_eq_right.mpr j.2] using he
      exact Subtype.ext (Subtype.ext (Subtype.ext huv))
    have inside : Fintype.card {i : C // U i ≤ R} ≤ nonzeroSubspaceCount r := by
      have h := Nat.card_le_card_of_injective g gi
      simpa only [countR, Nat.card_eq_fintype_card] using h
    refine ⟨r, by omega, ?_⟩
    have split := Fintype.card_subtype_compl (fun i : C => U i ≤ R)
    have lecard := Fintype.card_subtype_le (fun i : C => U i ≤ R)
    simp only [Fintype.card_coe] at split lecard
    omega
  -- A hyperplane embedding, one outside line, and the whole ambient space.
  have increment (r : ℕ) (hr : 1 ≤ r) :
      nonzeroSubspaceCount r + 2 ≤ nonzeroSubspaceCount (r + 1) := by
    classical
    let : Fintype (Vertex r) := Fintype.ofFinite _
    let : Fintype (Vertex (r + 1)) := Fintype.ofFinite _
    let f : (Fin r → ZMod 2) →ₗ[ZMod 2] (Fin (r + 1) → ZMod 2) :=
      LinearMap.vecCons 0 LinearMap.id
    have fi : Function.Injective f := by
      intro x y h
      ext i
      exact congrFun h i.succ
    let g : Vertex r → Vertex (r + 1) := fun P => ⟨P.1.map f, by
      intro h
      apply P.2
      apply Submodule.map_injective_of_injective fi
      simpa using h⟩
    have gi : Function.Injective g := fun P Q h =>
      Subtype.ext (Submodule.map_injective_of_injective fi (congrArg Subtype.val h))
    let v : Fin (r + 1) → ZMod 2 := Fin.cons 1 0
    have vn : v ≠ 0 := by intro h; have := congrFun h 0; simp [v] at this
    let L : Vertex (r + 1) := ⟨(ZMod 2) ∙ v, by simpa using vn⟩
    let T : Vertex (r + 1) := ⟨⊤, top_ne_bot⟩
    have lt : L ≠ T := by
      intro h
      have hd := congrArg (fun P : Vertex (r + 1) => finrank (ZMod 2) P.1) h
      have hl : finrank (ZMod 2) L.1 = 1 := finrank_span_singleton vn
      have ht : finrank (ZMod 2) T.1 = r + 1 := by simp [T]
      omega
    have outside (P : Vertex r) : v ∉ (g P).1 := by
      rintro ⟨x, hx, he⟩
      have := congrFun he 0
      simp [f, v] at this
    have ln : L ∉ Finset.univ.image g := by
      intro h; obtain ⟨P, hP, he⟩ := Finset.mem_image.mp h
      apply outside P
      rw [he]
      exact Submodule.mem_span_singleton_self v
    have tn : T ∉ Finset.univ.image g := by
      intro h; obtain ⟨P, hP, he⟩ := Finset.mem_image.mp h
      apply outside P
      rw [he]
      trivial
    have hc := (insert L (insert T (Finset.univ.image g))).card_le_univ
    rw [Finset.card_insert_of_notMem (by simp [lt, ln]), Finset.card_insert_of_notMem tn,
      Finset.card_image_of_injective _ gi, Finset.card_univ] at hc
    simpa only [nonzeroSubspaceCount, Nat.card_eq_fintype_card, Nat.add_assoc] using hc
  -- The first extremal clique consists of the coordinate lines.
  have coordinate (n : ℕ) : n ≤ (orthogonalityGraph n).cliqueNum := by
    classical
    let v : Fin n → (Fin n → ZMod 2) := fun i => Pi.single i 1
    have vn (i : Fin n) : v i ≠ 0 := by
      intro h; have := congrFun h i; simp [v] at this
    let L : Fin n → Vertex n := fun i => ⟨(ZMod 2) ∙ v i, by simpa using vn i⟩
    have li : Function.Injective L := by
      intro i j h
      by_contra hn
      have hm : v i ∈ (ZMod 2) ∙ v j := by
        have he := congrArg Subtype.val h
        change (ZMod 2) ∙ v i = (ZMod 2) ∙ v j at he
        rw [← he]; exact Submodule.mem_span_singleton_self _
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
      have := congrFun ha i
      simp [v, hn] at this
    have hc : (orthogonalityGraph n).IsClique (Finset.univ.image L) := by
      intro P hP Q hQ hpq
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hQ
      refine ⟨hpq, ?_⟩
      have hij : i ≠ j := fun h => hpq (congrArg L h)
      intro x hx y hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
      change dotProduct (a • v i) (b • v j) = 0
      simp [v, dotProduct_smul, hij.symm]
    simpa [Finset.card_image_of_injective _ li] using hc.card_le_cliqueNum
  -- Duplicate coordinates form a totally isotropic space of dimension t.
  have isotropic (t e : ℕ) (he : e ≤ 1) : nonzeroSubspaceCount t + e ≤
      (orthogonalityGraph (t + (t + e))).cliqueNum := by
    classical
    let : Fintype (Vertex t) := Fintype.ofFinite _
    let m := t + (t + e)
    let B := standardCoordinatePairing (ZMod 2) (Fin m)
    have bs : B.IsSymm := ⟨dotProduct_comm⟩
    have bn : B.Nondegenerate := bs.isRefl.nondegenerate_iff_separatingLeft.mpr
      (fun x hx => dotProduct_eq_zero x hx)
    let f : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) := {
      toFun := fun x => Fin.append x (Fin.append x 0)
      map_add' := by
        intro x y; ext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp
        · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;> simp
      map_smul' := by
        intro a x; ext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp
        · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;> simp }
    have fi : Function.Injective f := by
      intro x y h
      ext i
      simpa [f] using congrFun h (Fin.castAdd (t + e) i)
    have iso (x y : Fin t → ZMod 2) : B (f x) (f y) = 0 := by
      change (∑ i : Fin (t + (t + e)), f x i * f y i) = 0
      simp [f, Fin.sum_univ_add, CharTwo.add_self_eq_zero]
    let T := LinearMap.range f
    have dt : finrank (ZMod 2) T = t := by simpa using LinearMap.finrank_range_of_inj fi
    let g : Vertex t → Vertex m := fun P => ⟨P.1.map f, by
      intro h
      apply P.2
      apply Submodule.map_injective_of_injective fi
      simpa using h⟩
    have gi : Function.Injective g := fun P Q h =>
      Subtype.ext (Submodule.map_injective_of_injective fi (congrArg Subtype.val h))
    let C := Finset.univ.image g
    have cc : C.card = nonzeroSubspaceCount t := by
      simp only [C, Finset.card_image_of_injective _ gi, Finset.card_univ,
        nonzeroSubspaceCount, Nat.card_eq_fintype_card]
    have hc : (orthogonalityGraph m).IsClique C := by
      intro P hP Q hQ hpq
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hQ
      refine ⟨hpq, ?_⟩
      rintro x ⟨v, hv, rfl⟩ y ⟨w, hw, rfl⟩
      exact iso v w
    by_cases hz : e = 0
    · simpa only [hz, Nat.add_zero, cc] using hc.card_le_cliqueNum
    have he1 : e = 1 := by omega
    have dp : finrank (ZMod 2) (B.orthogonal T) = t + 1 := by
      have h := B.finrank_orthogonal bn T
      rw [dt, Module.finrank_fin_fun] at h
      simpa only [m, he1, Nat.add_sub_cancel_left] using h
    let E : Vertex m := ⟨B.orthogonal T, by
      intro h; rw [h, finrank_bot] at dp; omega⟩
    have en : E ∉ C := by
      intro h; obtain ⟨P, hP, heq⟩ := Finset.mem_image.mp h
      have leT : E.1 ≤ T := heq ▸ LinearMap.map_le_range
      have := Submodule.finrank_mono leT
      change finrank (ZMod 2) (B.orthogonal T) ≤ finrank (ZMod 2) T at this
      omega
    have hec : (orthogonalityGraph m).IsClique (insert E C : Finset _) := by
      rw [Finset.coe_insert]
      apply hc.insert
      intro P hP hne
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hP
      refine ⟨hne, fun x hx y hy => ?_⟩
      exact bs.eq_iff.mpr (hx y (LinearMap.map_le_range hy))
    simpa only [Finset.card_insert_of_notMem en, cc, he1] using hec.card_le_cliqueNum
  have zero_count : nonzeroSubspaceCount 0 = 0 := by
    have : IsEmpty (Vertex 0) := ⟨fun P => P.2 (Subsingleton.elim _ _)⟩
    exact Nat.card_of_isEmpty
  have growth (r t : ℕ) (hr : 1 ≤ r) (hrt : r ≤ t) :
      nonzeroSubspaceCount r + 2 * (t - r) ≤ nonzeroSubspaceCount t := by
    induction t, hrt using Nat.le_induction with
    | base => simp
    | succ t hrt ih =>
      have hi := increment t (by omega)
      omega
  obtain ⟨C, hC⟩ := (orthogonalityGraph n).exists_isNClique_cliqueNum
  obtain ⟨r, hr, hu⟩ := upper n C hC.isClique
  have bound : C.card ≤ max n (nonzeroSubspaceCount (n / 2) + n % 2) := by
    by_cases hz : r = 0
    · simp only [hz, zero_count, Nat.mul_zero, Nat.sub_zero, Nat.zero_add] at hu
      exact hu.trans (le_max_left _ _)
    · have hg := growth r (n / 2) (by omega) hr
      have he := Nat.mod_add_div n 2
      omega
  apply le_antisymm (hC.card_eq ▸ bound)
  apply max_le (coordinate n)
  have hl := isotropic (n / 2) (n % 2) (by omega)
  have hd : n / 2 + (n / 2 + n % 2) = n := by omega
  exact hl.trans_eq (congrArg (fun k => (orthogonalityGraph k).cliqueNum) hd)

#print axioms result

end D5.S3.Combinatorics.Orthogonality.NikandishClique
