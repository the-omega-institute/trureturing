/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnBlockFactorization
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnBlockFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Products.PartIIFixedCycleBlockValues
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace NikolovSegal.PartIISLnBlockFactorization
open Matrix PartIIUnitriangularLayers
universe u
variable {F : Type u} [Field F] {N B : ℕ}

private theorem product_one_add {R : Type*} [Ring R] (L : List R)
    (h : L.Pairwise (fun x y => x*y=0)) :
    (L.map (fun x => 1+x)).prod=1+L.sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    obtain ⟨hx,hL⟩ := List.pairwise_cons.mp h
    have hz : x*L.sum=0 := by
      have hsum (K : List R) (hK : ∀ y∈K, x*y=0) : x*K.sum=0 := by
        induction K with
        | nil => simp
        | cons y K ihK =>
          rw [List.sum_cons,mul_add,hK y (List.mem_cons_self),
            ihK (fun z hz => hK z (List.mem_cons_of_mem _ hz)),add_zero]
      exact hsum L hx
    rw [List.map_cons,List.prod_cons,ih hL,List.sum_cons]
    noncomm_ring [hz]

private def rect (col : Fin N → Fin B) (r s : Fin B)
    (v : SpecialLinearGroup (Fin N) F) : Matrix (Fin N) (Fin N) F :=
  fun i j => if col i=r ∧ col j=s ∧ r<s then v i j else 0
private theorem rect_depth (col : Fin N → Fin B) (hmono : Monotone col)
    (r s : Fin B) (v : SpecialLinearGroup (Fin N) F) :
    LayerDepth 1 (rect col r s v) := by
  intro i j hij
  change j.val < i.val+1 at hij
  have hji : j ≤ i := by change j.val ≤ i.val;omega
  have hh := hmono hji
  simp only [rect]
  split_ifs with h
  · rw [h.1,h.2.1] at hh
    exact False.elim (not_lt_of_ge hh h.2.2)
  · rfl
private def depthSL (A : Matrix (Fin N) (Fin N) F) (hA : LayerDepth 1 A) :
    SpecialLinearGroup (Fin N) F := by
  classical
  refine ⟨1+A,?_⟩
  have hupper : IsUpperTriangular (1+A) := by
    intro i j hij
    have he : i≠j := by intro h; subst j; exact lt_irrefl _ hij
    simp only [Matrix.add_apply,Matrix.one_apply,if_neg he,zero_add]
    exact hA i j (by change j.val < i.val+1; change j.val < i.val at hij;omega)
  rw [det_of_isUpperTriangular hupper]
  apply Finset.prod_eq_one
  intro i hi
  rw [Matrix.add_apply,Matrix.one_apply,if_pos rfl,hA i i (by omega),add_zero]
private def rectSL (col : Fin N → Fin B) (hmono : Monotone col)
    (r s : Fin B) (v : SpecialLinearGroup (Fin N) F) : SpecialLinearGroup (Fin N) F :=
  depthSL (rect col r s v) (rect_depth col hmono r s v)

private theorem rect_forward_zero (col : Fin N → Fin B)
    (r s r' s' : Fin B) (hr : r'≤r) (v : SpecialLinearGroup (Fin N) F) :
    rect col r s v*rect col r' s' v=0 := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro t ht
  simp only [rect]
  split_ifs with h h'
  · have hs : s=r' := h.2.1.symm.trans h'.1
    have hsr := h.2.2
    rw [hs] at hsr
    exact False.elim (not_lt_of_ge hr hsr)
  all_goals simp

private theorem ordered_rect_row (col : Fin N → Fin B) (hmono : Monotone col)
    (r : Fin B) (v : SpecialLinearGroup (Fin N) F) :
    (orderedProduct (fun s => rectSL col hmono r s v)).val=
      1+(List.ofFn (fun s => rect col r s v)).sum := by
  have hp : (List.ofFn (fun s => rect col r s v)).Pairwise (fun x y => x*y=0) := by
    rw [List.pairwise_ofFn]
    intro i j hij
    exact rect_forward_zero col r i r j (le_refl _) v
  have hh := product_one_add _ hp
  have hm := map_list_prod (SpecialLinearGroup.coeMonoidHom : SpecialLinearGroup (Fin N) F →* Matrix (Fin N) (Fin N) F)
    (List.ofFn (fun s => rectSL col hmono r s v))
  have hm' : (orderedProduct (fun s => rectSL col hmono r s v)).val=
      (List.ofFn (fun s => 1+rect col r s v)).prod := by
    simpa only [orderedProduct,SpecialLinearGroup.coeMonoidHom_apply,List.map_ofFn,
      Function.comp_def,rectSL,depthSL] using hm
  have hh' : (List.ofFn (fun s => 1+rect col r s v)).prod=
      1+(List.ofFn (fun s => rect col r s v)).sum := by
    simpa only [List.map_ofFn,Function.comp_def] using hh
  exact hm'.trans hh' 

private theorem row_sum_entry (col : Fin N → Fin B) (r : Fin B)
    (v : SpecialLinearGroup (Fin N) F) (i j : Fin N) :
    (List.ofFn (fun s => rect col r s v)).sum i j=
      if col i=r ∧ r<col j then v i j else 0 := by
  classical
  rw [show (List.ofFn (fun s => rect col r s v)).sum=
      ∑ s : Fin B, rect col r s v by rw [List.sum_ofFn]]
  simp only [Matrix.sum_apply,rect]
  rw [Finset.sum_eq_single (col j)]
  · simp
  · intro s hs hne
    simp [hne,Ne.symm hne]
  · simp

/-- Actual full off-block unitriangular reconstruction. Decreasing source
blocks and increasing destination blocks preserve the noncommutative
product. Every factor uses only its two true coordinate blocks.
This is the next finite block-decomposition step for the class-width route. -/
theorem actual_strict_block_factorization
    (col : Fin N → Fin B) (hmono : Monotone col)
    (v : SpecialLinearGroup (Fin N) F)
    (hv : ∀ i j, ¬col i<col j → v i j=(1:Matrix (Fin N) (Fin N) F) i j) :
    ∃ a : Fin B → Fin B → SpecialLinearGroup (Fin N) F,
      (∀ r s, PartIISLnDisplacedClassWords.Supported
        {i | col i=r.rev ∨ col i=s} (a r s)) ∧
      (∀ r s, LayerDepth 1 ((a r s).val-1)) ∧
      orderedProduct (fun r => orderedProduct (fun s => a r s))=v := by
  classical
  let a : Fin B → Fin B → SpecialLinearGroup (Fin N) F := fun r s => rectSL col hmono r.rev s v
  let X : Fin B → Matrix (Fin N) (Fin N) F := fun r => (List.ofFn (fun s => rect col r.rev s v)).sum
  have hrow : ∀ r, (orderedProduct (fun s => a r s)).val=1+X r := by
    intro r;exact ordered_rect_row col hmono r.rev v
  have hX : (List.ofFn X).Pairwise (fun x y => x*y=0) := by
    rw [List.pairwise_ofFn]
    intro r r' hrr'
    ext i j
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro t ht
    dsimp only [X]
    rw [row_sum_entry,row_sum_entry]
    split_ifs with h h'
    · have ht' : r'.rev=r.rev ∨ r'.rev<r.rev := by
        right
        exact Fin.rev_lt_rev.mpr hrr'
      have hh : r'.rev≤r.rev := ht'.elim le_of_eq le_of_lt
      have he : col t=r'.rev := h'.1
      rw [he] at h
      exact False.elim (not_lt_of_ge hh h.2)
    all_goals simp
  have hsum : (List.ofFn X).sum=v.val-1 := by
    ext i j
    rw [show (List.ofFn X).sum=∑ r : Fin B, X r by rw [List.sum_ofFn]]
    simp only [Matrix.sum_apply,X]
    simp_rw [row_sum_entry]
    have hperm : (∑ r : Fin B, if col i=r.rev ∧ r.rev<col j then v i j else 0)=
        ∑ r : Fin B, if col i=r ∧ r<col j then v i j else 0 :=
      Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin B))
        (fun r : Fin B => if col i=r ∧ r<col j then v i j else (0:F))
    rw [hperm]
    rw [Finset.sum_eq_single (col i)]
    · by_cases h : col i<col j
      · have hne : i≠j := by intro he; subst j;exact lt_irrefl _ h
        simp [h,Matrix.sub_apply,Matrix.one_apply,hne]
      · simp [h,Matrix.sub_apply,hv i j h]
    · intro r hr hne;simp [hne,Ne.symm hne]
    · simp
  refine ⟨a,?_,?_,?_⟩
  · intro r s i j hij
    change (1+rect col r.rev s v) i j=_
    have hz : rect col r.rev s v i j=0 := by
      simp only [rect]
      split_ifs with h
      · rcases hij with hi | hj
        · exact False.elim (hi (Or.inl h.1))
        · exact False.elim (hj (Or.inr h.2.1))
      · rfl
    simp [hz]
  · intro r s
    simpa only [a,rectSL,depthSL,add_sub_cancel_left] using rect_depth col hmono r.rev s v
  · apply Subtype.ext
    have hm := map_list_prod (SpecialLinearGroup.coeMonoidHom : SpecialLinearGroup (Fin N) F →* Matrix (Fin N) (Fin N) F)
      (List.ofFn (fun r => orderedProduct (fun s => a r s)))
    have hf : (fun r => (orderedProduct (fun s => a r s)).val)=fun r => 1+X r := funext hrow
    simp only [SpecialLinearGroup.coeMonoidHom_apply,List.map_ofFn,Function.comp_def] at hm
    rw [hf] at hm
    have hp := product_one_add _ hX
    have hp' : (List.ofFn (fun r => 1+X r)).prod=1+(List.ofFn X).sum := by
      simpa only [List.map_ofFn,Function.comp_def] using hp
    rw [hsum,add_comm (1:Matrix (Fin N) (Fin N) F) (v.val-1),sub_add_cancel] at hp'
    exact hm.trans hp' 
private theorem depth_memU (a : SpecialLinearGroup (Fin N) F) :
    LayerDepth 1 (a.val-1) ↔ a∈SLnNormalizer.Uplus N F := by
  classical
  rw [SLnNormalizer.mem_Uplus_iff]
  constructor
  · intro h
    constructor
    · intro i j hij
      have hne : i≠j := by intro he; subst j;omega
      simpa only [Matrix.sub_apply,Matrix.one_apply,if_neg hne,sub_zero] using h i j (by omega)
    · intro i
      have hh := h i i (by omega)
      simpa only [Matrix.sub_apply,Matrix.one_apply,if_pos rfl,ite_true,sub_eq_zero] using hh
  · rintro ⟨hupper,hdiag⟩ i j hij
    by_cases h : i=j
    · subst j;simp [hdiag]
    · have hji : j.val < i.val := by have hn : i.val≠j.val := fun he => h (Fin.ext he);omega
      simp [hupper i j hji,Matrix.one_apply,h]

private def piece (col : Fin N → Fin B) (r : Fin B)
    (u : SpecialLinearGroup (Fin N) F) : Matrix (Fin N) (Fin N) F :=
  fun i j => if col i=r ∧ col j=r then (u.val-1) i j else 0
private theorem piece_depth (col : Fin N → Fin B) (r : Fin B)
    (u : SpecialLinearGroup (Fin N) F) (hu : LayerDepth 1 (u.val-1)) :
    LayerDepth 1 (piece col r u) := by
  intro i j hij
  simp only [piece]
  split_ifs <;> simp [hu i j hij]
private def pieceSL (col : Fin N → Fin B) (r : Fin B)
    (u : SpecialLinearGroup (Fin N) F) (hu : LayerDepth 1 (u.val-1)) :
    SpecialLinearGroup (Fin N) F := depthSL (piece col r u) (piece_depth col r u hu)
private def diagonalBlocks (col : Fin N → Fin B) (u : SpecialLinearGroup (Fin N) F)
    (hu : LayerDepth 1 (u.val-1)) : SpecialLinearGroup (Fin N) F :=
  depthSL (fun i j => if col i=col j then (u.val-1) i j else 0) (by
    intro i j hij;change (if col i=col j then (u.val-1) i j else 0)=0;split_ifs <;> simp [hu i j hij])
private theorem diagonalBlocks_entry (col : Fin N → Fin B) (u : SpecialLinearGroup (Fin N) F)
    (hu : LayerDepth 1 (u.val-1)) (i j : Fin N) :
    diagonalBlocks col u hu i j=if col i=col j then u i j else 0 := by
  classical
  change (1:Matrix (Fin N) (Fin N) F) i j+
    (if col i=col j then (u.val-1) i j else 0)=_
  by_cases hc : col i=col j
  · simp [hc,Matrix.sub_apply]
  · have hne : i≠j := fun he => hc (congrArg col he)
    simp [hc,Matrix.one_apply,hne]

private theorem diagonal_factorization (col : Fin N → Fin B)
    (u : SpecialLinearGroup (Fin N) F) (hu : LayerDepth 1 (u.val-1)) :
    orderedProduct (fun r => pieceSL col r u hu)=diagonalBlocks col u hu := by
  classical
  have hp : (List.ofFn (fun r => piece col r u)).Pairwise (fun x y => x*y=0) := by
    rw [List.pairwise_ofFn]
    intro r s hrs
    ext i j
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro t ht
    simp only [piece]
    split_ifs with h h'
    · have he : r=s := h.2.symm.trans h'.1
      exact False.elim (ne_of_lt hrs he)
    all_goals simp
  have hsum : (List.ofFn (fun r => piece col r u)).sum=
      fun i j => if col i=col j then (u.val-1) i j else 0 := by
    ext i j
    rw [List.sum_ofFn,Matrix.sum_apply]
    simp only [piece]
    rw [Finset.sum_eq_single (col i)]
    · simp [eq_comm]
    · intro r hr hne;simp [Ne.symm hne]
    · simp
  have hprod := product_one_add _ hp
  have hm := map_list_prod
    (SpecialLinearGroup.coeMonoidHom : SpecialLinearGroup (Fin N) F →* Matrix (Fin N) (Fin N) F)
    (List.ofFn (fun r => pieceSL col r u hu))
  apply Subtype.ext
  have hm' : (orderedProduct (fun r => pieceSL col r u hu)).val=
      (List.ofFn (fun r => 1+piece col r u)).prod := by
    simpa only [orderedProduct,SpecialLinearGroup.coeMonoidHom_apply,List.map_ofFn,
      Function.comp_def,pieceSL,depthSL] using hm
  have hprod' : (List.ofFn (fun r => 1+piece col r u)).prod=
      1+(List.ofFn (fun r => piece col r u)).sum := by
    simpa only [List.map_ofFn,Function.comp_def] using hprod
  rw [hsum] at hprod'
  exact hm'.trans hprod'

private theorem diagonal_inverse_off (col : Fin N → Fin B)
    (u : SpecialLinearGroup (Fin N) F) (hu : LayerDepth 1 (u.val-1))
    (i j : Fin N) (hij : col i≠col j) :
    ((diagonalBlocks col u hu)⁻¹) i j=0 := by
  classical
  let D := diagonalBlocks col u hu
  let P : Matrix (Fin N) (Fin N) F := diagonal (fun t => if col t=col i then 1 else 0)
  have hcomm : D.val*P=P*D.val := by
    ext r s
    simp only [P,Matrix.mul_diagonal,Matrix.diagonal_mul]
    dsimp only [D]
    rw [diagonalBlocks_entry]
    by_cases h : col r=col s
    · simp [h]
    · simp [h]
  have hDD : D.val*(D⁻¹).val=1 := congrArg Subtype.val (mul_inv_cancel D)
  have hDD' : (D⁻¹).val*D.val=1 := congrArg Subtype.val (inv_mul_cancel D)
  have hInv : (D⁻¹).val*P=P*(D⁻¹).val := by
    calc
      _ = ((D⁻¹).val*P)*(D.val*(D⁻¹).val) := by rw [hDD,mul_one]
      _ = (D⁻¹).val*(P*D.val)*(D⁻¹).val := by simp only [mul_assoc]
      _ = (D⁻¹).val*(D.val*P)*(D⁻¹).val := by rw [hcomm]
      _ = _ := by rw [← mul_assoc (D⁻¹).val D.val P,hDD',one_mul]
  have he := congrArg (fun A : Matrix (Fin N) (Fin N) F => A i j) hInv
  simpa only [P,Matrix.mul_diagonal,Matrix.diagonal_mul,if_neg (Ne.symm hij),
    if_pos rfl,ite_true,mul_zero,one_mul] using he.symm

/-- The strict-block hypotheses above are DERIVED from each actual upper
target, by removing its constructed diagonal-block matrix. -/
private theorem strict_after_diagonal (col : Fin N → Fin B) (hmono : Monotone col)
    (u : SpecialLinearGroup (Fin N) F) (hu : LayerDepth 1 (u.val-1)) :
    ∀ i j, ¬col i<col j →
      ((diagonalBlocks col u hu)⁻¹*u) i j=(1:Matrix (Fin N) (Fin N) F) i j := by
  classical
  let D := diagonalBlocks col u hu
  have hD : LayerDepth 1 (D.val-1) := by
    change LayerDepth 1 ((1+_)-1)
    rw [add_sub_cancel_left]
    intro i j hij;change (if col i=col j then (u.val-1) i j else 0)=0;split_ifs <;> simp [hu i j hij]
  have hV := (SLnNormalizer.Uplus N F).mul_mem
    ((SLnNormalizer.Uplus N F).inv_mem ((depth_memU D).mp hD)) ((depth_memU u).mp hu)
  intro i j hij
  by_cases h : col i=col j
  · have he : (D⁻¹*u) i j=(D⁻¹*D) i j := by
      simp only [SpecialLinearGroup.coe_mul,Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hti : col t=col i
      · rw [diagonalBlocks_entry,if_pos (hti.trans h)]
      · rw [diagonal_inverse_off col u hu i t (Ne.symm hti),zero_mul,zero_mul]
    rw [he,inv_mul_cancel]
    rfl
  · have hji : j.val < i.val := by
      by_contra hh
      have hle : i≤j := by change i.val≤j.val;omega
      have hcol := hmono hle
      exact hij (lt_of_le_of_ne hcol h)
    have hne : i≠j := fun he => h (congrArg col he)
    simp only [Matrix.one_apply,if_neg hne]
    exact ((SLnNormalizer.mem_Uplus_iff _).mp hV).1 i j hji

/-- ALL coordinates of an arbitrary upper target: B diagonal-block factors
and B squared actual rectangular factors. The order is exact. Each factor
is supported on one or two genuine blocks, ready for actual class transport.
No diagonal/strict-block/reconstruction premise remains. -/
theorem actual_upper_block_factorization
    (col : Fin N → Fin B) (hmono : Monotone col)
    (u : SpecialLinearGroup (Fin N) F) (hu : LayerDepth 1 (u.val-1)) :
    ∃ a : Fin B → SpecialLinearGroup (Fin N) F,
      ∃ b : Fin B → Fin B → SpecialLinearGroup (Fin N) F,
      (∀ r, PartIISLnDisplacedClassWords.Supported {i | col i=r} (a r)) ∧
      (∀ r s, PartIISLnDisplacedClassWords.Supported {i | col i=r.rev ∨ col i=s} (b r s)) ∧
      (∀ r, LayerDepth 1 ((a r).val-1)) ∧
      (∀ r s, LayerDepth 1 ((b r s).val-1)) ∧
      orderedProduct a*orderedProduct (fun r => orderedProduct (b r))=u := by
  let D := diagonalBlocks col u hu
  obtain ⟨b,hb,hdepthb,hprod⟩ := actual_strict_block_factorization col hmono (D⁻¹*u)
    (strict_after_diagonal col hmono u hu)
  refine ⟨fun r => pieceSL col r u hu,b,?_,hb,?_,hdepthb,?_⟩
  · intro r i j hij
    change (1+piece col r u) i j=_
    have hz : piece col r u i j=0 := by
      simp only [piece]
      split_ifs with h
      · rcases hij with hi | hj
        · exact False.elim (hi h.1)
        · exact False.elim (hj h.2)
      · rfl
    simp [hz]
  · intro r
    simpa only [pieceSL,depthSL,add_sub_cancel_left] using piece_depth col r u hu
  · rw [diagonal_factorization,hprod]
    change D*(D⁻¹*u)=u
    group
private def chunk80 (s : ℕ) (hs : 0 < s) (hN : N≤80*s) : Fin N → Fin 80 :=
  fun i => ⟨i.val/s,(Nat.div_lt_iff_lt_mul hs).mpr (by have hi := i.isLt;omega)⟩
private theorem chunk80_mono (s : ℕ) (hs : 0 < s) (hN : N≤80*s) :
    Monotone (chunk80 s hs hN) := by
  intro i j hij
  change i.val/s≤j.val/s
  exact Nat.div_le_div_right hij
private theorem chunk80_card (s : ℕ) (hs : 0 < s) (hN : N≤80*s) (r : Fin 80) :
    Nat.card {i : Fin N // chunk80 s hs hN i=r}≤s := by
  classical
  let f : {i : Fin N // chunk80 s hs hN i=r} → Fin s :=
    fun i => ⟨i.val.val%s,Nat.mod_lt _ hs⟩
  have hf : Function.Injective f := by
    intro i j he
    have hi := congrArg Fin.val i.prop
    have hj := congrArg Fin.val j.prop
    change i.val.val/s=r.val at hi
    change j.val.val/s=r.val at hj
    have hm := congrArg Fin.val he
    change i.val.val%s=j.val.val%s at hm
    have h1 := Nat.div_add_mod i.val.val s
    have h2 := Nat.div_add_mod j.val.val s
    rw [hi] at h1
    rw [hj,← hm] at h2
    apply Subtype.ext
    exact Fin.ext (h1.symm.trans h2)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

/-- A CONSTANT number of genuinely small supported factors for every
actual upper target. The 80 consecutive chunks and both support-cardinality
bounds are constructed from N<=80s. Identity slots pad the exact length
80+80²=6480; no factor count depends on rank or target. -/
theorem actual_upper_eighty_chunk_factorization
    (s : ℕ) (hs : 0 < s) (hN : N≤80*s)
    (u : SpecialLinearGroup (Fin N) F) (hu : LayerDepth 1 (u.val-1)) :
    ∃ T : Fin 80 → Set (Fin N), ∃ U : Fin 80 → Fin 80 → Set (Fin N),
      ∃ a : Fin 80 → SpecialLinearGroup (Fin N) F,
      ∃ b : Fin 80 → Fin 80 → SpecialLinearGroup (Fin N) F,
      (∀ r, Nat.card (T r)≤s) ∧ (∀ r t, Nat.card (U r t)≤2*s) ∧
      (∀ r, PartIISLnDisplacedClassWords.Supported (T r) (a r)) ∧
      (∀ r t, PartIISLnDisplacedClassWords.Supported (U r t) (b r t)) ∧
      (∀ r, LayerDepth 1 ((a r).val-1)) ∧
      (∀ r t, LayerDepth 1 ((b r t).val-1)) ∧
      orderedProduct a*orderedProduct (fun r => orderedProduct (b r))=u := by
  classical
  let col := chunk80 s hs hN
  obtain ⟨a,b,ha,hb,hda,hdb,hprod⟩ := actual_upper_block_factorization col (chunk80_mono s hs hN) u hu
  refine ⟨fun r => {i | col i=r},fun r t => {i | col i=r.rev ∨ col i=t},
    a,b,?_,?_,ha,hb,hda,hdb,hprod⟩
  · intro r;exact chunk80_card s hs hN r
  · intro r t
    have h1 := chunk80_card s hs hN r.rev
    have h2 := chunk80_card s hs hN t
    have hc := Fintype.card_subtype_or (fun i : Fin N => col i=r.rev) (fun i : Fin N => col i=t)
    simp only [Nat.card_eq_fintype_card] at h1 h2 ⊢
    change Fintype.card {i : Fin N // col i=r.rev}≤s at h1
    change Fintype.card {i : Fin N // col i=t}≤s at h2
    change Fintype.card {i : Fin N // col i=r.rev ∨ col i=t}≤2*s
    omega

/-- The printed large-rank shape SUPPLIES the 80-chunk hypothesis and
the local displacement size d=2*(L/8), with no extra rank-width premise. -/
theorem actual_long_cycle_chunk_bounds (q r k : ℕ) (hp : k+2≤q*r)
    (hL : 16≤q*r+1) :
    0<(q*r+1)/8 ∧
      k+4*(q*r+1)+2≤80*((q*r+1)/8) ∧
      4*(2*((q*r+1)/8))≤q*r+1 := by
  let L := q*r+1
  let s := L/8
  have hs : 2≤s := (Nat.le_div_iff_mul_le (by decide : 0 < 8)).mpr hL
  have hm := Nat.div_add_mod L 8
  have hrem := Nat.mod_lt L (by decide : 0 < 8)
  have hshape : k+4*L+2≤5*L-1 := by dsimp only [L];omega
  dsimp only [s,L] at hs hm hrem hshape ⊢
  omega
end NikolovSegal.PartIISLnBlockFactorization
