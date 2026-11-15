/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/KingClosedForm
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/KingClosedForm
   mirror-E: none(waiver:structural-combinatorics)
   anchors: []
   utility: none
   digest: Closed counts of one-defect king colourings in arbitrary dimensions. -/
/-
admission_basis: open-problem-resolution (#30641; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229571.result, HardinA229573.result, HardinA229574.result, HardinA229575.result, HardinA229576.result, HardinA229577.result, HardinA229578.result)
normal_exists_unique: proof_shape=bind-only; consumers=KingClosedForm.normal_unique,KingClosedForm.normalize,KingClosedForm.normalize_spec
normalize: proof_shape=bind-only; consumers=KingClosedForm.canonical_transpose,KingClosedForm.canonical_transpose_twice,KingClosedForm.normalize_spec
normalize_spec: proof_shape=bind-only; consumers=KingClosedForm.canonical_transpose,KingClosedForm.canonical_transpose_twice
normal_unique: proof_shape=bind-only; consumers=KingClosedForm.canonical_transpose_twice
transpose_one: proof_shape=bind-only; consumers=KingClosedForm.canonical_transpose
canonical_transpose: proof_shape=bind-only; consumers=KingClosedForm.canonical_transpose_twice,KingClosedForm.symmetry
canonical_transpose_twice: proof_shape=bind-only; consumers=KingClosedForm.symmetry
symmetry: proof_shape=bind-only; consumers=KingClosedForm.width_three
closed_form: proof_shape=bind-only; consumers=HardinA229574.result,HardinA229575.result,HardinA229576.result,HardinA229577.result,KingClosedForm.diagonal_closed
width_two: proof_shape=bind-only; consumers=HardinA229578.result,KingClosedForm.width_three
width_three: proof_shape=bind-only; consumers=HardinA229573.result,KingClosedForm.diagonal_closed
diagonal_closed: proof_shape=bind-only; consumers=HardinA229571.result
-/
import D5.S3.StatisticalMechanics.Potts.KingDefects.KingDiagonal
import D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts

/-! Counts from the exact horizontal and diagonal slot decompositions. -/
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.KingClosedForm
open KingGrid KingDifference KingDiagonal KingHorizontal

private theorem normal_exists_unique {n k : ℕ} (f : Cell n k → Fin 4) :
    ∃! g, normal g ∧ ∃ p : Equiv.Perm (Fin 4), g = p ∘ f := by
  obtain ⟨Q,⟨hQ,p,hp⟩,hu⟩ :=
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.canonical_exists_unique
      (fun i : Fin (n*k) => f (finProdFinEquiv.symm i))
  let g : Cell n k → Fin 4 := fun c => Q (finProdFinEquiv c)
  refine ⟨g,⟨?_,p,?_⟩,?_⟩
  · change Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
      (fun i => Q (finProdFinEquiv (finProdFinEquiv.symm i)))
    simpa only [Equiv.apply_symm_apply] using hQ
  · funext c
    change Q (finProdFinEquiv c) = p (f c)
    rw [hp]
    change p (f (finProdFinEquiv.symm (finProdFinEquiv c))) = _
    rw [Equiv.symm_apply_apply]
  · rintro h ⟨hh,q,hq⟩
    have he := hu (fun i : Fin (n*k) => h (finProdFinEquiv.symm i))
      ⟨hh,q,by simp [hq,Function.comp_def]⟩
    funext c
    have he' := congrFun he (finProdFinEquiv c)
    change h (finProdFinEquiv.symm (finProdFinEquiv c)) = g c at he'
    rwa [Equiv.symm_apply_apply] at he'

private noncomputable def normalize {n k : ℕ} (f : Cell n k → Fin 4) :=
  Classical.choose (normal_exists_unique f)

private theorem normalize_spec {n k : ℕ} (f : Cell n k → Fin 4) :
    normal (normalize f) ∧ ∃ p : Equiv.Perm (Fin 4), normalize f = p ∘ f :=
  (Classical.choose_spec (normal_exists_unique f)).1

private theorem normal_unique {n k : ℕ} (f g : Cell n k → Fin 4)
    (hf : normal f) (hg : normal g) (p : Equiv.Perm (Fin 4)) (hp : g = p ∘ f) : g=f := by
  obtain ⟨u,hu,uniq⟩ := normal_exists_unique f
  exact (uniq g ⟨hg,p,hp⟩).trans (uniq f ⟨hf,Equiv.refl _,rfl⟩).symm

private theorem transpose_one {n k : ℕ} (f : Cell n k → Fin 4)
    (hf : OneDefect f) : OneDefect (transpose f) := by
  obtain ⟨e,he,hu⟩ := (oneDefect_iff f).mp hf
  apply (oneDefect_iff _).mpr
  refine ⟨transposeEdge e,(transpose_mono f e).mpr he,?_⟩
  intro a ha
  obtain ⟨d,rfl⟩ := transposeEdge.surjective a
  exact congrArg transposeEdge (hu d ((transpose_mono f d).mp ha))

private noncomputable def canonical_transpose {n k : ℕ}
    (f : {f : Cell n k → Fin 4 // OneDefect f ∧ normal f}) :
    {g : Cell k n → Fin 4 // OneDefect g ∧ normal g} := by
  refine ⟨normalize (transpose f.val),?_,(normalize_spec _).1⟩
  obtain ⟨p,hp⟩ := (normalize_spec (transpose f.val)).2
  rw [hp]
  simpa only [OneDefect,mono,Function.comp_apply,p.injective.eq_iff] using
    transpose_one f.val f.property.1

private theorem canonical_transpose_twice {n k : ℕ}
    (f : {f : Cell n k → Fin 4 // OneDefect f ∧ normal f}) :
    canonical_transpose (canonical_transpose f) = f := by
  apply Subtype.ext
  have hp := normalize_spec (transpose f.val)
  have hq := normalize_spec (transpose (canonical_transpose f).val)
  obtain ⟨p,hp⟩ := hp.2
  obtain ⟨q,hq⟩ := hq.2
  apply normal_unique f.val _ f.property.2
    (canonical_transpose (canonical_transpose f)).property.2 (p.trans q)
  change normalize (transpose (canonical_transpose f).val) = _
  rw [hq]
  have he : (canonical_transpose f).val = normalize (transpose f.val) := rfl
  rw [he,hp]
  rfl

private theorem symmetry (n k : ℕ) : T n k = T k n := by
  classical
  have h (a b : ℕ) : T a b =
      Nat.card {f : Cell a b → Fin 4 // OneDefect f ∧ normal f} := by
    simp [T,Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [h,h]
  exact Nat.card_congr {
    toFun := canonical_transpose
    invFun := canonical_transpose
    left_inv := canonical_transpose_twice
    right_inv := canonical_transpose_twice }

theorem closed_form (n k : ℕ) (hn : 4 ≤ n) (hk : 4 ≤ k) :
    4 * (T n k : ℤ) =
      ((n : ℤ)*k-n+6*k+12)*2^n + ((n : ℤ)*k-k+6*n+12)*2^k +
        16*(n : ℤ)*k-64*n-64*k-32 := by
  obtain ⟨a, rfl⟩ : ∃ a, n = a + 4 := ⟨n-4, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, k = b + 4 := ⟨k-4, by omega⟩
  have h := count_by_kind (a+3) (b+3) (by omega) (by omega)
  have h₁ := horizontal_sum a (b+1)
  have h₂ := horizontal_sum b (a+1)
  have hd := N_D_closed (a+3) (b+3) (by omega) (by omega)
  have h' := congrArg (fun x : ℕ => (x : ℤ)) h
  have h₁' := congrArg (fun x : ℕ => (x : ℤ)) h₁
  have h₂' := congrArg (fun x : ℕ => (x : ℤ)) h₂
  push_cast at h' h₁' h₂' hd ⊢
  simp only [pow_succ] at h' h₁' h₂' hd ⊢
  nlinarith [h', h₁', h₂', hd]

theorem width_two (n : ℕ) (hn : 2 ≤ n) :
    (T n 2 : ℤ) = (7*(n : ℤ)-8)*2^(n-2) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 2 := ⟨n-2, by omega⟩
  have h := count_by_kind (p+1) 1 (by omega) (by omega)
  rw [horizontal_two_columns, horizontal_two_rows, N_D_two_columns] at h
  have h' := congrArg (fun x : ℕ => (x : ℤ)) h
  push_cast at h' ⊢
  simp only [pow_succ] at h' ⊢
  nlinarith [h']

theorem width_three (n : ℕ) (hn : 2 ≤ n) :
    4*(T n 3 : ℤ) = (3*(n : ℤ)+27)*2^n+44*n-116 := by
  by_cases h2 : n = 2
  · subst n
    rw [symmetry 2 3, width_two 3 (by omega)]
    norm_num
  by_cases h3 : n = 3
  · subst n
    have h := count_by_kind 2 2 (by omega) (by omega)
    have hh := horizontal_three_rows 1
    have hd := N_D_closed 2 2 (by omega) (by omega)
    norm_num at hh hd h ⊢
    have h' := congrArg (fun x : ℕ => (x : ℤ)) h
    have hh' := congrArg (fun x : ℕ => (x : ℤ)) hh
    push_cast at h' hh'
    omega
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + 4 := ⟨n-4, by omega⟩
    have h := count_by_kind (p+3) 2 (by omega) (by omega)
    have h₁ := horizontal_sum p 0
    have h₂ := horizontal_three_rows (p+2)
    have hd := N_D_closed (p+3) 2 (by omega) (by omega)
    have h' := congrArg (fun x : ℕ => (x : ℤ)) h
    have h₁' := congrArg (fun x : ℕ => (x : ℤ)) h₁
    have h₂' := congrArg (fun x : ℕ => (x : ℤ)) h₂
    push_cast at h' h₁' h₂' hd ⊢
    norm_num [pow_succ] at h' h₁' h₂' hd ⊢
    nlinarith [h', h₁', h₂', hd]

theorem diagonal_closed (n : ℕ) (hn : 3 ≤ n) :
    2*(T n n : ℤ) = ((n : ℤ)^2+5*n+12)*2^n+8*(n : ℤ)^2-64*n-16 := by
  by_cases h3 : n=3
  · subst n
    have h := width_three 3 (by omega)
    norm_num at h ⊢
    omega
  · have h := closed_form n n (by omega) (by omega)
    nlinarith [h]

#check @symmetry
#check @closed_form
#check @width_two
#check @width_three
#check @diagonal_closed
#print axioms diagonal_closed
#print axioms symmetry
#print axioms closed_form
#print axioms width_two
#print axioms width_three
end D5.S3.StatisticalMechanics.Potts.KingDefects.KingClosedForm
