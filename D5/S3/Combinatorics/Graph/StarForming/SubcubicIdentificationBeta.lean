/- GID: D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual dissociation accounting for shared-port subcubic assemblies. -/

import D5.S3.Combinatorics.Graph.StarForming.SubcubicIdentification
import D5.S3.Combinatorics.Graph.StarForming.DisjointUnion

/-! The single-counted shared-port dissociation argument in
EXACT_SUBCUBIC_COMPOSITION, subquorum-colorings
48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0.
The original twelve-vertex port-state cap is reused unchanged. -/
namespace D5.S3.Combinatorics.Graph.StarForming.SubcubicIdentificationBeta
open StarFormingDissociationRefutation SubcubicIdentification
open scoped BigOperators
variable {I : Type} [Fintype I] [DecidableEq I]

def label (next : Equiv.Perm I) (i : I) (v : Fin 12) : I × Fin 11 :=
  (if v=6 then next i else i, ![10,0,1,2,3,4,10,5,6,7,8,9] v)

set_option maxRecDepth 8192 in
private theorem label_injective (next : Equiv.Perm I) (nf : ∀ i, next i≠i) (i : I) :
    Function.Injective (label next i) := by
  intro v w h
  have hn := nf i
  fin_cases v <;> fin_cases w <;> simp [label,Prod.mk.injEq,hn,Ne.symm hn] at h ⊢

set_option maxRecDepth 8192 in
private theorem label_edges (next : Equiv.Perm I) (nf : ∀ i, next i≠i)
    (i : I) (v w : Fin 12) :
    (graph next).Adj (label next i v) (label next i w) ↔ Subcubic.Adj v w := by
  have hn := nf i
  have hn' : next.symm i≠i := by
    intro h
    have hh := congrArg next h
    simp only [Equiv.apply_symm_apply] at hh
    exact hn hh.symm
  fin_cases v <;> fin_cases w <;>
    simp [label,graph,neighbors,Subcubic.Adj,Subcubic.neighbors,hn,hn',Ne.symm hn,Ne.symm hn']

def blockSlice (next : Equiv.Perm I) (S : Finset (I × Fin 11)) (i : I) : Finset (Fin 12) :=
  Finset.univ.filter (fun v => label next i v∈S)

def ports (S : Finset (I × Fin 11)) : Finset I := Finset.univ.filter (fun i => port i∈S)

def touched (next : Equiv.Perm I) (S : Finset (I × Fin 11)) : Finset I :=
  Finset.univ.filter (fun i => port i∈S ∨ port (next i)∈S)

private theorem block_independent (next : Equiv.Perm I) (nf : ∀ i, next i≠i)
    (S : Finset (I × Fin 11)) (hS : IsKIndependent (graph next) 2 S) (i : I) :
    IsKIndependent Subcubic.graph 2 (blockSlice next S i) := by
  apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
  intro c hc a ha b hb hca hcb
  apply label_injective next nf i
  exact (SubQuorum.DoubleStarGrafting.independent_iff _ _).mp hS
    (label next i c) (Finset.mem_filter.mp hc).2
    (label next i a) (Finset.mem_filter.mp ha).2
    (label next i b) (Finset.mem_filter.mp hb).2
    ((label_edges next nf i c a).mpr hca) ((label_edges next nf i c b).mpr hcb)

/-- Every actual block slice obeys the complete original port-state cap. -/
theorem block_cap (next : Equiv.Perm I) (nf : ∀ i, next i≠i)
    (S : Finset (I × Fin 11)) (hS : IsKIndependent (graph next) 2 S) (i : I) :
    (blockSlice next S i).card≤6+(if i∈touched next S then 1 else 0) := by
  classical
  obtain ⟨mask,hm⟩ := FiniteMasks.selection_mask (blockSlice next S i)
  have he : Subcubic.maskSet mask=blockSlice next S i := by
    ext v
    simp [Subcubic.maskSet,Subcubic.membership,hm]
  have hi : Subcubic.Dissociation mask := (Subcubic.mask_dissociation_iff mask).mpr
    (he.symm ▸ block_independent next nf S hS i)
  have hc : Subcubic.card mask=(blockSlice next S i).card := by
    rw [Subcubic.card,FiniteMasks.list_count]
    exact congrArg Finset.card he
  have hp0 : Subcubic.membership mask 0=true ↔ port i∈S := by
    change mask.val.testBit 0=true ↔ label next i 0∈S
    exact (hm 0).trans ⟨fun h => (Finset.mem_filter.mp h).2,
      fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
  have hp6 : Subcubic.membership mask 6=true ↔ port (next i)∈S := by
    change mask.val.testBit 6=true ↔ label next i 6∈S
    exact (hm 6).trans ⟨fun h => (Finset.mem_filter.mp h).2,
      fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
  have hb := Subcubic.dissociation_port_cap mask hi
  rw [hc] at hb
  simpa [touched,hp0,hp6] using hb

private theorem block_card (next : Equiv.Perm I) (S : Finset (I × Fin 11)) (i : I) :
    (blockSlice next S i).card=(coreSlice S i).card+
      (if port i∈S then 1 else 0)+(if port (next i)∈S then 1 else 0) := by
  classical
  have hb : (blockSlice next S i).card=∑ v : Fin 12, if label next i v∈S then 1 else 0 := by
    simp [blockSlice]
  have hc : (coreSlice S i).card=∑ v : Fin 10, if core i v∈S then 1 else 0 := by
    simp [coreSlice]
  rw [hb,hc]
  simp only [Fin.sum_univ_succ]
  simp [label,core,port]
  let c (v : Fin 11) : ℕ := if (i,v)∈S then 1 else 0
  let q : ℕ := if (next i,10)∈S then 1 else 0
  change c 10+(c 0+(c 1+(c 2+(c 3+(c 4+(q+(c 5+(c 6+(c 7+(c 8+c 9)))))))))) =
    (c 0+(c 1+(c 2+(c 3+(c 4+(c 5+(c 6+(c 7+(c 8+c 9)))))))))+c 10+q
  omega

/-- Each actual shared port is counted twice in the block sum and once globally. -/
theorem block_sum (next : Equiv.Perm I) (S : Finset (I × Fin 11)) :
    ∑ i : I, (blockSlice next S i).card=S.card+(ports S).card := by
  classical
  have he := ClosedModule.card_fibers S
  have hs : ∀ i, (Finset.univ.filter (fun v => (i,v)∈S)).card=(slice S i).card :=
    fun _ => rfl
  simp_rw [hs,card_slice] at he
  have ht : ∑ i : I, (if port i∈S then 1 else 0)=(ports S).card := by simp [ports]
  have hn : ∑ i : I, (if port (next i)∈S then 1 else 0)=(ports S).card := by
    exact (Equiv.sum_comp next (fun j => if port j∈S then (1 : ℕ) else 0)).trans ht
  simp_rw [block_card]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,ht,hn]
  rw [Finset.sum_add_distrib,ht] at he
  omega

private theorem touched_le_twice (next : Equiv.Perm I) (S : Finset (I × Fin 11)) :
    (touched next S).card≤2*(ports S).card := by
  classical
  have hpoint (i : I) : (if i∈touched next S then (1 : ℕ) else 0)≤
      (if port i∈S then 1 else 0)+(if port (next i)∈S then 1 else 0) := by
    by_cases h : port i∈S <;> by_cases h' : port (next i)∈S <;> simp [touched,h,h']
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  rw [Finset.sum_add_distrib,
    Equiv.sum_comp next (fun i => if port i∈S then (1 : ℕ) else 0)] at he
  simpa [ports,two_mul] using he

/-- The actual global dissociation upper bound uses each shared-port credit once. -/
theorem beta_upper (next : Equiv.Perm I) (nf : ∀ i, next i≠i) :
    2*beta (graph next) 2≤13*Fintype.card I := by
  classical
  obtain ⟨S,hS,hcard⟩ := beta_attained (graph next) 2
  have hb : ∑ i : I, (blockSlice next S i).card≤
      6*Fintype.card I+(touched next S).card := by
    calc
      _ ≤ ∑ i : I, (6+(if i∈touched next S then 1 else 0)) :=
        Finset.sum_le_sum (fun i _ => block_cap next nf S hS i)
      _ = _ := by simp [Finset.sum_add_distrib,Nat.mul_comm]
  rw [block_sum] at hb
  have ht := touched_le_twice next S
  have hn := Finset.card_le_univ (touched next S)
  rw [hcard] at hb
  omega

def witness (phase : I → Bool) (x : I × Fin 11) : Prop :=
  if phase x.1 then x.2∈([1,2,3,4,6,7,10] : List (Fin 11))
  else x.2∈([0,3,4,6,8,9] : List (Fin 11))
instance (phase : I → Bool) (x : I × Fin 11) : Decidable (witness phase x) :=
  by unfold witness; infer_instance

/-- The global selection restricts to the unchanged original attaining
port-state witness in every actual twelve-vertex block. -/
theorem witness_restriction (next : Equiv.Perm I) (phase : I → Bool)
    (hp : ∀ i, phase (next i)= !(phase i)) (i : I) (v : Fin 12) :
    witness phase (label next i v) ↔
      Subcubic.membership (Subcubic.portWitness (phase i) (phase (next i))) v=true := by
  fin_cases v <;> cases hi : phase i <;>
    simp [label,witness,hp,hi,Subcubic.membership,Subcubic.portWitness] <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem witness_independent (next : Equiv.Perm I) (phase : I → Bool)
    (hp : ∀ i, phase (next i)= !(phase i)) :
    DissociationCover.Dissociates (graph next).Adj (witness phase) := by
  have hprev (i : I) : phase (next.symm i)= !(phase i) := by
    have hh := hp (next.symm i)
    rw [Equiv.apply_symm_apply] at hh
    cases h : phase i <;> cases h' : phase (next.symm i) <;> simp_all
  rintro ⟨i,v⟩ a b hv ha hb hva hvb
  fin_cases v <;> cases hi : phase i <;>
    simp [witness,graph,neighbors,hi] at hv hva hvb <;>
    aesop (add simp [witness,hp,hprev,hi])

private theorem phase_balance (next : Equiv.Perm I) (phase : I → Bool)
    (hp : ∀ i, phase (next i)= !(phase i)) :
    2*(∑ i : I, if phase i=true then (1 : ℕ) else 0)=Fintype.card I := by
  classical
  have he := Equiv.sum_comp next (fun i => if phase i=true then (1 : ℕ) else 0)
  have hpoint (i : I) : (if phase i=true then (1 : ℕ) else 0)+
      (if phase (next i)=true then 1 else 0)=1 := by
    cases hi : phase i <;> simp [hp,hi]
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hpoint i)
  rw [Finset.sum_add_distrib,he] at hs
  simpa [two_mul] using hs

/-- Alternating port phases give the actual dissociation attainment, with
only half of the shared ports selected. -/
theorem beta_exact (next : Equiv.Perm I) (nf : ∀ i, next i≠i) (phase : I → Bool)
    (hp : ∀ i, phase (next i)= !(phase i)) :
    2*beta (graph next) 2=13*Fintype.card I := by
  classical
  let S : Finset (I × Fin 11) := Finset.univ.filter (witness phase)
  have hs : IsKIndependent (graph next) 2 S := by
    apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
    intro v hv a ha b hb hva hvb
    exact witness_independent next phase hp v a b
      (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp ha).2
      (Finset.mem_filter.mp hb).2 hva hvb
  have hc : S.card=6*Fintype.card I+∑ i : I, if phase i=true then (1 : ℕ) else 0 := by
    rw [ClosedModule.card_fibers]
    have hlocal (i : I) : (Finset.univ.filter (fun v : Fin 11 => witness phase (i,v))).card=
        6+(if phase i=true then 1 else 0) := by
      cases hi : phase i <;> simp [witness,hi] <;> decide +kernel
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,hlocal]
    simp [Finset.sum_add_distrib,Nat.mul_comm]
  have hb : S.card≤beta (graph next) 2 :=
    Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hs⟩)
  have he := phase_balance next phase hp
  have hu := beta_upper next nf
  omega

end D5.S3.Combinatorics.Graph.StarForming.SubcubicIdentificationBeta
