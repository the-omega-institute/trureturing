/- GID: D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/SubcubicIdentification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual shared-port subcubic assembly with single-counted core and port vertices. -/

import D5.S3.Combinatorics.Graph.StarForming.SubcubicExact
import D5.S3.Combinatorics.Graph.StarForming.ClosedModule

/-! The J_r identification in SUBCUBIC_STAR_FORMING_GAPS and
EXACT_SUBCUBIC_COMPOSITION, subquorum-colorings
48728b42d39ab3de5de251c61da5a404ec418a69. A cell contains ten original
core vertices and one shared port. Original port zero of i is shared port i;
original port six of i is shared port next i. Thus ports are counted once. -/
namespace D5.S3.Combinatorics.Graph.StarForming.SubcubicIdentification
open StarFormingDissociationRefutation
open scoped BigOperators
variable {I : Type} [Fintype I] [DecidableEq I]

def neighbors (next : Equiv.Perm I) (x : I × Fin 11) : List (I × Fin 11) :=
  let i := x.1
  ![[(i,5),(i,6),(i,7)],[(i,7),(i,8),(i,9)],[(next i,10),(i,6),(i,8)],
    [(i,5),(i,8)],[(i,5),(i,9)],[(i,0),(i,3),(i,4)],[(i,0),(i,2)],
    [(i,0),(i,1)],[(i,1),(i,2),(i,3)],[(i,10),(i,1),(i,4)],
    [(i,9),(next.symm i,2)]] x.2

set_option maxRecDepth 8192 in
private theorem neighbor_symm (next : Equiv.Perm I) (x y : I × Fin 11) :
    y∈neighbors next x ↔ x∈neighbors next y := by
  rcases x with ⟨i,v⟩
  rcases y with ⟨j,w⟩
  fin_cases v <;> fin_cases w <;>
    simp [neighbors,eq_comm,Equiv.eq_symm_apply]

def graph (next : Equiv.Perm I) : SimpleGraph (I × Fin 11) where
  Adj x y := y∈neighbors next x
  symm := ⟨fun x y h => (neighbor_symm next x y).mp h⟩
  loopless := ⟨by
    rintro ⟨i,v⟩ h
    fin_cases v <;> simpa [neighbors] using h⟩

instance (next : Equiv.Perm I) : DecidableRel (graph next).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_∈_))

/-- Every original core degree is preserved; the identified port has degree two. -/
theorem degrees (next : Equiv.Perm I) (i : I) (v : Fin 11) :
    DegreeCapacity.degree (graph next) (i,v)=
      if v=3 ∨ v=4 ∨ v=6 ∨ v=7 ∨ v=10 then 2 else 3 := by
  have hn : ∀ v : Fin 11, (neighbors next (i,v)).Nodup := by
    intro v
    fin_cases v <;> simp [neighbors]
  have he : Finset.univ.filter ((graph next).Adj (i,v))=(neighbors next (i,v)).toFinset := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,List.mem_toFinset]
    rfl
  change (Finset.univ.filter ((graph next).Adj (i,v))).card=_
  rw [he,List.toFinset_card_of_nodup (hn v)]
  fin_cases v <;> simp [neighbors]

def core (i : I) (v : Fin 10) : I × Fin 11 := (i,v.castSucc)
def port (i : I) : I × Fin 11 := (i,10)
def coreSlice (S : Finset (I × Fin 11)) (i : I) : Finset (Fin 10) :=
  Finset.univ.filter (fun v => core i v∈S)
def slice (S : Finset (I × Fin 11)) (i : I) : Finset (Fin 11) :=
  Finset.univ.filter (fun v => (i,v)∈S)

private theorem core_injective (i : I) : Function.Injective (core i) := by
  intro v w h
  exact Fin.ext (congrArg (fun x : I × Fin 11 => x.2.val) h)

theorem core_edges (next : Equiv.Perm I) (i : I) (v w : Fin 10) :
    (graph next).Adj (core i v) (core i w) ↔ Subcubic.CoreAdj v w := by
  fin_cases v <;> fin_cases w <;>
    simp [graph,core,neighbors,Subcubic.CoreAdj,Subcubic.Adj,
      Subcubic.coreLabel,Subcubic.neighbors]

private theorem core_closed (next : Equiv.Perm I) (i : I) (v : Fin 10)
    (hv : ¬ Subcubic.attachment v) (x : I × Fin 11)
    (hx : (graph next).Adj (core i v) x) : ∃ w : Fin 10, x=core i w := by
  have hr : x.1=i ∧ x.2.val<10 := by
    rcases x with ⟨j,w⟩
    fin_cases v <;>
      simp [Subcubic.attachment,Subcubic.coreLabel] at hv <;>
      simp_all [graph,core,neighbors] <;> aesop
  refine ⟨⟨x.2.val,hr.2⟩,Prod.ext hr.1 ?_⟩
  exact Fin.ext rfl

private theorem core_cap (next : Equiv.Perm I) (S : Finset (I × Fin 11))
    (hS : IsMinimalStarForming (graph next) 2 S) (i : I) : (coreSlice S i).card≤6 := by
  obtain ⟨mask,hm⟩ := FiniteMasks.selection_mask (coreSlice S i)
  have hsel (v : Fin 10) : core i v∈S ↔ Subcubic.coreSelected mask v := by
    simpa [coreSlice,Subcubic.coreSelected] using (hm v).symm
  have hc : Subcubic.coreCard mask=(coreSlice S i).card := by
    rw [Subcubic.coreCard,FiniteMasks.list_count]
    congr 1
    ext v
    simpa [Subcubic.coreSelected] using hm v
  have hb := Subcubic.ambient_core_cap (graph next).Adj (·∈S) (core i) mask
    (fun _ _ h => (graph next).adj_symm h)
    (fun _ _ h => core_injective i h) (core_edges next i) hsel
    (core_closed next i) ((regular_minimal_iff _ _).mpr hS)
  omega

/-- The port term is a single indicator, never one contribution from each block. -/
theorem card_slice (S : Finset (I × Fin 11)) (i : I) :
    (slice S i).card=(coreSlice S i).card+(if port i∈S then 1 else 0) := by
  classical
  calc
    (slice S i).card = ∑ v : Fin 11, if (i,v)∈S then 1 else 0 := by simp [slice]
    _ = _ := by
      rw [Fin.sum_univ_castSucc]
      simp [coreSlice,core,port]
      rfl

/-- The actual ambient ten-core theorem gives the full shared-port SF upper
bound for every finite index permutation, before any even-cycle restriction. -/
theorem sf_upper (next : Equiv.Perm I) : SF (graph next) 2≤7*Fintype.card I := by
  classical
  apply Finset.sup_le
  intro S hS
  have hs := (Finset.mem_filter.mp hS).2
  rw [ClosedModule.card_fibers]
  calc
    ∑ i : I, (Finset.univ.filter (fun v => (i,v)∈S)).card ≤ ∑ _i : I,7 := by
      apply Finset.sum_le_sum
      intro i _
      have hc := core_cap next S hs i
      have he := card_slice S i
      change (slice S i).card≤7
      split_ifs at he <;> omega
    _ = _ := by simp [Nat.mul_comm]

def forming (x : I × Fin 11) : Prop := x.2∈([0,3,4,5,6,7,10] : List (Fin 11))
instance (x : I × Fin 11) : Decidable (forming x) := inferInstanceAs (Decidable (_∈_))

private theorem twoAt_lists (next : Equiv.Perm I) (S : I × Fin 11 → Prop)
    (x : I × Fin 11) : Regular.TwoAt (graph next).Adj S x ↔
    (∃ a∈neighbors next x, ∃ b∈neighbors next x, S a ∧ S b ∧ a≠b) ∨
    (∃ c∈neighbors next x, S c ∧ ∃ l∈neighbors next c, S l) := by
  unfold Regular.TwoAt graph
  aesop

private theorem forming_forms (next : Equiv.Perm I) :
    Regular.Forms (graph next).Adj forming := by
  rintro ⟨i,v⟩ hv
  rw [twoAt_lists]
  fin_cases v <;> simp [forming] at hv
  · exact Or.inr ⟨(i,7),by simp [neighbors],by simp [forming],
      (i,0),by simp [neighbors],by simp [forming]⟩
  · exact Or.inl ⟨(next i,10),by simp [neighbors],(i,6),by simp [neighbors],
      by simp [forming],by simp [forming],by simp⟩
  · exact Or.inr ⟨(i,3),by simp [neighbors],by simp [forming],
      (i,5),by simp [neighbors],by simp [forming]⟩
  · exact Or.inl ⟨(i,10),by simp [neighbors],(i,4),by simp [neighbors],
      by simp [forming],by simp [forming],by simp⟩

def failure (x : I × Fin 11) : I × Fin 11 :=
  (x.1, ![1,0,0,8,9,8,2,1,0,0,10] x.2)

set_option maxRecDepth 8192 in
private theorem forming_failures (next : Equiv.Perm I) : ∀ d : I × Fin 11, forming d →
    ¬ (forming (failure d) ∧ failure d≠d) ∧
    ¬ Regular.TwoAt (graph next).Adj (fun x => forming x ∧ x≠d) (failure d) := by
  rintro ⟨i,v⟩ hv
  rw [twoAt_lists]
  fin_cases v <;>
    simp [forming,failure,neighbors,Prod.mk.injEq] at hv ⊢ <;> aesop

/-- The actual seven-per-cell selection is minimal for arbitrary finite
permutations; its certificate uses the identified ports only once. -/
theorem forming_minimal (next : Equiv.Perm I) :
    IsMinimalStarForming (graph next) 2 (Finset.univ.filter forming) := by
  apply (regular_minimal_iff _ _).mp
  simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using
    Subcubic.minimal_of_deletion_failures (graph next).Adj forming
      (forming_forms next) (fun d hd => ⟨failure d,forming_failures next d hd⟩)

/-- Full SF attainment for the actual shared-port graph, without an evenness
or nonempty premise. The cyclic beta theorem has its own restrictions. -/
theorem sf_exact (next : Equiv.Perm I) : SF (graph next) 2=7*Fintype.card I := by
  classical
  apply le_antisymm (sf_upper next)
  have hc : (Finset.univ.filter (forming : I × Fin 11 → Prop)).card=7*Fintype.card I := by
    rw [ClosedModule.card_fibers]
    have hlocal : (Finset.univ.filter (fun v : Fin 11 =>
      v∈([0,3,4,5,6,7,10] : List (Fin 11)))).card=7 := by decide +kernel
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,forming,hlocal,
      Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.mul_comm]
  rw [← hc]
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,forming_minimal next⟩)

end D5.S3.Combinatorics.Graph.StarForming.SubcubicIdentification
