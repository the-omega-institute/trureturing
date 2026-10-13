/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original finite-past guards have an exact finite directed graph presentation. -/

import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors

/-- Index zero is the most recent past letter; reversing indices gives the
chronological past word of the original memory graph. -/
abbrev MemoryVertex (n : ℕ) := Fin n → CuLetter

def memoryWindow (n : ℕ) (ω : ℤ → CuLetter) (i : ℤ) : MemoryVertex n :=
  fun k => ω (i - 1 - (k : ℕ))

def memoryShift {n : ℕ} (v : MemoryVertex n) (a : CuLetter) : MemoryVertex n :=
  fun k => if hk : k.val = 0 then a else v ⟨k.val-1,by omega⟩

noncomputable def memoryValue : {n : ℕ} → MemoryVertex n → ℝ → ℝ
  | 0, _, z => z
  | n+1, v, z => letterMap (v 0) (memoryValue (fun k : Fin n => v k.succ) z)

inductive MemorySide | lower | upper
  deriving DecidableEq, Repr

def memoryRun {n : ℕ} (v : MemoryVertex n) (a : CuLetter) (r : ℕ) : Prop :=
  a = .c ∧ ∀ k : Fin n, k.val+1 < r → v k = .c

noncomputable def memoryGuard {n : ℕ} (side : MemorySide) (K : ℕ) (d : ℝ)
    (v : MemoryVertex n) : Prop :=
  match side with
  | .lower => chi^(K-1)*d < memoryValue v 0
  | .upper => chi^(K-1)*d ≤ memoryValue v (hSide .high)

noncomputable def MemoryEdge {n : ℕ} (side : MemorySide) (K : ℕ) (d : ℝ)
    (v : MemoryVertex n) (a : CuLetter) (t : MemoryVertex n) : Prop :=
  t = memoryShift v a ∧ ¬ memoryRun v a (K+1) ∧
    (memoryRun v a K → memoryGuard side K d v)

noncomputable def BilateralGraphPath {n : ℕ} (side : MemorySide) (K : ℕ) (d : ℝ)
    (p : ℤ → MemoryVertex n) (ω : ℤ → CuLetter) : Prop :=
  ∀ i, MemoryEdge side K d (p i) (ω i) (p (i+1))

def UpperMemoryLanguage (n K : ℕ) (d : ℝ) : Set (ℤ → CuLetter) :=
  {ω | (∀ i : ℤ, ¬ ∀ k : Fin (K+1), ω (i+(k : ℕ))=.c) ∧
    ∀ i : ℤ, (∀ k : Fin K, ω (i-(k : ℕ))=.c) →
      chi^(K-1)*d ≤ finitePast ω i n (hSide .high)}

def MemoryLanguage (side : MemorySide) (n K : ℕ) (d : ℝ) : Set (ℤ → CuLetter) :=
  match side with
  | .lower => LowerMemoryLanguage n K d
  | .upper => UpperMemoryLanguage n K d

/-- The finite graph evaluates exactly the original n-letter seed composition. -/
theorem window_value (n : ℕ) (ω : ℤ → CuLetter) (i : ℤ) (z : ℝ) :
    memoryValue (memoryWindow n ω i) z = finitePast ω i n z := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    have tail : (fun k : Fin n => memoryWindow (n+1) ω i k.succ) =
        memoryWindow n ω (i-1) := by
      funext k
      dsimp [memoryWindow]
      congr 1
      push_cast
      ring
    rw [memoryValue,finitePast]
    have first : memoryWindow (n+1) ω i 0 = ω (i-1) := by simp [memoryWindow]
    rw [first,tail,ih]

theorem window_shift (n : ℕ) (ω : ℤ → CuLetter) (i : ℤ) :
    memoryWindow n ω (i+1) = memoryShift (memoryWindow n ω i) (ω i) := by
  funext k
  dsimp [memoryWindow,memoryShift]
  split_ifs with hk
  · congr 1; omega
  · congr 1; omega

/-- A bilateral path cannot carry an unrelated or arbitrary memory: its shift
equations recover every actual past letter, without a canonical-path premise. -/
theorem path_memory_reconstruction {n : ℕ} (p : ℤ → MemoryVertex n)
    (ω : ℤ → CuLetter) (shift : ∀ i, p (i+1) = memoryShift (p i) (ω i)) :
    p = memoryWindow n ω := by
  have recover : ∀ k : ℕ, ∀ hk : k < n, ∀ i : ℤ,
      p i ⟨k,hk⟩ = ω (i-1-(k : ℤ)) := by
    intro k
    induction k with
    | zero =>
      intro hk i
      have hs := congrFun (shift (i-1)) ⟨0,hk⟩
      simpa [memoryShift] using hs
    | succ k ih =>
      intro hk i
      have hs := congrFun (shift (i-1)) ⟨k+1,hk⟩
      simp only [show i-1+1=i by omega,memoryShift,
        show ¬ k+1=0 by omega,dif_neg,Nat.add_sub_cancel] at hs
      rw [ih (by omega) (i-1)] at hs
      convert hs using 1 <;> push_cast <;> ring
  funext i k
  exact recover k.val k.isLt i

theorem window_run (n r : ℕ) (positive : 0 < r) (bound : r ≤ n+1)
    (ω : ℤ → CuLetter) (i : ℤ) :
    memoryRun (memoryWindow n ω i) (ω i) r ↔
      ∀ k : Fin r, ω (i-(k : ℕ))=.c := by
  constructor
  · rintro ⟨current,past⟩ k
    by_cases hk : k.val=0
    · simpa [hk] using current
    · have h := past ⟨k.val-1,by omega⟩ (by change k.val-1+1 < r; omega)
      change ω (i-1-((k.val-1 : ℕ) : ℤ))=.c at h
      convert h using 1 <;> congr 1 <;> omega
  · intro run
    refine ⟨?_,?_⟩
    · simpa using run ⟨0,positive⟩
    · intro k hk
      have h := run ⟨k.val+1,hk⟩
      change ω (i-((k.val+1 : ℕ) : ℤ))=.c at h
      dsimp [memoryWindow]
      convert h using 1 <;> congr 1 <;> omega

/-- Reversing a finite run preserves the original forward forbidden-word test. -/
theorem forbidden_run_reversal (K : ℕ) (ω : ℤ → CuLetter) :
    (∀ i : ℤ, ¬ ∀ k : Fin (K+1), ω (i+(k : ℕ))=.c) ↔
    (∀ i : ℤ, ¬ ∀ k : Fin (K+1), ω (i-(k : ℕ))=.c) := by
  constructor
  · intro no i run
    apply no (i-(K : ℤ))
    intro k
    have h := run ⟨K-k.val,by omega⟩
    change ω (i-((K-k.val : ℕ) : ℤ))=.c at h
    convert h using 1 <;> congr 1 <;> omega
  · intro no i run
    apply no (i+(K : ℤ))
    intro k
    have h := run ⟨K-k.val,by omega⟩
    change ω (i+((K-k.val : ℕ) : ℤ))=.c at h
    convert h using 1 <;> congr 1 <;> omega

/-- Both original memory source models are precisely the labels of bilateral
paths on the same finite word carrier. The path is unique, not merely supplied. -/
theorem original_memory_graph_correspondence (side : MemorySide) (n K : ℕ)
    (d : ℝ) (positive : 0 < K) (memory : K ≤ n) (ω : ℤ → CuLetter) :
    ω ∈ MemoryLanguage side n K d ↔
      ∃! p : ℤ → MemoryVertex n, BilateralGraphPath side K d p ω := by
  have canonical : ω ∈ MemoryLanguage side n K d ↔
      BilateralGraphPath side K d (memoryWindow n ω) ω := by
    have cap := forbidden_run_reversal K ω
    have high := window_run n K positive (by omega) ω
    have over := window_run n (K+1) (by omega) (by omega) ω
    cases side <;>
      simp only [MemoryLanguage,LowerMemoryLanguage,UpperMemoryLanguage,Set.mem_setOf_eq,
        BilateralGraphPath,MemoryEdge,memoryGuard,window_value] <;>
      constructor
    · rintro ⟨hc,hg⟩ i
      exact ⟨window_shift n ω i,fun h => cap.mp hc i ((over i).mp h),
        fun h => hg i ((high i).mp h)⟩
    · intro path
      exact ⟨cap.mpr (fun i h => (path i).2.1 ((over i).mpr h)),
        fun i h => (path i).2.2 ((high i).mpr h)⟩
    · rintro ⟨hc,hg⟩ i
      exact ⟨window_shift n ω i,fun h => cap.mp hc i ((over i).mp h),
        fun h => hg i ((high i).mp h)⟩
    · intro path
      exact ⟨cap.mpr (fun i h => (path i).2.1 ((over i).mpr h)),
        fun i h => (path i).2.2 ((high i).mpr h)⟩
  constructor
  · intro member
    refine ⟨memoryWindow n ω,canonical.mp member,?_⟩
    intro p path
    exact path_memory_reconstruction p ω (fun i => (path i).1)
  · rintro ⟨p,path,_⟩
    have eq := path_memory_reconstruction p ω (fun i => (path i).1)
    rw [eq] at path
    exact canonical.mpr path

noncomputable def LiveVertex {n : ℕ} (side : MemorySide) (K : ℕ) (d : ℝ)
    (v : MemoryVertex n) : Prop :=
  ∃ p ω, BilateralGraphPath side K d p ω ∧ p 0 = v

/-- Only vertices appearing in actual bilateral paths are retained. A finite
walk may pass through transient bridges between different cyclic components. -/
noncomputable def RetainedWalk {n : ℕ} (side : MemorySide) (K : ℕ) (d : ℝ) :
    MemoryVertex n → List CuLetter → Prop
  | v, [] => LiveVertex side K d v
  | v, a :: w => LiveVertex side K d v ∧
      MemoryEdge side K d v a (memoryShift v a) ∧
      RetainedWalk side K d (memoryShift v a) w

/-- Join a genuine left past, one allowed edge and a genuine right future.
No irreducibility or canonical path completeness is assumed. -/
theorem prepend_bilateral_path {n : ℕ} (side : MemorySide) (K : ℕ) (d : ℝ)
    (v t : MemoryVertex n) (a : CuLetter)
    (left : LiveVertex side K d v)
    (p : ℤ → MemoryVertex n) (ω : ℤ → CuLetter)
    (right : BilateralGraphPath side K d p ω) (start : p 0 = t)
    (edge : MemoryEdge side K d v a t) :
    ∃ q ν, BilateralGraphPath side K d q ν ∧ q 0 = v ∧ ν 0 = a ∧
      ∀ i : ℤ, 0 ≤ i → ν (i+1) = ω i := by
  rcases left with ⟨l,μ,hl,hv⟩
  let q : ℤ → MemoryVertex n := fun i => if i ≤ 0 then l i else p (i-1)
  let ν : ℤ → CuLetter := fun i => if i < 0 then μ i else if i=0 then a else ω (i-1)
  refine ⟨q,ν,?_,?_,?_,?_⟩
  · intro i
    by_cases neg : i < 0
    · have next : i+1 ≤ 0 := by omega
      simpa [q,ν,neg,neg.le,next] using hl i
    · by_cases zero : i=0
      · subst i
        simpa [q,ν,hv,start] using edge
      · have pos : 0 < i := by omega
        have next : 0 < i+1 := by omega
        simpa [q,ν,not_le.mpr pos,not_le.mpr next,not_lt.mpr pos.le,zero,
          ne_of_gt next,show i+1-1=i by omega] using right (i-1)
  · simpa [q] using hv
  · simp [ν]
  · intro i hi
    simp [ν,show ¬ i+1<0 by omega,show i+1≠0 by omega]

/-- Every finite retained walk really has a two-sided extension, including the
empty walk and paths crossing transient bridges. -/
theorem retained_walk_extension {n : ℕ} (side : MemorySide) (K : ℕ) (d : ℝ)
    (v : MemoryVertex n) (w : List CuLetter)
    (walk : RetainedWalk side K d v w) :
    ∃ p ω, BilateralGraphPath side K d p ω ∧ p 0 = v ∧
      ∀ k : Fin w.length, ω (k : ℕ) = w[k] := by
  induction w generalizing v with
  | nil =>
    rcases walk with ⟨p,ω,hp,hv⟩
    exact ⟨p,ω,hp,hv,fun k => Fin.elim0 k⟩
  | cons a w ih =>
    rcases walk with ⟨live,edge,tail⟩
    rcases ih (memoryShift v a) tail with ⟨p,ω,hp,hv,hw⟩
    rcases prepend_bilateral_path side K d v (memoryShift v a) a live p ω hp hv edge
      with ⟨q,ν,hq,hv,first,rest⟩
    refine ⟨q,ν,hq,hv,?_⟩
    intro k
    by_cases zero : k.val=0
    · simpa [zero] using first
    · have hk : k.val-1 < w.length := by have := k.isLt; simp at this; omega
      have h := rest ((k.val-1 : ℕ) : ℤ) (by omega)
      have word := hw ⟨k.val-1,hk⟩
      change ω ((k.val-1 : ℕ) : ℤ)=w[k.val-1] at word
      rw [word] at h
      convert h using 1
      · congr 1; omega
      · simp only [Fin.getElem_fin,List.getElem_cons]
        split_ifs <;> simp_all

/-- Restrict any bilateral path to a finite segment; its translated vertices
remain retained without assuming that every ambient graph vertex is live. -/
theorem bilateral_path_segment {n : ℕ} (side : MemorySide) (K : ℕ) (d : ℝ)
    (p : ℤ → MemoryVertex n) (ω : ℤ → CuLetter)
    (path : BilateralGraphPath side K d p ω) (w : List CuLetter) (i : ℤ)
    (letters : ∀ k : Fin w.length, ω (i+(k : ℕ))=w[k]) :
    RetainedWalk side K d (p i) w := by
  have live (j : ℤ) : LiveVertex side K d (p j) := by
    refine ⟨fun t => p (t+j),fun t => ω (t+j),?_,by simp⟩
    intro t
    simpa only [show t+1+j=t+j+1 by ring] using path (t+j)
  induction w generalizing i with
  | nil => exact live i
  | cons a w ih =>
    have first : ω i=a := by simpa using letters ⟨0,by simp⟩
    have tail : ∀ k : Fin w.length, ω (i+1+(k : ℕ))=w[k] := by
      intro k
      have h := letters ⟨k.val+1,by simpa using k.isLt⟩
      change ω (i+((k.val+1 : ℕ) : ℤ))=(a::w)[k.val+1] at h
      simpa only [Fin.getElem_fin,Nat.cast_add,Nat.cast_one,List.getElem_cons_succ,
        add_assoc,add_comm,add_left_comm] using h
    have edge := path i
    rw [first] at edge
    exact ⟨live i,by simpa only [← edge.1] using edge,
      by simpa only [← edge.1] using ih (i+1) tail⟩

def RetainedPathDictionary (side : MemorySide) (n K : ℕ) (d : ℝ) (T : ℕ) :=
  {vw : MemoryVertex n × List CuLetter //
    RetainedWalk side K d vw.1 vw.2 ∧ wordWeight vw.2 = T}

/-- Distinct factors and retained labeled paths differ only by their actual
initial memory vertex. The original carrier has exactly 2^n choices. -/
theorem original_weighted_path_count (side : MemorySide) (n K : ℕ) (d : ℝ)
    (positive : 0 < K) (memory : K ≤ n) (T : ℕ) :
    Finite (RetainedPathDictionary side n K d T) ∧
    factorCount (MemoryLanguage side n K d) T ≤
      Nat.card (RetainedPathDictionary side n K d T) ∧
    Nat.card (RetainedPathDictionary side n K d T) ≤
      2^n * factorCount (MemoryLanguage side n K d) T := by
  classical
  let X := MemoryLanguage side n K d
  let V := RetainedPathDictionary side n K d T
  let F := FactorDictionary X T
  have factor (v : MemoryVertex n) (w : List CuLetter)
      (walk : RetainedWalk side K d v w) : ∃ ω ∈ X, Occurs ω w := by
    rcases retained_walk_extension side K d v w walk with ⟨p,ω,path,_,letters⟩
    refine ⟨ω,(original_memory_graph_correspondence side n K d positive memory ω).mpr
      ⟨p,path,fun q hq => (path_memory_reconstruction q ω (fun i => (hq i).1)).trans
        (path_memory_reconstruction p ω (fun i => (path i).1)).symm⟩,0,?_⟩
    simpa using letters
  let inject : V → MemoryVertex n × F := fun vw =>
    (vw.val.1,⟨vw.val.2,factor vw.val.1 vw.val.2 vw.property.1,vw.property.2⟩)
  have inj : Function.Injective inject := by
    intro x y h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z : MemoryVertex n × F => z.1) h
    · exact congrArg (fun z : MemoryVertex n × F => z.2.val) h
  letI : Finite F := (factor_dictionary_bound X T).1
  letI : Finite V := Finite.of_injective inject inj
  refine ⟨inferInstance,?_,?_⟩
  · let project : V → F := fun vw => (inject vw).2
    have surj : Function.Surjective project := by
      intro w
      rcases w.property.1 with ⟨ω,hω,i,letters⟩
      rcases (original_memory_graph_correspondence side n K d positive memory ω).mp hω
        with ⟨p,path,_⟩
      refine ⟨⟨(p i,w.val),bilateral_path_segment side K d p ω path w.val i letters,
        w.property.2⟩,?_⟩
      apply Subtype.ext
      rfl
    exact Nat.card_le_card_of_surjective project surj
  · have bound := Nat.card_le_card_of_injective inject inj
    have letters : Fintype.card CuLetter = 2 := by decide
    simpa [X,V,F,factorCount,Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_fun,
      letters] using bound

def CoreVertex (side : MemorySide) (n K : ℕ) (d : ℝ) :=
  {v : MemoryVertex n // LiveVertex side K d v}

noncomputable instance (side : MemorySide) (n K : ℕ) (d : ℝ) :
    Fintype (CoreVertex side n K d) := by
  unfold CoreVertex
  exact Fintype.ofFinite _

noncomputable instance (side : MemorySide) (n K : ℕ) (d : ℝ) :
    DecidableEq (CoreVertex side n K d) := Classical.decEq _

/-- Both labels are summed when they have the same endpoints; the exponents
remain the original actual source lengths, twenty and six. -/
noncomputable def weightedAdjacency (side : MemorySide) (n K : ℕ) (d z : ℝ) :
    Matrix (CoreVertex side n K d) (CoreVertex side n K d) ℝ := by
  classical
  exact fun v t => ∑ a : CuLetter,
    if MemoryEdge side K d v.val a t.val then z^letterWeight a else 0

noncomputable def CorePath {n : ℕ} (side : MemorySide) (K : ℕ) (d : ℝ) :
    (k : ℕ) → CoreVertex side n K d →
      (Fin k → CuLetter × CoreVertex side n K d) → Prop
  | 0, _, _ => True
  | k+1, v, choices => MemoryEdge side K d v.val (choices 0).1 (choices 0).2.val ∧
      CorePath side K d k (choices 0).2 (fun i => choices i.succ)

noncomputable def coreMonomial {n : ℕ} (side : MemorySide) (K : ℕ) (d z : ℝ) :
    (k : ℕ) → CoreVertex side n K d →
      (Fin k → CuLetter × CoreVertex side n K d) → ℝ := by
  classical
  exact fun k v choices => if CorePath side K d k v choices then
    z^wordWeight (List.ofFn (fun i => (choices i).1)) else 0

/-- The finite graph uses actual retained words, not an independent SFT carrier.
Its matrix powers sum the exact original weighted monomials of all labeled paths. -/
theorem original_weighted_adjacency_paths (side : MemorySide) (n K : ℕ) (d z : ℝ) :
    (∀ (k : ℕ) (v : CoreVertex side n K d)
      (choices : Fin k → CuLetter × CoreVertex side n K d),
      CorePath side K d k v choices → RetainedWalk side K d v.val
        (List.ofFn (fun i => (choices i).1))) ∧
    (∀ (k : ℕ) (v : CoreVertex side n K d),
      (∑ t : CoreVertex side n K d, (weightedAdjacency side n K d z ^ k) v t) =
      ∑ choices : Fin k → CuLetter × CoreVertex side n K d,
        coreMonomial side K d z k v choices) := by
  classical
  let C := CoreVertex side n K d
  let M := weightedAdjacency side n K d z
  have source : ∀ (k : ℕ) (v : C) (choices : Fin k → CuLetter × C),
      CorePath side K d k v choices → RetainedWalk side K d v.val
        (List.ofFn (fun i => (choices i).1)) := by
    intro k
    induction k with
    | zero => intro v choices _; simpa [RetainedWalk] using v.property
    | succ k ih =>
      intro v choices path
      rcases path with ⟨edge,tail⟩
      rw [List.ofFn_succ]
      exact ⟨v.property,by simpa only [← edge.1] using edge,
        by simpa only [← edge.1] using ih (choices 0).2 (fun i => choices i.succ) tail⟩
  have step (k : ℕ) (v : C) (a : CuLetter) (t : C)
      (choices : Fin k → CuLetter × C) :
      coreMonomial side K d z (k+1) v (Fin.cons (a,t) choices) =
      if MemoryEdge side K d v.val a t.val then
        z^letterWeight a * coreMonomial side K d z k t choices else 0 := by
    have weight (w : List CuLetter) : wordWeight (a::w)=letterWeight a+wordWeight w :=
      by cases a <;> rfl
    simp only [coreMonomial,CorePath,Fin.cons_zero,Fin.cons_succ,List.ofFn_succ,weight,
      pow_add]
    split_ifs <;> simp_all
  have transfer (f : C → ℝ) (v : C) :
      (∑ t : C, M v t * f t) = ∑ a : CuLetter, ∑ t : C,
        if MemoryEdge side K d v.val a t.val then z^letterWeight a * f t else 0 := by
    simp only [M,weightedAdjacency,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> simp
  refine ⟨source,?_⟩
  intro k
  induction k with
  | zero => intro v; simp [coreMonomial,CorePath,wordWeight,Matrix.one_apply]
  | succ k ih =>
    intro v
    rw [pow_succ',show weightedAdjacency side n K d z = M from rfl]
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum,ih]
    rw [transfer]
    rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (k+1) => CuLetter × C)]
    rw [Fintype.sum_prod_type]
    simp only [Fin.consEquiv,Equiv.coe_fn_mk]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro t _
    simp only [step]
    split_ifs
    · simpa only [Finset.mul_sum] using congrArg (fun x : ℝ => z^letterWeight a*x) (ih t)
    · simp

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
