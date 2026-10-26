/- GID: D5/S3/ConceptDynamics/Coding/OriginalAlignedBalanced/FiniteWindowWordTransport
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/OriginalAlignedBalanced/FiniteWindowWordTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual numbered finite-window histories and signed reversed path words. -/
import D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced

/- Reuse the original append-word theorem with its unchanged kernel identity. -/
namespace D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced
run_cmd do
  let supplier := Lean.Name.num
    `_private.D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced 0
  let owner := `D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced
  let kernel := supplier ++ owner ++ `word_appendPath
  unless (← Lean.getEnv).contains kernel do
    throwError "missing original kernel supplier {kernel}"
  modify fun s => { s with env := Lean.addAlias s.env (owner ++ `word_appendPath) kernel }
end D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced

/- Canonical numbered windows and their exact history and word relations. -/
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical
open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound
open D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting

namespace D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced.FiniteWindowWordTransport

def reverseEdge {n : ℕ} {A : CountMat n n} (a : Edge A) : Edge A.transpose :=
  ⟨a.target, a.source, a.number⟩

def reversePath {n : ℕ} {A : CountMat n n} (x : Path A) : Path A.transpose :=
  ⟨fun i => reverseEdge (x.val (-i-1)), fun i => by
    change (x.val (-i-1)).source = (x.val (-(i+1)-1)).target
    have h := x.property (-(i+1)-1)
    simpa only [show -(i+1)-1+1 = -i-1 by omega] using h.symm⟩

def window {p : ℕ} {M : CountMat p p} (x : Path M) :
    (d : ℕ) → (i : ℤ) → Σ j, FinitePath M d (x.val i).source j
  | 0, i => ⟨(x.val i).source, .nil _⟩
  | d+1, i =>
    let tail := window x d (i+1)
    ⟨tail.1, .cons ((x.property i) ▸ (x.val i).number) tail.2⟩

theorem window_endpoint {p : ℕ} {M : CountMat p p} (x : Path M) (d : ℕ) (i : ℤ) :
    (window x d i).1 = (x.val (i+d)).source := by
  induction d generalizing i with
  | zero => simp only [window, Int.natCast_zero, add_zero]
  | succ d ih =>
    change (window x d (i+1)).1 = _
    rw [ih]
    rw [show i+1+(d:ℤ) = i+(↑(d+1):ℤ) by push_cast; omega]

theorem history_trace {p : ℕ} {M : CountMat p p} {Q : Type}
    (L : IncomingLift M Q) (x : Path M) (r : ℤ → Q)
    (proj : ∀ i, L.project (r i) = (x.val i).source)
    (step : ∀ i (h : L.project (r (i+1)) = (x.val i).target),
      (L.lift (x.val i) ⟨r (i+1),h⟩).val = r i) :
    ∀ d i (q : {q : Q // L.project q = (window x d i).1}),
      q.val = r (i+d) → (L.liftPath (window x d i).2 q).val = r i := by
  have liftcast (a : Edge M) (v : Fin p) (h : a.target = v)
      (q : {q : Q // L.project q = v}) :
      (L.lift ⟨a.source,v,h ▸ a.number⟩ q).val =
      (L.lift a ⟨q.val,q.property.trans h.symm⟩).val := by cases h; rfl
  intro d
  induction d with
  | zero => intro i q h; simpa only [window, IncomingLift.liftPath, Int.natCast_zero, add_zero] using h
  | succ d ih =>
    intro i q h
    have hq : q.val = r (i+1+d) :=
      h.trans (congrArg r (by push_cast; omega))
    have ht := ih (i+1) q hq
    change (L.lift ⟨(x.val i).source,(x.val (i+1)).source,
      (x.property i) ▸ (x.val i).number⟩
      (L.liftPath (window x d (i+1)).2 q)).val = r i
    rw [liftcast]
    have hr : L.liftPath (window x d (i+1)).2 q = ⟨r (i+1),proj (i+1)⟩ :=
      Subtype.ext ht
    rw [hr]
    exact step i _

theorem cast_edge {p : ℕ} {M : CountMat p p} (a : Edge M) (v : Fin p)
    (h : a.target = v) :
    (⟨a.source,v,h ▸ a.number⟩ : Edge M) = a := by cases h; rfl

theorem window_word {p : ℕ} {M : CountMat p p} (x : Path M) (d : ℕ) (i : ℤ) :
    pathWord (window x d i).2 = List.ofFn (fun j : Fin d => x.val (i+j.val)) := by
  induction d generalizing i with
  | zero => rfl
  | succ d ih =>
    change _ :: pathWord (window x d (i+1)).2 = _
    rw [cast_edge (x.val i) _ (x.property i), ih, List.ofFn_succ]
    simp only [Fin.val_zero, Int.natCast_zero, add_zero]
    apply congrArg (List.cons (x.val i))
    apply congrArg List.ofFn
    funext j
    apply congrArg x.val
    change i + 1 + (j.val : ℤ) = i + ((j.val + 1 : ℕ) : ℤ)
    push_cast
    omega

theorem reverse_word {p : ℕ} {M : CountMat p p} {d : ℕ} {i j : Fin p}
    (alpha : FinitePath M d i j) :
    pathWord (reverseFinitePath alpha) = (pathWord alpha).reverse.map reverseEdge := by
  induction alpha with
  | nil => rfl
  | @cons d u v z edge tail ih =>
    calc
      pathWord (reverseFinitePath (.cons edge tail)) =
          pathWord (reverseFinitePath tail) ++ [(⟨v,u,edge⟩ : Edge M.transpose)] :=
        word_appendPath (A := M.transpose) (reverseFinitePath tail) edge
      _ = (pathWord tail).reverse.map (@reverseEdge p M) ++ [⟨v,u,edge⟩] :=
        congrArg (fun w : List (Edge M.transpose) => w ++ [⟨v,u,edge⟩]) ih
      _ = (pathWord (.cons edge tail)).reverse.map (@reverseEdge p M) := by
        simp only [pathWord,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,reverseEdge]

theorem past_word {p : ℕ} {M : CountMat p p} (x : Path M) (d : ℕ) (i : ℤ) :
    pathWord (reverseFinitePath (window (reversePath x) d (-i)).2) =
      (List.ofFn (fun j : Fin d => x.val (i-(j.val:ℤ)-1))).reverse := by
  rw [reverse_word,window_word,List.map_reverse,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext j
  change reverseEdge (reverseEdge (x.val (-(-i+(j.val:ℤ))-1))) = _
  rw [show -(-i+(j.val:ℤ))-1 = i-(j.val:ℤ)-1 by omega]
  rfl

end D5.S3.ConceptDynamics.Coding.OriginalAlignedBalanced.FiniteWindowWordTransport
