/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/BranchStorage
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/BranchStorage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nondegenerate paired literal tails force arbitrary-stem complete storage rates. -/

import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EndpointNecessity

set_option autoImplicit false
namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open Filter Topology
set_option maxHeartbeats 2000000

def LiteralTailPath (s : Guard) (w : List Label) (path : ℕ → Guard) : Prop :=
  path 0 = s ∧
    (∀ p, nextGuard (path p) (address w p) = some (path (p+1))) ∧
    (∀ p, InSupport (path p) (coordinate w p)) ∧
    (∀ p, coordinate w p = branch (address w p) (coordinate w (p+1)))

def LiteralTailSplice (A w : List Label) (path tailPath : ℕ → Guard) : Prop :=
  LiteralTailPath .G0 (A++w) path ∧ ∀ p,
    address (A++w) (A.length+p) = address w p ∧
    coordinate (A++w) (A.length+p) = coordinate w p ∧
    path (A.length+p) = tailPath p

private theorem literal_tail_alignment (s e : Guard) (A w : List Label)
    (hA : LegalWord .G0 s A) (hw : LegalWord s e w)
    (tailPath : ℕ → Guard)
    (ht0 : tailPath 0 = s)
    (hte : ∀ p, nextGuard (tailPath p) (address w p) = some (tailPath (p+1))) :
    ∃ path : ℕ → Guard,
      path 0 = .G0 ∧
      (∀ p, nextGuard (path p) (address (A++w) p) = some (path (p+1))) ∧
      (∀ p, InSupport (path p) (coordinate (A++w) p)) ∧
      (∀ p, coordinate (A++w) p = branch (address (A++w) p) (coordinate (A++w) (p+1))) ∧
      (∀ p, address (A++w) (A.length+p) = address w p ∧
        coordinate (A++w) (A.length+p) = coordinate w p ∧
        path (A.length+p) = tailPath p) := by
  obtain ⟨path,hp0,hpe,hps,hpr⟩ := literal_address_path .G0 e (A++w)
    (legal_append .G0 s e A w hA hw)
  have future (p : ℕ) : address (A++w) (A.length+p) = address w p := by
    simp only [address,List.getElem?_append_right (by omega : A.length ≤ A.length+p),
      Nat.add_sub_cancel_left]
  have endpoint := prefix_path_endpoint .G0 s A hA (address (A++w)) path hp0 hpe
    (fun p hp => address_prefix A w p hp)
  have guards (p : ℕ) : path (A.length+p) = tailPath p := by
    induction p with
    | zero => simpa only [Nat.add_zero,ht0] using endpoint
    | succ p ih =>
      have h1 := hpe (A.length+p)
      rw [ih,future p] at h1
      exact Option.some.inj (by simpa only [Nat.add_assoc,Nat.succ_eq_add_one] using h1.symm.trans (hte p))
  refine ⟨path,hp0,hpe,hps,hpr,?_⟩
  intro p
  refine ⟨future p,?_,guards p⟩
  simp only [coordinate,List.drop_append,List.drop_eq_nil_of_le (by omega : A.length ≤ A.length+p),
    List.nil_append,Nat.add_sub_cancel_left]

theorem common_stem_code_capacity {Configuration : Type*} {n k H : ℕ}
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (o : Ownership) (b : ℝ) (encoding : Configuration → List Bool)
    (faithful : Set.InjOn encoding {c | ∃ M,
      ReachThrough action initialConfiguration (OperationRecord o b .closed) M c})
    (cuts : (Fin n → Bool) → Frame Configuration Label) (stem : List Label)
    (joint : Function.Injective (fun z => ((cuts z).state,(cuts z).output)))
    (bounded : ∀ z, (cuts z).output.length ≤ k)
    (output : ∀ z, (cuts z).output = stem.take (cuts z).output.length)
    (reached : ∀ z, ReachThrough action initialConfiguration (OperationRecord o b .closed) H (cuts z).state)
    (B : ℕ) (peak : Peak action initialConfiguration (OperationRecord o b .closed) encoding H ≤ (B : WithTop ℕ)) :
    2^n ≤ (2^(B+1)-1)*(k+1) := by
  classical
  let codes : Finset (List Bool) := Finset.univ.image (fun z => encoding (cuts z).state)
  let f : (Fin n → Bool) → {v // v ∈ codes} × Fin (k+1) := fun z =>
    (⟨encoding (cuts z).state,Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩⟩,
      ⟨(cuts z).output.length,Nat.lt_succ_of_le (bounded z)⟩)
  have injection : Function.Injective f := by
    intro z z' eq
    apply joint
    have code : encoding (cuts z).state = encoding (cuts z').state :=
      congrArg (fun p : {v // v ∈ codes} × Fin (k+1) => p.1.val) eq
    have state := faithful ⟨H,reached z⟩ ⟨H,reached z'⟩ code
    have len : (cuts z).output.length = (cuts z').output.length :=
      congrArg (fun p : {v // v ∈ codes} × Fin (k+1) => p.2.val) eq
    refine Prod.ext state ?_
    change (cuts z).output = (cuts z').output
    rw [output z,output z',len]
  have count : 2^n ≤ codes.card*(k+1) := by
    simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Fintype.card_prod,
      Fintype.card_coe] using Fintype.card_le_of_injective f injection
  have lengths : ∀ v ∈ codes, v.length ≤ B := by
    intro v hv
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
    have bound := (peak_bound action initialConfiguration (OperationRecord o b .closed)
      encoding H (cuts z).state (reached z)).trans peak
    exact_mod_cast bound
  have codeCount : codes.card ≤ 2^(B+1)-1 := by
    calc codes.card = ∑ j ∈ Finset.range (B+1), (codes.filter (fun v => v.length=j)).card :=
           Finset.card_eq_sum_card_fiberwise (by
             intro v hv
             exact Finset.mem_range.mpr (Nat.lt_succ_of_le (lengths v hv)))
         _ ≤ ∑ j ∈ Finset.range (B+1), 2^j := by
           apply Finset.sum_le_sum
           intro j hj
           simpa only [Fintype.card_bool] using
             (Finset.card_filter_length_eq_le (T := codes) (s := j))
         _ = 2^(B+1)-1 := by
           simpa using geom_sum_mul_of_one_le (by norm_num : (1 : ℕ) ≤ 2) (B+1)
  exact count.trans (Nat.mul_le_mul_right (k+1) codeCount)

/-- Two interior literal tails construct the actual synchronized competitors.
The complete encoding counts every readable configuration and every trace vertex. -/
theorem nondegenerate_branch_storage {Configuration : Type*}
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (o : Ownership) (b : ℝ)
    (s1 s2 : Guard) (P Q : List Label) (h : List Color)
    (hP : LegalWord .G0 s1 P) (hQ : LegalWord .G0 s2 Q)
    (hPlen : P.length = h.length) (hQlen : Q.length = h.length)
    (U V : Bool → List Label) (W : Bool → List Color)
    (L : ℕ) (hL : 0 < L)
    (hU : ∀ i, LegalWord s1 s1 (U i)) (hV : ∀ i, LegalWord s2 s2 (V i))
    (hUlen : ∀ i, (U i).length = L) (hVlen : ∀ i, (V i).length = L)
    (hWlen : ∀ i, (W i).length = L)
    (differentU : U false ≠ U true) (differentV : V false ≠ V true)
    (hbudget : familyEndpointBudget P Q h U V W L ≤ b)
    (k : ℕ) (hk : k < P.length)
    (sameStem : ∀ p (hp : p < k), P[p] = Q[p]'(by omega))
    (differentStem : P[k] ≠ Q[k]'(by omega))
    (safety : ∀ a r, OperationRecord o b .closed a r → ∀ t,
      Run action (full r) ⟨initialConfiguration,0,[]⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = a p)
    (liveness : ∀ a r, OperationRecord o b .closed a r → OperationFiniteSource a → ∀ p,
      ∃ t, Run action (full r) ⟨initialConfiguration,0,[]⟩ t ∧ p < t.output.length)
    (postprocessing : ∀ a r, OperationRecord o b .closed a r →
      ∀ (c d : Configuration) (q : ℕ) (out batch : List Label)
      (f : Color → Option (Configuration × List Label)),
      Run action (full r) ⟨initialConfiguration,0,[]⟩ ⟨c,q,out⟩ →
      action c = .acquire f → f (r q) = some (d,batch) →
      ∃ t, Drain action ⟨d,q+1,out++batch⟩ t)
    (encoding : Configuration → List Bool)
    (faithful : Set.InjOn encoding {c | ∃ H,
      ReachThrough action initialConfiguration (OperationRecord o b .closed) H c}) :
    ∃ (e1 e2 : Guard) (w1 w2 : List Label),
      LegalWord s1 e1 w1 ∧ LegalWord s2 e2 w2 ∧
      canonicalReturnLo U L < coordinate w1 0 ∧ coordinate w1 0 < canonicalReturnHi U L ∧
      canonicalReturnLo V L < coordinate w2 0 ∧ coordinate w2 0 < canonicalReturnHi V L ∧
      (∃ tailPath1 tailPath2 : ℕ → Guard,
        LiteralTailPath s1 w1 tailPath1 ∧ LiteralTailPath s2 w2 tailPath2 ∧
        ∀ (n : ℕ) (z : Fin n → Bool), ∃ path1 path2 : ℕ → Guard,
          LiteralTailSplice (synchronousPrefix P U z) w1 path1 tailPath1 ∧
          LiteralTailSplice (synchronousPrefix Q V z) w2 path2 tailPath2) ∧
      (∀ n : ℕ, ∃ (cuts : (Fin n → Bool) → Frame Configuration Label) (states : Finset Configuration),
        (∀ z : Fin n → Bool,
          OperationRecord o b .closed (address (synchronousPrefix P U z++w1))
            (recordWithTail o (synchronousPrefix h W z) w1) ∧
          OperationFiniteSource (address (synchronousPrefix P U z++w1)) ∧
          OperationRecord o b .closed (address (synchronousPrefix Q V z++w2))
            (recordWithTail o (synchronousPrefix h W z) w2)) ∧
        (∀ z : Fin n → Bool, ∀ p,
          address (synchronousPrefix P U z++w1) (P.length+n*L+p) = address w1 p ∧
          coordinate (synchronousPrefix P U z++w1) (P.length+n*L+p) = coordinate w1 p ∧
          address (synchronousPrefix Q V z++w2) (P.length+n*L+p) = address w2 p ∧
          coordinate (synchronousPrefix Q V z++w2) (P.length+n*L+p) = coordinate w2 p ∧
          recordWithTail o (synchronousPrefix h W z) w1 (P.length+n*L+p) = observe o (coordinate w1 p) 0 ∧
          recordWithTail o (synchronousPrefix h W z) w2 (P.length+n*L+p) = observe o (coordinate w2 p) 0) ∧
        Function.Injective (fun z : Fin n → Bool => address (synchronousPrefix P U z++w1)) ∧
        (∀ z, Cut action initialConfiguration
          (front (recordWithTail o (synchronousPrefix h W z) w1) (P.length+n*L)) (cuts z) ∧
          (cuts z).output.length ≤ k ∧ (cuts z).output = (P.take k).take (cuts z).output.length ∧
          (cuts z).output <+: P.take k ∧
          ReachThrough action initialConfiguration (OperationRecord o b .closed) (P.length+n*L) (cuts z).state) ∧
        Function.Injective (fun z => ((cuts z).state,(cuts z).output)) ∧
        (∀ c, c ∈ states ↔ ∃ z, (cuts z).state = c) ∧
        2^n ≤ states.card*(k+1) ∧
        (∀ B : ℕ, Peak action initialConfiguration (OperationRecord o b .closed) encoding
          (P.length+n*L) ≤ (B : WithTop ℕ) → 2^n ≤ (2^(B+1)-1)*(k+1))) ∧
      (∀ H B : ℕ, P.length ≤ H →
        Peak action initialConfiguration (OperationRecord o b .closed) encoding H ≤ (B : WithTop ℕ) →
        (((H-P.length)/L : ℕ) : ℝ)-1-Real.logb 2 ((k+1 : ℕ) : ℝ) ≤ (B : ℝ)) ∧
      ENNReal.ofReal (1/(L : ℝ)) ≤
        liminf (fun H : ℕ => ENat.toENNReal
          (Peak action initialConfiguration (OperationRecord o b .closed) encoding H)/(H : ENNReal)) atTop ∧
      (∀ a r t vertices H, OperationRecord o b .closed a r →
        Trace action (full r) ⟨initialConfiguration,0,[]⟩ t vertices → t.acquired ≤ H →
        ∀ c ∈ vertices, ((encoding c).length : WithTop ℕ) ≤
          Peak action initialConfiguration (OperationRecord o b .closed) encoding H) := by
  classical
  obtain ⟨hb0,_,cP,cU,cQ,cV⟩ := family_endpoint_certificates o s1 s2 P Q h hP hQ hPlen hQlen
    U V W L hL hUlen hVlen hU hV (fun i => (hUlen i).trans (hWlen i).symm)
  have hb := hb0.trans hbudget
  have hullU := canonical_legal_return_hull s1 U L hL hUlen hU
  have hullV := canonical_legal_return_hull s2 V L hL hVlen hV
  obtain ⟨e1,w1,hw1,hin1,hout1,highAll⟩ := fixed_finite_tail_all_histories o b hb s1 P h hP hPlen U W hU
    (fun i => (hUlen i).trans (hWlen i).symm) _ _ (hullU.2.1 differentU) hullU.2.2.1 hullU.2.2.2.1
    (endpoint_certificate_mono _ b _ _ P h hbudget cP)
    (fun i => endpoint_certificate_mono _ b _ _ (U i) (W i) hbudget (cU i))
  obtain ⟨e2,w2,hw2,hin2,hout2,lowAll⟩ := fixed_finite_tail_all_histories o b hb s2 Q h hQ hQlen V W hV
    (fun i => (hVlen i).trans (hWlen i).symm) _ _ (hullV.2.1 differentV) hullV.2.2.1 hullV.2.2.2.1
    (endpoint_certificate_mono _ b _ _ Q h hbudget cQ)
    (fun i => endpoint_certificate_mono _ b _ _ (V i) (W i) hbudget (cV i))
  obtain ⟨tailPath1,tp10,tp1e,tp1s,tp1r⟩ := literal_address_path s1 e1 w1 hw1
  obtain ⟨tailPath2,tp20,tp2e,tp2s,tp2r⟩ := literal_address_path s2 e2 w2 hw2
  have aligned : ∃ tailPath1 tailPath2 : ℕ → Guard,
      LiteralTailPath s1 w1 tailPath1 ∧ LiteralTailPath s2 w2 tailPath2 ∧
      ∀ (n : ℕ) (z : Fin n → Bool), ∃ path1 path2 : ℕ → Guard,
        LiteralTailSplice (synchronousPrefix P U z) w1 path1 tailPath1 ∧
        LiteralTailSplice (synchronousPrefix Q V z) w2 path2 tailPath2 := by
    refine ⟨tailPath1,tailPath2,⟨tp10,tp1e,tp1s,tp1r⟩,⟨tp20,tp2e,tp2s,tp2r⟩,?_⟩
    intro n z
    obtain ⟨path1,p10,p1e,p1s,p1r,align1⟩ := literal_tail_alignment s1 e1 (synchronousPrefix P U z) w1
      (legal_append .G0 s1 s1 P _ hP (choices_legal s1 U hU (List.ofFn z))) hw1 tailPath1 tp10 tp1e
    obtain ⟨path2,p20,p2e,p2s,p2r,align2⟩ := literal_tail_alignment s2 e2 (synchronousPrefix Q V z) w2
      (legal_append .G0 s2 s2 Q _ hQ (choices_legal s2 V hV (List.ofFn z))) hw2 tailPath2 tp20 tp2e
    exact ⟨path1,path2,⟨⟨p10,p1e,p1s,p1r⟩,align1⟩,⟨⟨p20,p2e,p2s,p2r⟩,align2⟩⟩
  have atHigh : OperationRecord o b .closed (address (P++w1)) (recordWithTail o h w1) ∧
      OperationFiniteSource (address (P++w1)) := by
    exact ⟨by simpa [choiceBlocks] using (highAll []).1,
      by simpa [choiceBlocks] using (highAll []).2.1⟩
  have atLow : OperationRecord o b .closed (address (Q++w2)) (recordWithTail o h w2) := by
    simpa [choiceBlocks] using (lowAll []).1
  have processing : Processing action initialConfiguration (OperationRecord o b .closed) := by
    refine ⟨?_,postprocessing⟩
    obtain ⟨t,run,emitted⟩ := liveness _ _ atHigh.1 atHigh.2 k
    have acquired : 0 < t.acquired := by
      by_contra hn
      have zero : t.acquired = 0 := by omega
      obtain ⟨vertices,trace⟩ := run
      have lowRun : Run action (full (recordWithTail o h w2)) ⟨initialConfiguration,0,[]⟩ t :=
        ⟨vertices,trace_input_transfer trace (by intro q hq hqt; dsimp only at hq; omega)⟩
      have hh := safety _ _ atHigh.1 t ⟨vertices,trace⟩ k emitted
      have hl := safety _ _ atLow t lowRun k emitted
      rw [address_prefix P w1 k hk] at hh
      rw [address_prefix Q w2 k (by omega)] at hl
      exact differentStem (hh.symm.trans hl)
    exact initial_drain_of_acquired_run action initialConfiguration _ t run acquired
  have takeLen : (P.take k).length = k := by simp only [List.length_take,Nat.min_eq_left hk.le]
  let fullPeak := Peak action initialConfiguration (OperationRecord o b .closed) encoding
  have mono : Monotone fullPeak := peak_monotone action initialConfiguration (OperationRecord o b .closed) encoding
  have families (n : ℕ) : ∃ (cuts : (Fin n → Bool) → Frame Configuration Label) (states : Finset Configuration),
      (∀ z : Fin n → Bool, OperationRecord o b .closed (address (synchronousPrefix P U z++w1))
        (recordWithTail o (synchronousPrefix h W z) w1) ∧ OperationFiniteSource (address (synchronousPrefix P U z++w1)) ∧
        OperationRecord o b .closed (address (synchronousPrefix Q V z++w2)) (recordWithTail o (synchronousPrefix h W z) w2)) ∧
      (∀ z : Fin n → Bool, ∀ p,
        address (synchronousPrefix P U z++w1) (P.length+n*L+p) = address w1 p ∧
        coordinate (synchronousPrefix P U z++w1) (P.length+n*L+p) = coordinate w1 p ∧
        address (synchronousPrefix Q V z++w2) (P.length+n*L+p) = address w2 p ∧
        coordinate (synchronousPrefix Q V z++w2) (P.length+n*L+p) = coordinate w2 p ∧
        recordWithTail o (synchronousPrefix h W z) w1 (P.length+n*L+p) = observe o (coordinate w1 p) 0 ∧
        recordWithTail o (synchronousPrefix h W z) w2 (P.length+n*L+p) = observe o (coordinate w2 p) 0) ∧
      Function.Injective (fun z : Fin n → Bool => address (synchronousPrefix P U z++w1)) ∧
      (∀ z, Cut action initialConfiguration (front (recordWithTail o (synchronousPrefix h W z) w1) (P.length+n*L)) (cuts z) ∧
        (cuts z).output.length ≤ k ∧ (cuts z).output = (P.take k).take (cuts z).output.length ∧ (cuts z).output <+: P.take k ∧
        ReachThrough action initialConfiguration (OperationRecord o b .closed) (P.length+n*L) (cuts z).state) ∧
      Function.Injective (fun z => ((cuts z).state,(cuts z).output)) ∧
      (∀ c, c ∈ states ↔ ∃ z, (cuts z).state = c) ∧ 2^n ≤ states.card*(k+1) ∧
      (∀ B : ℕ, fullPeak (P.length+n*L) ≤ (B : WithTop ℕ) → 2^n ≤ (2^(B+1)-1)*(k+1)) := by
    let alpha : (Fin n → Bool) → ℕ → Label := fun z => address (synchronousPrefix P U z++w1)
    let beta : (Fin n → Bool) → ℕ → Label := fun z => address (synchronousPrefix Q V z++w2)
    let highRecord : (Fin n → Bool) → ℕ → Color := fun z => recordWithTail o (synchronousPrefix h W z) w1
    let lowRecord : (Fin n → Bool) → ℕ → Color := fun z => recordWithTail o (synchronousPrefix h W z) w2
    have highLen (z : Fin n → Bool) := synchronous_length P U L hUlen n z
    have lowLen (z : Fin n → Bool) : (synchronousPrefix Q V z).length = P.length+n*L := by
      rw [synchronous_length Q V L hVlen n z]; omega
    have colorLen (z : Fin n → Bool) : (synchronousPrefix h W z).length = P.length+n*L := by
      rw [synchronous_length h W L hWlen n z,← hPlen]
    have high (z : Fin n → Bool) : OperationRecord o b .closed (alpha z) (highRecord z) ∧ OperationFiniteSource (alpha z) :=
      ⟨(highAll (List.ofFn z)).1,(highAll (List.ofFn z)).2.1⟩
    have low (z : Fin n → Bool) : OperationRecord o b .closed (beta z) (lowRecord z) := (lowAll (List.ofFn z)).1
    have past (z : Fin n → Bool) (p : ℕ) (hp : p < P.length+n*L) : highRecord z p = lowRecord z p := by
      have hpc : p < (synchronousPrefix h W z).length := by rw [colorLen]; exact hp
      simp only [highRecord,lowRecord,recordWithTail,dif_pos hpc]
    have highFuture (z : Fin n → Bool) (p : ℕ) : highRecord z (P.length+n*L+p) = observe o (coordinate w1 p) 0 := by
      change recordWithTail o (synchronousPrefix h W z) w1 (P.length+n*L+p) = _
      rw [← colorLen z]
      exact (highAll (List.ofFn z)).2.2 p
    have future (z z' : Fin n → Bool) (p : ℕ) : highRecord z (P.length+n*L+p) = highRecord z' (P.length+n*L+p) :=
      (highFuture z p).trans (highFuture z' p).symm
    have alphaAt (z : Fin n → Bool) (p : ℕ) (hp : p < P.length) : alpha z p = P[p] := by
      have hpa : p < (synchronousPrefix P U z).length := by rw [highLen]; omega
      simpa only [alpha,synchronousPrefix,List.getElem_append_left hp] using address_prefix _ w1 p hpa
    have betaAt (z : Fin n → Bool) (p : ℕ) (hp : p < Q.length) : beta z p = Q[p] := by
      have hpa : p < (synchronousPrefix Q V z).length := by rw [lowLen]; omega
      simpa only [beta,synchronousPrefix,List.getElem_append_left hp] using address_prefix _ w2 p hpa
    have stemHigh (z : Fin n → Bool) (p : ℕ) (hp : p < (P.take k).length) : alpha z p = (P.take k)[p] := by
      have hpP : p < P.length := by rw [takeLen] at hp; omega
      simpa only [List.getElem_take] using alphaAt z p hpP
    have stemLow (z : Fin n → Bool) (p : ℕ) (hp : p < (P.take k).length) : beta z p = (P.take k)[p] := by
      have hpk : p < k := by rw [takeLen] at hp; exact hp
      calc beta z p = Q[p] := betaAt z p (by omega)
           _ = P[p] := (sameStem p hpk).symm
           _ = (P.take k)[p] := by simp only [List.getElem_take]
    have diff (z : Fin n → Bool) : alpha z (P.take k).length ≠ beta z (P.take k).length := by
      rw [takeLen,alphaAt z k hk,betaAt z k (by omega)]; exact differentStem
    have sourceInjection := synchronous_address_injective P U L hUlen differentU w1 n
    obtain ⟨cuts,states,cutData,joint,members,count⟩ := original_operation_common_stem
      action initialConfiguration o b .closed processing safety liveness alpha beta highRecord lowRecord
      (P.length+n*L) (P.take k) high low past future stemHigh stemLow diff sourceInjection
    have reached (z : Fin n → Bool) : ReachThrough action initialConfiguration (OperationRecord o b .closed)
        (P.length+n*L) (cuts z).state := by
      refine ⟨alpha z,highRecord z,cuts z,(high z).1,?_,?_,rfl⟩
      · obtain ⟨vertices,trace⟩ := (cutData z).1.1
        exact ⟨vertices,(prefix_trace_iff (highRecord z) (P.length+n*L) (by
          simpa only [front,List.length_ofFn] using (cutData z).1.2.1.le)).mpr trace⟩
      · simpa only [front,List.length_ofFn] using (cutData z).1.2.1.le
    refine ⟨cuts,states,(fun z => ⟨(high z).1,(high z).2,low z⟩),?_,sourceInjection,?_,joint,members,?_,?_⟩
    · intro z p
      obtain ⟨path1,_,_,_,_,align1⟩ := literal_tail_alignment s1 e1 (synchronousPrefix P U z) w1
        (legal_append .G0 s1 s1 P _ hP (choices_legal s1 U hU (List.ofFn z))) hw1 tailPath1 tp10 tp1e
      obtain ⟨path2,_,_,_,_,align2⟩ := literal_tail_alignment s2 e2 (synchronousPrefix Q V z) w2
        (legal_append .G0 s2 s2 Q _ hQ (choices_legal s2 V hV (List.ofFn z))) hw2 tailPath2 tp20 tp2e
      have a1 := align1 p
      have a2 := align2 p
      rw [highLen] at a1
      rw [lowLen] at a2
      refine ⟨a1.1,a1.2.1,a2.1,a2.2.1,highFuture z p,?_⟩
      simpa only [synchronousPrefix,← colorLen z] using (lowAll (List.ofFn z)).2.2 p
    · intro z
      exact ⟨(cutData z).1,by simpa only [takeLen] using (cutData z).2.1,
        (cutData z).2.2.1,(cutData z).2.2.2,reached z⟩
    · simpa only [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,takeLen] using count
    · intro B bound
      exact common_stem_code_capacity action initialConfiguration o b encoding faithful cuts (P.take k)
        joint (fun z => by simpa only [takeLen] using (cutData z).2.1)
        (fun z => (cutData z).2.2.1) reached B bound
  have capacity (n B : ℕ) (bound : fullPeak (P.length+n*L) ≤ (B : WithTop ℕ)) :
      2^n ≤ (2^(B+1)-1)*(k+1) := by
    obtain ⟨cuts,states,actual,alignment,inj,cutspec,joint,members,count,cap⟩ := families n
    exact cap B bound
  have finiteFloor (H B : ℕ) (hH : P.length ≤ H) (bound : fullPeak H ≤ (B : WithTop ℕ)) :
      (((H-P.length)/L : ℕ) : ℝ)-1-Real.logb 2 ((k+1 : ℕ) : ℝ) ≤ (B : ℝ) := by
    let n := (H-P.length)/L
    have nh : P.length+n*L ≤ H := by have hh := Nat.div_mul_le_self (H-P.length) L; dsimp [n]; omega
    have cn := (capacity n B ((mono nh).trans bound)).trans
      (Nat.mul_le_mul_right (k+1) (Nat.sub_le (2^(B+1)) 1))
    have cr : (2 : ℝ)^n ≤ (2 : ℝ)^(B+1)*((k+1 : ℕ) : ℝ) := by exact_mod_cast cn
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2) (by positivity : (0 : ℝ)<2^n) cr
    rw [Real.logb_mul (by positivity) (by positivity)] at hl
    simp only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2),mul_one,Nat.cast_add,Nat.cast_one] at hl
    change (n : ℝ)-1-Real.logb 2 ((k+1 : ℕ) : ℝ) ≤ (B : ℝ)
    simp only [Nat.cast_add,Nat.cast_one]
    linarith
  have lp : (0 : ℝ)<(L : ℝ) := by exact_mod_cast hL
  let loss : ℝ := ((P.length : ℝ)+(L : ℝ))/(L : ℝ)+1+Real.logb 2 ((k+1 : ℕ) : ℝ)
  have lower (H B : ℕ) (hH : max P.length 1 ≤ H) (bound : fullPeak H ≤ (B : WithTop ℕ)) :
      1/(L : ℝ)-loss/(H : ℝ) ≤ (B : ℝ)/(H : ℝ) := by
    have hp : (0 : ℝ)<(H : ℝ) := by exact_mod_cast (show 0<H by omega)
    let n := (H-P.length)/L
    have remainder := Nat.mod_lt (H-P.length) hL
    have decomp : (H-P.length)/L*L+(H-P.length)%L = H-P.length := by
      simpa only [Nat.mul_comm] using Nat.div_add_mod (H-P.length) L
    have hd : P.length ≤ H := le_trans (le_max_left _ _) hH
    have hn : H ≤ P.length+n*L+L := by dsimp [n]; omega
    have hr : (H : ℝ) ≤ (P.length : ℝ)+(n : ℝ)*(L : ℝ)+(L : ℝ) := by exact_mod_cast hn
    have hfloor := finiteFloor H B (by omega) bound
    rw [show 1/(L : ℝ)-loss/(H : ℝ) = ((H : ℝ)/(L : ℝ)-loss)/(H : ℝ) by field_simp]
    rw [div_le_div_iff_of_pos_right hp]
    have hratio : (H : ℝ)/(L : ℝ) ≤ (P.length : ℝ)/(L : ℝ)+(n : ℝ)+1 := by
      rw [div_le_iff₀ lp]
      nlinarith [div_mul_cancel₀ (P.length : ℝ) (ne_of_gt lp)]
    dsimp [loss,n] at *
    have hsplit : ((P.length : ℝ)+(L : ℝ))/(L : ℝ) = (P.length : ℝ)/(L : ℝ)+1 := by field_simp
    rw [hsplit]
    linarith
  have rate : ENNReal.ofReal (1/(L : ℝ)) ≤ liminf
      (fun H : ℕ => ENat.toENNReal (fullPeak H)/(H : ENNReal)) atTop := by
    have eventually : ∀ᶠ H : ℕ in atTop,
        ENNReal.ofReal (1/(L : ℝ)-loss/(H : ℝ)) ≤ ENat.toENNReal (fullPeak H)/(H : ENNReal) := by
      filter_upwards [eventually_ge_atTop (max P.length 1)] with H hH
      have hp : (0 : ℝ)<(H : ℝ) := by exact_mod_cast (show 0<H by omega)
      rcases eq_or_ne (fullPeak H) ⊤ with ht | hf
      · rw [ht]
        change ENNReal.ofReal _ ≤ (⊤ : ENNReal)/(H : ENNReal)
        rw [ENNReal.top_div_of_ne_top (by simp)]; exact le_top
      · obtain ⟨B,hB⟩ := WithTop.ne_top_iff_exists.mp hf
        have er := ENNReal.ofReal_le_ofReal (lower H B hH (by rw [← hB]; exact le_rfl))
        rw [← hB]
        change ENNReal.ofReal _ ≤ (B : ENNReal)/(H : ENNReal)
        simpa only [ENNReal.ofReal_div_of_pos hp,ENNReal.ofReal_natCast] using er
    have limit : Tendsto (fun H : ℕ => ENNReal.ofReal (1/(L : ℝ)-loss/(H : ℝ))) atTop
        (𝓝 (ENNReal.ofReal (1/(L : ℝ)))) :=
      by
        apply ENNReal.tendsto_ofReal
        simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat loss)
    rw [← limit.liminf_eq]
    exact liminf_le_liminf eventually
  refine ⟨e1,e2,w1,w2,hw1,hw2,hin1,hout1,hin2,hout2,aligned,families,finiteFloor,rate,?_⟩
  intro a r t vertices H ha trace hH c hc
  exact peak_trace_bound action initialConfiguration (OperationRecord o b .closed) encoding H a r t vertices ha trace hH c hc

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage
