# Five Mode Self Generated Laws

## Abstract

Same-update generated laws, exact uniform errors and attained initialized finite-carrier minimum bounds.

The source is the literal five-mode model: p,q,r>0 and p+q+r<1, a=1-p-q, b=1-r and c=1-p-q-r. This module treats a!=b in both holding orientations, including p=q. The hidden carrier is Fin 5. Visible symbols are Fin 4 with B=2; Lean order is (0,1,B,3), while the source prose uses (0,1,3,B).

Every source-legal finite history has positive actual historyMass. Empty history is included and predicts Y0; after a nonempty acquired history, the future begins after its last acquired read. Every natural horizon is included. H=0 has its unique normalized empty word and TV zero.

GeneratedObserver emits nonnegative normalized rows at every complete carrier configuration, including configurations used only by hypothetical generated words. The same total U defines retention and every product decoder. A legal actual input can have forecast row weight zero; all singleton overwrites remain defined and the actual-history accuracy guarantee uses actual source legality.

For positive N and k:Fin N put m=N-k, T_j=a^j+b^j, u=min(a,b), v=max(a,b), theta=u/v and delta_j=theta^j/(1+theta^j)=u^j/T_j. The actual laws agree through horizon m. At longer horizons only the chronological prefix List.replicate m B contributes to their signed difference. Its factor is T_N/T_k, followed by the actual startup-N residual versus the dominant pure residual. Complete word sums include impossible and zero-weight words.

The exact transient finite error is zero for H<=m and (T_N/T_k)*delta_N*(1-u^(H-m)) for H>m. Its all-horizon supremum is (T_N/T_k)*delta_N=u^N/T_k<=delta_N. The initialized B branch has mass 2/5 and enters A0, so initialized finite error is zero through N+1 and (u^N/5)*(1-u^(H-N-1)) thereafter; its exact supremum is u^N/5<=delta_N.

Actual source classification exhausts empty history, startup k<N at Ak, startup k>=N at the dominant pure label with delta_k<=delta_N, and singleton-containing pure histories. The actual source fold and the retained fold use the matching total update, giving the uniform all-history bound.

With 0<2 epsilon<kappa, N1=cutoff(theta,epsilon) is the first non-strict threshold and N2=cutoff(theta,2 epsilon). Ties are allowed. The constructed full carrier has 6+N1 configurations. Every competing finite normalized generator derives coherence and the original common-law lower bound 6+N2 under its original accuracy condition.

Attainable n means that an initialized accurate normalized generator exists on Fin n. Exact equivalence transport connects this predicate to every finite carrier and counts every configuration. Nonemptiness comes from the actual constructed law. Nat least-element existence gives an attained minimum with 6+N2<=minimum<=6+N1; coincident cutoffs give minimum=6+N1.

The formulas use Words(H) for the complete Fin H to Visible carrier, so zero-weight and impossible words remain included; Law abbreviates cutoffLaw, Startup abbreviates startupLaw, and Enc(k) is encodeSource(d,N,startup k). Distance is the all-natural-horizon profileDistance, TV is the finite half-L1 totalVariation, and Min is the proof-independent least attainable initialized size under the displayed small-error premises. differenceProfile(F,G)(H,w) is F(H,w)-G(H,w), and atHorizon(F,H) is F H. A Fin N index in T or N-k means its natural value. Accurate(toObserver(g),p,q,r,epsilon,true) is the exact actual-history and all-natural-horizon guarantee; proof arguments are suppressed. Missing statement projections are explicit gaps; their declaration handles still bind to the current compiled Lean source.

The stronger unequal optimum when N1>N2 remains open. Equality a=b, its separate seven-state realization and minimum, and the actual midpoint conditional-tail obstruction belong to their separate source obligations. No unequal logarithmic cutoff is evaluated at theta=1.

**Definition 1.1 (generatedLaw).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generatedLaw`

*Formalization.* `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generatedLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every carrier, total U, real row map g, configuration, natural horizon and complete visible word: horizon zero has weight one; the next-symbol weight multiplies the law at U(z,y).

**Definition 1.2 (GeneratedObserver).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.GeneratedObserver`

*Formalization.* `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.GeneratedObserver` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A carrier has one initial configuration, a total symbol update, and a nonnegative row of total mass one at every configuration.

**Definition 1.3 (GeneratedObserver toObserver).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.toObserver`

*Formalization.* `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.toObserver` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The retained fold and every hypothetical generated word use the same total update; the decoder is generatedLaw of this update and its rows.

**Lemma 1.4 (generated cons).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generated_cons`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generated_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Lemma 1.5 (generated nonnegative).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generated_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generated_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Lemma 1.6 (generated sum).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generated_sum`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generated_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Lemma 1.7 (generated final symbol).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generated_final_symbol`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generated_final_symbol` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Lemma 1.8 (generated coherent).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generated_coherent`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generated_coherent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Lemma 1.9 (one step probability).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.one_step_probability`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.one_step_probability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Definition 1.10 (cutoffRows).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoffRows`

*Formalization.* `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoffRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

I emits 1/5 at each singleton 0,1,3 and 2/5 at B. Every Ri emits its pure source row. Ak emits the actual one-step law of G_delta_k.

**Lemma 1.11 (cutoffRows probability).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoffRows_probability`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoffRows_probability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Definition 1.12 (cutoffGenerator).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoffGenerator`

*Formalization.* `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoffGenerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every admissible unequal source and natural cutoff N, use the complete SharpState N carrier with I as initial state, sharpUpdate of the matching dominant state, and the normalized cutoff rows.

**Lemma 1.13 (cutoff row is actual).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoff_row_is_actual`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoff_row_is_actual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Lemma 1.14 (cutoff run is actual).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoff_run_is_actual`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoff_run_is_actual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Lemma 1.15 (cutoff singleton total).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoff_singleton_total`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoff_singleton_total` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Lemma 1.16 (actual startup B recurrence).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.actual_startup_B_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.actual_startup_B_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Definition 1.17 (singletonState).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.singletonState`

*Formalization.* `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.singletonState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Definition 1.18 (nextPure).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.nextPure`

*Formalization.* `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.nextPure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Lemma 1.19 (pure zero).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.pure_zero`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.pure_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Lemma 1.20 (pure cons).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.pure_cons`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.pure_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Lemma 1.21 (pure update).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.pure_update`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.pure_update` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Definition 1.22 (cutoffLaw).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoffLaw`

*Formalization.* `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoffLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The decoder is precisely the product law of sharpUpdate and cutoffRows, at every carrier configuration and complete word.

**Lemma 1.23 (pure generated).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.pure_generated`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.pure_generated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Definition 1.24 (T).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.T`

*Formalization.* `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

T_k=a^k+b^k for every natural k.

**Definition 1.25 (startupLaw).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.startupLaw`

*Formalization.* `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.startupLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual conditional source future after the finite acquired history B^(k+1).

**Lemma 1.26 (T pos).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.T_pos`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.T_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Lemma 1.27 (startup zero).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.startup_zero`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.startup_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Lemma 1.28 (startup B).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.startup_B`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.startup_B` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Lemma 1.29 (startup singleton).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.startup_singleton`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.startup_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Lemma 1.30 (startup B row).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.startup_B_row`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.startup_B_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Lemma 1.31 (cutoff startup row).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoff_startup_row`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoff_startup_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Lemma 1.32 (generated startup B).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generated_startup_B`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generated_startup_B` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Lemma 1.33 (generated startup singleton).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generated_startup_singleton`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generated_startup_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Definition 1.34 (cylinder).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cylinder`

*Formalization.* `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cylinder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signed suffix law is placed on the literal chronological all-B prefix; words leaving that prefix have zero signed weight.

**Lemma 1.35 (cylinder zero).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cylinder_zero`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cylinder_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Lemma 1.36 (source product localization).**

$$\forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \left(\operatorname{admissible}\left(p, q, r\right) \land \operatorname{a}\left(p, q\right) \ne \operatorname{b}\left(r\right)\right) \Rightarrow \left(\forall N \in \operatorname{Nat}\left(\right),\; \forall k \in \operatorname{Nat}\left(\right),\; k \le N \Rightarrow \left(\forall H \in \operatorname{Nat}\left(\right),\; \forall w \in \operatorname{Words}\left(H\right),\; \operatorname{startupLaw}\left(p, q, r, k, H, w\right) - \operatorname{cutoffLaw}\left(p, q, r, N, \operatorname{encodeSource}\left(\operatorname{dominantState}\left(p, q, r\right), N, \operatorname{startup}\left(k\right)\right), H, w\right) = \frac{\operatorname{T}\left(p, q, r, N\right)}{\operatorname{T}\left(p, q, r, k\right)} \cdot \operatorname{cylinder}\left(N - k, \operatorname{differenceProfile}\left(\operatorname{startupLaw}\left(p, q, r, N\right), \operatorname{pureLaw}\left(p, q, r, \operatorname{dominantState}\left(p, q, r\right)\right)\right), H, w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.source_product_localization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every admissible unequal source, N,k,H with k<=N, and every complete word, startupLaw_k minus the actual generated cutoff law at encodeSource(startup k) equals (T_N/T_k) times the B^(N-k) cylinder of startupLaw_N minus the dominant pure law. Zero-weight words are included.

**Lemma 1.37 (cylinder pre).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cylinder_pre`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cylinder_pre` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration.

**Lemma 1.38 (precutoff agreement).**

$$\forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \left(\operatorname{admissible}\left(p, q, r\right) \land \operatorname{a}\left(p, q\right) \ne \operatorname{b}\left(r\right)\right) \Rightarrow \left(\forall N \in \operatorname{Nat}\left(\right),\; \forall k \in \operatorname{Fin}\left(N\right),\; \forall H \in \operatorname{Nat}\left(\right),\; \forall w \in \operatorname{Words}\left(H\right),\; H \le N - k \Rightarrow \operatorname{cutoffLaw}\left(p, q, r, N, \operatorname{some}\left(\operatorname{inr}\left(k\right)\right), H, w\right) = \operatorname{orientedMixture}\left(p, q, r, \operatorname{minority}\left(\operatorname{theta}\left(p, q, r\right), k\right), H, w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.precutoff_agreement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k:Fin N, every H<=N-k and every complete word, the actual generated law equals G_delta_k. Horizon zero and the cutoff endpoint are included.

**Lemma 1.39 (cylinder abs sum).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cylinder_abs_sum`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cylinder_abs_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the absolute cylinder weight over every word of length t+m gives the absolute suffix sum over every word of length t.

**Lemma 1.40 (startup dominant finite).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.startup_dominant_finite`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.startup_dominant_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact finite TV between the actual startup law and the dominant pure law is delta_k times (1-u^H), including H=0.

**Lemma 1.41 (transient shift tv).**

$$\forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \left(\operatorname{admissible}\left(p, q, r\right) \land \operatorname{a}\left(p, q\right) \ne \operatorname{b}\left(r\right)\right) \Rightarrow \left(\forall N \in \operatorname{Nat}\left(\right),\; \forall k \in \operatorname{Fin}\left(N\right),\; \forall t \in \operatorname{Nat}\left(\right),\; \operatorname{totalVariation}\left(\operatorname{atHorizon}\left(\operatorname{startupLaw}\left(p, q, r, k\right), t + N - k\right), \operatorname{atHorizon}\left(\operatorname{cutoffLaw}\left(p, q, r, N, \operatorname{some}\left(\operatorname{inr}\left(k\right)\right)\right), t + N - k\right)\right) = \frac{\operatorname{T}\left(p, q, r, N\right)}{\operatorname{T}\left(p, q, r, k\right)} \cdot \operatorname{totalVariation}\left(\operatorname{atHorizon}\left(\operatorname{startupLaw}\left(p, q, r, N\right), t\right), \operatorname{atHorizon}\left(\operatorname{pureLaw}\left(p, q, r, \operatorname{dominantState}\left(p, q, r\right)\right), t\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.transient_shift_tv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every residual horizon t, the actual transient TV at horizon t+(N-k) is T_N/T_k times the residual startup-N versus dominant-pure TV.

**Lemma 1.42 (transient finite tv).**

$$\forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \left(\operatorname{admissible}\left(p, q, r\right) \land \operatorname{a}\left(p, q\right) \ne \operatorname{b}\left(r\right)\right) \Rightarrow \left(\forall N \in \operatorname{Nat}\left(\right),\; \forall k \in \operatorname{Fin}\left(N\right),\; \forall H \in \operatorname{Nat}\left(\right),\; \operatorname{totalVariation}\left(\operatorname{atHorizon}\left(\operatorname{startupLaw}\left(p, q, r, k\right), H\right), \operatorname{atHorizon}\left(\operatorname{cutoffLaw}\left(p, q, r, N, \operatorname{some}\left(\operatorname{inr}\left(k\right)\right)\right), H\right)\right) = \operatorname{ifThenElse}\left(H \le N - k, 0, \frac{\operatorname{T}\left(p, q, r, N\right)}{\operatorname{T}\left(p, q, r, k\right)} \cdot \operatorname{minority}\left(\operatorname{theta}\left(p, q, r\right), N\right) \cdot \left(1 - \operatorname{min}\left(\operatorname{a}\left(p, q\right), \operatorname{b}\left(r\right)\right)^{H - \left(N - k\right)}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.transient_finite_tv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every admissible unequal source, N, k:Fin N and natural H, actual TV is zero when H<=N-k and is (T_N/T_k)*delta_N*(1-u^(H-(N-k))) otherwise. The half-L1 sum ranges over all words.

**Lemma 1.43 (transient profile distance).**

$$\forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \left(\operatorname{admissible}\left(p, q, r\right) \land \operatorname{a}\left(p, q\right) \ne \operatorname{b}\left(r\right)\right) \Rightarrow \left(\forall N \in \operatorname{Nat}\left(\right),\; \forall k \in \operatorname{Fin}\left(N\right),\; \operatorname{profileDistance}\left(\operatorname{startupLaw}\left(p, q, r, k\right), \operatorname{cutoffLaw}\left(p, q, r, N, \operatorname{some}\left(\operatorname{inr}\left(k\right)\right)\right)\right) = \frac{\operatorname{T}\left(p, q, r, N\right)}{\operatorname{T}\left(p, q, r, k\right)} \cdot \operatorname{minority}\left(\operatorname{theta}\left(p, q, r\right), N\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.transient_profile_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The genuine supremum over all natural horizons is (T_N/T_k)*delta_N. Every residual horizon is represented by the shifted full horizon N-k+t; the frozen residual profile geometry supplies the reverse inequality.

**Lemma 1.44 (minority power ratio).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.minority_power_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.minority_power_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every admissible unequal source and natural k, delta_k=u^k/T_k in either holding orientation.

**Lemma 1.45 (T antitone).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.T_antitone`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.T_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every admissible source and natural k<=N, T_N<=T_k.

**Lemma 1.46 (transient gain).**

$$\forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \left(\operatorname{admissible}\left(p, q, r\right) \land \operatorname{a}\left(p, q\right) \ne \operatorname{b}\left(r\right)\right) \Rightarrow \left(\forall N \in \operatorname{Nat}\left(\right),\; \forall k \in \operatorname{Fin}\left(N\right),\; \frac{\operatorname{T}\left(p, q, r, N\right)}{\operatorname{T}\left(p, q, r, k\right)} \cdot \operatorname{minority}\left(\operatorname{theta}\left(p, q, r\right), N\right) = \frac{\operatorname{min}\left(\operatorname{a}\left(p, q\right), \operatorname{b}\left(r\right)\right)^{N}}{\operatorname{T}\left(p, q, r, k\right)} \land \frac{\operatorname{T}\left(p, q, r, N\right)}{\operatorname{T}\left(p, q, r, k\right)} \cdot \operatorname{minority}\left(\operatorname{theta}\left(p, q, r\right), N\right) \le \operatorname{minority}\left(\operatorname{theta}\left(p, q, r\right), N\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.transient_gain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact transient profile error is u^N/T_k and is at most delta_N.

**Lemma 1.47 (empty singleton cons).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.empty_singleton_cons`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.empty_singleton_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every singleton y in 0,1,3 and every suffix word, the actual initialized joint word weight is 1/5 times its matching pure suffix law.

**Lemma 1.48 (empty B startup).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.empty_B_startup`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.empty_B_startup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual initialized B branch has mass 2/5 and continues at the actual startup-zero law.

**Lemma 1.49 (initial difference).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.initial_difference`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.initial_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive N, initialized singleton differences vanish; the B difference is 2/5 times the actual startup-zero minus cutoff-A0 suffix difference.

**Lemma 1.50 (initial succ tv).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.initial_succ_tv`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.initial_succ_tv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive N, the actual initialized TV at H+1 is 2/5 times the startup-zero transient TV at H.

**Lemma 1.51 (initial finite tv).**

$$\forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \left(\operatorname{admissible}\left(p, q, r\right) \land \operatorname{a}\left(p, q\right) \ne \operatorname{b}\left(r\right)\right) \Rightarrow \left(\forall N \in \operatorname{Nat}\left(\right),\; 0 < N \Rightarrow \left(\forall H \in \operatorname{Nat}\left(\right),\; \operatorname{totalVariation}\left(\operatorname{atHorizon}\left(\operatorname{emptyLaw}\left(p, q, r\right), H\right), \operatorname{atHorizon}\left(\operatorname{cutoffLaw}\left(p, q, r, N, \operatorname{none}\left(\right)\right), H\right)\right) = \operatorname{ifThenElse}\left(H \le N + 1, 0, \frac{\operatorname{min}\left(\operatorname{a}\left(p, q\right), \operatorname{b}\left(r\right)\right)^{N}}{5} \cdot \left(1 - \operatorname{min}\left(\operatorname{a}\left(p, q\right), \operatorname{b}\left(r\right)\right)^{H - \left(N + 1\right)}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.initial_finite_tv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive N and natural H, initialized TV is zero through N+1 and is (u^N/5)*(1-u^(H-N-1)) thereafter. The extra initial B read is included.

**Lemma 1.52 (initial profile distance).**

$$\forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \left(\operatorname{admissible}\left(p, q, r\right) \land \operatorname{a}\left(p, q\right) \ne \operatorname{b}\left(r\right)\right) \Rightarrow \left(\forall N \in \operatorname{Nat}\left(\right),\; 0 < N \Rightarrow \operatorname{profileDistance}\left(\operatorname{emptyLaw}\left(p, q, r\right), \operatorname{cutoffLaw}\left(p, q, r, N, \operatorname{none}\left(\right)\right)\right) = \frac{\operatorname{min}\left(\operatorname{a}\left(p, q\right), \operatorname{b}\left(r\right)\right)^{N}}{5}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.initial_profile_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive N, the initialized all-horizon supremum is exactly u^N/5.

**Lemma 1.53 (initial gain le).**

$$\forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \left(\operatorname{admissible}\left(p, q, r\right) \land \operatorname{a}\left(p, q\right) \ne \operatorname{b}\left(r\right)\right) \Rightarrow \left(\forall N \in \operatorname{Nat}\left(\right),\; 0 < N \Rightarrow \frac{\operatorname{min}\left(\operatorname{a}\left(p, q\right), \operatorname{b}\left(r\right)\right)^{N}}{5} \le \operatorname{minority}\left(\operatorname{theta}\left(p, q, r\right), N\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.initial_gain_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive N, u^N/5<=delta_N.

**Lemma 1.54 (saturated profile).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.saturated_profile`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.saturated_profile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual startup index k>=N, the retained dominant pure label has exact profile error delta_k.

**Lemma 1.55 (pure history exact).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.pure_history_exact`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.pure_history_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonempty actual history classified as pure i has its actual source law at the retained pure label, without any approximate-forecast support premise.

**Lemma 1.56 (cutoff history profile).**

$$\forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \left(\operatorname{admissible}\left(p, q, r\right) \land \operatorname{a}\left(p, q\right) \ne \operatorname{b}\left(r\right)\right) \Rightarrow \left(\forall N \in \operatorname{Nat}\left(\right),\; 0 < N \Rightarrow \left(\forall h \in \operatorname{List}\left(\operatorname{Visible}\left(\right)\right),\; 0 < \operatorname{historyMass}\left(p, q, r, h\right) \Rightarrow \operatorname{profileDistance}\left(\operatorname{actualFutureWordWeight}\left(p, q, r, h\right), \operatorname{decoder}\left(\operatorname{toObserver}\left(\operatorname{cutoffGenerator}\left(p, q, r, N\right)\right), \operatorname{run}\left(\operatorname{toObserver}\left(\operatorname{cutoffGenerator}\left(p, q, r, N\right)\right), h\right)\right)\right) \le \operatorname{minority}\left(\operatorname{theta}\left(p, q, r\right), N\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoff_history_profile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every admissible unequal source, positive N and every actual positive finite history, including empty history, the actual profile error of the same-U cutoff generator is at most delta_N.

**Lemma 1.57 (cutoff accuracy).**

$$\forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \left(\operatorname{admissible}\left(p, q, r\right) \land \operatorname{a}\left(p, q\right) \ne \operatorname{b}\left(r\right)\right) \Rightarrow \left(\forall N \in \operatorname{Nat}\left(\right),\; 0 < N \Rightarrow \operatorname{Accurate}\left(\operatorname{toObserver}\left(\operatorname{cutoffGenerator}\left(p, q, r, N\right)\right), p, q, r, \operatorname{minority}\left(\operatorname{theta}\left(p, q, r\right), N\right), \operatorname{true}\left(\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoff_accuracy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One generator has the finite-horizon guarantee simultaneously for every actual positive finite history and every natural horizon. Actual legality is measured by historyMass.

**Definition 1.58 (N1).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.N1`

*Formalization.* `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.N1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N1 is the natural ceiling cutoff(theta,epsilon), using the original non-strict minority threshold.

**Lemma 1.59 (N1 threshold).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.N1_threshold`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.N1_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under 0<2 epsilon<kappa and unequal holdings, N1 is positive, delta_N1<=epsilon, every earlier index is strict, and all non-strict cutoff ties satisfy the original logarithmic equality.

**Lemma 1.60 (N1 generator accuracy).**

$$\forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \left(\operatorname{admissible}\left(p, q, r\right) \land \operatorname{a}\left(p, q\right) \ne \operatorname{b}\left(r\right)\right) \Rightarrow \left(\forall epsilon \in \operatorname{Real}\left(\right),\; \left(0 < 2 \cdot \mathit{epsilon} \land 2 \cdot \mathit{epsilon} < \operatorname{kappa}\left(p, q, r\right)\right) \Rightarrow \operatorname{Accurate}\left(\operatorname{toObserver}\left(\operatorname{cutoffGenerator}\left(p, q, r, \operatorname{N1}\left(p, q, r, \mathit{epsilon}\right)\right)\right), p, q, r, \mathit{epsilon}, \operatorname{true}\left(\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.N1_generator_accuracy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual normalized generator on the full carrier I plus five pure labels plus N1 transients is uniformly epsilon accurate on every actual finite history and every horizon.

**Lemma 1.61 (generated competing lower).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generated_competing_lower`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generated_competing_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite normalized GeneratedObserver with the original actual-history guarantee is coherent and inherits the common-law lower bound 6+N2. No reachability, calibration or forecast-positivity condition is added.

**Definition 1.62 (transport).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.transport`

*Formalization.* `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.transport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An equivalence of full carrier types transports the initial configuration, total update and every emission row.

**Lemma 1.63 (transport law).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.transport_law`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.transport_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transported generated law at e(z) equals the original generated law at z at every horizon and word.

**Lemma 1.64 (transport run).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.transport_run`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.transport_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The retained run on every finite visible list transports exactly by e.

**Lemma 1.65 (transport accurate).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.transport_accurate`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.transport_accurate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete actual-history accuracy property is preserved under full-carrier equivalence.

**Definition 1.66 (Attainable).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.Attainable`

*Formalization.* `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.Attainable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A natural carrier size n is attainable exactly when some normalized GeneratedObserver on Fin n satisfies the original initialized all-history, all-horizon accuracy guarantee.

**Lemma 1.67 (attainable constructed).**

$$\forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \left(\operatorname{admissible}\left(p, q, r\right) \land \operatorname{a}\left(p, q\right) \ne \operatorname{b}\left(r\right)\right) \Rightarrow \left(\forall epsilon \in \operatorname{Real}\left(\right),\; \left(0 < 2 \cdot \mathit{epsilon} \land 2 \cdot \mathit{epsilon} < \operatorname{kappa}\left(p, q, r\right)\right) \Rightarrow \operatorname{Attainable}\left(p, q, r, \mathit{epsilon}, 6 + \operatorname{N1}\left(p, q, r, \mathit{epsilon}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.attainable_constructed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual N1 cutoff generator transports to Fin(6+N1), proving that this complete carrier size is attainable.

**Lemma 1.68 (attainable nonempty).**

$$\forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \left(\operatorname{admissible}\left(p, q, r\right) \land \operatorname{a}\left(p, q\right) \ne \operatorname{b}\left(r\right)\right) \Rightarrow \left(\forall epsilon \in \operatorname{Real}\left(\right),\; \left(0 < 2 \cdot \mathit{epsilon} \land 2 \cdot \mathit{epsilon} < \operatorname{kappa}\left(p, q, r\right)\right) \Rightarrow \left(\exists n \in \operatorname{Nat}\left(\right),\; \operatorname{Attainable}\left(p, q, r, \mathit{epsilon}, n\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.attainable_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constructed accurate generator proves nonemptiness of the attainable finite carrier-size predicate.

**Definition 1.69 (minimum).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.minimum`

*Formalization.* `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.minimum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initialized generated-law minimum is Nat.find of the nonempty attainable carrier-size predicate, rather than a witness size or a lower bound alone.

**Lemma 1.70 (minimum attained).**

$$\forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \left(\operatorname{admissible}\left(p, q, r\right) \land \operatorname{a}\left(p, q\right) \ne \operatorname{b}\left(r\right)\right) \Rightarrow \left(\forall epsilon \in \operatorname{Real}\left(\right),\; \left(0 < 2 \cdot \mathit{epsilon} \land 2 \cdot \mathit{epsilon} < \operatorname{kappa}\left(p, q, r\right)\right) \Rightarrow \operatorname{Attainable}\left(p, q, r, \mathit{epsilon}, \operatorname{minimum}\left(p, q, r, \mathit{epsilon}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.minimum_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual least attainable initialized finite carrier size is itself attained by a normalized GeneratedObserver.

**Lemma 1.71 (minimum le).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.minimum_le`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.minimum_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The least attainable initialized finite carrier size is at most every attainable size.

**Lemma 1.72 (minimum of any carrier).**

Lean statement: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.minimum_of_any_carrier`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.minimum_of_any_carrier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every accurately initialized normalized generator on every finite carrier transports to Fin(card Z), so the actual minimum is at most its complete carrier cardinality.

**Lemma 1.73 (initialized generated minimum).**

$$\forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \left(\operatorname{admissible}\left(p, q, r\right) \land \operatorname{a}\left(p, q\right) \ne \operatorname{b}\left(r\right)\right) \Rightarrow \left(\forall epsilon \in \operatorname{Real}\left(\right),\; \left(0 < 2 \cdot \mathit{epsilon} \land 2 \cdot \mathit{epsilon} < \operatorname{kappa}\left(p, q, r\right)\right) \Rightarrow \left(\left(\left(\left(\operatorname{Attainable}\left(p, q, r, \mathit{epsilon}, \operatorname{minimum}\left(p, q, r, \mathit{epsilon}\right)\right) \land \left(\forall n \in \operatorname{Nat}\left(\right),\; \operatorname{Attainable}\left(p, q, r, \mathit{epsilon}, n\right) \Rightarrow \operatorname{minimum}\left(p, q, r, \mathit{epsilon}\right) \le n\right)\right) \land 6 + \operatorname{N2}\left(p, q, r, \mathit{epsilon}\right) \le \operatorname{minimum}\left(p, q, r, \mathit{epsilon}\right)\right) \land \operatorname{minimum}\left(p, q, r, \mathit{epsilon}\right) \le 6 + \operatorname{N1}\left(p, q, r, \mathit{epsilon}\right)\right) \land \left(\operatorname{N1}\left(p, q, r, \mathit{epsilon}\right) = \operatorname{N2}\left(p, q, r, \mathit{epsilon}\right) \Rightarrow \operatorname{minimum}\left(p, q, r, \mathit{epsilon}\right) = 6 + \operatorname{N1}\left(p, q, r, \mathit{epsilon}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.initialized_generated_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under all original admissibility, unequal-holding and small-error premises, the actual initialized minimum is attained, is no larger than every attainable size, lies between 6+N2 and 6+N1, and equals 6+N1 when N1=N2.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.Attainable`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.GeneratedObserver`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.N1`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.N1_generator_accuracy`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.N1_threshold`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.T`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.T_antitone`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.T_pos`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.actual_startup_B_recurrence`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.attainable_constructed`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.attainable_nonempty`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoffGenerator`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoffLaw`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoffRows`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoffRows_probability`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoff_accuracy`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoff_history_profile`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoff_row_is_actual`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoff_run_is_actual`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoff_singleton_total`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cutoff_startup_row`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cylinder`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cylinder_abs_sum`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cylinder_pre`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.cylinder_zero`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.empty_B_startup`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.empty_singleton_cons`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generatedLaw`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generated_coherent`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generated_competing_lower`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generated_cons`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generated_final_symbol`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generated_nonnegative`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generated_startup_B`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generated_startup_singleton`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.generated_sum`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.initial_difference`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.initial_finite_tv`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.initial_gain_le`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.initial_profile_distance`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.initial_succ_tv`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.initialized_generated_minimum`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.minimum`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.minimum_attained`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.minimum_le`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.minimum_of_any_carrier`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.minority_power_ratio`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.nextPure`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.one_step_probability`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.precutoff_agreement`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.pure_cons`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.pure_generated`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.pure_history_exact`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.pure_update`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.pure_zero`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.saturated_profile`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.singletonState`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.source_product_localization`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.startupLaw`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.startup_B`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.startup_B_row`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.startup_dominant_finite`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.startup_singleton`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.startup_zero`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.toObserver`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.transient_finite_tv`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.transient_gain`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.transient_profile_distance`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.transient_shift_tv`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.transport`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.transport_accurate`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.transport_law`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws.transport_run`
- Dependency: [D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount](FiveModeAutonomousSharpCount.md)
