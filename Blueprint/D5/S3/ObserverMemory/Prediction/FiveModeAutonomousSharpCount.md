# Five Mode Autonomous Sharp Count

## Abstract

Sharp finite autonomous common-law observers for the actual finite-start source.

The source is the literal FiniteStartFiveModeSource: State=Fin 5, Visible=Fin 4 and B=2, with uniform stationary initial distribution, p,q,r>0 and p+q+r<1. Set s=p+q, a=1-s, b=1-r and c=1-s-r. The separation constant is kappa=min(c,p,q,a,c*s/(s+r),a*p/s,a*q/s,1/25)>0. The parameter domain includes p=q and r=p+q. The empty law predicts Y0. After a nonempty actual history h, actualFutureWordWeight is the source conditional future law beginning immediately after the acquired word. An actual history has strictly positive historyMass.

Observer Z consists of an initial configuration, one total deterministic update Z times Visible to Z, and one fixed decoder Z to LawProfile. Its run is a left fold using only the retained configuration and the next acquired read. CoherentObserver means every fixed decoder is nonnegative, normalized at every natural horizon, and consistent under deleting the final symbol. This common-law contract imposes no self-generated symbol-product law and no equality between decoder conditioning and the decoder at an updated state. No hidden state, prehistory, recording length, clock or external age is an input.

Accuracy holds jointly for every actual positive finite history and every finite future horizon. The queryEmpty=true convention includes empty history; false permits queries only after reads. H=0 has the unique normalized empty word and contributes TV zero. Reached is the image of actual positive nonempty histories. FintypeCard counts the carrier, and NatCard of Reached counts its subtype. notNoneSet denotes {z | z is not None} in the displayed Option carrier, and univ denotes its entire displayed carrier. The universal bounds range over every type, every finite-carrier instance, every initial configuration, every total deterministic update and every common coherent decoder.

SharpState N is Option(State+Fin N): None is I, Some(Inl i) is Ri, and Some(Inr k) is Ak. encodeSource maps start to I, pure i to Ri, and startup k to Ak when k<N, or Rd otherwise. representative reads only the retained label. sharpUpdate is encodeSource after sourceUpdate of that representative, and is total on impossible actual extensions. Every singleton 0,1,3 resets every label to its matching pure label. On B, pure labels 0/4 go to 4 and 1/2/3 go to 2; Ak advances until it saturates at Rd. I goes to A0 when N>0, with Rd as its total fallback when N=0. foldSharp d N h denotes the fold of this update from None.

The dominant state d is 2 when a>b and 4 otherwise. On unequal holdings theta=min(a,b)/max(a,b) is in (0,1), delta_k=theta^k/(1+theta^k), and N2 is the finite positive first non-strict cutoff delta_N2<=2 epsilon. Its exact expression is ceilNat(log((1-2 epsilon)/(2 epsilon))/abs(log theta)). Every i<N2 is strict and a tie delta_N2=2 epsilon is allowed. Startup k denotes the actual acquired word B^(k+1); startupState O k is its actual observer run. The Bstep of an update is the map z to update z B, and iterate uses a finite natural exponent.

midpointObserver uses N=N2 and beta=delta_N2/2. It decodes I by the actual empty law, Ak by the actual startup law G_delta_k, Rd by G_beta, and every other Ri by Fi. G_z=(1-z)Fd+zFf uses the matching dominant branch in both orientations. Saturated startup histories and synchronized dominant histories are within epsilon of this one midpoint; all other queried histories are exact. Pure witnesses 0,1,1B,3,0B have masses 1/5,1/5,p/5,1/5,r/5. Every transient witness B^(k+1) is positive. Thus every charged label belongs to this same actual reached image.

A collision i<j on the startup orbit recurs at i+ell(j-i), by the same total B update. Each corresponding history is finite and positive. At each finite H, triangles bound the fixed decoder at the collision state by epsilon+delta_(i+ell(j-i)) from the dominant law. Geometric decay then constrains that fixed decoder within epsilon, and the horizon supremum forces delta_i<=2 epsilon. No infinite all-B query, decoder continuity, assumed profile completion or supplied age occurs.

For after-read-only unequal observers, initialization cannot be a synchronized reached state: append a positive B in both contexts and compare the first-read half-mixture with pure 2 or 4 at distance one half. It cannot be a startup state either, because that makes startup zero recur and forces delta_0=1/2<=2 epsilon. This argument never queries the initial decoder and adds initialization to the same five-plus-N2 reached injection.

The equality post-read carrier is State+Unit, whose Unit label has the half-mixture law and a B self-loop. It initializes directly at that label. The initialized equality carrier is Option(State+Unit), with an additional I decoded by the actual empty law. Every singleton resets either machine to its pure label. The separate r=p+q argument gives exact predictions for all queried positive histories, and the independent injections give six post-read-only total states or seven initialized total states. Both machines reach exactly six labels after reads. These minima hold at epsilon=0 and at every nonnegative tolerance with 2 epsilon<kappa; no unequal theorem is specialized at theta=1.

Observer run: $(\forall Z: Type,\ (\forall O: \operatorname{Observer}\left(Z\right),\ (\forall h: \operatorname{List}\left(Visible\right),\ \operatorname{run}\left(O, h\right) = \operatorname{foldl}\left(\operatorname{update}\left(O\right), \operatorname{initial}\left(O\right), h\right))))$

Observer coherent: $(\forall Z: Type,\ (\forall O: \operatorname{Observer}\left(Z\right),\ (\operatorname{CoherentObserver}\left(O\right) \iff (\forall z: Z,\ \operatorname{CoherentProfile}\left(\operatorname{decoder}\left(O, z\right)\right)))))$

Observer accurate: $(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\forall epsilon: \mathbb{R},\ (\forall Z: Type,\ (\forall O: \operatorname{Observer}\left(Z\right),\ (\forall queryEmpty: Bool,\ (\operatorname{Accurate}\left(O, p, q, r, epsilon, queryEmpty\right) \iff (\forall h: \operatorname{List}\left(Visible\right),\ (0 < \operatorname{historyMass}\left(p, q, r, h\right) \Rightarrow ((queryEmpty = true \lor h \neq \operatorname{nil}\left(\right)) \Rightarrow (\forall H: \mathbb{N},\ \operatorname{TV}\left(\operatorname{at}\left(\operatorname{actualFutureWordWeight}\left(p, q, r, h\right), H\right), \operatorname{at}\left(\operatorname{decoder}\left(O, \operatorname{run}\left(O, h\right)\right), H\right)\right) \leq epsilon))))))))))))$

Observer reached: $(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\forall Z: Type,\ (\forall O: \operatorname{Observer}\left(Z\right),\ (\forall z: Z,\ (z \in \operatorname{Reached}\left(O, p, q, r\right) \iff (\exists h: \operatorname{List}\left(Visible\right),\ (h \neq \operatorname{nil}\left(\right) \land (0 < \operatorname{historyMass}\left(p, q, r, h\right) \land \operatorname{run}\left(O, h\right) = z))))))))))$

**Theorem 1.1 (Run snoc).**

$$(\forall Z: Type,\ (\forall O: \operatorname{Observer}\left(Z\right),\ (\forall h: \operatorname{List}\left(Visible\right),\ (\forall y: Visible,\ \operatorname{run}\left(O, \operatorname{append}\left(h, \operatorname{singleton}\left(y\right)\right)\right) = \operatorname{update}\left(O, \operatorname{run}\left(O, h\right), y\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.run_snoc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An appended symbol applies the same total update to the current retained state.

**Theorem 1.2 (Actual coherent).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall h: \operatorname{List}\left(Visible\right),\ (0 < \operatorname{historyMass}\left(p, q, r, h\right) \Rightarrow \operatorname{CoherentProfile}\left(\operatorname{actualFutureWordWeight}\left(p, q, r, h\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.actual_coherent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive finite histories induce normalized actual laws with final-symbol consistency.

**Theorem 1.3 (Accurate profile).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\forall epsilon: \mathbb{R},\ (\forall Z: Type,\ (\forall O: \operatorname{Observer}\left(Z\right),\ (\forall queryEmpty: Bool,\ (\operatorname{Accurate}\left(O, p, q, r, epsilon, queryEmpty\right) \Rightarrow (\forall h: \operatorname{List}\left(Visible\right),\ ((0 < \operatorname{historyMass}\left(p, q, r, h\right) \land (queryEmpty = true \lor h \neq \operatorname{nil}\left(\right))) \Rightarrow \operatorname{profileDistance}\left(\operatorname{actualFutureWordWeight}\left(p, q, r, h\right), \operatorname{decoder}\left(O, \operatorname{run}\left(O, h\right)\right)\right) \leq epsilon))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.accurate_profile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The uniform finite-horizon error bound also bounds its supremum.

**Theorem 1.4 (Common state distance).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\forall epsilon: \mathbb{R},\ (\forall Z: Type,\ (\forall O: \operatorname{Observer}\left(Z\right),\ (\forall queryEmpty: Bool,\ (\operatorname{Accurate}\left(O, p, q, r, epsilon, queryEmpty\right) \Rightarrow (\forall h: \operatorname{List}\left(Visible\right),\ (\forall t: \operatorname{List}\left(Visible\right),\ ((0 < \operatorname{historyMass}\left(p, q, r, h\right) \land (0 < \operatorname{historyMass}\left(p, q, r, t\right) \land ((queryEmpty = true \lor h \neq \operatorname{nil}\left(\right)) \land ((queryEmpty = true \lor t \neq \operatorname{nil}\left(\right)) \land \operatorname{run}\left(O, h\right) = \operatorname{run}\left(O, t\right))))) \Rightarrow \operatorname{profileDistance}\left(\operatorname{actualFutureWordWeight}\left(p, q, r, h\right), \operatorname{actualFutureWordWeight}\left(p, q, r, t\right)\right) \leq (2*epsilon))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.common_state_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One shared decoder and two finite-horizon triangles bound the true-law distance by twice epsilon.

**Theorem 1.5 (Dominant successor).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ \operatorname{pureBSuccessor}\left(\operatorname{dominantState}\left(p, q, r\right)\right) = \operatorname{dominantState}\left(p, q, r\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.dominant_successor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both possible dominant labels remain at the same pure label under B.

**Theorem 1.6 (Dominant law).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ \operatorname{pureLaw}\left(p, q, r, \operatorname{dominantState}\left(p, q, r\right)\right) = \operatorname{dominantLaw}\left(p, q, r\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.dominant_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The selected dominant state uses its matching pure future law.

**Theorem 1.7 (Sharp source step).**

$$(\forall d: State,\ (\forall N: \mathbb{N},\ (\operatorname{pureBSuccessor}\left(d\right) = d \Rightarrow (\forall z: SourceTag,\ (\forall y: Visible,\ \operatorname{sharpUpdate}\left(d, N, \operatorname{encodeSource}\left(d, N, z\right), y\right) = \operatorname{encodeSource}\left(d, N, \operatorname{sourceUpdate}\left(z, y\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.sharp_source_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every visible read preserves the projection, including the saturated boundary and impossible extensions.

**Theorem 1.8 (Sharp source run).**

$$(\forall d: State,\ (\forall N: \mathbb{N},\ (\operatorname{pureBSuccessor}\left(d\right) = d \Rightarrow (\forall h: \operatorname{List}\left(Visible\right),\ \operatorname{foldSharp}\left(d, N, h\right) = \operatorname{encodeSource}\left(d, N, \operatorname{sourceRun}\left(h\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.sharp_source_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The total-update projection is preserved along every finite word.

**Theorem 1.9 (Midpoint run).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\forall epsilon: \mathbb{R},\ (\forall h: \operatorname{List}\left(Visible\right),\ \operatorname{run}\left(\operatorname{midpointObserver}\left(p, q, r, epsilon\right), h\right) = \operatorname{encodeSource}\left(\operatorname{dominantState}\left(p, q, r\right), \operatorname{N2}\left(p, q, r, epsilon\right), \operatorname{sourceRun}\left(h\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.midpoint_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The run is a function of the acquired word through one retained-state update.

**Theorem 1.10 (Midpoint decoder coherent).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\operatorname{a}\left(p, q\right) \neq \operatorname{b}\left(r\right) \Rightarrow (\forall epsilon: \mathbb{R},\ ((0 < (2*epsilon) \land (2*epsilon) < \operatorname{kappa}\left(p, q, r\right)) \Rightarrow \operatorname{CoherentObserver}\left(\operatorname{midpointObserver}\left(p, q, r, epsilon\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.midpoint_decoder_coherent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every label has one normalized, marginally coherent complete-law decoder.

**Theorem 1.11 (Actual pure law).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\forall h: \operatorname{List}\left(Visible\right),\ (h \neq \operatorname{nil}\left(\right) \Rightarrow (\forall i: State,\ (\operatorname{acquiredPosterior}\left(p, q, r, h\right) = \operatorname{pureVector}\left(i\right) \Rightarrow \operatorname{actualFutureWordWeight}\left(p, q, r, h\right) = \operatorname{pureLaw}\left(p, q, r, i\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.actual_pure_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonempty boundary with point-mass posterior has that point mass's pure future law.

**Theorem 1.12 (Midpoint observer accuracy).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\operatorname{a}\left(p, q\right) \neq \operatorname{b}\left(r\right) \Rightarrow (\forall epsilon: \mathbb{R},\ ((0 < (2*epsilon) \land (2*epsilon) < \operatorname{kappa}\left(p, q, r\right)) \Rightarrow \operatorname{Accurate}\left(\operatorname{midpointObserver}\left(p, q, r, epsilon\right), p, q, r, epsilon, true\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.midpoint_observer_accuracy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual startup tail and dominant pure state use the same midpoint, uniformly over all actual histories and horizons.

**Theorem 1.13 (Sharp state card).**

$$(\forall N: \mathbb{N},\ \operatorname{FintypeCard}\left(\operatorname{SharpState}\left(N\right)\right) = (6+N))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.sharp_state_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One initialization label, five pure labels and N transient labels give six plus N.

**Theorem 1.14 (Midpoint reached iff).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall epsilon: \mathbb{R},\ (\forall z: \operatorname{SharpState}\left(\operatorname{N2}\left(p, q, r, epsilon\right)\right),\ (z \in \operatorname{Reached}\left(\operatorname{midpointObserver}\left(p, q, r, epsilon\right), p, q, r\right) \iff z \neq None)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.midpoint_reached_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every Some label is actually reached and no positive nonempty word reaches None.

**Theorem 1.15 (Midpoint observer reachability).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall epsilon: \mathbb{R},\ (\operatorname{Reached}\left(\operatorname{midpointObserver}\left(p, q, r, epsilon\right), p, q, r\right) = \operatorname{notNoneSet}\left(\right) \land (\operatorname{NatCard}\left(\operatorname{Reached}\left(\operatorname{midpointObserver}\left(p, q, r, epsilon\right), p, q, r\right)\right) = (5+\operatorname{N2}\left(p, q, r, epsilon\right)) \land \operatorname{FintypeCard}\left(\operatorname{SharpState}\left(\operatorname{N2}\left(p, q, r, epsilon\right)\right)\right) = (6+\operatorname{N2}\left(p, q, r, epsilon\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.midpoint_observer_reachability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual image has five plus N2 labels, while the total carrier has six plus N2.

**Theorem 1.16 (Fold replicate).**

$$(\forall Z: Type,\ (\forall u: Z \to Visible \to Z,\ (\forall z: Z,\ (\forall n: \mathbb{N},\ \operatorname{foldl}\left(u, z, \operatorname{replicate}\left(n, B\right)\right) = \operatorname{iterate}\left(\operatorname{Bstep}\left(u\right), n, z\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.fold_replicate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite repeated input is an iterate of the corresponding total update.

**Theorem 1.17 (Startup shift).**

$$(\forall Z: Type,\ (\forall O: \operatorname{Observer}\left(Z\right),\ (\forall i: \mathbb{N},\ (\forall n: \mathbb{N},\ \operatorname{startupState}\left(O, (i+n)\right) = \operatorname{iterate}\left(\operatorname{BstepObserver}\left(O\right), n, \operatorname{startupState}\left(O, i\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.startup_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The startup index increases by the number of appended B reads.

**Theorem 1.18 (Startup collision recurrence).**

$$(\forall Z: Type,\ (\forall O: \operatorname{Observer}\left(Z\right),\ (\forall i: \mathbb{N},\ (\forall j: \mathbb{N},\ ((i < j \land \operatorname{startupState}\left(O, i\right) = \operatorname{startupState}\left(O, j\right)) \Rightarrow (\forall ell: \mathbb{N},\ \operatorname{startupState}\left(O, (i+(ell*(j-i)))\right) = \operatorname{startupState}\left(O, i\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.startup_collision_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A collision fixes the retained state at every finite repetition of its gap.

**Theorem 1.19 (Recurring decoder dominant bound).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\operatorname{a}\left(p, q\right) \neq \operatorname{b}\left(r\right) \Rightarrow (\forall epsilon: \mathbb{R},\ (\forall Z: Type,\ (\forall O: \operatorname{Observer}\left(Z\right),\ (\forall queryEmpty: Bool,\ (\operatorname{Accurate}\left(O, p, q, r, epsilon, queryEmpty\right) \Rightarrow (\forall i: \mathbb{N},\ (\forall j: \mathbb{N},\ ((i < j \land \operatorname{startupState}\left(O, i\right) = \operatorname{startupState}\left(O, j\right)) \Rightarrow (\forall H: \mathbb{N},\ \operatorname{TV}\left(\operatorname{at}\left(\operatorname{decoder}\left(O, \operatorname{startupState}\left(O, i\right)\right), H\right), \operatorname{at}\left(\operatorname{dominantLaw}\left(p, q, r\right), H\right)\right) \leq epsilon))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.recurring_decoder_dominant_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite-horizon triangles and geometric decay constrain one fixed decoder; no infinite all-B query is used.

**Theorem 1.20 (Startup collision forces cutoff).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\operatorname{a}\left(p, q\right) \neq \operatorname{b}\left(r\right) \Rightarrow (\forall epsilon: \mathbb{R},\ (\forall Z: Type,\ (\forall O: \operatorname{Observer}\left(Z\right),\ (\forall queryEmpty: Bool,\ ((\operatorname{CoherentObserver}\left(O\right) \land \operatorname{Accurate}\left(O, p, q, r, epsilon, queryEmpty\right)) \Rightarrow (\forall i: \mathbb{N},\ (\forall j: \mathbb{N},\ ((i < j \land \operatorname{startupState}\left(O, i\right) = \operatorname{startupState}\left(O, j\right)) \Rightarrow \operatorname{minority}\left(\operatorname{theta}\left(p, q, r\right), i\right) \leq (2*epsilon))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.startup_collision_forces_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The horizon supremum forces the non-strict delta_i threshold without restricting the decoder to mixtures.

**Theorem 1.21 (Pure witness actual).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall i: State,\ (\operatorname{pureWitness}\left(i\right) \neq \operatorname{nil}\left(\right) \land (0 < \operatorname{historyMass}\left(p, q, r, \operatorname{pureWitness}\left(i\right)\right) \land \operatorname{actualFutureWordWeight}\left(p, q, r, \operatorname{pureWitness}\left(i\right)\right) = \operatorname{pureLaw}\left(p, q, r, i\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.pure_witness_actual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The five exhibited histories are nonempty, positive and have their matching pure laws.

**Theorem 1.22 (Charged reached).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall Z: Type,\ (\forall O: \operatorname{Observer}\left(Z\right),\ (\forall N: \mathbb{N},\ (\forall t: \operatorname{Sum}\left(State, \operatorname{Fin}\left(N\right)\right),\ \operatorname{chargedState}\left(O, N, t\right) \in \operatorname{Reached}\left(O, p, q, r\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.charged_reached` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pure and transient witnesses belong to one actual reached image.

**Theorem 1.23 (Unequal charged injective).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\operatorname{a}\left(p, q\right) \neq \operatorname{b}\left(r\right) \Rightarrow (\forall epsilon: \mathbb{R},\ ((0 < (2*epsilon) \land (2*epsilon) < \operatorname{kappa}\left(p, q, r\right)) \Rightarrow (\forall Z: Type,\ (\forall O: \operatorname{Observer}\left(Z\right),\ (\forall queryEmpty: Bool,\ ((\operatorname{CoherentObserver}\left(O\right) \land \operatorname{Accurate}\left(O, p, q, r, epsilon, queryEmpty\right)) \Rightarrow \operatorname{Injective}\left(\operatorname{chargedState}\left(O, \operatorname{N2}\left(p, q, r, epsilon\right)\right)\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.unequal_charged_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pre-cutoff startup collisions are forbidden, and each pure law is separate from every charged startup law.

**Theorem 1.24 (Initial b half).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow \operatorname{actualFutureWordWeight}\left(p, q, r, \operatorname{singleton}\left(B\right)\right) = \operatorname{mixtureLaw}\left(p, q, r, \frac{1}{2}\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.initial_B_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first acquired B has equal posterior weights on the two hidden B branches.

**Theorem 1.25 (Half pure b distance).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall i: State,\ \operatorname{profileDistance}\left(\operatorname{mixtureLaw}\left(p, q, r, \frac{1}{2}\right), \operatorname{pureLaw}\left(p, q, r, \operatorname{pureBSuccessor}\left(i\right)\right)\right) = \frac{1}{2})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.half_pure_B_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Either pure B successor is at complete-law distance one half from the first-read half-mixture.

**Theorem 1.26 (Postread initialization extra state).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\operatorname{a}\left(p, q\right) \neq \operatorname{b}\left(r\right) \Rightarrow (\forall epsilon: \mathbb{R},\ ((2*epsilon) < \operatorname{kappa}\left(p, q, r\right) \Rightarrow (\forall Z: Type,\ (\forall O: \operatorname{Observer}\left(Z\right),\ (\forall queryEmpty: Bool,\ ((\operatorname{CoherentObserver}\left(O\right) \land \operatorname{Accurate}\left(O, p, q, r, epsilon, queryEmpty\right)) \Rightarrow (\forall h: \operatorname{List}\left(Visible\right),\ ((h \neq \operatorname{nil}\left(\right) \land 0 < \operatorname{historyMass}\left(p, q, r, h\right)) \Rightarrow \operatorname{initial}\left(O\right) \neq \operatorname{run}\left(O, h\right))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.postread_initialization_extra_state` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive appended B separates synchronized states from initialization, and recurrence excludes startup states, without querying the initial decoder.

**Theorem 1.27 (Unequal initialized injective).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\operatorname{a}\left(p, q\right) \neq \operatorname{b}\left(r\right) \Rightarrow (\forall epsilon: \mathbb{R},\ ((0 < (2*epsilon) \land (2*epsilon) < \operatorname{kappa}\left(p, q, r\right)) \Rightarrow (\forall Z: Type,\ (\forall O: \operatorname{Observer}\left(Z\right),\ (\forall queryEmpty: Bool,\ ((\operatorname{CoherentObserver}\left(O\right) \land \operatorname{Accurate}\left(O, p, q, r, epsilon, queryEmpty\right)) \Rightarrow \operatorname{Injective}\left(\operatorname{initializedCharged}\left(O, \operatorname{N2}\left(p, q, r, epsilon\right)\right)\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.unequal_initialized_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Initialization adds to the same actual pure/transient injection.

**Theorem 1.28 (Universal unequal lower bound).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\operatorname{a}\left(p, q\right) \neq \operatorname{b}\left(r\right) \Rightarrow (\forall epsilon: \mathbb{R},\ ((0 < (2*epsilon) \land (2*epsilon) < \operatorname{kappa}\left(p, q, r\right)) \Rightarrow (\forall Z: Type,\ (\forall inst: \operatorname{Fintype}\left(Z\right),\ (\forall O: \operatorname{Observer}\left(Z\right),\ (\forall queryEmpty: Bool,\ ((\operatorname{CoherentObserver}\left(O\right) \land \operatorname{Accurate}\left(O, p, q, r, epsilon, queryEmpty\right)) \Rightarrow ((6+\operatorname{N2}\left(p, q, r, epsilon\right)) \leq \operatorname{FintypeCard}\left(Z\right) \land (5+\operatorname{N2}\left(p, q, r, epsilon\right)) \leq \operatorname{NatCard}\left(\operatorname{Reached}\left(O, p, q, r\right)\right))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.universal_unequal_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All arbitrary finite deterministic competitors obey both lower counts under either query convention.

**Theorem 1.29 (Equality project step).**

$$(\forall z: SourceTag,\ (\forall y: Visible,\ \operatorname{equalityUpdate}\left(\operatorname{equalityProject}\left(z\right), y\right) = \operatorname{equalityProject}\left(\operatorname{sourceUpdate}\left(z, y\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.equality_project_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Start and every startup tag share the B-fixed half-mixture label in the post-read carrier.

**Theorem 1.30 (Equality initialized step).**

$$(\forall z: SourceTag,\ (\forall y: Visible,\ \operatorname{equalityInitializedUpdate}\left(\operatorname{equalityInitializedProject}\left(z\right), y\right) = \operatorname{equalityInitializedProject}\left(\operatorname{sourceUpdate}\left(z, y\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.equality_initialized_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The initialized carrier preserves a separate initial label and collapses all startup tags.

**Theorem 1.31 (Equality run invariants).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\forall h: \operatorname{List}\left(Visible\right),\ (\operatorname{run}\left(\operatorname{equalityPostreadObserver}\left(p, q, r\right), h\right) = \operatorname{equalityProject}\left(\operatorname{sourceRun}\left(h\right)\right) \land \operatorname{run}\left(\operatorname{equalityInitializedObserver}\left(p, q, r\right), h\right) = \operatorname{equalityInitializedProject}\left(\operatorname{sourceRun}\left(h\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.equality_run_invariants` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both total updates preserve their source-tag projection along all finite words.

**Theorem 1.32 (Equality decoder coherent).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\operatorname{CoherentObserver}\left(\operatorname{equalityPostreadObserver}\left(p, q, r\right)\right) \land \operatorname{CoherentObserver}\left(\operatorname{equalityInitializedObserver}\left(p, q, r\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.equality_decoder_coherent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual empty, pure and half-mixture profiles are coherent.

**Theorem 1.33 (Equality observers exact).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (r = (p+q) \Rightarrow ((\forall h: \operatorname{List}\left(Visible\right),\ (h \neq \operatorname{nil}\left(\right) \Rightarrow (0 < \operatorname{historyMass}\left(p, q, r, h\right) \Rightarrow \operatorname{decoder}\left(\operatorname{equalityPostreadObserver}\left(p, q, r\right), \operatorname{run}\left(\operatorname{equalityPostreadObserver}\left(p, q, r\right), h\right)\right) = \operatorname{actualFutureWordWeight}\left(p, q, r, h\right)))) \land (\forall h: \operatorname{List}\left(Visible\right),\ (0 < \operatorname{historyMass}\left(p, q, r, h\right) \Rightarrow \operatorname{decoder}\left(\operatorname{equalityInitializedObserver}\left(p, q, r\right), \operatorname{run}\left(\operatorname{equalityInitializedObserver}\left(p, q, r\right), h\right)\right) = \operatorname{actualFutureWordWeight}\left(p, q, r, h\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.equality_observers_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of the holding probabilities makes both machines exact on their entire queried actual domains.

**Theorem 1.34 (Equality observer accuracy).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (r = (p+q) \Rightarrow (\forall epsilon: \mathbb{R},\ (0 \leq epsilon \Rightarrow (\operatorname{Accurate}\left(\operatorname{equalityPostreadObserver}\left(p, q, r\right), p, q, r, epsilon, false\right) \land \operatorname{Accurate}\left(\operatorname{equalityInitializedObserver}\left(p, q, r\right), p, q, r, epsilon, true\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.equality_observer_accuracy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact law reconstruction gives zero TV error at every future horizon.

**Theorem 1.35 (Equality reached all).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\operatorname{Reached}\left(\operatorname{equalityPostreadObserver}\left(p, q, r\right), p, q, r\right) = \operatorname{univ}\left(\right) \land \operatorname{Reached}\left(\operatorname{equalityInitializedObserver}\left(p, q, r\right), p, q, r\right) = \operatorname{notNoneSet}\left(\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.equality_reached_all` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All six post-read labels have actual witnesses; the initialized label is additional.

**Theorem 1.36 (Half pure separation).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall i: State,\ \operatorname{kappa}\left(p, q, r\right) \leq \operatorname{profileDistance}\left(\operatorname{mixtureLaw}\left(p, q, r, \frac{1}{2}\right), \operatorname{pureLaw}\left(p, q, r, i\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.half_pure_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The half-mixture is separated from all five pure laws without excluding p=q.

**Theorem 1.37 (Equality charged reached).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall Z: Type,\ (\forall O: \operatorname{Observer}\left(Z\right),\ (\forall z: \operatorname{Sum}\left(State, Unit\right),\ \operatorname{equalityCharged}\left(O, z\right) \in \operatorname{Reached}\left(O, p, q, r\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.equality_charged_reached` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The five pure witnesses and first B give six actual reached states.

**Theorem 1.38 (Equality charged injective).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall epsilon: \mathbb{R},\ ((2*epsilon) < \operatorname{kappa}\left(p, q, r\right) \Rightarrow (\forall Z: Type,\ (\forall O: \operatorname{Observer}\left(Z\right),\ (\forall queryEmpty: Bool,\ (\operatorname{Accurate}\left(O, p, q, r, epsilon, queryEmpty\right) \Rightarrow \operatorname{Injective}\left(\operatorname{equalityCharged}\left(O\right)\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.equality_charged_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Six separated actual laws require six distinct retained configurations.

**Theorem 1.39 (Equality initialized injective).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall epsilon: \mathbb{R},\ ((2*epsilon) < \operatorname{kappa}\left(p, q, r\right) \Rightarrow (\forall Z: Type,\ (\forall O: \operatorname{Observer}\left(Z\right),\ (\operatorname{Accurate}\left(O, p, q, r, epsilon, true\right) \Rightarrow \operatorname{Injective}\left(\operatorname{equalityInitializedCharged}\left(O\right)\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.equality_initialized_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The queryable empty law is separate from all six charged post-read laws.

**Theorem 1.40 (Universal equality lower bounds).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall epsilon: \mathbb{R},\ ((2*epsilon) < \operatorname{kappa}\left(p, q, r\right) \Rightarrow (\forall Z: Type,\ (\forall inst: \operatorname{Fintype}\left(Z\right),\ (\forall O: \operatorname{Observer}\left(Z\right),\ ((\operatorname{Accurate}\left(O, p, q, r, epsilon, false\right) \Rightarrow (6 \leq \operatorname{FintypeCard}\left(Z\right) \land 6 \leq \operatorname{NatCard}\left(\operatorname{Reached}\left(O, p, q, r\right)\right))) \land (\operatorname{Accurate}\left(O, p, q, r, epsilon, true\right) \Rightarrow (7 \leq \operatorname{FintypeCard}\left(Z\right) \land 6 \leq \operatorname{NatCard}\left(\operatorname{Reached}\left(O, p, q, r\right)\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.universal_equality_lower_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The independent equality injections yield six post-read-only or seven initialized total states, including tolerance zero.

**Theorem 1.41 (Equality observer cardinalities).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\operatorname{FintypeCard}\left(\operatorname{Sum}\left(State, Unit\right)\right) = 6 \land (\operatorname{FintypeCard}\left(\operatorname{Option}\left(\operatorname{Sum}\left(State, Unit\right)\right)\right) = 7 \land (\operatorname{NatCard}\left(\operatorname{Reached}\left(\operatorname{equalityPostreadObserver}\left(p, q, r\right), p, q, r\right)\right) = 6 \land \operatorname{NatCard}\left(\operatorname{Reached}\left(\operatorname{equalityInitializedObserver}\left(p, q, r\right), p, q, r\right)\right) = 6)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.equality_observer_cardinalities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carriers have six and seven labels and both post-read images have six.

**Theorem 1.42 (Sharp initialized common decoder).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall epsilon: \mathbb{R},\ ((r \neq (p+q) \land (0 < (2*epsilon) \land (2*epsilon) < \operatorname{kappa}\left(p, q, r\right))) \Rightarrow (\operatorname{CoherentObserver}\left(\operatorname{midpointObserver}\left(p, q, r, epsilon\right)\right) \land (\operatorname{Accurate}\left(\operatorname{midpointObserver}\left(p, q, r, epsilon\right), p, q, r, epsilon, true\right) \land (\operatorname{FintypeCard}\left(\operatorname{SharpState}\left(\operatorname{N2}\left(p, q, r, epsilon\right)\right)\right) = (6+\operatorname{N2}\left(p, q, r, epsilon\right)) \land (\operatorname{NatCard}\left(\operatorname{Reached}\left(\operatorname{midpointObserver}\left(p, q, r, epsilon\right), p, q, r\right)\right) = (5+\operatorname{N2}\left(p, q, r, epsilon\right)) \land (\forall Z: Type,\ (\forall inst: \operatorname{Fintype}\left(Z\right),\ (\forall O: \operatorname{Observer}\left(Z\right),\ (\operatorname{CoherentObserver}\left(O\right) \Rightarrow (\operatorname{Accurate}\left(O, p, q, r, epsilon, true\right) \Rightarrow ((6+\operatorname{N2}\left(p, q, r, epsilon\right)) \leq \operatorname{FintypeCard}\left(Z\right) \land (5+\operatorname{N2}\left(p, q, r, epsilon\right)) \leq \operatorname{NatCard}\left(\operatorname{Reached}\left(O, p, q, r\right)\right)))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.sharp_initialized_common_decoder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original source assumptions derive an attainable six-plus-N2 total and five-plus-N2 reached minimum for a common coherent decoder.

**Theorem 1.43 (Sharp postread reached common decoder).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall epsilon: \mathbb{R},\ ((r \neq (p+q) \land (0 < (2*epsilon) \land (2*epsilon) < \operatorname{kappa}\left(p, q, r\right))) \Rightarrow (\operatorname{CoherentObserver}\left(\operatorname{midpointObserver}\left(p, q, r, epsilon\right)\right) \land (\operatorname{Accurate}\left(\operatorname{midpointObserver}\left(p, q, r, epsilon\right), p, q, r, epsilon, false\right) \land (\operatorname{NatCard}\left(\operatorname{Reached}\left(\operatorname{midpointObserver}\left(p, q, r, epsilon\right), p, q, r\right)\right) = (5+\operatorname{N2}\left(p, q, r, epsilon\right)) \land (\forall Z: Type,\ (\forall inst: \operatorname{Fintype}\left(Z\right),\ (\forall O: \operatorname{Observer}\left(Z\right),\ (\operatorname{CoherentObserver}\left(O\right) \Rightarrow (\operatorname{Accurate}\left(O, p, q, r, epsilon, false\right) \Rightarrow (5+\operatorname{N2}\left(p, q, r, epsilon\right)) \leq \operatorname{NatCard}\left(\operatorname{Reached}\left(O, p, q, r\right)\right)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.sharp_postread_reached_common_decoder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With no empty query the exact reached minimum is still five plus N2.

**Theorem 1.44 (Postread only unequal minimum).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (\forall epsilon: \mathbb{R},\ ((r \neq (p+q) \land (0 < (2*epsilon) \land (2*epsilon) < \operatorname{kappa}\left(p, q, r\right))) \Rightarrow (\operatorname{CoherentObserver}\left(\operatorname{midpointObserver}\left(p, q, r, epsilon\right)\right) \land (\operatorname{Accurate}\left(\operatorname{midpointObserver}\left(p, q, r, epsilon\right), p, q, r, epsilon, false\right) \land (\operatorname{FintypeCard}\left(\operatorname{SharpState}\left(\operatorname{N2}\left(p, q, r, epsilon\right)\right)\right) = (6+\operatorname{N2}\left(p, q, r, epsilon\right)) \land (\operatorname{NatCard}\left(\operatorname{Reached}\left(\operatorname{midpointObserver}\left(p, q, r, epsilon\right), p, q, r\right)\right) = (5+\operatorname{N2}\left(p, q, r, epsilon\right)) \land (\forall Z: Type,\ (\forall inst: \operatorname{Fintype}\left(Z\right),\ (\forall O: \operatorname{Observer}\left(Z\right),\ (\operatorname{CoherentObserver}\left(O\right) \Rightarrow (\operatorname{Accurate}\left(O, p, q, r, epsilon, false\right) \Rightarrow ((6+\operatorname{N2}\left(p, q, r, epsilon\right)) \leq \operatorname{FintypeCard}\left(Z\right) \land (5+\operatorname{N2}\left(p, q, r, epsilon\right)) \leq \operatorname{NatCard}\left(\operatorname{Reached}\left(O, p, q, r\right)\right)))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.postread_only_unequal_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Initialization still requires an additional total configuration, although it is never queried.

**Theorem 1.45 (Equality observer minima).**

$$(\forall p: \mathbb{R},\ (\forall q: \mathbb{R},\ (\forall r: \mathbb{R},\ (\operatorname{admissible}\left(p, q, r\right) \Rightarrow (r = (p+q) \Rightarrow (\forall epsilon: \mathbb{R},\ ((0 \leq epsilon \land (2*epsilon) < \operatorname{kappa}\left(p, q, r\right)) \Rightarrow (\operatorname{CoherentObserver}\left(\operatorname{equalityInitializedObserver}\left(p, q, r\right)\right) \land (\operatorname{CoherentObserver}\left(\operatorname{equalityPostreadObserver}\left(p, q, r\right)\right) \land (\operatorname{Accurate}\left(\operatorname{equalityInitializedObserver}\left(p, q, r\right), p, q, r, epsilon, true\right) \land (\operatorname{Accurate}\left(\operatorname{equalityPostreadObserver}\left(p, q, r\right), p, q, r, epsilon, false\right) \land (\operatorname{FintypeCard}\left(\operatorname{Option}\left(\operatorname{Sum}\left(State, Unit\right)\right)\right) = 7 \land (\operatorname{FintypeCard}\left(\operatorname{Sum}\left(State, Unit\right)\right) = 6 \land (\operatorname{NatCard}\left(\operatorname{Reached}\left(\operatorname{equalityInitializedObserver}\left(p, q, r\right), p, q, r\right)\right) = 6 \land (\operatorname{NatCard}\left(\operatorname{Reached}\left(\operatorname{equalityPostreadObserver}\left(p, q, r\right), p, q, r\right)\right) = 6 \land ((\forall h: \operatorname{List}\left(Visible\right),\ (0 < \operatorname{historyMass}\left(p, q, r, h\right) \Rightarrow \operatorname{decoder}\left(\operatorname{equalityInitializedObserver}\left(p, q, r\right), \operatorname{run}\left(\operatorname{equalityInitializedObserver}\left(p, q, r\right), h\right)\right) = \operatorname{actualFutureWordWeight}\left(p, q, r, h\right))) \land ((\forall h: \operatorname{List}\left(Visible\right),\ (h \neq \operatorname{nil}\left(\right) \Rightarrow (0 < \operatorname{historyMass}\left(p, q, r, h\right) \Rightarrow \operatorname{decoder}\left(\operatorname{equalityPostreadObserver}\left(p, q, r\right), \operatorname{run}\left(\operatorname{equalityPostreadObserver}\left(p, q, r\right), h\right)\right) = \operatorname{actualFutureWordWeight}\left(p, q, r, h\right)))) \land (\forall Z: Type,\ (\forall inst: \operatorname{Fintype}\left(Z\right),\ (\forall O: \operatorname{Observer}\left(Z\right),\ ((\operatorname{CoherentObserver}\left(O\right) \Rightarrow (\operatorname{Accurate}\left(O, p, q, r, epsilon, true\right) \Rightarrow (7 \leq \operatorname{FintypeCard}\left(Z\right) \land 6 \leq \operatorname{NatCard}\left(\operatorname{Reached}\left(O, p, q, r\right)\right)))) \land (\operatorname{CoherentObserver}\left(O\right) \Rightarrow (\operatorname{Accurate}\left(O, p, q, r, epsilon, false\right) \Rightarrow (6 \leq \operatorname{FintypeCard}\left(Z\right) \land 6 \leq \operatorname{NatCard}\left(\operatorname{Reached}\left(O, p, q, r\right)\right)))))))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.equality_observer_minima` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The separate equality construction gives seven initialized or six post-read-only total configurations, exactly and at the stipulated tolerance.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.accurate_profile`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.actual_coherent`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.actual_pure_law`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.charged_reached`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.common_state_distance`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.dominant_law`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.dominant_successor`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.equality_charged_injective`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.equality_charged_reached`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.equality_decoder_coherent`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.equality_initialized_injective`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.equality_initialized_step`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.equality_observer_accuracy`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.equality_observer_cardinalities`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.equality_observer_minima`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.equality_observers_exact`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.equality_project_step`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.equality_reached_all`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.equality_run_invariants`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.fold_replicate`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.half_pure_B_distance`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.half_pure_separation`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.initial_B_half`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.midpoint_decoder_coherent`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.midpoint_observer_accuracy`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.midpoint_observer_reachability`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.midpoint_reached_iff`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.midpoint_run`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.postread_initialization_extra_state`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.postread_only_unequal_minimum`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.pure_witness_actual`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.recurring_decoder_dominant_bound`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.run_snoc`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.sharp_initialized_common_decoder`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.sharp_postread_reached_common_decoder`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.sharp_source_run`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.sharp_source_step`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.sharp_state_card`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.startup_collision_forces_cutoff`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.startup_collision_recurrence`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.startup_shift`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.unequal_charged_injective`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.unequal_initialized_injective`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.universal_equality_lower_bounds`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount.universal_unequal_lower_bound`
- Dependency: [D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry](FiveModePredictiveLawGeometry.md)
