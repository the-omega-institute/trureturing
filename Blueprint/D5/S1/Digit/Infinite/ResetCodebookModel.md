# Reset codebook: Model

## Abstract

Reset codebooks, actual sources and weighted lower-memory graphs.

**Definition 1.1 (U).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.U`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.U` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by U: List Label := [fiveLabel, nullLabel, threeLabel, nullLabel, threeLabel, threeLabel].

**Definition 1.2 (V).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.V`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.V` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by V: List Label := [nullLabel, threeLabel, threeLabel, fiveLabel, nullLabel, threeLabel].

**Definition 1.3 (C).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.C`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by C: List Label := [fiveLabel, fiveLabel, threeLabel, twoLabel, twoLabel, nullLabel, threeLabel, threeLabel, threeLabel, twoFiveLabel, fiveLabel, nullLabel, nullLabel, twoLabel, twoLabel, twoFiveLabel, threeLabel, threeLabel, nullLabel, fiveLabel].

**Definition 1.4 (sixColor).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.sixColor`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.sixColor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by sixColor: List (Fin 6) := [2,1,0,2,1,0].

**Definition 1.5 (twentyColor).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.twentyColor`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.twentyColor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by twentyColor: List (Fin 6) := [2,3,0,3,4,2,0,1,0,5,2,1,1,3,3,5,0,0,1,2].

**Definition 1.6 (sideWord).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.sideWord`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.sideWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by sideWord(low : Bool) : List Label := if low then V else U.

**Definition 1.7 (c0).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.c0`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.c0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by c0: ℝ := 2*t/5.

**Definition 1.8 (rho).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.rho`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.rho` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by rho: ℝ := g^6.

**Definition 1.9 (chi).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.chi`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.chi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by chi: ℝ := g^20.

**Definition 1.10 (h).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.h`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.h` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by h(low : Bool) : ℝ := if low then (46+31*g)/380 else (39-6*g)/380.

**Definition 1.11 (A).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.A`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by A(low : Bool) : ℝ := (1-rho)*h low.

**Definition 1.12 (E).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.E`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.E` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by E(low : Bool) : ℝ := if low then c0 else t^2-c0.

**Definition 1.13 (X).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.X`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.X` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by X(low : Bool) : ℝ := A low + rho*chi^3*E low.

**Definition 1.14 (Y).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.Y`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.Y` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by Y(low : Bool) : ℝ := A low + rho*chi*X low.

**Definition 1.15 (coord).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.coord`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.coord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by coord(low : Bool) (D : ℝ) : ℝ := if low then c0-D else c0+D.

**Theorem 1.16 (center).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.center`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookModel.center` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: c0=(1+g)/5

**Definition 1.17 (zeroAddress).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.zeroAddress`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.zeroAddress` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by zeroAddress: LegalDigits := ⟨fun _ => false, by simp⟩.

**Definition 1.18 (Return).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.Return`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.Return` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by Return := {mr : ℕ × ℕ // 1 ≤ mr.1 ∧ 1 ≤ mr.2}.

**Definition 1.19 (returnWord).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.returnWord`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.returnWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by returnWord(low : Bool) (a : Return) := wordPower a.val.1 (sideWord low) ++ wordPower a.val.2 C.

**Definition 1.20 (returnColors).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.returnColors`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.returnColors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by returnColors(a : Return) := wordPower a.val.1 sixColor ++ wordPower a.val.2 twentyColor.

**Definition 1.21 (tailWord).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.tailWord`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.tailWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by tailWord(low : Bool) := sideWord low ++ wordPower 3 C ++ (if low then [] else [fiveLabel]).

**Definition 1.22 (literalTail).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.literalTail`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.literalTail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by literalTail(low : Bool) : LegalDigits := Classical.choose (source_path_realization (tail_path low) zeroAddress (zero_state true)).

**Theorem 1.23 (literal tail spec).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.literal_tail_spec`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookModel.literal_tail_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (low : Bool) : stateAddress true (literalTail low) ∧ finiteTail (literalTail low) ∧ addressPrefix (tailWord low) (literalTail low) zeroAddress ∧ kappa (literalTail low)=wordScalar (tailWord low) 0

**Definition 1.24 (listWord).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.listWord`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.listWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by listWord(low : Bool) (as : List Return) := as.flatMap (returnWord low).

**Definition 1.25 (listColors).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.listColors`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.listColors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by listColors(as : List Return) := as.flatMap returnColors.

**Definition 1.26 (sourcePrefix).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.sourcePrefix`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.sourcePrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by sourcePrefix(low anchor : Bool) (exec : List Return) := (sideWord low ++ C) ++ listWord low exec.reverse ++ (if anchor then sideWord low ++ C else []).

**Definition 1.27 (colors).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.colors`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.colors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by colors(anchor : Bool) (exec : List Return) := (sixColor ++ twentyColor) ++ listColors exec.reverse ++ (if anchor then sixColor ++ twentyColor else []).

**Theorem 1.28 (actual pair).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.actual_pair`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookModel.actual_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (anchor : Bool) (exec : List Return) : ∃ src : Bool → LegalDigits, ∀ low, stateAddress false (src low) ∧ finiteTail (src low) ∧ addressPrefix (sourcePrefix low anchor exec) (src low) (literalTail low) ∧ kappa (src low)=wordScalar (sourcePrefix low anchor exec) (kappa (literalTail low))

**Definition 1.29 (weak).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.weak`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.weak` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by weak(K : ℕ) (d : ℝ) : List D5.S1.Digit.Infinite.ResetCodebook.Return → ℝ → Prop := | [], _ => True | a::as, D => a.val.2 ≤ K ∧ (a.val.2=K → d ≤ D) ∧ weak K d as (G false a D).

**Definition 1.30 (weight).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.weight`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by weight(as : List D5.S1.Digit.Infinite.ResetCodebook.Return) := (as.map (fun a => 6*a.val.1+20*a.val.2)).sum.

**Definition 1.31 (codebook).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.codebook`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.codebook` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by codebook(anchor : Bool) (K N : ℕ) (d : ℝ) : Set (List D5.S1.Digit.Infinite.ResetCodebook.Return) := {as | weight as=N ∧ weak K d as (if anchor then Y false else X false)}.

**Definition 1.32 (letters).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.letters`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.letters` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by letters(as : List D5.S1.Digit.Infinite.ResetCodebook.Return) : List Bool := as.flatMap (fun a => List.replicate a.val.2 true ++ List.replicate a.val.1 false).

**Definition 1.33 (letterWeight).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.letterWeight`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.letterWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by letterWeight(w : List Bool) := (w.map (fun c => if c then 20 else 6)).sum.

**Definition 1.34 (f).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.f`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.f` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by f(a : Bool) (D : ℝ) := if a then chi*D else A false+rho*D.

**Definition 1.35 (past).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.past`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.past` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by past(w : ℤ → Bool) (i : ℤ) (n : ℕ) (z : ℝ) := ((List.range n).map (fun j => w (i-(n:ℤ)+(j:ℤ)))).foldl (fun D a => f a D) z.

**Definition 1.36 (state).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.state`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.state` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by state(w : ℤ → Bool) (i : ℤ) := sSup (Set.range (fun n => past w i n 0)).

**Definition 1.37 (high).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.high`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.high` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by high(K : ℕ) (w : ℤ → Bool) (i : ℤ) := ∀ j<K, w (i-(j:ℤ))=true.

**Definition 1.38 (cap).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.cap`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.cap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by cap(K : ℕ) (w : ℤ → Bool) := ∀ i, ¬high (K+1) w i.

**Definition 1.39 (lowerLanguage).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.lowerLanguage`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.lowerLanguage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by lowerLanguage(K n : ℕ) (d : ℝ) : Set (ℤ → Bool) := {w | cap K w ∧ ∀ i, high K w i → chi^(K-1)*d < past w i n 0}.

**Definition 1.40 (factor).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.factor`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.factor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by factor(w : List Bool) (omega : ℤ → Bool) := ∃ i : ℤ, ∀ j : Fin w.length, omega (i+(j.val:ℤ))=w[j.val].

**Definition 1.41 (factorCount).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.factorCount`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.factorCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by factorCount(lang : Set (ℤ → Bool)) (N : ℕ) := Nat.card {w : List Bool // letterWeight w=N ∧ ∃ omega∈lang, factor w omega}.

**Definition 1.42 (rate).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.rate`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.rate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by rate(lang : Set (ℤ → Bool)) := Filter.limsup (fun N : ℕ => Real.log (max 1 (factorCount lang N):ℝ)/Real.log 2/(N:ℝ)) Filter.atTop.

**Definition 1.43 (reset).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.reset`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.reset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by reset(M : ℕ) (hM : 1 ≤ M) : D5.S1.Digit.Infinite.ResetCodebook.Return := ⟨(M,1),hM,Nat.le_refl 1⟩.

**Definition 1.44 (B).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.B`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by B(M : ℕ) := h false-rho^M*(h false-chi*A false).

**Definition 1.45 (autoCost).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.autoCost`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.autoCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by autoCost(K : ℕ) := max (lambda-g^2*chi*X false) (max (lambda-g^2*chi^(K-1)*A false) (lambda-rho)).

**Definition 1.46 (actualEps).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.actualEps`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.actualEps` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by actualEps(anchor : Bool) (K M N : ℕ) (b : ℝ) := min (b-autoCost K) (g^2*chi^K*(B M-(if anchor then Y false else X false))*g^N)/2.

**Definition 1.47 (concatenation).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.concatenation`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.concatenation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by concatenation(anchor : Bool) (K M N : ℕ) (d : ℝ) (hM : 1 ≤ M) (omega : ℤ → Bool) : Prop := ∃ cuts : ℤ → ℤ, StrictMono cuts ∧ Filter.Tendsto cuts Filter.atTop Filter.atTop ∧ Filter.Tendsto cuts Filter.atBot Filter.atBot ∧ ∃ v : ℤ → List D5.S1.Digit.Infinite.ResetCodebook.Return, ∀ i, v i ∈ codebook anchor K N d ∧ cuts (i+1)-cuts i=(letters (reset M hM::v i)).length ∧ ∀ j : Fin (letters (reset M hM::v i)).length, omega (cuts i+(j.val:ℤ))=(letters (reset M hM::v i))[j.val].

**Definition 1.48 (finiteActual).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.finiteActual`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.finiteActual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by finiteActual(anchor : Bool) (K M N : ℕ) (b d : ℝ) (hM : 1 ≤ M) : Prop := ∀ vs : List (List D5.S1.Digit.Infinite.ResetCodebook.Return), (∀ v∈vs, v∈codebook anchor K N d) → let exec := (vs.map (fun v => reset M hM::v)).flatten weak K (d+(B M-(if anchor then Y false else X false))*g^N) exec (if anchor then Y false else X false) ∧ ∃ src : Bool → LegalDigits, ∀ low, stateAddress false (src low) ∧ finiteTail (src low) ∧ addressPrefix (sourcePrefix low anchor exec) (src low) (literalTail low) ∧ wordCost (sourcePrefix low anchor exec) (colors anchor exec) (kappa (literalTail low)) ≤ b-2*actualEps anchor K M N b ∧ ∀ Q : ℝ → Fin 6, (∀ j z, z∈Set.Ioo (cellLower j) (cellUpper j) → Q z=j) → ∃ errors : ℕ → ℝ, ∀ p : Fin (colors anchor exec).length, |errors p.val| < b-actualEps anchor K M N b ∧ Q (min (1+t) (max (-1) (kappa ((originalT)^[p.val] (src low))+errors p.val))) =(colors anchor exec)[p.val].

**Definition 1.49 (target6218Language).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.target6218Language`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.target6218Language` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by target6218Language(anchor : Bool) (K M N : ℕ) (b d : ℝ) (hK : 2 ≤ K) (hM : 1 ≤ M) (hN : 0 < N) (hbudget : lambda-g^2*chi^K*h false < b ∧ b < lambda-g^2*chi^K*(A false/(1-rho*chi^K))) (hd : d=(lambda-b)/(g^2*chi^K)) (hreset : max (max (X false) (Y false)) d < B M) (hne : (codebook anchor K N d).Nonempty) : Prop := let delta := B M-(if anchor then Y false else X false) let eps := chi^(K-1)*delta*g^N (codebook anchor K N d).Finite ∧ 0<actualEps anchor K M N b ∧ finiteActual anchor K M N b d hM ∧ (∀ omega, concatenation anchor K M N d hM omega → cap K omega ∧ (∀ i, Filter.Tendsto (fun n => past omega i n 0) Filter.atTop (nhds (state omega i))) ∧ ∀ i, high K omega i → chi^(K-1)*d+eps ≤ state omega i) ∧ ∃ n : ℕ, K≤n ∧ h false*rho^n<eps ∧ (∀ omega, concatenation anchor K M N d hM omega → omega∈lowerLanguage K n d) ∧ Real.log (Nat.card {v // v∈codebook anchor K N d}:ℝ)/Real.log 2/(N+20+6*M:ℝ) ≤ rate (lowerLanguage K n d).

**Theorem 1.50 (positive pow).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.positive_pow`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookModel.positive_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) : ∀ i j, 0 ≤ (A^k) i j

**Definition 1.51 (wordSet).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.wordSet`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.wordSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by wordSet: ℕ → Finset (List Bool) := | 0 => {[]} | k+1 => (wordSet k).image (List.cons false) ∪ (wordSet k).image (List.cons true).

**Theorem 1.52 (mem wordSet).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.mem_wordSet`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookModel.mem_wordSet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (w : List Bool) (k : ℕ) : w∈wordSet k ↔ w.length=k

**Definition 1.53 (mass).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.mass`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.mass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by mass(z : ℝ) : ι → List Bool → ℝ := | _, [] => 1 | v, c::w => if allow v c then z^(if c then 20 else 6) * mass z (next v c) w else 0.

**Definition 1.54 (accepts).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.accepts`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.accepts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by accepts: ι → List Bool → Prop := | _, [] => True | v,c::w => allow v c ∧ accepts (next v c) w.

**Theorem 1.55 (mass of accepts).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.mass_of_accepts`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookModel.mass_of_accepts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (z : ℝ) (v : ι) (w : List Bool) (hw : accepts next allow v w) : mass next allow z v w=z^Statement.letterWeight w

**Theorem 1.56 (mass nonneg).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.mass_nonneg`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookModel.mass_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (z : ℝ) (hz : 0 ≤ z) (v : ι) (w : List Bool) : 0 ≤ mass next allow z v w

**Definition 1.57 (transfer).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.transfer`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.transfer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by transfer(z : ℝ) : Matrix ι ι ℝ := fun v u => (if allow v false ∧ next v false=u then z^6 else 0) + (if allow v true ∧ next v true=u then z^20 else 0).

**Theorem 1.58 (transfer nonneg).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.transfer_nonneg`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookModel.transfer_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (z : ℝ) (hz : 0 ≤ z) (v u : ι) : 0 ≤ transfer next allow z v u

**Theorem 1.59 (transfer pow nonneg).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.transfer_pow_nonneg`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookModel.transfer_pow_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (z : ℝ) (hz : 0 ≤ z) (k : ℕ) (v u : ι) : 0 ≤ (transfer next allow z ^ k) v u

**Theorem 1.60 (word mass eq row).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.word_mass_eq_row`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookModel.word_mass_eq_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (z : ℝ) (v : ι) (k : ℕ) : ∑ w ∈ wordSet k, mass next allow z v w = ∑ u, (transfer next allow z ^ k) v u

**Definition 1.61 (history).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.history`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.history` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by history(n : ℕ) (w : ℤ → Bool) (i : ℤ) : Fin n → Bool := fun j => w (i-(n:ℤ)+(j.val:ℤ)).

**Definition 1.62 (vertexAt).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.vertexAt`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.vertexAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by vertexAt(lang : Set (ℤ → Bool)) (n : ℕ) (w : ℤ → Bool) (hw : w∈lang) (i : ℤ) : Vertex lang n := ⟨history n w i,w,hw,i,rfl⟩.

**Definition 1.63 (graphAllowed).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.graphAllowed`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.graphAllowed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by graphAllowed(lang : Set (ℤ → Bool)) (n : ℕ) (v : Vertex lang n) (c : Bool) : Prop := ∃ w∈lang, ∃ i : ℤ, history n w i=v.val ∧ w i=c.

**Definition 1.64 (graphNext).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.graphNext`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.graphNext` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by graphNext(lang : Set (ℤ → Bool)) (n : ℕ) (v : Vertex lang n) (c : Bool) : Vertex lang n := if h : ∃ w∈lang, ∃ i : ℤ, history n w i=shiftHistory n v.val c then ⟨shiftHistory n v.val c,h⟩ else v.

**Theorem 1.65 (factor accepts).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.factor_accepts`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookModel.factor_accepts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (lang : Set (ℤ → Bool)) (n : ℕ) (w : List Bool) (u : ℤ → Bool) (hu : u∈lang) (i : ℤ) (hw : ∀ j : Fin w.length, u (i+(j.val:ℤ))=w[j.val]) : accepts (graphNext lang n) (graphAllowed lang n) (vertexAt lang n u hu i) w

**Definition 1.66 (lowerMatrix).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.lowerMatrix`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.lowerMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by lowerMatrix(K n : ℕ) (d z : ℝ) : Matrix (Vertex (Statement.lowerLanguage K n d) n) (Vertex (Statement.lowerLanguage K n d) n) ℝ := transfer (graphNext (Statement.lowerLanguage K n d) n) (graphAllowed (Statement.lowerLanguage K n d) n) z.

**Definition 1.67 (lowerComplexMatrix).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.lowerComplexMatrix`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.lowerComplexMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by lowerComplexMatrix(K n : ℕ) (d z : ℝ) : Matrix (Vertex (Statement.lowerLanguage K n d) n) (Vertex (Statement.lowerLanguage K n d) n) ℂ := (Complex.ofRealHom.mapMatrix) (lowerMatrix K n d z).

**Definition 1.68 (SpectralRoot).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.SpectralRoot`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.SpectralRoot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by SpectralRoot(K n : ℕ) (d z : ℝ) : Prop := 0<z ∧ z<1 ∧ spectralRadius ℂ (lowerComplexMatrix K n d z)=1.

**Definition 1.69 (gamma).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.gamma`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.gamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by gamma(z : ℝ) : ℝ := -Real.log z/Real.log 2.

**Definition 1.70 (RawGraphLabels).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.RawGraphLabels`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.RawGraphLabels` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by RawGraphLabels(K n : ℕ) (d : ℝ) (w : ℤ → Bool) : Prop := ∃ v : ℤ → Fin n → Bool, ∀ i, localAllowed K n d (v i) (w i) ∧ v (i+1)=shiftHistory n (v i) (w i).

**Theorem 1.71 (raw labels iff lower language).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.raw_labels_iff_lower_language`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookModel.raw_labels_iff_lower_language` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (K n : ℕ) (d : ℝ) (hn : 0<n) (hKn : K≤n) (w : ℤ → Bool) : RawGraphLabels K n d w ↔ w∈Statement.lowerLanguage K n d

**Definition 1.72 (originalLowerComplexMatrix).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.originalLowerComplexMatrix`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.originalLowerComplexMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by originalLowerComplexMatrix(K n : ℕ) (d z : ℝ) := Complex.ofRealHom.mapMatrix (originalLowerMatrix K n d z).

**Theorem 1.73 (originalLowerComplexMatrix eq).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.originalLowerComplexMatrix_eq`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookModel.originalLowerComplexMatrix_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (K n : ℕ) (d z : ℝ) (hn : 0<n) (hKn : K≤n) : originalLowerComplexMatrix K n d z=lowerComplexMatrix K n d z

**Definition 1.74 (OriginalSpectralRoot).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.OriginalSpectralRoot`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookModel.OriginalSpectralRoot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by OriginalSpectralRoot(K n : ℕ) (d z : ℝ) : Prop := 0<z ∧ z<1 ∧ spectralRadius ℂ (originalLowerComplexMatrix K n d z)=1.

**Theorem 1.75 (allow false).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.allow_false`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookModel.allow_false` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (K n : ℕ) (d : ℝ) (hK : 2 ≤ K) (hKn : K ≤ n) (v : Vertex (Statement.lowerLanguage K n d) n) : graphAllowed (Statement.lowerLanguage K n d) n v false

**Theorem 1.76 (allow after false).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.allow_after_false`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookModel.allow_after_false` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (K n : ℕ) (d : ℝ) (hK : 2 ≤ K) (hKn : K ≤ n) (v : Vertex (Statement.lowerLanguage K n d) n) (c : Bool) : graphAllowed (Statement.lowerLanguage K n d) n (graphNext (Statement.lowerLanguage K n d) n v false) c

**Theorem 1.77 (vertex nonempty).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookModel.vertex_nonempty`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookModel.vertex_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (K n : ℕ) (d : ℝ) (hK : 2 ≤ K) : Nonempty (Vertex (Statement.lowerLanguage K n d) n)

## References

- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.A`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.B`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.C`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.E`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.OriginalSpectralRoot`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.RawGraphLabels`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.Return`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.SpectralRoot`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.U`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.V`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.X`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.Y`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.accepts`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.actualEps`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.actual_pair`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.allow_after_false`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.allow_false`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.autoCost`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.c0`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.cap`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.center`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.chi`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.codebook`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.colors`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.concatenation`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.coord`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.f`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.factor`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.factorCount`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.factor_accepts`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.finiteActual`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.gamma`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.graphAllowed`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.graphNext`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.h`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.high`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.history`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.letterWeight`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.letters`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.listColors`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.listWord`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.literalTail`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.literal_tail_spec`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.lowerComplexMatrix`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.lowerLanguage`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.lowerMatrix`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.mass`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.mass_nonneg`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.mass_of_accepts`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.mem_wordSet`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.originalLowerComplexMatrix`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.originalLowerComplexMatrix_eq`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.past`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.positive_pow`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.rate`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.raw_labels_iff_lower_language`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.reset`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.returnColors`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.returnWord`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.rho`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.sideWord`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.sixColor`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.sourcePrefix`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.state`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.tailWord`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.target6218Language`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.transfer`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.transfer_nonneg`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.transfer_pow_nonneg`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.twentyColor`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.vertexAt`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.vertex_nonempty`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.weak`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.weight`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.wordSet`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.word_mass_eq_row`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookModel.zeroAddress`
- Dependency: [D5/S1/Digit/Infinite/FixedTailClosedBudget](FixedTailClosedBudget.md)
- Dependency: [D5/S1/Digit/Infinite/SixWindowForcing](SixWindowForcing.md)
