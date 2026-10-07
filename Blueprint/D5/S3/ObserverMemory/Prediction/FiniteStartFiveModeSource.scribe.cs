using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class FiniteStartFiveModeSourceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coherent finite word laws and exact acquired-history source updating.",
        H("Finite Start Five Mode Source"),
        Blocks(
            Paragraph(Text("States are Fin 5. Visible symbols are Fin 4, with code 2 denoted B. "
                + "The observation vector is [0,1,2,3,2]. The transition rows are "
                + "[1-p-q-r,p,0,q,r], [q,1-p-q,p,0,0], [0,q,1-p-q,p,0], "
                + "[p,0,q,1-p-q,0], [r,0,0,0,1-r]. Put a=1-p-q and b=1-r. "
                + "Admissibility means p>0, q>0, r>0 and p+q+r<1; it includes p=q and r=p+q.")),
            Paragraph(Text("The first acquired read filters the uniform vector pi directly. "
                + "Later reads advance through the literal matrix and then filter. "
                + "acquiredStateWeights retains unnormalized current-state weights, historyMass is their sum, "
                + "and acquiredPosterior divides them by that sum. initialWordWeight begins at Y0; "
                + "futureWordWeight advances before its first read. A word w is converted to its chronological "
                + "list by ofFn. Append denotes chronological concatenation, and snoc appends one final symbol.")),
            Entry("transition_row_stochastic", "Every literal row sums to one",
                Parameters(All("i", State, Equal(SumOver("j", State, Call("transition", P, Q, R, I, J)), D(1)))),
                "Row sums are one for every real parameter triple. Nonnegativity is a separate condition."),
            Entry("transition_nonnegative", "Admissible entries are nonnegative",
                Parameters(ImpliesF(Admissible, All("i", State, All("j", State,
                    Nonnegative(Call("transition", P, Q, R, I, J)))))),
                "The strict parameter inequalities make each of the displayed entries nonnegative."),
            Entry("uniform_stationary", "The uniform law is stationary",
                Parameters(All("j", State, Equal(SumOver("i", State,
                    Seq(Call("uniformPi", I), Star, Call("transition", P, Q, R, I, J))), Call("uniformPi", J)))),
                "Every column preserves weight one fifth, for arbitrary real parameters."),
            Entry("acquired_mass_eq_word", "State weights represent literal chronological words",
                Parameters(All("n", Nat, All("w", Word(N), Equal(Mass(Call("ofFn", W)), Initial(N, W))))),
                "The mass of the acquired state-weight recursion equals the independently defined literal initialized word weight."),
            Entry("future_word_nonnegative", "Finite future word weights are nonnegative",
                Parameters(ImpliesF(Admissible, All("v", Vector, ImpliesF(All("i", State,
                    Nonnegative(Call("v", I))), All("n", Nat, All("w", Word(N), Nonnegative(Future(V, N, W)))))))),
                "Advancement, observation filtering and finite summation preserve nonnegative weights."),
            Entry("sum_future_words", "The actual sum over all future words",
                Parameters(All("v", Vector, All("n", Nat,
                    Equal(SumOver("w", Word(N), Future(V, N, W)), SumOver("i", State, Call("v", I)))))),
                "The sum ranges over every function Fin n to Visible. Its proof connects this enumeration to the recursive total."),
            Entry("sum_initial_words", "The actual initialized word sum is one",
                Parameters(All("n", Nat,
                    Equal(SumOver("w", Word(N), Initial(N, W)), D(1)))),
                "The initialized law is normalized on the full finite word space at every horizon, including zero."),
            Entry("final_symbol_coherence", "Each future prefix has its final-symbol marginal",
                Parameters(All("v", Vector, All("n", Nat, All("w", Word(N),
                    Equal(SumOver("y", Visible, Future(V, Next(N), Call("snoc", W, Y))), Future(V, N, W)))))),
                "For each fixed chronological prefix w, summing over its last appended symbol gives exactly the weight of w."),
            Entry("initial_final_symbol_coherence", "Each initialized prefix has its final-symbol marginal",
                Parameters(All("n", Nat, All("w", Word(N),
                    Equal(SumOver("y", Visible, Initial(Next(N), Call("snoc", W, Y))), Initial(N, W))))),
                "The same pointwise marginal identity holds for the recording-boundary law."),
            Entry("empty_boundary_and_positive_timing", "Stationarity identifies the complete empty law",
                Parameters(All("H", Nat, All("w", Word(Horizon), Equal(Initial(Horizon, W), Future(Pi, Horizon, W))))),
                "The identity piP=pi equates initial and future weights word by word. The empty query still begins with Y0."),
            Entry("actual_positive_conditional_law", "Actual positive histories determine every future cylinder",
                Parameters(ImpliesF(Admissible, All("h", History, ImpliesF(AndF(NonemptyHistory, Positive(Mass(HistoryValue))),
                    All("H", Nat, All("w", Word(Horizon), AndF(
                        Equal(Div(Mass(Append(HistoryValue, Call("ofFn", W))), Mass(HistoryValue)),
                            Future(Posterior(HistoryValue), Horizon, W)),
                        AndF(Equal(SumOver("u", Word(Horizon), Future(Posterior(HistoryValue), Horizon, F.Id("u"))), D(1)),
                            Nonnegative(Future(Posterior(HistoryValue), Horizon, W)))))))))),
                "For every positive nonempty acquired history, the joint-cylinder quotient is its normalized posterior future law. "
                    + "That law is normalized and nonnegative at every finite horizon."),
            Entry("literal_conditional_future", "Conditioning in literal fixed-length word notation",
                Parameters(ImpliesF(Admissible, All("n", Nat, All("hword", Word(N),
                    ImpliesF(AndF(Positive(N), Positive(Initial(N, F.Id("hword")))),
                        All("H", Nat, All("w", Word(Horizon), Equal(
                            Div(Initial(Seq(N, Plus, Horizon), Call("append", F.Id("hword"), W)), Initial(N, F.Id("hword"))),
                            Future(Posterior(Call("ofFn", F.Id("hword"))), Horizon, W))))))))),
                "The same identity applies directly to the original initialized word law on concatenated Fin-indexed words."),
            Entry("positive_history_invariant", "The total source update tracks every positive acquired history",
                Parameters(All("h", History, ImpliesF(Positive(Mass(HistoryValue)),
                    Equal(Posterior(HistoryValue), Profile(Call("sourceRun", HistoryValue)))))),
                "sourceRun iterates sourceUpdate from Start on the actual symbols. Its normalized source profile equals the acquired posterior. "
                    + "Singletons reset to their pure states; B advances startup tags or the appropriate pure branch."),
            Entry("all_b_mass", "All-B cylinders have two literal hidden paths",
                Parameters(All("k", Nat, Equal(Initial(Next(K), Call("constant", Bsymbol)),
                    Div(Seq(Power(Call("a", P, Q), K), Plus, Power(Call("b", R), K)), D(5))))),
                "The initialized all-B word of length k+1 has mass (a^k+b^k)/5. This algebraic identity holds for every real parameter triple."),
            Entry("actual_all_B_posterior", "The acquired all-B posterior has the power coordinates",
                Parameters(ImpliesF(Admissible, All("k", Nat, Equal(
                    Posterior(Call("replicate", Next(K), Bsymbol)),
                    VectorLiteral(D(0), D(0), Div(Power(Call("a", P, Q), K), PowerSum), D(0),
                        Div(Power(Call("b", R), K), PowerSum)))))),
                "This is the posterior of the actual acquired cylinder, supported on states 2 and 4. Both coordinates are positive."),
            Entry("positive_history_classification", "Positive histories are exhaustively startup or pure",
                ClassificationFormula(),
                "A word with no singleton is an initial all-B run. The first singleton identifies its state, "
                    + "and every subsequent acquired symbol preserves purity. This covers all positive nonempty words."),
            Entry("actual_pure_B_transition", "Every pure B transition is an actual positive extension",
                PureBFormula(),
                "The B successor is 4 from states 0 and 4, and 2 from states 1,2,3. "
                    + "The corresponding positive masses are r,b,p,a,q respectively. The statement applies to every positive pure history."),
            Entry("positive_pure_padding", "All five pure witnesses have positive self-loop padding",
                PaddingFormula(),
                "The pure witnesses are [0], [1], [1,B], [3], [0,B] in state order. Their base masses are 1/5,1/5,p/5,1/5,r/5. "
                    + "Padding by n copies of the state's visible symbol multiplies the mass by the nth power of its diagonal transition, "
                    + "and the posterior remains pure. Every finite padding length has positive mass."),
            Entry("rare_B_extension_masses", "Rare transitions admit arbitrary positive B extensions",
                RareExtensionsFormula(),
                "Appending n B's after 1B gives mass p a^n/5 and posterior e2. Appending n B's after 0B gives mass r b^n/5 and posterior e4."),
            Entry("complete_source_tag_reachability", "Every source tag has an actual positive history",
                ReachabilityFormula(),
                "Start is realized by the empty history, each startup k by B^(k+1), and each pure state by its literal witness. "
                    + "The realization has its stated normalized acquired source profile."),
            Entry("actual_law_probability_and_coherence", "One coherent conditional family on every actual history",
                CoherentFormula(),
                "For a positive history, actualFutureWordWeight uses the initialized law at empty history and the posterior future law otherwise. "
                    + "Every horizon is normalized and nonnegative, with pointwise consistency under deletion of its final read."))));

    private static DocumentBlock.Describe Entry(string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Esc, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, F.Id(name), Colon, Sp, type, Comma, Esc, body);
    private static Formula Parameters(Formula body) => All("p", Real, All("q", Real, All("r", Real, body)));
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula ImpliesF(Formula left, Formula right) => Seq(Open, left, Close, Sp, Rightarrow, Sp, right);
    private static Formula AndF(Formula left, Formula right) => Seq(Open, left, Sp, Land, Sp, right, Close);
    private static Formula OrF(Formula left, Formula right) => Seq(Open, left, Sp, Lor, Sp, right, Close);
    private static Formula Positive(Formula value) => Seq(D(0), Sp, Lt, Sp, value);
    private static Formula Nonnegative(Formula value) => Seq(D(0), Sp, Leq, Sp, value);
    private static Formula Div(Formula top, Formula bottom) => new Formula.Fraction(top, bottom);
    private static Formula Power(Formula value, Formula exponent) => Seq(Open, value, Close, Caret, Grp(exponent));
    private static Formula Next(Formula value) => Seq(Open, value, Plus, D(1), Close);
    private static Formula SumOver(string name, Formula domain, Formula body) =>
        Seq(F.Sum, Underscore, Grp(F.Id(name), InMacro, Sp, domain), Sp, Open, body, Close);
    private static Formula Append(Formula left, Formula right) => Call("append", left, right);
    private static Formula Initial(Formula length, Formula word) => Call("initialWordWeight", P, Q, R, Pi, length, word);
    private static Formula Future(Formula vector, Formula length, Formula word) => Call("futureWordWeight", P, Q, R, vector, length, word);
    private static Formula Mass(Formula history) => Call("historyMass", P, Q, R, history);
    private static Formula Posterior(Formula history) => Call("acquiredPosterior", P, Q, R, history);
    private static Formula Profile(Formula tag) => Call("sourceProfile", P, Q, R, tag);
    private static Formula Actual(Formula history, Formula length, Formula word) => Call("actualFutureWordWeight", P, Q, R, history, length, word);
    private static Formula Word(Formula length) => Seq(Call("Fin", length), To, Sp, Visible);
    private static Formula VectorLiteral(Formula v, Formula w, Formula x, Formula y, Formula z) =>
        Seq(OpenBracket, v, Comma, w, Comma, x, Comma, y, Comma, z, CloseBracket);
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula State => F.Id("State");
    private static Formula Visible => F.Id("Visible");
    private static Formula Vector => Seq(State, To, Sp, Real);
    private static Formula History => Call("List", Visible);
    private static Formula P => F.Id("p");
    private static Formula Q => F.Id("q");
    private static Formula R => F.Id("r");
    private static Formula I => F.Id("i");
    private static Formula J => F.Id("j");
    private static Formula N => F.Id("n");
    private static Formula K => F.Id("k");
    private static Formula W => F.Id("w");
    private static Formula Y => F.Id("y");
    private static Formula V => F.Id("v");
    private static Formula Horizon => F.Id("H");
    private static Formula HistoryValue => F.Id("h");
    private static Formula Pi => F.Id("uniformPi");
    private static Formula Bsymbol => F.Id("B");
    private static Formula Admissible => Call("admissible", P, Q, R);
    private static Formula NonemptyHistory => Seq(HistoryValue, Sp, Neq, Sp, OpenBracket, CloseBracket);
    private static Formula PowerSum => Seq(Power(Call("a", P, Q), K), Plus, Power(Call("b", R), K));

    private static Formula ClassificationFormula() => Parameters(
        All("h", History, ImpliesF(AndF(NonemptyHistory, Positive(Mass(HistoryValue))),
            OrF(Some("k", Nat, AndF(Equal(HistoryValue, Call("replicate", Next(K), Bsymbol)),
                AndF(Equal(Call("sourceRun", HistoryValue), Call("startup", K)),
                    Equal(Call("acquiredStateWeights", P, Q, R, HistoryValue), Call("startupVector", P, Q, R, K))))),
                Some("i", State, AndF(Equal(Call("sourceRun", HistoryValue), Call("pure", I)),
                    Equal(Posterior(HistoryValue), Call("pureVector", I))))))));

    private static Formula PureBFormula() => Parameters(ImpliesF(Admissible, All("h", History,
        ImpliesF(AndF(NonemptyHistory, Positive(Mass(HistoryValue))), All("j", State,
            ImpliesF(Equal(Posterior(HistoryValue), Call("pureVector", J)),
                AndF(Equal(Mass(Append(HistoryValue, Seq(OpenBracket, Bsymbol, CloseBracket))),
                    Seq(Mass(HistoryValue), Star, Call("pureBMass", P, Q, R, J))),
                    AndF(Positive(Mass(Append(HistoryValue, Seq(OpenBracket, Bsymbol, CloseBracket)))),
                        Equal(Posterior(Append(HistoryValue, Seq(OpenBracket, Bsymbol, CloseBracket))), Call("pureVector", Call("pureBSuccessor", J)))))))))));

    private static Formula PaddingHistory => Append(Call("pureWitness", J), Call("replicate", N, Call("observation", J)));
    private static Formula PaddingFormula() => Parameters(ImpliesF(Admissible, All("j", State, All("n", Nat,
        AndF(Equal(Mass(PaddingHistory), Seq(Call("pureWitnessMass", P, R, J), Star, Power(Call("transition", P, Q, R, J, J), N))),
            AndF(Positive(Mass(PaddingHistory)), Equal(Posterior(PaddingHistory), Call("pureVector", J))))))));

    private static Formula RareHistory(Formula first) => Append(Seq(OpenBracket, first, Comma, Bsymbol, CloseBracket), Call("replicate", N, Bsymbol));
    private static Formula RareExtensionsFormula() => Parameters(ImpliesF(Admissible, All("n", Nat,
        AndF(Equal(Mass(RareHistory(D(1))), Div(Seq(P, Star, Power(Call("a", P, Q), N)), D(5))),
            AndF(Positive(Mass(RareHistory(D(1)))), AndF(Equal(Posterior(RareHistory(D(1))), Call("pureVector", D(2))),
                AndF(Equal(Mass(RareHistory(D(0))), Div(Seq(R, Star, Power(Call("b", R), N)), D(5))),
                    AndF(Positive(Mass(RareHistory(D(0)))), Equal(Posterior(RareHistory(D(0))), Call("pureVector", D(4)))))))))));

    private static Formula ReachabilityFormula() => Parameters(ImpliesF(Admissible,
        All("z", F.Id("SourceTag"), Some("h", History, AndF(Equal(Call("sourceRun", HistoryValue), F.Id("z")),
            AndF(Positive(Mass(HistoryValue)), AndF(Equal(Posterior(HistoryValue), Profile(F.Id("z"))),
                Seq(Open, Equal(HistoryValue, Seq(OpenBracket, CloseBracket)), Sp, Iff, Sp,
                    Equal(F.Id("z"), F.Id("Start")), Close))))))));

    private static Formula CoherentFormula() => Parameters(ImpliesF(Admissible,
        All("h", History, ImpliesF(Positive(Mass(HistoryValue)), All("H", Nat, All("w", Word(Horizon),
            AndF(Nonnegative(Actual(HistoryValue, Horizon, W)),
                AndF(Equal(SumOver("u", Word(Horizon), Actual(HistoryValue, Horizon, F.Id("u"))), D(1)),
                    Equal(SumOver("y", Visible, Actual(HistoryValue, Next(Horizon), Call("snoc", W, Y))), Actual(HistoryValue, Horizon, W))))))))));
}
