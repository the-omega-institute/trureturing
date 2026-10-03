using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class VisibleAdaptiveRecordLawDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Measurement/VisibleAdaptiveRecordLaw.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite visible adaptive instruments have hidden-state independent physical records and sharp absolute minimax risk.",
        H("Visible Adaptive Physical Record Law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("visible-adaptive-event-stage"),
                DeclarationHandle.Create(Prefix + "ActualEventStage"),
                H("Legal dependent instrument events"),
                StatementSource.FromAuthor(EventFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A preceding history has its own outcome carrier and measurable structure. "
                        + "Every measurable event in the declared next-history space pulls back to a legal "
                        + "instrument event. The measurable preceding projection recovers the previous "
                        + "history on each fibre embedding. Completely positive event operations vanish "
                        + "on the empty event, are countably additive in their matrix coordinates, and "
                        + "have measurable coordinates for every fixed retained event. Neither outcome "
                        + "cardinality nor a StandardBorel structure is imposed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-visible-stopped-policy"),
                DeclarationHandle.Create(Prefix + "FiniteStoppedPolicy"),
                H("Finite adaptive waiting and stopping"),
                StatementSource.FromAuthor(PolicyFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite family contains exactly the history spaces from depth zero through N. "
                        + "Before N, the visible policy supplies a legal instrument, a measurable real "
                        + "waiting-time control, a measurable stop set, and a measurable cemetery "
                        + "continuation compatible with the preceding projection. Stopping persists "
                        + "where a subsequent stop set exists. The measurable returned record includes "
                        + "a natural-number length: an active outcome increments it and a stopped "
                        + "continuation preserves the entire record."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-visible-finite-step"),
                DeclarationHandle.Create(Prefix + "actualFiniteStep"),
                H("Actual local tensor wait and instrument amplification"),
                StatementSource.FromAuthor(StepFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An active transition first conjugates the joint state by the actual matrix "
                        + "exponential of minus i times the controlled waiting time times H_A tensor I_B. "
                        + "It then applies the actual tensor amplification of the visible CP event "
                        + "operation with the identity map on B. The visible map is transported "
                        + "through the CStarMatrix linear equivalence and tensored by the matrix-map "
                        + "Kronecker operation. For each supplied finite Kraus representation of the "
                        + "visible map, this amplification agrees on every joint matrix with the sum "
                        + "of conjugations by its Kraus operators tensored with I_B. This identity "
                        + "does not restrict the measurable classical outcome carrier or require a "
                        + "measurable choice of Kraus operators. A stopped transition is the identity "
                        + "quantum action on its deterministic cemetery event, with no added wait."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("visible-adaptive-record-law-and-absolute-minimax"),
                DeclarationHandle.Create(Prefix + "visible_adaptive_record_law_and_absolute_minimax"),
                H("Physical law independence and sharp randomized absolute risk"),
                StatementSource.FromAuthor(TheoremFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a finite-dimensional visible state rho_A, a Hermitian local Hamiltonian "
                            + "H_A, a hidden dimension e at least two, and a positive inverse temperature "
                            + "beta. The same finite measurable visible policy is used for every hidden "
                            + "density sigma_B. Its independently specified physical histories have "
                            + "measurable integrable positive trace-one densities, initial Dirac history "
                            + "law and product preparation rho_A tensor sigma_B. Their next quantum "
                            + "event integrals satisfy the actual finite-step transition equations. "
                            + "Total trace preservation is required almost everywhere on executed "
                            + "active histories, separately for each hidden state.")),
                    Paragraph(Text(
                        "The conclusion constructs a common probability measure equal to every "
                            + "terminal physical history law. Pushing it through the same returned "
                            + "record map gives the same record law for every hidden density. For every "
                            + "retained measurable record event, the next mass whose preceding history "
                            + "was stopped equals its previous stopped-record mass. No stopping or "
                            + "failure mass is discarded or renormalized.")),
                    Paragraph(Text(
                        "For the hidden target (log(e) minus von Neumann entropy of sigma_B) divided "
                            + "by beta, the infimum over all real-valued Markov estimator kernels of "
                            + "the supremum over all hidden density states of expected absolute error "
                            + "is exactly log(e) divided by twice beta. Expectation is an extended "
                            + "nonnegative integral, so infinite risks and arbitrary real outputs "
                            + "remain in scope. Pure and maximally mixed hidden states provide the "
                            + "indistinguishable endpoints, and a constant midpoint estimator attains "
                            + "the bound. The logarithm is natural.")),
                    Paragraph(Text(
                        "The proof constructs the visible history from the actual instruments. "
                            + "Its finite induction identifies joint quantum event integrals with "
                            + "visible event integrals tensored with the fixed hidden density. Taking "
                            + "eventwise traces identifies the independently specified physical "
                            + "classical measure before common-density uniqueness gives the tensor "
                            + "posterior almost everywhere. Measurable cemetery completion outside "
                            + "the normalization domain changes no physical event integral. Record "
                            + "independence is a conclusion, not an interface field.")),
                    Paragraph(Text(
                        "This is a per-protocol theorem with explicit operational history "
                            + "hypotheses. It does not posit a hidden-state oracle, measurable Kraus "
                            + "selection, full-rank hidden states, a common null set for all hidden "
                            + "states, or a finite classical outcome space. The zero-Hamiltonian Gibbs "
                            + "identity identifies the hidden reference with I/e. Optimizing also over "
                            + "a nonempty legal experiment class is an application of the universal "
                            + "per-protocol value; it is not a separate declaration in this module. "
                            + "The result makes no algorithmic runtime or hidden partition-function "
                            + "counting claim."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] args) => F.Seq(
        F.Operatorname, F.Grp(V(name)), F.Open,
        F.Seq(args.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { F.Comma, F.Sp, x }).ToArray()), F.Close);
    private static Formula S(params Formula[] xs) => F.Seq(xs);
    private static Formula Eq(Formula x, Formula y) => S(x, F.Sp, F.Eq, F.Sp, y);
    private static Formula And(params Formula[] xs) => F.Seq(
        xs.SelectMany((x, i) => i == 0 ? new[] { F.Open, x, F.Close }
            : new[] { F.Sp, F.Land, F.Sp, F.Open, x, F.Close }).ToArray());
    private static Formula All(string name, Formula type, Formula body) => S(
        F.Forall, F.Sp, F.Open, V(name), F.Colon, F.Sp, type, F.Close, F.Comma, F.Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) => S(
        F.Exists, F.Sp, F.Open, V(name), F.Colon, F.Sp, type, F.Close, F.Comma, F.Sp, body);
    private static Formula Imp(Formula x, Formula y) => S(F.Open, x, F.Close, F.Sp, F.Implies, F.Sp, F.Open, y, F.Close);
    private static Formula Mem(Formula x, Formula y) => S(x, F.Sp, F.InMacro, F.Sp, y);
    private static Formula Inv(Formula f, Formula e) => S(f, F.Caret, F.Grp(F.Minus, F.Sp, F.D(1)), F.Open, e, F.Close);
    private static Formula Tensor(Formula x, Formula y) => C("tensor", x, y);
    private static Formula Number => S(F.Mathbb, F.Grp(V("N")));
    private static Formula Real => S(F.Mathbb, F.Grp(V("R")));
    private static Formula Type => C("Type");
    private static Formula Matrix(Formula a) => C("Matrix", a, a, S(F.Mathbb, F.Grp(V("C"))));
    private static Formula Meas(Formula a) => C("MeasurableSpace", a);
    private static Formula Evt(Formula e, Formula a) => Mem(e, C("measurableSets", a));
    private static Formula Row(params Formula[] xs) => S(F.Begin, F.Grp(V("gathered")),
        F.Seq(xs.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { F.RowBreak, x }).ToArray()),
        F.End, F.Grp(V("gathered")));

    private static Formula EventFormula()
    {
        Formula h = V("h"), a = V("A"), hist = V("H"), t = V("T"), j = V("J");
        Formula o = C("Outcome", j, h), embed = C("embed", j, h), e = V("E"), x = V("X");
        Formula op(Formula eventSet, Formula input) => C("operation", j, h, eventSet, input);
        Formula coordinates = All("a", a, All("b", a, All("i", a, All("j", a,
            C("Measurable", S(F.LambdaLower, F.Sp, h, F.Mapsto, F.Sp,
                C("entry", op(Inv(embed, e), C("single", V("a"), V("b"), F.D(1))), V("i"), V("j"))))))));
        Formula additivity = All("f", S(Number, F.To, F.Sp, C("Set", o)), Imp(And(
            All("n", Number, Evt(C("f", V("n")), o)), C("PairwiseDisjoint", V("f"))),
            All("X", Matrix(a), All("i", a, All("j", a, C("HasSum",
                S(F.LambdaLower, F.Sp, V("n"), F.Mapsto, F.Sp, C("entry", op(C("f", V("n")), x), V("i"), V("j"))),
                C("entry", op(S(F.Cup, F.Underscore, F.Grp(V("n")), F.Sp, C("f", V("n"))), x), V("i"), V("j"))))))));
        Formula fields = All("h", hist, And(
            C("MeasurableSpace", o),
            All("o", o, Eq(C("preceding", j, C("embed", j, h, V("o"))), h)),
            All("E", C("Set", t), Imp(Evt(e, t), And(Evt(Inv(embed, e), o), coordinates))),
            All("E", C("Set", o), C("CompletelyPositive", C("operation", j, h, e))),
            All("X", Matrix(a), Eq(op(F.Emptyset, x), F.D(0))), additivity));
        return F.Disp(All("H", Type, All("T", Type, All("A", Type,
            Imp(And(Meas(hist), Meas(t), C("Fintype", a), C("DecidableEq", a)),
                All("J", C("ActualEventStage", hist, t, a),
                    And(C("Measurable", C("preceding", j)), fields)))))));
    }

    private static Formula PolicyFormula()
    {
        Formula n = V("n"), p = V("P"), h = V("h"), f = V("F"), d = V("D"), a = V("A");
        Formula fn(Formula index) => C("F", index);
        Formula next = S(n, F.Plus, F.Sp, F.D(1));
        Formula stop = C("stop", p, n), cem = C("cemetery", p, n), stage = C("stage", p, n);
        Formula record(Formula index, Formula history) => C("record", p, index, history);
        Formula transition = All("n", Number, Imp(S(n, F.Lt, F.Sp, V("N")), And(
            Evt(stop, fn(n)), Mem(stage, C("ActualEventStage", fn(n), fn(next), a)),
            C("Measurable", C("time", p, n)), Mem(C("time", p, n), S(fn(n), F.To, F.Sp, Real)),
            C("Measurable", cem), Mem(cem, S(fn(n), F.To, F.Sp, fn(next))),
            All("h", fn(n), And(Eq(C("preceding", stage, C("cemetery", p, n, h)), h),
                Imp(And(Mem(h, stop), S(next, F.Lt, F.Sp, V("N"))), Mem(C("cemetery", p, n, h), C("stop", p, next))),
                Imp(Mem(h, stop), Eq(record(next, C("cemetery", p, n, h)), record(n, h))),
                All("o", C("Outcome", stage, h), Imp(S(F.Neg, F.Sp, Mem(h, stop)),
                    Eq(C("fst", record(next, C("embed", stage, h, V("o")))),
                        S(C("fst", record(n, h)), F.Plus, F.Sp, F.D(1))))))))));
        Formula records = All("i", C("Fin", S(V("N"), F.Plus, F.Sp, F.D(1))), And(
            Mem(C("record", p, V("i")), S(fn(V("i")), F.To, F.Sp, Number, F.Times, F.Sp, d)),
            C("Measurable", C("record", p, V("i")))));
        return F.Disp(All("N", Number, All("F", S(C("Fin", S(V("N"), F.Plus, F.Sp, F.D(1))), F.To, F.Sp, Type),
            All("D", Type, All("A", Type, Imp(And(Meas(d), C("Fintype", a), C("DecidableEq", a),
                All("i", C("Fin", S(V("N"), F.Plus, F.Sp, F.D(1))), Meas(fn(V("i"))))),
                All("P", C("FiniteStoppedPolicy", V("N"), f, d, a), And(transition, records))))))));
    }

    private static Formula StepFormula()
    {
        Formula n = V("n"), p = V("P"), h = V("h"), e = V("E"), x = V("X"), a = V("A"), b = V("B");
        Formula phi = C("operation", C("stage", p, n), h, Inv(C("embed", C("stage", p, n), h), e));
        Formula wait = C("exp", S(F.Minus, F.Sp, C("imaginaryUnit"), C("time", p, n, h), Tensor(V("H"), C("I", b))));
        Formula joint = C("mul", wait, x, C("adjoint", wait));
        Formula linear = S(C("ofMatrixLinearEquiv", a), F.Caret, F.Grp(F.Minus, F.D(1)),
            F.Circ, C("linearMap", phi), F.Circ, C("ofMatrixLinearEquiv", a));
        Formula action = C("kron", linear, C("id", Matrix(b)), joint);
        Formula branches = Row(
            Imp(Mem(h, C("stop", p, n)), Eq(C("actualFiniteStep", p, V("H"), n, h, e, x),
                C("indicator", e, C("cemetery", p, n, h), x))),
            Imp(S(F.Neg, F.Sp, Mem(h, C("stop", p, n))), Eq(C("actualFiniteStep", p, V("H"), n, h, e, x), action)));
        return F.Disp(All("N", Number, All("F", S(C("Fin", S(V("N"), F.Plus, F.Sp, F.D(1))), F.To, F.Sp, Type),
            All("D", Type, All("A", Type, All("B", Type,
            Imp(And(Meas(V("D")), C("Fintype", a), C("DecidableEq", a), C("Fintype", b), C("DecidableEq", b),
                All("i", C("Fin", S(V("N"), F.Plus, F.Sp, F.D(1))), Meas(C("F", V("i"))))),
            All("P", C("FiniteStoppedPolicy", V("N"), V("F"), V("D"), a), All("H", Matrix(a),
            All("n", Number, Imp(S(n, F.Lt, F.Sp, V("N")), All("h", C("F", n),
            All("E", C("Set", C("F", S(n, F.Plus, F.Sp, F.D(1)))), All("X", Matrix(S(a, F.Times, F.Sp, b)), branches))))))))))))));
    }

    private static Formula TheoremFormula()
    {
        Formula n = V("n"), sigma = V("s"), h = V("h"), mu = V("m"), beta = V("b"), e = V("e");
        Formula hidden = C("DensityState", C("Fin", e));
        Formula hist(Formula index) => C("F", index);
        Formula law(Formula index) => C("law", C("G", sigma, index));
        Formula rho(Formula index, Formula history) => C("density", C("G", sigma, index), history);
        Formula record(Formula index) => C("record", V("P"), index);
        Formula next = S(n, F.Plus, F.Sp, F.D(1));
        Formula map(Formula measure, Formula index) => C("map", record(index), measure);
        Formula integral(Formula eventSet, Formula density, Formula measure) => C("integral", eventSet, density, measure);
        Formula historyStates = All("i", C("Fin", S(V("N"), F.Plus, F.Sp, F.D(1))), And(
            C("IsProbabilityMeasure", law(V("i"))), C("Measurable", C("density", C("G", sigma, V("i")))),
            C("Integrable", C("density", C("G", sigma, V("i"))), law(V("i"))),
            All("h", hist(V("i")), And(C("PosSemidef", rho(V("i"), h)), Eq(C("trace", rho(V("i"), h)), F.D(1))))));
        Formula normalized = C("AlmostEverywhere", law(n), S(F.LambdaLower, F.Sp, h, F.Mapsto,
            Imp(S(F.Neg, F.Sp, F.Open, Mem(h, C("stop", V("P"), n)), F.Close),
                All("X", Matrix(V("A")), Eq(
                    C("trace", C("operation", C("stage", V("P"), n), h, C("univ"), V("X"))),
                    C("trace", V("X")))))));
        Formula nextIntegral = integral(V("E"), S(F.LambdaLower, F.Sp, h, F.Mapsto,
            C("entry", rho(next, h), V("i"), V("j"))), law(next));
        Formula precedingIntegral = integral(C("univ"), S(F.LambdaLower, F.Sp, h, F.Mapsto,
            C("entry", C("actualFiniteStep", V("P"), V("H"), n, h, V("E"), rho(n, h)), V("i"), V("j"))), law(n));
        Formula physical = All("E", C("Set", hist(next)), Imp(Evt(V("E"), hist(next)),
            All("i", S(V("A"), F.Times, F.Sp, C("Fin", e)),
            All("j", S(V("A"), F.Times, F.Sp, C("Fin", e)), Eq(nextIntegral, precedingIntegral)))));
        Formula initial = And(Eq(law(F.D(0)), C("dirac", V("hzero"))),
            C("EventuallyEqual", law(F.D(0)), C("density", C("G", sigma, F.D(0))),
                S(F.LambdaLower, F.Sp, h, F.Mapsto, Tensor(V("r"), C("matrix", sigma)))));
        Formula operational = All("s", hidden, And(historyStates, initial,
            All("n", Number, Imp(S(n, F.Lt, F.Sp, V("N")), And(normalized, physical)))));
        Formula stopped = All("s", hidden, All("n", Number, Imp(S(n, F.Lt, F.Sp, V("N")),
            All("E", C("Set", S(Number, F.Times, F.Sp, V("D"))), Imp(Evt(V("E"), S(Number, F.Times, F.Sp, V("D"))),
                Eq(C("measure", law(next), C("inter", Inv(C("preceding", C("stage", V("P"), n)), C("stop", V("P"), n)), Inv(record(next), V("E")))),
                    C("measure", law(n), C("inter", C("stop", V("P"), n), Inv(record(n), V("E"))))))))));
        Formula theta = S(F.Frac, F.Grp(S(C("log", e), F.Minus, F.Sp, C("vonNeumannEntropy", sigma))), F.Grp(beta));
        Formula risk = S(F.Int, F.Caret, F.Grp(F.Minus), F.Underscore, F.Grp(Mem(V("z"), Real)), F.Sp,
            C("ofReal", S(F.Lvert, F.Sp, V("z"), F.Minus, F.Sp, theta, F.Rvert)),
            F.Sp, C("d", C("bind", map(law(V("N")), V("N")), C("kernel", V("k"))), V("z")));
        Formula minimax = Eq(S(F.Operatorname, F.Grp(V("inf")), F.Underscore, F.Grp(Mem(V("k"), C("RealOutput", S(Number, F.Times, F.Sp, V("D"))))),
            F.Sp, F.Operatorname, F.Grp(V("sup")), F.Underscore, F.Grp(Mem(sigma, hidden)), F.Sp, risk),
            C("ofReal", S(F.Frac, F.Grp(C("log", e)), F.Grp(S(F.D(2), beta)))));
        Formula conclusion = Ex("m", C("Measure", hist(V("N"))), And(C("IsProbabilityMeasure", mu),
            All("s", hidden, And(Eq(law(V("N")), mu), Eq(map(law(V("N")), V("N")), map(mu, V("N"))))), stopped, minimax));
        Formula hypotheses = And(C("IsHermitian", V("H")), C("PosSemidef", V("r")), Eq(C("trace", V("r")), F.D(1)), operational);
        return F.Disp(All("A", Type, All("e", Number, All("b", Real,
            Imp(And(C("Fintype", V("A")), C("DecidableEq", V("A")), S(e, F.Geq, F.Sp, F.D(2)), S(beta, F.Gt, F.Sp, F.D(0))),
            All("N", Number, All("F", S(C("Fin", S(V("N"), F.Plus, F.Sp, F.D(1))), F.To, F.Sp, Type),
            All("D", Type, Imp(And(Meas(V("D")), All("i", C("Fin", S(V("N"), F.Plus, F.Sp, F.D(1))), Meas(hist(V("i"))))),
            All("P", C("FiniteStoppedPolicy", V("N"), V("F"), V("D"), V("A")), All("H", Matrix(V("A")),
            All("hzero", hist(F.D(0)), All("r", Matrix(V("A")),
            All("G", S(hidden, F.To, F.Sp, F.Prod, F.Underscore, F.Grp(Mem(V("i"), C("Fin", S(V("N"), F.Plus, F.Sp, F.D(1))))),
                C("ActualHistory", hist(V("i")), S(V("A"), F.Times, F.Sp, C("Fin", e)))), Imp(hypotheses, conclusion)))))))))))))));
    }
}
