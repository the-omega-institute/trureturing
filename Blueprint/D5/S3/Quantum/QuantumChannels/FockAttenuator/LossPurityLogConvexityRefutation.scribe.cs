using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.FockAttenuator;

internal sealed class LossPurityLogConvexityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/hertz2025lossbeamsplitters");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The purity of a three-level mixed Fock state under vacuum-environment optical loss fails the midpoint inequality for log-convexity.",
        H("Optical-loss purity need not be log-convex"), Blocks(
            Paragraph(Text(
                "The one-mode Hilbert space is the full space of square-summable complex sequences. "
                    + "H and Op retain the namespaces of PureLossIncompatibility. The outer coordinate "
                    + "of the two-mode space indexes the environment, which purePartialTrace discards. "
                    + "The vectors e n are the Fock basis. Transmissivity T ranges over the closed "
                    + "unit interval, and hT is its interval-membership proof. Complex.ofReal is "
                    + "the real-to-complex cast; scalar multiplication uses the complex scalar action. "
                    + "Named objects retain their Lean namespaces.")),
            Node("loss", "Loss of a finite ensemble", LossFormula(),
                "Section I.A, equation (2), defines optical loss by mixing the input with a vacuum environment on a beam splitter and tracing out that environment. The displayed finite sum applies this channel to each pure vector with its real weight. Normalized nonnegative weights and unit vectors are required by claim, rather than by loss itself. T=1 means no loss.",
                AssessedProvenance.FromLiterature(Source)),
            Node("IsPurityCurve", "The convergent Fock-basis trace of the square", PurityFormula(),
                "The purity in Section III and Conjecture 7 is the trace of the square of the output state. HasSum expresses the sum of its Fock-basis diagonal, including convergence and equality to the real value P(T), viewed in Complex. Every T in the closed unit interval is included.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 7 on finite ensembles", ClaimFormula(),
                "Section III, Conjecture 7, asserts that the purity under loss is log-convex on [0,1]; equation (26) states the equivalent derivative inequality. Here k is any natural number, the real weights are nonnegative and sum to one, and every pure vector has norm one. The claim asks for the actual purity curve and convexity of its logarithm. Every finite ensemble represents a state, so the source's assertion for every state implies this finite-ensemble statement. ConvexOn includes both endpoints and requires no differentiability hypothesis.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("loss-purity-log-convexity-result"), DeclarationHandle.Create(Prefix + "result"),
                H("A three-level counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take the Fock-diagonal input diag(1/100,3/4,6/25), with zero population above level two. "
                            + "Binomial thinning gives diag(q_0,q_1,q_2), where "
                            + "q_0=1/100+(3/4)(1-T)+(6/25)(1-T)^2, "
                            + "q_1=(3/4)T+(12/25)T(1-T), and q_2=(6/25)T^2. "
                            + "Its purity is q_0^2+q_1^2+q_2^2="
                            + "(1728T^4-8856T^3+17529T^2-12300T+5000)/5000.")),
                    Paragraph(Text(
                        "At T=39/40, 49/50 and 197/200 the purity values are respectively "
                            + "120972467/200000000, 4749230357/7812500000 and 76369391837/125000000000. "
                            + "The middle transmissivity is the midpoint of the other two. "
                            + "The square of its purity exceeds the product of the endpoint purities by "
                            + "7296233469022569/15625000000000000000000. All three values are positive. "
                            + "Convexity of their logarithms would give the opposite weak inequality, "
                            + "so Conjecture 7 fails for this mixed state."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hertz-lupu-gladstein-heshami-goldberg-2025-loss-purity-log-convexity"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("loss-purity-log-convexity-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula LossFormula()
    {
        Formula output = At(Qualified("D5", "S3", "Quantum", "QuantumChannels",
                "FockAttenuator", "DisplacementCovariance", "purePartialTrace"),
            At(Qualified("D5", "S3", "Quantum", "QuantumChannels", "FockAttenuator",
                    "BeamSplitter", "beamSplitter"), X("T"), X("hT"),
                At(Qualified("D5", "S3", "Quantum", "QuantumChannels", "FockAttenuator",
                    "BeamSplitter", "tensor"), At(X("phi"), X("i")), E(D(0)))));
        return EnsembleBinders(All("T", Reals(), All("hT", Member(X("T"), Interval()),
            Equal(LocalCall("loss", X("p"), X("phi"), X("T"), X("hT")),
                SumOver("i", FinOf(X("k")),
                    Smul(At(Qualified("Complex", "ofReal"), At(X("p"), X("i"))), output))))));
    }

    private static Formula PurityFormula()
    {
        Formula output = LocalCall("loss", X("p"), X("phi"), X("T"), X("hT"));
        Formula summand = At(Qualified("inner"), Complexes(), E(X("n")),
            At(At(Qualified("ContinuousLinearMap", "comp"), output, output), E(X("n"))));
        return EnsembleBinders(All("P", Arrow(Reals(), Reals()),
            Equivalence(LocalCall("IsPurityCurve", X("p"), X("phi"), X("P")),
                All("T", Reals(), All("hT", Member(X("T"), Interval()),
                    At(Qualified("HasSum"), LambdaOf("n", Naturals(), summand),
                        At(Qualified("Complex", "ofReal"), At(X("P"), X("T")))))))));
    }

    private static Formula ClaimFormula()
    {
        Formula nonnegative = All("i", FinOf(X("k")), LE(D(0), At(X("p"), X("i"))));
        Formula normalized = Equal(SumOver("i", FinOf(X("k")), At(X("p"), X("i"))), D(1));
        Formula unitVectors = All("i", FinOf(X("k")),
            Equal(new Formula.Norm(At(X("phi"), X("i"))), D(1)));
        Formula conclusion = Ex("P", Arrow(Reals(), Reals()),
            And(LocalCall("IsPurityCurve", X("p"), X("phi"), X("P")),
                At(Qualified("ConvexOn"), Reals(), Interval(),
                    LambdaOf("T", Reals(), At(Qualified("Real", "log"), At(X("P"), X("T")))))));
        return Equivalence(Local("claim"), EnsembleBinders(
            Imp(nonnegative, Imp(normalized, Imp(unitVectors, conclusion)))));
    }

    private static Formula EnsembleBinders(Formula body) => All("k", Naturals(),
        All("p", Arrow(FinOf(X("k")), Reals()),
            All("phi", Arrow(FinOf(X("k")), Measurement("H")), body)));
    private static Formula E(Formula n) => At(Qualified("D5", "S3", "Estimation",
        "TransmissivityBetaPriorProbeRefutation", "e"), n);
    private static Formula Measurement(string name) =>
        Qualified("D5", "S3", "Quantum", "Measurement", "PureLossIncompatibility", name);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum",
        "QuantumChannels", "FockAttenuator", "LossPurityLogConvexityRefutation", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Interval() => At(Qualified("Set", "Icc"), Typed(D(0), Reals()), D(1));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula Smul(Formula scalar, Formula vector) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(vector));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
