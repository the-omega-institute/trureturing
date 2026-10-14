using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class UnentangledOddPrimeCommunicationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/UnentangledOddPrimeCommunication.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/bakhshinezhad2024scalable");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every odd prime dimension, unentangled quantum messages have sharp average success probability 2/(d + 1), including finite mixtures with shared classical randomness.",
        H("The sharp odd-prime unentangled communication bound"),
        Blocks(
            Node("tensor", "The joint matrix space", "tensor", TensorFormula(),
                "The standard Kronecker product is reindexed by finProdFinEquiv on both indices. Thus matrices on Fin m and Fin n give a matrix on Fin (m * n), representing the joint message space.",
                AssessedProvenance.FromRepo()),
            Node("phase", "The two coordinate phases", "phase", PhaseFormula(),
                "For none, the phase is s times x.1, the pair's first coordinate. For some t, it is x.2 minus 2 times s times t times x.1. The Lean coordinates x.1 and x.2 correspond to the source coordinates x₀ and x₁, respectively; none represents the source input z = d.",
                AssessedProvenance.FromLiterature(Source)),
            Node("win", "The winning output", "win", WinFormula(),
                "Equation (27) adds Alice's phase with sign one to Bob's phase with sign minus one. In the source's coordinate notation, win (some t) x y = x₁ + y₁ − 2t(x₀ − y₀), and win none x y = x₀ − y₀. Both expressions are in ZMod d.",
                AssessedProvenance.FromLiterature(Source)),
            Node("valid", "Density matrices and joint measurements", "Valid", ValidFormula(),
                "For every input pair, Alice and Bob each send a positive semidefinite d-by-d matrix of trace one. For each z, Charlie's d effects are positive semidefinite matrices on the joint d²-dimensional space and sum to the identity. The effects may describe an entangled joint measurement.",
                AssessedProvenance.FromLiterature(Source)),
            Node("score", "The average success probability", "score", ScoreFormula(),
                "This is Equation (28), with p(c | x, y, z) = tr(α_x ⊗ β_y M_c|z) from Equation (19), and none the source's z = d. The two input pairs range independently over ZMod d × ZMod d, and Charlie's input ranges over Option (ZMod d). Taking Complex.re defines a real score for all matrices; for a valid strategy the trace is real and is the winning probability.",
                AssessedProvenance.FromLiterature(Source)),
            Node("mixture-score", "Shared classical randomness", "mixtureScore", MixtureFormula(),
                "A finite mixture uses one common index l for Alice's encoding, Bob's encoding and Charlie's measurement. The mixture score is their weighted sum. Nonnegative weights summing to one describe shared classical randomness, as allowed in Section V.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The upper bound and its attainment", "claim", ClaimFormula(),
                "Conjecture 1, Equation (29), asserts that the largest unentangled value is 2/(d + 1) for every odd prime d. The first two clauses bound every fixed strategy and every finite convex mixture, respectively. The final clause states attainment by a valid fixed strategy. Primality supplies the nonzero dimension required by Valid, score and mixtureScore.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("unentangled-odd-prime-communication-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The sharp bound holds in every odd prime dimension"),
                StatementSource.FromAuthor(Disp(Local("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Character orthogonality expands the score into the constant contribution 1/d and a sum over nonzero Fourier modes. Each term pairs the Kronecker product of the two encoding coefficients with a Fourier coefficient of Charlie's POVM. Positivity of the trace of a product of positive semidefinite effects bounds the squared Frobenius norm of each measurement coefficient by d². Cauchy–Schwarz then bounds the real trace term by d/2 times the sum of the two squared encoding norms.")),
                    Paragraph(Text(
                        "For either encoding sign s, the slope frequencies (s k, 0) for none and (−2s t k, k) for some t, with k nonzero, enumerate every nonzero frequency in (ZMod d)² exactly once. This uses that d is prime and odd. Parseval with the constant mode removed gives d² times the sum of the squared state norms minus the squared norm of their sum. Each density matrix has squared Frobenius norm at most one, while their sum has trace d² and squared norm at least d³. Hence the total nonzero-mode energy is at most d⁴ − d³ for each sender, giving the score bound 2/(d + 1). Nonnegative normalized mixtures preserve the bound.")),
                    Paragraph(Text(
                        "For attainment, Alice and Bob send the computational-basis states labeled by x₀ and y₀. For none, Charlie measures their label difference and wins with probability one. For some t, the uniform effects (1/d) times the identity give success probability 1/d. Averaging over the d + 1 inputs gives (1 + d(1/d))/(d + 1) = 2/(d + 1)."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bakhshinezhad-mehboudi-roch-i-carceller-tavakoli-2024-odd-prime-unentangled-bound"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("unentangled-odd-prime-communication-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(name));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "QuantumBounds", "UnentangledOddPrimeCommunication", name);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Dimension() => Parenthesized(Seq(X("d"), Sp, Colon, Eq, Sp, X("d")));
    private static Formula StrategyCall(string name, Formula alpha, Formula beta, Formula measurement) =>
        LocalCall(name, Dimension(), alpha, beta, measurement);
    private static Formula Parenthesized(Formula value) => Seq(F.Open, value, F.Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula Fin(Formula n) => At(Qualified("Fin"), n);
    private static Formula Field() => At(Qualified("ZMod"), X("d"));
    private static Formula Pair() => Parenthesized(Seq(Field(), Sp, Times, Sp, Field()));
    private static Formula Inputs() => At(Qualified("Option"), Field());
    private static Formula MatrixType(Formula n) => At(Qualified("Matrix"), Fin(n), Fin(n), Complexes());
    private static Formula MessageMatrix() => MatrixType(X("d"));
    private static Formula JointMatrix() => MatrixType(Multiply(X("d"), X("d")));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Encoding() => Arrow(Pair(), MessageMatrix());
    private static Formula Measurement() => Arrow(Inputs(), Arrow(Field(), JointMatrix()));
    private static Formula MixtureEncoding() => Arrow(Fin(X("L")), Encoding());
    private static Formula MixtureMeasurement() => Arrow(Fin(X("L")), Measurement());
    private static Formula All(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula Some(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), type, body);
    private static Formula WithDimension(Formula body) => All("d", Naturals(), Seq(
        OpenBracket, At(Qualified("NeZero"), X("d")), CloseBracket, Comma, Sp, body));
    private static Formula ForStrategy(Formula body) => All("alpha", Encoding(),
        All("beta", Encoding(), All("M", Measurement(), body)));
    private static Formula ForMixture(Formula body) => All("L", Naturals(),
        All("q", Arrow(Fin(X("L")), Reals()), All("alpha", MixtureEncoding(),
            All("beta", MixtureEncoding(), All("M", MixtureMeasurement(), body)))));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalent(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Coordinate(string name, byte index) => Seq(X(name), Dot, D(index));
    private static Formula SumOver(string variable, Formula type, Formula summand) => Seq(
        new Formula.Subscript(F.Sum, Seq(X(variable), Colon, Sp, type)), Sp, Parenthesized(summand));
    private static Formula Trace(Formula matrix) => At(Qualified("Matrix", "trace"), matrix);
    private static Formula PositiveSemidefinite(Formula matrix) => At(Qualified("Matrix", "PosSemidef"), matrix);
    private static Formula Density(Formula matrix) => And(PositiveSemidefinite(matrix), Equal(Trace(matrix), D(1)));
    private static Formula Bound() => new Formula.Fraction(D(2), Add(Parenthesized(Seq(X("d"), Colon, Sp, Reals())), D(1)));

    private static Formula TensorFormula() => All("m", Naturals(), All("n", Naturals(),
        All("A", MatrixType(X("m")), All("B", MatrixType(X("n")), Equal(
            LocalCall("tensor", X("A"), X("B")),
            At(Qualified("Matrix", "reindex"), Qualified("finProdFinEquiv"), Qualified("finProdFinEquiv"),
                At(Qualified("Matrix", "kronecker"), X("A"), X("B"))))))));

    private static Formula PhaseFormula()
    {
        Formula finitePhase = Subtract(Coordinate("x", 2),
            Multiply(Multiply(Multiply(D(2), X("s")), X("t")), Coordinate("x", 1)));
        Formula lambda = Parenthesized(Seq(LambdaLower, Sp, X("t"), Colon, Sp, Field(), Comma, Sp, finitePhase));
        return All("d", Naturals(), All("s", Field(), All("z", Inputs(), All("x", Pair(), Equal(
            LocalCall("phase", X("s"), X("z"), X("x")),
            At(Qualified("Option", "elim"), X("z"), Multiply(X("s"), Coordinate("x", 1)), lambda))))));
    }

    private static Formula WinFormula() => All("d", Naturals(), All("z", Inputs(),
        All("x", Pair(), All("y", Pair(), Equal(LocalCall("win", X("z"), X("x"), X("y")),
            Add(LocalCall("phase", D(1), X("z"), X("x")),
                LocalCall("phase", new Formula.Negate(D(1)), X("z"), X("y"))))))));

    private static Formula ValidFormula()
    {
        Formula conditions = And(All("x", Pair(), Density(At(X("alpha"), X("x")))),
            And(All("y", Pair(), Density(At(X("beta"), X("y")))),
                And(All("z", Inputs(), All("c", Field(), PositiveSemidefinite(At(X("M"), X("z"), X("c"))))),
                    All("z", Inputs(), Equal(SumOver("c", Field(), At(X("M"), X("z"), X("c"))), D(1))))));
        return WithDimension(ForStrategy(Equivalent(
            StrategyCall("Valid", X("alpha"), X("beta"), X("M")), conditions)));
    }

    private static Formula ScoreFormula()
    {
        Formula probability = At(Qualified("Complex", "re"), Trace(Multiply(
            LocalCall("tensor", At(X("alpha"), X("x")), At(X("beta"), X("y"))),
            At(X("M"), X("z"), LocalCall("win", X("z"), X("x"), X("y"))))));
        Formula realDimension = Parenthesized(Seq(X("d"), Colon, Sp, Reals()));
        Formula normalization = new Formula.Fraction(D(1), Multiply(
            new Formula.Power(realDimension, D(4)), Parenthesized(Add(realDimension, D(1)))));
        return WithDimension(ForStrategy(Equal(
            StrategyCall("score", X("alpha"), X("beta"), X("M")), Multiply(normalization,
                SumOver("x", Pair(), SumOver("y", Pair(), SumOver("z", Inputs(), probability)))))));
    }

    private static Formula MixtureValue() => LocalCall("mixtureScore", Dimension(), X("q"), X("alpha"), X("beta"), X("M"));
    private static Formula MixtureFormula() => WithDimension(ForMixture(Equal(MixtureValue(),
        SumOver("l", Fin(X("L")), Multiply(At(X("q"), X("l")),
            StrategyCall("score", At(X("alpha"), X("l")), At(X("beta"), X("l")), At(X("M"), X("l"))))))));

    private static Formula ClaimFormula()
    {
        Formula fixedBound = ForStrategy(ImpliesFormula(
            StrategyCall("Valid", X("alpha"), X("beta"), X("M")),
            AtMost(StrategyCall("score", X("alpha"), X("beta"), X("M")), Bound())));
        Formula mixtureBound = ForMixture(ImpliesFormula(All("l", Fin(X("L")), AtMost(D(0), At(X("q"), X("l")))),
            ImpliesFormula(Equal(SumOver("l", Fin(X("L")), At(X("q"), X("l"))), D(1)),
                ImpliesFormula(All("l", Fin(X("L")), StrategyCall("Valid",
                    At(X("alpha"), X("l")), At(X("beta"), X("l")), At(X("M"), X("l")))),
                    AtMost(MixtureValue(), Bound())))));
        Formula attainment = Some("alpha", Encoding(), Some("beta", Encoding(), Some("M", Measurement(),
            And(StrategyCall("Valid", X("alpha"), X("beta"), X("M")),
                Equal(StrategyCall("score", X("alpha"), X("beta"), X("M")), Bound())))));
        return Equivalent(Local("claim"), All("d", Naturals(),
            ImpliesFormula(At(Qualified("Nat", "Prime"), X("d")),
                ImpliesFormula(At(Qualified("Odd"), X("d")),
                    And(And(fixedBound, mixtureBound), attainment)))));
    }
}
