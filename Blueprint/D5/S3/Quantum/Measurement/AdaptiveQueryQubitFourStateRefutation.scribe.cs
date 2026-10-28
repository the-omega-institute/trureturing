using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class AdaptiveQueryQubitFourStateRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/leeheinosaari2026adaptivequery");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four qubit states admit an adaptive one-bit query with success 99/100, while every pre-measurement query has success at most 483/500.",
        H("An adaptive query advantage for four qubit states"), Blocks(
            Paragraph(Text(
                "Fin(n) consists of the indices 0 through n − 1. A one-bit query asks whether the state label "
                    + "belongs to a chosen finite subset X. Its two answers select X and its complement in Fin(n). "
                    + "The displayed conditional sets give these two subsets explicitly. Matrix.PosSemidef means "
                    + "positive semidefinite, Matrix.trace is the complex trace, and Complex.re takes its real part. "
                    + "The matrix 1 is the identity. Finset.Nonempty means that a finite set contains an element. "
                    + "All sums range over their displayed finite type or finite subset. The bracketed Fintype "
                    + "assumption is an anonymous instance supplying a finite enumeration.")),
            Node("Q2", "Qubit matrices", QubitFormula(),
                "The qubit operators are complex matrices with two rows and two columns. "
                    + "Density matrices and measurement effects use this same matrix space."),
            Node("IsEnsemble", "Priors and density matrices", EnsembleFormula(),
                "An ensemble assigns a nonnegative prior to every label, with total prior one, "
                    + "and a positive semidefinite matrix of trace one to each label. "
                    + "This is the state-discrimination setting of equations (1) and (2), with arbitrary priors."),
            Node("IsPOVM", "Finite quantum measurements", PovmFormula(),
                "A finite positive operator-valued measure consists of positive semidefinite effects summing "
                    + "to the identity. For a density matrix R and an effect E, Re tr(R E) is the probability "
                    + "of that measurement outcome, as in equation (1)."),
            Node("IsPreStrategy", "Querying before the measurement", PreStrategyFormula(),
                "The partition is chosen and its answer received before the measurement. "
                    + "For each nonempty answer subset, the receiver chooses a separate POVM indexed by that subset. "
                    + "Effects outside the corresponding subset are unrestricted and unused. "
                    + "An empty subset has no positivity or normalization requirements: its sum contributes zero. "
                    + "Thus X = Fin(n), whose other subset is empty, is included among the binary partitions in equation (3)."),
            Node("preValue", "Success with a pre-measurement query", PreValueFormula(),
                "For a fixed partition and its two measurements, equation (3) sums the prior-weighted "
                    + "probabilities of correctly guessing each label. The two answer subsets are disjoint, "
                    + "so their contributions add. An empty subset contributes an empty sum, equal to zero. "
                    + "The expression is defined for arbitrary priors, matrices and effects; the preceding predicates "
                    + "specify when it describes a discrimination experiment."),
            Node("Ppre", "The best pre-measurement value", PreSupremumFormula(),
                "The real supremum ranges over the values of every partition X and every pair of measurements "
                    + "satisfying IsPreStrategy. This expresses the optimization in equation (3), including "
                    + "partitions with an empty subset. The definition itself imposes no ensemble hypothesis."),
            Node("IsAdaptiveStrategy", "Queries chosen after an outcome", AdaptiveStrategyFormula(),
                "The receiver first performs one finite POVM. After observing outcome z, the receiver chooses "
                    + "the subset P(z) and asks the one-bit query for that partition. For each possible answer, "
                    + "the guess must lie in the corresponding subset. Both the partition and the guesses may "
                    + "depend on z, as in equation (5). The two guesses therefore belong to different subsets."),
            Node("adaptiveValue", "Success with an adaptive post-measurement query", AdaptiveValueFormula(),
                "Equation (5) adds the prior-weighted outcome probabilities for the two guesses at every "
                    + "measurement outcome. A label contributes when it equals the guess for the answer subset "
                    + "that contains it. The partition determines which guesses are allowed through IsAdaptiveStrategy; "
                    + "the numerical value depends only on the priors, states, measurement and guesses."),
            Node("claim", "The proposed absence of advantage from four labels onward", ClaimFormula(),
                "Section VI suggests that an adaptive post-measurement query may never outperform "
                    + "a pre-measurement query for qubit ensembles with at least four labels. "
                    + "The statement quantifies over every such ensemble, every finite number of outcomes, "
                    + "and every adaptive strategy. It bounds each adaptive value by Ppre, expressing "
                    + "the suggested inequality without taking an additional supremum over adaptive strategies.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("adaptive-query-qubit-four-state-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Four pure states with a strict adaptive advantage"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(N("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Use labels 0, 1, 2, 3 with priors (33,33,33,1)/100. "
                            + "The four density matrices are [[1,0],[0,0]], "
                            + "(1/5)[[1,2],[2,4]], (1/5)[[1,−2],[−2,4]], and (1/2)[[1,1],[1,1]], respectively. "
                            + "Each is a rational positive semidefinite matrix of rank one and trace one, "
                            + "so all four states are pure.")),
                    Paragraph(Text(
                        "Perform the three-outcome measurement with effects (3/4)[[0,0],[0,1]], "
                            + "(1/8)[[4,−2],[−2,1]], and (1/8)[[4,2],[2,1]]. "
                            + "These positive semidefinite matrices sum to the identity. "
                            + "Outcomes 0, 1, 2 have zero probability on states 0, 1, 2, respectively. "
                            + "At outcome 0, ask whether the label is in {1} and use guesses (1,2) for answers (0,1). "
                            + "At outcome 1, ask for {0} and use guesses (0,2). "
                            + "At outcome 2, ask for {0} and use guesses (0,1). "
                            + "The two surviving labels among 0, 1, 2 are distinguished at every outcome. "
                            + "Label 3 is never guessed. The success value is therefore 99/100.")),
                    Paragraph(Text(
                        "For the pre-measurement upper bound, associate a rational symmetric matrix Y_C "
                            + "to each answer subset C, with Y_C − π_x R_x positive semidefinite for every x in C. "
                            + "Here π_x and R_x are the displayed prior and density matrix for label x. "
                            + "Write S(a,b,c) = [[a,b],[b,c]]. For each of the following eight subsets X, "
                            + "the ordered pair specifies (Y_X,Y_(X complement)); every binary partition "
                            + "occurs in this list up to exchanging its two subsets.")),
                    Paragraph(Text(
                        "X = {0}: (S(33/100,0,0), S(99/500,0,99/250)). "
                            + "X = {0,1}: (S(173/500,33/500,7/25), S(147/2000,−16/125,533/2000)). "
                            + "X = {0,2}: (S(173/500,−33/500,7/25), S(27/400,33/250,529/2000)). "
                            + "X = {0,1,2}: (S(33/100,0,33/100), S(1/200,1/200,1/200)).")),
                    Paragraph(Text(
                        "X = {0,3}: (S(661/2000,0,11/2000), S(99/500,0,99/250)). "
                            + "X = {0,1,3}: (S(173/500,33/500,7/25), S(33/500,−33/250,33/125)). "
                            + "X = {0,2,3}: (S(173/500,−33/500,7/25), S(33/500,33/250,33/125)). "
                            + "X = {0,1,2,3}: (S(33/100,0,33/100), S(0,0,0)).")),
                    Paragraph(Text(
                        "The differences Y_C − π_x R_x have nonnegative diagonal entries and determinant. "
                            + "For a nonempty C and its POVM effects E_x, positivity gives "
                            + "π_x Re tr(R_x E_x) ≤ Re tr(Y_C E_x). Summing over C and using "
                            + "the identity sum of its effects bounds the contribution by Re tr(Y_C). "
                            + "An empty subset contributes zero, and all displayed traces are nonnegative. "
                            + "Each pair of traces has sum at most 483/500. The attainable pre-measurement "
                            + "value set is nonempty, so its supremum is at most 483/500. "
                            + "Since 99/100 exceeds 483/500 by 3/125, the four-state ensemble contradicts claim."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("lee-heinosaari-2026-adaptive-query-four-qubit-states"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance? provenance = null) => Describe.Lean(
            DescribeId.Create("adaptive-query-qubit-four-state-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance ?? AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Q(string name)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(Operatorname);
            items.Add(Grp(N(part)));
        }
        return Seq([.. items]);
    }
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Q(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Labels() => Fin(N("n"));
    private static Formula Subsets() => Call("Finset", Labels());
    private static Formula Priors() => Arrow(Labels(), N("Real"));
    private static Formula States() => Arrow(Labels(), N("Q2"));
    private static Formula PreEffects() => Arrow(Fin(D(2)), States());
    private static Formula Effects() => Arrow(Fin(N("m")), N("Q2"));
    private static Formula Partitions() => Arrow(Fin(N("m")), Subsets());
    private static Formula Guesses() => Arrow(Fin(N("m")), Arrow(Fin(D(2)), Labels()));
    private static Formula EnsembleBinders(Formula body) =>
        All("n", N("Nat"), All("q", Priors(), All("R", States(), body)));
    private static Formula PreBinders(Formula body) => All("X", Subsets(), All("M", PreEffects(), body));
    private static Formula AdaptiveBinders(Formula body) => All("m", N("Nat"),
        All("M", Effects(), All("P", Partitions(), All("f", Guesses(), body))));
    private static Formula AnswerSubset(Formula subset, Formula answer) => Seq(
        Q("if"), Sp, Parenthesized(Eq(answer, D(0))), Sp, Q("then"), Sp, subset,
        Sp, Q("else"), Sp, Call("Finset.compl", subset));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(N(name), Colon, type)), Parenthesized(body));
    private static Formula SumIn(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Member(N(name), set)), Parenthesized(body));
    private static Formula Positive(Formula matrix) => Call("Matrix.PosSemidef", matrix);
    private static Formula Trace(Formula matrix) => Call("Matrix.trace", matrix);
    private static Formula RealTrace(Formula matrix) => Call("Complex.re", Trace(matrix));
    private static Formula PreCall(string name) => Call(name, N("q"), N("R"), N("X"), N("M"));
    private static Formula AdaptiveCall() => Call("adaptiveValue", N("q"), N("R"), N("M"), N("f"));

    private static Formula QubitFormula() => Eq(N("Q2"), Call("Matrix", Fin(D(2)), Fin(D(2)), N("Complex")));

    private static Formula EnsembleFormula() => EnsembleBinders(IffFormula(Call("IsEnsemble", N("q"), N("R")),
        And(All("x", Labels(), Le(D(0), At(N("q"), N("x")))),
            And(Eq(SumOver("x", Labels(), At(N("q"), N("x"))), D(1)),
                All("x", Labels(), And(Positive(At(N("R"), N("x"))),
                    Eq(Trace(At(N("R"), N("x"))), D(1))))))));

    private static Formula PovmFormula() => All("iota", N("Type"), Instance(Call("Fintype", N("iota")),
        All("M", Arrow(N("iota"), N("Q2")), IffFormula(Call("IsPOVM", N("M")),
            And(All("z", N("iota"), Positive(At(N("M"), N("z")))),
                Eq(SumOver("z", N("iota"), At(N("M"), N("z"))), D(1)))))));

    private static Formula PreStrategyFormula()
    {
        var subset = AnswerSubset(N("X"), N("ell"));
        return All("n", N("Nat"), PreBinders(IffFormula(Call("IsPreStrategy", N("X"), N("M")),
            All("ell", Fin(D(2)), And(All("x", Labels(),
                Imp(Member(N("x"), subset), Positive(At(N("M"), N("ell"), N("x"))))),
                Imp(Call("Finset.Nonempty", subset),
                    Eq(SumIn("x", subset, At(N("M"), N("ell"), N("x"))), D(1))))))));
    }

    private static Formula PreValueFormula() => EnsembleBinders(PreBinders(
        Eq(Typed(PreCall("preValue"), N("Real")), SumOver("ell", Fin(D(2)),
            SumIn("x", AnswerSubset(N("X"), N("ell")), Mul(At(N("q"), N("x")),
                RealTrace(Mul(At(N("R"), N("x")), At(N("M"), N("ell"), N("x"))))))))));

    private static Formula PreSupremumFormula()
    {
        var values = Seq(OpenBrace, N("v"), Colon, N("Real"), Bar,
            Some("X", Subsets(), Some("M", PreEffects(),
                And(Call("IsPreStrategy", N("X"), N("M")), Eq(N("v"), PreCall("preValue"))))), CloseBrace);
        return EnsembleBinders(Eq(Typed(Call("Ppre", N("q"), N("R")), N("Real")), Call("sSup", values)));
    }

    private static Formula AdaptiveStrategyFormula() => All("n", N("Nat"), AdaptiveBinders(
        IffFormula(Call("IsAdaptiveStrategy", N("M"), N("P"), N("f")),
            And(Call("IsPOVM", N("M")), All("z", Fin(N("m")), All("ell", Fin(D(2)),
                Member(At(N("f"), N("z"), N("ell")), AnswerSubset(At(N("P"), N("z")), N("ell")))))))));

    private static Formula AdaptiveValueFormula()
    {
        var selected = At(N("f"), N("z"), N("ell"));
        var value = Eq(Typed(AdaptiveCall(), N("Real")),
            SumOver("z", Fin(N("m")), SumOver("ell", Fin(D(2)),
                Mul(At(N("q"), selected), RealTrace(Mul(At(N("R"), selected), At(N("M"), N("z"))))))));
        return All("n", N("Nat"), All("m", N("Nat"), All("q", Priors(), All("R", States(),
            All("M", Effects(), All("f", Guesses(), value))))));
    }

    private static Formula ClaimFormula() => IffFormula(N("claim"), All("n", N("Nat"),
        Imp(Le(D(4), N("n")), All("q", Priors(), All("R", States(),
            Imp(Call("IsEnsemble", N("q"), N("R")), AdaptiveBinders(
                Imp(Call("IsAdaptiveStrategy", N("M"), N("P"), N("f")),
                    Le(AdaptiveCall(), Call("Ppre", N("q"), N("R")))))))))));
}
