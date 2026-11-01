using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Contextuality;

internal sealed class OutcomeCommunicationChainedInequalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Contextuality/OutcomeCommunicationChainedInequality.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/braskchaves2017bellcommunication");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The relabelled chained inequality holds for every odd-input binary COD model.",
        H("The relabelled chained inequality for outcome communication"),
        Blocks(
            Node("is-cod-model", "Finite causal outcome-dependent models", "IsCODModel",
                IsCODModelFormula(),
                "A finite hidden-variable model has nonnegative weights summing to one. "
                    + "For each input and hidden value, Alice's binary response probabilities are nonnegative and normalized, "
                    + "and Bob's response probabilities are nonnegative and normalized for every raw Alice output. "
                    + "This is the finite formal reading of the causal outcome-dependent model in the source's equation (7), TeX lines 150–155.",
                AssessedProvenance.FromLiterature(Source)),
            Node("cod-behaviour", "The COD behaviour", "codBehaviour", CodBehaviourFormula(),
                "The behaviour is the weighted sum over hidden values of Alice's response at x and raw output a, "
                    + "followed by Bob's response at y conditioned on that same raw output. "
                    + "It is the factorization in the source's equation (7), TeX lines 150–155.",
                AssessedProvenance.FromLiterature(Source)),
            Node("relabel", "Alice's every-second-input relabelling", "relabel", RelabelFormula(),
                "The binary output is unchanged when the natural index of x is even and is reversed otherwise. "
                    + "Nat.mod denotes natural-number remainder, and the source input number is Fin.val(x)+1. "
                    + "Thus the displayed inequality reads Alice's output with the flip on every second input, as specified in TeX line 325.",
                AssessedProvenance.FromLiterature(Source)),
            Node("chained-value", "The relabelled chained expression", "chainedValue", ChainedValueFormula(),
                "The expression sums the unequal-output diagonal terms, the unequal-output consecutive off-diagonal terms, "
                    + "and the equal-output closing term. The predicates on Fin.val select consecutive pairs and the pair from zero to n−1. "
                    + "This is equation (25) in the source, TeX lines 317–325, with the relabelling made explicit.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The finite odd-input COD inequality", "claim", ClaimFormula(),
                "For every odd natural number of inputs and every finite hidden-variable binary COD model, "
                    + "the relabelled chained expression is at least one. This is the precise finite formal reading of the conjecture in TeX lines 321–325.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("outcome-communication-chained-inequality-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The odd-input COD inequality is proved"),
                StatementSource.FromAuthor(Disp(Local("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix an odd n, a finite hidden-variable type, and a COD model. For a deterministic response table, "
                            + "the chained expression is a sum of nonnegative zero-or-one terms. If it were below one, "
                            + "every diagonal term and every consecutive off-diagonal term would vanish. The diagonal condition "
                            + "then identifies Bob's response on each raw Alice output, while the consecutive condition identifies "
                            + "the response at the neighboring input. The relabelling makes these two required binary outputs different, "
                            + "so Alice's raw outputs must alternate along the consecutive inputs.")),
                    Paragraph(Text(
                        "Because n is odd, the last input has the same raw Alice output as the first, and both endpoint relabellings are the identity. "
                            + "The last diagonal condition therefore forces Bob's closing response to equal that output, whereas the closing equal-output term "
                            + "being zero forces it to differ. This contradiction proves the lower bound for every deterministic table.")),
                    Paragraph(Text(
                        "Every stochastic COD model is a convex mixture of those deterministic response tables. The mixture weights are nonnegative, "
                            + "sum to one, and reproduce the original factorized behaviour by finite response marginalization. "
                            + "The chained expression is linear in the behaviour, so it is the weighted sum of the deterministic expressions. "
                            + "Applying the deterministic lower bound to each table and summing the weighted inequalities gives the claimed bound."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("brask-chaves-2017-outcome-communication-chained-inequality"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("outcome-communication-chained-inequality-" + id),
        DeclarationHandle.Create(Prefix + declaration),
        H(title),
        StatementSource.FromAuthor(Disp(formula)),
        provenance,
        Blocks(Paragraph(Text(prose))),
        DescribeRole.Definition);

    private static Formula IsCODModelFormula()
    {
        Formula weights = All("l", X("α"), LE(Real(D(0)), At(X("w"), X("l"))));
        Formula weightSum = Equal(SumOver("l", X("α"), At(X("w"), X("l"))), Real(D(1)));
        Formula aliceNonnegative = All("x", FinOf(X("n")),
            All("l", X("α"),
                All("a", Binary(),
                    LE(Real(D(0)), At(X("alice"), X("x"), X("l"), X("a"))))));
        Formula aliceNormalized = All("x", FinOf(X("n")),
            All("l", X("α"),
                Equal(SumOver("a", Binary(), At(X("alice"), X("x"), X("l"), X("a"))), Real(D(1)))));
        Formula bobNonnegative = All("y", FinOf(X("n")),
            All("l", X("α"),
                All("a", Binary(),
                    All("b", Binary(),
                        LE(Real(D(0)), At(X("bob"), X("y"), X("l"), X("a"), X("b")))))));
        Formula bobNormalized = All("y", FinOf(X("n")),
            All("l", X("α"),
                All("a", Binary(),
                    Equal(SumOver("b", Binary(), At(X("bob"), X("y"), X("l"), X("a"), X("b"))), Real(D(1))))));
        Formula body = And(weights, And(weightSum,
            And(aliceNonnegative, And(aliceNormalized, And(bobNonnegative, bobNormalized)))));
        Formula binders = All("w", Arrow(X("α"), Reals()),
            All("alice", Arrow(FinOf(X("n")), Arrow(X("α"), Arrow(Binary(), Reals()))),
                All("bob", Arrow(FinOf(X("n")), Arrow(X("α"), Arrow(Binary(), Arrow(Binary(), Reals())))),
                    Iff(LocalCall("IsCODModel", X("w"), X("alice"), X("bob")), body))));
        return All("n", Naturals(), All("α", TypeSort(), InstanceBinder("α", binders)));
    }

    private static Formula CodBehaviourFormula()
    {
        Formula value = SumOver("l", X("α"),
            Mul(Mul(At(X("w"), X("l")), At(X("alice"), X("x"), X("l"), X("a"))),
                At(X("bob"), X("y"), X("l"), X("a"), X("b"))));
        Formula binders = All("w", Arrow(X("α"), Reals()),
            All("alice", Arrow(FinOf(X("n")), Arrow(X("α"), Arrow(Binary(), Reals()))),
                All("bob", Arrow(FinOf(X("n")), Arrow(X("α"), Arrow(Binary(), Arrow(Binary(), Reals())))),
                    All("x", FinOf(X("n")),
                        All("y", FinOf(X("n")),
                            All("a", Binary(),
                                All("b", Binary(),
                                    Equal(LocalCall("codBehaviour", X("w"), X("alice"), X("bob"), X("x"), X("y"), X("a"), X("b")), value))))))));
        return All("n", Naturals(), All("α", TypeSort(), InstanceBinder("α", binders)));
    }

    private static Formula RelabelFormula()
    {
        Formula body = Equal(LocalCall("relabel", X("x"), X("a")),
            If(Equal(At(Qualified("Nat", "mod"), Val(X("x")), D(2)), D(0)), X("a"), At(Qualified("Fin", "rev"), X("a"))));
        return All("n", Naturals(), All("x", FinOf(X("n")), All("a", Binary(), body)));
    }

    private static Formula ChainedValueFormula()
    {
        Formula diagonal = SumOver("x", FinOf(X("n")), SumOver("c", Binary(), SumOver("b", Binary(),
            If(Ne(X("c"), X("b")), At(X("p"), X("x"), X("x"), LocalCall("relabel", X("x"), X("c")), X("b")), Real(D(0))))));
        Formula adjacent = SumOver("x", FinOf(X("n")), SumOver("y", FinOf(X("n")),
            If(Equal(Val(X("x")), Add(Val(X("y")), D(1))),
                SumOver("c", Binary(), SumOver("b", Binary(),
                    If(Ne(X("c"), X("b")), At(X("p"), X("x"), X("y"), LocalCall("relabel", X("x"), X("c")), X("b")), Real(D(0))))),
                Real(D(0)))));
        Formula closing = SumOver("x", FinOf(X("n")), SumOver("y", FinOf(X("n")),
            If(And(Equal(Val(X("x")), D(0)), Equal(Add(Val(X("y")), D(1)), X("n"))),
                SumOver("c", Binary(), SumOver("b", Binary(),
                    If(Equal(X("c"), X("b")), At(X("p"), X("x"), X("y"), LocalCall("relabel", X("x"), X("c")), X("b")), Real(D(0))))),
                Real(D(0)))));
        Formula total = Add(Add(diagonal, adjacent), closing);
        return All("n", Naturals(),
            All("p", Arrow(FinOf(X("n")), Arrow(FinOf(X("n")), Arrow(Binary(), Arrow(Binary(), Reals())))),
                Equal(LocalCall("chainedValue", X("n"), X("p")), total)));
    }

    private static Formula ClaimFormula() => Iff(LocalCall("claim"), ClaimBody());

    private static Formula ClaimBody()
    {
        Formula conclusion = LE(Real(D(1)), LocalCall("chainedValue", X("n"),
            LocalCall("codBehaviour", X("w"), X("alice"), X("bob"))));
        Formula assumptions = Imp(LocalCall("IsCODModel", X("w"), X("alice"), X("bob")), conclusion);
        Formula binders = All("w", Arrow(X("α"), Reals()),
            All("alice", Arrow(FinOf(X("n")), Arrow(X("α"), Arrow(Binary(), Reals()))),
                All("bob", Arrow(FinOf(X("n")), Arrow(X("α"), Arrow(Binary(), Arrow(Binary(), Reals())))),
                    assumptions)));
        return All("n", Naturals(), Imp(Call("Odd", X("n")),
            All("α", TypeSort(), InstanceBinder("α", binders))));
    }

    private static Formula Local(string name) => Qualified(
        "D5", "S3", "Quantum", "Contextuality", "OutcomeCommunicationChainedInequality", name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula X(string name) => name == "α" ? Alpha : F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Call(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula Qualified(params string[] parts)
    {
        var items = new List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }

    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula TypeSort() => Seq(Operatorname, Grp(X("Type")));
    private static Formula Binary() => Call("Fin", D(2));
    private static Formula FinOf(Formula value) => Call("Fin", value);
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula InstanceBinder(string name, Formula body) => Seq(
        OpenBracket, Call("Fintype", X(name)), CloseBracket, Comma, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula Val(Formula value) => At(Qualified("Fin", "val"), value);
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        At(Qualified("ite"), Parenthesized(condition), yes, no);
    private static Formula Real(Formula value) => Typed(value, Reals());
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
