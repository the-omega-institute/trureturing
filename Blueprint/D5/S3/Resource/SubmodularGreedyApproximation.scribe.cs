using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Resource;

internal sealed class SubmodularGreedyApproximationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Resource/SubmodularGreedyApproximation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cardinality greedy approximation for monotone submodular objectives.",
        H("Cardinality greedy approximation for monotone submodular objectives"),
        Blocks(
            Node("marginal", "Marginal gain", MarginalFormula(),
                "The marginal is the change in a finite-set objective after inserting one element.", DescribeRole.Definition),
            Node("submodular", "Submodularity", SubmodularFormula(),
                "Submodularity is expressed by the union/intersection inequality.", DescribeRole.Definition),
            Node("monotone", "Monotonicity", MonotoneFormula(),
                "Monotonicity is inclusion monotonicity of the finite-set objective.", DescribeRole.Definition),
            Node("marginal-antitone", "Diminishing returns", MarginalAntitoneFormula(),
                "For nested base sets, a new element has no larger marginal at the larger base.", DescribeRole.Theorem),
            Node("marginal-sum-bound", "Union gain bound", MarginalSumBoundFormula(),
                "The gain of adjoining a finite set is bounded by the sum of its original-base marginals.", DescribeRole.Theorem),
            Node("greedy-step-gap", "One greedy step", GreedyStepFormula(),
                "A maximum available marginal captures at least the average remaining gain of a comparison set.", DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cardinality-greedy-one-sub-exp"),
                DeclarationHandle.Create(Prefix + "cardinality_greedy_one_sub_exp"),
                H("Nemhauser–Wolsey–Fisher cardinality-greedy bound"),
                StatementSource.FromAuthor(CardinalityGreedyFormula()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Combinatorics/nemhauserwolseyfisher1978submodular")),
                Blocks(Paragraph(Text(
                    "The proof iterates the one-step gap with ratio 1-1/k and uses " +
                    "(1-1/k)^k ≤ exp(-1). The statement is valid for any ground type with " +
                    "decidable equality because all comparison and greedy sets are finite. " +
                    "It does not assert a weighted-cost, curvature-dependent, or non-monotone extension."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string id, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("submodular-greedy-" + id), DeclarationHandle.Create(Prefix + Declaration(id)),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static string Declaration(string id) => id switch
    {
        "marginal" => "marginal",
        "submodular" => "Submodular",
        "monotone" => "Monotone",
        "marginal-antitone" => "marginal_antitone",
        "marginal-sum-bound" => "marginal_sum_bound",
        "greedy-step-gap" => "greedy_step_gap",
        _ => id
    };

    private static Formula MarginalFormula() =>
        Disp(Forall("Alpha", Type(), Forall("f", FinsetTo("Alpha", Real()),
            Forall("S", Finset("Alpha"), Forall("x", X("Alpha"),
                Eq(Call("marginal", X("f"), X("S"), X("x")),
                    Sub(Call("f", Insert(X("x"), X("S"))), Call("f", X("S")))))))));

    private static Formula SubmodularFormula() =>
        Disp(Forall("Alpha", Type(), Forall("f", FinsetTo("Alpha", Real()),
            Iff(Call("Submodular", X("f")),
                Forall("A", Finset("Alpha"), Forall("B", Finset("Alpha"),
                    Ge(Add(Call("f", X("A")), Call("f", X("B"))),
                        Add(Call("f", Union(X("A"), X("B"))), Call("f", Inter(X("A"), X("B")))))))))));

    private static Formula MonotoneFormula() =>
        Disp(Forall("Alpha", Type(), Forall("f", FinsetTo("Alpha", Real()),
            Iff(Call("Monotone", X("f")),
                Forall("A", Finset("Alpha"), Forall("B", Finset("Alpha"),
                    Imp(Subset(X("A"), X("B")), Le(Call("f", X("A")), Call("f", X("B"))))))))));

    private static Formula MarginalAntitoneFormula() =>
        Disp(Forall("Alpha", Type(), Forall("f", FinsetTo("Alpha", Real()),
            Forall("hf", Call("Submodular", X("f")),
                Forall("A", Finset("Alpha"), Forall("B", Finset("Alpha"),
                    Forall("x", X("Alpha"),
                        Imp(Subset(X("A"), X("B")), Imp(NotMem(X("x"), X("B")),
                            Le(Call("marginal", X("f"), X("B"), X("x")),
                               Call("marginal", X("f"), X("A"), X("x"))))))))))));

    private static Formula MarginalSumBoundFormula() =>
        Disp(Forall("Alpha", Type(), Forall("f", FinsetTo("Alpha", Real()),
            Forall("hf", Call("Submodular", X("f")), Forall("A", Finset("Alpha"), Forall("B", Finset("Alpha"),
                Le(Sub(Call("f", Union(X("A"), X("B"))), Call("f", X("A"))),
                    SumOver(X("x"), X("B"), Call("marginal", X("f"), X("A"), X("x"))))))))));

    private static Formula GreedyStepFormula() =>
        Disp(Forall("Alpha", Type(), Forall("f", FinsetTo("Alpha", Real()),
            Forall("hfmono", Call("Monotone", X("f")), Forall("hfsub", Call("Submodular", X("f")),
                Forall("k", Nat(), Forall("O", Finset("Alpha"), Forall("S", Finset("Alpha"), Forall("e", X("Alpha"),
                    Imp(Le(Card(X("O")), X("k")),
                        Imp(Forall("x", X("Alpha"), Imp(NotMem(X("x"), X("S")),
                            Le(Call("marginal", X("f"), X("S"), X("x")), Call("marginal", X("f"), X("S"), X("e"))))),
                            Le(Sub(Call("f", X("O")), Call("f", X("S"))),
                                Mul(Cast(X("k")), Call("marginal", X("f"), X("S"), X("e")))))))))))))));

    private static Formula CardinalityGreedyFormula()
    {
        Formula hstep = Forall("i", Nat(), Imp(Lt(X("i"), X("k")),
            Eq(At(X("S"), Add(X("i"), D(1))),
                Insert(At(X("e"), X("i")), At(X("S"), X("i"))))));
        Formula hgreedy = Forall("i", Nat(), Imp(Lt(X("i"), X("k")),
            Forall("x", X("Alpha"), Imp(NotMem(X("x"), At(X("S"), X("i"))),
                Le(Call("marginal", X("f"), At(X("S"), X("i")), X("x")),
                   Call("marginal", X("f"), At(X("S"), X("i")), At(X("e"), X("i"))))))));
        Formula conclusion = Ge(Call("f", At(X("S"), X("k"))),
            Mul(Sub(D(1), Call("RealExp", Seq(Minus, D(1)))), Call("f", X("O"))));
        Formula hypotheses = Imp(Eq(Call("f", Empty()), D(0)),
            Imp(Call("Monotone", X("f")),
                Imp(Call("Submodular", X("f")),
                    Imp(Gt(X("k"), D(0)),
                        Imp(Le(Card(X("O")), X("k")),
                            Imp(Eq(At(X("S"), D(0)), Empty()),
                                Imp(hstep, Imp(hgreedy, conclusion))))))));
        return Disp(Forall("Alpha", Type(), Forall("f", FinsetTo("Alpha", Real()),
            Forall("k", Nat(), Forall("O", Finset("Alpha"),
                Forall("S", NatTo(Finset("Alpha")), Forall("e", NatTo(X("Alpha")), hypotheses)))))));
    }

    private static Formula Type() => F.Id("Type");
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula X(string name) => F.Id(name);
    private static Formula Forall(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Finset(Formula type) => Call("Finset", type);
    private static Formula Finset(string name) => Finset(X(name));
    private static Formula FinsetTo(string name, Formula codomain) => new Formula.TypeArrow(Finset(X(name)), codomain);
    private static Formula NatTo(Formula codomain) => new Formula.TypeArrow(Nat(), codomain);
    private static Formula Insert(Formula x, Formula s) => Call("insert", x, s);
    private static Formula Union(Formula a, Formula b) => Seq(a, Sp, Cup, Sp, b);
    private static Formula Inter(Formula a, Formula b) => Call("inter", a, b);
    private static Formula Empty() => Emptyset;
    private static Formula Sub(Formula a, Formula b) => Seq(Open, a, Minus, b, Close);
    private static Formula Mul(Formula a, Formula b) => Seq(Open, a, Cdot, b, Close);
    private static Formula Add(Formula a, Formula b) => Seq(Open, a, Plus, b, Close);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ge(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.GreaterThanOrEqual, b);
    private static Formula Gt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.GreaterThan, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula NotMem(Formula x, Formula s) => new Formula.Not(new Formula.Relation(x, FormulaRelationOperator.MemberOf, s));
    private static Formula Subset(Formula a, Formula b) => Seq(a, Sp, Subseteq, Sp, b);
    private static Formula Card(Formula s) => Seq(s, Dot, F.Id("card"));
    private static Formula SumOver(Formula x, Formula s, Formula body) =>
        Seq(F.Sum, Underscore, Grp(Seq(x, Sp, InMacro, Sp, s)), Sp, body);
    private static Formula Cast(Formula x) => Seq(Open, x, Colon, Sp, Real(), Close);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
}
