using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class DirectedPositiveNetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An increasing positive operator net converges strongly to its operator-order least upper bound.",
        H("Directed positive operator nets"),
        Blocks(Describe.Lean(
            DescribeId.Create("directed-positive-net-strong-order-lub"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Measurements/DirectedPositiveNet.directed_positive_net_strong_of_isLUB"),
            H("Strong convergence to the order supremum"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Analytic/peterson2013monotonenet")),
            Blocks(
                Paragraph(Text(
                    "H is any complete complex inner-product space. J is any nonempty directed "
                    + "preorder; a common upper index is sufficient, and no countable cofinal "
                    + "subset is assumed. ContinuousLinearMap denotes bounded complex linear "
                    + "operators. Their order is the positive-operator order.")),
                Paragraph(Text(
                    "X is positive at every index and monotone. IsLUB(range(X), U) says that U "
                    + "bounds all X(j) above and is below every such upper bound. The conclusions "
                    + "give the operator norm bound and pointwise strong convergence to U.")),
                Paragraph(Text(
                    "For a positive difference D, its continuous-functional-calculus square root "
                    + "gives the bound norm(D(v)) squared by norm(D) times the real quadratic form. "
                    + "Scalar monotone convergence and common upper indices then make every vector "
                    + "net Cauchy. Completeness, linearity of limits and the uniform norm bound "
                    + "construct a bounded linear limit S. Positivity survives strong limits, so "
                    + "S is a least upper bound and equals U.")),
                Paragraph(Text(
                    "The proof uses the positive constant norm(U) plus one. It applies also when "
                    + "U is zero or H is the zero space. Peterson's Lemma 2.7.1 supplies the "
                    + "classical monotone-net context; the displayed result identifies the limit "
                    + "with a specified operator-order least upper bound."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula App(Formula a, params Formula[] args) => new Formula.Apply(a, [.. args]);
    private static Formula Op(Formula h) => Call("ContinuousLinearMap", Seq(Mathbb, Grp(F.Id("C"))), h, h);
    private static Formula Instances(Formula h, Formula j) => Seq(
        OpenBracket, Call("NormedAddCommGroup", h), CloseBracket, Sp,
        OpenBracket, Call("InnerProductSpace", Seq(Mathbb, Grp(F.Id("C"))), h), CloseBracket, Sp,
        OpenBracket, Call("CompleteSpace", h), CloseBracket, Sp,
        OpenBracket, Call("Preorder", j), CloseBracket, Sp,
        OpenBracket, Call("Nonempty", j), CloseBracket, Sp,
        OpenBracket, Call("IsDirectedOrder", j), CloseBracket, Sp);

    private static Formula TheoremFormula()
    {
        Formula h = F.Id("H"), j = F.Id("J"), x = F.Id("X"), u = F.Id("U"),
            i = F.Id("i"), v = F.Id("v");
        Formula bound = All("i", j, Le(new Formula.Norm(App(x, i)), new Formula.Norm(u)));
        Formula pointwise = Seq(Open, i, Colon, Sp, j, Close, Sp, Mapsto, Sp, App(App(x, i), v));
        Formula strong = All("v", h, Call("Tendsto", pointwise, F.Id("atTop"), Call("nhds", App(u, v))));
        Formula body = Implies(All("i", j, Le(D(0), App(x, i))),
            Implies(Call("Monotone", x),
                Implies(Call("IsLUB", Call("range", x), u), And(bound, strong))));
        return Disp(All("H", Call("Type"), All("J", Call("Type"),
            Seq(Instances(h, j), All("X", Seq(j, Sp, To, Sp, Op(h)), All("U", Op(h), body))))));
    }
}
