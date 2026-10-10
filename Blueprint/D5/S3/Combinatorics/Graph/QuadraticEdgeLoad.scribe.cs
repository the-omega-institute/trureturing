using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class QuadraticEdgeLoadDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/QuadraticEdgeLoad.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The smallest possible maximum of the squared edge-share loads reaches one quarter "
        + "of the maximum degree exactly when a connected component has that constant degree.",
        H("Quadratic edge loads and regular components"),
        Blocks(
            Paragraph(Text(
                "Let G be a finite simple undirected graph with a nonempty vertex type V. "
                + "The coordinate a(b,c) denotes the share paid by b on the edge joining b and c. "
                + "Coordinates on nonedges are bounded extensions and never enter the loads. "
                + "Every allocation on oriented edges extends by assigning one half on nonedges; "
                + "restriction recovers the original allocation with identical loads.")),
            Describe.Lean(DescribeId.Create("feasible"), DeclarationHandle.Create(Prefix + "Feasible"),
                H("Actual feasible shares"), StatementSource.FromAuthor(FeasibleFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "All coordinates lie in the closed unit interval. Opposite shares add to one "
                    + "on every edge; no opposite-share equation is imposed on nonedges."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("load"), DeclarationHandle.Create(Prefix + "load"),
                H("Vertex load"), StatementSource.FromAuthor(LoadFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "A vertex pays the sum of the squares of its incident shares. "
                    + "An isolated vertex has load zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("maximum"), DeclarationHandle.Create(Prefix + "maxLoad"),
                H("Maximum load"), StatementSource.FromAuthor(MaximumFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The maximum ranges over all vertices, including isolated vertices."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("kappa"), DeclarationHandle.Create(Prefix + "kappa"),
                H("The optimization value"), StatementSource.FromAuthor(KappaFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Kappa is the infimum of actual maximum loads over feasible allocations. "
                    + "The following minimum-attainment statement identifies it with a minimum."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("minimum-attained"),
                DeclarationHandle.Create(Prefix + "minimum_attained"),
                H("An actual minimum"), StatementSource.FromAuthor(MinimumFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The feasible set is a closed subset of the finite product of closed unit "
                    + "intervals and contains the equal-share allocation. Each load is continuous, "
                    + "as is their finite maximum. Compact minimum attainment therefore applies."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("strict-allocation"),
                DeclarationHandle.Create(Prefix + "strict_allocation_of_no_regular_component"),
                H("A strict allocation without a regular component"),
                StatementSource.FromAuthor(StrictFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If no component is maximum-degree regular, every vertex can reach a vertex "
                    + "whose degree is smaller than the maximum D. Let l(b) be the shortest walk "
                    + "length to such a vertex. Adjacent levels differ by at most one, and every "
                    + "positive level has a neighbor one level lower. For j at least one, put "
                    + "epsilon(j) equal to one half times (1/(8D)) to the power j. "
                    + "On an edge from level j to level j minus one, the higher vertex pays "
                    + "one half minus epsilon(j), and the lower vertex pays one half plus epsilon(j). "
                    + "Equal levels pay one half. A positive-level vertex saves at least epsilon(j)/2 "
                    + "on a descending edge, while all increases together are at most epsilon(j)/4. "
                    + "A level-zero vertex has a missing degree unit; its total increase is at most "
                    + "one eighth. Every vertex load is consequently strictly below D/4."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("maximum-degree-equality"),
                DeclarationHandle.Create(Prefix + "maximum_degree_equality_iff"),
                H("The complete equality characterization"),
                StatementSource.FromAuthor(EqualityFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Equal shares give the universal upper bound D/4. In a D-regular component, "
                    + "the two squared shares on each edge sum to at least one half, so the average "
                    + "vertex load is at least D/4 for every feasible allocation. Conversely, the "
                    + "strict allocation above has a strict maximum because the vertex set is finite. "
                    + "The equivalence includes disconnected graphs and arbitrary isolated vertices. "
                    + "When D is zero, every component is an isolated zero-regular vertex and kappa "
                    + "is zero. No dual optimization identity is assumed."))), DescribeRole.Theorem))));

    private static Formula V() => F.Id("V");
    private static Formula G() => F.Id("G");
    private static Formula Real() => Call("Real");
    private static Formula Shares() => new Formula.TypeArrow(V(), new Formula.TypeArrow(V(), Real()));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula FiniteGraph(Formula body, bool nonempty = true) =>
        All("V", Call("Type"), Instance(Call("Fintype", V()),
            All("G", Call("SimpleGraph", V()), Instance(Call("DecidableRel", Call("Adj", G())),
                nonempty ? Instance(Call("Nonempty", V()), body) : body))));
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) =>
        new Formula.Relation(a, op, b);
    private static Formula Eq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Not(Formula a) => Seq(Neg, Sp, Open, a, Close);
    private static Formula DegreeBound() => new Formula.Fraction(Call("maxDegree", G()), D(4));
    private static Formula Feasible(Formula a) => Call("Feasible", G(), a);
    private static Formula Load(Formula a, Formula b) => Call("load", G(), a, b);
    private static Formula Maximum(Formula a) => Call("maxLoad", G(), a);
    private static Formula Kappa() => Call("kappa", G());
    private static Formula RegularComponent() => Some("C", Call("ConnectedComponent", G()),
        All("b", V(), Imp(Rel(F.Id("b"), FormulaRelationOperator.MemberOf, Call("supp", F.Id("C"))),
            Eq(Call("degree", G(), F.Id("b")), Call("maxDegree", G())))));

    private static Formula FeasibleFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c");
        Formula bounds = All("b", V(), All("c", V(),
            And(Rel(D(0), FormulaRelationOperator.LessThanOrEqual, App(a, b, c)),
                Rel(App(a, b, c), FormulaRelationOperator.LessThanOrEqual, D(1)))));
        Formula opposite = All("b", V(), All("c", V(), Imp(Call("Adj", G(), b, c),
            Eq(new Formula.Binary(App(a, b, c), FormulaBinaryOperator.Add, App(a, c, b)), D(1)))));
        return Disp(All("V", Call("Type"), All("G", Call("SimpleGraph", V()),
            All("a", Shares(), new Formula.Logic(Feasible(a), FormulaLogicOperator.Iff, And(bounds, opposite))))));
    }

    private static Formula LoadFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c");
        Formula sum = Seq(new Formula.Subscript(F.Sum,
            Seq(c, Sp, InMacro, Sp, Call("neighborFinset", G(), b))), Sp,
            new Formula.Power(App(a, b, c), D(2)));
        return Disp(FiniteGraph(All("a", Shares(), All("b", V(), Eq(Load(a, b), sum))), false));
    }

    private static Formula MaximumFormula() => Disp(FiniteGraph(All("a", Shares(),
        Eq(Maximum(F.Id("a")), Seq(new Formula.Subscript(F.Max, Seq(F.Id("b"), Sp, Colon, Sp, V())),
            Sp, Load(F.Id("a"), F.Id("b")))))));

    private static Formula KappaFormula()
    {
        Formula r = F.Id("r"), a = F.Id("a");
        Formula values = Seq(OpenBrace, r, Sp, Colon, Sp, Real(), Sp, Bar, Sp,
            Some("a", Shares(), And(Feasible(a), Eq(Maximum(a), r))), CloseBrace);
        return Disp(FiniteGraph(Eq(Kappa(), Call("sInf", values))));
    }

    private static Formula MinimumFormula() => Disp(FiniteGraph(Some("a", Shares(),
        And(Feasible(F.Id("a")), Eq(Maximum(F.Id("a")), Kappa())))));
    private static Formula StrictFormula() => Disp(FiniteGraph(Imp(Not(RegularComponent()),
        Some("a", Shares(), And(Feasible(F.Id("a")), All("b", V(),
            Rel(Load(F.Id("a"), F.Id("b")), FormulaRelationOperator.LessThan, DegreeBound())))))));
    private static Formula EqualityFormula() => Disp(FiniteGraph(new Formula.Logic(
        Eq(Kappa(), DegreeBound()), FormulaLogicOperator.Iff, RegularComponent())));
}
