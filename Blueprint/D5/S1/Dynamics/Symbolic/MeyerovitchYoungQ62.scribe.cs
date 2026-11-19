using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class MeyerovitchYoungQ62Document : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ62.";
    private static readonly Formula Z = new Formula.Integers();
    private static readonly Formula N = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula R = Seq(Mathbb, Grp(F.Id("R")));
    private static readonly Formula B = F.Id("B");
    private static readonly Formula A = F.Id("A");
    private static readonly Formula Y = F.Id("Y");
    private static readonly Formula EquationShift = new Formula.Subscript(Y, F.Id("paper"));
    private static readonly Formula Configurations = new Formula.TypeArrow(Z, A);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two finite primitive multigraphs give a nonempty aperiodic and nonsofic Equation (19) payoff shift.",
        H("An Aperiodic Payoff Shift on Primitive Graphs"),
        Blocks(
            Paragraph(DefinitionDsl.Text(
                "Tom Meyerovitch and Aidan Young ask whether the shift in Equation (19) is always sofic "
                + "and whether it always has a periodic point for primitive graphs and real payoffs. "
                + "Question 6.2 is at https://arxiv.org/html/2603.21449v1#S6.Thmlemma2 "
                + "and Equation (19) is at https://arxiv.org/html/2603.21449v1#S5.E19.")),
            Paragraph(DefinitionDsl.Text(
                "Write B for Bool and A for the paired edge alphabet B × (B × B). The H graph has one "
                + "vertex and two distinct loop edges indexed by B. The G graph has vertices B and one "
                + "edge (s,t) from s to t for each ordered pair. With α = √2 − 1 and signs −1 for false "
                + "and +1 for true, the payoff on ((s,t),b) is the source sign times (b − α), with b "
                + "read as zero or one, plus a cost of two if s and t differ. This payoff is real-valued.")),
            Describe.Lean(
                DescribeId.Create("edge-endpoint-minimum"),
                DeclarationHandle.Create(Owner + "edgeMinimum_iff"),
                H("Attained minima at prescribed vertices"),
                StatementSource.FromAuthor(Disp(EdgeMinimum())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text(
                    "For every positive length and every binary H word, the minimum at each ordered pair of G "
                    + "vertices is attained among all legal G edge walks with those vertices as endpoints. "
                    + "The endpoint equivalence converts between these edge walks and the corresponding "
                    + "Boolean vertex sequences of length one greater."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-endpoint-window"),
                DeclarationHandle.Create(Owner + "equation19Window"),
                H("Nonimprovability and optimal response on a finite block"),
                StatementSource.FromAuthor(Disp(ActualEndpointWindow())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text(
                    "Hpart and Gpart are the edge projections of w. HBetween requires the competitor "
                    + "to run between the initial and final H vertices of Hpart(w). GBetween tests "
                    + "the actual initial and final vertices of Gpart(w) and every internal adjacency. "
                    + "In the two minima of the improvement test, c is the original minimum and d "
                    + "is the competing minimum. Both are attained. The response clause compares "
                    + "the actual cost of Gpart(w) with all legal walks at that same vertex pair."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("inclusive-equation"),
                DeclarationHandle.Create(Owner + "equation19"),
                H("The two-sided shift of Equation (19)"),
                StatementSource.FromAuthor(Disp(Equation())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text(
                    "The subscript paper denotes this shift. LegalH and LegalG impose the H and G adjacency equalities at every integer coordinate. "
                    + "The interval block W starts at m and has n − m + 1 letters, including both endpoints. "
                    + "The finite-window condition requires that no H walk of the same length and with the original "
                    + "H vertex endpoints strictly increases the attained minima at every ordered pair of G vertices. "
                    + "It also requires that the given G walk attain the minimum at its own vertex endpoints. "
                    + "This is the union over all ordered G vertex pairs in the definition of the response set."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("endpoint-window-equivalence"),
                DeclarationHandle.Create(Owner + "windowCondition_iff_equation19Window"),
                H("Window equivalence at the actual vertex endpoints"),
                StatementSource.FromAuthor(Disp(WindowEquivalence())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text(
                    "The optimized window condition computes both minima using vertex responses. "
                    + "The walk formulation uses attained minima over the actual edge paths. "
                    + "The comparison of H walks takes one competitor for all G endpoint pairs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equation-identification"),
                DeclarationHandle.Create(Owner + "shift_iff_equation19"),
                H("The length-indexed shift equals the shift of Equation (19)"),
                StatementSource.FromAuthor(Disp(All(F.Id("x"), Configurations,
                    IffOf(Member(F.Id("x"), Y), Member(F.Id("x"), EquationShift))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text(
                    "Y is the shift using optimized window conditions on W(x,i,n), the block of length n starting at i. "
                    + "Every inclusive interval with distinct endpoints gives a window of length at least two. "
                    + "Conversely the length-n window beginning at i occupies the inclusive interval from i "
                    + "through i + n − 1. The two window conditions agree by the attained-minimum identification."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("primitive-payoff-counterexample"),
                DeclarationHandle.Create(Owner + "result"),
                H("A nonempty shift with no periodic point and no finite edge presentation"),
                StatementSource.FromAuthor(Disp(Counterexample())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(DefinitionDsl.Text(
                        "AllPositiveLengths gives a walk at every positive length between any ordered vertex pair. "
                        + "For H both endpoint maps are hVertex, and for G they are the first and second projections. "
                        + "The cylinder condition is closedness in the product of the discrete paired edge alphabet. "
                        + "In the last clause V and E range over types in arbitrary universes with the displayed "
                        + "finiteness instances. The maps s and t are source and target, and l labels each edge by A.")),
                    Paragraph(DefinitionDsl.Text(
                        "A two-sided mechanical H word with the constant positive G loop satisfies all windows. "
                        + "Nonimprovability bounds the H discrepancy by seven on every allowed window. "
                        + "A positive period would multiply a nonzero irrational-slope discrepancy without bound. "
                        + "A nonempty finite presenting graph would supply a closed walk that repeats in both "
                        + "directions and gives a periodic point."))),
                DescribeRole.Theorem))));

    private static Formula EdgeMinimum()
    {
        var n = F.Id("n");
        var w = F.Id("w");
        var s = F.Id("s");
        var t = F.Id("t");
        var c = F.Id("c");
        var edgeMinimum = Apply("IsEdgeMinimum", n, w, s, t, c);
        var responseMinimum = Apply("endpointMinimum", Alpha, n, w, s, t);
        return All(n, N, ImpliesOf(Less(D(0), n),
            All(w, new Formula.TypeArrow(Apply("Fin", n), B), All(s, B, All(t, B, All(c, R,
                IffOf(edgeMinimum, Equal(c, responseMinimum))))))));
    }

    private static Formula ActualEndpointWindow()
    {
        var n = F.Id("n");
        var w = F.Id("w");
        var v = F.Id("v");
        var s = F.Id("s");
        var t = F.Id("t");
        var c = F.Id("c");
        var d = F.Id("d");
        var hWord = Apply("Hpart", w);
        var gWalk = Apply("Gpart", w);
        var allPairs = All(s, B, All(t, B, ExistsOf(c, R, ExistsOf(d, R,
            And(Apply("IsEdgeMinimum", n, hWord, s, t, c),
                And(Apply("IsEdgeMinimum", n, v, s, t, d), Less(c, d)))))));
        var improvement = ExistsOf(v, new Formula.TypeArrow(Apply("Fin", n), B),
            And(Apply("HBetween", hWord, v), Parens(allPairs)));
        var response = ExistsOf(s, B, ExistsOf(t, B,
            And(Apply("GBetween", gWalk, s, t),
                Apply("IsEdgeMinimum", n, hWord, s, t, Apply("edgeCost", hWord, gWalk)))));
        var block = new Formula.TypeArrow(Apply("Fin", n), A);
        return All(n, N, ImpliesOf(Less(D(0), n), All(w, block,
            IffOf(Apply("equationWindow", w), And(new Formula.Not(Parens(improvement)), Parens(response))))));
    }

    private static Formula Equation()
    {
        var x = F.Id("x");
        var m = F.Id("m");
        var n = F.Id("n");
        var length = Add(Subtract(n, m), D(1));
        var window = All(m, Z, All(n, Z, ImpliesOf(Less(m, n),
            Apply("equationWindow", Apply("W", x, m, length)))));
        return All(x, Configurations, IffOf(Member(x, EquationShift),
            And(Apply("LegalH", x), And(Apply("LegalG", x), window))));
    }

    private static Formula WindowEquivalence()
    {
        var n = F.Id("n");
        var w = F.Id("w");
        return All(n, N, ImpliesOf(Less(D(0), n),
            All(w, new Formula.TypeArrow(Apply("Fin", n), A),
                IffOf(Apply("windowCondition", w), Apply("equationWindow", w)))));
    }

    private static Formula Counterexample()
    {
        var x = F.Id("x");
        var y = F.Id("y");
        var k = F.Id("k");
        var i = F.Id("i");
        var n = F.Id("n");
        var p = F.Id("p");
        var v = F.Id("V");
        var e = F.Id("E");
        var s = F.Id("s");
        var t = F.Id("t");
        var l = F.Id("l");
        var q = F.Id("q");
        var translation = All(x, Configurations, All(k, Z,
            IffOf(Member(x, Y), Member(Seq(Open, LambdaLower, Sp, i, Comma, Sp,
                Apply("x", Add(k, i)), Close), Y))));
        var cylinders = All(x, Configurations, ImpliesOf(All(i, Z, All(n, N,
            ImpliesOf(AtMost(D(2), n), ExistsOf(y, Configurations,
                And(Member(y, Y), Equal(Apply("W", x, i, n), Apply("W", y, i, n))))))),
            Member(x, Y)));
        var nonempty = ExistsOf(x, Configurations, Member(x, Y));
        var noPeriod = new Formula.Not(Parens(ExistsOf(x, Configurations,
            And(Member(x, Y), ExistsOf(p, Z,
                And(Less(D(0), p), Apply("Periodic", x, p)))))));
        var adjacency = All(i, Z, Equal(Apply("t", Apply("q", i)), Apply("s", Apply("q", Add(i, D(1))))));
        var labels = All(i, Z, Equal(Apply("l", Apply("q", i)), Apply("x", i)));
        var saysPresented = All(x, Configurations, IffOf(Member(x, Y),
            ExistsOf(q, new Formula.TypeArrow(Z, e), And(Parens(adjacency), Parens(labels)))));
        var presentation = All(v, F.Id("Type"), All(e, F.Id("Type"),
            Seq(OpenBracket, Apply("Finite", v), CloseBracket, Sp,
                OpenBracket, Apply("Finite", e), CloseBracket, Comma, Sp,
                All(s, new Formula.TypeArrow(e, v), All(t, new Formula.TypeArrow(e, v),
                    All(l, new Formula.TypeArrow(e, A), new Formula.Not(Parens(saysPresented))))))));
        return new Formula.Aligned([
            And(Apply("AllPositiveLengths", F.Id("hVertex"), F.Id("hVertex")),
                Apply("AllPositiveLengths", F.Id("fst"), F.Id("snd"))),
            Seq(Land, Sp, Parens(translation)),
            Seq(Land, Sp, Parens(cylinders)),
            Seq(Land, Sp, Parens(nonempty)),
            Seq(Land, Sp, Parens(noPeriod)),
            Seq(Land, Sp, Parens(presentation))
        ]);
    }

    private static Formula Apply(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Parens(Formula value) => Seq(Open, value, Close);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Parens(Seq(variable, Colon, Sp, type)), Comma, Sp, body);
    private static Formula ExistsOf(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Parens(Seq(variable, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Member(Formula element, Formula set) => Seq(element, Sp, InMacro, Sp, set);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula ImpliesOf(Formula left, Formula right) =>
        new Formula.Logic(Parens(left), FormulaLogicOperator.Implies, Parens(right));
}
