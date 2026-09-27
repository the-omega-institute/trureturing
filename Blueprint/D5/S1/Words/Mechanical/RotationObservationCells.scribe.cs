using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class RotationObservationCellsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Mechanical/RotationObservationCells.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual rotation readouts determine half-open phase cells, sharp phase decoders, and a unique new split.",
        H("Rotation Observation Cells"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rotation-observation-prefix"),
                DeclarationHandle.Create(Prefix + "rotationPrefix"),
                H("Actual window observations"),
                StatementSource.FromAuthor(RotationPrefixFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The binary word evaluates the indicator of [1-alpha,1) on the actual fractional iterates x+k*alpha. This is an observable on phases, rather than an abstract supplied partition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rotation-observation-cell-decoder"),
                DeclarationHandle.Create(Prefix + "rotation_prefix_cell_and_decoder"),
                H("Exact fibers and all uniform decoders"),
                StatementSource.FromAuthor(CellAndDecoderFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every irrational slope in [0,1), every prefix length and every sorted rotation arc, the actual observation fiber of its left endpoint is exactly that half-open arc. Every center and radius valid on the observed word is then characterized by b-radius <= center <= a+radius. The proof identifies bits with the existing mechanical word, reconstructs cumulative floors, proves equivalence with every rotation-cut test, and only then uses the sorted-arc owner. The radius lower bound handles the excluded right endpoint by an interior contradiction. No cylinder estimate or phase-decoding guarantee is a premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rotation-observation-unique-split"),
                DeclarationHandle.Create(Prefix + "rotation_prefix_single_cut"),
                H("A unique cell is split by the next observation"),
                StatementSource.FromAuthor(SingleCutFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An additional actual bit adds exactly the threshold at fractional part -(n+1)*alpha to the old equality test. Irrationality proves this cut is absent from the old boundary set, so it lies strictly inside a unique old arc. Explicit phases on its two sides have equal old words and different extended words. Pairwise disjointness proves uniqueness; no list-refinement history is assumed. This establishes the geometric input needed for subsequent entropy and decision-risk consumers. Classical Sturmian complexity and the three-gap theorem are prior background, not claims of new discovery."))),
                DescribeRole.Theorem))));

    private static Formula RotationPrefixFormula()
    {
        var alpha = F.Id("alpha");
        var n = F.Id("n");
        var x = F.Id("x");
        var k = F.Id("k");
        var threshold = Subtract(D(1), alpha);
        var iterate = Add(x, Multiply(Call("val", k), alpha));
        var body = Call("decide", LessOrEqual(threshold, Call("fract", iterate)));
        var function = Seq(k, Colon, Sp, Fin(n), Sp, Mapsto, Sp, body);
        return Disp(All("alpha", Reals(), All("n", Naturals(), All("x", Reals(),
            Equal(ObservationPrefix(alpha, n, x), function)))));
    }

    private static Formula CellAndDecoderFormula()
    {
        var alpha = F.Id("alpha");
        var n = F.Id("n");
        var j = F.Id("j");
        var x = F.Id("x");
        var center = F.Id("center");
        var radius = F.Id("radius");
        var one = D(1);
        var size = Add(n, one);
        var a = Call("rotationCut", alpha, size, Call("castSucc", j));
        var b = Call("rotationCut", alpha, size, Call("succ", j));
        var unit = Ico(D(0), one);
        var sameWord = Equal(
            ObservationPrefix(alpha, n, x), ObservationPrefix(alpha, n, a));
        var fiber = Seq(OpenBrace, x, Sp, InMacro, Sp, Reals(), Sp, Mid, Sp,
            Parenthesized(And(Member(x, unit), sameWord)), CloseBrace);
        var exactCell = Equal(fiber, Ico(a, b));
        var pointBound = All("x", Reals(), Implies(Member(x, unit),
            Implies(sameWord,
                LessOrEqual(new Formula.Absolute(Subtract(x, center)), radius))));
        var decoder = All("center", Reals(), All("radius", Reals(),
            Iff(pointBound, And(
                LessOrEqual(Subtract(b, radius), center),
                LessOrEqual(center, Add(a, radius))))));
        var assumptions = And(
            Call("Irrational", alpha),
            And(LessOrEqual(D(0), alpha), Less(alpha, one)));
        return Disp(All("alpha", Reals(), Implies(assumptions,
            All("n", Naturals(), All("j", Fin(size), And(exactCell, decoder))))));
    }

    private static Formula SingleCutFormula()
    {
        var alpha = F.Id("alpha");
        var n = F.Id("n");
        var x = F.Id("x");
        var y = F.Id("y");
        var j = F.Id("j");
        var k = F.Id("k");
        var one = D(1);
        var size = Add(n, one);
        var unit = Ico(D(0), one);
        var beta = Call("fract", Multiply(size, new Formula.Negate(alpha)));
        var oldWords = Equal(
            ObservationPrefix(alpha, n, x), ObservationPrefix(alpha, n, y));
        var newWords = Equal(
            ObservationPrefix(alpha, size, x), ObservationPrefix(alpha, size, y));
        var thresholdSide = Iff(LessOrEqual(beta, x), LessOrEqual(beta, y));
        var stepLaw = All("x", Reals(), Implies(Member(x, unit),
            All("y", Reals(), Implies(Member(y, unit),
                Iff(newWords, And(oldWords, thresholdSide))))));

        Formula StrictContainment(Formula index)
        {
            var left = Call("rotationCut", alpha, size, Call("castSucc", index));
            var right = Call("rotationCut", alpha, size, Call("succ", index));
            return And(Less(left, beta), Less(beta, right));
        }

        Formula SplitWitness(Formula index)
        {
            var arc = Call("rotationGapArc", alpha, size, index);
            var phases = Exists("x", Reals(), Exists("y", Reals(), And(
                Member(x, arc),
                And(Member(y, arc),
                    And(Less(x, beta),
                        And(LessOrEqual(beta, y),
                            And(oldWords,
                                Not(Equal(
                                    ObservationPrefix(alpha, size, x),
                                    ObservationPrefix(alpha, size, y))))))))));
            return phases;
        }

        var uniqueCell = Exists("j", Fin(size), And(
            StrictContainment(j),
            And(All("k", Fin(size), Implies(StrictContainment(k), Equal(k, j))),
                SplitWitness(j))));
        var conclusion = And(stepLaw, uniqueCell);
        var assumptions = And(
            Call("Irrational", alpha),
            And(LessOrEqual(D(0), alpha), Less(alpha, one)));
        return Disp(All("alpha", Reals(), Implies(assumptions,
            All("n", Naturals(), conclusion))));
    }

    private static Formula ObservationPrefix(Formula alpha, Formula n, Formula x) =>
        Call("rotationPrefix", alpha, n, x);
    private static Formula Ico(Formula left, Formula right) => Call("Ico", left, right);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Exists(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Not(Formula value) => new Formula.Not(value);
}
