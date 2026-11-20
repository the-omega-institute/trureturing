using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class GanTanHuangConjecture17RefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/GanTanHuangConjecture17Refutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/gantanhuang2026extremalcycles");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six clique vertices with three private leaves each meet the proposed degree threshold at d = k = 8.",
        H("A counterexample to Gan, Tan and Huang's Conjecture 1.7"),
        Blocks(
            Describe.Lean(DescribeId.Create("conjecture-seventeen"), DeclarationHandle.Create(Prefix + "claim"),
                H("Conjecture 1.7"), StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("The vertex type V carries a Fintype instance. The vertex count n is its "
                        + "cardinality, and Mathlib's SimpleGraph encodes the finite simple undirected graph "
                        + "on V. The source's high-degree count is the cardinality of the set of vertices "
                        + "whose neighbor set has at least d elements. Fin k consists of the indices "
                        + "0 through k−1, so castSucc embeds each index into Fin(k+1) with the same value "
                        + "and succ embeds it at the next value. The injective sequence has exactly k+1 vertices.")),
                    Paragraph(Text("The floor q is evaluated by dividing k−3 in the integers by positive 4. "
                        + "All arithmetic in the threshold after that floor, including n−1 and d−1, "
                        + "is rational. The positive source domain gives d > 0 and q ≥ −1. "
                        + "At d = 1 we have k = 1 and q + d(d−1) = −1. "
                        + "For d ≥ 2 the product d(d−1) is at least 2, so q + d(d−1) ≥ 1."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("conjecture-seventeen-refuted"), DeclarationHandle.Create(Prefix + "result"),
                H("A clique with private leaves"), StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The vertices are the disjoint sum of Fin 6 and Fin 6 × Fin 3. The first "
                        + "summand forms a clique, and each vertex (i,j) of the second summand is adjacent "
                        + "only to clique vertex i. Every vertex reaches core vertex 0, through its own "
                        + "core vertex if it is a leaf. There are 24 vertices. The six core vertices "
                        + "have degree 8 and the 18 leaves have degree 1. At d = k = 8 the floor is 1, "
                        + "the second denominator is 57, and the threshold is 298/57, below 6 by 44/57.")),
                    Paragraph(Text("In a hypothetical nine-vertex path, injectivity makes the predecessor "
                        + "and successor of each interior vertex distinct. A leaf has a single neighbor, "
                        + "so all seven interior vertices must be core vertices. Their distinct core "
                        + "labels would give an injection from Fin 7 into Fin 6. "
                        + "Mathlib's finite-cardinality bound for injections rules this out."))),
                DescribeRole.Theorem))));

    private static Formula Named(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    private static Formula Par(Formula expression) => Seq(Open, expression, Close);

    private static Formula Typed(Formula expression, Formula type) =>
        Par(Seq(expression, Sp, Colon, Sp, type));

    private static Formula Bind(Formula quantifier, Formula variable, Formula type, Formula body) =>
        Seq(quantifier, Sp, Typed(variable, type), Comma, Sp, body);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula ImpliesTo(Formula premise, Formula conclusion) =>
        new Formula.Logic(Par(premise), FormulaLogicOperator.Implies, Par(conclusion));

    private static Formula ClaimFormula()
    {
        var vertices = F.Id("V");
        var graph = F.Id("G");
        var k = F.Id("k");
        var d = F.Id("d");
        var path = F.Id("p");
        var i = F.Id("i");
        var v = F.Id("v");
        var naturals = Seq(Mathbb, Grp(F.Id("N")));
        var integers = Seq(Mathbb, Grp(F.Id("Z")));
        var rationals = Seq(Mathbb, Grp(F.Id("Q")));
        var n = Named("card", vertices);
        var q = Typed(new Formula.Floor(new Formula.Fraction(Subtract(Typed(k, integers), D(3)), D(4))),
            rationals);
        var rationalDegree = Typed(d, rationals);
        var countMinusOne = Subtract(Typed(n, rationals), D(1));
        var denominator = Add(q, Multiply(rationalDegree, Subtract(rationalDegree, D(1))));
        var threshold = Add(Add(new Formula.Fraction(Multiply(q, countMinusOne), rationalDegree),
            Multiply(Subtract(D(1), new Formula.Fraction(q, rationalDegree)),
                new Formula.Fraction(Multiply(countMinusOne, q), denominator))), D(2));

        var highVertices = Seq(OpenBrace, v, Sp, Mid, Sp,
            Le(d, Named("ncard", Named("neighborSet", graph, v))), CloseBrace);
        var highCount = Typed(Named("ncard", highVertices), rationals);
        var pathType = Seq(Named("Fin", Add(k, D(1))), Sp, To, Sp, vertices);
        var consecutive = Bind(Forall, i, Named("Fin", k),
            Named("Adj", graph, Named("p", Named("castSucc", i)), Named("p", Named("succ", i))));
        var conclusion = Bind(Exists, path, pathType,
            new Formula.Logic(Named("Injective", path), FormulaLogicOperator.And, Par(consecutive)));
        var body = ImpliesTo(Lt(D(0), k), ImpliesTo(Le(k, d), ImpliesTo(Lt(d, n),
            ImpliesTo(Named("Connected", graph), ImpliesTo(Le(threshold, highCount), conclusion)))));
        var graphBinder = Bind(Forall, graph, Named("SimpleGraph", vertices),
            Bind(Forall, d, naturals, Bind(Forall, k, naturals, body)));
        var instance = Seq(OpenBracket, Named("Fintype", vertices), CloseBracket, Comma, Sp, graphBinder);
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            Par(Bind(Forall, vertices, F.Id("Type"), instance))));
    }
}
