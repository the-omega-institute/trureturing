using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class HammingWeakTwoMetricDimensionLowerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionLower.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Endpoint-degree constraints give a sharp lower bound for weak two-resolving landmark sets in rectangular Hamming graphs.",
        H("Reciprocal-degree charging for rectangular Hamming graphs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bipartite-degree-charging"),
                DeclarationHandle.Create(Prefix + "bipartite_degree_charging"),
                H("Two-thirds incidence bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let I and J be finite types with decidable equality and S a finite subset of I times J. Write g(i) and h(j) for the numbers of members of S incident with i and j. Suppose every g(i) and h(j) is positive, the total number of vertices is at least six, and any two edges with distinct row and column endpoints have total endpoint degree at least six. Then 2(|I|+|J|) is at most 3|S|.")),
                    Paragraph(Text("The sum over S of 1/g(i)+1/h(j) equals |I|+|J|: each vertex contributes one when its incident edges are summed. If no edge has both endpoint degrees equal to one, each edge contributes at most 3/2. If such an edge exists, its contribution is two, and every other edge is disjoint from it and has endpoint-degree sum at least four. Each remaining contribution is at most 4/3. Thus 3(|I|+|J|) is at most 4|S|+2; the hypothesis |I|+|J| at least six yields the same two-thirds bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rectangular-lower-bound"),
                DeclarationHandle.Create(Prefix + "lower_bound"),
                H("Lower bound for landmark cardinality"),
                StatementSource.FromAuthor(LowerFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every pair of natural numbers n and m with 4 <= n < m, every weak two-resolving landmark set S has cardinality at least min(ceil(2(n+m)/3),2n-2). Here natDiv(a,b) denotes natural number division, and the ceiling equals natDiv(2(n+m)+2,3). An empty row forces at least two landmarks in every other row. An empty column forces at least two landmarks in every other column. If every row and column is occupied, the disjoint-landmark degree constraint and reciprocal-degree charging give 3|S| >= 2(n+m)."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula LowerFormula()
    {
        var nat = new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
        var n = F.Id("n"); var m = F.Id("m"); var s = F.Id("S");
        var vertices = Call("Prod", Call("Fin", n), Call("Fin", m));
        var ceiling = Call("natDiv", Add(Mul(F.D(2), Add(n, m)), F.D(2)), F.D(3));
        var rowBound = new Formula.Binary(Mul(F.D(2), n), FormulaBinaryOperator.Subtract, F.D(2));
        var bound = new Formula.Relation(Call("min", ceiling, rowBound),
            FormulaRelationOperator.LessThanOrEqual, Call("card", s));
        return F.Disp(All("n", nat, All("m", nat, All("S", Call("Finset", vertices),
            Imp(Call("IsWeakResolving", F.D(2), s),
                Imp(new Formula.Relation(F.D(4), FormulaRelationOperator.LessThanOrEqual, n),
                    Imp(new Formula.Relation(n, FormulaRelationOperator.LessThan, m), bound)))))));
    }
}
