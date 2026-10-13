using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Saturation;

internal sealed class MatchingConeLeafExistenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Saturation/MatchingConeLeafExistence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite maximal H-free graph of order at least twenty with at most order plus five edges has a vertex of degree one, for the cone H over three disjoint edges and an isolated vertex.",
        H("Leaf Existence in Sparse Matching-Cone-Saturated Graphs"),
        Blocks(Describe.Lean(DescribeId.Create("exists-degree-one"),
            DeclarationHandle.Create(Prefix + "exists_degree_one"), H("A Sparse Saturated Host Has a Leaf"),
            StatementSource.FromAuthor(TheoremFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "H is the existing eight-vertex graph MatchingConeLeafUniversality.H: its center "
                + "has seven required neighbors, its pendant has one, and each of the six matching "
                + "endpoints has two. Copies are injective adjacency-preserving maps, with extra "
                + "host edges allowed. Maximal H-freeness means that every missing edge creates "
                + "such a copy on the original vertex set.")),
                Paragraph(Text(
                "A new copy must use the added edge as a required edge. If an isolated vertex v "
                + "is joined to w, the degree bound in the enlarged graph forces v to occupy the "
                + "pendant role and w the center. The six matching endpoints give six distinct "
                + "old neighbors of w. This holds for every w other than v; the degree sum then "
                + "contradicts the order and edge bounds. Thus there are no isolated vertices.")),
                Paragraph(Text(
                "Suppose there is no leaf. Every vertex has degree at least two. Partition the "
                + "same original host into C, the vertices of degree at least six, and L, the "
                + "remaining vertices. The degree sum and edge bound give |C| <= 2 and "
                + "sum over C of degree <= 2|C|+10, while |L| >= 18. Each x in L has degree "
                + "at most five, so it has a distinct nonneighbor y in L. In a copy created by "
                + "xy, neither endpoint can be the center: each enlarged degree is at most six. "
                + "The center therefore has all seven required spokes in the old host, belongs "
                + "to C, and is adjacent to x. Hence L lies in the union of the old neighbor "
                + "sets of C. Counting that union by the sum of its set sizes gives "
                + "|L| <= sum over C of degree. Consequently the host order is at most "
                + "10+3|C| <= 16, a contradiction.")),
                Paragraph(Text(
                "The result preserves every finite original host, including disconnected and "
                + "nonextremal hosts. It assumes neither exact edge count, connectivity, a "
                + "universal vertex, nor an existing leaf. It is a structural implication, "
                + "not a saturation-number equality, a sharp order cutoff, or a resolution "
                + "of the general matching-cone problem. The finite role-degree calculations "
                + "are consumed inside this unbounded structural proof; utility is none. "
                + "The new inference is the saturation-forced old-host center incidence, "
                + "which is used in the final counting contradiction."))), DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula g = F.Id("G"), v = F.Id("v"), n = Call("FintypeCard", F.Id("V"));
        Formula hypotheses = And(Call("Maximal", Call("Free",
                F.Id("H")), g),
            And(Le(D(2, 0), n), Le(Call("card", Call("edgeFinset", g)), Add(n, D(5)))));
        Formula conclusion = new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("v"), F.Id("V"), Equal(Call("degree", g, v), D(1)));
        return Disp(All("V", Call("Type"), Seq(
            OpenBracket, Call("Fintype", F.Id("V")), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", F.Id("V")), CloseBracket, Sp,
            All("G", Call("SimpleGraph", F.Id("V")), Seq(
                OpenBracket, Call("DecidableRel", Call("Adj", g)), CloseBracket, Sp,
                Implies(hypotheses, conclusion))))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.And, Seq(Open, right, Close));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Implies, Seq(Open, right, Close));
}
