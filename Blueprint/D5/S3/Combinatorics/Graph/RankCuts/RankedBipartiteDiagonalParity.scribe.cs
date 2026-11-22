using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.RankCuts;

internal sealed class RankedBipartiteDiagonalParityDocument : IScribeDocumentDefinition
{
    private static Formula Statement()
    {
        var vertices = F.Id("V");
        var naturals = new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
        var source = F.Id("a");
        var target = F.Id("b");
        var exceptional = F.Id("t");
        var rank = F.Id("r");
        var sourceRank = Call("rho", source);
        var targetRank = Call("rho", target);
        var ordinaryEdge = Both(
            Relation(source, FormulaRelationOperator.NotEqual, exceptional),
            Relation(Call("e", source, target), FormulaRelationOperator.NotEqual, D(0)));
        var increases = All("a", vertices, All("b", vertices,
            Implies(ordinaryEdge, Logic(Equal(source, target), FormulaLogicOperator.Or,
                Relation(sourceRank, FormulaRelationOperator.LessThan, targetRank)))));
        var oddTotals = All("a", vertices, Implies(
            Relation(sourceRank, FormulaRelationOperator.LessThanOrEqual, rank),
            Both(Equal(Call("mod", Call("Row", source), D(2)), D(1)),
                Equal(Call("mod", Call("Col", source), D(2)), D(1)))));
        var hypotheses = Both(Call("Finite", vertices), Both(
            Relation(rank, FormulaRelationOperator.LessThan, Call("rho", exceptional)),
            Both(increases, oddTotals)));
        var diagonal = Call("Diag", rank);
        var sum = Add(Add(Call("LayerSize", rank), Call("Inflow", rank)), Call("Bypass", rank));
        var conclusion = Equal(Call("mod", diagonal, D(2)), Call("mod", sum, D(2)));
        return Disp(All("V", F.Id("Type"),
            All("rho", new Formula.TypeArrow(vertices, naturals),
                All("e", new Formula.TypeArrow(vertices, new Formula.TypeArrow(vertices, naturals)),
                    All("t", vertices, All("r", naturals, Implies(hypotheses, conclusion)))))));
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Relation(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);

    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), op, Seq(Open, right, Close));

    private static Formula Both(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.Implies, right);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compute the parity of the diagonal of each rank below an exceptional row.",
        H("Diagonal parity in ranked bipartite graphs"),
        Blocks(Describe.Lean(
            DescribeId.Create("ranked-bipartite-diagonal-parity"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/RankCuts/RankedBipartiteDiagonalParity.diagonal_parity"),
            H("Diagonal parity from an oriented rank cut"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Take two copies of a finite vertex set with natural-number ranks. "
                    + "Every ordered pair has a nonnegative integer edge multiplicity. Outside "
                    + "a designated left vertex, each positive entry is diagonal or goes to a "
                    + "strictly higher rank. Fix a rank r below the designated vertex. "
                    + "Every row and every column through rank r has odd total multiplicity.")),
                Paragraph(Text("Row and Col are the sums of all multiplicities in the given row "
                    + "and column, respectively. Diag is the sum of diagonal entries at rank r. LayerSize counts "
                    + "vertices at rank r. Inflow sums multiplicities from the designated row "
                    + "to columns of rank at most r. Bypass sums multiplicities from rows of "
                    + "rank strictly below r to columns of rank strictly above r.")),
                Paragraph(Text("The row and column sums through rank r have equal parity. Their "
                    + "internal entries cancel, so the outgoing sum has the parity of the "
                    + "incoming sum. Split the outgoing sum into entries from rank r and "
                    + "entries bypassing r. The rank-r rows contribute only their diagonal "
                    + "and outgoing entries. Their total has the parity of the layer size."))),
            DescribeRole.Theorem))));
}
