using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class RankedBipartiteDiagonalParityDocument : IScribeDocumentDefinition
{
    private static Formula Statement()
    {
        var rank = F.Id("r");
        var diagonal = Call("Diag", rank);
        var sum = Add(Add(Call("LayerSize", rank), Call("Inflow", rank)), Call("Bypass", rank));
        return Disp(Equal(Call("mod", diagonal, D(2)), Call("mod", sum, D(2))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compute the parity of the diagonal of each rank below an exceptional row.",
        H("Diagonal parity in ranked bipartite graphs"),
        Blocks(Describe.Lean(
            DescribeId.Create("ranked-bipartite-diagonal-parity"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/RankedBipartiteDiagonalParity.diagonal_parity"),
            H("Diagonal parity from an oriented rank cut"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Take two copies of a finite vertex set with natural-number ranks. "
                    + "Every ordered pair has a nonnegative integer edge multiplicity. Outside "
                    + "a designated left vertex, each positive entry is diagonal or goes to a "
                    + "strictly higher rank. Fix a rank r below the designated vertex. "
                    + "Every row and every column through rank r has odd total multiplicity.")),
                Paragraph(Text("Diag is the sum of diagonal entries at rank r. LayerSize counts "
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
