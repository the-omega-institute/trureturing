using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ParityFourSparseCountsDocument : IScribeDocumentDefinition
{
    private static Formula Statement()
    {
        var k = F.Id("k");
        var i = F.Id("i");
        var counts = Call("FourAt", i);
        var equivalence = new Formula.Logic(Call("Realizable", D(2), k, counts),
            FormulaLogicOperator.Iff, Seq(D(2), Sp, Le, Sp, k));
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("k"),
            F.Id("Nat"), new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("i"),
                Call("Fin", D(4)), equivalence)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The budget threshold for exactly four fixed seeds concentrated at one coordinate.",
        H("Fixed seeds at a single coordinate in dimension four"),
        Blocks(Describe.Lean(
            DescribeId.Create("four-coordinate-single-fixed-count"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Attribution/ParityFourSparseCounts.exact_four_sparse"),
            H("The least multiplier is two"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("FourAt(i) has value four at i and zero at each other coordinate. "
                    + "Realizable(2,k,z) requires an equivariant seed action with 32k seeds, "
                    + "uniform coloured even and odd parity marginals, and fixed counts z.")),
                Paragraph(Text("At multiplier one the all-ones even word gives a cut that excludes "
                    + "the prescribed vector. At multiplier zero the seed set is empty. For two "
                    + "and three, two explicit integer tables specify the preimage multiplicities at each output point. "
                    + "They satisfy both coloured marginals and their odd entries supply exactly "
                    + "the required fixed seeds through the orbit fibre criterion.")),
                Paragraph(Text("At larger multipliers, adjoining an even block with zero fixed "
                    + "counts preserves the same vector. A permutation of the four coordinates "
                    + "moves the construction to any prescribed coordinate."))),
            DescribeRole.Theorem))));
}
