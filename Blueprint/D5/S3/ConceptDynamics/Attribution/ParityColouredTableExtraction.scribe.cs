using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ParityColouredTableExtractionDocument : IScribeDocumentDefinition
{
    private static Formula Statement()
    {
        var d = F.Id("d");
        var k = F.Id("k");
        var z = F.Id("z");
        return Disp(new Formula.Logic(
            Call("EvenDimensionalSeedCounts", d, k, z), FormulaLogicOperator.Implies,
            Call("BoundedColouredTable", d, k, z)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Extract coloured parity multiplicities and coordinate bounds from one seed action.",
        H("Extract a coloured table from an even-dimensional seed action"),
        Blocks(Describe.Lean(
            DescribeId.Create("coloured-parity-table-extraction"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Attribution/ParityColouredTableExtraction.extract_coloured_subsets"),
            H("Coloured multiplicities under coordinate fixed-count bounds"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let d be even and at least two, let k be a natural number, and "
                    + "suppose a common equivariant action on k times 2 raised to the power "
                    + "(d + 1) seeds realizes the coordinate fixed-count vector z with uniform "
                    + "coloured marginals. There is a table of nonnegative integer multiplicities "
                    + "for an even subset, an odd subset, and a left colour.")),
                Paragraph(Text("Each even subset and left colour has marginal k. Each odd subset "
                    + "has marginal 2k after summing over even subsets and both left colours. "
                    + "The two left-colour entries coincide away from the full even subset. "
                    + "At every coordinate i, twice the sum of the entries modulo two over "
                    + "pairs of subsets both containing i and both left colours is at most z(i).")),
                Paragraph(Text("Right colours lie in the same output orbit for any fixed left "
                    + "colour. An ordinary even subset lets the action change the left colour "
                    + "independently. These orbit identities give the marginal equations for "
                    + "the table of fibre sizes. On a fixed output point, the coordinate-fixed "
                    + "seed count has the same parity as the fibre size. Summing the least "
                    + "compatible counts gives the bound."))),
            DescribeRole.Theorem))));
}
