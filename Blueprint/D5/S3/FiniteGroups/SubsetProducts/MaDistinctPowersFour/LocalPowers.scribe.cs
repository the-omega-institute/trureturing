using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour;

internal sealed class MaLocalPowersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Power separation within generator classes of size two, three or four.",
        H("Power separation within generator classes of size two, three or four"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ma-localpowers-zpowers-pow-of-bound"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LocalPowers.zpowers_pow_of_bound"),
                H("zpowers_pow_of_bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/ma2026distinctpowers")),
                Blocks(Paragraph(Text("Every allowed exponent is coprime to the element order and preserves its cyclic subgroup."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ma-localpowers-arrange-pair"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LocalPowers.arrange_pair"),
                H("arrange_pair"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/ma2026distinctpowers")),
                Blocks(Paragraph(Text("Both endpoint assignments failing would force the common element order to divide the difference of the squared exponents."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ma-localpowers-arrange-triple"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LocalPowers.arrange_triple"),
                H("arrange_triple"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/ma2026distinctpowers")),
                Blocks(Paragraph(Text("Three consecutive exponents are assigned by reducing to a prime dividing the generator order."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ma-localpowers-arrange-four"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LocalPowers.arrange_four"),
                H("arrange_four"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/ma2026distinctpowers")),
                Blocks(Paragraph(Text("Coordinates in the units modulo the common order transfer the modular four-block assignment to the original group."))),
                DescribeRole.Theorem))));
}
