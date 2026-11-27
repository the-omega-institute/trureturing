using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class FiniteCategoricalCoverCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Categorical cover certificates for finite posets",
        H("Categorical cover certificates for finite posets"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-categorical-cover-certificate"),
            DeclarationHandle.Create(
                "D5/S3/Topology/FiniteCategoricalCoverCertificate.hasCategoricalCover_of_tables"),
            H("Order tables and zigzags certify an ordinary categorical cover"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(
                "A finite order table and two lower sets carry explicit sequences of vertex maps. " +
                "Each sequence starts at the inclusion, ends at a constant, and consists of monotone maps with pointwise comparable neighbors. " +
                "The checked data give a categorical cover in the ordinary finite-space sense."))),
            DescribeRole.Theorem), Describe.Lean(
            DescribeId.Create("categorical-induced-subposet"),
            DeclarationHandle.Create(
                "D5/S3/Topology/FiniteCategoricalCoverCertificate.categorical_of_table"),
            H("A checked zigzag contracts the inclusion of an induced subposet"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(
                "The Boolean domain can be any vertex subset. The checked monotone maps give a contraction in the ambient finite poset. " +
                "Two such subsets covering the vertices supply the input for the subdivision transfer."))),
            DescribeRole.Theorem))));
}
