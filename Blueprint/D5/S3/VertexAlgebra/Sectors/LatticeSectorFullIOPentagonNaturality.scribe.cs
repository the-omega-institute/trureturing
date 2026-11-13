using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorFullIOPentagonNaturalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Naturality of the finite FullIO pentagon", H("Naturality of the finite FullIO pentagon"), Blocks(
            Describe.Lean(
                DescribeId.Create("latticesectorfulliopentagonnaturality-short-path-natural"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/Sectors/LatticeSectorFullIOPentagonNaturality."
                        + "pentagonShortPath_natural"),
                H("Short-path naturality"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Postcomposition by every finite-target module morphism commutes with "
                        + "the short side of the explicit finite FullIO pentagon; the proof "
                        + "composes the two concrete channel naturality squares."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticesectorfulliopentagonnaturality-long-path-natural"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/Sectors/LatticeSectorFullIOPentagonNaturality."
                        + "pentagonLongPath_natural"),
                H("Long-path naturality"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The long side is natural in the finite target by transport across the "
                        + "concrete pentagon equality at both endpoints."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticesectorfulliopentagonnaturality-fullio-pentagon-natural"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/Sectors/LatticeSectorFullIOPentagonNaturality."
                        + "fullIO_pentagon_natural"),
                H("Pentagon naturality"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite-target pentagon identity is natural under every lawful "
                        + "target-module morphism."))),
                DescribeRole.Theorem))));
}
