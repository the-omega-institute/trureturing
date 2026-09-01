using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class FiniteVandermondeTomographyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct finite phase nodes make the matching finite moment window a faithful observer.",
        H("Finite Vandermonde Tomography"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-moment-readout-injective"),
                DeclarationHandle.Create("D5/S3/Analytic/GoldenTomography/FiniteVandermondeTomography.finite_moment_readout_injective"),
                H("Distinct nodes give faithful finite moments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite family of pairwise distinct nodes over a field, the first matching number of power moments uniquely determines the hidden amplitude vector.")),
                    Paragraph(Text(
                        "The proof reuses Mathlib's Vandermonde determinant and determinant-kernel machinery. It asserts exact finite injectivity and leaves conditioning and infinite reconstruction outside its scope."))),
                DescribeRole.Theorem))));
}
