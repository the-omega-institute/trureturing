using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds.ReferenceFrame;

internal sealed class ReferenceFrameTaxExactDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite exchange model has an exact fidelity bridge, sharp tax, restricted flat tax, and paired top eigenspace.",
        H("Exact Finite Reference-Frame Tax"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-finite-reference-frame-tax-is-exact"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumBounds/ReferenceFrame/ReferenceFrameTaxExact.reference_frame_tax_exact"),
                H("The finite reference-frame tax is exact"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The declaration packages the concrete exchange permutation, its "
                        + "conservation law, the finite Kraus representation, and both exact "
                        + "fidelity forms. It then applies the frozen sharp quadratic bound, "
                        + "the sine identity, the flat identity for ladders of length at least "
                        + "two, and the imported paired top-eigenspace characterization.")),
                    Paragraph(Text(
                        "The lower bound on the ladder length is explicit because the one-level "
                        + "flat calculation has tax one rather than the displayed three-halves "
                        + "formula."))),
                DescribeRole.Theorem))));
}
