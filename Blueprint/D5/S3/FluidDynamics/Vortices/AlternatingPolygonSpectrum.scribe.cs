using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Vortices;

internal sealed class AlternatingPolygonSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Barry–Kevrekidis alternating vortex polygon field, Jacobian, and real spectrum claim.",
        H("Alternating Vortex Polygon Spectrum"),
        Blocks(
            Describe.Lean(DescribeId.Create("alternating-polygon-spectrum-charge"),
                DeclarationHandle.Create(Prefix + "charge"), H("Alternating charge"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Zero-based polygon labels represent the source's one-based labels."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("alternating-polygon-spectrum-field"),
                DeclarationHandle.Create(Prefix + "field"), H("Point-vortex field"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Cartesian field at b = 2 and Ω = 1/2."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("alternating-polygon-spectrum-polygon"),
                DeclarationHandle.Create(Prefix + "polygon"), H("Regular unit polygon"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The regular unit N-gon in cyclic order."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("alternating-polygon-spectrum-jacobian"),
                DeclarationHandle.Create(Prefix + "jacobian"), H("Cartesian Jacobian"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Partial derivatives of the field at the polygon."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("alternating-polygon-spectrum-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("Conjecture 4.4"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every m ≥ 3, nonzero real roots occur in opposite pairs and have cardinality 2(m−2)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("alternating-polygon-spectrum-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Conjecture 4.4 proved"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The named settlement theorem proves the claim."))),
                DescribeRole.Theorem))));
}
