using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Fourier;

internal sealed class ReversalWaveSynthesisDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Fourier/ReversalWaveSynthesis.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reversal witness coefficients synthesize the stated smooth divergence-free real cosine fields.",
        H("Reversal Wave Synthesis"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reversal-wave-synthesis-character"),
                DeclarationHandle.Create(Prefix + "character"),
                H("character"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The character exp(i*k.x), written in real sine/cosine coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reversal-wave-synthesis-synthesis"),
                DeclarationHandle.Create(Prefix + "synthesis"),
                H("synthesis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Literal finite synthesis using the same four frequencies and coefficients."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reversal-wave-synthesis-realvelocity"),
                DeclarationHandle.Create(Prefix + "realVelocity"),
                H("realVelocity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual smooth velocity field, independent of the third coordinate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reversal-wave-synthesis-synthesis-eq-realvelocity"),
                DeclarationHandle.Create(Prefix + "synthesis_eq_realVelocity"),
                H("synthesis eq realVelocity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite Fourier data is exactly the advertised real cosine field."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reversal-wave-synthesis-realvelocity-contdiff"),
                DeclarationHandle.Create(Prefix + "realVelocity_contDiff"),
                H("realVelocity contDiff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both active spatial coordinates are jointly smooth to every finite order."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reversal-wave-synthesis-realvelocity-periodic"),
                DeclarationHandle.Create(Prefix + "realVelocity_periodic"),
                H("realVelocity periodic"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal field has the correct 2*pi period in each active coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reversal-wave-synthesis-realvelocity-divergence"),
                DeclarationHandle.Create(Prefix + "realVelocity_divergence"),
                H("realVelocity divergence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Ordinary coordinate derivatives give zero divergence; no symbolic 'divergence-free' label is used as a premise."))),
                DescribeRole.Theorem))));
}
