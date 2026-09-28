using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class FiniteSectorPhysicalConstructionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Entanglement/FiniteSectorPhysicalConstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite quantum channels and local dilations for the sector encoding.",
        H("Physical Sector Channel Construction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-sector-choi-kraus-stinespring"),
                DeclarationHandle.Create(Owner + "channel_kraus_stinespring"),
                H("Finite Kraus and Stinespring construction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every channel between finite matrix spaces, complete positivity makes "
                        + "the Choi matrix positive semidefinite. Its spectral decomposition supplies "
                        + "a finite Kraus family. Trace preservation forces the sum of the Kraus "
                        + "adjoint products to be the identity on the input.")),
                    Paragraph(Text(
                        "Stacking the Kraus family gives an isometry into a finite output and "
                        + "environment space. Partial trace over that environment equals the "
                        + "original channel on every input matrix, including off-diagonal units. "
                        + "The construction includes empty finite types where the channel exists. "
                        + "The Choi and Kraus argument adapts physlib revision "
                        + "6a09b2d1761a0d4430083045a247eb121d8da260 under Apache-2.0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-sector-physical-encoding"),
                DeclarationHandle.Create(Owner + "physical_encoding"),
                H("Physical encodings and residual splitter"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For positive sector ranks and normalized residual spectra, the prescribed "
                        + "source and flat target isometries induce actual quantum channels. "
                        + "Arbitrary local channel pairs have an actual product channel, and finite "
                        + "probability mixtures have an actual shared-classical channel. Each "
                        + "identity holds on every physical input matrix.")),
                    Paragraph(Text(
                        "The residual splitter traces out the spectral coordinate on both local "
                        + "systems. Its local output is the explicit partial trace on every input "
                        + "matrix. On encoded logical matrices, the joint channel multiplies each "
                        + "sector pair by the Gram overlap of the residual spectra before applying "
                        + "the flat target encoding."))),
                DescribeRole.Theorem))));
}
