using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class FiniteSectorPassivePairDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A passive correlated sector test bounds the overlap of every pair of actual local dilations.",
        H("Passive Sector-Pair Bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-sector-passive-pair"),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteSectorPassivePair.sector_pair"),
            H("Spectral prefix bound for two sectors"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Two isometric local dilations act on the same encoded source sector "
                    + "amplitude. Contracting their joint output against the flat target "
                    + "basis gives an environment matrix Z(s) for each sector s. For every "
                    + "sector pair s,t, the real Frobenius inner product of Z(s) and Z(t) "
                    + "is at most the Gram overlap of the two residual spectra.")),
                Paragraph(Text(
                    "The proof controls every singular-value prefix of Z(s) by the "
                    + "corresponding residual-spectrum prefix. It combines the rectangular "
                    + "variational bound with the source dilation's isometry and a trace "
                    + "majorization estimate. The same actual pair of dilations is used "
                    + "throughout; the result does not optimize the two sectors separately."))),
            DescribeRole.Theorem))));
}
