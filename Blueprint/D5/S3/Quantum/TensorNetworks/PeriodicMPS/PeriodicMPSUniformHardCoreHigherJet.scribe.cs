using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSUniformHardCoreHigherJetDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreHigherJet";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact higher transfer coefficients at all lengths",
        H("Exact higher transfer coefficients at all lengths"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcorehigherjet-pathraw-coeff-eq"),
                DeclarationHandle.Create(Module + ".pathRaw_coeff_eq"),
                H("Checked transfer coefficients through degree four"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Along the polynomial hard-core chart paths, the coefficients of degrees two through four in seven raw marginal entries are polynomially weighted Fibonacci sequences at every length n ≥ 7. A Python calculation supplies the candidate weights. Lean verifies the sparse integer identities after clearing denominators at six, eight and ten consecutive lengths beginning at seven, respectively. The transfer recurrence extends the verified formulas to all later lengths."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcorehigherjet-forbiddencorner-coeff-four"),
                DeclarationHandle.Create(Module + ".forbiddenCorner_coeff_four"),
                H("The fourth coefficient of the raw 11,11 population"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The same identity gives the fourth raw coefficient at the forbidden 11,11 corner. The normalization and branch comparison are carried out in the subsequent jet calculation."))),
                DescribeRole.Theorem))));
}
