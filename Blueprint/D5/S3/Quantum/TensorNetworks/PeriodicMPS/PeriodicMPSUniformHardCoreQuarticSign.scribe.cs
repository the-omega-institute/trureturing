using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSUniformHardCoreQuarticSignDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreQuarticSign";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sign of the hard-core quartic coefficient",
        H("Sign of the hard-core quartic coefficient"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcorequarticsign-quartic-sign"),
                DeclarationHandle.Create(Module + ".quartic_sign"),
                H("Parity of the quartic coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For n ≥ 7 the displayed Fibonacci expression for the quartic has sign (−1)^(n−1). Bounds on consecutive Fibonacci ratios control the denominator and remaining factors, and Cassini's identity supplies the alternating factor. This makes the quartic nonzero at every admissible length."))),
                DescribeRole.Theorem))));
}
