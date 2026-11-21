using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSUniformHardCoreJetGermDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreJetGerm";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized coefficient identities for physical polynomial paths",
        H("Normalized coefficient identities for physical polynomial paths"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcorejetgerm-opposite-polynomial-forbidden-expansion"),
                DeclarationHandle.Create(Module + ".opposite_polynomial_forbidden_expansion"),
                H("Fourth-order expansion of the physical forbidden corner"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The raw transfer and mass are polynomial on the chart paths. Their quotient has the coefficients of the formal series division because the witness mass is nonzero. At the opposite slope, matching the regular coefficients through degree three gives a physical 11,11 difference equal to quartic(n) times the fourth power of the path parameter plus a little-o remainder."))),
                DescribeRole.Theorem))));
}
