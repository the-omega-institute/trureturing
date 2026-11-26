using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformVerticalPrimeExclusionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalPrimeExclusion";
    private const string Title = "Exclusion of noncoordinate divisors on paired sections";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformverticalprimeexclusion"),
                DeclarationHandle.Create(Module + ".no_noncoordinate_prime_of_sectionRankImplication"),
                H("Pairing obstructions rule out the section rank implication"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For m at least three, no irreducible divisor avoiding the trace sum and the root coordinate primes satisfies the simultaneous rank implication on the paired sections."))),
                DescribeRole.Theorem))));
}
