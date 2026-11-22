using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class PeriodicMPSUniformGuardedCriticalDimensionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformGuardedCriticalDimension";
    private const string Title = "Dimension under the guarded cofactor criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformguardedcriticaldimension-dimh-guarded-criticalcoordinates-le"),
                DeclarationHandle.Create(Module + ".dimH_guarded_criticalCoordinates_le"),
                H("Dimension under the guarded cofactor criterion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A nonzero cofactor ideal whose common irreducible divisors divide the guard gives Hausdorff dimension at most six on the nonzero mixed-trace and guard open."))),
                DescribeRole.Theorem))));
}
