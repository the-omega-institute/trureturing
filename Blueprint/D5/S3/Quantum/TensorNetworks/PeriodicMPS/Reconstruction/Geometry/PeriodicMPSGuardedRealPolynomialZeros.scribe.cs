using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSGuardedRealPolynomialZerosDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSGuardedRealPolynomialZeros";
    private const string Title = "A guarded real common-zero cover";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsguardedrealpolynomialzeros-cover-guarded-real-common-zeros"),
                DeclarationHandle.Create(Module + ".cover_guarded_real_common_zeros"),
                H("A guarded real common-zero cover"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When a nonzero polynomial ideal has all its common irreducible divisors in the guard, its real common zeros off that guard admit a countable differentiable cover with three real inputs."))),
                DescribeRole.Theorem))));
}
