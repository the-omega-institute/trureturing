using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reflection;

internal sealed class QubitBlochReflectionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reflection/QubitBlochReflection";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A reflection selected by a degenerate Bloch Krylov matrix",
        H("A reflection selected by a degenerate Bloch Krylov matrix"),
        Blocks(
            Describe.Lean(DescribeId.Create("qubitblochreflection-exists-unit-eigenvector-of-krylov-det-zero"),
                DeclarationHandle.Create(Module + ".exists_unit_eigenvector_of_krylov_det_zero"),
                H("A reflection selected by a degenerate Bloch Krylov matrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When the Bloch matrix is symmetric and the three Krylov columns are dependent, their invariant span has a perpendicular unit eigenvector."))),
                DescribeRole.Theorem))));
}
