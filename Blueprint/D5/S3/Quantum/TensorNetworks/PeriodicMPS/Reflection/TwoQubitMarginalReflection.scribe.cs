using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reflection;

internal sealed class TwoQubitMarginalReflectionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reflection/TwoQubitMarginalReflection";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A two-qubit marginal preserved by an antiunitary reflection",
        H("A two-qubit marginal preserved by an antiunitary reflection"),
        Blocks(
            Describe.Lean(DescribeId.Create("twoqubitmarginalreflection-exists-reflection-of-det-zero"),
                DeclarationHandle.Create(Module + ".exists_reflection_of_det_zero"),
                H("A two-qubit marginal preserved by an antiunitary reflection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an exchange-symmetric Hermitian two-qubit density whose Bloch Krylov determinant vanishes, a simultaneous single-qubit antiunitary leaves the marginal invariant."))),
                DescribeRole.Theorem))));
}
