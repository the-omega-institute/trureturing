using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class UniformNativeCriticalMatrixDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/UniformNativeCriticalMatrix";
    private const string Title = "Native maximal minors of the two-site critical matrix";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("uniformnativecriticalmatrix"),
                DeclarationHandle.Create(Module + ".ordinaryMarginal_rank_eq_eight_iff_minor"),
                H("Rank eight detected by an exact native minor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On the positive mixed-trace slice and at nonzero trace-word amplitude, the normalized ordinary marginal has differential rank eight exactly when an evaluated maximal minor of the native matrix is nonzero."))),
                DescribeRole.Theorem))));
}
