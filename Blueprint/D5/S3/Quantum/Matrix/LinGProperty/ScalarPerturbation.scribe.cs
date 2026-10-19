using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.LinGProperty;

internal sealed class ScalarPerturbationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Matrix/LinGProperty/ScalarPerturbation.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scalar perturbation of sorted singular values.",
        H("Scalar perturbation of sorted singular values"), Blocks(
            Describe.Lean(DescribeId.Create("lin-scalarperturbation-0"),
                DeclarationHandle.Create(Owner + "singularValuesSorted_add_scalar"),
                H("Scalar perturbation of sorted singular values"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/lin2016gproperty")),
                Blocks(Paragraph(Text("For every square complex matrix Y, scalar z and decreasing index j, s_j(Y+zI) is at most s_j(Y)+|z|. The spectral subspace of the perturbed Gram matrix meets the subspace where the original Gram form is small; the vector triangle inequality then bounds the selected singular value."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lin-scalarperturbation-1"),
                DeclarationHandle.Create(Owner + "eigenvalues_zero_add_scalar"),
                H("Real scalar shifts of a Hermitian spectrum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/lin2016gproperty")),
                Blocks(Paragraph(Text("Adding rI to a Hermitian matrix adds r to every decreasing eigenvalue. Two complementary spectral subspace comparisons prove both directions, including repeated eigenvalues."))),
                DescribeRole.Theorem))));
}
