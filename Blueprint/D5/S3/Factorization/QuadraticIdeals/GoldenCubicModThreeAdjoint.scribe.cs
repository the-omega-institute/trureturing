using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class GoldenCubicModThreeAdjointDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Factorization/QuadraticIdeals/GoldenCubicModThreeAdjoint.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four explicit special-linear conjugations certify irreducibility of the mod-three adjoint module.",
        H("The four selected matrices have determinant one"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("wss-mod9-selected-sl"),
                DeclarationHandle.Create(Module + "selected_sl"),
                H("The four selected matrices have determinant one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The selected finite conjugations use actual two-by-two special-linear matrices."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-mod9-adjoint-no-invariants"),
                DeclarationHandle.Create(Module + "adjoint_no_invariants"),
                H("The elementary conjugations have no common nonzero fixed vector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The claim concerns every vector of the native trace-zero coordinate space over the field of three elements."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-mod9-adjoint-irreducible-of-invariant"),
                DeclarationHandle.Create(Module + "adjoint_irreducible_of_invariant"),
                H("The adjoint trace-zero module is irreducible"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every nonzero vector has two selected conjugates making a basis with it, so a submodule invariant under the four conjugations is all or zero."))),
                DescribeRole.Theorem))));
}
