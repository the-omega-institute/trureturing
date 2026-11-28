using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EntanglementBreaking;

internal sealed class RightIsometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A right isometric factorization through a prescribed finite dimension.",
        H("Right isometric factorization"),
        Blocks(
            Describe.Lean(DescribeId.Create("eb-rightisometry-exists-right-isometry-factorization"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/RightIsometry.exists_right_isometry_factorization"),
                H("Rectangular right isometric factorization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Factor a k by d complex matrix through the adjoint of an isometry from dimension k into dimension d when k is at most d. Extend an orthonormal basis of the range of its adjoint to obtain the isometry."))),
                DescribeRole.Theorem))));
}
