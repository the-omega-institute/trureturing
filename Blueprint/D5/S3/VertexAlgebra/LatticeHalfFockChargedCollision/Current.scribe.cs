using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockChargedCollisionCurrentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Charged collision current moments.",
        H("Charged collision current moments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("charged-source-closed-recurrence"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Current.source_closed_recurrence"),
                H("The closed corrected-source recurrence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every signed exponent and actual tensor input, the corrected creation sequence obeys the closed current recurrence, with its one-half norm term and finite bilinear lower-order terms."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-collisionmoment"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Current.collisionMoment"),
                H("The finite normal-current moment"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The moment weights each finite creator diagonal by one half of the second creator degree minus the second translation degree, on the actual translated polynomial support."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("charged-collision-normal-moment"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Current.collision_normal_moment"),
                H("The arbitrary-input normal-current calculation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The normal current of collisionField on p tensor g equals the scalar-weighted collisionMoment tensor the actual ground action. The negative branch uses the creation differential equation; the nonnegative branch differentiates the full translated polynomial and counts repeated variables. All ranks and charges, including zero, remain in scope."))), DescribeRole.Theorem))));
}
