using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class ReflectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "This module supplies the indicated step in the unbounded solidification construction.",
        H("Reflection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-reflection-issolid-iff-islocal"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/Reflection.isSolid_iff_isLocal"),
                H("is Solid iff is Local"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. This module supplies the indicated step in the unbounded solidification construction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-reflection-reflection-rightadjoint"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/Reflection.reflection_rightAdjoint"),
                H("reflection right Adjoint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Orthogonal reflection applies because the generating maps have finitely presentable domains and codomains."))),
                DescribeRole.Theorem))));
}
