using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class UnboundedTruncationColimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Copyright (c) 2026. Released under Apache 2.0. The actual increasing brutal lower truncations of every unbounded cochain complex have that complex as their colimit. Each fixed coefficient is eventually the original coefficient with identity transition. This is the concrete first telescope input for unbounded realization, not a hypothesis postulating generation or a realization equivalence. Research: Juan Esteban Rodríguez Camargo, Notes on Solid Geometry, Theorem 3.3.1, unbounded extension by truncations.",
        H("Unbounded Truncation Colimit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-unboundedtruncationcolimit-lowertruncationcocone"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/UnboundedTruncationColimit.lowerTruncationCocone"),
                H("lower Truncation Cocone"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Copyright (c) 2026. Released under Apache 2.0. The actual increasing brutal lower truncations of every unbounded cochain complex have that complex as their colimit. Each fixed coefficient is eventually the original coefficient with identity transition. This is the concrete first telescope input for unbounded realization, not a hypothesis postulating generation or a realization equivalence. Research: Juan Esteban Rodríguez Camargo, Notes on Solid Geometry, Theorem 3.3.1, unbounded extension by truncations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("solid-unboundedtruncationcolimit-lowertruncationdiagram-eventuallyconstant"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/UnboundedTruncationColimit.lowerTruncationDiagram_eventuallyConstant"),
                H("lower Truncation Diagram eventually Constant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each coefficient of this specific unbounded diagram stabilizes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-unboundedtruncationcolimit-lowertruncationcocone-iscolimit"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/UnboundedTruncationColimit.lowerTruncationCocone_isColimit"),
                H("lower Truncation Cocone is Colimit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every arbitrary unbounded complex is the actual colimit of its bounded-below lower truncations. No completeness premise is used."))),
                DescribeRole.Definition))));
}
