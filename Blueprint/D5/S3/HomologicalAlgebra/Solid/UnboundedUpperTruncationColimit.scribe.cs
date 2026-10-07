using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class UnboundedUpperTruncationColimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Copyright (c) 2026. Released under the Apache 2.0 license. The actual increasing good upper truncations have every unrestricted cochain complex as their colimit. Together with the accepted lower truncation construction, this is the concrete double truncation step in unbounded generation. No realization equivalence or completeness premise is asserted. Research: Rodríguez Camargo, Notes on Solid Geometry, Theorem 3.3.1, unbounded extension by truncations and telescopes.",
        H("Unbounded Upper Truncation Colimit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-unboundeduppertruncationcolimit-uppertruncationdiagram-eventuallyconstant"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/UnboundedUpperTruncationColimit.upperTruncationDiagram_eventuallyConstant"),
                H("upperTruncationDiagram eventuallyConstant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled statement supplies upperTruncationDiagram eventuallyConstant. These eventual-constant component diagrams have the original arbitrary unbounded complex as their colimit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-unboundeduppertruncationcolimit-uppertruncationcocone-iscolimit"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/UnboundedUpperTruncationColimit.upperTruncationCocone_isColimit"),
                H("upperTruncationCocone isColimit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled statement supplies upperTruncationCocone isColimit. These eventual-constant component diagrams have the original arbitrary unbounded complex as their colimit."))),
                DescribeRole.Definition))));
}
