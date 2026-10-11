using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class LowerTruncationLayersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Copyright (c) 2026. Released under the Apache 2.0 license. The concrete one-term filtration of the verified brutal lower truncations. For arbitrary unbounded K, increasing the truncation cutoff by one fits into an actual short exact sequence with the newly added coefficient as its single-complex quotient. These are the finite cone steps used with the actual generator resolution and the two unbounded telescopes. Research: Rodríguez Camargo, Notes on Solid Geometry, Theorem 3.3.1.",
        H("Lower Truncation Layers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-lowertruncationlayers-lowertruncationlayerprojection"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/LowerTruncationLayers.lowerTruncationLayerProjection"),
                H("lower Truncation Layer Projection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Project the newly added bottom coefficient onto its literal stalk."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("solid-lowertruncationlayers-lowertruncationlayersequence"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/LowerTruncationLayers.lowerTruncationLayerSequence"),
                H("lower Truncation Layer Sequence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Copyright (c) 2026. Released under the Apache 2.0 license. The concrete one-term filtration of the verified brutal lower truncations. For arbitrary unbounded K, increasing the truncation cutoff by one fits into an actual short exact sequence with the newly added coefficient as its single-complex quotient. These are the finite cone steps used with the actual generator resolution and the two unbounded telescopes. Research: Rodríguez Camargo, Notes on Solid Geometry, Theorem 3.3.1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("solid-lowertruncationlayers-lowertruncationlayersequence-shortexact"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/LowerTruncationLayers.lowerTruncationLayerSequence_shortExact"),
                H("lower Truncation Layer Sequence short Exact"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The filtration is short exact on all integer coefficients, including the zero coefficients below the cutoff. No boundedness of K is used."))),
                DescribeRole.Theorem))));
}
