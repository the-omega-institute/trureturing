using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class SolidGeneratorAugmentationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Copyright (c) 2026. Released under the Apache 2.0 license. The concrete generator augmentation used in unbounded realization: sums of the exact protected solidification(P) map epimorphically onto every solid object, and iteration on kernels produces an actual exact augmented resolution. This does not assume EnoughProjectives of LightCondAb, a derived adjunction, derived full faithfulness, or unbounded realization. Ambient P projectivity is reused from the immutable accepted CWComparison checkpoint; its source attribution is preserved in that supplier. Research: Juan Esteban Rodríguez Camargo, Notes on Solid Geometry, Theorem 3.3.1; the kernel resolution is Mathlib's proved LeftResolution API. The augmentation quasi-isomorphism proof adapts the degree-zero/positive degree argument of Mathlib/CategoryTheory/Abelian/Projective/Resolution.lean at 5e0c4e5239cb0a2d86d68a884bf52cfd963fce22, copyright (c) 2022 Jujian Zhang, authors Markus Himmel, Kim Morrison, Jakob von Raumer and Joël Riou, released under Apache 2.0.",
        H("Solid Generator Augmentation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-solidgeneratoraugmentation-solidp-isseparator"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/SolidGeneratorAugmentation.solidP_isSeparator"),
                H("solidP isSeparator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled statement supplies solidP isSeparator. The canonical augmentation is built by iterated kernels and proved exact; its cochain form is concentrated in nonpositive degrees."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-solidgeneratoraugmentation-solidgeneratorevaluation-epi"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/SolidGeneratorAugmentation.solidGeneratorEvaluation_epi"),
                H("solidGeneratorEvaluation epi"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled statement supplies solidGeneratorEvaluation epi. The canonical augmentation is built by iterated kernels and proved exact; its cochain form is concentrated in nonpositive degrees."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-solidgeneratoraugmentation-solidgeneratorcochainresolution-negative-term"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/SolidGeneratorAugmentation.solidGeneratorCochainResolution_negative_term"),
                H("solidGeneratorCochainResolution negative term"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled statement supplies solidGeneratorCochainResolution negative term. The canonical augmentation is built by iterated kernels and proved exact; its cochain form is concentrated in nonpositive degrees."))),
                DescribeRole.Theorem))));
}
