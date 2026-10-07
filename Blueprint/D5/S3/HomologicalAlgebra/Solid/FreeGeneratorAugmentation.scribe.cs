using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class FreeGeneratorAugmentationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Copyright (c) 2026. Released under the Apache 2.0 license. An actual augmented resolution by coproducts of free light-profinite objects. The evaluation is epimorphic by the proved free-generator morphism detection; ambient projectivity is neither asserted nor needed. Successive kernels give every negative cochain degree. This is the concrete ambient resolution used in unbounded derived-local realization. Research: Juan Esteban Rodríguez Camargo, Notes on Solid Geometry, Theorem 3.3.1. Kernel iteration reuses Mathlib's LeftResolution API, copyright (c) 2025 Joël Riou, Apache-2.0, at Mathlib 5e0c4e5239cb0a2d86d68a884bf52cfd963fce22.",
        H("Free Generator Augmentation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-freegeneratoraugmentation-freegeneratorevaluation-epi"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FreeGeneratorAugmentation.freeGeneratorEvaluation_epi"),
                H("freeGeneratorEvaluation epi"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled statement supplies freeGeneratorEvaluation epi. The canonical augmentation is built by iterated kernels and proved exact; its cochain form is concentrated in nonpositive degrees."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-freegeneratoraugmentation-freegeneratorcochainresolution-strictlyle"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FreeGeneratorAugmentation.freeGeneratorCochainResolution_strictlyLE"),
                H("freeGeneratorCochainResolution strictlyLE"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled statement supplies freeGeneratorCochainResolution strictlyLE. The canonical augmentation is built by iterated kernels and proved exact; its cochain form is concentrated in nonpositive degrees."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-freegeneratoraugmentation-freegeneratorcochainresolution-negative-term"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FreeGeneratorAugmentation.freeGeneratorCochainResolution_negative_term"),
                H("freeGeneratorCochainResolution negative term"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled statement supplies freeGeneratorCochainResolution negative term. The canonical augmentation is built by iterated kernels and proved exact; its cochain form is concentrated in nonpositive degrees."))),
                DescribeRole.Theorem))));
}
