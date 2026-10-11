using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class AugmentedKernelResolutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Copyright (c) 2026. Released under the Apache 2.0 license. The actual augmentation of Mathlib's successive-kernel left resolution is quasi-isomorphic to the input object. This supplies both the solid generator resolution and the ambient nonprojective free resolution. The resolution is constructed from the given natural epi data; no resolution-existence hypothesis is introduced. Mathlib construction: copyright (c) 2025 Joël Riou, Apache-2.0, commit 5e0c4e5239cb0a2d86d68a884bf52cfd963fce22.",
        H("Augmented Kernel Resolution"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-augmentedkernelresolution-kernelresolutionevaluation-exact"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/AugmentedKernelResolution.kernelResolutionEvaluation_exact"),
                H("kernelResolutionEvaluation exact"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled statement supplies kernelResolutionEvaluation exact. The canonical augmentation is built by iterated kernels and proved exact; its cochain form is concentrated in nonpositive degrees."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-augmentedkernelresolution-kernelresolutionevaluation-epi"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/AugmentedKernelResolution.kernelResolutionEvaluation_epi"),
                H("kernelResolutionEvaluation epi"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled statement supplies kernelResolutionEvaluation epi. The canonical augmentation is built by iterated kernels and proved exact; its cochain form is concentrated in nonpositive degrees."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-augmentedkernelresolution-kernelresolutioncochain-strictlyle"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/AugmentedKernelResolution.kernelResolutionCochain_strictlyLE"),
                H("kernelResolutionCochain strictlyLE"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled statement supplies kernelResolutionCochain strictlyLE. The canonical augmentation is built by iterated kernels and proved exact; its cochain form is concentrated in nonpositive degrees."))),
                DescribeRole.Theorem))));
}
