using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class FreeDetectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Free light-profinite generators detect morphisms and exactness. New proofs, released under the Apache 2.0 license.",
        H("Free Detect"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-freedetect-hom-eq-zero-of-free"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FreeDetect.hom_eq_zero_of_free"),
                H("hom eq zero of free"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Free light-profinite generators detect morphisms and exactness. New proofs, released under the Apache 2.0 license."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-freedetect-exact-of-free-boundaries"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FreeDetect.exact_of_free_boundaries"),
                H("exact of free boundaries"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Free light-profinite generators detect morphisms and exactness. New proofs, released under the Apache 2.0 license."))),
                DescribeRole.Theorem))));
}
