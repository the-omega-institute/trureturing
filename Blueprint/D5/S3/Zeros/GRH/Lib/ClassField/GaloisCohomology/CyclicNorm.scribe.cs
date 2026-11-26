using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.GaloisCohomology;

internal sealed class CyclicNormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclic Norm", H("Cyclic Norm"),
        Blocks(
            Paragraph(Text("Index of n-th powers in the multiplicative group of a local field. Tate's index formula for norms on stable subgroups in prime-degree Galois extensions. Classes split by a cyclic extension are symbols; symbols vanish exactly on norms.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/GaloisCohomology/CyclicNorm.cyclicClass_spec"),
                H("cyclicClass_spec"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let χ : Γ → ℚ/ℤ have open kernel U. A class in H²(Γ, Ω^×) restricts to zero on U exactly when it is a symbol (χ, w), w ∈ K^×; and (χ, w) = 0 exactly when w is a norm from the fixed field of U.")))))));
}
