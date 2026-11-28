using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.LocalDuality;

internal sealed class CrystallineDualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Crystalline Duality", H("Crystalline Duality"),
        Blocks(
            Paragraph(Text("Dual crystalline lattices have complementary cocycle counts; index form of the local duality inequality.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/LocalDuality/CrystallineDuality.relIndex_dvd_of_orthogonal"),
                H("relIndex_dvd_of_orthogonal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Local duality: L, L' potentially crystalline, perfectly paired by b into ℤ_ℓ(1), Γ → G_ℓ an open embedding, A the image of Z_f(L) in V = L/ℓ^m. If A and S consist of continuous cocycles whose cup products with H bound in ℚ̄_ℓ^×, then [S : S∩A] divides [Z_f(L') : H∩Z_f(L')].")))))));
}
