using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Rows;

internal sealed class HeckeValueHeightDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hecke Value Height", H("Hecke Value Height"),
        Blocks(
            Paragraph(Text("Inverse ratio of twisted Hecke values has height repaying one direction; product version.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Rows/HeckeValueHeight.heightLe_inv_heckeValueProd_div"),
                H("heightLe_inv_heckeValueProd_div"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For m-fold twists θ(ι) satisfying Data.IsFitFamily and 1 ≤ j ≤ m, the numbers (Γ(θ(ι)^j)/Γ(1))⁻¹, Γ = Data.heckeValueProd, have height (HeightLe) at most 10m·x^999 + k(6B₀ − 𝖴), 𝖴 = Data.dirCost.")))))));
}
