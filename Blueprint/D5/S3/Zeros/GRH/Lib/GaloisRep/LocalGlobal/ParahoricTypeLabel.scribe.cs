using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.LocalGlobal;

internal sealed class ParahoricTypeLabelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parahoric Type Label", H("Parahoric Type Label"),
        Blocks(
            Paragraph(Text("Parahoric types and depth-zero labels; type implies label by Frobenius reciprocity.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/ParahoricTypeLabel.hasProductLabel"),
                H("hasProductLabel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Type implies label (Frobenius reciprocity): let c be a label of degree |ρ|, c' its roots scaled by x_ψ, the χ_l distinct, c'(x_{χ_l}) ≠ 0, and Σ conj(Ξ_c(x))F(x) ≠ 0. Then HasParahoricType gives HasProductLabel for c', the χ_l and the block sizes.")))))));
}
