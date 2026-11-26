using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Unramified;

internal sealed class HeckeTransferDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hecke Transfer", H("Hecke Transfer"),
        Blocks(
            Paragraph(Text("Eichler commutation relation of Hecke polynomials through theta lifts at split places.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Unramified/HeckeTransfer.isSphericalWith_formLift"),
                H("isSphericalWith_formLift"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let w be split, ranks n of S, n + k of T, a, b unramified and f the vacuum at w, f an arrow e → e' (IsArrow). If y is spherical at w with Hecke eigenvalue p(X), so is its lift, with ∏_{l<k}(1 − q^{l+n/2}χ_S(w)X)·p(q^{k/2}χ_Sχ_T⁻¹(w)X).")))))));
}
