using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.LocalDuality;

internal sealed class RealPlaceSymbolsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real Place Symbols", H("Real Place Symbols"),
        Blocks(
            Paragraph(Text("Invariant map Br(k) ≅ Q/Z of a henselian local field and its functoriality. Number of Kummer cocycles; finiteness of local 1-cocycles of finite modules. The local Artin map sends uniformisers to geometric Frobenius elements. Order bound for orthogonal cocycle groups, the inequality for local Tate duality. Complex conjugations; symbol of a totally positive element dies keeping real places real.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/LocalDuality/RealPlaceSymbols.cycChar_eq_neg_one"),
                H("cycChar_eq_neg_one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If σ ∈ Γ acts as a complex conjugation on the algebraically closed field Ω of characteristic zero, then the ℓ-adic cyclotomic character takes the value −1 at σ.")))))));
}
