using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Rows;

internal sealed class SeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separation", H("Separation"),
        Blocks(
            Paragraph(Text("The main result Data.eq_zero_of_integral_fNatural_tableTheta. Hodge–Tate jumps of the data lie in low or high windows. The three character pairs and the product of Hecke value ratios. Untwisted Hecke value is large against parallel weight, giving negative height. One twist-free form is a multiple, possibly zero here, of each twisted theta form, with L-value ratio. Level and holomorphic weight of the twist-free theta form.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Rows/Separation.eq_zero_of_integral_fNatural_tableTheta"),
                H("eq_zero_of_integral_fNatural_tableTheta"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For 1 ≤ j ≤ m, a good form F on U(W_j) vanishes if ∫ conj(F·F♮_i)·θo(ζ) = 0 over [U(W_j)] for all choices i and all ζ, where F♮ = Data.fNatural and θo = Data.tableTheta.")))))));
}
