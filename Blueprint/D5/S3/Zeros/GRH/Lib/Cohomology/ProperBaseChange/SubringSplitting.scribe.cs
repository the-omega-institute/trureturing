using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.ProperBaseChange;

internal sealed class SubringSplittingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Subring Splitting", H("Subring Splitting"),
        Blocks(
            Paragraph(Text("A non-valuation subring splits into two larger ones with exact Mayer-Vietoris sequence.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/ProperBaseChange/SubringSplitting.exists_split_mayer_vietoris"),
                H("exists_split_mayer_vietoris"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let K be algebraically closed, divisibility in D total, ℓ ∈ D^× prime, B in aicSubrings γ not a valuation ring of K. There are B₁, B₂ ⊋ B generating B₃, all in aicSubrings γ, such that every valuation ring of K containing B contains B₁ or B₂, and the Mayer–Vietoris sequence of locally constant ℤ/ℓ-valued functions on the spectra modulo γ(J) is short exact.")))))));
}
