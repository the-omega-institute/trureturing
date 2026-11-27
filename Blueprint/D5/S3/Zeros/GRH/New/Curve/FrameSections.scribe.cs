using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Curve;

internal sealed class FrameSectionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Frame Sections", H("Frame Sections"),
        Blocks(
            Paragraph(Text("The jet series of a Weil vector is the Taylor series of its theta function. Curve theta products along tight frames: translates, jets, integral values, relation to the vacuum.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Curve/FrameSections.exists_finitePart_of_isTightFrame"),
                H("exists_finitePart_of_isTightFrame"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For V standard, (w, m) a tight frame of length M, δδ̄ = N ≠ 0, a ∈ Λ, area(C) = |a|²M√d/(2N): a product of degree-m_i monomials at (a/δ̄)w_i†z_k comes from some F ∈ 𝒲_f, compatibly with rational translations (theta values, Taylor series), integral-valued, with data Space.VacuumExpansion.")))))));
}
