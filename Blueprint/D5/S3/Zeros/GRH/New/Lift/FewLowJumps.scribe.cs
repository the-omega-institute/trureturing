using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Lift;

internal sealed class FewLowJumpsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Few Low Jumps", H("Few Low Jumps"),
        Blocks(
            Paragraph(Text("Colength bound for constants lifting to deep points; cup products vanish on that submodule.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Lift/FewLowJumps.exists_scaledCupBounds_few_low_jumps"),
                H("exists_scaledCupBounds_few_low_jumps"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Few low jumps (unramified chart, p ≥ 5, window and gap hypotheses; n_i, r_i bound f times the low, all jumps at i): on a ℤ_p-submodule of C of colength ≤ 11Σ_i(n_i(a+1) + r_i(W+1)), α(d) ∪-pairs to a coboundary with every α'(c) of paired sides with opposite windows.")))))));
}
