using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.ProperBaseChange;

internal sealed class KummerLineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kummer Line", H("Kummer Line"),
        Blocks(
            Paragraph(Text("Mayer-Vietoris for locally constant functions on two rings with a common localisation.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/ProperBaseChange/KummerLine.exists_noetherian_fg_filtration"),
                H("exists_noetherian_fg_filtration"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let D = B[1/t] = C[1/s], ts = 1, be a ring integral over A[t,s]. For finite G ⊂ D there are a subring R ⊂ A and a Noetherian R-submodule Y ⊃ G ∪ {1} such that each n has R-submodules P ⊂ im B, Q ⊂ im C and finitely generated M with Yⁿ, PQ ⊂ M ⊂ P+Q+Y.")))))));
}
