using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GLn.SchurModule;

internal sealed class HookDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hook", H("Hook"),
        Blocks(
            Paragraph(Text("Weights majorised by λ, extremal weights have multiplicity one, symmetric power case. Positivity and crude bound for Fischer norms of products of minors.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GLn/SchurModule/Hook.hookNumber_le"),
                H("hookNumber_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If Σ_τ Σ_{h<N_τ} h·κ_τ(h) ≤ L, then the hook number attached to κ and N is at most L^{3L}.")))))));
}
