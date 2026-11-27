using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.TwistedHecke;

internal sealed class RootLemmaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Root Lemma", H("Root Lemma"),
        Blocks(
            Paragraph(Text("Root lemma: a term least in all frames obeys Frobenius inequalities; Gauss filtrations.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/TwistedHecke/RootLemma.root_lemma"),
                H("root_lemma"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Root lemma. Let a ≠ a', τ(a) = τ(a'), and c(u_s) − c(ū_s) ∈ [2/5, 8/5] for all s, with u_s, ū_s as in TwistingData.excessWeight. If all terms of all τ-Levi translates of f have w-order plus c-weight ≥ l + c·α and w^{l+1} ∤ f_α, then α has excess ≤ 0 at letter i.")))))));
}
