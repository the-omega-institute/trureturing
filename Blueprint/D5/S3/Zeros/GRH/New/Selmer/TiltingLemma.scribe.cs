using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class TiltingLemmaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tilting Lemma", H("Tilting Lemma"),
        Blocks(
            Paragraph(Text("Selmer groups cut by relations lie in Selmer groups with local conditions. Ties cost only determinants along twists; a group no new prime shortens is short. tilting: generic members of a pencil of linear maps have short kernels.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/TiltingLemma.tilting"),
                H("tilting"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Tilting. Let O/I be Artinian, Φ₀, Φ₁: B → (O/I)^m linear, Y ⊆ B a submodule. For all s off at most |m| residues, length(Y ∩ ker(sΦ₀ − Φ₁)) ≤ length(Y ∩ ker Φ₀ ∩ Φ₁⁻¹(Φ₀Y)).")))))));
}
