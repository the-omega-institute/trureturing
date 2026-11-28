using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class ThickSpacingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Thick Spacing", H("Thick Spacing"),
        Blocks(
            Paragraph(Text("Spacing lemma: no three thick places (Data.thick) in a short Frobenius arc; thick embeddings have the same sign if ℓ divides Data.cycloConductor.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/ThickSpacing.cmSign_eq_of_thick"),
                H("cmSign_eq_of_thick"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let the prime ℓ divide N₁d and e embed E in Q̄_ℓ. If the complex embeddings complexEmbOf e g and complexEmbOf e g' (g, g' in G_ℓ) both define thick places, then both or neither belong to the CM type.")))))));
}
