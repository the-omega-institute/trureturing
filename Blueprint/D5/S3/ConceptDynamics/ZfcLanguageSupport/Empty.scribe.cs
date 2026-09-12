using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ZfcLanguageSupport;

internal sealed class EmptyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/ZfcLanguageSupport/Empty.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/foundation2026firstorder");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every map from Empty equals its eliminator.",
        H("Empty"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("empty-map-elimination"),
                DeclarationHandle.Create(Prefix + "eq_elim"),
                H("Elimination of an empty domain"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Id("f"), F.Colon, F.Sp, new Formula.TypeArrow(Id("Empty"), F.Alpha), F.Comma, F.Sp, Id("f"), F.Eq, F.Sp, Id("elim")))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every target sort and every function from Empty to it, the function equals Empty.elim."))),
                DescribeRole.Theorem),
            Paragraph(Text("This equality supports empty-language elimination in the retained first-order semantics route. It does not construct a model or eliminate all CSA definitions.")),
            Paragraph(Text("Retained mathematical command: upstream line 9. The selected definitions and proofs retain Foundation revision 30a16ffa93d79d73ab4d02427fa00f50e039bf29. Attribution, the complete Apache-2.0 license and the replacement condition are in Library/ConceptDynamics/foundation2026firstorder.md.")))));
}
