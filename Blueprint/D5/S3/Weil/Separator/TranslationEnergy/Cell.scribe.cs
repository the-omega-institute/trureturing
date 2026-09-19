using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator.TranslationEnergy;

internal sealed class CellDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pointwise literal energy enclosures.",
        H("Pointwise literal energy enclosures"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cell-checked-canonical-cell-normsq-encloses"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/Cell.checked_canonical_cell_normSq_encloses"),
                H("Every point of an accepted cell"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let R be a natural radius, p and q rational polynomials with supplied coefficient lists, and s a rational shift. A successful canonical cell check verifies the positive radius, the cell endpoints, four cutoff endpoint checks, exact even polynomial provenance and all signed expression bounds.")),
                    Paragraph(Text("For every real y in the returned closed cell, the annotated norm-square expression encloses the squared complex norm of H(y)-H(y-s), where H is smoothTransition(2-|y|/R) times the evenized complex polynomial p+i q. Endpoint and shifted cutoff intervals use the same exact scalar function."))),
                DescribeRole.Theorem)),
        []));
}
