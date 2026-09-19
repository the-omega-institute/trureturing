using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator.TranslationEnergy;

internal sealed class SourceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical translation partition.",
        H("Canonical translation partition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("source-cellat-gap-le-mesh"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/Source.cellAt_gap_le_mesh"),
                H("A mesh bound after inserting breakpoints"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a positive natural radius R, a rational shift s, and a natural depth d, the source points are the sorted distinct union of a relative dyadic mesh and the ten original and translated cutoff breakpoints. The support hull runs from min(-2R,s-2R) to max(2R,s+2R).")),
                    Paragraph(Text("If cellAt returns adjacent endpoints a and b, then a<b, both endpoints lie in the support hull, and b-a is at most the hull length divided by 2^d. If a gap were larger, the next mesh point obtained by a floor operation would lie strictly inside that gap, contradicting adjacency.")),
                    Paragraph(Text("The first and last points are the hull endpoints. The sourceCells list contains exactly the adjacent pairs, with one fewer cell than source points, and its list indices agree with cellAt."))),
                DescribeRole.Theorem)),
        []));
}
