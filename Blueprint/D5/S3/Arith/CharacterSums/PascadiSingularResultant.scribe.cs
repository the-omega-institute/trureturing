using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiSingularResultantDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integrated from the completed pinned singular-cover formalization. A common singular point with square value divisibility forces fourth-power divisibility of the actual Sylvester resultant. This is repository-derived mathematics supporting the Pascadi research problem; it is not a theorem attributed to Pascadi’s published paper.",
        H("Singular resultant divisibility"),
        Blocks(
            Paragraph(Text("Integrated from the completed pinned singular-cover formalization. A common singular point with square value divisibility forces fourth-power divisibility of the actual Sylvester resultant. This is repository-derived mathematics supporting the Pascadi research problem; it is not a theorem attributed to Pascadi’s published paper.")),
            Describe.Lean(DescribeId.Create("pascadi-pascadi-singular-resultant-singular-resultant-dvd-fourth"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiSingularResultant.singular_resultant_dvd_fourth"), H("singular_resultant_dvd_fourth"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A common singular root modulo a square forces fourth-power divisibility of the actual integer polynomial resultant. The divisor need not be prime, the degrees may be any integers at least two, and leading coefficients need not be units."))), DescribeRole.Theorem)),
        edges: []));
}
