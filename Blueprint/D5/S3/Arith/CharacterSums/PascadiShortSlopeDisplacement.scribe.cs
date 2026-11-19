using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiShortSlopeDisplacementDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite count for prime-square Pascadi word lifts in middle-slope coordinates.",
        H("Displacement count for short middle slopes"),
        Blocks(
            Describe.Lean(DescribeId.Create("pascadi-short-slope-word-count"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiShortSlopeDisplacement.short_slope_word_count"),
                H("Bound for prime-square word lifts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For each residue triple b in the cube of a finite set S, take a finite set of lift triples k. Their integer representatives are first coordinates of the form u*b_i+p*e*k_i with u and e units modulo p. Assume they solve the Pascadi word modulo p squared and their nonzero residue differences belong to a finite set D.")),
                    Paragraph(Text("The number of lifts is at most |S| cubed plus 3 times |D| times |S| squared. Subtracting the integer words and dividing by p gives a linear equation on a displacement. The lower word turns that equation into a cubic polynomial in b. Each nonzero displacement gives a nonzero polynomial, so Schwartz–Zippel bounds its base triples. Each nonempty fibre contributes one base lift and injects its other lifts into the allowed displacements."))),
                DescribeRole.Theorem))));
}
