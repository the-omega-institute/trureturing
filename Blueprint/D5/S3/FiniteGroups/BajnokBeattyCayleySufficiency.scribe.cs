using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class BajnokBeattyCayleySufficiencyDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/bajnokbeatty2025diameter");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform sufficient family of signed two-generator Cayley diameter bounds.",
        H("A skew lattice construction for the even-radius sufficiency direction"),
        Blocks(Describe.Lean(
            DescribeId.Create("uniform-signed-radius-sufficiency"),
            DeclarationHandle.Create("D5/S3/FiniteGroups/BajnokBeattyCayleySufficiency.result"),
            H("Distinct spanning pairs for k = 2(t² − j)"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "For every natural t ≥ 1 and 0 ≤ j < t, assume t is even or j is even. "
                    + "Put k = 2(t² − j). The group Z/2 × Z/(2k) contains distinct elements a,b "
                    + "such that every g equals x•a + y•b for integers x,y with |x| + |y| ≤ 2t. "
                    + "Thus the two-element generating set has undirected Cayley diameter at most 2t. "
                    + "The statement includes t=1,j=0 and extends past the top strip 0 ≤ 2j < t.")),
                Paragraph(Text(
                    "The covering mechanism is simultaneous remainder descent for the skew vectors "
                    + "(A,−b) and (−a,A), where A>0 and 0≤a,b<A. A positive multiple of their "
                    + "sum moves a coset representative into the nonnegative quadrant. A representative "
                    + "of least coordinate sum must lie in [0,A)², because subtracting a basis vector "
                    + "otherwise preserves nonnegativity and strictly reduces that sum. Applied after "
                    + "integer rotation to A=4t,a=4j,b=4, the square bound becomes a signed coefficient "
                    + "diamond of radius 2t. The endpoint uses integer division directly.")),
                Paragraph(Text(
                    "The lattice relations are twice (t−j,−t−j) and twice (t−1,t+1). "
                    + "Explicit surjective additive maps into Z/2 × Z/(4(t²−j)) annihilate both relations. "
                    + "For even t the coordinate change has determinant −1. For odd t and even j, "
                    + "d=t²−j is odd and a Bézout identity for 4 and d lifts every group element. "
                    + "The two coordinate images are distinct because their first coordinates sum to one "
                    + "in Z/2. Translation by the group identifies this signed coefficient ball with "
                    + "the same radius bound from every vertex.")),
                Paragraph(Text(
                    "This is partial sufficiency for Bajnok–Beatty Conjecture 4.1 in the checked "
                    + "arXiv v1 scope. General necessity, including exclusion of arbitrary alternative "
                    + "primitive lattices, remains open. No conclusion about the full conjecture or "
                    + "literature priority follows from the construction."))),
            DescribeRole.Theorem))));
}
