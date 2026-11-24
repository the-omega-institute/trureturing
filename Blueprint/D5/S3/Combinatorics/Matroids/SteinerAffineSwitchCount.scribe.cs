using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class SteinerAffineSwitchCountDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/SteinerAffineSwitchCount";
    private static readonly LibraryNoteRef Extensions =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/falconefigulagalici2025veblenpoints");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact switch counts in binary extensions of affine ternary Steiner loops.",
        H("Affine Steiner Switch Counts"),
        Blocks(Describe.Lean(
            DescribeId.Create("steiner-affine-labelled-switch-count"),
            DeclarationHandle.Create(Module + ".labelledAffineSwitchCount"),
            H("Every affine pivot pair has the same switch count"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Extensions),
            Blocks(
                Paragraph(Text("Take a finite additive group V with x+x=-x for every x and more than three elements. Adjoin a new identity to V. Two different points x and y multiply to -x-y, and two equal points multiply to the new identity. Choose any triple labelling with values in a finite binary vector space A and form the normalized extension.")),
                Paragraph(Text("There is one numbering of the extension and one complete Steiner triple system for this labelling. Its centre is the fibre over the adjoined identity. For each ordered pair of distinct affine points p and q, delete the label of (p,0) and retain (q,0) as pivot. Using the actual matching of uncovered pairs, there are exactly |A|(|V|-3) successful starts.")),
                Paragraph(Text("Off the affine line through p and q the composite of the left translations is translation by q-p, so each such point has period three. On the line together with the identity the composite consists of two transpositions. Each two-step return uses the same triple twice after normalization, so its binary return row vanishes. The off-line calculation also supplies a witness to failure of associativity at each affine point and gives trivial centre in the quotient. Every off-line point contributes a full fibre to the count."))),
            DescribeRole.Theorem))));
}
