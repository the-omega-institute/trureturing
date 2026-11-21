using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry.Ultrametric;

internal sealed class MCDWeakSimilarityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/Ultrametric/MCDWeakSimilarity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Topology/dovgosheyrovenska2026ultrametriccenter");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimum-order finite ultrametric spaces with equally many points are weakly similar, "
            + "and weak similarity preserves the number of central distances.",
        H("Weak similarity of minimum-order ultrametric spaces"),
        Blocks(
            Describe.Lean(DescribeId.Create("mcd-weakly-similar"),
                DeclarationHandle.Create(Prefix + "WeaklySimilar"),
                H("Weak similarity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A weak similarity of metric spaces X and Y is a bijection Φ : X → Y together "
                    + "with a function f, strictly increasing on the set of distances of Y, such "
                    + "that d(x, y) = f(ρ(Φ x, Φ y)) for all x and y (Dovgoshey and Rovenska, "
                    + "Definition 4.1)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mcd-weak-similarity-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Weak similarity and the center"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Two finite ultrametric spaces X and Y with |X| = 2^(|C(X)| - 1), "
                        + "|Y| = 2^(|C(Y)| - 1) and |X| = |Y| are weakly similar. Every weak "
                        + "similarity of metric spaces preserves the number of central distances. "
                        + "Hence, for finite ultrametric spaces with |X| = |Y| = 2^h and "
                        + "|C(X)| = h + 1, |C(Y)| = h + 1 exactly when X and Y are weakly similar. "
                        + "This is Conjecture 4.2 of O. Dovgoshey and O. Rovenska.")),
                    Paragraph(Text(
                        "On a minimum-order space every distance is central, and the two open "
                        + "balls below the diameter around points at the diameter are "
                        + "minimum-order halves with the lower center. Let g be the order "
                        + "isomorphism from C(Y) to C(X); it sends the diameter of Y to that of X "
                        + "and restricts to the lower centers, so by induction the halves of X and "
                        + "Y admit bijections carrying ρ to d through g, and these glue across the "
                        + "diameter. Conversely a weak similarity Φ, f maps C(Y) onto C(X) through "
                        + "f, which is injective on the distances of Y."))),
                DescribeRole.Theorem))));
}
