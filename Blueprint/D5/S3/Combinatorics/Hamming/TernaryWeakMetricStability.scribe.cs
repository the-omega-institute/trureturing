using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hamming;

internal sealed class TernaryWeakMetricStabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.";
    private static readonly LibraryNoteRef Kumar =
        LibraryNoteRef.Create("D5/L/Hamming/kumar2026weakmetric");
    private static readonly LibraryNoteRef Boundary =
        LibraryNoteRef.Create("D5/L/Hamming/fernandezetal2025weakmetric");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ternary near-maximum weak metric dimensions at deficits four and five stabilize exactly in dimension three.",
        H("The least ternary stabilization threshold at deficits four and five"),
        Blocks(
            Paragraph(Text("Kumar's Theorem 6.4 proves an eventual formula for every nonbinary alphabet, "
                + "with a sufficient dimension inequality. The present result fixes the ternary alphabet "
                + "and deficits four and five and determines every dimension at least two. Its least "
                + "threshold concerns these two deficits only. The published two-dimensional values "
                + "of Fernandez, Klavzar, Kuziak, Munoz-Marquez and Yero are used to establish leastness.")),
            Definition("word", "Ternary words", "Word",
                "Word d is the literal finite function type Fin d to Fin 3. A landmark or omitted set is a Finset of distinct words."),
            Definition("distance", "Hamming distance", "distance",
                "The distance sums one over the coordinates where two words differ, and zero elsewhere."),
            Theorem("native-distance", "Agreement with the native metric", "distance_eq_hammingDist",
                "For every dimension and both words, distance equals Mathlib's native hammingDist."),
            Definition("separation", "Weak separation", "separation",
                "For a finite set T and words x,y, separation T x y sums Nat.dist(distance x z, distance y z) over z in T. This is the sum of absolute differences of distances."),
            Definition("resolving", "Weak resolving sets", "IsWeakResolving",
                "For every ordered pair of distinct words, the separation is at least k. No pair is omitted from this quantifier."),
            Definition("dimension", "Weak metric dimension", "metricDimension",
                "The natural infimum of the cardinalities of weak k-resolving Finsets. The construction in the theorem proves that this collection is nonempty at each requested parameter."),
            Definition("kappa", "The maximum parameter", "kappa",
                "kappa d is 2 times 3 to the power d minus one; it is the full-universe separation of an adjacent pair."),
            Definition("capacity", "The eventual omitted capacity", "omittedCapacity",
                "omittedCapacity t is 3 times the natural quotient t/2 plus t mod 2, so its values at four and five are six and seven."),
            Definition("complement", "Complement in the actual universe", "complement",
                "complement T is univ minus T in the finite type Word d."),
            Theorem("complement-card", "Cardinalities of complementary sets", "complement_card",
                "For every dimension and omitted set T, the cardinalities of T and its complement sum to 3 to the power d."),
            Theorem("complement-separation", "Separation splits over complements", "separation_complement",
                "For every dimension, finite set T, and words x,y, the separation over T plus that over its complement equals the separation over all words."),
            Theorem("uniform-bound", "The uniform separation gain", "full_separation_bound",
                "For every d at least three and every distinct x,y, the full-universe separation is at least kappa d plus 6 times (distance x y minus one). "
                + "Write F(x,y) for full separation and Z(x,y) for the number of words equally distant from x and y. Prefixing equal letters multiplies F by three. "
                + "Prefixing different letters gives 3F+2Z, from the integer identity |u-1|+|u|+|u+1|=3|u|+2 times the indicator of u=0. "
                + "A neutral word chooses the third letter in each differing coordinate. It witnesses Z at least one. Changing one differing coordinate to either endpoint gives distance differences plus or minus one. "
                + "In a tail of dimension at least two, equal prefix letters give three neutral extensions; different prefix letters with a nonconstant tail use the three distance differences; an equal tail has 3 to the tail dimension neutral extensions. Thus Z is at least three. "
                + "Induction first gives F at least kappa plus 2 times (distance minus one). Applying one coordinate recurrence to that estimate and Z at least three gives the stated factor six. "
                + "The proof is symbolic in every dimension."),
            LiteratureTheorem("boundary-four", "The published weak two-metric boundary", "d2_metricDimension_four",
                "At d=2 and deficit four, kappa minus four equals two and the metric dimension is four. The four corners with both coordinates in {0,1} attain it. "
                + "For the lower bound, at most three weak two-landmarks would have one landmark in each row and column. Opposite corners from two of them are equally distant from all three."),
            LiteratureTheorem("boundary-five", "The published weak one-metric boundary", "d2_metricDimension_five",
                "At d=2 and deficit five, kappa minus five equals one and the metric dimension is three. The L consisting of (0,0),(0,1),(1,0) resolves. "
                + "Differences between the distances to two landmarks in a row recover one coordinate, and a pair in a column recovers the other. "
                + "Two landmarks fail: when they share a coordinate, the other two letters in that coordinate are indistinguishable; otherwise the two opposite corners are indistinguishable."),
            Theorem("exact-dimensions", "Every requested dimension", "result",
                "For every natural d at least two and t equal to four or five, the weak (2 times 3^(d-1) minus t)-metric dimension is four or three, respectively, at d=2. "
                + "For every d at least three it is 3^d minus six or seven, respectively. "
                + "An adjacent pair forces the sum of two column frequencies of an omitted set to be at most t. Adding the three pair constraints bounds its size by floor(3t/2). "
                + "For attainment, take the translation orbit of the constant zero word and that of the word whose first coordinate is zero and whose remaining coordinates are one. "
                + "They are disjoint actual three-element sets. For deficit five also insert the word with first two coordinates zero and two and every remaining coordinate zero. "
                + "The first two coordinates prove this seventh word is distinct. Each orbit loses at most twice the pair distance, and a singleton at most the pair distance. "
                + "The uniform separation gain therefore makes every complement weak resolving: the residual surplus is at least (6-t) times (distance minus one)."),
            Theorem("omitted-maxima", "Actual attainers and universal maxima", "omitted_maximum",
                "For every d at least two and t equal to four or five, an actual omitted Finset realizes the maximum, and every omitted Finset with a weak resolving complement has at most that cardinality. "
                + "The maxima are five and six at d=2, and six and seven at every d at least three. The existential statement and universal bound use the same literal Word d carrier."),
            Theorem("least-threshold", "The least eventual threshold", "least_threshold",
                "For each t in {4,5}, three is the least natural D for which the eventual formula holds for every d at least two with D at most d. "
                + "The all-dimensional construction proves the formula from three onward. The exact d=2 values contradict it at every D at most two. "
                + "This does not claim the full q,d,t threshold question is settled.")),
        []));

    private static DocumentBlock Definition(string id, string title, string declaration, string text) =>
        Node(id, title, declaration, text, DescribeRole.Definition, AssessedProvenance.FromLiterature(Kumar));
    private static DocumentBlock Theorem(string id, string title, string declaration, string text) =>
        Node(id, title, declaration, text, DescribeRole.Theorem, AssessedProvenance.FromRepo(Kumar, Boundary));
    private static DocumentBlock LiteratureTheorem(string id, string title, string declaration, string text) =>
        Node(id, title, declaration, text, DescribeRole.Theorem, AssessedProvenance.FromLiterature(Boundary));
    private static DocumentBlock Node(string id, string title, string declaration, string text,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.WithoutFormula(), provenance, Blocks(Paragraph(Text(text))), role);
}
