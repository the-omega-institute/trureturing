using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class ClassCSitesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/ClassCSites.";
    private static readonly LibraryNoteRef PatternSource =
        LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Admissible values of class-C inversion prefixes have an exact sorted-site succession.",
        H("Class-C Admissible Sites"),
        Blocks(
            Paragraph(Text("Inversion-sequence entries are nonnegative and satisfy the zero-based bound at their positions. Pattern ranks alone are shifted to the positive letters used by ranked occurrences. The four patterns here are 211, 212, 221 and 321; they differ from the class-A quadruple at its fourth pattern. The derivation uses the native ranked occurrence relation. The cited Callan–Mansour source supplies the inversion-sequence and pattern context; the admissible-site arguments below are derived here.")),
            Node("patterns", "Class-C patterns",
                "The pattern list consists exactly of 211, 212, 221 and 321.", DescribeRole.Definition),
            Node("Safe", "Append safety",
                "For any word w and natural value x, safety means that w followed by x avoids every class-C pattern. This predicate does not impose the inversion-sequence bound.", DescribeRole.Definition),
            Node("ForbiddenTriple", "Exclusion by an ordered pair",
                "An ordered pair with values a and b excludes a subsequent x precisely when a is greater than b and either x is at most b or x equals a, or when a equals b and x is smaller than a.", DescribeRole.Definition),
            Node("maximum", "Maximum entry",
                "The maximum is the fold of the natural maximum operation with initial value zero.", DescribeRole.Definition),
            Node("safe_append_iff", "Exact append criterion",
                "For every finite natural word w and natural x, appending x is safe if and only if w already avoids class C and every pair of positions i less than j less than the length of w fails to exclude x. A newly created forbidden occurrence must end at the appended position; the converse constructs the corresponding ranked occurrence.", DescribeRole.Theorem),
            Node("safe_update", "Exact update of safety",
                "Let w be any nonempty natural word and suppose appending x is safe. For every natural y, appending y after x is safe exactly when y was safe after w and satisfies the following condition. If x is below the maximum of w, y must be greater than x and absent from w. If x equals the maximum, y must be at least that maximum. If x is a new maximum, no additional condition is imposed. Old exclusions therefore persist in all three cases.", DescribeRole.Theorem),
            Node("admissible", "Old admissible values",
                "The old admissible values are the safe naturals from zero through the maximum, retained as a finite set.", DescribeRole.Definition),
            Node("values", "Sorted numeric sites",
                "The admissible values are listed in increasing order without duplicates. Keeping their numeric identities permits inversion of the choice correspondence.", DescribeRole.Definition),
            Node("label", "Seen and unused labels",
                "A value has label S when it occurs in the current word and label U otherwise.", DescribeRole.Definition),
            Node("siteWord", "Sorted site word",
                "Map the seen-or-unused label over the sorted admissible-value list. Repeated labels retain their distinct positions.", DescribeRole.Definition),
            Node("site_word_succession", "Succession of sorted site words",
                "For every nonempty natural word w and safe appended x, a lower choice leaves a word of U labels, one for each old admissible unused value greater than x. Repeating the maximum leaves the single site S. A new maximum leaves the old site word followed by x minus the old maximum minus one U labels and one S label. These statements concern safety independently of the inversion bound.", DescribeRole.Theorem),
            Node("choiceValue", "Numeric choice decoder",
                "An old choice is a position in the sorted value list and decodes to that value. A new choice has index j from zero through the slack minus one and decodes to the old maximum plus j plus one.", DescribeRole.Definition),
            Node("choiceEquiv", "Bijection with legal appends",
                "For every nonempty class-C-avoiding inversion sequence, the disjoint sum of old-site positions and slack indices is equivalent to the type of natural appends satisfying both safety and the bound by the current length. The inverse selects the unique sorted index of an old admissible value or the offset of a new maximum. All positions remain distinct even when child states agree.", DescribeRole.Definition),
            Node("stateOf", "Actual prefix state",
                "For a nonempty inversion sequence, the state consists of its sorted site word, length minus maximum as positive slack, and the Boolean safety of its maximum. If that maximum is admissible, it is the final sorted site and has label S.", DescribeRole.Definition),
            Node("lowerState", "Formal lower state",
                "For every natural k and positive slack s, the formal lower state has k unused sites and no repeat flag. Such states are defined independently of actual-prefix reachability.", DescribeRole.Definition),
            Node("repeatState", "Formal repeat state",
                "For every positive slack s, the formal repeat state has one seen site and a true repeat flag.", DescribeRole.Definition),
            Node("child", "Labelled child transition",
                "Each old position is a separate choice. If the repeat flag is true and that position is final, its child is the repeat state with slack increased by one. Every other old choice has the lower state whose number of sites counts U labels strictly to its right, also with slack increased by one. A new choice with zero-based index j appends j unused labels and one seen label, and decreases the slack by j.", DescribeRole.Definition),
            Node("liftChoice", "Choice coordinates of the actual state",
                "The numeric site's index and the corresponding site-word index agree because labelling preserves list length. Slack indices are unchanged.", DescribeRole.Definition),
            Node("native_succession", "Native state-transition correspondence",
                "For every nonempty class-C-avoiding inversion sequence and every labelled choice, append its decoded numeric value. The resulting word is again an inversion sequence, and its actual state equals the formal child of the original actual state at that choice. The equality includes the complete site word, positive slack and repeat flag. The final old position repeats exactly when its numeric value is the maximum; lower-site multiplicities count unused positions strictly to the right.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string declaration, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("inversionseq-classcsites-" + declaration.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(PatternSource), Blocks(Paragraph(Text(prose))), role);
}
