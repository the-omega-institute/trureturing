using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class ClassCInsertionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/ClassCInsertion.";
    private static readonly LibraryNoteRef PatternSource =
        LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Marked-prefix insertion gives explicit injections of actual labelled paths and exact finite complements.",
        H("Class-C Path Insertion and Complements"),
        Blocks(
            Paragraph(Text("The carriers are the existing coherent State and labelled Path types. Every finite site word is included, every slack is positive, and coherence says only that a true flag implies a final seen site. A false flag may also accompany a final seen site. Old positions and new labels remain distinct even when children coincide. These are formal path correspondences; numeric continuation words enter only through the existing equivalence for actual nonempty prefixes and the separate root-count theorem.")),
            Node("prepend", "A marked prefix of sites",
                "For a finite site word v and any coherent state q, prepend v to the site word and retain exactly q's slack and Boolean flag. Coherence follows by prepending to its existing final-S witness. No realization premise is added.", DescribeRole.Definition),
            Node("choiceSplit", "Exact labelled first-choice partition",
                "Every choice from the prepended state is uniquely a marked position of v, an old position of q translated by the length of v, or the unchanged new-maximum label of q. The inverse compares the old position with the prefix length and subtracts that length only in the translated branch. Equal children do not identify any positions.", DescribeRole.Definition),
            Node("Outside", "First marked old choice and arbitrary tail",
                "At depth zero this type is empty. At depth r plus one it is the disjoint sum of a marked old position with an arbitrary depth-r path from its actual child, and a legal new label j with the recursively decoded complement at depth r from q's actual new child. Thus every initial new label is retained, the first marked old choice is unique, and its remaining path is unrestricted. This is an explicit finite carrier, independent of subtraction of cardinalities.", DescribeRole.Definition),
            Node("splitInserted", "Insertion decoder and reconstruction",
                "For every v, natural depth r and coherent q, paths from the prepended state are equivalent to the disjoint sum of paths from q and Outside v r q. A matched old position is shifted by the prefix length and its child is exactly the source child, so the whole tail is retained. A new label is unchanged and the smaller-depth decoder is used. A marked old choice records that position and stops. The composed equivalences include both inverse laws.", DescribeRole.Definition),
            Node("insertPath", "Explicit insertion map",
                "Insert a source path by applying the inverse partition equivalence to its source summand. Its image is precisely the source branch of the decoder. The complement branch consists of paths whose first old selection is marked; a path with no old selection stays in the image.", DescribeRole.Definition),
            Node("insertionComplement", "The actual finite complement",
                "The subtype of target paths outside the existential image of insertPath is equivalent to Outside. The forward map decodes the complement branch; reconstructing a complement cannot lie in the source branch. Both inverse laws follow from the actual partition equivalence.", DescribeRole.Definition),
            Node("unusedInjection", "One additional leading unused site",
                "For every r,k at least zero and positive s, paths from the actual lower state with k unused sites embed in paths from the lower state with k plus one unused sites. The inserted site is the leading U; every existing position and every new label is retained.", DescribeRole.Definition),
            Node("EmptyOutside", "Changed-flag empty-to-repeat complement",
                "At depth zero this complement is empty. At positive depth, its first summand is an immediate repeat with the arbitrary remaining path from repeat slack s plus one. Its other summand records one legal initial new label and the marked-S complement in the smaller-depth new child of the empty lower state. Every later marked-old stop therefore occurs after at least one new choice.", DescribeRole.Definition),
            Node("splitEmpty", "Special first-step partition",
                "For every depth and positive slack, repeat-state paths are equivalent to the disjoint sum of empty-lower-state paths and EmptyOutside. The empty source has only a new first choice. The map keeps that label and then inserts the original S into the tail. This changes the initial flag from false to true correctly; it is not ordinary flag-preserving insertion at depth zero. Immediate repeat is the separate complement summand.", DescribeRole.Definition),
            Node("emptyInjection", "Empty-to-repeat path embedding",
                "Apply the inverse special partition to the source summand. This is an injection from paths with an empty site word and false flag to paths with one S and true flag, at every depth and positive slack.", DescribeRole.Definition),
            Node("emptyComplement", "Exact empty-to-repeat complement",
                "The subtype of repeat-state paths outside the actual image of emptyInjection is equivalent to EmptyOutside. Its decoder retains all initial new labels and arbitrary tails and separates the immediate repeat.", DescribeRole.Definition),
            Node("LowerComplement", "Decoded legal initial-new histories",
                "At depth zero there are no histories. At positive depth, stopping retains an arbitrary actual path from the lower state with suffix-U count k and slack s plus one. Continuing records a separate Fin s label j, decreases slack to s minus j, increases the suffix-U count to k plus j and decreases depth. This retains all legal finite label histories, including distinct histories with equal sums. Since j is strictly below s, every continued slack stays positive.", DescribeRole.Definition),
            Node("outsideLowerEquiv", "Computing the first-old terminal state",
                "For either marked site U or S, any depth and any coherent q, Outside with that one marked site is equivalent to LowerComplement at q's actual slack and number of unused sites. Choosing the marked site leaves the exact unused count of q's suffix and increases slack by one. The marked site cannot be the repeat position: if the initial flag is true, coherence provides a nonempty final-S suffix in q. Each new choice appends j unused sites and a seen site, giving precisely the recursive slack and unused-count updates. Both directions preserve every label and the entire terminal path.", DescribeRole.Definition),
            Node("unusedComplementDecoded", "Exact decoded unused-site complement",
                "For every depth, positive slack and unused count, the subtype outside the image of unusedInjection is equivalent to LowerComplement with those exact parameters. This composes the actual complement decoder with the terminal-state computation, rather than inferring a correspondence from equal cardinalities.", DescribeRole.Definition),
            Node("RepeatComplement", "Decoded changed-flag histories",
                "At positive depth the complement either chooses the initial repeat immediately, retaining a path from repeat slack s plus one, or records a first new label j and a LowerComplement at slack s minus j and suffix-U count j. The second branch therefore has at least one initial new label. At zero depth it is empty.", DescribeRole.Definition),
            Node("emptyComplementDecoded", "Exact decoded empty-to-repeat complement",
                "The actual subtype outside the image of emptyInjection is equivalent to RepeatComplement. The direct immediate-repeat branch remains separate from every branch with an initial new label. This includes the changed initial flag and all inverse laws.", DescribeRole.Definition),
            Node("unused_difference", "Unused-site natural difference",
                "For every r,k at least zero and every s at least one, the actual lower count at k is at most the count at k plus one. Their natural difference is exactly the cardinality of LowerComplement r s k. This finite carrier retains each initial new label, subtracts it from slack and adds it to k, then retains an arbitrary Path tail from lower state k at slack s plus one when the first marked old choice occurs. The proof counts the explicit disjoint path partition. In particular the zero-depth difference vanishes and k equal to zero still uses a lower initial marked-U selection because its flag is false.", DescribeRole.Theorem),
            Node("empty_difference", "Repeat-minus-empty natural difference",
                "For every depth r and positive slack s, the actual empty-lower count is at most b r s, and b minus that count is exactly the cardinality of RepeatComplement. Its immediate-repeat branch has an arbitrary repeat Path tail; its other branch records a legal first new label and then the full LowerComplement history with that label as its initial suffix-U count. The proof counts the changed-flag partition. At zero depth both path sets are singletons and the complement is empty. No sign assumption or truncated-subtraction argument is used to manufacture the inequality.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string declaration, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("inversionseq-classcinsertion-" + declaration.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(PatternSource), Blocks(Paragraph(Text(prose))), role);
}
