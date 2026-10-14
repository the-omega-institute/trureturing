using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class ClassCPathsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/ClassCPaths.";
    private static readonly LibraryNoteRef PatternSource =
        LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite labelled paths of coherent site states are equivalent to actual native prefix extensions.",
        H("Class-C Continuation Paths"),
        Blocks(
            Paragraph(Text("Every position of the site word and every new-maximum index labels its own branch. Equal child states therefore preserve the multiplicity of their incoming choices. The construction applies to all coherent formal states, including those not realized by a prefix. Its interpretation by numeric words is established separately for nonempty native inversion prefixes avoiding the four class-C patterns.")),
            Node("Path", "Labelled continuation paths",
                "At depth zero the path type is a singleton. At depth r plus one, a path consists of one labelled choice and a depth-r path from its formal child. This dependent finite type retains the chosen branch at every step.", DescribeRole.Definition),
            Node("phi", "Finite continuation count",
                "For every depth and coherent state, the continuation count is the natural cardinality of the finite labelled path type.", DescribeRole.Definition),
            Node("b", "Formal repeat-state continuation count",
                "For every depth r and positive slack s, b is the continuation count from the single seen site with the repeat flag. It is defined on every such formal state independently of actual-prefix reachability.", DescribeRole.Definition),
            Node("Extensions", "Actual numeric suffixes",
                "An extension of a valid nonempty prefix q at depth r is a list u of length r such that q followed by u lies in the native avoider set at total length q.length plus r. Both position-dependent inversion bounds and all four ranked-pattern exclusions are retained.", DescribeRole.Definition),
            Node("extensionEquiv", "Constructor and decoder correspondence",
                "For every valid nonempty prefix and every depth, actual numeric suffixes are equivalent to labelled formal paths from its actual state. Splitting a nonempty suffix selects its first legal value and its remaining suffix; joining prepends that value. Prefix deletion preserves native avoidance and the inversion bound. The sorted-value choice bijection and the native one-step state equality then transport the constructor recursively. Both inverse laws are proved.", DescribeRole.Definition),
            Node("native_continuation_count", "Cardinality of actual continuations",
                "For every valid nonempty prefix q and every natural depth r, the cardinality of its actual extension type equals the depth-r path count of its actual state. Finiteness of the actual extensions follows from the explicit equivalence to finite labelled paths. The equality uses the constructor and decoder correspondence rather than a state-sufficiency assumption.", DescribeRole.Theorem),
            Node("native_avoider_counts", "Native empty and root counts",
                "The native class-C avoider set at length zero contains exactly the empty word and has cardinality one. For every natural n, its cardinality at length n plus one equals b at depth n and slack one. Every positive-length inversion sequence begins with zero. Deleting that first zero and reattaching it gives inverse maps between whole avoiders and the actual suffixes of the prefix consisting of zero. This prefix has one seen admissible site, positive slack one and a true repeat flag. The result identifies the actual cardinality with finite labelled paths. The all-depth affine invariant, path injections with complement cardinalities and nonnegative differences, both universal a/b recurrences, the class-A/B equality and generating-series identities remain open.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string declaration, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("inversionseq-classcpaths-" + declaration.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(PatternSource), Blocks(Paragraph(Text(prose))), role);
}
