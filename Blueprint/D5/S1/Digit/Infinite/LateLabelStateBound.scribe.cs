using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class LateLabelStateBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/Infinite/LateLabelStateBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Late nonnull labels at finite-source extrema.",
        H("Late nonnull labels at finite-source extrema"),
        Blocks(
            Node("Representation", "Finite full-path representations",
                "A finite directed multigraph has finite vertex and edge types, an incoming Boolean guard at each vertex, and an original legal three-bit label at each edge. Each edge obeys the original guard transition. All vertices in the finite initial set have guard zero. Parallel edges and nondeterministic choices are permitted."),
            Node("Path", "All infinite paths",
                "A path is any infinite sequence of edges whose successive target and source vertices agree. No further acceptance condition or scalar membership test is imposed."),
            Node("shiftPath", "Actual edge deletion",
                "Deleting n edges of a path deletes exactly n original three-bit windows."),
            Node("splicePath", "Replacement of a continuation",
                "Any infinite continuation starting at the vertex reached after n edges can replace the tail of a path, with all preceding edges retained."),
            Node("pathAddress", "Actual source addresses",
                "Concatenating the original three-bit edge labels gives a legal infinite Boolean address. The edge guards prevent adjacent ones across window boundaries. Its scalar is the original window series kappa, with no initial offset."),
            Node("scalarImage", "The total initial scalar image",
                "The total image consists of the original scalar values of all infinite paths whose first vertex belongs to the initial set."),
            Node("Surviving", "Surviving vertices",
                "A vertex survives precisely when some infinite compatible path starts there. Vertices that are unreachable from the initial set are allowed to survive."),
            Node("survivorCount", "Surviving vertex count",
                "The number s is the finite cardinality of the surviving vertex type."),
            Describe.Lean(
                DescribeId.Create("latelabelstatebound-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The late-label lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every such finite representation, every minimum or maximum e of its total initial scalar image, every actual eventually-zero address x with kappa(x)=e, and every zero-based window position j with a nonnull label, the surviving vertex count satisfies s>=ceil((j+2)/2).")),
                    Paragraph(Text(
                        "The signed golden-series fiber classification implies that an eventually-zero address is the only legal address over its scalar. The two addresses at each seam have nonzero alternating tails, even after a finite prefix.")),
                    Paragraph(Text(
                        "Replacing a path tail after n windows changes the scalar by (-g)^n times the change of tail scalar. At two occurrences of the same vertex with the same parity, extremality in both replacement directions forces the tail scalars to agree. The finite-source uniqueness then forces the whole tail addresses to agree.")),
                    Paragraph(Text(
                        "Equal tails at two distinct positions are periodic from the earlier position onward. An eventually-zero tail with a positive period is entirely zero. A nonnull window at j therefore forces the first j+2 signed vertices to be distinct. Each signed vertex consists of one surviving vertex and a parity, so there are only 2s available states."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string selector, string title, string text) =>
        Describe.Lean(
            DescribeId.Create("latelabelstatebound-" + selector.Replace(".", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            DescribeRole.Definition);
}
