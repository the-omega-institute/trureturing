using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class CertificateBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/CertificateBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingcertificates");
    private static DocumentBlock Node(string name, string title, string text,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every finite simple graph, disjoint certificates for high internal degree "
            + "bound the largest inclusion-minimal two-star-forming set by half the sum "
            + "of the vertex count and dissociation number, rounded down.",
        H("Global certificates for two-star formation"),
        Blocks(
            Paragraph(Text("The proof is taken from the public note An elementary global "
                + "certificate bound for 2-star-forming sets, in the-omega-institute/"
                + "subquorum-colorings, revision 2e430b6481d4959f05f6d805871117261257e39d, "
                + "docs/STAR_FORMING_CERTIFICATES.md. It applies to every finite simple graph, "
                + "including the empty graph. Stars and three-vertex paths need not be induced. "
                + "Minimal always means inclusion-minimal. The established lower comparison "
                + "beta two at most SF two is attributed to Chellali and Favaron (2009).")),
            Node("high", "High internal degree",
                "For a finite vertex set S, high consists of the vertices s in S with at "
                    + "least two neighbours in S. Adjacency is the original graph adjacency.",
                DescribeRole.Definition),
            Node("Certificate", "Outside deletion certificates",
                "For vertices s and x, Certificate G S s x means that x is outside S and "
                    + "belongs to no two-leaf star contained in S with s removed and x added. "
                    + "The center is distinct from the leaves and the two leaves are distinct; "
                    + "extra graph edges are permitted.", DescribeRole.Definition),
            Node("certificate_exists", "High vertices have outside certificates",
                "For any inclusion-minimal two-star-forming S and every s in high G S, "
                    + "there exists x with Certificate G S s x. Removing s destroys star "
                    + "formation. The resulting obstruction cannot be s itself, because its "
                    + "two neighbours in S already give a path centered at s."),
            Node("certificate_unique", "One certificate cannot serve two high vertices",
                "For every two-star-forming S and high vertices s and t, if x certifies "
                    + "both s and t, then s equals t. A path containing x must contain both "
                    + "s and t; otherwise it survives the corresponding deletion. Its three "
                    + "vertices are exactly x,s,t. The vertex x is adjacent to one of s,t. "
                    + "That high vertex has a selected neighbour different from the other "
                    + "one, producing a path that survives the other deletion."),
            Node("certificates_disjoint", "Disjoint certificate sets",
                "For every two-star-forming S and distinct s,t in high G S, the sets of "
                    + "outside certificates of s and t are disjoint. No bipartition or "
                    + "triangle-free hypothesis is needed."),
            Node("certificate_injection", "Choose an injective certificate map",
                "For every inclusion-minimal two-star-forming S there exists an injective "
                    + "function from high G S to the complement of S in the whole finite "
                    + "vertex type. This also covers an empty domain."),
            Node("high_card_le", "High vertices fit in the complement",
                "For every inclusion-minimal two-star-forming S, the cardinality of high "
                    + "G S is at most the number of vertices outside S."),
            Node("low_independent", "The low part is a dissociation set",
                "For every S, the set S minus high G S is two-independent in the original "
                    + "IsKIndependent definition. Every retained vertex already had fewer "
                    + "than two neighbours in S, and deleting vertices cannot increase that count."),
            Node("minimal_card_bound", "The global cardinality inequality",
                "For every inclusion-minimal two-star-forming S, twice its cardinality is "
                    + "at most the cardinality of the vertex type plus beta G 2. The "
                    + "complement bounds the high part, and beta bounds the low part."),
            Node("minimal_card_le_floor", "The floor bound for each minimal set",
                "For every inclusion-minimal two-star-forming S, its cardinality is at "
                    + "most the natural-number quotient of the vertex count plus beta G 2 "
                    + "by two. This quotient is the floor in the source statement."),
            Node("sf_le_floor", "The upper two-star-forming number",
                "For every finite simple graph with decidable equality and adjacency, "
                    + "SF G 2 is at most the floor of the vertex count plus beta G 2, divided "
                    + "by two. The finite supremum ranges over the existing inclusion-minimal "
                    + "star-forming predicate. Injectivity does not show that replacing high "
                    + "vertices by certificates preserves dissociation: inserted vertices "
                    + "may create new paths. No equality of SF and beta is inferred.")),
        []));
}
