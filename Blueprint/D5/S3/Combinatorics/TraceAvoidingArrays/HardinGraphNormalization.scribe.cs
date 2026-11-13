using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinGraphNormalizationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinGraphNormalization.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233170");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "First occurrences and exact complementary-pair fibers on finite ordered graphs.",
        H("Independent signs after the first vertex of each class"),
        Blocks(
            Paragraph(Text("Vertices are Fin (n+1), with their natural order. The map beta has fibers {0,5}, {1,4}, {2,3}. Normal uses the existing good scanner with both flags initially false and fixes vertex zero to colour zero. By good_iff, every 2, 3 or 4 has an earlier 1, and every 3 has an earlier 2. No condition requires an absent colour to appear.")),
            Node("normal", "Normal", "The literal scanner convention", DescribeRole.Definition,
                "The domain is nonempty. In a strip the vertex index is its row-major rank. The source convention of a zero empty-series coefficient is separate from the one empty function on an empty graph."),
            Node("first", "First", "The minimum of a pair class", DescribeRole.Definition,
                "First p i says that no strictly earlier vertex has the same pair label as i. This predicate is also defined on Fin 0."),
            Node("ordered", "Ordered", "The order of the three pair classes", DescribeRole.Definition,
                "The first label is zero. Every occurrence of label two has an earlier occurrence of label one. Together these conditions order all nonempty classes by their first vertex; labels may be absent."),
            Node("normal-iff", "normal_iff", "The exact first-appearance characterization", DescribeRole.Theorem,
                "For a literal assignment, the pair labels are Ordered and the colour at every pair-class minimum equals its label. Conversely those two properties imply every literal predecessor requirement. To recover a required predecessor, take the least occurrence of its pair label at or before the current vertex. Its sign is fixed. If the current colour is 3 or 4 that predecessor is strictly earlier; if it uses pair two, Ordered first supplies the earlier pair-one class. This argument applies to arbitrary length, rather than to a finite sample."),
            Node("lift", "lift", "The two colours of a pair", DescribeRole.Definition,
                "A false sign selects p; a true sign selects 5-p. Here p is a Fin 3 label. The two choices are distinct, have the same beta label, and exhaust its two-element fiber."),
            Node("free", "Free", "The free vertices", DescribeRole.Definition,
                "Free p is the subtype of vertices that are not first in their pair class. One vertex is omitted for each used label, including when only one or two labels occur."),
            Node("fiber", "Fiber", "Literal lifts of an ordered pair word", DescribeRole.Definition,
                "The fiber retains the entire six-colour assignment, its Normal property and the equality of its beta projection with p."),
            Node("fiber-equiv", "fiberEquiv", "Mutually inverse literal lifts and free signs", DescribeRole.Definition,
                "The forward map reads whether the actual colour is at least three at each free vertex. The inverse fixes every first sign to false and uses the supplied Boolean function at every other vertex. beta_lift, lift_sign and sign_lift prove both inverse identities. First occurrences are in bijection with the range of p, so the number of free vertices is N-j, where j is the number of nonempty classes."),
            Node("legal", "Legal", "Literal graph assignments", DescribeRole.Definition,
                "For every edge, the actual colours are unequal and their natural values do not sum to five. The existing colour_bond_iff identifies this exact condition with unequal beta labels. No connectivity or bipartiteness assumption enters."),
            Node("graph-fiber", "GraphFiber", "The fiber over an actual proper colouring", DescribeRole.Definition,
                "The parameter p is a SimpleGraph.Coloring (Fin 3), not an assumed adjacency summary. Mathlib's colorClasses_isPartition and isIndepSet_colorClass identify its nonempty fibers as independent sets, and card_colorClasses_le bounds their number by three. The theorem below does not yet identify distinct ordered colourings with all unlabelled independent-set partitions."),
            Node("result", "result", "The exact graph fiber cardinality", DescribeRole.Theorem,
                "For every finite graph on N=n+1 ordered vertices and every Ordered proper pair colouring p, the number of literal lifts is exactly 2^(N-j), with j the cardinality of the range of p. The graph condition adds no further sign restriction, because every sign lift preserves beta. A one-class assignment has N-1 free signs; the singleton therefore has exactly one lift. Fewer than three used labels are retained. In particular this count is not a uniform division of all labelled six-colourings by 48."),
            Paragraph(Text("The marked-partition interpretation is prior work of Britnell and Wildon, arXiv:1507.04803v1, equation (9) and Proposition 8.1, subsequently JCTA 148 (2017), 116–144, DOI 10.1016/j.jcta.2016.12.003. The graphical Stirling expansion is established in Duncan and Peele, Bell and Stirling Numbers for Graphs, JIS 12 (2009), Article 09.7.1, with attribution to Biggs, Proposition 9.2. The present finite-word characterization connects the actual scanner to its sign fibers; it makes no priority claim.")))));

    private static DocumentBlock Node(string id, string name, string title,
        DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
