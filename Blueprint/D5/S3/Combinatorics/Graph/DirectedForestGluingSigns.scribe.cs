using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class DirectedForestGluingSignsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual directed forests determine the empty, gluing, and reattachment identities for ascending component-matching signs.",
        H("Directed forest gluing signs"),
        Blocks(Describe.Lean(
            DescribeId.Create("directed-forest-gluing-signs"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/DirectedForestGluingSigns.directed_forest_gluing_signs"),
            H("The three sign identities for literal directed forests"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Combinatorics/zernik2013allminors")),
            Blocks(
                Paragraph(Text(
                    "For every natural number n, the vertices are Fin n in increasing order, including all isolated vertices. "
                    + "U and W are finite vertex sets and F is a finite set of ordered pairs. A lawful forest has no loops "
                    + "or antiparallel pairs, an acyclic underlying undirected graph, exactly one U root and one W mark "
                    + "in each component, and every arrow points strictly away from its U root as measured by graph distance.")),
                Paragraph(Text(
                    "There exists a single family of permutations mu for every common cardinality k, every pair U and W "
                    + "of cardinality k, and every lawful F. For each ascending U coordinate a, its root is connected "
                    + "to the W vertex at ascending coordinate mu(a). Unique component membership makes this the actual "
                    + "component matching. The family is total at k = 0; this case has no matching coordinates.")),
                Paragraph(Text(
                    "Epsilon is the integer sign of that permutation multiplied by (-1) raised to n + k plus the "
                    + "sum of the zero-based labels in U and the sum of those in W. This definition uses graph components "
                    + "and ascending order. With U = W equal to the full vertex set, the empty forest is lawful and "
                    + "epsilon equals one, including n = 0.")),
                Paragraph(Text(
                    "For k at least one, let U and W have cardinality k, take w0 in W, i outside W and j outside U, "
                    + "and let F be lawful for the augmented root sets obtained by inserting j and i respectively. "
                    + "If j reaches i by directed arrows, insert the arrow from w0 to j; otherwise insert the arrow "
                    + "from i to j. Directed reachability is reflexive, so i = j belongs to the first branch. "
                    + "The resulting H is lawful for U and W.")),
                Paragraph(Text(
                    "Let a count the U vertices smaller than j and let b count the W vertices smaller than i. "
                    + "Multiplying the augmented epsilon by (-1) raised to i + b + j + a gives epsilon of H "
                    + "times minus one in the directed-descendant branch and times plus one in the other branch. "
                    + "In the first branch the matching arrow from j to i is removed. In the second branch the "
                    + "root previously matched to i is matched to the W mark previously matched to j; every other "
                    + "U-to-W match retains its mark.")),
                Paragraph(Text(
                    "For k at least one, take arbitrary vertices i and j and w0 in W. If F and the forest obtained "
                    + "by erasing the arrow (i,j) and inserting (w0,j) are both lawful for the same U and W, their "
                    + "epsilon values are equal. There is no assumption that the erased arrow exists, that i is "
                    + "outside W, or that j is outside U. Identical erased and inserted arrows and unchanged forests "
                    + "are included.")),
                Paragraph(Text(
                    "Shortest paths from a root follow the prescribed arrow orientation. Adding an edge between "
                    + "distinct components preserves distances within each old component; a path across the bridge "
                    + "has length equal to the distance to its first endpoint, plus one, plus the distance from "
                    + "its second endpoint. These paths give the new root and mark ownership and the new orientation. "
                    + "Ascending deletion coordinates identify the actual smaller matching with the finite permutation "
                    + "decomposition, whose sign yields the displayed gluing identity.")),
                Paragraph(Text(
                    "For a changed lawful reattachment, the old arrow really exists. Cutting it leaves no U root "
                    + "on the j side, since the old arrow points away from its root. The inserted edge and unique "
                    + "W membership in the new lawful forest force that side to contain no W mark. Thus every old "
                    + "U-to-W connection survives, and uniqueness identifies the two matchings. Root-set overlaps, "
                    + "reflexive descendants, isolated vertices, and arbitrary finite size are included throughout."))),
            DescribeRole.Theorem)),
        []));
}
