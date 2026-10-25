using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Rainbow;

internal sealed class TwoEdgeChoicesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Rainbow/TwoEdgeChoices.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Repeated-colour two-edge choices have sparse exceptional endpoints; the genuine rainbow choices split into three classes using disjoint tagged vertex and colour coordinates.",
        H("Deterministic Rainbow Two-Edge Choices"),
        Blocks(
            Paragraph(Text(
                "A directed graph here is Mathlib Digraph: a relation on vertices, with at most one edge "
                + "in each ordered direction. OutProper says that colours leaving any one vertex are "
                + "distinct; InProper says that colours entering any one vertex are distinct. Colours "
                + "may repeat between the two stars and elsewhere. The literal colour function is "
                + "evaluated only on actual edges; its values on nonedges are unconstrained. No group "
                + "structure, symmetry, bipartition or global injectivity is used. The colour type need "
                + "not be finite. The final simple-path conclusion explicitly assumes looplessness.")),
            Describe.Lean(DescribeId.Create("repeated-colour-mass"),
                DeclarationHandle.Create(Prefix + "repeated_colour_mass_le_outdegree"),
                H("Total Repeated-Colour Endpoint Mass"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix a root u. For each endpoint w, repeated counts the intermediate vertices x "
                    + "of u to x to w whose two literal colours coincide. For each fixed outgoing "
                    + "neighbour x of u, outgoing properness at x allows at most one such w. Double "
                    + "counting the actual pairs (x,w) therefore bounds their total by the actual "
                    + "outdegree of u, and consequently by the original vertex count n. This argument "
                    + "does not assume that every two-edge path is rainbow. Its live consumer below "
                    + "uses the mass to bound the exceptional endpoints."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("three-disjoint-classes"),
                DeclarationHandle.Create(Prefix + "exists_three_disjoint_classes"),
                H("Three Classes with Disjoint Coordinate Supports"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any finite choice family A, let a and b be separately injective literal "
                    + "colour maps on A. Join distinct choices exactly when their colour pairs "
                    + "intersect. Same-position equalities are excluded by injectivity; at most one "
                    + "neighbour has its second colour equal to the fixed first colour, and at most "
                    + "one has its first colour equal to the fixed second colour. The actual conflict "
                    + "graph thus has degree at most two. Apply BrooksSubcubic.colorable_of_lower_neighbors_lt "
                    + "directly with an injective finite rank and three colours. That existing supplier "
                    + "is Juan Pablo Traverso Gianini's licensed greedy-colouring result, retained in "
                    + "Graph/Brooks/Coloring; no new greedy theorem is asserted here. The resulting "
                    + "three finite classes partition all choices and preserve their total cardinality. "
                    + "Each support is {inl x, inr (a x), inr (b x)} in Sum V C. Distinct choices in a "
                    + "class have disjoint supports, including when V and C are the same underlying "
                    + "type. The tags prevent a vertex value from being mistaken for a colour coordinate."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quantitative-rainbow-core"),
                DeclarationHandle.Create(Prefix + "deterministic_rainbow_choice_core"),
                H("Sparse Exceptions and a Quantitative True-Rainbow Base"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive nu and n, define B_u by repeated count greater than nu*n/16. "
                    + "The mass estimate proves |B_u| < 16/nu, including the empty exceptional-set "
                    + "case. At any distinct endpoint w outside B_u, take any deterministic actual "
                    + "two-edge base family of size at least nu*n/4. Deleting its repeated-colour "
                    + "choices loses at most nu*n/16, leaving at least 3*nu*n/16 genuine rainbow "
                    + "choices. Apply the preceding actual tricolouring to precisely this remaining "
                    + "family, using outgoing properness at u and incoming properness at w. Every "
                    + "choice gives two actual directed edges, three distinct path vertices, two "
                    + "different literal colours and exactly three tagged coordinates. This is a "
                    + "retained quantitative consumer of both the new endpoint counting and the "
                    + "new disjointness construction; it supplies the within-class disjoint-coordinate "
                    + "hypotheses needed by a later Bernoulli reservoir calculation."))), DescribeRole.Theorem),
            Paragraph(Text(
                "Source attribution: Bucić, Frederickson, Müyesser, Pokrovskiy and Yepremyan, "
                + "Towards Graham's rearrangement conjecture via rainbow paths, arXiv:2503.01825v2, "
                + "Section 2 and Section 4.3, Lemma 4.3 (https://arxiv.org/html/2503.01825v2). "
                + "The present deterministic estimates reconstruct the colour-aware repair's "
                + "counting and conflict-graph steps as Lean proofs. They are adaptations of "
                + "standard double counting and graph colouring, with no novelty claim.")),
            Paragraph(Text(
                "This unit proves no probability bound. The dependent Bernoulli MGF and Hölder "
                + "argument, robust layer construction, all-pairs and post-revelation forbidden-set "
                + "quantifiers, exact length bound and common B1/B2/B3 event of probability at least "
                + "1-5/n remain outside this unit. The full original connector, arbitrary-abelian "
                + "proper-interval Good statement and unrestricted AM remain open in this development.")))));
}
