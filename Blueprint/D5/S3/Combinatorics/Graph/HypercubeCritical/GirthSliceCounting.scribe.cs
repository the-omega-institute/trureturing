using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class GirthSliceCountingDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/GirthSliceCounting.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual short-path and incidence counting gives two weighted cubic slice bounds in a finite bipartite graph.",
        H("Weighted cubic slice counting at extended girth eight"),
        Blocks(
            Paragraph(Text(
                "The external research anchor is Hong, Wu and Xia, Graph Sensitivity of "
                    + "Cartesian Products with Matched Bridges, arXiv:2610.09483v1, "
                    + "7 October 2026, Section 7 Problem 2, Determine whether f₂(Q₉)=3 or 4. "
                    + "The exact locator is https://arxiv.org/html/2610.09483v1#Thmproblem2 . "
                    + "That problem asks for 258 vertices inducing maximum degree at most three, "
                    + "or a complete exclusion. This module is a repository-derived generic "
                    + "short-path counting result: it does not claim to solve the Q₉ problem, "
                    + "to be a world-first result, or to have formalized the complete lower bound 48.")),
            Paragraph(Text(
                "The theorem concerns an arbitrary finite SimpleGraph G on V and finite left "
                    + "and right sets L and R satisfying the actual bipartite relation "
                    + "G.IsBipartiteWith (L : Set V) (R : Set V). Every actual vertex has degree "
                    + "two or three. Degree-two vertices are independent, and the extended girth "
                    + "is at least eight. The slices L3, L2, R3 and R2 are the actual degree-three "
                    + "and degree-two filters of L and R; no path injection, path cardinality, "
                    + "or local weight identity is assumed as an input.")),
            Paragraph(Text(
                "Write h=|L3|, b=|R|, k=|R3| and r=|R2|. The conclusion is "
                    + "15h ≤ h*b + 2*k + 4*r, together with the exchanged inequality "
                    + "15|R3| ≤ |R3|*|L| + 2|L3| + 4|L2|. The proof uses additive natural-number "
                    + "equalities, so no truncated subtraction is hidden in the statement.")),
            Paragraph(Text(
                "For the first inequality, the actual length-one paths rooted at L3 have "
                    + "cardinality 3h. They are joined to the actual nonbacktracking length-three "
                    + "paths, whose cardinality is P, and the joint endpoint map (root, endpoint) "
                    + "is injective into L3×R. Extended girth at least eight forces this endpoint "
                    + "uniqueness, giving 3h+P ≤ h*b. The three-step family is then reindexed by "
                    + "its actual first middle vertex. If that vertex has g high-degree neighbors "
                    + "and j low-degree neighbors, its actual three-step count C satisfies "
                    + "C+2g = g*(j+2g). At a low middle vertex, independence gives j=0, g=2 "
                    + "and C=4. At a high middle vertex, j+g=3, C+j*g=4g and j*g≤2. "
                    + "The actual edge-incidence double count Σ_R g=3h gives "
                    + "12h ≤ P+4r+2k; combining the two derived bounds yields the result.")),
            Paragraph(Text(
                "As a nonempty equality illustration, subdivide every edge of K3,3 once. "
                    + "The original six vertices form the degree-three side, the nine new "
                    + "vertices form the degree-two side, the low-degree vertices are independent, "
                    + "and the girth is eight. Thus h=6, b=9, k=0 and r=9, and the first bound "
                    + "has 90 on both sides. This is only a mathematical illustration; this "
                    + "module does not compile that concrete graph instance and introduces no "
                    + "instance declaration or instance Describe. A later 48-vertex lower-bound "
                    + "argument may use this counting result, while an actual Q₉ slice construction "
                    + "and every bridge to its hypotheses must be completed elsewhere.")),
            Paragraph(Text(
                "The Lean source imports Mathlib.Combinatorics.SimpleGraph.Girth and "
                    + "Mathlib.Combinatorics.Enumerative.DoubleCounting (along with the ordinary "
                    + "finite-graph support) and has no dependency on a D5 project module. "
                    + "The formal content is the generic graph theorem and its two degree filters; "
                    + "it does not assert that the Q₉ construction or the full ≥48 argument is "
                    + "already formalized.")),
            Describe.Lean(
                DescribeId.Create("degree-two-slice"),
                DeclarationHandle.Create(Prefix + "degreeTwo"),
                H("The actual degree-two slice"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "degreeTwo G S is the finite subset of S consisting exactly of vertices "
                        + "whose actual G-degree is 2. It is a filter of the supplied set S, "
                        + "not a separately postulated layer or a path-counting surrogate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("degree-three-slice"),
                DeclarationHandle.Create(Prefix + "degreeThree"),
                H("The actual degree-three slice"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "degreeThree G S is the finite subset of S consisting exactly of vertices "
                        + "whose actual G-degree is 3. Together with degreeTwo it records the "
                        + "degree filters used in the weighted bipartite estimate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cubic-slice-counting"),
                DeclarationHandle.Create(Prefix + "cubic_slice_counting"),
                H("The two weighted cubic slice inequalities"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For finite L and R in the stated bipartite relation, if every actual "
                        + "vertex has degree 2 or 3, degree-two vertices are independent, and "
                        + "the extended girth is at least 8, then both side-swapped inequalities "
                        + "hold: 15 times the number of degree-three vertices on one side is at "
                        + "most that number times the opposite-side cardinality, plus twice the "
                        + "opposite degree-three slice and four times the opposite degree-two "
                        + "slice. The proof derives the endpoint injection, the local three-step "
                        + "identity and the incidence double count from the actual graph; none is "
                        + "an added hypothesis. The theorem is generic combinatorics motivated by "
                        + "the cited Q₉ question, with the construction and hypothesis bridges for "
                        + "that question left to other modules."))),
                DescribeRole.Theorem))));
}
