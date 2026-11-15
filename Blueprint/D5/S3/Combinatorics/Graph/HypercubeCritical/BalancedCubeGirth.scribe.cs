using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class BalancedCubeGirthDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every switching-balanced restriction of the original Huang cube signing has "
            + "extended girth at least eight, in every dimension.",
        H("Extended girth of balanced cube restrictions"),
        Blocks(
            Paragraph(Text(
                "For arbitrary n and C : Finset (BalancedCriticalSpectrum.Q n), "
                    + "IsBalanced C means that sigma takes values plus or minus one on C "
                    + "and the existing Huang matrix coefficient on every selected actual "
                    + "cube edge equals sigma(x) times sigma(y). The matrix is the same "
                    + "original matrix from Archive.Sensitivity used by the companion "
                    + "BalancedCriticalSpectrum. TRUE selects its first recursive block, "
                    + "so directional signs use earlier FALSE coordinates. No bridge to "
                    + "a TRUE-prefix construction is asserted.")),
            Paragraph(Text(
                "The external motivation, as in the companion, is Hong, Wu and Xia, "
                    + "Graph Sensitivity of Cartesian Products with Matched Bridges, "
                    + "arXiv:2610.09483v1, Section 7, Problem 2, "
                    + "https://arxiv.org/html/2610.09483v1#Thmproblem2 : determine "
                    + "f₂(Q₉)=3 or 4, by finding 258 selected vertices with induced maximum "
                    + "degree at most three, or proving complete exclusion. This is "
                    + "repository-derived structural progress under switching balance; "
                    + "it neither proves a lower bound of 48 nor solves the external Q9 problem.")),
            Paragraph(Text(
                "Signed-cube and Clifford precedents recorded in the companion are "
                    + "Laplante, Naserasr, Sunny and Wang, "
                    + "https://hal.science/hal-04080411/document , commentary after "
                    + "Lemma 4.1 and Theorem 6.2; Karasev, "
                    + "https://arxiv.org/abs/1907.11175v2 , Sections 1.2–1.3; and Mathews, "
                    + "https://arxiv.org/abs/1907.12357v2 , Sections 2.2–2.3. These are "
                    + "companion source references, not a new search or an assertion of "
                    + "an exact girth theorem in those papers. No novelty or priority "
                    + "claim is made; the helpers serve the proof consumers below.")),
            Describe.Lean(
                DescribeId.Create("balanced-cube-girth-gamma-anticommute"),
                DeclarationHandle.Create(Prefix + "gamma_anticommute"),
                H("Distinct actual coordinate operators anticommute"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For distinct i and j, Gamma_i Gamma_j z equals minus Gamma_j "
                        + "Gamma_i z for every actual function z : Q n → Real, with no "
                        + "balance assumption. The recursive gammaV Clifford proof is "
                        + "transported through coeff; the companion gamma_apply binds "
                        + "these operators to actual coordinate flips and the original "
                        + "Huang entries. It is consumed by no_selected_square and the "
                        + "private three-swap reversal used for three-step uniqueness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("balanced-cube-girth-no-selected-square"),
                DeclarationHandle.Create(Prefix + "no_selected_square"),
                H("Balance excludes selected coordinate squares"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If C is balanced, i differs from j, and x, flip_i(x), flip_j(x) "
                        + "are selected, then flip_j(flip_i(x)) is not selected. If it "
                        + "were, both two-step products would telescope to the same "
                        + "nonzero endpoint product, contradicting anticommutation. "
                        + "This supplies three_directions_distinct and the two- and "
                        + "three-step first-direction arguments."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("balanced-cube-girth-three-directions-distinct"),
                DeclarationHandle.Create(Prefix + "three_directions_distinct"),
                H("Selected nonbacktracking three-step words use distinct directions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a selected word i,j,k with i different from j and j different "
                        + "from k, balance forces i different from k. Otherwise its "
                        + "four selected vertices form a forbidden coordinate square. "
                        + "The consumer three_step_first_direction_eq uses this to "
                        + "obtain pairwise distinct directions in both words."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("balanced-cube-girth-three-step-first-direction-eq"),
                DeclarationHandle.Create(Prefix + "three_step_first_direction_eq"),
                H("Equal-endpoint three-step words have the same first direction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For balanced C, two selected nonbacktracking three-step words from the same "
                        + "vertex to the same endpoint have equal first actual cube "
                        + "directions. Coordinate parity and square exclusion reduce "
                        + "different-first cases to reverse words. Three pairwise "
                        + "swaps make their operator products opposite, while switching "
                        + "makes both the same nonzero endpoint product. This is the "
                        + "first-direction result consumed by no_six_cycle, with every "
                        + "intermediate vertex selected; it makes no uniqueness claim "
                        + "for arbitrary path lengths."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("balanced-cube-girth-no-four-cycle"),
                DeclarationHandle.Create(Prefix + "no_four_cycle"),
                H("The actual induced graph has no four-cycle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For balanced C, an actual closed induced-graph walk satisfying "
                        + "IsCycle cannot have length four. Extracting actual flip "
                        + "coordinates gives two nonbacktracking two-step halves. "
                        + "The private two-step first-direction result, from square "
                        + "exclusion, identifies their first vertices, contradicting "
                        + "cycle vertex injectivity. eight_le_egirth consumes this exclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("balanced-cube-girth-no-six-cycle"),
                DeclarationHandle.Create(Prefix + "no_six_cycle"),
                H("The actual induced graph has no six-cycle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For balanced C, an actual closed induced-graph walk satisfying "
                        + "IsCycle cannot have length six. Actual coordinate extraction "
                        + "and cycle vertex injectivity give two nonbacktracking "
                        + "three-step halves. three_step_first_direction_eq identifies "
                        + "their first vertices, contradicting injectivity. The consumer "
                        + "is eight_le_egirth."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("balanced-cube-girth-eight-le-egirth"),
                DeclarationHandle.Create(Prefix + "eight_le_egirth"),
                H("Balance alone forces extended girth at least eight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every n and C : Finset (BalancedCriticalSpectrum.Q n), the "
                        + "sole hypothesis BalancedCriticalSpectrum.IsBalanced C gives "
                        + "8 ≤ ((hypercube n).induce (C : Set _)).egirth. Reusing the "
                        + "private cubeParity and its adjacency property supplies an "
                        + "actual Boolean coloring, so closed walks have even length. "
                        + "IsCycle gives length at least three; excluding four and six "
                        + "therefore gives length at least eight. Extended girth includes "
                        + "empty and acyclic restrictions. No nonemptiness, regularity, "
                        + "connectivity, degree bound or dimension restriction is assumed."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum"))
        ]));
}
