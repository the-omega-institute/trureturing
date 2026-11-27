using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9WeightedBoundaryGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted boundary Gram and rooted cofactors in the nine-cube",
        H("Coordinate weights on the separated boundary"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-weighted-boundary-gram-separated"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/"
                    + "Q9WeightedBoundaryGram.separated_cubic_weighted_boundary_factorization"),
                H("The rooted cofactor product is the square of the actual boundary determinant"),
                StatementSource.FromAuthor(Disp(Seq(
                    CallDet(Seq(F.Id("B"), Underscore, F.Id("C"))), Sp,
                    CallDet(Seq(F.Id("B"), Underscore, F.Id("D"))), Sp, Eq, Sp,
                    CallDet(F.Id("Z")), Caret, D(2)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let C and D be disjoint Huang-balanced induced cubic supports with 72 and 186 vertices in Q9. Assume there is no cube edge between the supports. Choose one root from each in a common parity b. The rows are all vertices of parity b in C and D except the two roots. The 127 columns are all opposite-parity vertices outside the union, reindexed by a bijection with those rows.")),
                    Paragraph(Text("Use an arbitrary nine-coordinate weight vector w over a commutative ring. There is an integer switching sign of square one at every vertex. The entry of Z from a retained vertex x to an exterior vertex y is the sum over flips from x to y of the coordinate weight times the Huang flip sign and the two switching signs. The entry is zero when no flip connects x and y.")),
                    Paragraph(Text("For each support G, M sub G is the unsigned weighted biadjacency on its retained rows and all its selected opposite-parity columns. Its entries are the sums of weights of the flips joining the endpoints. Write q for the sum of the nine squared weights. Then B sub G is q times the identity minus M sub G times its transpose, so B sub G is the principal submatrix of the full defect obtained by removing the root.")),
                    Paragraph(Text("The weighted signed flips square to q times the identity after summing their pairwise anticommutators. Splitting the opposite-parity columns into the interior and exterior gives the exterior Gram as the interior defect. Switching makes the interior weights unsigned, and separation makes the two cross blocks zero. Consequently Z times its transpose is the block diagonal matrix with blocks B sub C and B sub D. Taking determinants gives the displayed product.")),
                    Paragraph(Text("Over the integer polynomial ring in the nine coordinates, take the weights to be the nine indeterminates. For two nonzero rooted cofactors, the product identity forces each irreducible polynomial factor to have the same multiplicity parity in the two cofactors. This gives a test for proposed placements using their actual coordinate-labelled internal edges. The Gram and determinant identities also apply when some or all weights specialize to zero.")),
                    Paragraph(Text("For the following paper deduction, suppose each induced support is connected and attains the ambient norm for every positive weight. For a component with full biadjacency M, Perron simplicity gives generic corank one for the full defects K₀ = qI − MMᵀ and K₁ = qI − MᵀM. Over the rational polynomial ring take primitive kernel vectors p₀ and p₁. The intertwiners Mᵀp₀ = a p₁ and Mp₁ = b p₀ have polynomial factors by primitivity, and ab = q. The rank-nine quadratic q is irreducible, so rescaling gives a and b equal to one and q in some order.")),
                    Paragraph(Text("Write the adjugates as f₀p₀p₀ᵀ and f₁p₁p₁ᵀ. The factors f₀ and f₁ are polynomials by primitivity. The adjugate traces agree since the full defects have the same characteristic polynomial. Also a² p₁ᵀp₁ = q p₀ᵀp₀, so f₀/f₁ = q/a². Each rooted cofactor is its corresponding f times a nonzero square of a root entry. Exactly one parity therefore has odd q-multiplicity. The square identity forces this parity to agree for the two components.")),
                    Paragraph(Text("Reversing a weight tᵢ conjugates either full defect by the vertex sign (−1)ˣⁱ. The sign change of a primitive kernel generator is that conjugation times a rational unit of square one. The two parity generators give the same unit because Mᵀp₀ = a p₁ and a is invariant under the sign change. These nine units determine a cube vertex. A translation toggles the corresponding bits of the vertex, and a coordinate permutation permutes them. The shared units give the same transformation even when the automorphism exchanges parities. Consequently every ambient automorphism stabilizing the support fixes this vertex.")),
                    Paragraph(Text("The problem reference is Zhen-Mu Hong, Zi-Yi Wu and Zheng-Jiang Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, Section 7, Problem 2. The weighted cofactor identity is a repository derivation for the separated balanced cubic branch. The question about f₂(Q₉) remains open. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        []));

    private static Formula CallDet(Formula argument) =>
        new Formula.FunctionCall(FormulaIdentifier.Create("det"), [argument]);
}
