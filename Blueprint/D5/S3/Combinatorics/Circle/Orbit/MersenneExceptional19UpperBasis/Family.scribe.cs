using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis;

internal sealed class FamilyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Selected literal exceptional19 integer-basis problem: exact physical family.",
        H("Original labels and actual zero indicators"),
        Blocks(
            Describe.Lean(DescribeId.Create("card-upperIndex"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Family.card_upperIndex"),
                H("card upperIndex"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The selected family consists of the literal G, F and H upper endpoints and the eight terminal indicators. Its cardinality is 3d-1. Actual affine endpoint bounds and exact triple totals prove literal zero membership, including the one disjoint union of the two exceptional triples. No selected spanning conclusion is inferred here."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("selected-literal-zero"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Family.selected_literal_zero"),
                H("selected literal zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The selected family consists of the literal G, F and H upper endpoints and the eight terminal indicators. Its cardinality is 3d-1. Actual affine endpoint bounds and exact triple totals prove literal zero membership, including the one disjoint union of the two exceptional triples. No selected spanning conclusion is inferred here."))), DescribeRole.Theorem),

            Paragraph(Text("For every natural r, including zero, put d=18r+12, B=2^d, n=3d and t=(2^d-1)(2^(d+1)-3). The ambient module is the integer-valued functions on the original Fin n. The weighted-sum map is the existing integerWeightedSum, whose coefficients are literally SourceWidth.actualSource n t i. The indicator is the existing coefficient-one row of a finite subset. There is no coordinate quotient, sign change, rational replacement or extra rank assumption in the intended basis statement.")),
            Paragraph(Text("The selected G indicators are R_(B/2+2^j), j=1,...,d-4, followed by R_(3B/4) and R_(B/2). The F indicators are R_(B-b-2^j), j=2,...,d-3, followed by R_(3B/4-b). The H indicators are R_(B/2+a-2^j), j=2,...,d-3. Here a=(2B-3)/19, b=(3B+5)/19 and R_M is the actual three-block binary indicator chi(M+b,M,M-a). UpperIndex retains these occurrences separately. Its cardinality is (d-2)+(d-3)+(d-4)+8=3d-1. No claim of distinctness is needed to define the family; its eventual basis theorem must imply distinctness.")),
            Paragraph(Text("The eight terminal actual indicators, in their source order, are T0,T1,T_(d-2), T_(d-3) union T_(d-1), R_a,R_(3B/8),chi(Q),chi(8Q), with Q=(B^2+B+1)/19. Each Tj consists of the three ORIGINAL labels j,d+j,2d+j. The union is disjoint and is ONE six-coordinate actual indicator. Its zero sum follows by cancellation of the two opposite triple totals; neither of those two triples is separately asserted to be zero. Empty subsets are allowed by the ambient literal-zero definition. The selected family uses no empty-set exception or r>0 premise; d>=12 covers all boundary indices at r=0 as well.")),
            Paragraph(Text("selected_literal_zero uses only sealed physical APIs: the upper endpoint range component of gPoint_data, fPoint_data and hPoint_data, affine_zero, triple_total, triples_disjoint and q_zero. selectedKernelRow turns these very indicators into elements of the actual integer kernel. The selected rows retain every original physical label. The exact original-source relation actualSource=19(B-1)*primitive is reused from the owning Weights theorem.")),
            Paragraph(Text("The intended conclusion is existence of a Basis indexed by UpperIndex of the original integerWeightedSum kernel whose underlying functions are exactly row(selectedMask r k). It has not been proved in this delivery. In particular, the earlier all-zero-family span theorem does not prove that this selected subfamily spans. No determinant, spanning or certificate premise is added to disguise that missing inference.")),
            Paragraph(Text("For the associated zero-sum hypergraph, such a basis would give exactly n-1 actual edges generating every integral relation among the original weights. Since -3a+2b=1, the primitive weight homomorphism is surjective. A genuine selected-basis proof would identify the free abelian quotient by these edges with Z, retaining torsion control. Permutations preserving the complete literal zero family then act on this quotient; transporting this action to weight relations is the group-action relevance. The selected set itself is not asserted to be permutation invariant, and none of these consequences is claimed as a new compiled theorem here.")),
            Paragraph(Text("Provenance is the immutable ordinary upper-only brief and determinant answer, plus the completed ordinary review conclusions. They are fallible mathematical input, not Lean evidence. The worker has repository prior and belongs to the same model family; no sterile-prior, diversity, novelty or independent kernel-review claim is made."))), []));
}
