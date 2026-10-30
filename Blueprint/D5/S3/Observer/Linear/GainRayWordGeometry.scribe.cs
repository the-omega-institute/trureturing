using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class GainRayWordGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three source directions in every mixed word", H("Three source directions in every mixed word"), Blocks(
            Describe.Lean(DescribeId.Create("gain-ray-owner-action-m-shape"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayWordGeometry.action_m_shape"),
                H("The native M matrix"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The false native action is exactly the real matrix [[0,1],[1,1]]. This original matrix identity is used in the critical source-partner and word-plane proofs."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-owner-action-j-shape"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayWordGeometry.action_j_shape"),
                H("The native J matrix"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The true native action is exactly the real matrix [[0,1],[1,0]]. This original matrix identity is used in the critical source-partner and word-plane proofs."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-owner-m-power-coordinates"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayWordGeometry.m_power_coordinates"),
                H("Positive Fibonacci coordinates for M powers"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every power M^(k+1) has the form a*I+b*M with a nonnegative and b strictly positive. These original power coordinates supply the positive Perron-line scalar in the complete-target partner construction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-owner-first-switch-independent"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayWordGeometry.first_switch_independent"),
                H("Independent first-switch matrices"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either first action a and every positive k, the matrices I, action a and action(!a)*(action a)^k are linearly independent over the reals. The complete-target proof uses this original result to identify every three-dimensional mixed cumulative plane."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-owner-switch-decomposition"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayWordGeometry.switch_decomposition"),
                H("The first switch in a mixed word"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every literal Boolean word containing both native actions has a positive initial block replicate(k,a), followed by !a and an arbitrary tail. This original decomposition is used without a later-letter classification."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-owner-acquisition-unit"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayWordGeometry.acquisition_unit"),
                H("Invertible literal cumulative matrices"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every original cumulative acquisition matrix is a unit. The signed determinant of its integer native word is a power of minus one. This original invertibility supplies the legal conjugated-transpose partner operations."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-first-switch-generators"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayWordGeometry.first_switch_generators_mem"),
                H("The first switch supplies three actual prefix generators"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every Boolean word w, first action a, positive initial block length k and tail r with w=replicate(k,a)++(!a::r), the cumulative span contains I, action a and action(!a)*(action a)^k. They occur at actual read indices 0, 1 and k+1. This extracted prefix argument is consumed both by the mixed cumulative-span lower bound and by the complete-target first-switch plane argument."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-gainraywordgeometry-mixed-cumulative-span"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayWordGeometry.mixed_cumulative_span"),
                H("Every mixed cumulative trajectory spans at least three dimensions"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every chronological Boolean word w containing both false and true, the real span of acquisition(take i w), for all initial-inclusive i in Fin(length(w)+1), has dimension at least three. Both switch orientations are included. If M occurs first and its initial block has positive length k, the cumulative matrices include I,M,J*M^k. The existing frozen Fibonacci block identity gives M^k=a*I+b*M with a nonnegative and b positive; the two off-diagonal entries of J*M^k differ by b. If J occurs first, the trajectory includes I,J and M*J^k. According to k modulo two, the third matrix is M or M*J, each outside the span of I,J. The proof uses the actual cumulative prefixes of the same literal word."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-word-adjacent-nonproportional"), DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayWordGeometry.cumulative_not_proportional_adjacent"), H("Consecutive cumulative matrices are not proportional"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every chronological Boolean word w, every i less than its action length, and every real c, acquisition(take(i+1,w)) differs from c times acquisition(take(i,w)). Every native cumulative matrix is invertible by its signed determinant. Proportionality would force the next M or J to be scalar, contrary to its off-diagonal entry one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-word-proportionality-card"), DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayWordGeometry.cumulative_proportionality_card"), H("A matrix ray occupies at most half the read positions rounded up"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every word w and every real auxiliary matrix L, the number of initial-inclusive indices i whose actual cumulative matrix equals c*L for some real c is at most (length(w)+2)/2 using natural division. No two such indices are consecutive. The map from such an index to its natural value divided by two is injective, and its image lies below this ceiling. The statement includes L=0 and every pure or mixed word."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gain-ray-word-proportionality-card-even"), DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayWordGeometry.cumulative_proportionality_card_even"), H("An M action excludes the maximal alternating matrix ray"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every natural m, every legal Boolean word w of action length 2*m containing M, and every real matrix L, at most m of the 2*m+1 initial-inclusive cumulative matrices are proportional to L. Select the even-starting action pair containing an M. Its three cumulative matrices are pairwise nonproportional: only J*J among the four two-action products is scalar. Group these three positions together and pair the other adjacent positions. Each group contains at most one member of any matrix ray, giving m groups. This bound is consumed by the critical scalar-span theorem."))), DescribeRole.Theorem))));
}
