using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class SectionPositiveLiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive functionals on a unital real section of native real symmetric or complex Hermitian matrices have PSD lifts; one lift characterizes simultaneous finite pure exclusions on the whole original cone.",
        H("Positive lifts of whole-section effects"),
        Blocks(
            Paragraph(Text("Let F be the real or complex field, let J be any finite index type with decidable equality, and let H be the real vector space of Hermitian J by J matrices over F. For the real field these are precisely symmetric matrices. The inner product is Re tr(AB), using the existing HermitianMat structure and its compatible Frobenius norm. L is an arbitrary real linear subspace. The unital conclusions assume I belongs to L. No Jordan closure, chosen pure configuration, codimension restriction or ROG hypothesis is needed for the effect lift and its geometry. The empty ambient index also remains valid for these results; the intended normalized input has cardinality n at least one.")),
            Definition("native-rank-one", "rankOne", "Native rank one matrices",
                "For every vector v in F to the power J, rankOne(v) is vv*, with star the transpose over the reals and conjugate transpose over the complexes. The zero vector is allowed here. Complex rank one is retained over the complex field."),
            Definition("whole-section-cone", "cone", "The entire original positive cone",
                "cone(L) is the pointed cone on the real subtype L consisting of every X in L whose underlying native matrix is PSD."),
            Definition("section-trace-unit", "unit", "The trace unit",
                "unit(L) is the real linear functional on all of L taking X to its real trace."),
            Definition("whole-proper-interval", "Proper", "Whole-cone proper effects",
                "For any real linear f from L to the reals, Proper(f) means that 0 <= f(X) <= tr(X) for every X in the entire cone(L), including zero and all unnormalized positive matrices. No ambient positive contraction representative is required."),
            Definition("same-unit-lifts", "lifts", "All same-unit positive lifts",
                "lifts(L) consists exactly of all M in H such that M is PSD and M-I belongs to the real trace orthogonal complement of L. Thus it is (I+L-perp) intersect PSD."),
            Theorem("outer-product-positive", "rankOne_nonneg", "Positivity of the native outer product",
                "For every native vector v, rankOne(v) is PSD. This applies the existing Matrix.posSemidef_vecMulVec_self_star inside the effect and ROG proofs."),
            Theorem("trace-quadratic-reading", "pair_rankOne", "Trace pairing is the native quadratic reading",
                "For every A in H and every native vector v, the real number <A,rankOne(v)> embedded into F equals v*Av. The original field is used throughout. This identity is consumed when testing positivity of the global extension and when computing the confirming and zero readings."),
            Theorem("positive-section-functional-lift", "positive_functional_psd_lift", "Every original positive functional has a PSD lift",
                "For every L containing I and every real linear f:L to R that is nonnegative on every original X in cone(L), there exists E in H with E PSD and f(X)=<E,X> for every X in L. Ambient majorization ranges over every Hermitian Y, not just Y in L: the sum of absolute eigenvalues of -Y gives t>=0 with Y+tI PSD. Riesz positive extension applies to the original partial functional. Finite dimensional continuity and the existing trace inner product give E; testing every ambient vv*, including those outside L, proves E PSD."),
            Theorem("singular-rank-one-deflation", "rank_one_deflation", "Deflation below the same positive matrix",
                "For every PSD M and every native vector v satisfying v*Mv=1, E=Mvv*M is PSD and M-E is PSD. No invertibility or unit length of v is assumed in this theorem. With p=vv* and Q=I-pM, the scalar identity gives pMp=p and Q*MQ=M-MpM. PSD congruence proves the complement, including singular M. The theorem is consumed by common_original_effect_lift; its upper bound is M."),
            Theorem("common-finite-original-effect", "common_original_effect_lift", "One original effect exactly matches one common lift",
                "For every unital L, every native vector v with v*v=1 and vv* in L, every natural m, and every list w:Fin(m) to F to the power J with each w(j)w(j)* in L, the following are equivalent. There exists one real linear f on all of L with Proper(f), f(vv*)=1, and f(w(j)w(j)*)=0 for every j. There exists one M in lifts(L) with v*Mw(j)=0 for every j. The theorem is stronger than the normalized-pure-list clause because the rejected vectors need not have unit length. It includes the empty list and repeated entries. Lifting f and unit-f gives PSD E,F and M=E+F. The zero quadratic values force Fv=0 and Ew(j)=0. Conversely use E=Mvv*M and the complement M-E: on every original positive X their nonnegative readings sum to tr(X), giving whole-cone properness. The scalar readings are one at vv* and |v*Mw(j)| squared at each rejected rank one point. No inequality E<=I is used."),
            Theorem("lift-set-geometry", "lift_geometry", "Compact convex geometry and exact real affine dimension",
                "For every L containing I, lifts(L) is nonempty, compact and convex. Every M in it has tr(M)=card(J). Its affine span has direction exactly L-perp, and hence its real affine dimension is real finrank(L-perp). I supplies nonemptiness. Orthogonality to I gives the trace equation; closedness and the existing PSD trace bound place the set in the compact order interval [0,card(J) I]. For each N in L-perp, ambient majorization gives t>=0 and a=1/(t+1)>0 with I+aN PSD. The direction of the affine span contains aN and therefore N, proving fullness without assuming it."),
            Paragraph(Text("These statements supply the same-unit effect lift, deflation and geometry clauses of QuantumVI Lemma 96.2. SectionROGFrame treats the whole pure carrier and the full frame using the actual ROG hypothesis. Arbitrary-original-unit support restriction and determinant normalization from 93.2/94.2 remain an outside mathematical bridge. No original arbitrary-unit normalization, full Z0, classification, PRE or completion of section 97 is asserted. The separate QuantumVII facet theorem is outside this result. Literature priority is not asserted; the existing Physlib trace-space and order port and pinned Mathlib Riesz extension are reused directly.")))));

    private static DocumentBlock.Describe Definition(string id, string declaration, string title, string text) =>
        Entry(id, declaration, title, text, DescribeRole.Definition);
    private static DocumentBlock.Describe Theorem(string id, string declaration, string title, string text) =>
        Entry(id, declaration, title, text, DescribeRole.Theorem);
    private static DocumentBlock.Describe Entry(string id, string declaration, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/SectionPositiveLift." + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
