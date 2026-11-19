using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class EllipsoidShapeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive shapes of entire finite ellipsoids", H("Positive shapes of entire finite ellipsoids"), Blocks(
        Describe.Lean(DescribeId.Create("gram-eq-of-ball-image-eq"),
            DeclarationHandle.Create("D5/S3/Geometry/EllipsoidShape.gram_eq_of_ball_image_eq"), H("The entire ball determines the shape"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("For real finite dimensional inner product spaces, equality of the entire images of the closed unit balls under A and B implies equality of A composed with its adjoint and B composed with its adjoint. The source dimensions may differ and either map may have a kernel. A normalized adjoint vector attains the support value. Equal support values and real polarization determine the positive operator.")))),
        Describe.Lean(DescribeId.Create("metric-pullback"),
            DeclarationHandle.Create("D5/S3/Geometry/EllipsoidShape.metric_pullback"), H("The actual inverse metric"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("If A is injective, the form inner(A x, (A A adjoint) dagger (A y)) equals inner(x,y). The dagger is the existing FiniteMoorePenroseInverse construction. Surjectivity of the adjoint and the first Penrose law give the identity on the source.")))),
        Describe.Lean(DescribeId.Create("metric-ball-image"),
            DeclarationHandle.Create("D5/S3/Geometry/EllipsoidShape.metric_ball_image"), H("The range disc and sphere"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("Membership in the whole ball image is equivalent to membership in the actual range of A A adjoint together with inverse-shape quadratic value at most one. The corresponding sphere uses equality to one. The range condition is essential: without it the inequality describes an ambient cylinder.")))),
        Describe.Lean(DescribeId.Create("comp-dagger-eq-projection"),
            DeclarationHandle.Create("D5/S3/Geometry/EllipsoidShape.comp_dagger_eq_projection"), H("The actual orthogonal projection"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("For every finite operator Q, Q composed with its actual Moore-Penrose inverse equals the auxiliary orthogonal projection onto the actual range. The Penrose laws and the defining orthogonality criterion identify this projection.")))),
        Describe.Lean(DescribeId.Create("gram-dagger-norm-bound"),
            DeclarationHandle.Create("D5/S3/Geometry/EllipsoidShape.gram_dagger_norm_bound"), H("Uniform inverse bound from noncollapse"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("If eta is positive and eta times norm x is at most norm(A x) for every source vector, the operator norm of the actual inverse of A A adjoint is at most the inverse of eta squared. Coercivity is first proved on the actual range. The Penrose projection controls the ambient input, including null directions.")))),
        Describe.Lean(DescribeId.Create("continuous-dagger-of-bound"),
            DeclarationHandle.Create("D5/S3/Geometry/EllipsoidShape.continuous_dagger_of_bound"), H("Continuity of actual inverses"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("A continuous finite dimensional operator family with uniformly bounded actual Moore-Penrose inverses has a continuous inverse family. Bounded inverse subsequences have convergent subsubsequences. All four Penrose laws pass to the limit, and uniqueness identifies each limit with the actual inverse. This proves continuity without assuming a spectral gap or a chosen eigenbasis.")))),
        Describe.Lean(DescribeId.Create("positive-sqrt"),
            DeclarationHandle.Create("D5/S3/Geometry/EllipsoidShape.positiveSqrt"), H("The full ambient positive square root"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("The positive square root is defined through a typed star algebra equivalence from actual operators to real matrices in an orthonormal basis and the pinned matrix continuous functional calculus. It acts on the entire ambient Euclidean space."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("positive-sqrt-spec"),
            DeclarationHandle.Create("D5/S3/Geometry/EllipsoidShape.positiveSqrt_spec"), H("Positive square-root specification"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("For a positive shape, its constructed square root is positive, its square is the original operator, and every positive operator with that square is equal to it. These are direct applications of pinned matrix functional calculus through the typed equivalence.")))),
        Describe.Lean(DescribeId.Create("ball-image-eq-of-gram-eq"),
            DeclarationHandle.Create("D5/S3/Geometry/EllipsoidShape.ball_image_eq_of_gram_eq"), H("Equal shapes give equal entire balls"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("Equal Gram operators imply equal closed-ball images even with unequal source dimensions or ambient null directions. Equal Gram quadratic values give equal adjoint norms. Separation of a point from the compact convex ball image contradicts the equal support bounds.")))),
        Describe.Lean(DescribeId.Create("continuous-positive-sqrt"),
            DeclarationHandle.Create("D5/S3/Geometry/EllipsoidShape.continuous_positiveSqrt"), H("Continuous square roots"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("Every continuous family of positive finite operators has a continuous full ambient positive square root. The finite dimensional operator-matrix equivalence and its inverse are continuous, and the pinned continuous functional calculus square root is continuous on the positive cone.")))),
        Describe.Lean(DescribeId.Create("positive-sqrt-ball-image"),
            DeclarationHandle.Create("D5/S3/Geometry/EllipsoidShape.positiveSqrt_ball_image"), H("The whole ambient square-root image"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("For every A, the image of the entire ambient closed unit ball under the positive square root of A A adjoint equals the entire original ball image under A. The equality includes all null directions and follows from equality of Gram operators.")))),
        Describe.Lean(DescribeId.Create("dagger-positive"),
            DeclarationHandle.Create("D5/S3/Geometry/EllipsoidShape.dagger_positive"), H("Positivity of the actual inverse"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("The actual Moore-Penrose inverse of a positive finite shape is positive on the whole ambient Euclidean space and vanishes in null directions. Adjoint transport of the four Penrose laws and uniqueness yield symmetry; the original positive quadratic form then yields inverse positivity."))))) ));
}
