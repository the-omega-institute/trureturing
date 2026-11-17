using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class AffineBallRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An entire extreme affine sphere determines a same-dimensional enclosing affine ball.",
        H("Affine ball rigidity from an extreme sphere"), Blocks(
        Describe.Lean(DescribeId.Create("unique-affine-ball-center"),
            DeclarationHandle.Create("D5/S3/Geometry/AffineBallRigidity.center_eq_of_ball_eq"),
            H("Uniqueness of the affine center"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("Equal entire affine closed unit balls have equal centers, even if either linear parametrization has a kernel and the source dimensions differ. Compactness is supplied by the finite dimensional first source. Reflection about either center preserves the common set. Composing the two reflections translates a maximizer of any real continuous linear functional by twice the difference of centers. Maximality bounds this difference by zero. A norming dual functional for the center difference forces its norm to vanish.")))),
        Describe.Lean(DescribeId.Create("extreme-sphere-ball-rigidity"),
            DeclarationHandle.Create("D5/S3/Geometry/AffineBallRigidity.eq_of_subset_of_extreme_sphere"),
            H("Equality of nested affine balls"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("Let E be a finite dimensional real normed space and V a real normed space. Let A and B be injective continuous real linear maps from E to V, and let c and d be points of V. Suppose the image of the entire closed unit ball under x mapped to c plus A x is contained in the corresponding image under d plus B x. The latter ball is contained in a set K. If every point c plus A x with x on the unit sphere is an extreme point of K, the two entire affine balls coincide. K need not itself be a ball or have the dimension of E.")),
            Paragraph(Text("Ball inclusion gives inclusion of linear ranges: subtract the image of zero from the image of a unit vector and then rescale. Injectivity and the common finite dimensional source make the two ranges equal. Thus every point y of the larger ball can be written c plus A v. If the norm of v exceeded one, the point c plus A of v divided by its norm would lie both on the extreme sphere and strictly between c and y. Extremity makes that sphere point equal c. Injectivity then contradicts its unit source norm. Hence v lies in the closed unit ball.")),
            Paragraph(Text("The finite dimension and injectivity conditions carry the range equality. A lower dimensional disc can lie inside a larger ball, so mere containment with an extreme boundary does not replace these hypotheses. The theorem is an affine convexity statement; it supplies no manifold or quantum reconstruction claim.")),
            Paragraph(Text("For the Euclidean three-space E, the real linear maps v mapped to (v, t times the first coordinate of v) into the product normed space E times R are injective of rank three. Distinct real parameters give distinct ranges. Their unit-ball images are contained in the images under twice the maps. Rigidity therefore rules out extremity of the entire smaller sphere in the doubled ball. Scaling by a positive real number a gives the estimate a times the norm of v at most the norm of the scaled graph image. This example allows the actual range to move and records the dependence of a lower estimate on rescaling; it is not a realization of the original cone assumptions."))))) ));
}
