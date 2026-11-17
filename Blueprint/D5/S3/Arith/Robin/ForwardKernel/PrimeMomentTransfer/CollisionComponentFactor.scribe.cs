using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class CollisionComponentFactorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionComponentFactor.";

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Free collision components and retained distinct-index moments.",
        H("Collision component factorization"),
        Blocks(
            Paragraph(Text(
                "Let B and D be finite types, let A be a commutative real algebra, let ell be any real linear functional on A, "
                + "and let Y map D to A. A retained subset S of B specifies the factors of Y in an assignment sum. "
                + "The remaining indices carry only scalar weights. No positivity, centering, normalization, or independence is needed.")),
            Entry("component-assignment-factorization", "component_assignment_factorization", "Summation over free components",
                "For every finite retained subset S and weight family w indexed by B, sum over all assignments x from B to D "
                + "whose restriction to S is injective, multiplying the product of w(t,x(t)) over all t in B by ell of the product of Y(x(t)) over t in S. "
                + "This equals the product, over t outside S, of the scalar sum of w(t,d) over d, multiplied by the ordered distinct-index moment "
                + "of the retained weight family. The retained family is enumerated by the inverse of Mathlib's equivFin on the finite type S. "
                + "Split each assignment into its restrictions to S and its complement, distribute the finite sums, and then reindex the retained tuple.", DescribeRole.Theorem),
            Entry("collision-component-weight", "collisionComponentWeight", "Merged component weight",
                "For a setoid tau on B, a component c in its quotient and an index d in D, collisionComponentWeight is the product of w(b,d) "
                + "over all b whose tau-class is c.", DescribeRole.Definition),
            Entry("quotient-assignment-factorization", "quotient_assignment_factorization", "Factorization after identifying collision components",
                "Assume that the quotient map from B to its tau-classes is injective on S. "
                + "Sum over assignments x from B to D that are constant on each tau-class and injective on S, with the product of the positional scalar weights "
                + "times ell of the retained Y factors. This equals the product, over quotient classes containing no retained element, "
                + "of the scalar sum of the merged component weight, multiplied by the ordered distinct-index moment of the merged weights of retained classes. "
                + "The retained classes are exactly the image of S under the quotient map and are enumerated by equivFin. "
                + "Every constant assignment descends uniquely to the quotient. Finite fiber products combine its weights, and injectivity of the quotient map "
                + "on S preserves the retained Y product. Summation over the free quotient classes then gives the preceding factorization.", DescribeRole.Theorem),
            Entry("quotient-assignment-zero-retained-collision", "quotient_assignment_zero_of_retained_collision", "Two retained blocks cannot merge",
                "If the quotient map is not injective on S, the same constant-on-components and injective-on-S assignment sum is zero. "
                + "Indeed, two distinct retained elements in one component must have equal assigned values, contradicting injectivity of the assignment on S.", DescribeRole.Theorem),
            Entry("quotient-assignment-absolute-bound", "quotient_assignment_abs_le", "Signed component bound",
                "Let C and H be at least one, let s be nonnegative, and let q and r be natural numbers. Assume that the cardinality of D is at most C*H, "
                + "every scalar weight has absolute value at most one, and there are at most q quotient classes outside the image of S. "
                + "Whenever the quotient map is injective on S, assume the absolute value of the retained merged-weight distinct-index moment is at most C*s^r. "
                + "Then the absolute value of the constrained assignment sum is at most C^(q+1)*H^q*s^r. "
                + "Each free component contributes a scalar sum of absolute value at most C*H. The product of their bounds multiplies the absolute value "
                + "of the retained moment, whose internal sum remains signed. If retained blocks collide, the contribution is zero.", DescribeRole.Theorem))));
}
