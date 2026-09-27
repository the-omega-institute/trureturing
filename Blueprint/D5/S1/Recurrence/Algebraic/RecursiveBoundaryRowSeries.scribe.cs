using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class RecursiveBoundaryRowSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every boundary sequence over a commutative ring determines a unique recursive array "
            + "whose rows have exact formal composition and finite coefficient formulas.",
        H("Recursive Arrays from Arbitrary Boundaries"),
        Blocks(
            Paragraph(Text(
                "Let R be a commutative ring and a a sequence indexed by the natural numbers. "
                    + "All indices start at zero. The first column is T(n,0)=a(n), and the "
                    + "successor rule is T(n,k+1)=T(n+1,k)-sum over 0<=j<=k of "
                    + "T(n,j)a(k-j). This constructs each column from earlier columns. "
                    + "The boundary entries may vanish, and the zeroth row is unrestricted. "
                    + "The coefficient ring can in particular be the rationals or the complex numbers.")),
            Node("array", "The recursive array",
                "array(a,n,k) is defined by the boundary at k=0 and the successor rule at "
                    + "k+1. The recursive calls have strictly smaller column index. The finite "
                    + "index type Fin(k+1) includes both endpoints j=0 and j=k.",
                DescribeRole.Definition),
            Node("IsExtension", "The boundary and recurrence equations",
                "IsExtension(a,T) asserts that T has first column a and satisfies the successor "
                    + "rule at every pair of natural indices. Replacing a(k-j) by T(k-j,0) "
                    + "and moving the sum to the other side gives the equivalent row-successor equation.",
                DescribeRole.Definition),
            Node("row", "An actual row series",
                "row(T,n) has coefficient T(n,k) at degree k. It is the generating series "
                    + "of the given array, defined independently of the composition formula.",
                DescribeRole.Definition),
            Node("source", "The normalized boundary series",
                "source(a)=1+X*mk(a), where mk(a) has coefficient a(k) at degree k. "
                    + "Thus the constant coefficient of source(a) is one for every a.",
                DescribeRole.Definition),
            Node("reciprocal", "The formal reciprocal",
                "reciprocal(a)=invOfUnit(source(a),1) is the two-sided multiplicative inverse "
                    + "of source(a). The inverse uses its unit constant coefficient and is "
                    + "defined over an arbitrary commutative ring.",
                DescribeRole.Definition),
            Node("inner", "The substitution series",
                "inner(a)=X*reciprocal(a) has constant coefficient zero. Substitution "
                    + "of this series into an arbitrary outer formal series is therefore defined.",
                DescribeRole.Definition),
            Node("tail", "A shifted boundary series",
                "tail(a,n) has coefficient a(n+j) at degree j. The starting row n is arbitrary.",
                DescribeRole.Definition),
            Node("result", "Unique extension and exact row formulas",
                "For every a, array(a) satisfies IsExtension(a), and every other extension "
                    + "equals it. Write I=reciprocal(a), Y=inner(a), and R(n)=row(array(a),n). "
                    + "For every n and N, R(n)=I*sum over 0<=j<N of C(a(n+j))*Y^j "
                    + "+Y^N*R(n+N), where C embeds a coefficient as a constant series. "
                    + "The remainder is divisible by X^N, including N=0. Consequently "
                    + "R(n)=I*tail(a,n).subst(Y), where subst means formal composition, "
                    + "and array(a,n,k)=sum over 0<=j<=k of "
                    + "a(n+j)*coeff(k-j)(I^(j+1)). Uniqueness gives the same two formulas "
                    + "for any array with the stated boundary and recurrence. "
                    + "To prove the identities, coefficient convolution first gives "
                    + "source(a)*R(n)=C(a(n))+X*R(n+1). Finite iteration yields the expansion. "
                    + "At degree k, taking N=k+1 makes the remainder coefficient zero. "
                    + "All identities concern formal coefficients and require no analytic convergence.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create("recursive-boundary-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),
            role);
}
