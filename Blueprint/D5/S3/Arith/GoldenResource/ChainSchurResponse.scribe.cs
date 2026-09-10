using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class ChainSchurResponseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/ChainSchurResponse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The chain Schur response has explicit linear coefficients and a quadratic error bound.",
        H("Chain Schur Response"),
        Blocks(
            Paragraph(Text("Let n be any natural number and m=n+1. The matrix H(m) has "
                + "diagonal four and adjacent entries minus one. Put A=H(m) direct sum H(m). "
                + "The two rows of B select the first vertex of the first and second chains, "
                + "respectively. The hidden spatial matrix Gh is the hidden submatrix of "
                + "G(n,k,b): it is diagonal with entry k everywhere except at the last vertex "
                + "of the first chain, where the entry is k-b. All parameters k,b,s,u are real. "
                + "Here u denotes the spatial perturbation parameter. Put E=u Gh-s I and "
                + "Q=(A+E) inverse. An inverse is the nonsingular matrix inverse; Unit means "
                + "invertibility. For the first identity alone, A and E may be arbitrary real "
                + "square matrices on any finite decidable index type, including the empty type.")),
            Paragraph(Text("Define w=H(m) inverse applied to the first unit vector, "
                + "z=1+sum of the squares of the coordinates of w, t=w(n), and eta=t squared/z. "
                + "Thus the vector square is Euclidean. The recurrence d has d(0)=1, d(1)=4, "
                + "and d(j+2)=4d(j+1)-d(j). Write P=diag(1,0). The matrix coefficients are "
                + "Z=I+(B A inverse)(A inverse B transpose) and "
                + "C=k I+(B A inverse) Gh (A inverse B transpose). The effective matrix "
                + "T is the actual product Z inverse times C. Define "
                + "S(s,u)=(1+ku-s)I-B Q B transpose and "
                + "R(s,u)=-B A inverse E A inverse E Q B transpose. "
                + "Matrix norms below are the maximum absolute row-sum norm, also for "
                + "rectangular matrices. Let F=norm(B) norm(A inverse) squared norm(B transpose) "
                + "and L=2 norm(B) norm(A inverse) cubed norm(B transpose). "
                + "These constants depend on n, and not on s or u.")),
            Describe.Lean(
                DescribeId.Create("resolvent-exact-first-order"),
                DeclarationHandle.Create(Prefix + "inverse_first_order"),
                H("The iterated inverse identity"),
                StatementSource.FromAuthor(Disp(ImpliesFormula(
                    And(Call("Unit", F.Id("A")), Call("Unit", Add(F.Id("A"), F.Id("E")))),
                    Eq(F.Id("Q"), Add(Sub(Inv(F.Id("A")),
                        Mul(Inv(F.Id("A")), F.Id("E"), Inv(F.Id("A")))),
                        Mul(Inv(F.Id("A")), F.Id("E"), Inv(F.Id("A")),
                            F.Id("E"), F.Id("Q"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inverse-difference identity gives "
                    + "Q=A inverse-A inverse E Q. Substitute this same expression for the "
                    + "last Q on the right once and distribute in the original matrix order. "
                    + "The result is exact for every invertible A and A+E."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-common-mass-coefficient"),
                DeclarationHandle.Create(Prefix + "z_pos"),
                H("A positive common coefficient"),
                StatementSource.FromAuthor(Disp(Lt(D(0), F.Id("z")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every coordinate square is nonnegative, "
                    + "and z is their sum plus one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("endpoint-reciprocal-denominator"),
                DeclarationHandle.Create(Prefix + "endpoint_formula"),
                H("The endpoint transfer"),
                StatementSource.FromAuthor(Disp(Eq(F.Id("t"),
                    new Formula.Fraction(D(1), Call("d", F.Id("m")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The first inverse column of the chain is the "
                    + "reversed recurrence divided by d(m). Its last numerator is d(0)=1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("spectral-coefficient-scalar"),
                DeclarationHandle.Create(Prefix + "Z_eq"),
                H("The spectral coefficient"),
                StatementSource.FromAuthor(Disp(Eq(F.Id("Z"), Mul(F.Id("z"), F.Id("I"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The columns of A inverse B transpose are copies "
                    + "of w supported on separate chains. Symmetry therefore makes their "
                    + "Gram matrix the sum of the coordinate squares times the identity. "
                    + "Adding the visible identity gives Z."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("spatial-coefficient-endpoint-correction"),
                DeclarationHandle.Create(Prefix + "C_eq"),
                H("The spatial coefficient"),
                StatementSource.FromAuthor(Disp(Eq(F.Id("C"),
                    Sub(Mul(F.Id("k"), F.Id("z"), F.Id("I")),
                        Mul(F.Id("b"), Pow(F.Id("t"), 2), F.Id("P")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The constant spatial weight contributes k times "
                    + "the same Gram matrix. The exceptional endpoint subtracts b times "
                    + "t squared from the first visible diagonal entry. Adding the visible "
                    + "k I gives the displayed coefficient."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("effective-principal-diagonal"),
                DeclarationHandle.Create(Prefix + "effective_eq"),
                H("The normalized effective matrix"),
                StatementSource.FromAuthor(Disp(Eq(F.Id("T"),
                    Call("diag", Sub(F.Id("k"), Mul(F.Id("b"), F.Id("eta"))), F.Id("k"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Since z is positive, the inverse of Z is "
                    + "z inverse times the identity. Multiplication by C divides the "
                    + "endpoint correction by z."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("schur-exact-expansion"),
                DeclarationHandle.Create(Prefix + "response_expansion"),
                H("The exact Schur expansion"),
                StatementSource.FromAuthor(Disp(ImpliesFormula(
                    Call("Unit", Add(F.Id("A"), F.Id("E"))), Expansion()))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The hidden mass matrix is positive definite. "
                    + "Insert the iterated inverse identity into S and collect the two "
                    + "linear terms. The Schur subtraction gives R its negative sign. "
                    + "Only invertibility of A+E is assumed here."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("schur-remainder-product-bound"),
                DeclarationHandle.Create(Prefix + "remainder_bound"),
                H("The remainder product bound"),
                StatementSource.FromAuthor(Disp(Le(Norm(R()),
                    Mul(F.Id("F"), Norm(F.Id("Q")), Pow(Norm(F.Id("E")), 2))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply submultiplicativity to every matrix factor. "
                    + "The two copies of E produce its squared norm. This bound holds for "
                    + "all real parameters, even when the nonsingular inverse is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("schur-remainder-bounded-inverse"),
                DeclarationHandle.Create(Prefix + "remainder_bound_of_inverse_bound"),
                H("A bounded inverse"),
                StatementSource.FromAuthor(Disp(ImpliesFormula(Le(Norm(F.Id("Q")), F.Id("M")),
                    Le(Norm(R()), Mul(F.Id("F"), F.Id("M"), Pow(Norm(F.Id("E")), 2)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any real M bounding the inverse norm, "
                    + "replace that norm in the product estimate by M. "
                    + "All the other factors are nonnegative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("schur-first-order-quadratic-error"),
                DeclarationHandle.Create(Prefix + "response_first_order"),
                H("A fixed quadratic error constant"),
                StatementSource.FromAuthor(Disp(ImpliesFormula(
                    And(Call("Unit", Add(F.Id("A"), F.Id("E"))),
                        Le(Mul(Norm(Inv(F.Id("A"))), Norm(F.Id("E"))),
                            new Formula.Fraction(D(1), D(2)))),
                    And(Expansion(), Le(Norm(R()),
                        Mul(F.Id("L"), Pow(Norm(F.Id("E")), 2))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("From Q=A inverse-A inverse E Q and the triangle "
                    + "inequality, norm(Q) is at most norm(A inverse) plus "
                    + "norm(A inverse) norm(E) norm(Q). The smallness condition lets us "
                    + "move the last term to the left and bound norm(Q) by twice "
                    + "norm(A inverse). Substitution in the remainder estimate gives L. "
                    + "This is an exact expansion with a quantitative bound, "
                    + "proved without taking a derivative."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Add(Formula left, Formula right) => Seq(left, Plus, right);
    private static Formula Sub(Formula left, Formula right) => Seq(left, Minus, right);
    private static Formula Pow(Formula value, byte exponent) => Seq(value, Caret, Grp(D(exponent)));
    private static Formula Inv(Formula value) => Seq(value, Caret, Grp(Minus, D(1)));
    private static Formula Norm(Formula value) => Seq(Vert, Sp, value, Vert, Sp);
    private static Formula And(Formula left, Formula right) => Seq(left, Land, Sp, right);
    private static Formula ImpliesFormula(Formula left, Formula right) =>
        Seq(Grp(left), Implies, Sp, Grp(right));

    private static Formula Mul(params Formula[] factors) =>
        factors.Aggregate((left, right) => Seq(left, Cdot, Sp, right));

    private static Formula S(Formula s, Formula u) => Call("S", s, u);
    private static Formula R() => Call("R", F.Id("s"), F.Id("u"));
    private static Formula Expansion() => Eq(S(F.Id("s"), F.Id("u")),
        Add(Add(Sub(S(D(0), D(0)), Mul(F.Id("s"), F.Id("Z"))),
            Mul(F.Id("u"), F.Id("C"))), R()));

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
}
