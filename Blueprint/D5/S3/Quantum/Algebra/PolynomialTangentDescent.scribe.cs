using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PolynomialTangentDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A polynomial with gradient parallel to a fixed nonzero vector depends on one linear form.",
        H("Polynomial Tangent Descent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("polynomial-tangent-descent"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/PolynomialTangentDescent.tangent_descent"),
                H("Dependence on a linear form"),
                StatementSource.FromAuthor(TangentDescentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let K be a field of characteristic zero, sigma a finite set of variables, "
                        + "c a nonzero K-valued function on sigma, and p a polynomial over K in "
                        + "those variables. Write ell for the sum of c(i) times X(i). The partial "
                        + "derivatives of p satisfy c(j) times partial_i p equals c(i) times "
                        + "partial_j p for every i and j if and only if p equals F(ell) for some "
                        + "univariate polynomial F over K. Products by c(i) denote scalar actions.")),
                    Paragraph(Text(
                        "Choose j with c(j) nonzero. Replace X(j) by the inverse of c(j) times "
                        + "the difference between X(j) and the sum of c(i)X(i) over i different "
                        + "from j, and fix the other variables. The inverse substitution replaces "
                        + "X(j) by ell. The product rule, applied inductively to a polynomial, "
                        + "shows that each nonpivot partial derivative after substitution is the "
                        + "substitution of partial_i p minus c(i)/c(j) times partial_j p. "
                        + "The assumed identities make all these derivatives zero.")),
                    Paragraph(Text(
                        "If a monomial contains a nonpivot variable with positive exponent, "
                        + "its coefficient contributes to a unique coefficient of that partial "
                        + "derivative, multiplied by the exponent. Characteristic zero makes "
                        + "this multiplier nonzero. Consequently no such monomial has a nonzero "
                        + "coefficient. The substituted polynomial is therefore F(X(j)), and "
                        + "applying the inverse substitution gives p = F(ell). Conversely the "
                        + "univariate chain rule gives partial_i F(ell) = c(i) F'(ell), which "
                        + "implies the stated identities.")),
                    Paragraph(Text(
                        "The polynomial p may be zero or constant, and individual coefficients "
                        + "c(i) may vanish. No order or positivity is required. A nonzero c "
                        + "already ensures that a pivot exists, so no separate assumption that "
                        + "sigma is nonempty is needed."))),
                DescribeRole.Theorem))));

    private static Formula TangentDescentFormula()
    {
        Formula field = F.Id("K");
        Formula variables = F.Id("sigma");
        Formula c = F.Id("c");
        Formula p = F.Id("p");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula polynomial = F.Id("F");
        Formula ring = Call("MvPolynomial", variables, field);
        Formula linearForm = Seq(Sum, Underscore, Grp(i), Sp,
            c, Open, i, Close, Sp, Cdot, Sp, F.Id("X"), Underscore, Grp(i));
        Formula left = Seq(Forall, Sp, i, Comma, Sp, j, Sp, InMacro, Sp, variables,
            Comma, Sp, c, Open, j, Close, Sp, Cdot, Sp,
            Call("pderiv", i, p), Sp, Eq, Sp,
            c, Open, i, Close, Sp, Cdot, Sp, Call("pderiv", j, p));
        Formula right = Seq(Exists, Sp, polynomial, Colon, Sp, Call("Polynomial", field),
            Comma, Sp, p, Sp, Eq, Sp, Call("aeval", linearForm, polynomial));

        return Disp(Seq(
            Forall, Sp, field, Comma, Sp, variables, Colon, Sp, F.Id("Type"), Comma, Sp,
            Call("Field", field), Comma, Sp, Call("CharZero", field), Comma, Sp,
            Call("Fintype", variables), Comma, Sp,
            c, Colon, Sp, variables, Sp, To, Sp, field, Comma, Sp,
            c, Sp, Neq, Sp, D(0), Comma, Sp, p, Colon, Sp, ring, Comma, Esc,
            Open, left, Close, Sp, Iff, Sp, Open, right, Close, Dot));
    }
}
