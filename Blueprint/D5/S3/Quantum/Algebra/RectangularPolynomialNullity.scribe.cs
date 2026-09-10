using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class RectangularPolynomialNullityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rectangular support bounds the dimension of a polynomial subspace with conditional derivative closure.",
        H("Rectangular Polynomial Nullity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("stationary-rectangular-nullity-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/RectangularPolynomialNullity.stationary_rectangular_nullity_bound"),
                H("The rectangular dimension bound"),
                StatementSource.FromAuthor(NullityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let K be any field of characteristic zero, sigma any finite type, " +
                        "and a a function from sigma to the natural numbers. Let L be a " +
                        "finite-dimensional K-linear subspace of MvPolynomial sigma K. " +
                        "Suppose every constant polynomial C(b) belonging to L has b equal " +
                        "to zero. Suppose also that every partial derivative of a member p " +
                        "of L belongs to L whenever the constant coefficient of p vanishes. " +
                        "Finally, for every p in L, every exponent d in its support, and " +
                        "every i in sigma, assume d(i) is at most a(i). Then the dimension " +
                        "of L is at most Finset.sup univ a. This is the finite supremum " +
                        "of the natural numbers a(i), with value zero for an empty sigma.")),
                    Paragraph(Text(
                        "If this supremum is zero, all a(i) vanish. Every supported " +
                        "exponent is then zero, so every polynomial in L is constant. " +
                        "The exclusion of nonzero constants gives L equal to the zero " +
                        "subspace. This argument also covers an empty sigma. If the " +
                        "supremum is positive and the dimension of L is less than two, " +
                        "the bound follows directly from the natural-number inequalities.")),
                    Paragraph(Text(
                        "In the remaining case, conditional polynomial rigidity supplies " +
                        "one nonzero function c from sigma to K such that every member " +
                        "of L is F(ell) for a univariate polynomial F over K, where ell " +
                        "is the sum of c(j) times X(j). Choose i with c(i) nonzero. " +
                        "For each natural number n, the coefficient of the pure monomial " +
                        "X(i) to the power n in F(ell) equals the coefficient of degree n " +
                        "in F times c(i) to the power n. The multinomial coefficient " +
                        "formula and the expansion of polynomial evaluation give this identity.")),
                    Paragraph(Text(
                        "For nonzero F, its leading coefficient and c(i) are nonzero. " +
                        "Thus the pure monomial of degree F.natDegree occurs in F(ell), " +
                        "and the rectangular support condition bounds F.natDegree by a(i). " +
                        "The zero polynomial satisfies the same natural-degree bound. " +
                        "The coefficient identity also shows that evaluation at ell is " +
                        "injective, by cancelling each nonzero power of c(i).")),
                    Paragraph(Text(
                        "Take the inverse image S of L under this evaluation map. " +
                        "It is a linear subspace of the univariate polynomials of degree " +
                        "less than a(i) plus one. It is proper: that ambient space " +
                        "contains one, whereas S cannot contain one because evaluation " +
                        "sends one to the forbidden nonzero constant in L. The monomial " +
                        "basis gives the ambient space dimension a(i) plus one, so S " +
                        "has dimension at most a(i). Evaluation restricts to a linear " +
                        "bijection from S to L: injectivity was proved above, and " +
                        "surjectivity is the common-linear-form representation. Hence " +
                        "L has the same dimension as S, bounded by a(i) and therefore " +
                        "by the finite supremum of a."))),
                DescribeRole.Theorem))));

    private static Formula NullityFormula()
    {
        Formula field = F.Id("K");
        Formula variables = F.Id("sigma");
        Formula a = F.Id("a");
        Formula subspace = F.Id("L");
        Formula p = F.Id("p");
        Formula b = F.Id("b");
        Formula i = F.Id("i");
        Formula d = F.Id("d");
        Formula ring = Call("MvPolynomial", variables, field);
        Formula excludesConstants = Seq(
            Forall, Sp, b, Colon, Sp, field, Comma, Sp,
            Call("C", b), Sp, InMacro, Sp, subspace, Sp, Implies, Sp,
            b, Sp, Eq, Sp, D(0));
        Formula conditionalClosure = Seq(
            Forall, Sp, p, Sp, InMacro, Sp, subspace, Comma, Sp,
            Call("constantCoeff", p), Sp, Eq, Sp, D(0), Sp, Implies, Sp,
            Forall, Sp, i, Sp, InMacro, Sp, variables, Comma, Sp,
            Call("pderiv", i, p), Sp, InMacro, Sp, subspace);
        Formula rectangularSupport = Seq(
            Forall, Sp, p, Sp, InMacro, Sp, subspace, Comma, Sp,
            Forall, Sp, d, Sp, InMacro, Sp, Call("support", p), Comma, Sp,
            Forall, Sp, i, Sp, InMacro, Sp, variables, Comma, Sp,
            d, Open, i, Close, Sp, Leq, Sp, a, Open, i, Close);

        return Disp(Seq(
            Forall, Sp, field, Comma, Sp, variables, Colon, Sp, F.Id("Type"), Comma, Sp,
            Call("Field", field), Comma, Sp, Call("CharZero", field), Comma, Sp,
            Call("Fintype", variables), Comma, Esc,
            Forall, Sp, a, Colon, Sp, variables, Sp, To, Sp, F.Id("Nat"), Comma, Esc,
            Forall, Sp, subspace, Colon, Sp, Call("Submodule", field, ring), Comma, Sp,
            Call("FiniteDimensional", field, subspace), Comma, Esc,
            Open, excludesConstants, Close, Sp, Implies, Esc,
            Open, conditionalClosure, Close, Sp, Implies, Esc,
            Open, rectangularSupport, Close, Sp, Implies, Esc,
            Call("finrank", field, subspace), Sp, Leq, Sp,
            Call("FinsetSup", Call("univ", variables), a), Dot));
    }
}
