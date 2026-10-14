using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class CohnUniformThreeAdicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform three-adic congruence and its obstruction for the explicit Cohn polynomial.",
        H("The Cohn Polynomial: A Uniform Three-Adic Obstruction"),
        Blocks(
            Paragraph(Text(
                "For a natural number q, put m=(q-1)/2 and define the integer polynomial "
                + "P_q(T) as the sum, for 0<=k<=m, of binom(q,2k+1)(-3)^k(1+T)^(m-k). "
                + "Write nu=v_3(q-1). The notation Dvd(a,b) below means integer divisibility. "
                + "The hypotheses range over every q>=7 with q congruent to 1 modulo 6, "
                + "including composite q, and every integer xi divisible by 3.")),
            Describe.Lean(
                DescribeId.Create("cohn-stationary-congruence"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/CohnUniformThreeAdic.cohn_stationary_congruence"),
                H("Uniform congruence of the actual polynomial"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("q"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Forall, Sp, F.Id("xi"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Sp,
                    D(7), Sp, Le, Sp, F.Id("q"), Sp, Rightarrow, Sp,
                    F.Id("q"), Sp, Operatorname, Grp(F.Id("mod")), Sp, D(6), Sp, Eq, Sp, D(1), Sp, Rightarrow, Sp,
                    F.Id("dvd"), Grp(Seq(D(3), Comma, F.Id("xi"))), Sp, Rightarrow, Sp,
                    F.Id("dvd"), Grp(Seq(
                        new Formula.Power(D(3), Add(F.Id("nu"), D(2))), Comma, Sp,
                        new Formula.Subscript(F.Id("P"), F.Id("q")), Grp(F.Id("xi")), Sp,
                        Minus, Sp, new Formula.Power(D(2), Seq(F.Id("q"), Minus, D(1)))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Factorization/cohn1993squareplusthree")),
                Blocks(Paragraph(Text(
                    "The proof identifies P_q(X^2-1) with the imaginary coordinate of "
                    + "(X+sqrt(-3))^q in the quadratic algebra over integer polynomials. "
                    + "Formal differentiation gives the second-order polynomial identity. "
                    + "For c_r=coeff(P_q,r) and d_r=r!c_r, it yields "
                    + "16d_(r+2)=4(q-5r-3)d_(r+1)-(q-2r)(q-2r-1)d_r, with integer signed factors. "
                    + "The sixth power at X=1 gives c_0=2^(q-1) and c_1=0. "
                    + "Unbounded induction proves 3^nu divides d_r for every r>=1, "
                    + "including coefficients beyond the degree. Mathlib's strict factorial "
                    + "valuation bound then gives 3^(nu+2) dividing c_r xi^r for r>=2. "
                    + "Zero coefficients and xi=0 are handled before nonzero valuation formulas. "
                    + "The finite polynomial sum concludes the congruence. "
                    + "This is a polynomial and integer reformulation of Cohn's argument; "
                    + "there is no mathematical priority claim and no finite exponent cutoff."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cohn-polynomial-ne-one"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/CohnUniformThreeAdic.cohn_polynomial_ne_one"),
                H("The value one is excluded"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("q"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Forall, Sp, F.Id("xi"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Sp,
                    D(7), Sp, Le, Sp, F.Id("q"), Sp, Rightarrow, Sp,
                    F.Id("q"), Sp, Operatorname, Grp(F.Id("mod")), Sp, D(6), Sp, Eq, Sp, D(1), Sp, Rightarrow, Sp,
                    F.Id("dvd"), Grp(Seq(D(3), Comma, F.Id("xi"))), Sp, Rightarrow, Sp,
                    new Formula.Not(Seq(
                        new Formula.Subscript(F.Id("P"), F.Id("q")), Grp(F.Id("xi")),
                        Sp, Eq, Sp, D(1)))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Factorization/cohn1993squareplusthree")),
                Blocks(Paragraph(Text(
                    "The actual polynomial congruence is consumed here. LTE at 4, 1 and "
                    + "(q-1)/2 gives v_3(2^(q-1)-1)=nu+1, while P_q(xi)=1 would make "
                    + "the same nonzero integer divisible by 3^(nu+2). "
                    + "In a later Eisenstein reduction, xi=a^2-1 and P_q(xi)=1 are the "
                    + "remaining-exponent input. That reduction, the q=3 branch and the "
                    + "arbitrary-exponent theorem are separate obligations. Neither this "
                    + "consumer nor the congruence states a classification of x^2+3=y^e, "
                    + "an original Fibonacci-depth gcd theorem, a Wall-Sun-Sun result, "
                    + "or closure of the parent DCE task."))),
                DescribeRole.Theorem))));
}
