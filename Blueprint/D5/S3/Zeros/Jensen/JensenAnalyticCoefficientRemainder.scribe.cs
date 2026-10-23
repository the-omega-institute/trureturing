using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class JensenAnalyticCoefficientRemainderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/Jensen/JensenAnalyticCoefficientRemainder.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Pow(Formula value, Formula power) => Seq(value, Caret, Grp(power));
    private static Formula Fr(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));
    private static Formula Cplx() => Seq(Mathbb, Grp(V("C")));
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Norm(Formula value) => Seq(Lvert, Sp, value, Rvert, Sp);
    private static Formula RangeSum(string index, Formula top, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(D(0), Le, Sp, V(index), Le, Sp, top)), Sp, body);
    private static Formula Correction() => RangeSum("k", Seq(D(2), V("r")),
        Seq(Call("c", V("r"), V("k")), Pow(V("z"), V("k")),
            Call("D", V("k"), V("F"), V("z"))));
    private static Formula Error() => Seq(Call("p", V("a"), V("n"), V("w")), Minus,
        RangeSum("r", V("K"), Seq(Fr(Pow(Seq(Open, Minus, D(1), Close), V("r")),
            Pow(V("n"), V("r"))), Call("correctionOperator", V("r"), V("F"), V("w")))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An entire complex coefficient series determines the derivatives of its finite Jensen correction remainder.",
        H("Analytic coefficient remainder"),
        Blocks(
            Describe.Lean(DescribeId.Create("jensen-analytic-correction-operator"),
                DeclarationHandle.Create(Prefix + "correctionOperator"), H("Finite correction operator"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, V("r"), InMacro, Sp, Nat(), Comma, Sp,
                    Forall, Sp, V("F"), Colon, Cplx(), To, Sp, Cplx(), Comma, Sp,
                    Forall, Sp, V("z"), InMacro, Sp, Cplx(), Comma, Sp,
                    Call("correctionOperator", V("r"), V("F"), V("z")), Eq, Correction()))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("c(r,k) is correctionCoeff and D(k,F,z) is iteratedDeriv k F z. The sum includes both endpoints 0 and 2r. The finite identity e(r,j)=sum(k<=2r)c(r,k)*descFactorial(j,k) identifies its entire series as sum_j e(r,j)*a(j)*z^j."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jensen-analytic-weighted-norm"),
                DeclarationHandle.Create(Prefix + "weightedNorm"), H("Weighted coefficient norm"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, V("a"), Colon, Nat(), To, Sp, Cplx(), Comma, Sp,
                    Forall, Sp, V("L"), InMacro, Sp, Nat(), Comma, Sp,
                    Forall, Sp, V("R"), InMacro, Sp, Reals(), Comma, Sp,
                    Call("weightedNorm", V("a"), V("L"), V("R")), Eq,
                    Sum, Underscore, Grp(Seq(V("j"), InMacro, Sp, Nat())), Sp,
                    Norm(Call("a", V("j"))), Pow(V("j"), V("L")), Pow(V("R"), V("j"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All coefficients are retained. The analytic theorem requires summability for every natural order and every nonnegative radius. The infinite sum is weightedNorm, with no tail cutoff."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jensen-analytic-coefficient-polynomial"),
                DeclarationHandle.Create(Prefix + "coefficientPolynomial"), H("Natural falling-factorial polynomial"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, V("a"), Colon, Nat(), To, Sp, Cplx(), Comma, Sp,
                    Forall, Sp, V("n"), InMacro, Sp, Nat(), Comma, Sp,
                    Call("coefficientPolynomial", V("a"), V("n")), Eq,
                    RangeSum("j", V("n"), Seq(Call("C", Seq(
                        Fr(Call("descFactorial", V("n"), V("j")), Pow(V("n"), V("j"))),
                        Call("a", V("j")))), Pow(V("X"), V("j"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("C embeds a complex coefficient in the polynomial ring and X is its indeterminate. p(a,n,z) denotes evaluation of this polynomial at z. The natural falling factorial vanishes for j>n, so the finite polynomial also has the full infinite coefficient-series representation."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jensen-analytic-coefficient-operator-error"),
                DeclarationHandle.Create(Prefix + "analytic_coefficient_operator_error"),
                H("Every derivative order of the actual remainder"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Seq(Forall, Sp, V("a"), Colon, Nat(), To, Sp, Cplx(), Comma, Sp,
                        Forall, Sp, V("F"), Colon, Cplx(), To, Sp, Cplx(), Comma),
                    Seq(Open, Forall, Sp, V("z"), InMacro, Sp, Cplx(), Comma, Sp,
                        Call("HasSum", Seq(V("j"), Mapsto, Sp, Call("a", V("j")), Pow(V("z"), V("j"))),
                            Call("F", V("z"))), Close, Sp, Land),
                    Seq(Open, Forall, Sp, V("L"), InMacro, Sp, Nat(), Comma, Sp,
                        Forall, Sp, V("R"), InMacro, Sp, Reals(), Comma, Sp, D(0), Le, Sp, V("R"), Implies, Sp, Call("Summable", Seq(V("j"), Mapsto, Sp, Norm(Call("a", V("j"))),
                            Pow(V("j"), V("L")), Pow(V("R"), V("j")))), Close, Implies),
                    Seq(Forall, Sp, V("n"), Comma, V("K"), Comma, V("b"), InMacro, Sp, Nat(), Comma, Sp,
                        D(1), Le, Sp, V("n"), Implies, Sp, Forall, Sp, V("R"), InMacro, Sp, Reals(), Comma, Sp,
                        D(1), Le, Sp, V("R"), Implies, Sp, Forall, Sp, V("z"), InMacro, Sp, Cplx(), Comma, Sp,
                        Norm(V("z")), Le, Sp, V("R"), Implies),
                    Seq(Norm(Call("D", V("b"), Seq(V("w"), Mapsto, Sp, Error()), V("z"))), Le, Sp, Fr(D(2), Pow(V("n"), Seq(V("K"), Plus, D(1)))),
                        Call("weightedNorm", V("a"), Seq(D(2), V("K"), Plus, D(2), Plus, V("b")), V("R")))
                ]))), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every order b the coefficient derivative series has terms a(j)*descFactorial(j,b)*z^(j-b). On an open disk of radius R+1, descFactorial(j,b)<=j^b and the radius-power bound give a summable uniform majorant. Mathlib's complex differentiation theorem justifies each induction step; the derivative identity is proved rather than assumed.")),
                    Paragraph(Text("Multiplying the k-th derivative series by c(r,k)*z^k and summing the finite k range gives the correction operator series. Terms j<k vanish exactly. Subtracting the finite correction sum from the polynomial gives the actual error series rho(n,K,j)*a(j)*z^j, where rho is the complete finite bonferroniResidual.")),
                    Paragraph(Text("The finite residual estimate gives weighted summability for these error coefficients at every radius. Applying the all-order derivative series to this actual error and then the weighted residual bound proves the stated inequality. The theorem includes n=1, j=0, K=0, b=0, j<b and j>n.")),
                    Paragraph(Text("The actual theta-source consumer supplies its entire series and weighted summability, and identifies sourcePolynomial with coefficientPolynomial sourceA n. This estimate does not establish the local scaled Hermite estimates, node enumeration, the original boundary comparison, compact-window exhaustion, or RH."))),
                DescribeRole.Theorem))));
}
