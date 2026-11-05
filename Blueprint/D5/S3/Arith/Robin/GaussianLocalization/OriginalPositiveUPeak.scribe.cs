using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class OriginalPositiveUPeakDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A right-of-critical actual zero produces a quantitative positive peak of the complete Mangoldt cumulative.",
        H("The original positive complete-U peak"),
        Blocks(Describe.Lean(
            DescribeId.Create("original-positive-u-peak"),
            DeclarationHandle.Create("D5/S3/Arith/Robin/GaussianLocalization/OriginalPositiveUPeak.original_positive_U_peak"),
            H("The original closed quantitative witness interval"),
            StatementSource.FromAuthor(PeakFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let rho be a complex number with classicalZeta(rho)=0, 0<re(rho)<1, "
                    + "re(rho)>1/2 and im(rho)>0. Put delta=re(rho)-1/2, D=im(rho)+10, "
                    + "m0=100*D^2/delta^2 and m1=500*D^4/delta^2. There exists a real A in "
                    + "the CLOSED interval [exp(4*m0),exp(28*m1)] such that "
                    + "sqrt(A)*(4*log(A)+9)<U(A). These are the only premises of this theorem.")),
                Paragraph(Text(
                    "Here U is literally CompleteMertensPeak.U: "
                    + "U(t)=t*sum(Lambda(n)/n,0<n<=floorNat(t))-psi(t)-t*log(t)+(1+gammaE)*t. "
                    + "Lambda is ArithmeticFunction.vonMangoldt, psi is Chebyshev.psi and "
                    + "gammaE is Real.eulerMascheroniConstant. All prime powers and the inclusive "
                    + "upper endpoint remain in this cumulative. This is not a prime-only substitute.")),
                Paragraph(Text(
                    "The current actual zero supplier includes both ordinate signs and repeats "
                    + "each zero according to its analytic multiplicity. Its mass and height theorems "
                    + "give |im(rho)|>10 and inverse-square occurrence mass less than two. "
                    + "ActualGaussianLocalWindow enumerates exactly the closed distance-six window. "
                    + "ZeroPowerSum.exists_pow_sum_re_ge_one selects a power between one and "
                    + "twice the occurrence count plus one, giving a time m in [m0,m1]. "
                    + "ActualGaussianDirectTail.full_E_original_time pays the entire strict "
                    + "complement and gives Re(E(m,im(rho)))>=exp((re(rho)^2+16*re(rho))*m)/2.")),
                Paragraph(Text(
                    "Suppose every A in the asserted interval fails the peak inequality. "
                    + "WholeFormula.actual_integrated_explicit_formula identifies the literal actual "
                    + "H(y) with U(exp(y))-log(2*pi)+trivialT(y). The full correction bound "
                    + "trivialT(y)<=1-log(2)<log(2*pi) gives Re(H(y))<=U(exp(y)) for y>0. "
                    + "Hence on J=[4*m,28*m], Re(H(y))<=b(y)=(4*y+11)*exp(y/2). "
                    + "The larger constant eleven is a positive central majorant, not a change "
                    + "to the asserted peak constant nine.")),
                Paragraph(Text(
                    "The signed W/K exchange identifies integral Re(H)*K with Re(E). "
                    + "The localization helper combines integral_mono, indicator decomposition and order algebra; "
                    + "it is bind-only proof support consumed by full_E_upper_of_central_bound, "
                    + "not an independent content or admission witness. "
                    + "The consumed private signed_localization_debit helper retains the full "
                    + "negative debit -integral Re(H)*V before relaxing it to its absolute value. "
                    + "The exact complement is ([0,infinity)\\J) union (-infinity,0); "
                    + "both endpoints of J stay central, and the singleton zero is transported "
                    + "only by nonatomic Lebesgue measure. The four original budgets are "
                    + "300*m*D^2*exp(33*m/4), 12*D^2*exp(9*m/2), "
                    + "8*D^2*exp(-32*m) and 1000*D^2*exp(-83*m). "
                    + "After the localization factors two, their sum is at most "
                    + "2000*m*D^2*exp(33*m/4). Every integral is preceded by integrability.")),
                Paragraph(Text(
                    "Finally re(rho)^2+16*re(rho)=33/4+17*delta+delta^2. "
                    + "The lower time bound pays 4000*m*D^2<exp(17*delta*m) through the second "
                    + "Taylor term of exp. This contradicts the preceding upper and lower "
                    + "bounds on Re(E), proving the stated existential with its original constants.")),
                Paragraph(Text(
                    "Conditional arithmetic application. Separately assume EXACTLY "
                    + "hJY: for every REAL u>=2, |psi(u)-u| <= "
                    + "(939/100)*u*(log(u))^(303/200)*exp(-(4137/5000)*sqrt(log(u))). "
                    + "This is an additional hypothesis; no implication from the zero premise "
                    + "to hJY is asserted. The Johnston-Yang constants refer to the quantitative "
                    + "hypothesis documented by the existing CompleteMertensPeak owner.")),
                Paragraph(Text(
                    "For the witness A above, 0<delta<1/2 and D>20 imply m0>160000. "
                    + "Thus exp(4*m0)>10000 (for instance exp(x)>=1+x suffices), and A>=10000. "
                    + "Write L=log(A)>=0. The inequality L^2/(1+L)<=L converts the strict "
                    + "positive-U peak into the exact premise of CompleteMertensPeak.complete_mertens_peak. "
                    + "WeightedPrimeLimit.chebyshev_error_kernel_integrable supplies the full "
                    + "(1,infinity) integrability unconditionally. Applying "
                    + "CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity at every "
                    + "real t>=2 discharges the supplier's hLay premise, with Q its literal "
                    + "Chebyshev-error tail integral. Neither integrability nor hLay is an "
                    + "extra premise of this application.")),
                Paragraph(Text(
                    "Applying complete_mertens_peak with this hLay and the separate hJY gives "
                    + "a real t in [A,B(A)], B(A)=exp(4*(log(A)+20)^2), and the actual "
                    + "integer N=Nat.lcmUpto(floorNat(t)). It satisfies 5040<N and "
                    + "divisorRatio(N)>exp(gammaE)*log(log(N)), where "
                    + "divisorRatio(N)=(ArithmeticFunction.sigma 1 N : real)/N, and "
                    + "(N:real)<=exp(B(A)*log(B(A))). From A<=exp(28*m1) we have "
                    + "0<=L<=28*m1, so 1<=B(A)<=B0=exp(4*(28*m1+20)^2). "
                    + "The nonnegative products B(A)*log(B(A))<=B0*log(B0) therefore give "
                    + "the ORIGINAL upper bound (N:real)<=exp(B0*log(B0)).")),
                Paragraph(Text(
                    "This arithmetic application is a composition of the peak and current "
                    + "suppliers, recorded here without a separate named application theorem. "
                    + "No actual off-critical zero or hJY instance is supplied. The conclusions "
                    + "are conditional peak existence and conditional finite Robin failure; "
                    + "they assert neither RH nor a universal Robin inequality."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);

    private static Formula PeakFormula()
    {
        var rho = F.Id("rho");
        var real = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        var half = new Formula.Fraction(F.D(1), F.D(2));
        var delta = new Formula.Binary(Call("re", rho), FormulaBinaryOperator.Subtract, half);
        var d = Add(Call("im", rho), F.D(1, 0));
        var m0 = new Formula.Fraction(Mul(F.D(1, 0, 0), new Formula.Power(d, F.D(2))), new Formula.Power(delta, F.D(2)));
        var m1 = new Formula.Fraction(Mul(F.D(5, 0, 0), new Formula.Power(d, F.D(4))), new Formula.Power(delta, F.D(2)));
        var a = F.Id("A");
        var member = new Formula.Relation(a, FormulaRelationOperator.MemberOf,
            Call("Icc", Call("exp", Mul(F.D(4), m0)), Call("exp", Mul(F.D(2, 8), m1))));
        var peak = Lt(Mul(Call("sqrt", a), Add(Mul(F.D(4), Call("log", a)), F.D(9))), Call("U", a));
        var witness = new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create("A"), real)],
            new Formula.Logic(member, FormulaLogicOperator.And, peak));
        return F.Disp(All("rho", F.Id("C"), Imp(Call("IsNontrivialZero", rho),
            Imp(Lt(half, Call("re", rho)), Imp(Lt(F.D(0), Call("im", rho)), witness)))));
    }
}
