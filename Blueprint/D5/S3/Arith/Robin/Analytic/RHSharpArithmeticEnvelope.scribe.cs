using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

internal sealed class RHSharpArithmeticEnvelopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full-real sharp actual-B lower endpoint",
        H("Signed arithmetic transport and the exact lower liminf"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("arithmetic-normalization"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/RHSharpArithmeticEnvelope.D"),
                H("Square-root logarithmic normalization"),
                StatementSource.FromAuthor(DDefinition()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The normalization D is defined on all real endpoints."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-arithmetic-error"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/RHSharpArithmeticEnvelope.B"),
                H("The actual Mertens and theta error"),
                StatementSource.FromAuthor(BDefinition()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here E₃ is Mertens.E₃ and theta is Chebyshev.theta. Both are the canonical actual arithmetic functions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-b-lower-endpoint"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/RHSharpArithmeticEnvelope.actual_B_lower_endpoint"),
                H("All-real envelope, arbitrarily late attainment and exact liminf in one result"),
                StatementSource.FromAuthor(EndpointClaim()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let D(x)=sqrt(x)*log(x), M=firstLiMass and "
                        + "B(x)=Mertens.E₃(x)+log(log(theta(x)))-log(log(x)). Under RH, the conclusion "
                        + "has three clauses. For every epsilon>0, eventually for ALL real x, theta(x)>1 and "
                        + "abs(D(x)*B(x)+2)<M+epsilon. For every epsilon>0 and real Y there is a real "
                        + "x>=max(2,Y) with theta(x)>1 and abs(D(x)*B(x)+2+M)<epsilon. Finally "
                        + "Filter.liminf (fun x:Real => D(x)*B(x)) atTop=-2-M. This states the lower endpoint; "
                        + "upper endpoint attainment and integer Robin conclusions require further results.")),
                    Paragraph(Text(
                        "Use w(t)=ActualRobinClockCovariance.activationDensity(t)=(log(t)+1)/(t^2*log(t)^2), "
                        + "Jpsi(x)=integral_(t>x)(psi(t)-t)*w(t), S(x)=integral_(t>x)(psi(t)-theta(t))*w(t), "
                        + "and N(x)=log(log(theta(x)))-log(log(x))-(theta(x)-x)/(x*log(x)). All tails are the "
                        + "actual infinite Lebesgue tails. CompleteMertensPeak.complete_mertens_ledger supplies "
                        + "the actual psiErrorKernel L1 premise and weighted integrability. The identity "
                        + "psiErrorKernel*r=(psi-t)*w is algebraic. CompleteChebyshevTailIdentity, followed "
                        + "by algebra with U, gives Q(x)=-U(x)/x for every x>=2, hence "
                        + "sqrt(x)*Q(x)=-G(log(x)). Inclusive finite Mangoldt sums remain intact.")),
                    Paragraph(Text(
                        "Apply WeightedTailTransport.transport_exp to this actual kernel, using "
                        + "R(y)=(y+1)/y^2 and W(y)=(y+2)/y^3. Its exact identity is "
                        + "Jpsi(exp(y))=R(y)*Q(exp(y))-T(y), T(y)=integral_(v>y)W(v)*Q(exp(v)); "
                        + "there is NO additional exp(-y) factor. A fixed eventual bound abs(G)<=C, C=M+1>=0, "
                        + "gives abs(Q(exp(v)))<=C*exp(-v/2). W_nonneg and W_antitone, together with Mathlib's "
                        + "integrableOn_exp_mul_Ioi and integral_exp_mul_Ioi at coefficient -1/2, give "
                        + "abs(T(y))<=2*C*W(y)*exp(-y/2). The signed boundary is "
                        + "D(exp(y))*Jpsi(exp(y))+G(y)=-G(y)/y-exp(y/2)*y*T(y), so its absolute value "
                        + "is at most C*(3/y+4/y^2), which tends to zero. This uses the "
                        + "absolute-Fubini transport.")),
                    Paragraph(Text(
                        "The Schoenfeld estimate gives abs(psi(x)-x)<=(7/8)*sqrt(x)*log(x)^2 "
                        + "for every real x>=5000 under RH. Chebyshev.psi_sub_theta_le_mul_sqrt supplies "
                        + "psi(x)-theta(x)<=C*sqrt(x), with theta<=psi. The theta error "
                        + "therefore bounds abs((theta(x)-x)/x^(3/4)) by "
                        + "(7/8)*log(x)^2/x^(1/4)+C/x^(1/4). The root Mathlib API "
                        + "isLittleO_log_rpow_rpow_atTop, with r=2 and s=1/4, makes this tend to zero. "
                        + "This estimate also controls the nonlinear remainder below. Multiplication "
                        + "by x^(-1/4) gives (theta(x)-x)/x->0, hence theta(x)/x->1 and eventually "
                        + "theta(x)>1.")),
                    Paragraph(Text(
                        "For the psi-theta root rate, apply the same public Schoenfeld "
                        + "bound at sqrt(x). The actual Costa-Pereira inequalities with exponents "
                        + "1/2,1/3,1/5 above and 1/2,1/3,1/7 below imply "
                        + "abs(psi(x)-theta(x)-sqrt(x))<=abs(psi(sqrt(x))-sqrt(x))"
                        + "+psi(x^(1/3))+psi(x^(1/5)); the lower estimate uses the nonnegative actual "
                        + "psi terms. With C=log(4)+4, Chebyshev.psi_le_const_mul_self and log(sqrt(x))"
                        + "=log(x)/2 yield the nonnegative majorant "
                        + "abs(log(x)*((psi(x)-theta(x))/sqrt(x)-1))<="
                        + "(7/32)*log(x)^3/x^(1/4)+C*log(x)/x^(1/6)+C*log(x)/x^(3/10). "
                        + "The root power-log API makes each term tend to zero. Multiply this actual rate "
                        + "by 1/log(x), cancelling only eventually where x>1, to obtain the "
                        + "limit (psi-theta)/sqrt->1 used in the square-root tail estimate. "
                        + "These are consequences of RH, not additional root-rate or error premises.")),
                    Paragraph(Text(
                        "For the nonlinear term put delta=theta(x)-x, L=log(x), u=delta/x and "
                        + "v=log(1+u)/L. Eventually L>=1 and abs(u)<=1/4. Mathlib "
                        + "Real.abs_log_sub_add_sum_range_le, with x=-u and n=1, gives "
                        + "abs(log(1+u)-u)<=u^2/(1-abs(u))<=2*u^2; hence abs(log(1+u))<=2*abs(u) "
                        + "and abs(v)<=1/2. Apply the same literal lemma to -v. From theta=x*(1+u) and "
                        + "log(theta)=L*(1+v), exact log algebra gives "
                        + "N=[log(1+v)-v]+[log(1+u)-u]/L. Thus abs(N)<=10*u^2/L and "
                        + "abs(D*N)<=10*((theta-x)/x^(3/4))^2->0. Positivity of all log arguments is paid "
                        + "from these bounds; delta=0 and both signs are included.")),
                    Paragraph(Text(
                        "For the square-root tail put a(t)=sqrt(t)*w(t), H(t)=2/(sqrt(t)*log(t)), "
                        + "q(t)=(log(t)+2)/(t*sqrt(t)*log(t)^2)=-H'(t). For t>=x>1, "
                        + "0<=a(t)<=q(t)<=(1+1/log(x))*a(t). Apply the nonnegative-derivative improper FTC "
                        + "to g=-H on Ici(x), with derivative q>=0 and limit zero: q is integrable and "
                        + "integral_(t>x)q(t)=H(x). Domination pays integrability of a. If A=integral a, "
                        + "H(x)/(1+1/log(x))<=A(x)<=H(x), and D(x)*H(x)=2, so D*A->2. "
                        + "The local RH-only limit (psi-theta)/sqrt->1 gives, uniformly over the whole tail, "
                        + "abs((psi-theta)*w-a)<=eta*a. Integrability of the actual S kernel follows by "
                        + "subtracting the supplied psi and theta kernels. setIntegral_mono_on then gives "
                        + "abs(S-A)<=eta*A and D*S->2. No derivative of a Chebyshev step function is used.")),
                    Paragraph(Text(
                        "ThetaTailRobinWitness.theta_tail_mertens_robin supplies the actual theta-tail "
                        + "integrability and exact equality -(integral(theta-t)*w)=E₂p-(theta-x)/(x*log(x)). "
                        + "Subtracting actual integrable tails gives Jpsi-S=(theta-x)/(x*log(x))-E₂p, hence "
                        + "B=Jpsi-S+(E₃+E₂p)+N. The finite cancellation is "
                        + "E₃+E₂p=sum_(n in Ioc(0,floorNat(x)))M_eq_summand(n)-(Mertens.M-Mertens.γ). "
                        + "The estimate sum_M_eq_summand_le' bounds its absolute value by 4/x; normalized it "
                        + "is bounded by 4*log(x)/sqrt(x)->0.")),
                    Paragraph(Text(
                        "The resulting signed limit is D(x)*B(x)+2+G(log(x))->0 on ALL real endpoints. "
                        + "Combine this with the actual_G_control envelope and theta_late(hRH) for the first clause. For lower "
                        + "attainment choose the real arithmetic threshold first, then take x=exp(n). Spend "
                        + "epsilon/3 on the signed arithmetic error and 2*epsilon/3 on actual_G_control; "
                        + "the latter spends epsilon/3 each on phase-cluster distance and the WholeFormula "
                        + "residual. Thus three separate errors are paid. The envelope at epsilon=1 gives "
                        + "eventual lower and upper boundedness of D*B. The nontrivial atTop filter and the "
                        + "upper bound give IsCoboundedUnder (>=). Apply le_liminf_iff using the lower "
                        + "epsilon envelope, and liminf_le_iff using the arbitrarily-late witnesses converted "
                        + "to frequently_atTop."))),
                DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsOne(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula AtMost(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula ImpliesClaim(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula DDefinition()
    {
        var x = F.Id("x");
        return Disp(All("x", Real, new Formula.Relation(Call("D", x),
            FormulaRelationOperator.Equal, Multiply(Seq(Sqrt, Grp(x)), Call("log", x)))));
    }

    private static Formula BDefinition()
    {
        var x = F.Id("x");
        var mertens = Seq(F.Id("E"), Underscore, Grp(D(3)), Open, x, Close);
        return Disp(All("x", Real, new Formula.Relation(Call("B", x),
            FormulaRelationOperator.Equal,
            Subtract(Add(mertens, Call("log", Call("log", Call("theta", x)))),
                Call("log", Call("log", x))))));
    }

    private static Formula EndpointClaim()
    {
        var e = F.Id("epsilon");
        var x = F.Id("x");
        var t = F.Id("T");
        var y = F.Id("Y");
        var mass = F.Id("firstLiMass");
        var db = Multiply(Call("D", x), Call("B", x));
        var thetaPositive = Less(D(1), Call("theta", x));
        var envelope = All("epsilon", Real, ImpliesClaim(Less(D(0), e),
            ExistsOne("T", Real, All("x", Real, ImpliesClaim(AtMost(t, x),
                And(thetaPositive, Less(new Formula.Absolute(Add(db, D(2))), Add(mass, e))))))));
        var attainment = All("epsilon", Real, ImpliesClaim(Less(D(0), e),
            All("Y", Real, ExistsOne("x", Real,
                And(AtMost(Call("max", D(2), y), x),
                    And(thetaPositive, Less(new Formula.Absolute(Add(Add(db, D(2)), mass)), e)))))));
        var lowerLimit = new Formula.Relation(
            Seq(Operatorname, Grp(F.Id("liminf")), Underscore,
                Grp(x, InMacro, Sp, Real, Comma, Sp, x, To, Sp, Infty), Sp, db),
            FormulaRelationOperator.Equal, Subtract(new Formula.Negate(D(2)), mass));
        return Disp(ImpliesClaim(Seq(Operatorname, Grp(F.Id("RiemannHypothesis"))),
            And(envelope, And(attainment, lowerLimit))));
    }
}
