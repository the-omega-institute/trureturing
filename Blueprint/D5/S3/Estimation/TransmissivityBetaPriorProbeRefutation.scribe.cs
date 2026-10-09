using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation;

internal sealed class TransmissivityBetaPriorProbeRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/zhou2023transmissivity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At mean photon number one quarter and beta parameters alpha=3, beta=1, a vacuum–two-photon probe has strictly smaller Hermitian-measurement Bayesian error than every phased in-between state.",
        H("In-between states need not be optimal for a beta prior"),
        Blocks(
            Node("betaDensity", "Beta prior density", DensityFormula(),
                "Section VI: P(tau)=tau^(alpha-1)(1-tau)^(beta-1)/B(alpha,beta), with B(alpha,beta)=Gamma(alpha)Gamma(beta)/Gamma(alpha+beta). Both exponents are real powers, and Gamma is the real gamma function. The prior is used on the interval [0,1]; the definition extends to raw real parameters, while the conjecture assumes alpha and beta positive."),
            Node("momentBeta", "Beta prior moment matrices", MomentFormula(),
                "Gamma_k is the entrywise interval integral of P(tau) tau^k rho(tau) on [0,1], with the real scalar cast to complex numbers. outputState is the pure-loss Kraus output on the finite Fock span, reused from the two-point formulation. k is a natural exponent."),
            Node("deltaB", "Bayesian error of a Hermitian observable", RiskFormula(),
                "Section I, equation (6): delta_B is the interval integral of P(tau) Re(trace(rho(tau) (H-tau I)^2)). The source measures in the eigenvectors of the Hermitian observable H, with its eigenvalues as estimates. The definition accepts any matrix H on the finite output span; the minimum restricts H to Hermitian matrices."),
            Node("MMSE", "Minimum over Hermitian observables", MmseFormula(),
                "Section I, the line after equation (6): the error is minimized over all Hermitian observables H. The Lean definition takes the real infimum of deltaB over Hermitian matrices on the output span. The certificates used here attain that infimum, giving the source's minimum."),
            Node("deltaB_eq_moments", "Integral error in terms of the prior moments", MomentsRiskFormula(),
                "If the prior density is continuous on [0,1], expanding (H-tau I)^2 and integrating entry by entry gives Re(trace(H H Gamma_0)-2 trace(H Gamma_1)+trace(Gamma_2)). The pure-loss output entries are continuous. Cyclicity of trace places each moment matrix on the right; Hermiticity of H is not needed for this identity.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("claim", "Beta-prior in-between optimality conjecture", ClaimFormula(),
                "Section VI: \"The numerical results indicate that the optimal input states with non-integer mean photon number, have the form of Eq. (27), which means that for nbar in N the optimal states are Fock states.\" Section VII: \"We note that for the beta prior PDF, we were not able to prove analytically that the Fock states or the in-between states of Eq. (27) states are optimal, even though our numerical computations support such conjecture.\" The encoding quantifies over positive alpha, beta and nbar, every finite cutoff N, and normalized pure inputs with mean photon number nbar. Some phase of the in-between state is asserted to have no greater MMSE than each competitor. Each Hermitian observable acts on the corresponding finite output span. The refutation uses alpha=3, beta=1, outside the two parameter pairs sampled in the source's figure."),
            Node("result", "A strictly better nonadjacent probe", Disp(new Formula.Not(F.Id("claim"))),
                "Take alpha=3, beta=1 and nbar=1/4. The prior density is 3 tau^2. Every in-between phase has MMSE at least 167/4575, while psi=(sqrt(14)/4)|0>+(sqrt(2)/4)|2> has MMSE at most 2/55. The difference is 7/50325>0. Both inputs have Euclidean norm one and mean photon number one quarter. Exact polynomial and square-root integrals give the moment matrices. The phased in-between Hermitian observable has diagonal entries 216/305 and 204/305, and off-diagonal entries 7 sqrt(3) star(z)/183 and 7 sqrt(3) z/183, with z star(z)=1. The competitor observable is [[8/11,0,2 sqrt(7)/77],[0,2/3,0],[2 sqrt(7)/77,0,20/33]]. Each solves Gamma_0 B+B Gamma_0=2 Gamma_1. Positive rank-one plus nonnegative diagonal decompositions establish positivity of Gamma_0. Square completion bounds deltaB for every Hermitian H from below by Re(trace(Gamma_2)-trace(B Gamma_1)); substituting H=B attains the bound. Thus the comparison uses the source's minimum over Hermitian observables. The rational strict inequality contradicts the conjecture; it does not assert global optimality of the competing probe.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zhou-bash-guha-gagatsos-2023-transmissivity-beta-prior-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Definition, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("beta-bmse-" + name.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance ?? AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. xs]);
    private static Formula At(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula All(string v, Formula type, Formula body) => Seq(Forall, Sp, F.Id(v), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string v, Formula type, Formula body) => Seq(Exists, Sp, F.Id(v), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula LeqOf(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula LtOf(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula IffOf(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(Parenthesized(x), FormulaBinaryOperator.Multiply, Parenthesized(y));
    private static Formula Pow(Formula x, Formula y) => Seq(Parenthesized(x), Caret, Grp(y));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Index(Formula cutoff) => Call("Fin", Add(cutoff, D(1)));
    private static Formula Func(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula Ket(Formula cutoff) => Func(Index(cutoff), Complex());
    private static Formula State(Formula cutoff) => Call("Matrix", Index(cutoff), Index(cutoff), Complex());
    private static Formula C(Formula x) => Call("ofReal", x);
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula N => F.Id("N");
    private static Formula A => F.Id("alpha");
    private static Formula B => F.Id("beta");
    private static Formula P => F.Id("psi");
    private static Formula K => F.Id("k");
    private static Formula Nb => F.Id("nbar");
    private static Formula Phi => F.Id("phi");
    private static Formula Ceiling => Call("ceilNat", Nb);
    private static Formula Moment(Formula k) => Call("momentBeta", N, A, B, P, k);
    private static Formula Obs => F.Id("H");
    private static Formula Risk => Call("deltaB", N, A, B, P, Obs);
    private static Formula PriorBind(Formula body) => All("alpha", Real(), All("beta", Real(), body));
    private static Formula IntervalIntegral(string v, Formula body) => Seq(Int, Underscore, Grp(D(0)), Caret, Grp(D(1)),
        Sp, Parenthesized(body), Sp, F.Id("d"), F.Id(v));

    private static Formula DensityFormula()
    {
        Formula t=F.Id("tau");
        return Disp(PriorBind(All("tau",Real(),Eqn(Call("betaDensity",A,B,t),
            Div(Mul(Pow(t,Sub(A,D(1))),Pow(Sub(D(1),t),Sub(B,D(1)))),
                Div(Mul(Call("Gamma",A),Call("Gamma",B)),Call("Gamma",Add(A,B))))))));
    }

    private static Formula MomentFormula()
    {
        Formula t=F.Id("tau"), i=F.Id("i"), j=F.Id("j");
        return Disp(All("N",Nat(),PriorBind(All("psi",Ket(N),All("k",Nat(),
            All("i",Index(N),All("j",Index(N),Eqn(At(Moment(K),i,j),
                IntervalIntegral("tau",Mul(C(Mul(Call("betaDensity",A,B,t),Pow(t,K))),
                    At(Call("outputState",N,t,P),i,j)))))))))));
    }

    private static Formula ObservableBind(Formula body) => All("N", Nat(),
        PriorBind(All("psi", Ket(N), All("H", State(N), body))));

    private static Formula RiskFormula()
    {
        Formula t=F.Id("tau");
        Formula square=Pow(Sub(Obs,Call("smul",C(t),D(1))),D(2));
        return Disp(ObservableBind(Eqn(Risk,IntervalIntegral("tau",
            Mul(Call("betaDensity",A,B,t),Call("Re",Call("trace",
                Mul(Call("outputState",N,t,P),square))))))));
    }

    private static Formula MomentsRiskFormula()
    {
        Formula expression=Add(Sub(Call("trace",Mul(Mul(Obs,Obs),Moment(D(0)))),
            Mul(D(2),Call("trace",Mul(Obs,Moment(D(1)))))),Call("trace",Moment(D(2))));
        Formula continuous=Call("ContinuousOn",Call("betaDensity",A,B),Call("Icc",D(0),D(1)));
        return Disp(ObservableBind(Imp(continuous,Eqn(Risk,Call("Re",expression)))));
    }

    private static Formula MmseFormula()
    {
        Formula r=F.Id("r");
        Formula predicate=Ex("H",State(N),And(Call("IsHermitian",Obs),Eqn(r,Risk)));
        Formula set=Seq(OpenBrace,r,Sp,Colon,Sp,Real(),Sp,Mid,Sp,predicate,CloseBrace);
        return Disp(All("N",Nat(),PriorBind(All("psi",Ket(N),
            Eqn(Call("MMSE",N,A,B,P),Call("sInf",set))))));
    }

    private static Formula ClaimFormula()
    {
        Formula normal=Eqn(Call("norm",Call("toLp",D(2),P)),D(1));
        Formula choice=Ex("phi",Real(),LeqOf(Call("MMSE",Ceiling,A,B,Call("inBetween",Nb,Phi)),
            Call("MMSE",N,A,B,P)));
        Formula competitors=All("N",Nat(),All("psi",Ket(N),Imp(normal,
            Imp(Eqn(Call("meanPhoton",N,P),Nb),choice))));
        return Disp(IffOf(F.Id("claim"),PriorBind(All("nbar",Real(),
            Imp(LtOf(D(0),A),Imp(LtOf(D(0),B),Imp(LtOf(D(0),Nb),competitors)))))));
    }
}
