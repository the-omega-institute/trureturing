using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class ThreeLabelCoalescentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/ThreeLabelCoalescent.";
    private static Formula Q(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        Seq(Q(name), Open, Join(args), Close);
    private static Formula Join(Formula[] args) => args.Length switch
    {
        0 => Seq(),
        1 => args[0],
        _ => Seq(args[0], Comma, Join(args[1..]))
    };
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, To, b);
    private static Formula Mass => Arrow(Call("Fin", D(5)), R);
    private static Formula Trajectory => Arrow(R, Mass);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A labelled pure coalescence chain on the five partitions of three labels.",
        H("Three-label pure coalescence"),
        Blocks(
            Paragraph(Text("The state order is N = 1|2|3, A = 12|3, B = 23|1, T = 123, C = 13|2. "
                + "The nonzero rates are N to A: 3, N to B: 1, N to C: 1/4, N to T: h, "
                + "A to T: 1/4, B to T: 17/4+h, and C to T: 1/4. T is absorbing. "
                + "The initial vector is (1,0,0,0,0). ForwardLaw requires this initial vector and "
                + "the five componentwise differential equations for every nonnegative real time; "
                + "it contains no closed-form equation. Write K = 4+h, ell = 17/4+h, "
                + "u = exp(-t/4), and v = exp(-ell*t).")),
            Paragraph(Text("The candidate vector explicit(h,t) is "
                + "(v,3(u-v)/K,t*v,1-v-3(u-v)/K-t*v-(u-v)/(4K),(u-v)/(4K)). "
                + "The association determinant delta(q) is q(N)q(T)-q(A)q(B). "
                + "The scalar H(h,t) is 1-((13/4+3t)/K)u-((h+3/4+(1+h)t)/K)v.")),
            Describe.Lean(
                DescribeId.Create("three-label-forward-solution"),
                DeclarationHandle.Create(Prefix + "forward_solution"),
                H("The forward equations determine the five masses and association"),
                StatementSource.FromAuthor(Disp(SolutionFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Uniqueness is applied successively to N, A, B and C, then T. "
                    + "Each difference solves a scalar homogeneous linear equation with zero initial value. "
                    + "The checked candidate therefore equals any solution of the original forward system. "
                    + "Substituting its five masses gives delta = v H. "
                    + "The resonant transition N to B produces the factor t v."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("three-label-positive-probability"),
                DeclarationHandle.Create(Prefix + "positive_probability_solution"),
                H("A strictly positive probability law at every positive time"),
                StatementSource.FromAuthor(Disp(ProbabilityFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The explicit vector solves the initial-value problem. At positive time, "
                    + "u exceeds v, so the masses at N, A, B and C are positive. The derivative of the T mass "
                    + "is a sum of nonnegative incoming flows, with strictly positive direct flow h times "
                    + "the N mass. Thus T grows strictly from zero. The five masses sum to one. The event maps merge12, merge23 and separate13 "
                    + "on N,A,B,T,C have truth tables (0,1,0,1,0), (0,0,1,1,0), and (0,0,0,0,1). "
                    + "Their means are X=pA+pT, Y=pB+pT and Z=pC. The pyramid width is "
                    + "min(X,Y,1-Z-X,1-Z-Y)>0. The conditional product joint mass is XY/(1-Z), "
                    + "and delta vanishes exactly when pT equals this mass. The productCompletion law "
                    + "is (1-Z-X-Y+kstar,X-kstar,Y-kstar,kstar,Z), with kstar=XY/(1-Z). "
                    + "The actual taskError is the expectation of f under p minus its expectation "
                    + "under productCompletion(p). It equals (fT-fA-fB+fN)*delta/(1-Z). "
                    + "Nonzero contrast preserves the zero set; negative contrast reverses all signs."))),
                DescribeRole.Theorem),
            Paragraph(Text("For V = 35/16+Kh and W = ell(1+h), set "
                + "G(h,t) = 3t/4-35/16+(V+Wt)exp(-Kt). Differentiation gives H' = uG/K and "
                + "G'' = K exp(-Kt)(KV-2W+KWt). The coefficient KV-2W equals "
                + "1/4+123h/16+6h squared+h cubed, so G is strictly convex on nonnegative time.")),
            Describe.Lean(
                DescribeId.Create("three-label-at-most-two-zeros"),
                DeclarationHandle.Create(Prefix + "no_three_positive_zeros"),
                H("At most two distinct positive association zeros"),
                StatementSource.FromAuthor(Disp(NoThreeFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Three positive determinant zeros would, together with H(0)=0, "
                    + "give three distinct zeros of H' by Rolle's theorem. Because u and K are positive, "
                    + "these would be three distinct zeros of G. Strict convexity makes the middle value "
                    + "strictly smaller than the maximum of the two outer zero values, a contradiction. "
                    + "The separate fold theorem supplies existence, simplicity and the critical parameter."))),
                DescribeRole.Theorem),
            Paragraph(Text("TwoCrossings(h) means that there are real numbers a,b with 0<a<b, "
                + "H(h,a)=H(h,b)=0 and nonzero time derivatives at both points, with H(h,t)>0 "
                + "for 0<t<a, H(h,t)<0 for a<t<b, and H(h,t)>0 for t>b. "
                + "These signs exclude every other positive zero. Since v is strictly positive, "
                + "the determinant has exactly the same signs and zeros.")),
            Describe.Lean(
                DescribeId.Create("three-label-unique-fold"),
                DeclarationHandle.Create(Prefix + "unique_fold_classification"),
                H("The unique fold and the complete parameter classification"),
                StatementSource.FromAuthor(Disp(FoldFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("H is strictly increasing in h at every positive time. "
                    + "For h at most 1 its value at time 2 is negative, whereas for h at least 8 "
                    + "it is positive at all positive times. Positivity near zero and at infinity "
                    + "uniformly confines zeros for h in [1,8] to a compact time interval. "
                    + "The maximum parameter in this compact zero locus gives a nonnegative law "
                    + "with a stationary zero. Strict convexity of G bounds the number of roots, "
                    + "forces two simple crossings below the threshold, and makes the critical "
                    + "second derivative strictly positive. Parameter monotonicity gives strict "
                    + "positivity above the threshold. This theorem concerns the specified one-parameter "
                    + "family; stability under arbitrary perturbation of seven rates is not asserted."))),
                DescribeRole.Theorem),
            Paragraph(Text("For seven rates r=(alpha,beta,gamma,zeta,d,e,f), let "
                + "L=alpha+beta+gamma+zeta. GeneralForwardLaw requires an initially N, normalized "
                + "nonnegative trajectory satisfying the seven-rate forward equations. It assumes "
                + "no explicit mass formula or determinant bound. Put "
                + "M(r)=min(d,L)+min(e,L)-L. Here deltaTrajectory(p) means the function t maps to delta(p(t)). The embedding baseRates(h) is "
                + "(3,1,1/4,h,1/4,17/4+h,1/4).")),
            Describe.Lean(
                DescribeId.Create("three-label-seven-rate-endpoints"),
                DeclarationHandle.Create(Prefix + "seven_rate_endpoint_certificates"),
                H("Seven-rate tail and initial-derivative certificates"),
                StatementSource.FromAuthor(Disp(EndpointFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each incoming branch, multiply its mass by exp(min(d,L)t). "
                    + "Its derivative is bounded above by the corresponding incoming rate, since "
                    + "both the forcing exponential and the nonnegative-loss term have the required signs. "
                    + "The mean-value bound gives pA<=alpha*t*exp(-min(d,L)t) and the analogous "
                    + "bound for pB. Multiplication and division by pN give the global ratio bound. "
                    + "The forward equations at zero give the association derivative zeta. "
                    + "The original family is a probability trajectory of this generator and has M=1/4. "
                    + "These are endpoint certificates; a uniform neighborhood with exactly two roots "
                    + "has not been established."))),
                DescribeRole.Theorem)
        )));

    private static Formula SolutionFormula()
    {
        Formula h = F.Id("h"), p = F.Id("p"), t = F.Id("t");
        Formula body = And(Eq(Seq(p, Open, t, Close), Call("explicit", h, t)),
            Eq(Call("delta", Seq(p, Open, t, Close)), Mul(Call("v", h, t), Call("H", h, t))));
        return All("h", R, Imp(Lt(D(0), h), All("p", Trajectory,
            Imp(Call("ForwardLaw", h, p), All("t", R, Imp(Le(D(0), t), body))))));
    }
    private static Formula ProbabilityFormula()
    {
        Formula h = F.Id("h"), p = F.Id("p"), t = F.Id("t"), i = F.Id("i");
        Formula q = Seq(p, Open, t, Close);
        Formula normalization = Eq(Seq(new Formula.Subscript(Sum, Seq(i, InMacro, Sp, Call("Fin", D(5)))),
            Seq(p, Open, t, Comma, i, Close)), D(1));
        Formula positive = All("i", Call("Fin", D(5)), Lt(D(0), Seq(p, Open, t, Comma, i, Close)));
        Formula residual = new Formula.Binary(D(1), FormulaBinaryOperator.Subtract, Call("Z", q));
        Formula independent = new Formula.Logic(Eq(Call("delta", q), D(0)), FormulaLogicOperator.Iff,
            Eq(Seq(p, Open, t, Comma, D(3), Close), Call("productJoint", q)));
        Formula f = F.Id("f");
        Formula response = All("f", Mass, Eq(Call("taskError", q, f),
            new Formula.Fraction(Mul(Call("contrast", f), Call("delta", q)), residual)));
        Formula fixedPoint = new Formula.Logic(Eq(Call("delta", q), D(0)), FormulaLogicOperator.Iff,
            Eq(q, Call("productCompletion", q)));
        Formula geometry = And(Lt(D(0), Call("pyramidWidth", q)),
            And(Lt(D(0), residual), And(independent, And(fixedPoint, response))));
        Formula conclusion = And(Eq(q, Call("explicit", h, t)), And(normalization,
            And(positive, And(Eq(Call("delta", q), Mul(Call("v", h, t), Call("H", h, t))), geometry))));
        return All("h", R, Imp(Lt(D(0), h),
            And(Call("ForwardLaw", h, Call("explicit", h)),
                All("p", Trajectory, Imp(Call("ForwardLaw", h, p),
                    All("t", R, Imp(Lt(D(0), t), conclusion)))))));
    }

    private static Formula NoThreeFormula()
    {
        Formula h = F.Id("h"), p = F.Id("p"), a = F.Id("a"), b = F.Id("b"), c = F.Id("c");
        Formula Delta(Formula t) => Call("delta", Seq(p, Open, t, Close));
        Formula premise = And(Lt(D(0), a), And(Lt(a, b), And(Lt(b, c),
            And(Eq(Delta(a), D(0)), Eq(Delta(b), D(0))))));
        Formula nonzero = new Formula.Relation(Delta(c), FormulaRelationOperator.NotEqual, D(0));
        return All("h", R, Imp(Lt(D(0), h), All("p", Trajectory,
            Imp(Call("ForwardLaw", h, p), All("a", R, All("b", R,
                All("c", R, Imp(premise, nonzero))))))));
    }

    private static Formula FoldFormula()
    {
        Formula hc = F.Id("hc"), tc = F.Id("tc"), h = F.Id("h"), t = F.Id("t");
        Formula Deriv(Formula k, Formula s) => Call("deriv", Call("H", k), s);
        Formula second = Call("deriv", Call("deriv", Call("H", hc)), tc);
        Formula critical = And(Eq(Call("H", hc, tc), D(0)), And(Eq(Deriv(hc, tc), D(0)), Lt(D(0), second)));
        Formula unique = All("h", R, All("t", R, Imp(Lt(D(0), h), Imp(Lt(D(0), t),
            Imp(Eq(Call("H", h, t), D(0)), Imp(Eq(Deriv(h, t), D(0)), And(Eq(h, hc), Eq(t, tc))))))));
        Formula low = All("h", R, Imp(Lt(D(0), h), Imp(Lt(h, hc), Call("TwoCrossings", h))));
        Formula middle = All("t", R, Imp(Lt(D(0), t), Imp(
            new Formula.Relation(t, FormulaRelationOperator.NotEqual, tc), Lt(D(0), Call("H", hc, t)))));
        Formula high = All("h", R, Imp(Lt(hc, h), All("t", R, Imp(Lt(D(0), t), Lt(D(0), Call("H", h, t))))));
        Formula body = And(And(Lt(D(1), hc), Lt(hc, D(8))), And(Lt(D(0), tc),
            And(critical, And(unique, And(low, And(middle, high))))));
        return new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("hc"), R,
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("tc"), R, body));
    }

    private static Formula EndpointFormula()
    {
        Formula r = F.Id("r"), p = F.Id("p"), t = F.Id("t"), i = F.Id("i");
        Formula h = F.Id("h"), q = F.Id("q");
        Formula Rate(byte j) => Seq(r, Open, D(j), Close);
        Formula MassAt(byte j) => Seq(p, Open, t, Comma, D(j), Close);
        Formula neg(Formula a) => new Formula.Negate(a);
        Formula sum(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
        Formula sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
        Formula l = Call("outgoing", r);
        Formula m = sub(sum(Call("min", Rate(4), l), Call("min", Rate(5), l)), l);
        Formula bound = Le(new Formula.Fraction(Mul(MassAt(1), MassAt(2)), MassAt(0)),
            Mul(Mul(Mul(Rate(0), Rate(1)), new Formula.Power(t, D(2))), Call("exp", Mul(neg(m), t))));
        Formula first = All("t", R, Imp(Le(D(0), t), Eq(MassAt(0), Call("exp", Mul(neg(l), t)))));
        Formula tail = All("t", R, Imp(Le(D(0), t), bound));
        Formula slope = Call("HasDerivAt", Call("deltaTrajectory", p), Rate(3), D(0));
        Formula baseRates = Call("baseRates", h), baseL = Call("outgoing", baseRates);
        Formula baseM = sub(sum(Call("min", Seq(baseRates, Open, D(4), Close), baseL),
            Call("min", Seq(baseRates, Open, D(5), Close), baseL)), baseL);
        Formula embedding = All("h", R, Imp(Lt(D(0), h), And(Eq(baseM,
            new Formula.Fraction(D(1), D(4))),
            All("q", Trajectory, Imp(Call("ForwardLaw", h, q), Call("GeneralForwardLaw", baseRates, q))))));
        Formula branches = All("t", R, Imp(Le(D(0), t), And(
            Le(MassAt(1), Mul(Mul(Rate(0), t), Call("exp", Mul(neg(Call("min", Rate(4), l)), t)))),
            And(Le(MassAt(2), Mul(Mul(Rate(1), t), Call("exp", Mul(neg(Call("min", Rate(5), l)), t)))),
                Le(MassAt(4), Mul(Mul(Rate(2), t), Call("exp", Mul(neg(Call("min", Rate(6), l)), t))))))));
        Formula body = And(first, And(tail, And(branches, And(slope, embedding))));
        Formula positive = All("i", Call("Fin", D(7)), Lt(D(0), Seq(r, Open, i, Close)));
        return All("r", Arrow(Call("Fin", D(7)), R), Imp(positive, All("p", Trajectory,
            Imp(Call("GeneralForwardLaw", r, p), body))));
    }

}
