using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class MittagLefflerModulusRefutationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/AnalyticClosure/garrappa2025mittagmodulus");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A closed beta interval of strict deficits exists for every alpha between one and two.",
        H("The reverse Mittag-Leffler modulus characterization fails"),
        Blocks(
            Entry("ggps-source-series", "IsSourceSeries", "The convergent two-parameter series",
                SeriesFormula(), AssessedProvenance.FromLiterature(Source),
                "Page 1, equation (1.1): “In this paper we study several inequalities of the two-parameter Mittag-Leffler function Eα,β, which is defined on the complex plane for α > 0 and β ∈ ℝ by the series representation” Eα,β(z) = ∑ from k = 0 to infinity of z^k/Γ(αk+β), z ∈ ℂ. The formula uses HasSum, so convergence is part of the relation. Alpha and beta are real, z is complex, and k is natural. The value val(k,Real) is the natural-to-real coercion, and val(Real.Gamma(alpha*val(k,Real)+beta),Complex) embeds the denominator in the complex plane. Division is totalized at Gamma poles.",
                DescribeRole.Definition),
            Entry("ggps-reciprocal", "reciprocal", "The real reciprocal on the positive axis",
                ReciprocalFormula(), AssessedProvenance.FromLiterature(Source),
                "Page 18, Conjecture 25 uses “1/Eα,β(x)”. Here E is a real-real-complex-complex family and alpha, beta and x are real. The real part reads the real-valued series on real arguments, after embedding x in Complex.",
                DescribeRole.Definition),
            Entry("ggps-characterization", "claim", "Conjecture 25 in full",
                Equal(F.Id("claim"), ClaimBody()), AssessedProvenance.FromLiterature(Source),
                "Page 18: “Conjecture 25. For every α ∈ (1, 2), one has The inequality (1.4) holds globally ⇐⇒ β ∈ [α − 1, α] ⇐⇒ 1/Eα,β(x) is CM on (0, ∞).” Inequality (1.4) is |Eα,β(z)| ≥ Eα,β(Re z), and globally means every complex z. The parameter beta is nonnegative, as in the paper's inequality problem. The leading existential supplies the entire convergent family. The second conjunct expresses both equivalences for every such family. CompletelyMonotoneOn supplies smoothness and all nonnegative signed derivatives; the separate positivity clause preserves the positive codomain. The displayed val operations are the real-to-complex coercions.",
                DescribeRole.Definition),
            Entry("ggps-beta-continuity", "source_continuous_beta", "Continuity in the second parameter",
                All("E", FamilyType(), Implies(Call("IsSourceSeries", F.Id("E")),
                    All("alpha", F.Id("Real"), Implies(Lt(Num(0), F.Id("alpha")),
                        All("z", F.Id("Complex"), Call("Continuous",
                            Seq(Open, F.Id("beta"), Colon, F.Id("Real"), Sp, Mapsto, Sp,
                                App(F.Id("E"), F.Id("alpha"), F.Id("beta"), F.Id("z")), Close))))))),
                AssessedProvenance.FromRepo(Source),
                "For each positive alpha and complex z, every family satisfying the literal convergent source series is continuous as a function of beta on the whole real line. On every compact beta interval, eventual monotonicity of real Gamma on [2,infinity) gives a summable majorant from its left endpoint. The partial sums are continuous because reciprocal complex Gamma is entire, including at its zeros. Their local uniform limit equals E by HasSum uniqueness.",
                DescribeRole.Theorem),
            Entry("ggps-left-contour-limit", "source_left_integral_tendsto_zero", "The actual moving-left limit",
                EndpointParameters(Call("Tendsto", MapVariable("n",F.Id("Nat"),EndpointIntegral(Call("leftLine",F.Id("n")))),F.Id("atTop"),Call("nhds",Num(0)))),
                AssessedProvenance.FromRepo(Source),
                "At beta=alpha-1 the real reciprocal-Gamma argument on the line indexed by n is alpha*n+alpha/2-1. Write n=m+1. The retained Gamma denominator then has fixed betaPrime=3*alpha/2-1, so the integral bound is a fixed factor times the m-th norm coefficient of the actual convergent Mittag-Leffler series at betaPrime. Summability forces it to zero. No Barnes identity or asymptotic is assumed.", DescribeRole.Theorem),
            Entry("ggps-barnes-identity", "source_barnes_identity", "The literal Barnes identity",
                All("E",FamilyType(),Implies(Call("IsSourceSeries",F.Id("E")),EndpointParameters(
                    Equal(App(F.Id("E"),F.Id("alpha"),Subtract(F.Id("alpha"),Num(1)),F.Id("z")),
                        Multiply(new Formula.Fraction(Num(1),Multiply(Num(2),Seq(Pi,Sp))),EndpointIntegral(new Formula.Fraction(Num(1),Num(2)))))))),
                AssessedProvenance.FromRepo(Source),
                "For every literal source realization, alpha greater than one and nonzero exterior z, the endpoint beta=alpha-1 value is one over 2*pi times the integral in dy on Re(s)=1/2. The proof supplies the actual shifted-Gamma holomorphic numerator, single-pole factorization, all boundary-line integrability, both horizontal limits and moving-left limit. Its residues are exactly z^n/Gamma(alpha*n+beta). The residue HasSum and the original source HasSum agree by uniqueness. The rightward shifts use this literal identity to obtain the endpoint inverse-square expansion.", DescribeRole.Theorem),
            Entry("ggps-endpoint-coefficient", "endpointCoefficient", "The endpoint coefficient", EndpointFamilyFormula("coefficient"), AssessedProvenance.FromRepo(Source), "The first nonzero inverse-power coefficient is minus the reciprocal of Gamma at minus alpha minus one.", DescribeRole.Definition),
            Entry("ggps-endpoint-coefficient-positive", "endpointCoefficient_formula", "The positive endpoint coefficient", EndpointFamilyFormula("coefficientFormula"), AssessedProvenance.FromRepo(Source), "Three Gamma recurrences identify the coefficient with alpha times alpha minus one times alpha plus one divided by Gamma at two minus alpha. It is strictly positive throughout the open alpha interval.", DescribeRole.Theorem),
            Entry("ggps-endpoint-expansion", "source_endpoint_expansion", "The actual endpoint expansion", EndpointFamilyFormula("expansion"), AssessedProvenance.FromRepo(Source), "The shifts from one half to three halves and then five halves cross the poles at one and two. The first coefficient vanishes because reciprocal Gamma at minus one is zero. The remainder is the actual integral on the five-halves line, with integration in dy.", DescribeRole.Theorem),
            Entry("ggps-endpoint-scaled-limit", "source_endpoint_scaled_limit", "The endpoint scaled limit", EndpointFamilyFormula("limit"), AssessedProvenance.FromRepo(Source), "Positive radial scaling gives a fixed constant times r to the power minus five halves for the remainder. After multiplication by r squared the error tends to zero. The limit is the endpoint coefficient divided by w squared.", DescribeRole.Theorem),
            Entry("ggps-ray-tilt", "rayTilt", "The prescribed ray tilt", EndpointFamilyFormula("tilt"), AssessedProvenance.FromRepo(Source), "The angle is pi times two minus alpha divided by four.", DescribeRole.Definition),
            Entry("ggps-ray-direction", "rayDirection", "The prescribed exterior direction", EndpointFamilyFormula("direction"), AssessedProvenance.FromRepo(Source), "The direction is minus one plus i times the prescribed positive tilt.", DescribeRole.Definition),
            Entry("ggps-ray-parameters", "ray_parameters", "The ray geometry and angular margin", EndpointFamilyFormula("parameters"), AssessedProvenance.FromRepo(Source), "The argument of minus the direction is minus the prescribed angle. The principal argument follows by positive scaling of the unit-circle direction, and the angular margin is strictly positive.", DescribeRole.Theorem),
            Entry("ggps-endpoint-failure", "source_endpoint_failure", "One finite endpoint deficit", EndpointFamilyFormula("failure"), AssessedProvenance.FromRepo(Source), "The scaled negative-axis real part tends to the positive endpoint coefficient. The scaled ray norm tends to that coefficient divided by one plus the squared tilt. Their strict limit gap gives one finite positive radius.", DescribeRole.Theorem),
            Entry("ggps-closed-beta-family", "source_closed_beta_family", "The same point on a closed beta interval", EndpointFamilyFormula("family"), AssessedProvenance.FromRepo(Source), "For every alpha between one and two, choose the finite point on the prescribed ray first. Continuity in beta gives an open neighborhood of strict deficits. A positive epsilon smaller than one places the whole closed interval from alpha minus one to alpha minus one plus epsilon inside that neighborhood.", DescribeRole.Theorem),
            Entry("ggps-refutation", "result", "The characterization is false",
                Seq(Neg, Sp, Parenthesized(ClaimBody())), AssessedProvenance.FromRepo(Source),
                "The literal source family exists for every positive alpha, every real beta and every complex argument. Apply the closed-beta family at alpha three halves and beta one half. The first original global equivalence would force the reverse modulus inequality at its chosen point, contradicting the strict deficit. The source definition and both original global equivalences retain their full quantifiers.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        AssessedProvenance provenance, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/MittagLefflerModulusRefutation." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role,
            openProblemResolutionClaim: name == "result"
                ? new OpenProblemResolutionClaim(ProblemSlugRef.Create("ggps2025"), ResolutionKind.Refuted)
                : null);


    private static Formula Some(string n, Formula t, Formula f) => new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(n),t,f);
    private static Formula EndpointFamilyFormula(string kind)
    {
        Formula a=F.Id("alpha"), z=F.Id("z"), w=F.Id("w"), r=F.Id("r"), b=F.Id("beta"), eps=F.Id("epsilon"), e=F.Id("E"), real=F.Id("Real"), complex=F.Id("Complex");
        Formula zero=Num(0), one=Num(1), two=Num(2), imag=Seq(Operatorname,Grp(F.Id("ComplexI")));
        Formula coeff=Call("endpointCoefficient",a), tilt=Call("rayTilt",a), direction=Call("rayDirection",a), endpoint=Subtract(a,one);
        Formula sq(Formula x) => new Formula.Power(x,two);
        Formula div(Formula x,Formula y) => new Formula.Fraction(x,y);
        Formula norm(Formula x) => new Formula.Norm(x);
        Formula neg(Formula x) => Seq(Minus,Open,x,Close);
        Formula nonzero(Formula x) => Seq(x,Neq,Sp,zero);
        Formula strict(Formula beta,Formula point) => Lt(norm(App(e,a,beta,point)),Call("re",App(e,a,beta,Cast(Call("re",point),complex))));
        Formula alphaRange(Formula f) => All("alpha",real,Implies(And(Lt(one,a),Lt(a,two)),f));
        Formula source(Formula f) => All("E",FamilyType(),Implies(Call("IsSourceSeries",e),f));
        if(kind=="coefficient") return All("alpha",real,Equal(coeff,div(neg(one),Call("RealGamma",Subtract(neg(a),one)))));
        if(kind=="coefficientFormula") return alphaRange(And(Equal(coeff,div(Multiply(Multiply(a,Subtract(a,one)),Add(a,one)),Call("RealGamma",Subtract(two,a)))),Lt(zero,coeff)));
        if(kind=="tilt") return All("alpha",real,Equal(tilt,Call("tan",div(Multiply(Seq(Pi,Sp),Subtract(two,a)),Num(4)))));
        if(kind=="direction") return All("alpha",real,Equal(direction,Add(neg(one),Multiply(tilt,imag))));
        if(kind=="parameters") return alphaRange(And(Lt(zero,tilt),And(nonzero(direction),And(Lt(zero,Call("margin",a,direction)),And(Equal(Call("re",direction),neg(one)),Equal(sq(norm(direction)),Add(one,sq(tilt))))))));
        if(kind=="expansion") return source(EndpointParameters(Equal(App(e,a,endpoint,z),Add(div(coeff,sq(z)),Multiply(div(one,Multiply(two,Seq(Pi,Sp))),EndpointIntegral(div(Num(5),two)))))));
        if(kind=="limit") return source(All("alpha",real,Implies(Lt(one,a),All("w",complex,Implies(And(nonzero(w),Lt(zero,Call("margin",a,w))),Call("Tendsto",MapVariable("r",real,Multiply(sq(r),App(e,a,endpoint,Multiply(r,w)))),F.Id("atTop"),Call("nhds",div(coeff,sq(w)))))))));
        Formula point=Multiply(r,direction);
        if(kind=="failure") return source(alphaRange(Some("r",real,And(Lt(zero,r),strict(endpoint,point)))));
        Formula interval=And(Le(endpoint,b),Le(b,Add(endpoint,eps)));
        Formula radius=Some("r",real,And(Lt(zero,r),Equal(z,point)));
        return source(alphaRange(Some("z",complex,Some("epsilon",real,And(Lt(zero,eps),And(Lt(eps,one),And(Lt(zero,Call("im",z)),And(radius,All("beta",real,Implies(interval,strict(b,z)))))))))));
    }

    private static Formula MapVariable(string n,Formula type,Formula f) => Seq(Open,F.Id(n),Colon,type,Sp,Mapsto,Sp,f,Close);
    private static Formula EndpointIntegral(Formula c)
    {
        Formula y=F.Id("y"), imaginary=Seq(Operatorname,Grp(F.Id("ComplexI")));
        return Call("integral",MapVariable("y",F.Id("Real"),Call("kernel",F.Id("alpha"),Subtract(F.Id("alpha"),Num(1)),F.Id("z"),Add(c,Multiply(y,imaginary)))));
    }
    private static Formula EndpointParameters(Formula f)
    {
        Formula alpha=F.Id("alpha"), z=F.Id("z");
        Formula hypotheses=And(Seq(z,Neq,Sp,Num(0)),Lt(Num(0),Call("margin",alpha,z)));
        return All("alpha",F.Id("Real"),Implies(Lt(Num(1),alpha),All("z",F.Id("Complex"),Implies(hypotheses,f))));
    }

    private static Formula SeriesFormula()
    {
        Formula e = F.Id("E");
        Formula alpha = F.Id("alpha");
        Formula beta = F.Id("beta");
        Formula z = F.Id("z");
        Formula k = F.Id("k");
        Formula summand = new Formula.Fraction(new Formula.Power(z, k),
            Cast(App(Qualified("Real", "Gamma"), Add(Multiply(alpha, Cast(k, F.Id("Real"))), beta)),
                F.Id("Complex")));
        Formula sequence = Parenthesized(Seq(Parenthesized(Seq(k, Colon, Sp, F.Id("Nat"))),
            Sp, Mapsto, Sp, summand));
        Formula sums = All("beta", F.Id("Real"), All("z", F.Id("Complex"),
            Call("HasSum", sequence, App(e, alpha, beta, z))));
        Formula parameters = All("alpha", F.Id("Real"), Implies(Lt(Num(0), alpha), sums));
        return All("E", FamilyType(), Iff(Call("IsSourceSeries", e), parameters));
    }

    private static Formula ReciprocalFormula()
    {
        Formula e = F.Id("E");
        Formula alpha = F.Id("alpha");
        Formula beta = F.Id("beta");
        Formula x = F.Id("x");
        Formula value = App(Qualified("Complex", "re"),
            App(e, alpha, beta, Cast(x, F.Id("Complex"))));
        Formula equation = Equal(Call("reciprocal", e, alpha, beta, x),
            new Formula.Fraction(Num(1), value));
        return All("E", FamilyType(), All("alpha", F.Id("Real"),
            All("beta", F.Id("Real"), All("x", F.Id("Real"), equation))));
    }

    private static Formula ClaimBody()
    {
        Formula e = F.Id("E");
        Formula alpha = F.Id("alpha");
        Formula beta = F.Id("beta");
        Formula z = F.Id("z");
        Formula x = F.Id("x");
        Formula interval = And(Le(Subtract(alpha, Num(1)), beta), Le(beta, alpha));
        Formula global = All("z", F.Id("Complex"), Le(
            App(Qualified("Complex", "re"), App(e, alpha, beta,
                Cast(App(Qualified("Complex", "re"), z), F.Id("Complex")))),
            new Formula.Norm(App(e, alpha, beta, z))));
        Formula positive = All("x", F.Id("Real"), Implies(Lt(Num(0), x),
            Lt(Num(0), Call("reciprocal", e, alpha, beta, x))));
        Formula cm = App(Qualified("D5", "S3", "Analytic", "ExpRatioCM", "Defs", "CompletelyMonotoneOn"),
            App(F.Id("reciprocal"), e, alpha, beta));
        Formula equivalences = And(Iff(global, interval), Iff(interval, And(positive, cm)));
        Formula hypotheses = Implies(Lt(Num(1), alpha),
            Implies(Lt(alpha, Num(2)), Implies(Le(Num(0), beta), equivalences)));
        Formula parameters = All("alpha", F.Id("Real"), All("beta", F.Id("Real"), hypotheses));
        Formula family = All("E", FamilyType(), Implies(Call("IsSourceSeries", e), parameters));
        return And(new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("E"),
            FamilyType(), Call("IsSourceSeries", e)), family);
    }

    private static Formula FamilyType() => new Formula.TypeArrow(F.Id("Real"),
        new Formula.TypeArrow(F.Id("Real"), new Formula.TypeArrow(F.Id("Complex"), F.Id("Complex"))));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => App(F.Id(name), arguments);
    private static Formula Cast(Formula value, Formula type) => Call("val", value, type);
    private static Formula Qualified(params string[] names) =>
        Seq(names.SelectMany((name, index) => index == 0
            ? new[] { Operatorname, Grp(F.Id(name)) }
            : new[] { Dot, Operatorname, Grp(F.Id(name)) }).ToArray());
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
}
