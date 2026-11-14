using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class PositiveRankOneWeightObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Semigroups/PositiveRankOneWeightObstruction.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ContinuousObservables/madouremizovvafadar2024semigroups");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive rank-one semigroup on the unit interval has no equivalent contractive weighted essential sup norm.",
        H("Positive rank-one obstruction to weighted L∞ contraction"),
        Blocks(
            Paragraph(Text("Madou–Remizov–Vafadar (eds.), Open problems in one-parameter operator semigroups theory, "
                + "arXiv:2410.00416v2, §6, Problem 22, equation (3), asks for g>0 almost everywhere with g and 1/g "
                + "essentially bounded and ‖gT(t)f‖∞≤‖gf‖∞ for every complex f in L²∩L∞. The comments on p. 18 "
                + "suggest positivity as a restriction. This result gives a positive counterexample in the bounded, "
                + "self-adjoint, full-domain angle-zero case. It does not settle Problems 21, 23 or 24, and does not "
                + "claim a first resolution of the unrestricted Problem 22 or literature priority.")),
            Entry("measure", "μ", "The unit-interval measure",
                Eqn(V("mu"), Call("restrict", V("volume"), Call("Ioo", D(0), D(1)))),
                "The measure is real Lebesgue measure restricted to (0,1). Its total mass is one; in particular it is finite and sigma-finite."),
            Entry("hilbert", "H", "The actual complex L2 space",
                Eqn(V("H"), Call("Lp", Complex, D(2), V("mu"))),
                "H is Mathlib's complex Lp at exponent 2 over mu. Every essential sup norm in the claim uses this same measure."),
            Entry("vector", "h", "The L2 vector with vanishing essential floor",
                Eqn(V("h"), Call("toLp", Map("x", Real, Call("ofReal", V("x"))))),
                "The toLp class is constructed from the proved square-integrability of x↦(x:ℂ). Its representative equals x almost everywhere, "
                + "and its squared Hilbert norm is exactly 1/3."),
            Entry("projection", "P", "The orthogonal rank-one projection",
                Eqn(V("P"), Call("starProjection", Call("spanC", V("h")))),
                "The existing orthogonal projection onto the complex span of h is used directly. The compiled representative formula is "
                + "P f(x)=3 x ∫ y f(y) dmu(y), for every complex L2 input f. The inner product in Lean is conjugate-linear in its first argument; "
                + "therefore P f=3⟨h,f⟩h. This operator is idempotent and positive on real nonnegative representatives."),
            Entry("generator", "A", "The bounded nonnegative generator",
                Eqn(V("A"), Sub(V("I"), V("P"))),
                "A is I−P, equivalently the orthogonal projection onto the orthogonal complement of h. It is bounded and self-adjoint, "
                + "and ⟨u,Au⟩=‖Au‖². The zero eigenvector h is retained; no strict coercivity or strict spectral stability is assumed."),
            Entry("semigroup", "T", "The actual complex-time semigroup",
                All("z", Complex, Eqn(Call("T", V("z")), Add(V("P"),
                    Call("smul", Call("exp", MinusOf(V("z"))), V("A"))))),
                "A continuous algebra map (a,b)↦aP+bA sends the scalar pair exponential to the operator exponential. Hence T(z)=exp(−zA), "
                + "T(0)=I and T(z+w)=T(z)T(w). The operator-valued function is entire with derivative −A at zero. Orthogonal Pythagoras "
                + "gives ‖T(z)‖≤1 whenever Re z≥0. The actual representative is e^(−z)f(x)+(1−e^(−z))3x∫yf(y)dmu(y). "
                + "For real t≥0 this preserves the real positive cone and has uniform actual L∞ bound 3/2."),
            Entry("form", "form", "The source inner-product convention",
                All("B", Op, All("u", V("H"), All("v", V("H"),
                    Eqn(Call("form", V("B"), V("u"), V("v")),
                        Call("innerC", V("v"), Apply(V("B"), V("u"))))))),
                "For any bounded complex linear B, form B u v is ⟨v,Bu⟩ in Lean's convention. Thus it is linear in u and conjugate-linear in v, "
                + "as in the source's ⟨Bu,v⟩ convention. Its domain is the full Hilbert space. The association condition tested in claim "
                + "characterizes w=Bu by form B u v=⟨v,w⟩ for every v."),
            Entry("form-norm", "formNorm", "The actual form norm",
                All("B", Op, All("u", V("H"), Eqn(Call("formNorm", V("B"), V("u")),
                    Call("sqrt", Add(Sq(Norm(V("u"))), Re(Form(V("B"), V("u"), V("u")))))))),
                "For A, the diagonal form is real and nonnegative, and ‖u‖≤formNorm A u≤√2‖u‖. Every form-norm Cauchy sequence converges "
                + "in that form norm, by completeness of the actual L2 Hilbert norm and these two inequalities. This establishes closedness "
                + "on the full dense domain; it is not a surrogate for the weighted essential sup norm."),
            Entry("claim", "claim", "The source-faithful restricted weight assertion", Claim(),
                "The displayed implications state, in order: bounded self-adjoint B; angle-zero sectoriality; association of B to its full-domain "
                + "form; sesquilinearity; continuity; density; completeness in the actual form norm; the operator exponential formula; the identity "
                + "at zero and semigroup law; entire analyticity and generator derivative; right-half-plane operator contractivity; positivity "
                + "on real nonnegative representatives; the uniform 3/2 actual L∞ bound. The conclusion quantifies a measurable real positive "
                + "weight and its bounded reciprocal, and all real times and complex inputs in L²∩L∞. AE denotes mu-almost-everywhere; "
                + "Linf(f) means the actual eLpNorm f infinity mu, not a newly defined scalar norm. CLM means bounded complex linear maps; "
                + "innerC is Lean's complex inner product; eval selects an actual AE representative; MemLp uses the same mu."),
            Entry("refutation", "result", "No equivalent positive weight contracts this positive semigroup",
                Seq(Neg, Sp, V("claim")),
                "The proof supplies B=A and S=T and discharges every form and semigroup premise in Lean. Suppose a weight existed and put "
                + "w=1/g. Finite measure and essential boundedness put this real positive test function into the actual complex L²∩L∞. "
                + "The weighted input is one almost everywhere. The actual eLpNorm bound at the single time t=1 gives T(1)w≤w. "
                + "The representative formula and 1−e^(−1)>0 imply Pw≤w. The integral of x(w−Pw) vanishes because ∫x²=1/3; its integrand "
                + "is nonnegative. The existing integral-zero criterion and x>0 almost everywhere give w=Pw=cx almost everywhere. "
                + "Boundedness of g gives w a positive essential lower bound epsilon. For arbitrary real c and epsilon>0 the proof constructs "
                + "delta=min(1/2,epsilon/(2(|c|+1)))>0. The interval (0,delta) has positive mu measure and satisfies cx<epsilon throughout, "
                + "contradicting that lower bound. This explicit positive-measure construction is the consumed non-bind escape witness. "
                + "The faithful-functional rigidity helper is private and consumed by the obstruction; it is not delivered as a standalone wrapper. "
                + "The remaining helpers organize direct applications of pinned Mathlib and are consumed by this result. "
                + "The proof uses complex inputs throughout the claim, testing a real positive input only for the contradiction. "
                + "The positivity restriction is not a separately numbered conjecture in the source. Novelty and priority outside the checked "
                + "sources remain ASSUMED-UNVERIFIED. The existing damped rotating counterexample retains its separate attribution.", true))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, bool theorem = false) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, V(x), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string x, Formula type, Formula body) =>
        Seq(Exists, Sp, V(x), Colon, Sp, type, Comma, Sp, body);
    private static Formula Map(string x, Formula type, Formula body) =>
        Seq(Open, V(x), Colon, Sp, type, Close, Mapsto, Sp, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) =>
        new Formula.Relation(a, op, b);
    private static Formula Eqn(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Par(a), op, Par(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Binary(Formula a, FormulaBinaryOperator op, Formula b) =>
        new Formula.Binary(a, op, b);
    private static Formula Add(Formula a, Formula b) => Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sq(Formula a) => new Formula.Power(a, D(2));
    private static Formula MinusOf(Formula a) => Seq(Minus, Par(a));
    private static Formula Arrow(Formula a, Formula b) => Seq(Par(a), To, Sp, b);
    private static Formula Apply(Formula f, Formula x) => Call("apply", f, x);
    private static Formula Norm(Formula a) => Call("norm", a);
    private static Formula Re(Formula a) => Call("re", a);
    private static Formula Im(Formula a) => Call("im", a);
    private static Formula Form(Formula b, Formula u, Formula v) => Call("form", b, u, v);
    private static Formula Fn(Formula b, Formula u) => Call("formNorm", b, u);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Op => Call("CLM", Complex, V("H"), V("H"));
    private static Formula Eval(Formula f, Formula x) => Call("eval", f, x);
    private static Formula AE(string x, Formula body) => Call("AE", V("mu"), Map(x, Real, body));
    private static Formula Linf(Formula f) => Call("eLpNorm", f, Infty, V("mu"));
    private static Formula Bounded(Formula f) => Call("MemLp", f, Infty, V("mu"));
    private static Formula Positive(Formula f) => AE("x", And(
        Le(D(0), Re(Eval(f, V("x")))), Eqn(Im(Eval(f, V("x"))), D(0))));
    private static Formula HalfThree => Call("divide", D(3), D(2));
    private static Formula Image(Formula t, Formula f) =>
        Apply(Apply(V("S"), Call("ofReal", t)), f);

    private static Formula Sesquilinear() => All("u", V("H"), All("v", V("H"),
        All("w", V("H"), All("c", Complex,
        And(Eqn(Form(V("B"), Add(V("u"), V("v")), V("w")),
                Add(Form(V("B"), V("u"), V("w")), Form(V("B"), V("v"), V("w")))),
        And(Eqn(Form(V("B"), Call("smul", V("c"), V("u")), V("v")),
                Mul(V("c"), Form(V("B"), V("u"), V("v")))),
        And(Eqn(Form(V("B"), V("u"), Add(V("v"), V("w"))),
                Add(Form(V("B"), V("u"), V("v")), Form(V("B"), V("u"), V("w")))),
            Eqn(Form(V("B"), V("u"), Call("smul", V("c"), V("v"))),
                Mul(Call("conj", V("c")), Form(V("B"), V("u"), V("v")))))))))));

    private static Formula Cauchy() => All("e", Real, Imp(Lt(D(0), V("e")),
        Ex("N", Nat, All("m", Nat, Imp(Le(V("N"), V("m")), All("n", Nat,
            Imp(Le(V("N"), V("n")), Lt(Fn(V("B"), Sub(Apply(V("s"), V("m")), Apply(V("s"), V("n")))), V("e")))))))));
    private static Formula Limit() => Ex("u", V("H"), All("e", Real, Imp(Lt(D(0), V("e")),
        Ex("N", Nat, All("n", Nat, Imp(Le(V("N"), V("n")),
            Lt(Fn(V("B"), Sub(Apply(V("s"), V("n")), V("u"))), V("e"))))))));

    private static Formula Weight()
    {
        Formula g = V("g"), x = V("x"), f = V("f");
        Formula weighted(Formula u) => Map("x", Real,
            Mul(Call("ofReal", Apply(g, x)), Eval(u, x)));
        Formula contract = All("t", Real, Imp(Le(D(0), V("t")), All("f", V("H"),
            Imp(Bounded(f), Le(Linf(weighted(Image(V("t"), f))), Linf(weighted(f)))))));
        return Ex("g", Arrow(Real, Real), And(Call("Measurable", g),
            And(Bounded(g), And(Bounded(Map("x", Real, Call("inv", Apply(g, x)))),
            And(AE("x", Lt(D(0), Apply(g, x))), contract)))));
    }

    private static Formula Claim()
    {
        Formula b = V("B"), s = V("S"), u = V("u"), v = V("v"), w = V("w"), z = V("z");
        Formula association = All("u", V("H"), All("w", V("H"),
            Iff(All("v", V("H"), Eqn(Form(b,u,v), Call("innerC",v,w))), Eqn(w,Apply(b,u)))));
        Formula formContinuous = Call("Continuous", Map("p", Call("Prod",V("H"),V("H")),
            Form(b,Call("fst",V("p")),Call("snd",V("p")))));
        Formula[] hypotheses = [
            Call("IsSelfAdjoint", b),
            All("u",V("H"),And(Le(D(0),Re(Form(b,u,u))),Eqn(Im(Form(b,u,u)),D(0)))),
            association,
            Sesquilinear(),
            formContinuous,
            Call("Dense", Call("univ", V("H"))),
            All("s",Arrow(Nat,V("H")),Imp(Cauchy(),Limit())),
            All("z",Complex,Eqn(Apply(s,z),Call("exp",Call("smul",MinusOf(z),b)))),
            Eqn(Apply(s,D(0)),V("I")),
            All("z",Complex,All("w",Complex,Eqn(Apply(s,Add(z,w)),Mul(Apply(s,z),Apply(s,w))))),
            All("z",Complex,Call("AnalyticAt",Complex,s,z)),
            Call("HasDerivAt",s,MinusOf(b),D(0)),
            All("z",Complex,Imp(Le(D(0),Re(z)),Le(Norm(Apply(s,z)),D(1)))),
            All("t",Real,Imp(Le(D(0),V("t")),All("f",V("H"),
                Imp(Positive(V("f")),Positive(Image(V("t"),V("f"))))))),
            All("t",Real,Imp(Le(D(0),V("t")),All("f",V("H"),
                Imp(Bounded(V("f")),Le(Linf(Image(V("t"),V("f"))),
                    Mul(Call("ofRealENN",HalfThree),Linf(V("f"))))))))
        ];
        Formula body = Weight();
        for (int i = hypotheses.Length-1; i >= 0; --i) body = Imp(hypotheses[i],body);
        return Iff(V("claim"),All("B",Op,All("S",Arrow(Complex,Op),body)));
    }
}
