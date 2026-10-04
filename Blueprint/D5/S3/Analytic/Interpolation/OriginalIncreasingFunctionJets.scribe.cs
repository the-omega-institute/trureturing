using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class OriginalIncreasingFunctionJetsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/burkeharismadhavendra2025repeatedintegrals");
    private static Formula V(string name) => F.Id(name);
    private static Formula R => Call("Real");
    private static Formula N => Call("Nat");
    private static Formula FunctionType => new Formula.TypeArrow(R, R);
    private static Formula NP => Add(V("n"), Num(1));
    private static Formula FinType => Call("Fin", NP);
    private static Formula VectorType => new Formula.TypeArrow(FinType, R);
    private static Formula Interval => Call("unitInterval");
    private static Formula Q(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula E(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Mem(Formula a, Formula b) => Rel(a, FormulaRelationOperator.MemberOf, b);
    private static Formula LtF(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(params Formula[] clauses) => clauses.Aggregate((a, b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Fn(string variable, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, V(variable), Colon, Sp, type, Comma, Sp, body);
    private static Formula Integral(Formula domain, Formula body) =>
        Seq(Int, Underscore, Grp(V("t"), Sp, InMacro, Sp, domain), Sp, body, Sp, Call("dt"));
    private static Formula Gamma(string n, Formula t) => Call("gamma", V(n), t);
    private static Formula Jet(Formula j, Formula x) => Call("jet", j, V("f"), x);
    private static Formula EndpointJets() => Q("j", FinType,
        And(Equal(Jet(Call("val", V("j")), Num(0)), Num(0)),
            Equal(Jet(Call("val", V("j")), Num(1)), Apply(V("b"), V("j")))));
    private static Formula WDefinition()
    {
        Formula property = E("f", FunctionType, And(
            Call("ContDiffOn", R, Call("NatToWithTopNatInfinity", V("n")), V("f"), Interval),
            Call("MonotoneOn", Call("jet", V("n"), V("f")), Interval),
            E("x", R, And(Mem(V("x"), Interval), E("y", R,
                And(Mem(V("y"), Interval), NotEqual(Jet(V("n"), V("x")), Jet(V("n"), V("y"))))))),
            EndpointJets()));
        return Q("n", N, Equal(Call("W", V("n")),
            Seq(OpenBrace, V("b"), Colon, Sp, VectorType, Sp, Mid, Sp, property, CloseBrace)));
    }
    private static Formula PDefinition() => Q("n", N, Equal(Call("P", V("n")), And(
        Call("IsOpen", Call("W", V("n"))),
        Q("b", VectorType, Imp(Mem(V("b"), Call("W", V("n"))), E("f", FunctionType, And(
            Call("ContDiffOn", R, Infty, V("f"), Interval), EndpointJets(),
            Q("x", R, Imp(Mem(V("x"), Call("Ioo", Num(0), Num(1))), LtF(Num(0), Jet(NP, V("x"))))),
            Equal(Jet(NP, Num(0)), Num(1)), Equal(Jet(NP, Num(1)), Num(1)),
            Q("j", N, Imp(LtF(NP, V("j")), And(Equal(Jet(V("j"), Num(0)), Num(0)),
                Equal(Jet(V("j"), Num(1)), Num(0))))))))))));
    private static Formula FinsuppType => Call("Finsupp", Call("Param"),
        Call("Subtype", Fn("a", R, Rel(Num(0), FormulaRelationOperator.LessThanOrEqual, V("a")))));
    private static Formula Density(Formula xi, Formula sigma, Formula t) => Call("density", xi, sigma, t);
    private static Formula FlatWeight(Formula t) => Multiply(Call("expNegInvGlue", t),
        Call("expNegInvGlue", Subtract(Num(1), t)));
    private static Formula Gaussian(Formula xi, Formula sigma, Formula t) => Call("exp",
        new Formula.Negate(new Formula.Fraction(new Formula.Power(Subtract(t, xi), Num(2)),
            new Formula.Power(sigma, Num(2)))));
    private static Formula Cut(Formula delta, Formula t) => Add(
        Call("smoothTransition", Subtract(Num(2), new Formula.Fraction(Multiply(Num(2), t), delta))),
        Call("smoothTransition", Subtract(Num(2), new Formula.Fraction(
            Multiply(Num(2), Subtract(Num(1), t)), delta))));
    private static DocumentBlock Definition(string name, Formula formula, string description,
        string ns = "PnOriginal", AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("pn-original-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.FromAuthor(Disp(formula)), provenance ?? AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ns + "." + name + ": " + description))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original all-order endpoint-jet assertion, with its monotone input class and one simultaneous smooth witness.",
        H("Original increasing-function endpoint jets"), Blocks(
            Definition("unitInterval", Equal(Interval, Call("Icc", Num(0), Num(1))),
                "The closed real interval [0,1]. Every endpoint derivative below is iteratedDerivWithin on this interval."),
            Definition("primitive", Q("g", FunctionType, Q("x", R,
                Equal(Call("primitive", V("g"), V("x")), Seq(Int, Underscore, Grp(Num(0)),
                    Caret, Grp(V("x")), Sp, Call("g", V("s")), Sp, Call("ds"))))),
                "The variable s is bound by the interval integral; its orientation is from 0 to x."),
            Definition("repeatedIntegral", Q("k", N, Q("g", FunctionType,
                Equal(Call("repeatedIntegral", V("k"), V("g")),
                    Call("iterate", Call("primitive"), V("k"), V("g"))))),
                "Function.iterate applies primitive k times; k=0 returns g."),
            Definition("jet", Q("j", N, Q("f", FunctionType,
                Equal(Call("jet", V("j"), V("f")), Call("iteratedDerivWithin", V("j"), V("f"), Interval)))),
                "The full one-sided endpoint convention is iteratedDerivWithin j f unitInterval, including j=0."),
            Definition("W", WDefinition(),
                "The source defines W_n using f in C^n[0,1], increasing and nonconstant D^n f, and all endpoint jets from 0 through n. Increasing means nondecreasing. NatToWithTopNatInfinity denotes the actual natural-order coercion in ContDiffOn. No strict input monotonicity or absolute continuity is assumed.",
                provenance: AssessedProvenance.FromLiterature(Source)),
            Definition("P", PDefinition(),
                "The source's (P_n) requires openness of W_n and one C-infinity witness for each b in W_n, with all original finite endpoint jets, positive order n+1 derivative in (0,1), value 1 at both endpoints at that order, and zero at both endpoints at every higher order.",
                provenance: AssessedProvenance.FromLiterature(Source)),
            Definition("clamp", Q("x", R, Equal(Call("clamp", V("x")),
                Call("max", Num(0), Call("min", Num(1), V("x"))))), "Clamp to the original closed interval."),
            Definition("extend", Q("g", FunctionType, Equal(Call("extend", V("g")),
                Seq(V("g"), Sp, Circ, Sp, Call("clamp")))), "Compose g with clamp."),
            Definition("Vec", Q("n", N, Equal(Call("Vec", V("n")), VectorType)),
                "The actual finite real-coordinate carrier.", "PnActualMixtureConsumer"),
            Definition("Center", Equal(Call("Center"), Call("Subtype", Call("Icc", Num(0), Num(1)))),
                "Center is the subtype of the closed real interval, so endpoints are retained.", "PnActualMixtureConsumer"),
            Definition("Width", Equal(Call("Width"), Call("Subtype", Call("Ioi", Num(0)))),
                "Width is the subtype of positive real numbers.", "PnActualMixtureConsumer"),
            Definition("Param", Equal(Call("Param"), Call("Prod", Call("Center"), Call("Width"))),
                "The center-width product subtype.", "PnActualMixtureConsumer"),
            Definition("gamma", Q("n", N, Q("t", R, Equal(Call("gamma", V("n"), V("t")),
                Fn("k", FinType, new Formula.Power(Subtract(Num(1), V("t")), Call("val", V("k"))))))),
                "Every finite index is coerced to its natural value before exponentiation.", "PnActualMixtureConsumer"),
            Definition("raw", Q("xi", R, Q("sigma", R, Q("t", R,
                Equal(Call("raw", V("xi"), V("sigma"), V("t")), Multiply(FlatWeight(V("t")),
                    Gaussian(V("xi"), V("sigma"), V("t"))))))),
                "The explicit flat smooth weight times the Gaussian factor; exp is Real.exp.", "PnActualMixtureConsumer"),
            Definition("z", Q("xi", R, Q("sigma", R, Equal(Call("z", V("xi"), V("sigma")),
                Integral(Call("Icc", Num(0), Num(1)), Call("raw", V("xi"), V("sigma"), V("t")))))),
                "The Lean definition is the interval integral 0..1; the Icc volume integral is equal on these ordered endpoints.", "PnActualMixtureConsumer"),
            Definition("density", Q("xi", R, Q("sigma", R, Q("t", R,
                Equal(Density(V("xi"), V("sigma"), V("t")), new Formula.Fraction(
                    Call("raw", V("xi"), V("sigma"), V("t")), Call("z", V("xi"), V("sigma"))))))),
                "Division is real division.", "PnActualMixtureConsumer"),
            Definition("moment", Q("n", N, Q("xi", R, Q("sigma", R,
                Equal(Call("moment", V("n"), V("xi"), V("sigma")), Integral(Call("Icc", Num(0), Num(1)),
                    Call("smul", Density(V("xi"), V("sigma"), V("t")), Gamma("n", V("t")))))))),
                "The actual Bochner moment vector over the closed interval.", "PnActualMixtureConsumer"),
            Definition("component", Q("n", N, Q("q", Call("Param"),
                Equal(Call("component", V("n"), V("q")), Call("moment", V("n"),
                    Call("SubtypeToReal", Call("fst", V("q"))), Call("SubtypeToReal", Call("snd", V("q"))))))),
                "Both subtype projections are explicitly coerced to real numbers.", "PnActualMixtureConsumer"),
            Definition("S", Q("n", N, Equal(Call("S", V("n")), Call("PointedConeHull", R,
                Call("range", Fn("t", Call("Center"), Gamma("n", Call("SubtypeToReal", V("t")))))))),
                "PointedConeHull is PointedCone.hull, with nonnegative scalar coefficients.", "PnActualMixtureConsumer"),
            Definition("T", Q("n", N, Equal(Call("T", V("n")), Call("PointedConeHull", R,
                Call("range", Call("component", V("n")))))),
                "The cone generated by the actual density components.", "PnActualMixtureConsumer"),
            Definition("mixture", Q("c", FinsuppType, Q("t", R,
                Equal(Call("mixture", V("c"), V("t")), Seq(Sum, Underscore,
                    Grp(V("q"), Sp, InMacro, Sp, Call("support", V("c"))), Sp,
                    Multiply(Call("SubtypeToReal", Apply(V("c"), V("q"))),
                        Density(Call("SubtypeToReal", Call("fst", V("q"))),
                            Call("SubtypeToReal", Call("snd", V("q"))), V("t"))))))),
                "q is bound by the finite support sum; each nonnegative coefficient and parameter subtype is coerced to Real.", "PnActualMixtureConsumer"),
            Definition("endpointCut", Q("delta", R, Q("t", R,
                Equal(Call("endpointCut", V("delta"), V("t")), Cut(V("delta"), V("t"))))),
                "The two reflected smooth transitions give the endpoint correction.", "PnActualMixtureConsumer"),
            Definition("cutMoment", Q("n", N, Q("delta", R,
                Equal(Call("cutMoment", V("n"), V("delta")), Integral(Call("Icc", Num(0), Num(1)),
                    Call("smul", Call("endpointCut", V("delta"), V("t")), Gamma("n", V("t"))))))),
                "The moment vector of the endpoint correction.", "PnActualMixtureConsumer"),
            Definition("rho", Q("delta", R, Q("c", FinsuppType, Q("t", R,
                Equal(Call("rho", V("delta"), V("c"), V("t")), Add(
                    Call("endpointCut", V("delta"), V("t")), Call("mixture", V("c"), V("t"))))))),
                "One density combines the endpoint correction with a finite nonnegative mixture.", "PnActualMixtureConsumer"),
            Describe.Lean(DescribeId.Create("pn-original-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The original all-order assertion"), StatementSource.FromAuthor(Disp(Q("n", N, Call("P", V("n"))))),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("Conjecture 1.2, arXiv:2512.02151v1, p. 2: '(P_n) is true for all nonnegative integers n.' The mathematical source proves exactly forall n : Nat, PnOriginal.P n.")),
                    Paragraph(Text("The source's W and P use their original closed-interval derivatives. The Stieltjes argument retains singular continuous and flat input derivatives and arbitrary positive mass. Reversed factorial coordinates connect all endpoint jets to one moment vector. The single witness is repeatedIntegral (n+1) rho; the same rho realizes every coordinate and every endpoint condition.")),
                    Paragraph(Text("The coordinate-transform function sends each endpoint-jet vector b to its reversed factorial coordinates:")),
                    Paragraph(Math(Disp(Fn("n", N, Fn("b", VectorType, Fn("k", FinType,
                        Multiply(Call("NatToReal", Call("factorial", Call("val", V("k")))),
                            Apply(V("b"), Call("rev", V("k"))))))))))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("burke-haris-madhavendra-increasing-function-jets"),
                    ResolutionKind.Proved)))));
}
