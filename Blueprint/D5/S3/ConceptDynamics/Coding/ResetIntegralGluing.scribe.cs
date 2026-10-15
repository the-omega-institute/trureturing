using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ResetIntegralGluingDocument : IScribeDocumentDefinition
{
    private static Formula I(string s) => F.Id(s);
    private static Formula.BoundVariable B(string s, Formula t) => new(FormulaIdentifier.Create(s), t);
    private static Formula All(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. v], f);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Conj(params Formula[] c)
    {
        Formula f = c[^1];
        for (int j = c.Length - 2; j >= 0; --j) f = And(c[j], f);
        return f;
    }
    private static Formula Q(string s) => Call(s, I("q"));
    private static Formula Scope(Formula f) => All(new Formula.Logic(Call("positive", I("q")),
        FormulaLogicOperator.Implies, f), B("q", I("Nat")));
    private static Formula P(string s, Formula p) => Call(s, I("q"), p);
    private static Formula Pair(Formula a, Formula b) => Call("pair", a, b);
    private static Formula Value(Formula a) => Call("value", a);
    private static Formula Diff => Call("sub", P("a0", Call("fst", Value(I("z")))),
        P("b0", Call("snd", Value(I("z")))));
    private static DocumentBlock Entry(string n, string h, Formula f, string prose) => Describe.Lean(
        DescribeId.Create(n.Replace('_','-')), DeclarationHandle.Create(
            "D5/S3/ConceptDynamics/Coding/ResetIntegralGluing." + n),
        H(h), StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral sign components are glued by their literal common residue, with a canonical inverse.",
        H("Integral sign gluing and coefficient halves"),
        Blocks(
            Paragraph(Text("For q natural put S(q)=sum over k<q of X^k, f(q)=X^q-S(q), "
                + "g(q)=X^q+S(q), F(q)=f(q)g(q), and W(q)=S(q)-(X-1)X^q. "
                + "Plus(q) and Minus(q) are the literal integer polynomial quotients by f and g. "
                + "reduce maps each integer coefficient to ZMod 2 and fixes X. Common(q) is "
                + "(ZMod 2)[X]/reduce(g(q)); g(q)=S(q+1). The ring maps rplus and rminus descend "
                + "this same coefficient reduction. Compatible(q) is their RingHom.pullback subring "
                + "of Plus(q) times Minus(q). fp is the original ResetSignIntegerCyclic quotient map.")),
            Entry("sign_ideals", "The actual sum and intersection ideals",
                All(And(
                    Equal(Call("sup", Call("span", Q("f")), Call("span", Q("g"))),
                        Call("spanPair", Num(2), Q("g"))),
                    Equal(Call("inf", Call("span", Q("f")), Call("span", Q("g"))),
                        Call("span", Q("F")))), B("q", I("Nat"))),
                "span is the principal ideal in Int[X], spanPair generates an ideal with two elements, "
                + "and sup and inf are the ideal sum and intersection. The geometric identity supplied "
                + "by ResetSignIntegerCyclic gives X*f+(2-X)*g=2. Since f=g-2*S, the sum is (2,g). "
                + "For a common multiple f*a=g*b the same certificate makes 2*b a multiple of f. "
                + "Take its monic f remainder. Remainders commute with integer scalar multiplication, "
                + "and each integer coefficient is free of two-torsion. Thus f divides b and F divides "
                + "the common multiple. Integral comaximality is neither assumed nor used."),
            Entry("compatible_even", "Compatibility detects every even remainder coefficient",
                All(Call("divides", Num(2), Call("coeff", Diff, I("i"))),
                    B("q", I("Nat")), B("z", Q("Compatible")), B("i", I("Nat"))),
                "a0 and b0 are AdjoinRoot.modByMonicHom for the monic degree-q polynomials f and g. "
                + "They are canonical representatives, including zero. Mapping these remainders to "
                + "characteristic two agrees with the common monic remainder. The compatibility "
                + "equation therefore makes reduce(a0-b0)=0, so every integer coefficient is even. "
                + "No nonnegative-coefficient assumption is present."),
            Entry("integral_gluing", "The literal equivalence and both inverse identities",
                Scope(Conj(
                    All(Equal(P("fromCompatible", P("toCompatible", I("v"))), I("v")), B("v", Q("QF"))),
                    All(Equal(P("toCompatible", P("fromCompatible", I("z"))), I("z")), B("z", Q("Compatible"))),
                    All(Equal(Value(P("gluing", P("fp", I("p")))),
                        Pair(Call("mk", Q("f"), I("p")), Call("mk", Q("g"), I("p")))),
                        B("p", I("IntPolynomial"))),
                    All(Equal(Call("inverseApply", Q("gluing"), I("z")),
                        P("fp", Call("sub", P("a0", Call("fst", Value(I("z")))),
                            Call("mul", Call("mul", I("X"), Q("f")), Call("half", Diff))))),
                        B("z", Q("Compatible"))),
                    All(And(Call("degreeLess", P("a0", Call("fst", Value(I("z")))), I("q")),
                        Call("degreeLess", P("b0", Call("snd", Value(I("z")))), I("q"))),
                        B("z", Q("Compatible"))),
                    All(Equal(Call("half", Diff), Call("coefficientHalfRangeSum", I("q"), Diff)),
                        B("z", Q("Compatible"))))
                    ),
                "positive(q) means 0<q. degreeLess is polynomial degree strictly below q, including zero. "
                 + "coefficientHalfRangeSum(q,p) is sum over i<q of monomial i (p.coeff(i)/2). "
                + "mk denotes the indicated polynomial quotient map; value forgets "
                + "pullback membership. half divides every coefficient by 2 using integer Euclidean "
                + "division, so negative coefficients are included. Since a0-b0=2*half(a0-b0), "
                + "the polynomial p=a0-X*f*half(a0-b0) projects to a0 modulo f and to b0 modulo g: "
                + "p-b0=(2-X)*g*half(a0-b0). This proves the pullback-side inverse identity. "
                + "The intersection ideal identity reflects equality from both components back to "
                + "QF, proving the other inverse identity. gluing has toCompatible as its forward "
                + "ring homomorphism and this exact fromCompatible as its inverse. All positive q, "
                + "including q=1, are retained; no entropy assertion occurs."),
            Entry("gluing_generators", "Forward time, original sign, scalars and the common quotient",
                All(Conj(
                    Equal(Value(P("gluing", P("fp", I("X")))),
                        Pair(Call("root", Q("f")), Call("root", Q("g")))),
                    Equal(Value(P("gluing", P("fp", Q("W")))), Pair(Num(1), Call("neg", Num(1)))),
                    All(Equal(Value(P("gluing", P("fp", Call("C", I("z"))))),
                        Pair(Call("integerCastPlus", I("z")), Call("integerCastMinus", I("z")))),
                        B("z", I("Int"))),
                    All(Equal(P("commonQuotientEquiv", Call("mkSumIdeal", I("p"))),
                        P("commonPolynomial", I("p"))), B("p", I("IntPolynomial"))),
                    Equal(Call("reduce", Q("g")), Call("geometricSum", Call("succ", I("q"))))),
                    B("q", I("Nat"))),
                "commonQuotientEquiv identifies Int[X] modulo the actual sum ideal with Common(q). "
                + "Its map is literally coefficient reduction followed by the common quotient, fixing X. "
                + "Its kernel proof uses monic division by g and evenness of the remainder; coefficient "
                + "lifts give surjectivity. The identities W=1-X*f and W=-1+(2-X)*g give the two sign "
                + "images. Each integer maps to the same integer in both components. "
                + "At q=1 this is the congruence pullback of two copies of Int over the two-element field."),
            Paragraph(Text("The construction is a repository derivation from standard quotient, monic division "
                + "and pullback APIs in pinned Mathlib, together with ResetSignIntegerCyclic's literal "
                + "geometric certificate. It supplies the integral reconstruction used by ResetIntegralUnits "
                + "and the original native action in ResetNativeUnitNormalForm; no literature novelty is claimed. "
                + "Uniform eigenlattices, conductor, additive cokernel and common-residue action are further "
                + "consequences requiring their own statements. Compatible is a subring containing one, "
                + "so its quotient inside the product would be additive, not a ring quotient.")))));
}
