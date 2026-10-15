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
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Ex(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. v], f);
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
    private static Formula Eigen(Formula sign) => Call("eigenLattice", I("q"), sign);
    private static Formula LatticeSum => Call("sup", Eigen(Num(1)), Eigen(Call("neg", Num(1))));
    private static Formula Twice(Formula a) => Call("mul", Num(2), a);
    private static Formula Product => Call("product", Q("Plus"), Q("Minus"));
    private static Formula ResidueQuotient => Call("additiveQuotient", Q("Compatible"), LatticeSum);
    private static Formula Diff => Call("sub", P("a0", Call("fst", Value(I("z")))),
        P("b0", Call("snd", Value(I("z")))));
    private static DocumentBlock Entry(string n, string h, Formula f, string prose,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create(n.Replace('_','-')), DeclarationHandle.Create(
            "D5/S3/ConceptDynamics/Coding/ResetIntegralGluing." + n),
        H(h), StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role);

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
            Entry("component_residue_kernels", "The component kernels are exactly twice the integral components",
                Scope(And(
                    All(Iff(Equal(P("rplus", I("a")), Num(0)),
                        Ex(Equal(I("a"), Twice(I("u"))), B("u", Q("Plus")))), B("a", Q("Plus"))),
                    All(Iff(Equal(P("rminus", I("b")), Num(0)),
                        Ex(Equal(I("b"), Twice(I("v"))), B("v", Q("Minus")))), B("b", Q("Minus"))))),
                "A vanishing component residue makes the reduction of its canonical monic representative zero. "
                + "The existing coefficient-half construction then gives an explicit integral half, and the "
                + "monic representative inverse recovers the component. Conversely two vanishes in Common, "
                + "as follows from the original commonPolynomial kernel (2,g). No squarefree or field "
                + "hypothesis is imposed on the integral components or the common quotient."),
            Entry("eigenLattice", "The actual sign eigenlattices",
                All(Iff(Call("member", I("z"), Call("eigenLattice", I("q"), I("epsilon"))),
                    Equal(Call("mul", P("gluing", P("fp", Q("W"))), I("z")),
                        Call("integerScale", I("epsilon"), I("z")))),
                    B("q", I("Nat")), B("epsilon", I("Int")), B("z", Q("Compatible"))),
                "eigenLattice(q,epsilon) is an additive subgroup of Compatible(q), defined by multiplication "
                + "by the literal original W. The two relevant integer eigenvalues are one and minus one.",
                DescribeRole.Definition),
            Entry("w_eigenlattices", "The two sign eigenlattices are the even axes",
                Scope(All(And(
                    Iff(Call("member", I("z"), Eigen(Num(1))),
                        Ex(Equal(Value(I("z")), Pair(Twice(I("a")), Num(0))), B("a", Q("Plus")))),
                    Iff(Call("member", I("z"), Eigen(Call("neg", Num(1)))),
                        Ex(Equal(Value(I("z")), Pair(Num(0), Twice(I("b")))), B("b", Q("Minus"))))),
                    B("z", Q("Compatible")))),
                "The literal sign is (1,-1). In the fixed lattice its opposite component has twice itself "
                + "zero, hence is zero: monic integer representatives transport the owner's polynomial "
                + "two_torsion argument to each quotient. Compatibility then puts the remaining component "
                + "in its residue kernel. The negative lattice follows with the components interchanged."),
            Entry("eigenlattice_sum_even_product", "The sum is twice the full product",
                Scope(All(Iff(Call("member", I("z"), LatticeSum),
                    Ex(Equal(Value(I("z")), Pair(Twice(I("a")), Twice(I("b")))),
                        B("a", Q("Plus")), B("b", Q("Minus")))), B("z", Q("Compatible")))),
                "Split an element of the subgroup sum into its two even axes. Conversely both even axes "
                + "are compatible and add to the indicated pair. The halves a and b range independently "
                + "over the integral components; they need not be a compatible pair. Thus this is 2D "
                + "for D=Plus times Minus inside Compatible, rather than a claim that the sum is 2Compatible."),
            Entry("pullback_conductor_even_product", "The conductor in the specified product overring",
                Scope(All(Iff(
                    All(Call("member", Call("mul", I("d"), I("t")), Q("Compatible")), B("t", Product)),
                    Ex(Equal(I("d"), Twice(I("e"))), B("e", Product))), B("d", Product))),
                "The left side tests every multiplier in D=Plus(q) times Minus(q), the stated overring. "
                + "Testing (1,0) and (0,1) forces both component residues to vanish, so the component "
                + "kernel theorem supplies d=2e. Conversely every even product multiplies D into the "
                + "pullback. No normalization, squarefree, or general unit-classification assertion is made."),
            Entry("commonResidue", "The common residue map",
                All(Equal(P("commonResidue", I("z")), P("rplus", Call("fst", Value(I("z"))))),
                    B("q", I("Nat")), B("z", Q("Compatible"))),
                "commonResidue is a ring homomorphism on the pullback. Compatibility identifies this "
                + "first-component residue with rminus applied to the second component.", DescribeRole.Definition),
            Entry("common_residue_surjective", "Every common residue has an integral compatible lift",
                All(Call("surjective", Q("commonResidue")), B("q", I("Nat"))),
                "Use the owner's private common_surjective coefficient lift p, then the compatible pair "
                + "gluing(fp(p)). This helper is consumed by the additive quotient equivalence. "
                + "It asserts no surjectivity of a native centralizer or of the original rho image."),
            Entry("common_residue_kernel", "The residue kernel is the sign eigenlattice sum",
                Scope(Equal(Call("additiveKernel", Q("commonResidue")), LatticeSum)),
                "Zero common residue forces both components into their even kernels. The even-product "
                + "description identifies these pairs with exactly the sum of the sign eigenlattices."),
            Entry("commonResidueQuotientEquiv", "The additive quotient is the common residue group",
                Scope(Call("hasType", Q("commonResidueQuotientEquiv"),
                    Call("AddEquiv", ResidueQuotient, Q("Common")))),
                "This is the generic additive first-isomorphism equivalence after the exact kernel equality. "
                + "It takes the class of every compatible z to commonResidue(z). Compatible contains one "
                + "as a subring of D; the quotient here is by an additive subgroup, not a ring ideal of D.",
                DescribeRole.Definition),
            Entry("common_residue_cardinality", "The common residue and sign quotient each have size two to the q",
                Scope(And(Equal(Call("card", Q("Common")), Call("power", Num(2), I("q"))),
                    Equal(Call("card", ResidueQuotient), Call("power", Num(2), I("q"))))),
                "The common polynomial is monic of degree q after reduction. Its AdjoinRoot power basis "
                + "identifies its additive carrier with Fin(q) to ZMod(2), giving cardinality 2^q. "
                + "The additive equivalence transfers this size to the actual sign quotient. "
                + "Repeated factors, including those at odd q, are retained."),
            Entry("commonTimeUnit", "The literal common forward-time unit",
                All(Call("hasType", Q("commonTimeUnit"), Call("Units", Q("Common"))), B("q", I("Nat"))),
                "Its value is AdjoinRoot.root(reduce(g(q))), literally [X], and its inverse value is [X]^q. "
                + "The geometric polynomial certificate gives [X]^(q+1)=1. This specifies one unit "
                + "without classifying all units of Common(q).", DescribeRole.Definition),
            Entry("exact_common_time_order", "The exact common forward-time order including q equals one",
                And(Equal(Call("orderOf", Call("commonTimeUnit", Num(1))), Num(1)),
                    All(new Formula.Logic(Call("atLeastTwo", I("q")), FormulaLogicOperator.Implies,
                        Equal(Call("orderOf", Q("commonTimeUnit")), Call("succ", I("q")))), B("q", I("Nat")))),
                "atLeastTwo(q) means 2<=q. A smaller positive period m would make reduce(g(q)) divide "
                + "X^m-1. Monic degree comparison forces m=q. Equality of the two monic degree-q "
                + "polynomials then contradicts their X coefficients, which are one and zero for q>=2. "
                + "At q=1 the defining polynomial is X-1, so [X]=1. The proof requires no separability."),
            Paragraph(Text("The construction is a repository derivation from standard quotient, monic division "
                + "and pullback APIs in pinned Mathlib, together with ResetSignIntegerCyclic's literal "
                + "geometric certificate. It supplies the integral reconstruction used by ResetIntegralUnits "
                + "and the original native action in ResetNativeUnitNormalForm; no literature novelty is claimed. "
                + "The uniform eigenlattice sum and conductor, common-residue kernel and quotient, cardinality "
                + "and exact common-time order apply to the original Native groups as described in "
                + "ResetNativeUnitNormalForm. That application uses nativeGluing and its existing "
                + "all-centralizer scalarization; there is no reverse Native dependency in this arithmetic owner. "
                + "Compatible is a subring containing one; the sign quotient used here is additive.")))));
}
