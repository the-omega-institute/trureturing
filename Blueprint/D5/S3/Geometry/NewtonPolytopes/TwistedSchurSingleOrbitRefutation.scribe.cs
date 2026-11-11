using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.NewtonPolytopes;

internal sealed class TwistedSchurSingleOrbitRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/marin2026twistedschur");

    private const string SourceClaim = "If Φ_{t,r}≠0 then {μ:A_μ≠0} has a unique maximal element μ_max for the Weyl majorisation order μ≼μ′⇔μ∈conv(W(C_r) μ′); equivalently, Newt(Φ_{t,r}) is the orbit polytope conv(W(C_r) μ_max).";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A twisted Schur Newton polytope need not be a single signed-permutation orbit.",
        H("A twisted Schur Newton polytope with two competing dominant vertices"),
        Blocks(
            Entry("size", "N", "The alphabet size", Sizes(),
                "Marín, §1.1, p. 1: “Fix t ≥ 1 and r ≥ 1, put N = t + 2r”. The finite alphabet has t frozen roots and r reciprocal pairs.", true),
            Entry("indices", "sourceIndex", "The order of the alphabet", Indices(),
                "The source alphabet, §1.1, p. 1, is x=(1,ζ,…,ζ^(t−1),z₁,z₁⁻¹,…,zᵣ,zᵣ⁻¹). Sum.inl indexes the frozen roots; Sum.inr (Sum.inl k) and Sum.inr (Sum.inr k) index a variable and its reciprocal. sourceIndex gives their zero-based position.", true),
            Entry("delta", "delta", "The denominator exponents", Deltas(),
                "Marín, §1.1, p. 1: “write δ=(N−1,N−2,…,0) and λ=β−δ, so that λ is a partition”. Integer subtraction here is in ℤ.", true),
            Entry("normalization", "NormalizedBeta", "Strict decrease and zero final exponent", Normalization(),
                "Marín, §1.1, p. 1: “For a strictly decreasing β∈ℤᴺ normalised by β_N=0”. The order is the zero-based sourceIndex order, and the last position is characterized by sourceIndex j+1=N t r.", true),
            Entry("powers", "alphabetPower", "Powers in the reciprocal Laurent alphabet", Powers(),
                "Marín, §1.1, p. 1: “let ζ=e^{2πi/t} and μ_t={1,ζ,…,ζ^(t−1)}”. The source defines x=(1,ζ,…,ζ^(t−1),z₁,z₁⁻¹,…,zᵣ,zᵣ⁻¹). The displayed three cases give x_i^b. AddMonoidAlgebra.single stores a complex coefficient at an integral exponent function; Pi.single inserts b in one coordinate. The exponential uses real division followed by the inclusion ℝ→ℂ, and the power exponent is an integer.", true),
            Entry("numerator", "numerator", "The numerator alternant", Numerator(),
                "The numerator in equation (1), §1.1, p. 1, is det(x_i^{β_j}) for i,j=1,…,N. Both determinant indices use the same finite alphabet order.", true),
            Entry("denominator", "denominator", "The denominator alternant", Denominator(),
                "The denominator in equation (1), §1.1, p. 1, is det(x_i^{δ_j}) for i,j=1,…,N. It is the same determinant construction at delta.", true),
            Entry("quotient", "IsPhi", "The literal alternant quotient", Quotient(),
                "Marín, equation (1), §1.1, p. 1: “Φ_{t,r}(β)=det(x_i^{β_j})/det(x_i^{δ_j})”. In the Laurent ring IsPhi requires the denominator to be nonzero and the cross-multiplied equality f·denominator=numerator. Thus no division is performed at a zero denominator.", true),
            Entry("newton", "newtonPolytope", "The Newton polytope", Newton(),
                "Marín, §7, p. 47: “Let N_β denote the numerator of (1) and Newt(N_β) its Newton polytope.” For a Laurent polynomial the Newton polytope is the real convex hull of integral exponent functions with nonzero complex coefficient. The inclusion of integral coordinates into real coordinates is explicit.", true),
            Entry("signed-orbit", "signedOrbit", "The signed-permutation orbit", Signed(),
                "The W(C_r) orbit appearing in Conjecture 8.1, §8, p. 49, consists of all coordinate permutations and independent sign choices. sigma is a permutation of Fin r; each epsilon k is the integer 1 or −1.", true),
            Entry("orbit-hull", "orbitPolytope", "The convex hull of one orbit", Orbit(),
                "Conjecture 8.1, §8, p. 49, uses conv(W(C_r) μ). orbitPolytope takes the real convex hull of the signedOrbit of an integral weight.", true),
            Entry("dominant", "Dominant", "Dominant integral weights", Dominance(),
                "The dominant integral weights for W(C_r) are the nonnegative weakly decreasing integer vectors. Antitone uses the natural order on Fin r.", true),
            Entry("claim", "claim", "Marín Conjecture 8.1", ClaimBody(),
                "Marín, Conjecture 8.1, §8, p. 49, verbatim: “" + SourceClaim + "” "
                + "Here A_mu is the folded coefficient support specified immediately before the conjecture. "
                + "The formula states the explicitly equivalent Newton-polytope assertion for every t,r≥1 and "
                + "every strictly decreasing normalized beta. It also requires a Laurent quotient to exist; "
                + "the counterexample has such a quotient.", true),
            Entry("result", "result", "The universal single-orbit assertion is false",
                Seq(Neg, Parenthesized(ClaimBody())),
                "At t=3, r=2 and beta=(10,9,5,4,2,1,0), the alternant quotient has 33 nonzero Laurent monomials. Its support contains (4,0) and (3,3). Every point x in its Newton polytope satisfies x₀≤4, x₀+x₁≤6 and 3x₀+x₁≤12. If the polytope were one signed-permutation orbit hull with dominant generator mu, the first two maxima would force mu=(4,2). The third bound would then give 14≤12. Exact determinant identities establish the quotient and a nonzero denominator. This refutes the universal assertion with the full reciprocal alphabet. The denominator's single-orbit property and Conjecture 8.2 are not refuted here; no infinite-family theorem is asserted.", false, DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, Formula body,
        string prose, bool literature, DescribeRole role = DescribeRole.Definition) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(body)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("marin-conjecture-8-1"),
                ResolutionKind.Refuted) : null);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Field(Formula value, string name) => Seq(value, Dot, Operatorname, Grp(V(name)));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Ints => Seq(Mathbb, Grp(V("Z")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Index => Call("Sum", Fin(V("t")), Call("Sum", Fin(V("r")), Fin(V("r"))));
    private static Formula Exponents => Arrow(Fin(V("r")), Ints);
    private static Formula Coordinates => Arrow(Fin(V("r")), Real);
    private static Formula Laurent => Call("AddMonoidAlgebra", Complex, Parenthesized(Exponents));
    private static Formula Cast(Formula x, Formula type) => Parenthesized(Seq(x, Colon, Sp, type));
    private static Formula All(string x, Formula type, Formula body) => Seq(Forall, Sp, V(x), Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(string x, Formula type, Formula body) => Seq(Exists, Sp, V(x), Colon, Sp, type, Comma, Sp, body);
    private static Formula Lam(string x, Formula type, Formula body) => Seq(Operatorname, Grp(V("fun")), Sp, V(x), Colon, Sp, type, Sp, Mapsto, Sp, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Plus(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Minus(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Both(Formula body) => All("t", Nat, All("r", Nat, body));
    private static Formula Sizes() => Both(Eqn(Call("N", V("t"), V("r")), Plus(V("t"), Mul(D(2), V("r")))));
    private static Formula Inl(Formula a) => App(Q("Sum", "inl"), a);
    private static Formula Inr(Formula a) => App(Q("Sum", "inr"), a);
    private static Formula Val(string x) => Call("val", V(x));
    private static Formula Indices() => Both(And(
        All("a", Fin(V("t")), Eqn(Call("sourceIndex", Inl(V("a"))), Val("a"))),
        All("k", Fin(V("r")), And(
            Eqn(Call("sourceIndex", Inr(Inl(V("k")))), Plus(V("t"), Mul(D(2), Val("k")))),
            Eqn(Call("sourceIndex", Inr(Inr(V("k")))), Plus(Plus(V("t"), Mul(D(2), Val("k"))), D(1)))))));
    private static Formula Deltas() => Both(All("j", Index,
        Eqn(Call("delta", V("t"), V("r"), V("j")),
            Minus(Minus(Cast(Call("N", V("t"), V("r")), Ints), D(1)), Cast(Call("sourceIndex", V("j")), Ints)))));
    private static Formula Normalization()
    {
        var decreasing = All("i", Index, All("j", Index,
            Imp(Lt(Call("sourceIndex", V("i")), Call("sourceIndex", V("j"))),
                Lt(Call("beta", V("j")), Call("beta", V("i"))))));
        var finalZero = All("j", Index,
            Imp(Eqn(Plus(Call("sourceIndex", V("j")), D(1)), Call("N", V("t"), V("r"))),
                Eqn(Call("beta", V("j")), D(0))));
        return Both(All("beta", Arrow(Index, Ints),
            Eqn(Call("NormalizedBeta", V("t"), V("r"), V("beta")), And(decreasing, finalZero))));
    }
    private static Formula Root() => App(Q("Complex", "exp"), Mul(
        Cast(new Formula.Fraction(Mul(D(2), Q("Real", "pi")), Cast(V("t"), Real)), Complex), Q("Complex", "I")));
    private static Formula Single(Formula exponent, Formula coefficient) => App(Q("AddMonoidAlgebra", "single"), exponent, coefficient);
    private static Formula Powers() => Both(All("b", Ints, And(
        All("a", Fin(V("t")), Eqn(Call("alphabetPower", V("t"), V("r"), V("b"), Inl(V("a"))),
            Single(D(0), new Formula.Power(Root(), Mul(Cast(Val("a"), Ints), V("b")))))),
        All("k", Fin(V("r")), And(
            Eqn(Call("alphabetPower", V("t"), V("r"), V("b"), Inr(Inl(V("k")))), Single(App(Q("Pi", "single"), V("k"), V("b")), D(1))),
            Eqn(Call("alphabetPower", V("t"), V("r"), V("b"), Inr(Inr(V("k")))), Single(App(Q("Pi", "single"), V("k"), new Formula.Negate(V("b"))), D(1))))))));
    private static Formula Det(Formula exponent) => App(Q("Matrix", "det"),
        Lam("i", Index, Lam("j", Index, Call("alphabetPower", V("t"), V("r"), exponent, V("i")))));
    private static Formula Numerator() => Both(All("beta", Arrow(Index, Ints),
        Eqn(Call("numerator", V("t"), V("r"), V("beta")), Det(Call("beta", V("j"))))));
    private static Formula Denominator() => Both(Eqn(Call("denominator", V("t"), V("r")), Det(Call("delta", V("t"), V("r"), V("j")))));
    private static Formula Quotient()
    {
        var denominator = Call("denominator", V("t"), V("r"));
        var numerator = Call("numerator", V("t"), V("r"), V("beta"));
        var body = And(Ne(denominator, D(0)), Eqn(Mul(V("f"), denominator), numerator));
        return Both(All("beta", Arrow(Index, Ints), All("f", Laurent,
            Eqn(Call("IsPhi", V("t"), V("r"), V("beta"), V("f")), body))));
    }
    private static Formula Newton() => All("r", Nat, All("f", Laurent,
        Eqn(Call("newtonPolytope", V("f")), Call("convexHull", Real,
            App(Q("Set", "image"), Lam("a", Exponents, Lam("k", Fin(V("r")), Cast(Call("a", V("k")), Real))),
                Cast(Field(Field(V("f"), "coeff"), "support"), Call("Set", Parenthesized(Exponents))))))));
    private static Formula Signed()
    {
        var signs = All("k", Fin(V("r")), Or(Eqn(Call("epsilon", V("k")), D(1)),
            Eqn(Call("epsilon", V("k")), new Formula.Negate(D(1)))));
        var coordinates = All("k", Fin(V("r")), Eqn(Call("x", V("k")),
            Mul(Cast(Call("epsilon", V("k")), Real), Cast(Call("mu", Call("sigma", V("k"))), Real))));
        var elements = Some("sigma", App(Q("Equiv", "Perm"), Fin(V("r"))),
            Some("epsilon", Exponents, And(signs, coordinates)));
        var set = Seq(OpenBrace, V("x"), Colon, Sp, Coordinates, Mid, elements, CloseBrace);
        return All("r", Nat, All("mu", Exponents, Eqn(Call("signedOrbit", V("mu")), set)));
    }
    private static Formula Orbit() => All("r", Nat, All("mu", Exponents,
        Eqn(Call("orbitPolytope", V("mu")), Call("convexHull", Real, Call("signedOrbit", V("mu"))))));
    private static Formula Dominance() => All("r", Nat, All("mu", Exponents,
        Eqn(Call("Dominant", V("mu")), And(All("k", Fin(V("r")), Leq(D(0), Call("mu", V("k")))), Call("Antitone", V("mu"))))));
    private static Formula ClaimBody()
    {
        var quotient = Call("IsPhi", V("t"), V("r"), V("beta"), V("f"));
        var existence = Some("f", Laurent, quotient);
        var singleOrbit = Some("mu", Exponents, And(Call("Dominant", V("mu")),
            Eqn(Call("newtonPolytope", V("f")), Call("orbitPolytope", V("mu")))));
        var assertion = All("f", Laurent, Imp(quotient, Imp(Ne(V("f"), D(0)), singleOrbit)));
        return Both(Imp(Leq(D(1), V("t")), Imp(Leq(D(1), V("r")),
            All("beta", Arrow(Index, Ints), Imp(Call("NormalizedBeta", V("t"), V("r"), V("beta")),
                And(existence, assertion))))));
    }
}
