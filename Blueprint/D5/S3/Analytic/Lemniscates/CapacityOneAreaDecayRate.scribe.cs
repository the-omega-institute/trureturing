using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Lemniscates;

internal sealed class CapacityOneAreaDecayRateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Lemniscates/CapacityOneAreaDecayRate.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/ghosh2026erdos");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The closed unit disc together with the isolated point 4 has capacity one and minimal lemniscate area of neither order 1/n nor order 1/log n.",
        H("Capacity-One Area Decay Rate"),
        Blocks(
            Entry("point-diameter", "pointDiameter", "The finite-point diameter", PointDiameter(),
                "The s-point diameter is the supremum of the Vandermonde products of s-tuples in K, "
                + "raised to the real power 2/(s(s−1)). The subtraction in the exponent is in ℝ. "
                + "Repeated entries are allowed and contribute zero products. The capacity argument uses s≥2.",
                DescribeRole.Definition, true),
            Entry("transfinite-diameter", "TransfiniteDiameterOne", "Transfinite diameter one", DiameterOne(),
                "The finite-point diameters converge to one as s tends to infinity. "
                + "The paper defines cap as logarithmic capacity, equivalently the transfinite diameter; "
                + "this predicate expresses the capacity-one condition through that limit.",
                DescribeRole.Definition, true),
            Entry("minimal-area", "minimalArea", "Minimal unit-lemniscate area", MinimalArea(),
                "P_n(K) consists of monic degree-n complex polynomials with all roots in K. "
                + "The infimum is taken over their unit-lemniscate areas, represented by planar Lebesgue "
                + "volume on ℂ in the extended non-negative reals. The asymptotic claim uses its toReal projection.",
                DescribeRole.Definition, true),
            Entry("two-rate-claim", "claim", "The capacity-one two-rate claim", Claim(),
                "The claim requires one of the two Θ orders for every nonempty compact set of transfinite "
                + "diameter one. Each order means both eventual upper and positive lower bounds by constant "
                + "multiples of the corresponding sequence, along natural degrees tending to infinity.",
                DescribeRole.Definition, true),
            Entry("refutation", "result", "An isolated point gives another decay type", Disp(Seq(Neg, Sp, V("claim"))),
                "Take K equal to the closed unit disc together with {4}. Roots of unity have Vandermonde "
                + "product s^(s/2), while the Vandermonde determinant gives the upper bound s!·4^s≤(4s)^s. "
                + "Thus 1≤d_s(K)≤exp(2(log 4+log s)/(s−1)) for s≥2, and K has transfinite diameter one. "
                + "The competitor p(z)=(z^N−1)(z−4)^k is monic of degree N+k with all roots in K. "
                + "For k≥2 and N≥k(k−2)+1 its unit lemniscate lies in the annulus "
                + "1−2^(−k)<|z|<1+2^(−k) together with the disc |z−4|<2^(−(k−2)). "
                + "The annulus has area 4π·2^(−k), and the disc has area 16π·2^(−2k)≤16π·2^(−k). "
                + "Setting N=k²+1 gives A_(k²+k+1)(K)≤20π·2^(−k). Multiplying this bound by k²+k+1 "
                + "gives a limit of zero, excluding an eventual lower bound of order 1/n. "
                + "Since 1/n=O(1/log n), an eventual lower bound of order 1/log n is excluded as well. "
                + "The argument answers the two-rate question without an all-degree sharp estimate or a connected example.",
                DescribeRole.Theorem, false))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Commentary(name, prose), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("ghosh-ramachandran-2026-capacity-one-decay-rate"),
                ResolutionKind.Refuted) : null);

    private static BlockSequence Commentary(string name, string prose)
    {
        if (name != "claim") return Blocks(Paragraph(Text(prose)));
        return Blocks(
            Paragraph(Text("Beginning of Section 4, verbatim: “This shows that while "),
                Math(Eqn(Call("vartheta", V("K")), D(0))),
                Text(" may hold for all compacts "), Math(V("K")), Text(" with "),
                Math(Eqn(Call("cap", V("K")), D(1))),
                Text(", the decay rate of "), Math(At(V("A"), V("n"), V("K"))),
                Text(" is not universal. It will be interesting to determine whether "),
                Math(At(V("A"), V("n"), V("K"))), Text(" can only decay like "),
                Math(Div(D(1), V("n"))), Text(" or "), Math(Div(D(1), Call("log", V("n")))),
                Text(", or whether other rates are possible.”")),
            Paragraph(Text(prose)));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Sets => Call("Set", Complex);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.Implies, P(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, P(y));
    private static Formula At(Formula a, Formula n, Formula k) => Seq(new Formula.Subscript(a, n), P(k));
    private static Formula Lambda(string name, Formula type, Formula body) =>
        P(Seq(V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula AreaSequence() => Lambda("n", Nat, Call("toReal", Call("minimalArea", V("K"), V("n"))));
    private static Formula Theta(Formula f, Formula g) => Call("IsTheta", V("atTop"), f, g);

    private static Formula PointDiameter()
    {
        Formula k = V("K"), s = V("s"), a = V("a");
        Formula tuples = Seq(Left, OpenBrace, a, Colon, Sp, Call("Fin", s), To, Sp, Complex,
            Sp, Mid, Sp, All("i", Call("Fin", s), Seq(new Formula.Apply(a, [V("i")]), Sp, InMacro, Sp, k)),
            Right, CloseBrace);
        Formula supremum = Seq(Operatorname, Grp(V("sup")), Underscore,
            Grp(Seq(a, Sp, InMacro, Sp, tuples)), Sp, Call("vandermonde", a));
        Formula exponent = Div(D(2), Mul(P(Call("ofNat", s)), P(Sub(Call("ofNat", s), D(1)))));
        return Disp(All("K", Sets, All("s", Nat,
            Eqn(Call("pointDiameter", k, s), new Formula.Power(P(supremum), exponent)))));
    }

    private static Formula DiameterOne() => Disp(All("K", Sets,
        Iff(Call("TransfiniteDiameterOne", V("K")),
            Call("Tendsto", Lambda("s", Nat, Call("pointDiameter", V("K"), V("s"))),
                V("atTop"), Call("nhds", D(1))))));

    private static Formula MinimalArea()
    {
        Formula k = V("K"), n = V("n"), p = V("p");
        Formula infimum = Seq(Operatorname, Grp(V("inf")), Underscore,
            Grp(Seq(p, Colon, Sp, Call("Polynomial", Complex), Comma, Sp, Call("InP", k, n, p))),
            Sp, Call("lemniscateArea", p));
        return Disp(All("K", Sets, All("n", Nat, Eqn(Call("minimalArea", k, n), infimum))));
    }

    private static Formula Claim()
    {
        Formula rates = new Formula.Logic(
            Theta(AreaSequence(), Lambda("n", Nat, Div(D(1), Call("ofNat", V("n"))))),
            FormulaLogicOperator.Or,
            Theta(AreaSequence(), Lambda("n", Nat, Div(D(1), Call("log", Call("ofNat", V("n")))))));
        Formula body = Imp(Call("IsCompact", V("K")), Imp(Call("Nonempty", V("K")),
            Imp(Call("TransfiniteDiameterOne", V("K")), rates)));
        return Disp(Iff(V("claim"), All("K", Sets, body)));
    }
}
