using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.BesselProductOrderLogConvexity;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/bariczponnusamy2013turan");
    private static readonly LibraryNoteRef Definitions =
        LibraryNoteRef.Create("D5/L/Asymptotics/nist2026dlmfmodifiedbessel");
    private const string Prefix = "D5/S3/Analytic/BesselProductOrderLogConvexity/Result.";
    private const string Conjecture = "The function ν ↦ I_ν(u)K_ν(u) is log-convex on (−1, ∞) for all u > 0 fixed.";
    private const string TheoremOne = "the function ν ↦ I_{√ν}(u)K_{√ν}(u) is log-convex on (0, ∞) for all u > 0 fixed;";
    private const string TheoremTwo = "The function ν ↦ I_ν(u)K_ν(u) is decreasing and (0, ∞) for all u > 0 fixed. Moreover, for all ν ≥ 1/2 and u > 0 we have 2I_ν(u)K_ν(u) ≤ I_{ν−1}(u)K_{ν−1}(u) + I_{ν+1}(u)K_{ν+1}(u).";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Half-integer modified Bessel values contradict log-convexity in the order.",
        H("The modified Bessel product need not be log-convex in its order"), Blocks(
            Describe.Lean(DescribeId.Create("bessel-product-second-kind"),
                DeclarationHandle.Create(Prefix + "besselK"),
                H("The second-kind function at noninteger orders"),
                StatementSource.FromAuthor(Disp(All("nu", R, All("u", R,
                    Eqn(K(V("nu"), V("u")),
                        Fr(Mul(Fr(Call("Real.pi"), D(2)),
                            Sub(I(Negate(V("nu")), V("u")), I(V("nu"), V("u")))),
                            Call("Real.sin", Mul(V("nu"), Call("Real.pi"))))))))),
                AssessedProvenance.FromLiterature(Definitions),
                Blocks(Paragraph(Text("DLMF §10.25(ii), equation 10.25.2 (https://dlmf.nist.gov/10.25.E2), defines the first-kind function by: “I_ν(z) = (½z)^ν Σ_{k=0}^∞ (¼z²)^k / (k! Γ(ν+k+1)).” The page states that the principal branch of I_ν(z) “is analytic in ℂ∖(−∞,0]”.")),
                    Paragraph(Text("The first-kind function besselI in every formula is the existing D5.S3.Analytic.BesselRatioLogConcavity.Result.besselI. At real z=u>0, the principal branch agrees with the real power: (u/2)^nu (u²/4)^k=(u/2)^(2k+nu). Thus the owner's summand (u/2)^(2k+nu)/(k! Gamma(k+nu+1)) has exactly the DLMF normalization.")),
                    Paragraph(Text("DLMF §10.27(ii), equation 10.27.4 (https://dlmf.nist.gov/10.27.E4), gives: “K_ν(z) = ½π (I_{−ν}(z) − I_ν(z)) / sin(νπ)”, followed by “When ν is an integer limiting values are taken”. Equation 10.27.1 (https://dlmf.nist.gov/10.27.E1) states: “I_{−n}(z) = I_n(z), n an integer.”")),
                    Paragraph(Text("For positive u and noninteger nu, besselK is this standard connection formula with the same first-kind normalization. Lean's real quotient is a total operation; only noninteger orders enter the assertion below, so no value assigned by that operation at an integer is used. Integer-order K values require the stated limiting convention and are outside this definition's asserted correspondence."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bessel-product-function"),
                DeclarationHandle.Create(Prefix + "P"), H("The product at a fixed argument"),
                StatementSource.FromAuthor(Disp(All("u", R, All("nu", R,
                    Eqn(P(V("u"), V("nu")), Mul(I(V("nu"), V("u")), K(V("nu"), V("u")))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("On printed p. 1 of arXiv:1010.3346v1, §1, Baricz and Ponnusamy write: “Let us denote with Iν and Kν the modified Bessel functions of the first and second kind, respectively. For definitions, recurrence formulas and other properties of modified Bessel functions of the first and second kind we refer to the classical book of G.N. Watson [Wa].”")),
                    Paragraph(Text("The product is P(u,nu)=Iν(u)Kν(u). The argument u is its first parameter, while the order nu is its second parameter. The defining-series and connection-formula quotations above are from DLMF; the paper's passage identifies the functions and refers the reader to Watson."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bessel-product-midpoint-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The necessary midpoint product inequality"),
                StatementSource.FromAuthor(Disp(Eqn(V("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The final Conjecture in §3, printed page 7 of arXiv:1010.3346v1, reads: “Motivated by Theorems 1 and 2 we conjecture the following. Conjecture. " + Conjecture + "”")),
                    Paragraph(Text("Theorem 1(4), printed page 4, states: “" + TheoremOne + "”")),
                    Paragraph(Text("Theorem 2, printed page 6, with equation (19) joined to its sentence, states: “" + TheoremTwo + "” The word ‘and’ in the first sentence is retained from the source text.")),
                    Paragraph(Text("For a positive function, log-convexity on (−1,∞) implies 2 log P(u,nu+h)≤log P(u,nu)+log P(u,nu+2h), hence P(u,nu+h)^2≤P(u,nu)P(u,nu+2h). The orders nu, nu+h and nu+2h all lie in the interval when nu>−1 and h>0. The formal assertion restricts to triples of noninteger orders, where the connection formula is valid. It is therefore weaker than the conjecture, and its refutation refutes the conjecture. The square-root parametrization in Theorem 1(4) is a different assertion."))),
                DescribeRole.Definition),
            Helper("gamma_factorial", "The half-integer Gamma normalization",
                All("k", N, Eqn(Mul(Mul(Factorial(V("k")),
                    Call("Real.Gamma", Add(V("k"), Qn(1,2)))), Pow(D(4), V("k"))),
                    Mul(Factorial(Mul(D(2), V("k"))), Call("Real.sqrt", Call("Real.pi"))))),
                "Mathlib's Gamma duplication formula at k+1/2, together with the Gamma values at positive integers, gives the even-factorial identity after real-power normalization."),
            Helper("minus_term", "The terms at order minus one half",
                All("k", N, Eqn(BesselTerm(Negate(Qn(1,2)), V("k")),
                    Fr(V("a"), Factorial(Mul(D(2), V("k")))))),
                "The private real constant a is (1/2)^(−1/2)/sqrt(pi). The half-integer Gamma identity converts each defining term of I−1/2(1) into a/(2k)!. Natural indices in real expressions are coerced to real numbers."),
            Helper("plus_term", "The terms at order one half",
                All("k", N, Eqn(BesselTerm(Qn(1,2), V("k")),
                    Fr(V("a"), Factorial(Add(Mul(D(2), V("k")), D(1)))))),
                "One Gamma step and one factorial step transform the order-one-half summand into a/(2k+1)!."),
            Helper("a_eq_sqrt", "The elementary square-root factor",
                Eqn(V("a"), Call("Real.sqrt", Fr(D(2), Call("Real.pi")))),
                "The positive real-power factor (1/2)^(−1/2) divided by sqrt(pi) equals sqrt(2/pi). Positivity determines the square root uniquely."),
            Helper("half_values", "The first two half-integer evaluations",
                And(Eqn(I(Negate(Qn(1,2)), D(1)),
                    Mul(Call("Real.sqrt", Fr(D(2), Call("Real.pi"))), Call("Real.cosh", D(1)))),
                    Eqn(I(Qn(1,2), D(1)),
                    Mul(Call("Real.sqrt", Fr(D(2), Call("Real.pi"))), Call("Real.sinh", D(1))))),
                "Summing the even and odd factorial terms gives cosh(1) and sinh(1), respectively. The prefactor is sqrt(2/pi)."),
            Helper("lower", "A Gamma recurrence for the summands", Lower(),
                "Here summand(nu,k) denotes the defining Bessel summand at argument one. The Gamma recurrence relates adjacent orders at the same index, provided k+nu+1 is nonzero."),
            Helper("shift", "An index-shift identity", Shift(),
                "Increasing the natural index raises the exponent by two and the factorial by one step. A factor 2(k+1) relates the resulting summands."),
            Helper("step", "The summand form of the order recurrence", Step(),
                "Combining the adjacent-order Gamma identity with the index shift gives the additive relation between three consecutive orders."),
            Helper("recurrence", "The order recurrence at argument one", Recurrence(),
                "For nu>−2 the series at nu+1 and nu+2 converge. The summand relation then proves convergence at nu and identifies its sum. Splitting off index zero yields Iν(1)=Iν+2(1)+2(nu+1)Iν+1(1). The nonzero hypotheses exclude the Gamma recurrence's exceptional arguments."),
            Helper("recurrence_minus", "The order minus three halves",
                Eqn(I(Negate(Qn(3,2)), D(1)),
                    Sub(I(Qn(1,2), D(1)), I(Negate(Qn(1,2)), D(1)))),
                "The order recurrence at nu=−3/2 expresses I−3/2(1) as I1/2(1)−I−1/2(1)."),
            Helper("recurrence_plus", "The order three halves",
                Eqn(I(Qn(3,2), D(1)),
                    Sub(I(Negate(Qn(1,2)), D(1)), I(Qn(1,2), D(1)))),
                "The order recurrence at nu=−1/2 expresses I3/2(1) as I−1/2(1)−I1/2(1). This is sqrt(2/pi)(cosh(1)−sinh(1))."),
            Helper("product_values", "Three exact product values", ProductValues(),
                "The sine values at −pi/2, pi/2 and 3pi/2 are −1, 1 and −1. Substituting the four first-kind values into the connection formula gives P(1,−1/2)=(1+exp(−2))/2, P(1,1/2)=(1−exp(−2))/2 and P(1,3/2)=2exp(−2). The factor pi cancels the square 2/pi of the common prefactor."),
            Helper("exp_bound", "A rational upper bound on the exponential",
                And(Less(D(0), Call("Real.exp", Negate(D(2)))),
                    Less(Call("Real.exp", Negate(D(2))), Qn(1,7))),
                "The exponential is positive. The lower bound exp(1)>8/3 implies exp(1)^2>7, so exp(−2)=1/exp(1)^2<1/7."),
            Helper("witness", "The strict reversal of the midpoint inequality", Witness(),
                "Put t=exp(−2). The product difference is (1+t)t−(1−t)^2/4=(3t^2+6t−1)/4. A rational bound on exp(1) gives an upper bound on t for which this expression is strictly negative."),
            Helper("half_noninteger", "Half-integer orders are noninteger",
                All("k", Z, All("n", Z, Ne(Add(Parenthesized(Seq(Call("Int.cast", V("k")), Colon, R)), Qn(1,2)), Parenthesized(Seq(Call("Int.cast", V("n")), Colon, R))))),
                "For integers k and n, the real number k+1/2 differs from n because doubling would equate an odd integer with an even one."),
            Describe.Lean(DescribeId.Create("bessel-product-order-refutation"),
                DeclarationHandle.Create(Prefix + "result"), H("Refutation of order log-convexity"),
                StatementSource.FromAuthor(Disp(new Formula.Not(V("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take u=1, nu=−1/2 and h=1. All three orders are noninteger and greater than −1. The strict product comparison contradicts the asserted three-point inequality. Thus the positive modified Bessel product is not log-convex in its order on the entire interval (−1,∞) for every positive argument. The conclusion concerns the order itself, rather than the square-root parametrization."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("baricz-ponnusamy-2013-bessel-product-order-log-convexity"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Helper(string name, string title, Formula statement, string text) =>
        Describe.Lean(DescribeId.Create("bessel-product-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    private static Formula V(string name) => F.Id(name);
    private static Formula R => Seq(Mathbb, Sp, Grp(V("R")));
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Z => Seq(Mathbb, Sp, Grp(V("Z")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qn(long a, long b) => Fr(new Formula.Number(a), new Formula.Number(b));
    private static Formula Fr(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Negate(Formula a) => new Formula.Negate(a);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula>();
        foreach (var word in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(V(word));
        }
        var head = Seq(Operatorname, Sp, Grp([.. parts]));
        return args.Length == 0 ? head : new Formula.Apply(head, [.. args]);
    }
    private static Formula I(Formula nu, Formula u) => Call("besselI", nu, u);
    private static Formula K(Formula nu, Formula u) => Call("besselK", nu, u);
    private static Formula P(Formula u, Formula nu) => Call("P", u, nu);
    private static Formula Factorial(Formula k) => Call("Nat.factorial", k);
    private static Formula Summand(Formula nu, Formula k) => Call("summand", nu, k);
    private static Formula BesselTerm(Formula nu, Formula k) =>
        Fr(Pow(Qn(1,2), Add(Mul(D(2), k), nu)),
            Mul(Factorial(k), Call("Real.Gamma", Add(Add(k, nu), D(1)))));
    private static Formula Noninteger(Formula x) => All("n", Z, Ne(x, V("n")));
    private static Formula ClaimBody() => All("u", R, Imp(Less(D(0), V("u")),
        All("nu", R, All("h", R,
            Imp(Less(Negate(D(1)), V("nu")), Imp(Less(D(0), V("h")),
            Imp(Noninteger(V("nu")), Imp(Noninteger(Add(V("nu"), V("h"))),
            Imp(Noninteger(Add(V("nu"), Mul(D(2), V("h")))),
                Leq(Pow(P(V("u"), Add(V("nu"), V("h"))), D(2)),
                    Mul(P(V("u"), V("nu")), P(V("u"), Add(V("nu"), Mul(D(2), V("h")))))))))))))));
    private static Formula Lower() => All("nu", R, All("k", N,
        Imp(Ne(Add(Add(V("k"), V("nu")), D(1)), D(0)),
            Eqn(Summand(V("nu"), V("k")),
                Mul(Mul(D(2), Add(Add(V("k"), V("nu")), D(1))),
                    Summand(Add(V("nu"), D(1)), V("k")))))));
    private static Formula Shift() => All("nu", R, All("k", N,
        Eqn(Summand(Add(V("nu"), D(2)), V("k")),
            Mul(Mul(D(2), Add(V("k"), D(1))),
                Summand(Add(V("nu"), D(1)), Add(V("k"), D(1)))))));
    private static Formula Step() => All("nu", R, All("k", N,
        Imp(Ne(Add(Add(Add(V("k"), D(1)), V("nu")), D(1)), D(0)),
            Eqn(Summand(V("nu"), Add(V("k"), D(1))),
                Add(Summand(Add(V("nu"), D(2)), V("k")),
                    Mul(Mul(D(2), Add(V("nu"), D(1))),
                        Summand(Add(V("nu"), D(1)), Add(V("k"), D(1)))))))));
    private static Formula Recurrence() => All("nu", R,
        Imp(Less(Negate(D(2)), V("nu")),
            Imp(All("k", N, Ne(Add(Add(V("k"), V("nu")), D(1)), D(0))),
                Eqn(I(V("nu"), D(1)), Add(I(Add(V("nu"), D(2)), D(1)),
                    Mul(Mul(D(2), Add(V("nu"), D(1))), I(Add(V("nu"), D(1)), D(1))))))));
    private static Formula ProductValues()
    {
        var t = Call("Real.exp", Negate(D(2)));
        return And(Eqn(P(D(1), Negate(Qn(1,2))), Fr(Add(D(1), t), D(2))),
            And(Eqn(P(D(1), Qn(1,2)), Fr(Sub(D(1), t), D(2))),
                Eqn(P(D(1), Qn(3,2)), Mul(D(2), t))));
    }
    private static Formula Witness() => Less(
        Mul(P(D(1), Negate(Qn(1,2))), P(D(1), Qn(3,2))),
        Pow(P(D(1), Qn(1,2)), D(2)));
}
