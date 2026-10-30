using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PowerSeries;

internal sealed class HannaA352700CatalanCongruencesDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2022a352700");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lagrange substitution and Frobenius pairing prove Hanna's six A352700 congruences.",
        H("Hanna's modulo 2 and modulo 3 conjectures for OEIS A352700"),
        Blocks(
            Paragraph(Text("Power series are formal univariate series in X over Z or ZMod(p). "
                + "The operation PowerSeries.subst(u,f) denotes formal composition f(u) "
                + "when u has zero constant coefficient; PowerSeries.coeff(k,f) extracts the degree-k "
                + "coefficient of f; Finset.range(k) is the finite set {0,...,k-1}; PowerSeries.map applies "
                + "a ring homomorphism coefficientwise, and PowerSeries.invOfUnit(f,1) is the multiplicative "
                + "inverse of a series f with constant coefficient one. Natural division Nat.div is exact on "
                + "every displayed weight, Catalan quotient Nat.div(Nat.choose(2*n+1,n), 2*n+1) = catalan(n), "
                + "and Raney quotient; Nat.cast embeds natural numbers into Z, "
                + "Int.ModEq(m,a,b) denotes congruence a ≡ b (mod m) in Z, and catalan(n) is the n-th "
                + "Catalan number A000108(n).")),
            Paragraph(Text("CatalanCompositionSquareParity.catalanUnit is the integral Catalan "
                + "series C(X), with constant coefficient one by catalan_unit_zero. "
                + "BilateralProductModFour.geometric represents (1+X)^(-1); geometric_spec gives "
                + "its inverse identity and geometric_coeff its coefficients (-1)^n. "
                + "AlternatingPoleCoefficients.alternating_pole_coefficients gives the alternating "
                + "binomial coefficients of its powers. SignedCatalanCubicSubstitutionModThree."
                + "inverse_exists supplies two-sided compositional inversion on normalized integral "
                + "power series, and SignedCatalanCubicSubstitutionModThree.prime_power_subst gives "
                + "the Frobenius identity f^p = f(X^p) over ZMod(p) for prime p.")),
            Node("weight", "Exact integer binomial weight", WeightFormula(),
                "OEIS A352700, NAME (unpaginated): the m-th summand carries weight "
                + "binomial((m+1)*(2*m+1), m)/(2*m+1). Because gcd(2*m+1, m) = 1 and "
                + "(m+1)*(2*m+1)*binomial((m+1)*(2*m+1)-1, m-1) = m*binomial((m+1)*(2*m+1), m) for m >= 1, "
                + "the odd denominator 2*m+1 divides the binomial numerator in N for every m >= 0.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("catalanInvZ", "Multiplicative inverse of the Catalan series", CatalanInvZFormula(),
                "CatalanCompositionSquareParity.catalanUnit is the Catalan series C(X) "
                + "of OEIS A000108, satisfying C(X) = 1 + X*C(X)^2 with constant coefficient 1. "
                + "Its multiplicative inverse C(X)^(-1) satisfies C(X)^(-1) = 1 - X*C(X).",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("coeffA", "Coefficient sequence of OEIS A352700", CoeffAFormula(),
                "OEIS A352700, NAME and PROG (unpaginated): in the defining sum "
                + "sum_{m>=0} weight(m)*X^m*(C(X)^(-1))^(m*(2*m+1)+1), every summand with m > n is divisible "
                + "by X^(n+1), so the degree-n coefficient a(n) equals the displayed finite sum over 0 <= m <= n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("seriesA", "Integral generating series of OEIS A352700", SeriesAFormula(),
                "OEIS A352700, NAME (unpaginated): A(X) = sum_{n>=0} a(n)*X^n in Z[[X]] assembled from coeffA.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("seriesMod", "Modular reduction of A(X)", SeriesModFormula(),
                "Coefficientwise reduction of seriesA from Z[[X]] to (ZMod(p))[[X]].",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("catalanMod", "Modular reduction of C(X)", CatalanModFormula(),
                "Coefficientwise reduction of CatalanCompositionSquareParity.catalanUnit "
                + "from Z[[X]] to (ZMod(p))[[X]], where C(X) = 1 + X*C(X)^2 is the Catalan "
                + "series of OEIS A000108.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("raneyTerm", "Second binomial quotient of conjecture (4)", RaneyTermFormula(),
                "OEIS A352700, COMMENTS (4) and EXAMPLE (unpaginated): represents "
                + "3*binomial(2*n-1, n-2)/(2*n-1) under the standard negative-lower-index binomial rule "
                + "binomial(2*n-1, n-2) = 0 for n < 2. For n = k+2 >= 2, exact division holds in N and "
                + "equals catalan(k+2) - catalan(k+1).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjunction of Hanna's six A352700 conjectures",
                Disp(Seq(Named("claim"), Sp, Iff, Sp, Parenthesized(ClaimBody()))),
                "OEIS A352700, COMMENTS (unpaginated), conjectures (1)-(6) of Paul D. Hanna (March 2022): "
                + "(1) A(X)^3 ≡ A(X^3) (mod 3); (2) A(X) ≡ C(X) + X^2*C(X)^3 ≡ (2 - X)*C(X) - 1 (mod 3); "
                + "(3) A(X) ≡ C(X) (mod 2); (4) a(n) ≡ binomial(2*n+1,n)/(2*n+1) + raneyTerm(n) (mod 3) "
                + "for all n >= 0, where 2*n+1 divides Nat.choose(2*n+1,n) in N with exact quotient catalan(n); "
                + "(5) a(n) ≡ 2*catalan(n) - catalan(n-1) (mod 3) for all n >= 1; and "
                + "(6) a(n) ≡ catalan(n) (mod 2) for all n >= 0.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of Hanna's six A352700 conjectures", Disp(ClaimBody()),
                "Substituting zeta(X) = X*(1+X)^(-2) sends C(X) - 1 to X and C(X)^(-1) to (1+X)^(-1), "
                + "transforming A(X) into B(C(X) - 1) where B(X) = sum_{m>=0} weight(m)*X^m*(1+X)^(-(m+1)*(2*m+1)) "
                + "has degree-n coefficient sum_{m=0}^n (-1)^(n-m)*weight(m)*binomial(2*m*(m+1)+n, n-m). "
                + "Modulo 2, Pascal absorption splits each m >= 1 summand into two quadratic binomial sums "
                + "sum_{j=0}^L binomial(L,j)*binomial(2*(j+c)*(j+c+1)+d+L, L), which vanish for L >= 1 by "
                + "pairing j with j + 2^k where 2^k <= L < 2^(k+1); hence B(X) ≡ 1 + X (mod 2) and "
                + "A(X) ≡ 1 + (C(X) - 1) = C(X) (mod 2), giving (3) and (6). Modulo 3, binomial absorption and "
                + "Lucas decomposition force weight(m) ≡ 0 (mod 3) whenever m >= 1 and m ≢ 1 (mod 3), while for "
                + "n = 3*N + 1 >= 4 the remaining m = 3*M + 1 slice reduces to "
                + "2*sum_{M=0}^N (-1)^(N-M)*binomial(N,M)*binomial(6*M*(M+1)+1+N, N), which vanishes by "
                + "3-way Frobenius grouping M, M + 3^k, M + 2*3^k for 3^k <= N < 3^(k+1). Thus "
                + "B(X) ≡ (1+X)^(-1) + 2*X (mod 3), so A(X) ≡ C(X)^(-1) + 2*(C(X) - 1) = (2 - X)*C(X) - 1 "
                + "= C(X) + X^2*C(X)^3 (mod 3), establishing (2), (1) by prime_power_subst, and (4)-(5) by "
                + "coefficient extraction. Global literature novelty is unverified.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("a352700-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula QName(string ns, string name) => Seq(Named(ns), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula QCall(string ns, string name, params Formula[] args) =>
        new Formula.Apply(QName(ns, name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Subtract(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Power(Formula a, Formula b) =>
        new Formula.Power(Parenthesized(a), b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Imp(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula And(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula SumAt(string idx, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(V(idx), InMacro, domain)), Parenthesized(body));
    private static Formula NatCast(Formula value) => QCall("Nat", "cast", value);

    private static Formula WeightFormula() => Disp(All("m", Naturals(),
        Equal(Call("weight", V("m")),
            QCall("Nat", "div",
                QCall("Nat", "choose",
                    Mul(Add(V("m"), D(1)), Add(Mul(D(2), V("m")), D(1))), V("m")),
                Add(Mul(D(2), V("m")), D(1))))));

    private static Formula CatalanInvZFormula() => Disp(Equal(Named("catalanInvZ"),
        QCall("PowerSeries", "invOfUnit", QName("CatalanCompositionSquareParity", "catalanUnit"), D(1))));

    private static Formula CoeffAFormula() => Disp(All("n", Naturals(),
        Equal(Call("coeffA", V("n")),
            SumAt("m", QCall("Finset", "range", Add(V("n"), D(1))),
                Mul(NatCast(Call("weight", V("m"))),
                    QCall("PowerSeries", "coeff", Subtract(V("n"), V("m")),
                        Power(Named("catalanInvZ"),
                            Add(Mul(V("m"), Add(Mul(D(2), V("m")), D(1))), D(1)))))))));

    private static Formula SeriesAFormula() => Disp(Equal(Named("seriesA"),
        QCall("PowerSeries", "mk", Named("coeffA"))));

    private static Formula SeriesModFormula() => Disp(All("p", Naturals(),
        Equal(Call("seriesMod", V("p")),
            QCall("PowerSeries", "map",
                QCall("Int", "castRingHom", Call("ZMod", V("p"))), Named("seriesA")))));

    private static Formula CatalanModFormula() => Disp(All("p", Naturals(),
        Equal(Call("catalanMod", V("p")),
            QCall("PowerSeries", "map",
                QCall("Int", "castRingHom", Call("ZMod", V("p"))), QName("CatalanCompositionSquareParity", "catalanUnit")))));

    private static Formula RaneyTermFormula() => Disp(All("n", Naturals(),
        Equal(Call("raneyTerm", V("n")),
            Call("ite", Seq(V("n"), Sp, Lt, Sp, D(2)), D(0),
                QCall("Nat", "div",
                    Mul(D(3), QCall("Nat", "choose",
                        Subtract(Mul(D(2), V("n")), D(1)),
                        Subtract(V("n"), D(2)))),
                    Subtract(Mul(D(2), V("n")), D(1)))))));

    private static Formula CubicCatalanMod3() =>
        Add(Call("catalanMod", D(3)),
            Mul(Power(V("X"), D(2)), Power(Call("catalanMod", D(3)), D(3))));

    private static Formula LinearCatalanMod3() =>
        Subtract(Mul(Subtract(D(2), V("X")), Call("catalanMod", D(3))), D(1));

    private static Formula ClaimBody() =>
        And(Equal(Power(Call("seriesMod", D(3)), D(3)),
                QCall("PowerSeries", "subst", Power(V("X"), D(3)), Call("seriesMod", D(3)))),
        And(And(Equal(Call("seriesMod", D(3)), CubicCatalanMod3()),
                Equal(CubicCatalanMod3(), LinearCatalanMod3())),
        And(Equal(Call("seriesMod", D(2)), Call("catalanMod", D(2))),
        And(All("n", Naturals(),
                QCall("Int", "ModEq", D(3), Call("coeffA", V("n")),
                    Add(NatCast(QCall("Nat", "div",
                            QCall("Nat", "choose", Add(Mul(D(2), V("n")), D(1)), V("n")),
                            Add(Mul(D(2), V("n")), D(1)))),
                        NatCast(Call("raneyTerm", V("n")))))),
        And(All("n", Naturals(),
                Imp(Le(D(1), V("n")),
                    QCall("Int", "ModEq", D(3), Call("coeffA", V("n")),
                        Subtract(Mul(D(2), NatCast(Call("catalan", V("n")))),
                            NatCast(Call("catalan", Subtract(V("n"), D(1)))))))),
            All("n", Naturals(),
                QCall("Int", "ModEq", D(2), Call("coeffA", V("n")),
                    NatCast(Call("catalan", V("n"))))))))));
}
