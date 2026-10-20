using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class AlcarazRamosConformalTowerRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/AlcarazRamosConformalTowerRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/alcarazramos2024conformaltower");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The homogeneous N=3 lowest quasienergy cannot have the predicted conformal limit.",
        H("The lowest-mode Alcaraz–Ramos prediction fails"),
        Blocks(
            Node("poly", "The polynomial recurrence", PolyFormula(),
                "Page 4, Eqs. (26)–(27): “P_M^{(N)}(z) = P_{M−1}^{(N)}(z) − zλ_M^N P_{M−N}^{(N)}(z),” followed by “with the initial condition” and “P_M^{(N)}(z) = 1, for M ≤ 0,”. Here N=3, λ_j=1, and poly(n)=P_{n−2}; the three initial indices represent nonpositive M. Polynomial.X is the polynomial indeterminate.",
                AssessedProvenance.FromLiterature(Source)),
            Node("P", "Nonnegative lattice sizes", All("M", Nats,
                    Eqn(Call("P", V("M")), Call("poly", Add(V("M"), D(2))))),
                "Page 4, Eq. (26): “P_M^{(N)}(z) = P_{M−1}^{(N)}(z) − zλ_M^N P_{M−N}^{(N)}(z),”. P(M) is P_M^{(3)} at homogeneous couplings λ_j=1, expressed through poly with its index shifted by two. Thus P(0)=1.",
                AssessedProvenance.FromLiterature(Source)),
            Node("quasienergy", "Ordered positive-root quasienergies", QuasienergyFormula(),
                "Page 4, immediately before Eq. (26): “Apart from the zero modes they are given by Λ_k = 1/z_k^{1/N}, where z_k are the roots (P_M^{(N)}(z_k)=0) of the characteristic polynomial”. Eq. (38), pages 5–6, orders the quasienergies by i=1,2,… . Positive real roots are sorted in decreasing order with multiplicity. The index i−1 uses natural subtraction, truncated at zero. List.getD supplies zero when the index is absent. The outer power is Real.rpow, so the exponent is the real number −1/3.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The fixed-index leading prediction", Eqn(Named("claim"), Parenthesized(ClaimBody())),
                "Page 5, Eq. (38), continuing on page 6: “1/z_i^{1/N} = ε_i = π A_i^{(N)}/M = π A^{(N)}/M (x_s^{(N)} + i − 1),” and “for i = 1, 2, …”. Page 6: “Our numerical solutions for polynomial roots with M up to 10⁹ corroborate the conformal invariance prediction (38) for the roots. We conjecture the following exact values for N = 2, 3, 4 and 6”. Eqs. (39) and (41) include “A^{(3)} = 2√3” and “x_s^{(3)} = 7/6 (mod(M,3)=0)”. The leading behaviour is expressed as Tendsto along M=3m for every fixed natural i≥1. The coefficients involving i are real; the lattice-size multiplication 3*m is natural before its cast to ℝ. The TeX labels (4.7), (4.8), (4.10) correspond to printed Eqs. (38), (39), (41).",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("alcaraz-ramos-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Refutation at the lowest mode"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "It suffices to use i=1. The recurrence gives the coefficient formula (−1)^j choose(n−2j,j). Reversing the finite sum at M=3m gives a scaled polynomial Q_m. Binomial asymptotics and dominated convergence imply Q_m(v_m) → F(u) whenever v_m → u and eventually |v_m|≤5, where F(u)=Σ_{k≥0}(−1)^k u^{3k}/(3k+2)!. The alternating-series lower bound through k=5 proves F(u)>0 throughout [4.2321,4.2323]. Bounds on π and √3 place 7π/(3√3) in that interval. The predicted quasienergy limit would produce positive roots with Q_m(v_m)=0 eventually, forcing F(7π/(3√3))=0, a contradiction. The argument does not establish existence or the exact value of the actual lowest-mode limit, equal spacing of its first zeros, other N or residue classes, or asymptotic large-index spacing."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("alcaraz-ramos-2024-conformal-tower-lowest-mode"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("alcaraz-ramos-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Nats => Seq(Mathbb, Grp(V("N")));
    private static Formula Reals => Seq(Mathbb, Grp(V("R")));
    private static Formula Cast(Formula value) => Parenthesized(Seq(value, Sp, Colon, Sp, Reals));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Parenthesized(Seq(V(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body));

    private static Formula PolyFormula()
    {
        var initial = And(Eqn(Call("poly", D(0)), D(1)),
            And(Eqn(Call("poly", D(1)), D(1)), Eqn(Call("poly", D(2)), D(1))));
        var recurrence = All("n", Nats, Eqn(Call("poly", Add(V("n"), D(3))),
            Sub(Call("poly", Add(V("n"), D(2))), Mul(Qualified("Polynomial", "X"), Call("poly", V("n"))))));
        return And(initial, recurrence);
    }

    private static Formula QuasienergyFormula()
    {
        var roots = Seq(Parenthesized(Call("P", V("M"))), Dot, Named("roots"));
        var positive = LambdaOf("z", Reals, new Formula.Relation(D(0), FormulaRelationOperator.LessThan, V("z")));
        var order = LambdaOf("a", Reals, LambdaOf("b", Reals,
            new Formula.Relation(V("a"), FormulaRelationOperator.GreaterThanOrEqual, V("b"))));
        var sorted = At(Qualified("Multiset", "sort"), order,
            At(Qualified("Multiset", "filter"), positive, roots));
        var entry = At(Qualified("List", "getD"), sorted, Parenthesized(Sub(V("i"), D(1))), D(0));
        var power = new Formula.Power(Parenthesized(entry), new Formula.Negate(new Formula.Fraction(D(1), D(3))));
        return All("M", Nats, All("i", Nats, Eqn(Call("quasienergy", V("M"), V("i")), power)));
    }

    private static Formula ClaimBody()
    {
        var sequence = LambdaOf("m", Nats,
            Mul(Cast(Mul(D(3), V("m"))), Call("quasienergy", Parenthesized(Mul(D(3), V("m"))), V("i"))));
        var constant = Mul(Mul(Seq(Qualified("Real", "pi")), Parenthesized(Mul(D(2), At(Qualified("Real", "sqrt"), D(3))))),
            Parenthesized(Sub(Add(new Formula.Fraction(D(7), D(6)), Cast(V("i"))), D(1))));
        var limit = Call("Tendsto", sequence, Named("atTop"), Call("nhds", constant));
        return All("i", Nats, Imp(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, V("i")), limit));
    }
}
