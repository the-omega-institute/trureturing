using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaSigmaProductExpModThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThree.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2025a382124a382125");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The A382124 and A382125 coefficients agree at the Frobenius indices modulo three.",
        H("Hanna's Sigma-Product Exponential Congruence"),
        Blocks(
            Node("A", "The A382124 generating function", Eqn(Call("A"), SeriesBody(true)),
                "G.f. A(x) = exp( Sum_{n>=1} sigma(n)*sigma(2*n)/3 * x^n/n ), where sigma(n) = A000203(n) is the sum of the divisors of n. The NAME is unpaginated. The formal exponential is PowerSeries.exp over the rationals, composed with the power series constructed by mk. Indices begin at zero; the zero coefficient in the input is zero. All divisions displayed here are rational divisions.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("B", "The A382125 generating function", Eqn(Call("B"), SeriesBody(false)),
                "G.f. A(x) = exp( Sum_{n>=1} sigma(n)*sigma(2*n) * x^n/n ), where sigma(n) = A000203(n) is the sum of the divisors of n. The NAME is unpaginated. The formal exponential is PowerSeries.exp over the rationals, composed with the power series constructed by mk. Indices begin at zero; the zero coefficient in the input is zero. All divisions displayed here are rational divisions.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Hanna's congruence", Seq(Call("claim"), Sp, Iff, Sp, P(ClaimBody())),
                "Conjecture: a(n) == A382125(3*n) (mod 3) for n >= 0. OEIS A382124, COMMENT (unpaginated). The two integer witnesses encode the indicated rational coefficients and their integer congruence for every natural index.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("AIntegral", "Integer coefficients of A", All("n", N(), Ex("z", Z(), Eqn(Coeff(V("n"), Call("A")), Cast(V("z"), Q())))),
                "The integer sequence sigma(n) sigma(2n)/3 satisfies the Dold prime-power congruences. At the prime three, multiplicativity separates a power of three and the difference of two consecutive divisor sums supplies the needed power of three.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)),
            Node("integerSeries", "An integer lift of A", Eqn(Call("integerSeries"), Call("mk", Lam("n", N(), QualifiedCall("Classical", "choose", Call("AIntegral", V("n")))))),
                "Classical.choose selects the integer coefficient whose rational image equals coefficient n of A.", DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source)),
            Node("integerCube_map", "The cube maps to B", Eqn(Call("map", QualifiedCall("Int", "castRingHom", Q()), Pow(Call("integerSeries"), D(3))), Call("B")),
                "Multiplying the logarithmic input by three cubes its formal exponential. Mapping the integer lift to the rationals therefore identifies its cube with B.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)),
            Node("cube_residues", "Frobenius in each residue class", All("n", N(), And(Mod(Coeff(Mul(D(3), V("n")), Pow(Call("integerSeries"), D(3))), Coeff(V("n"), Call("integerSeries"))), And(Mod(Coeff(Add(Mul(D(3), V("n")), D(1)), Pow(Call("integerSeries"), D(3))), D(0)), Mod(Coeff(Add(Mul(D(3), V("n")), D(2)), Pow(Call("integerSeries"), D(3))), D(0))))),
                "Reduction to ZMod(3) turns cubing into substitution of X cubed. The coefficients in the other two residue classes vanish modulo three.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)),
            Node("result", "The A382124 conjecture", ClaimBody(),
                "The integer lift and its cube give the two coefficient witnesses; Frobenius proves their congruence at every index.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("hannasigmaproductexpmodthree-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula P(Formula value) => Parenthesized(value);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Cast(Formula a, Formula type) => P(Seq(a, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula And(Formula a, Formula b) => Seq(P(a), Sp, Land, Sp, P(b));
    private static Formula Lam(string name, Formula type, Formula body) =>
        P(Seq(V("fun"), Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Coeff(Formula n, Formula series) => Call("coeff", n, series);
    private static Formula Mod(Formula a, Formula b) => Seq(a, Sp, Equiv, Sp, b, Sp, Pmod, Grp(D(3)));
    private static Formula ClaimBody() => All("n", N(), Ex("u", Z(), Ex("v", Z(), And(Eqn(Coeff(V("n"), Call("A")), Cast(V("u"), Q())), And(Eqn(Coeff(Mul(D(3), V("n")), Call("B")), Cast(V("v"), Q())), Mod(V("u"), V("v")))))));
    private static Formula SigmaAt(Formula n) => Cast(Call("sigma", D(1), n), Q());
    private static Formula SeriesBody(bool divideThree)
    {
        var n = V("n");
        Formula value = Mul(SigmaAt(n), SigmaAt(Mul(D(2), n)));
        if (divideThree) value = new Formula.Fraction(value, D(3));
        value = new Formula.Fraction(value, Cast(n, Q()));
        return Call("subst", Call("mk", Lam("n", N(), value)), Call("exp", Q()));
    }
    private static Formula QualifiedCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(name))), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
