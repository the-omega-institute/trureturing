using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class HannaA181316IntegralityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/HannaA181316Integrality.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/hanna2010a181316");
    private const string Original = "Conjecture: exp( Sum_{n>=1} (q-1)*((q^n-1)/(q-1))^(n-1)*x^n/n ) is an integer series for all integer q>1.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer coefficients of Hanna's full all-parameter q-integer exponential.",
        H("Hanna A181316: all integer parameters"), Blocks(
            Node("logarithm", "The literal rational logarithm",
                All("q", Z(), Eqn(Call("logarithm", V("q")),
                    Qualified("PowerSeries", "mk", Lam("n", N(), LogCoefficient())))),
                "OEIS A181316, sole COMMENTS conjecture, revision 2 (unpaginated): \"" + Original + "\" The positive coefficient is exactly the source rational quotient and exponent. Its constant coefficient is zero. The variable q is an integer and n is a natural index.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("A", "The formal exponential",
                All("q", Z(), Eqn(Call("A", V("q")), ExpOf(Call("logarithm", V("q"))))),
                "The exponential is formal over Q. Substitution takes logarithm q first and exp Q second. The zero logarithm constant makes this the ordinary formal exponential, without analytic convergence.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The complete source assertion", Iffn(Call("claim"), ClaimBody()),
                Original + " Every integer q>1 and every natural degree N, including zero, is quantified. Integrality is an integer witness for each rational coefficient; there is no nonnegativity assertion.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Integrality for every allowed parameter", ClaimBody(),
                "For q>=2 write S(n)=1+q+...+q^(n-1) and b(n)=(q-1)*S(n)^(n-1). The finite geometric identity identifies the literal quotient with S(n). Fix a prime p, n>0, and a=v_p(n). If p divides q-1, factoring S(p^a*t) into a geometric blocks proves p^a divides S(n). The factor q-1 supplies the remaining p in b(n) and b(p*n); a=0 is handled directly. If p does not divide q-1, the original fermat_lift theorem gives q^(p*n) congruent to q^n modulo p^(a+1), uniformly including p dividing q. Cancelling the prime unit q-1 gives S(p*n) congruent to S(n). For a unit S(n), Euler's theorem identifies the exponents p*n-1 and n-1. For a nonunit, n cannot equal p^a: Frobenius in ZMod p would otherwise give q^n=q and S(n)=1. Thus n=p^a*t with t>=2 and n-1>=a+1, so both powers vanish at the required modulus. This covers p=2, q=2, n=1 and every valuation. The existing DoldExponentialIntegrality.integral_exp_of_dold now proves all coefficients integral. The explicit conversion q.toNat covers every allowed integer q. No Euler-product machinery is reproved and no sign condition on its exponents is used.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hanna181316"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("hannaa181316-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(V(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(name))), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iffn(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Iff, Sp, Parenthesized(b));
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Parenthesized(Seq(V("fun"), Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Coeff(Formula n, Formula a) => Qualified("PowerSeries", "coeff", n, a);
    private static Formula ExpOf(Formula f) => Qualified("PowerSeries", "subst", f, Qualified("PowerSeries", "exp", Q()));
    private static Formula RangeSum(string index, Formula bound, Formula body) =>
        Qualified("Finset", "sum", Qualified("Finset", "range", bound), Lam(index, N(), body));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula LogCoefficient()
    {
        var q = Cast(V("q"), Q()); var n = V("n");
        var value = new Formula.Fraction(Mul(Sub(q, D(1)),
            Pow(new Formula.Fraction(Sub(Pow(q, n), D(1)), Sub(q, D(1))), Sub(n, D(1)))), Cast(n, Q()));
        return Seq(V("if"), Sp, Eqn(n, D(0)), Sp, V("then"), Sp, D(0), Sp, V("else"), Sp, value);
    }
    private static Formula ClaimBody() => All("q", Z(), Imp(Lt(D(1), V("q")),
        All("N", N(), Ex("z", Z(), Eqn(Coeff(V("N"), Call("A", V("q"))), Cast(V("z"), Q()))))));
}
