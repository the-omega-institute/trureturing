using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class HannaA181082IntegralityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/HannaA181082Integrality.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2010a181082");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer coefficients of Hanna's OEIS A181082 formal exponential.",
        H("Hanna A181082 Integrality"), Blocks(
            Node("logarithm", "The rational logarithm", Eqn(Call("logarithm"), Qualified("PowerSeries", "mk", Lam("m", N(), DiagonalSum(true, Pow(Cast(Choose(V("n"), V("k")), Q()), Add(V("n"), V("k"))))))),
                "OEIS A181082, NAME (web entry, no page number): \"Expansion of g.f.: exp( Sum_{n>=1} [Sum_{k=0..n} C(n,k)^(n+k) * x^k] * x^n/n ).\" The displayed coefficient formula collects the terms of degree m. The indices and the exponent n+k are natural numbers. The binomial coefficient is Nat.choose.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("A", "The formal exponential", Eqn(Call("A"), ExpOf(Call("logarithm"))),
                "OEIS A181082, NAME (web entry, no page number): \"Expansion of g.f.: exp( Sum_{n>=1} [Sum_{k=0..n} C(n,k)^(n+k) * x^k] * x^n/n ).\" The exponential is formal over the rationals. PowerSeries.subst takes the inner series as its first argument.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Integer coefficients", Iffn(Call("claim"), ClaimBody()),
                "OEIS A181082, first COMMENTS line (web entry, no page number): \"Conjecture: this sequence consists entirely of integers.\" The degree m ranges over all natural numbers, including zero; the integer z may depend on m.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Integrality in every degree", ClaimBody(),
                "Every ordinary coefficient of the displayed formal exponential is an integer, without a degree cutoff, factorial scaling, positivity or extra hypotheses. The source is Paul D. Hanna's A181082 integrality conjecture, preregistration #30033. The fixed OEIS source is revision 6 at commit de48538e52019dc132e250666b0d677b40045ceb; its SHA256 is c188a5d690604f08247757259908274b40830107aae8998171b674dc76ee1da5. Global literature completeness, priority and originality are unverified.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("hannaa181082-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, name == "result" ? Blocks(
                Paragraph(Text(prose)),
                Paragraph(Text("Parameter correspondence: define F82(0,k)=0 and F82(n,k)=Nat.choose(n,k)^(n+k) for n>0. Apply HannaA181070Integrality.integralGeneric to F82. Its conclusion is coefficientwise integrality of PowerSeries.subst (L F82) (PowerSeries.exp Q), using the existing DoldExponentialIntegrality criterion and existing AINTLIB port. No provider is reproved and no third-party code is copied; the port's provenance and license are in Library/RecurrenceComposition/aintlib2026dieudonnedwork.md.")),
                Paragraph(Text("The first criterion hypothesis is n divides k*F82(n,k) for n>0. HannaA181070Integrality.binomDiv gives n divides k*Nat.choose(n,k); multiply by Nat.choose(n,k)^(n+k-1), since n+k>=1. The private helper div82 is used directly by result.")),
                Paragraph(Text("For the prime-scaling hypothesis fix any prime p, n>0 and k>=0. Put a=padicValNat(p,n), q=p^(a+1), t=n+k, b=Nat.choose(n,k) and B=Nat.choose(p*n,p*k). HannaA181070Integrality.binomCong gives B congruent to b modulo q; taking the power p*t reduces the goal to b^(p*t) congruent to b^t modulo q.")),
                Paragraph(Text("If p divides b, Nat.padicValNat_lt_self gives a<n and hence a+1<=t. Both b^t and b^(p*t) are divisible by q. This includes b=0, with no use of a valuation of zero. Otherwise p and b are coprime. From p^a divides n and n divides k*b, coprime cancellation yields p^a divides k, hence p^a divides t. Write t=p^a*u. Euler's theorem and Nat.totient_prime_pow_succ give b^((p-1)*t) congruent to 1 modulo q. Thus b^(p*t)=b^t*b^((p-1)*t) is congruent to b^t. Every prime, including 2, is covered; so are a=0 and k=0. The private exponent_congruence is consumed by cong82, which is consumed by result.")),
                Paragraph(Text("Finite diagonal equality: in degree m only n<=m and n+k=m contribute. HannaA181070Integrality.literalBounded identifies exactly the source sum with L F82. When k>n, Nat.choose(n,k)=0 and n+k>0; the term vanishes. The n=0 convention is zero. At m=0 the logarithm has coefficient zero, so the ordinary exponential has constant coefficient 1. There is no analytic convergence premise or infinite-sum rearrangement.")),
                Paragraph(Text("Per-declaration shape: div82, exponent_congruence, cong82 and result are bind-only, with no escape witness. Each private helper has the live consumer named above. logarithm, A, claim and F82 are definitions, not proof credit. The direct frozen provider is D5/S1/Recurrence/Algebraic/HannaA181070Integrality with statement_id sha256:3092db66acc6fd1d6f4354d8aefb1d52c3e934f2a8cbf9e86d1bed30e823810b. The proposed admission basis for the sole public result is open-problem-resolution; no global novelty or delivered-resolution claim follows from this exposition.")))
                : Blocks(Paragraph(Text(prose))), role);

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
    private static Formula Choose(Formula n, Formula k) => Qualified("Nat", "choose", n, k);
    private static Formula ExpOf(Formula f) => Qualified("PowerSeries", "subst", f, Qualified("PowerSeries", "exp", Q()));
    private static Formula RangeSum(string index, Formula bound, Formula body) =>
        Qualified("Finset", "sum", Qualified("Finset", "range", bound), Lam(index, N(), body));
    private static Formula DiagonalSum(bool bounded, Formula value)
    {
        var n = V("n"); var k = V("k"); var m = V("m");
        var condition = And(Lt(D(0), n), Eqn(Add(n, k), m));
        var summand = Seq(V("if"), Sp, Parenthesized(condition), Sp, V("then"), Sp,
            new Formula.Fraction(value, Cast(n, Q())), Sp, V("else"), Sp, D(0));
        return RangeSum("n", Add(m, D(1)), RangeSum("k", Add(bounded ? n : m, D(1)), summand));
    }
    private static Formula ClaimBody() => All("m", N(), Ex("z", Z(), Eqn(Coeff(V("m"), Call("A")), Cast(V("z"), Q()))));
}
