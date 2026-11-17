using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaTripleSquareFrobeniusModThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HannaTripleSquareFrobeniusModThree.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2025a3894congruences");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna's normalized triple-substitution series satisfies both coefficientwise congruences modulo three.",
        H("Triple-substitution congruences modulo three"), Blocks(
            Paragraph(Text("PowerSeries.subst takes the inner series first. All indices and exponents are natural numbers; each rational congruence is expressed by an integer multiplier. The two initial coefficients select the normalized solution.")),
            Node("IsGF", "The normalized triple-substitution equation", All("A", Series(Rat()), Iffn(Predicate(V("A")), SourceBody(V("A")))),
                "OEIS A389475, NAME (unpaginated): \"G.f. A(x) satisfies A(3*x^2) = 2*x^2 + A(x)^2 - 2*A(x)^3.\" The displayed expansion starts x+x^2, fixing the constant coefficient zero and linear coefficient one.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The cube congruence", Iffn(Named("claim"), ClaimBody()),
                "OEIS A389475, FORMULA (4.a), unpaginated: \"(4.a) A(x)^3 == A(x^3) (mod 3) (conjecture).\" Equality modulo three means the difference at every natural coefficient index is three times an integer; existence is included.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claimFourB", "The square congruence", Iffn(Q("FormulaFourB", "claimFourB"), ClaimFourBBody()),
                "OEIS A389475, FORMULA (4.b), unpaginated: \"(4.b) A(x)^2 == x^2 + 2*A(x^3) (mod 3) (conjecture).\" The coefficientwise rational equality has an integer multiplier and includes existence of the normalized series.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("integral_frobenius", "The integral power congruence", FrobeniusFormula(),
                "For every integral power series and all natural n and k, the displayed coefficient is divisible by three. Map to ZMod 3 and apply the power-series Frobenius identity, then lift coefficient equality back to integer divisibility.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", "The cube congruence holds", ClaimBody(),
                "A389475 (4.a), #21672. Reduction modulo two makes the triangular residual coefficients even, giving an integral normalized solution. Its coefficient diagonal is minus two, so strong induction identifies all normalized rational solutions. The integral Frobenius congruence then proves the cube congruence.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("resultFourB", "The square congruence holds", ClaimFourBBody(),
                "A389475 (4.b), #21673. The integral solution's equation reduces in characteristic three to A^2=X^2+2A^3. Frobenius replaces A^3 by A(X^3), giving the square congruence at every coefficient.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static Formula SourceBody(Formula a) => And(Eqn(Call("constantCoeff", a), D(0)), And(Eqn(Coeff(D(1), a), D(1)), Eqn(Compose(a, Mul(D(3), Pow(V("X"), D(2)))),
        Sub(Add(Mul(D(2), Pow(V("X"), D(2))), Pow(a, D(2))), Mul(D(2), Pow(a, D(3)))))));
    private static Formula ClaimBody() => And(Existence(), All("A", Series(Rat()), Imp(Predicate(V("A")),
        All("n", N(), Multiple(V("n"), Sub(Pow(V("A"), D(3)), Compose(V("A"), Pow(V("X"), D(3)))), 3)))));
    private static Formula ClaimFourBBody() => And(Existence(), All("A", Series(Rat()), Imp(Predicate(V("A")),
        All("n", N(), Multiple(V("n"), Sub(Pow(V("A"), D(2)), Add(Pow(V("X"), D(2)),
            Mul(D(2), Compose(V("A"), Pow(V("X"), D(3)))))), 3)))));
    private static Formula FrobeniusFormula() => All("f", Series(Z()), All("n", N(), All("k", N(),
        Rel(Cast(D(3), Z()), Mid, Coeff(V("n"), Sub(Pow(V("f"), Mul(D(3), V("k"))),
            Pow(Compose(V("f"), Pow(V("X"), D(3))), V("k"))))))));
    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("a475-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role,
            name switch
            {
                "result" => new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("h3894-triple-square-frobenius-mod-three"), ResolutionKind.Proved),
                "resultFourB" => new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("h3894-a389475-formula-four-b"), ResolutionKind.Proved),
                _ => null
            });
    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Rel(Formula a, Formula op, Formula b) => Seq(a, Sp, op, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Iffn(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Iff, Sp, Parenthesized(b));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Rat() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Series(Formula r) => Call("PowerSeries", r);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula Coeff(Formula n, Formula a) => Call("coeff", n, a);
    private static Formula Compose(Formula a, Formula h) => App(Q("PowerSeries", "subst"), h, a);
    private static Formula Predicate(Formula a) => Call("IsGF", a);
    private static Formula Existence() => Ex("A", Series(Rat()), Predicate(V("A")));
    private static Formula Multiple(Formula n, Formula f, byte modulus) => Ex("m", Z(),
        Eqn(Coeff(n, f), Mul(Cast(D(modulus), Rat()), Cast(V("m"), Rat()))));
}
