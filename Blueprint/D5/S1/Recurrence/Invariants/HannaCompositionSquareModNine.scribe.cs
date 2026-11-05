using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaCompositionSquareModNineDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HannaCompositionSquareModNine.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2025a3894congruences");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized solution of Hanna's composition equation has square coefficients divisible by nine beyond degree three.",
        H("Square coefficients modulo nine"), Blocks(
            Paragraph(Text("The rings are formal power-series rings over the displayed coefficient rings. PowerSeries.subst takes the inner series first. The rational series has constant coefficient zero and linear coefficient one. Each rational congruence asserts an integer multiple of its modulus, so it includes the integrality needed for that congruence.")),
            Node("IsGF", "The normalized composition equation", All("A", Series(Rat()), Iffn(Predicate(V("A")), SourceBody(V("A")))),
                "OEIS A389474, NAME (unpaginated): \"G.f. A(x) satisfies A( x^2 + 2*x^3 + 2*A(x)^2 ) = 3*A(x)^2.\" The displayed expansion begins x+x^2 and fixes the two normalization coefficients.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The square-coefficient conjecture", Iffn(Named("claim"), ClaimBody()),
                "OEIS A389474, FORMULA (3), unpaginated: \"(3) [x^n] A(x)^2 == 0 (mod 9) for n > 3 (conjecture).\" The index n is natural and the multiplier m is integral; existence of a normalized rational solution is included.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claimFour", "The power-congruence conjecture", Iffn(Q("FormulaFour", "claimFour"), ClaimFourBody()),
                "OEIS A389474, FORMULA (4), unpaginated: \"(4) [x^n] A(x)^(3*k) - A(x^3)^k == 0 (mod 3) for n >= 1 and k >= 1 (conjecture).\" Both indices are natural numbers with the stated lower bounds, and the congruence has an integer multiplier.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The square-coefficient conjecture holds", ClaimBody(),
                "Triangular lifting gives an integral solution and coefficient induction identifies every normalized rational solution with it. Write A=X+X^2Q and H=X^2+2X^3+2A^2. The equation gives H(1+HQ(H))=3A^2. The factor with constant coefficient one has an integral inverse, so H is three times an integral series. Then A^2-X^2-2X^3=H^2Q(H) is nine times an integral series.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("resultFour", "The power-congruence conjecture holds", ClaimFourBody(),
                "The integral solution satisfies the coefficientwise Frobenius congruence for every exponent 3k. Identification with each normalized rational solution gives the stated integer multiples.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static Formula SourceBody(Formula a) => And(Eqn(Call("constantCoeff", a), D(0)), And(Eqn(Coeff(D(1), a), D(1)), Eqn(
        Compose(a, Add(Add(Pow(V("X"), D(2)), Mul(D(2), Pow(V("X"), D(3)))), Mul(D(2), Pow(a, D(2))))),
        Mul(D(3), Pow(a, D(2))))));
    private static Formula ClaimBody() => And(Existence(), All("A", Series(Rat()), Imp(Predicate(V("A")),
        All("n", N(), Imp(Rel(D(3), Lt, V("n")), Multiple(V("n"), Pow(V("A"), D(2)), 9))))));
    private static Formula ClaimFourBody() => And(Existence(), All("A", Series(Rat()), Imp(Predicate(V("A")),
        All("n", N(), All("k", N(), Imp(Rel(D(1), Le, V("n")), Imp(Rel(D(1), Le, V("k")),
            Multiple(V("n"), Sub(Pow(V("A"), Mul(D(3), V("k"))), Pow(Compose(V("A"), Pow(V("X"), D(3))), V("k"))), 3))))))));
    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("a474-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);
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
