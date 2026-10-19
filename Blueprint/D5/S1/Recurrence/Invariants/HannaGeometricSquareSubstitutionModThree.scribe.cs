using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaGeometricSquareSubstitutionModThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HannaGeometricSquareSubstitutionModThree.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized generating equation has an integral solution, and every positive coefficient of every normalized solution is one modulo three.", H("Hanna\u2019s A274479 mod-three conjecture"),
        Blocks(
            Node("IsGF", "The normalized generating equation",
                Disp(Seq(Forall, Sp, F.Id("A"), Colon, Sp, Call("PowerSeries", Seq(Mathbb, Grp(F.Id("Q")))), Comma, Sp, Seq(Parenthesized(Call("IsGF", F.Id("A"))), Sp, Iff, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("constantCoeff", F.Id("A")), Sp, Eq, Sp, D(0))), Sp, Land, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("coeff", D(1), F.Id("A")), Sp, Eq, Sp, D(1))), Sp, Land, Sp, Parenthesized(Seq(new Formula.Power(Parenthesized(F.Id("A")), D(2)), Sp, Eq, Sp, Call("subst", new Formula.Binary(Parenthesized(new Formula.Power(Parenthesized(F.Id("X")), D(2))), FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Power(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(D(1)), FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(F.Id("X")))))), FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Binary(Parenthesized(D(4)), FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Power(Parenthesized(F.Id("X")), D(2))))))), Seq(Minus, D(1))))), F.Id("A"))))))))))),
                "OEIS A274479, Name (unpaginated): \"G.f. satisfies: A(x)^2 = A( x^2/(1 - 2*x - 4*x^2) ).\" The series has rational coefficients, constant coefficient zero and coefficient one at X. The denominator has constant coefficient one, so its power-series inverse exists.", DescribeRole.Definition, AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2016a274479"))),
            Node("claim", "Hanna\u2019s coefficient conjecture",
                Disp(Seq(Parenthesized(Call("claim")), Sp, Iff, Sp, Parenthesized(Seq(Parenthesized(Seq(Exists, Sp, F.Id("A"), Colon, Sp, Call("PowerSeries", Seq(Mathbb, Grp(F.Id("Q")))), Comma, Sp, Call("IsGF", F.Id("A")))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("A"), Colon, Sp, Call("PowerSeries", Seq(Mathbb, Grp(F.Id("Q")))), Comma, Sp, Seq(Parenthesized(Call("IsGF", F.Id("A"))), Sp, Implies, Sp, Parenthesized(Seq(Forall, Sp, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Parenthesized(Seq(D(1), Sp, Le, Sp, F.Id("n"))), Sp, Implies, Sp, Parenthesized(Seq(Exists, Sp, F.Id("m"), Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))), Comma, Sp, Seq(Parenthesized(Seq(Call("coeff", F.Id("n"), F.Id("A")), Sp, Eq, Sp, Parenthesized(Seq(F.Id("m"), Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))))), Sp, Land, Sp, Parenthesized(ModEq( D(3), F.Id("m"), D(1)))))))))))))))),
                "OEIS A274479, Comments (unpaginated): \"a(n) = 1 (mod 3) for n>=1 (conjecture).\" Here a(n) is coeff n A, n starts at one, and the integer m is coerced into Q in the coefficient equality. The proposition also asserts existence.", DescribeRole.Definition, AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2016a274479"))),
            Node("result", "Every positive coefficient is one modulo three",
                Disp(Seq(Parenthesized(Seq(Exists, Sp, F.Id("A"), Colon, Sp, Call("PowerSeries", Seq(Mathbb, Grp(F.Id("Q")))), Comma, Sp, Call("IsGF", F.Id("A")))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("A"), Colon, Sp, Call("PowerSeries", Seq(Mathbb, Grp(F.Id("Q")))), Comma, Sp, Seq(Parenthesized(Call("IsGF", F.Id("A"))), Sp, Implies, Sp, Parenthesized(Seq(Forall, Sp, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Parenthesized(Seq(D(1), Sp, Le, Sp, F.Id("n"))), Sp, Implies, Sp, Parenthesized(Seq(Exists, Sp, F.Id("m"), Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))), Comma, Sp, Seq(Parenthesized(Seq(Call("coeff", F.Id("n"), F.Id("A")), Sp, Eq, Sp, Parenthesized(Seq(F.Id("m"), Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))))), Sp, Land, Sp, Parenthesized(ModEq( D(3), F.Id("m"), D(1)))))))))))))),
                "Coefficientwise contraction constructs an integral compositional inverse. Frobenius in characteristic two makes each division by two exact. Reversion gives the integral solution; uniqueness and the geometric solution over ZMod 3 give every coefficient congruence.", DescribeRole.Theorem, AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2016a274479"))))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("hannageometricsquaresubstitutionmodthree-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        arguments.Length == 0 ? Named(name) : new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula ModEq(Formula modulus, Formula left, Formula right) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id("Int")), Dot,
            Operatorname, Grp(F.Id("ModEq"))), [modulus, left, right]);
}
