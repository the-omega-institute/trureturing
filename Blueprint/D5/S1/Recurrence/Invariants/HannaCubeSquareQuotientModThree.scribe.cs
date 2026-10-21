using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaCubeSquareQuotientModThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HannaCubeSquareQuotientModThree.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized generating equation has an integral solution, and every positive coefficient of every normalized solution is one modulo three.", H("Hanna\u2019s A377100 mod-three conjecture"),
        Blocks(
            Node("IsGF", "The normalized generating equation",
                Disp(Seq(Forall, Sp, F.Id("A"), Colon, Sp, Call("PowerSeries", Seq(Mathbb, Grp(F.Id("Q")))), Comma, Sp, Seq(Parenthesized(Call("IsGF", F.Id("A"))), Sp, Iff, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("constantCoeff", F.Id("A")), Sp, Eq, Sp, D(0))), Sp, Land, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("coeff", D(1), F.Id("A")), Sp, Eq, Sp, D(1))), Sp, Land, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("A"), Colon, Sp, Call("LaurentSeries", Seq(Mathbb, Grp(F.Id("Q")))))), Sp, Eq, Sp, new Formula.Binary(Parenthesized(new Formula.Fraction(Parenthesized(Seq(Call("subst", new Formula.Power(Parenthesized(F.Id("X")), D(3)), F.Id("A")), Colon, Sp, Call("LaurentSeries", Seq(Mathbb, Grp(F.Id("Q")))))), Parenthesized(Seq(Call("subst", new Formula.Power(Parenthesized(F.Id("X")), D(2)), F.Id("A")), Colon, Sp, Call("LaurentSeries", Seq(Mathbb, Grp(F.Id("Q")))))))), FormulaBinaryOperator.Add, Parenthesized(new Formula.Power(Parenthesized(Parenthesized(Seq(F.Id("A"), Colon, Sp, Call("LaurentSeries", Seq(Mathbb, Grp(F.Id("Q"))))))), D(2))))))))))))),
                "OEIS A377100, Name (unpaginated): \"G.f. A(x) satisfies A(x) = A(x^3)/A(x^2) + A(x)^2.\" The series has rational coefficients, constant coefficient zero and coefficient one at X. The quotient is taken in LaurentSeries Q.", DescribeRole.Definition, AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2024a377100"))),
            Node("claim", "Hanna\u2019s coefficient conjecture",
                Disp(Seq(Parenthesized(Call("claim")), Sp, Iff, Sp, Parenthesized(Seq(Parenthesized(Seq(Exists, Sp, F.Id("A"), Colon, Sp, Call("PowerSeries", Seq(Mathbb, Grp(F.Id("Q")))), Comma, Sp, Call("IsGF", F.Id("A")))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("A"), Colon, Sp, Call("PowerSeries", Seq(Mathbb, Grp(F.Id("Q")))), Comma, Sp, Seq(Parenthesized(Call("IsGF", F.Id("A"))), Sp, Implies, Sp, Parenthesized(Seq(Forall, Sp, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Parenthesized(Seq(D(1), Sp, Le, Sp, F.Id("n"))), Sp, Implies, Sp, Parenthesized(Seq(Exists, Sp, F.Id("m"), Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))), Comma, Sp, Seq(Parenthesized(Seq(Call("coeff", F.Id("n"), F.Id("A")), Sp, Eq, Sp, Parenthesized(Seq(F.Id("m"), Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))))), Sp, Land, Sp, Parenthesized(ModEq( D(3), F.Id("m"), D(1)))))))))))))))),
                "OEIS A377100, Comments (unpaginated): \"Conjecture: a(n) == 1 (mod 3) for n >= 1, which has been verified for the initial 2305 terms.\" Here a(n) is coeff n A, n starts at one, and the integer m is coerced into Q in the coefficient equality. The proposition also asserts existence.", DescribeRole.Definition, AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2024a377100"))),
            Node("result", "Every positive coefficient is one modulo three",
                Disp(Seq(Parenthesized(Seq(Exists, Sp, F.Id("A"), Colon, Sp, Call("PowerSeries", Seq(Mathbb, Grp(F.Id("Q")))), Comma, Sp, Call("IsGF", F.Id("A")))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("A"), Colon, Sp, Call("PowerSeries", Seq(Mathbb, Grp(F.Id("Q")))), Comma, Sp, Seq(Parenthesized(Call("IsGF", F.Id("A"))), Sp, Implies, Sp, Parenthesized(Seq(Forall, Sp, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Parenthesized(Seq(D(1), Sp, Le, Sp, F.Id("n"))), Sp, Implies, Sp, Parenthesized(Seq(Exists, Sp, F.Id("m"), Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))), Comma, Sp, Seq(Parenthesized(Seq(Call("coeff", F.Id("n"), F.Id("A")), Sp, Eq, Sp, Parenthesized(Seq(F.Id("m"), Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))))), Sp, Land, Sp, Parenthesized(ModEq( D(3), F.Id("m"), D(1)))))))))))))),
                "Writing the solution as X times a normalized series gives a coefficient contraction over every commutative ring. The integral fixed point reduces to the geometric series over ZMod 3. Injectivity into Laurent series identifies the polynomial equation with the displayed quotient.", DescribeRole.Theorem, AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2024a377100")), new OpenProblemResolutionClaim(ProblemSlugRef.Create("hanna-a377100-mod-three"), ResolutionKind.Proved))),
        edges: [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Recurrence/Invariants/UnitReversionSquareParity")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Recurrence/Invariants/ScaledReversionCongruence"))]));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("hannacubesquarequotientmodthree-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        arguments.Length == 0 ? Named(name) : new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula ModEq(Formula modulus, Formula left, Formula right) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id("Int")), Dot,
            Operatorname, Grp(F.Id("ModEq"))), [modulus, left, right]);
}
