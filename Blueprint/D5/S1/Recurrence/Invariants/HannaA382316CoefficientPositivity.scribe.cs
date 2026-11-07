using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaA382316CoefficientPositivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HannaA382316CoefficientPositivity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A normalized rational solution exists, and every normalized rational solution of Hanna's equation has nonnegative coefficients.",
        H("Hanna's A382316 nonnegativity conjecture"),
        Blocks(
            Node("IsSourceSeries", "The normalized source equation",
                Disp(All("A", Series(), Relation(Call("IsSourceSeries", F.Id("A")), Iff, SourceBody()))),
                "OEIS A382316, NAME (unpaginated): \"G.f. satisfies A(x) = A(x^2) + A(x^2)^2*A(x^3)/A(x^6), with A(0) = 0 and A'(0) = 1.\" FORMULA (1) (unpaginated): \"(1) A(x) = A(x^2) + A(x^2)^2*A(x^3)/A(x^6).\" The rational series A has constant coefficient zero and coefficient one at X. Each substitution is formed in PowerSeries Q and then coerced into LaurentSeries Q. The quotient is in that field; its denominator is nonzero because its coefficient at degree six is one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Note())),
            Node("claim", "The nonnegativity assertion",
                Disp(Relation(Call("claim"), Iff, ClaimBody())),
                "OEIS A382316, COMMENTS (unpaginated): \"Conjecture: there are no negative terms.\" FORMULA (unpaginated): \"G.f. A(x) = Sum_{n>=1} a(n)*x^n satisfies the following formulas.\" Here a(n) is coeff n A. The first OFFSET component is one; the second component is display metadata. Existence of a rational solution is asserted together with the coefficient inequalities for every normalized rational solution and every natural index at least one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Note())),
            Node("result", "Every source solution has nonnegative coefficients",
                Disp(ClaimBody()),
                "Write A = X * f with constantCoeff f = 1. The normalized equation yields a series g with constantCoeff g = 1, f = subst (X^2) f * g and g = X + subst (X^2) f * subst (X^3) g. Strong induction proves nonnegativity of both coefficient sequences, first for g at each positive degree and then for f. A normalized coefficient contraction supplies existence. These are formal series identities and require no convergence hypothesis.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Note()))),
        edges: [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Recurrence/Invariants/UnitReversionSquareParity")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity"))]));

    private static LibraryNoteRef Note() => LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2025a382316");

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("hannaa382316-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula ClaimBody()
    {
        var existence = Seq(Exists, Sp, F.Id("A"), Colon, Sp, Series(), Comma, Sp,
            Call("IsSourceSeries", F.Id("A")));
        var signs = All("n", Seq(Mathbb, Grp(F.Id("N"))), Seq(
            Relation(D(1), Le, F.Id("n")), Sp, Implies, Sp,
            Relation(D(0), Le, Call("coeff", F.Id("n"), F.Id("A")))));
        var universal = All("A", Series(), Seq(
            Call("IsSourceSeries", F.Id("A")), Sp, Implies, Sp, signs));
        return Seq(Parenthesized(existence), Sp, Land, Sp, Parenthesized(universal));
    }

    private static Formula SourceBody() => Seq(
        Relation(Call("constantCoeff", F.Id("A")), Eq, D(0)), Sp, Land, Sp,
        Relation(Call("coeff", D(1), F.Id("A")), Eq, D(1)), Sp, Land, Sp,
        Relation(CastLaurent(F.Id("A")), Eq,
            new Formula.Binary(Substituted(2), FormulaBinaryOperator.Add,
                new Formula.Fraction(
                    new Formula.Binary(new Formula.Power(Substituted(2), D(2)),
                        FormulaBinaryOperator.Multiply, Substituted(3)), Substituted(6)))));

    private static Formula Substituted(int exponent) => CastLaurent(Call("subst",
        Parenthesized(Seq(new Formula.Power(F.Id("X"), D((byte)exponent)), Colon, Sp, Series())), F.Id("A")));
    private static Formula CastLaurent(Formula value) =>
        Parenthesized(Seq(value, Colon, Sp, Call("LaurentSeries", Seq(Mathbb, Grp(F.Id("Q"))))));
    private static Formula Series() => Call("PowerSeries", Seq(Mathbb, Grp(F.Id("Q"))));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Relation(Formula left, Formula relation, Formula right) =>
        Parenthesized(Seq(left, Sp, relation, Sp, right));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        arguments.Length == 0 ? Named(name) : new Formula.Apply(Named(name), [.. arguments]);
}
