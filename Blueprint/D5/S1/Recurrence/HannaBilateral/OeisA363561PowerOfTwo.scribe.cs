using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.HannaBilateral;

internal sealed class OeisA363561PowerOfTwoDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/HannaBilateral/OeisA363561PowerOfTwo.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2023bilateral");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna's A363561 power-of-two coefficient formula.",
        H("Hanna's A363561 Power-of-Two Formula"),
        Blocks(
            Node("a", "The A363561 sequence", Disp(All("m", Nat(), Eqn(Call("a", X("m")), App(Q("OeisA363558PowerOfTwo", "coeffA"), Cast(App(Q("Real", "sqrt"), D(2)), Cplx()), X("m"))))), "G.f.: Sum_{n=-oo..+oo} x^n * (sqrt(2) + x^n)^(2*n). The parameter is the nonnegative real square root of 2, embedded in the complex numbers.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Hanna's A363561 conjecture", Disp(Eqn(X("claim"), Parenthesized(ClaimBody()))), "a(2^n) = 2^(2^n) for n > 0 (conjecture). Source: OEIS A363561, FORMULA field (an unpaginated entry). Indices are natural numbers; values and numeric expressions on both sides are complex. The displayed hypotheses retain the source range.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The A363561 power-of-two formula", Disp(ClaimBody()), "Apply the complex-parameter dyadic coefficient identity and simplify the indicated parameter powers.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static Formula ClaimBody() => All("n", Nat(), Imp(Lt(D(0), X("n")), Eqn(Call("a", Pow(D(2), X("n"))), Pow(D(2), Pow(D(2), X("n"))))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("hanna-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role,
            name == "result"
                ? new OpenProblemResolutionClaim(ProblemSlugRef.Create("oeis-a363561-hanna-bilateral-power-of-two-values"), ResolutionKind.Proved)
                : null);
    private static Formula X(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Cplx() => Seq(Mathbb, Grp(X("C")));
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, X(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
