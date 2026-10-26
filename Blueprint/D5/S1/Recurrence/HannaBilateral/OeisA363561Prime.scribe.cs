using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.HannaBilateral;

internal sealed class OeisA363561PrimeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/HannaBilateral/OeisA363561Prime.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2023bilateral");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna's A363561 prime-index coefficient formula.",
        H("Hanna's A363561 Prime-Index Formula"),
        Blocks(
            Node("claim", "Hanna's A363561 conjecture", Disp(Eqn(X("claim"), Parenthesized(ClaimBody()))), "a(p) = p*2^((p-1)/2) + 2^p for primes p > 3 (conjecture). Source: OEIS A363561, FORMULA field (an unpaginated entry). Indices are natural numbers; values and numeric expressions on both sides are complex. Nat.div denotes natural-number division, so division by two is integer division.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The A363561 prime-index formula", Disp(ClaimBody()), "Apply the complex-parameter prime coefficient identity and simplify the indicated parameter powers.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static Formula ClaimBody() => All("p", Nat(), Imp(App(Q("Nat", "Prime"), X("p")), Imp(Lt(D(3), X("p")), Eqn(App(Q("OeisA363561PowerOfTwo", "a"), X("p")), Add(Mul(Cast(X("p"), Cplx()), Pow(D(2), App(Q("Nat", "div"), Sub(X("p"), D(1)), D(2)))), Pow(D(2), X("p")))))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("hanna-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role,
            name == "result"
                ? new OpenProblemResolutionClaim(ProblemSlugRef.Create("oeis-a363561-hanna-bilateral-prime-values"), ResolutionKind.Proved)
                : null);
    private static Formula X(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Cplx() => Seq(Mathbb, Grp(X("C")));
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, X(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
