using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class SquareCubeSubstitutionThreeIndexModThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/SquareCubeSubstitutionThreeIndexModThree.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2025a3894congruences");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The A389472 coefficients at indices 3n-1 are divisible by three for n greater than one.",
        H("A389472 modulo three"), Blocks(
            Paragraph(Text("The coefficient sequence a is the existing normalized integer sequence in SquareCubeSubstitutionOddIndexParity. It satisfies X^2(A+1)=A(X^2+X^3), with a(0)=0 and a(1)=a(2)=1. The index uses natural subtraction; n>1 ensures 3n-1 is positive. The independent odd-index parity theorem remains available from the same sequence owner.")),
            Node("claim", "Hanna's residue-class conjecture", Iffn(Named("claim"), ClaimBody()),
                "OEIS A389472, COMMENTS (unpaginated): \"Conjecture: a(3*n-1) = 0 (mod 3) for n > 1.\" The natural index n has its stated lower bound, divisibility is in the integers, and a is the sequence selected by the source expansion x+x^2+2*x^3+3*x^4+6*x^5+... .", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The modulo-three conjecture holds", ClaimBody(),
                "Lucas congruences annihilate summands whose upper binomial index is zero or one modulo three. Strong descent annihilates those with upper index two modulo three beyond the initial case; the remaining index two has a vanishing binomial coefficient. Every summand in the coefficient recurrence is divisible by three.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static Formula ClaimBody() => All("n", N(), Imp(Rel(D(1), Lt, V("n")),
        Rel(Seq(Open, D(3), Colon, Sp, Z(), Close), Mid,
            App(Q("SquareCubeSubstitutionOddIndexParity", "a"), Sub(Mul(D(3), V("n")), D(1))))));
    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("a472-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("h3894-square-cube-three-index"), ResolutionKind.Proved) : null);
    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Rel(Formula a, Formula op, Formula b) => Seq(a, Sp, op, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Iffn(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Iff, Sp, Parenthesized(b));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
}
