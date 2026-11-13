using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class HannaSelfSubstitutionIntegralityA157675Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegralityA157675.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/hanna2009a163921a157675");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna's A157675 self-substitution series has integer coefficients.",
        H("Hanna's A157675 Integrality"),
        Blocks(
            Node("claim", "The A157675 integrality conjecture",
                Disp(Equal(V("claim"), Parenthesized(ClaimBody()))),
                "OEIS A157675, name (unpaginated): \"G.f.: A(x) = exp( Sum_{n>=1} A(2^n*x)^n * x^n/n ).\" "
                    + "Comment: \"Conjectured to consist entirely of integers.\" "
                    + "The equation is SolvesHanna with L(n)=2^n over the rationals. "
                    + "The conclusion asserts existence of a solution and integer coefficients "
                    + "for every solution. The entry of L at zero is unused.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The A157675 series is integral", Disp(ClaimBody()),
                "The exponential input exp(Sum_{n>=1} 2^n*x^n/n) is the integer geometric "
                    + "series (1-2X) inverse. HannaSelfSubstitutionIntegrality.result therefore "
                    + "gives existence and integrality of every solution of the displayed equation.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hannasubst-a157675"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("hanna-self-substitution-a157675-" + name),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula ClaimBody() => new Formula.Logic(
        Parenthesized(Ex("A", PS(), Solves(V("A")))), FormulaLogicOperator.And,
        Parenthesized(All("A", PS(), new Formula.Logic(Solves(V("A")), FormulaLogicOperator.Implies,
            App(Q("HannaLogarithmicPowerClosure", "IntegralSeries"), V("A"))))));
    private static Formula Solves(Formula series) =>
        App(Q("HannaSelfSubstitutionIntegrality", "SolvesHanna"),
            Parenthesized(Seq(V("fun"), Sp, V("n"), Colon, Sp, Nat(), Sp, Mapsto, Sp,
                new Formula.Power(Parenthesized(Seq(D(2), Colon, Sp, Rat())), V("n")))), series);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Rat() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula PS() => App(Seq(Operatorname, Grp(V("PowerSeries"))), Rat());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
}
