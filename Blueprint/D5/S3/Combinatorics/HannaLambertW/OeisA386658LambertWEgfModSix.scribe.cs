using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.HannaLambertW;

internal sealed class OeisA386658LambertWEgfModSix_Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/HannaLambertW/OeisA386658LambertWEgfModSix.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2025a386655a386658");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integrality and a period-six congruence for Hanna's Lambert W exponential coefficients.",
        H("Hanna's OEIS 386658 congruence"), Blocks(
            Node("a", "OEIS A386658", Disp(Seq(Bind("m", Nat()), Eqn(Call("a", F.Id("m")), Call("egf", D(5), F.Id("m"))))), "The entry NAME reads verbatim: E.g.f.: Sum_{n>=0} (5^n*x + LambertW(x))^n / n!. Here egf is the rational coefficient function of OeisA386655LambertWEgfModSix.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The proposed six-term pattern", Disp(Eqn(Named("claim"), Parenthesized(ClaimBody()))), "Conjecture: for n >= 6, a(n) (mod 6) equals [4, 3, 0, 3, 0, 5] repeating. This is the COMMENTS sentence of OEIS A386658 (unpaginated). The integer z has rational cast a(n); getD uses the zero-based index (n-6) mod 6 and default zero. Both remainder operations and natural subtraction are Lean integer or natural operations, respectively.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Hanna's congruence", Disp(ClaimBody()), "The integral closed form and its six-term periodicity reduce the assertion to the six indices from six through eleven, which give the displayed pattern.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));
    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("a386658-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Z() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rat() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mod(Formula a, Formula b) => new Formula.Modulo(a, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Impl(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Bind(string name, Formula type) => Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula Pattern() => Seq(OpenBracket, D(4), Comma, Sp, D(3), Comma, Sp, D(0), Comma, Sp, D(3), Comma, Sp, D(0), Comma, Sp, D(5), CloseBracket);
    private static Formula ClaimBody() => Seq(Bind("n", Nat()), Impl(Seq(D(6), Sp, Le, Sp, F.Id("n")),
        Seq(Exists, Sp, F.Id("z"), Colon, Sp, Z(), Comma, Sp,
            And(Eqn(Cast(F.Id("z"), Rat()), Call("a", F.Id("n"))),
                Eqn(Mod(F.Id("z"), D(6)), Call("getD", Pattern(),
                    Mod(Parenthesized(Sub(F.Id("n"), D(6))), D(6)), D(0)))))));


}
