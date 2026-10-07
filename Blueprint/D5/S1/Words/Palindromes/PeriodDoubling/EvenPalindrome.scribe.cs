using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class EvenPalindromeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/EvenPalindrome.";
    private static readonly LibraryNoteRef Li =
        LibraryNoteRef.Create("D5/L/Words/li2020rulerperioddoubling");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An even palindrome in period doubling has length zero or two.",
        H("Even Palindromes in Period Doubling"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pd-evenpalindrome-even-palindrome-length"),
                DeclarationHandle.Create(Prefix + "even_palindrome_length"),
                H("The even-palindrome obstruction"),
                StatementSource.FromAuthor(EvenFormula()),
                AssessedProvenance.FromRepo(Li),
                Blocks(Paragraph(Text("The subword starts at zero-based offset s and has length 2k. Reflection in an even length exchanges index parities. All source letters at even zero-based positions are zero, whereas every four consecutive positions include a one at index congruent to one modulo four. Thus a palindromic factor of even length at least four is impossible."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Upd(Formula n) =>
        new Formula.Apply(new Formula.Subscript(V("u"), Seq(Mathrm, Grp(V("pd")))), [n]);
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula LeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);

    private static Formula EvenFormula()
    {
        var indexed = Seq(V("i"), Colon, Call("Fin", Mul(D(2), V("k"))),
            Sp, Mapsto, Sp, Upd(Add(V("s"), Call("val", V("i")))));
        var palindrome = Call("Palindrome", Call("ofFn", indexed));
        return Disp(All("s", N(), All("k", N(), Imp(palindrome, LeF(V("k"), D(1))))));
    }
}
