using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class EvenPalindromeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/EvenPalindrome.";
    private static readonly LibraryNoteRef Flp =
        LibraryNoteRef.Create("D5/L/Words/fridlabordepeltomaki2021automaticppl");
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
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula ListOf(Formula value) => Call("List", value);
    private static Formula Fn(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula EvenFormula()
    {
        var indexed = Seq(V("i"), Colon, Call("Fin", Mul(D(2), V("k"))),
            Sp, Mapsto, Sp, Call("upd", Add(V("s"), Call("val", V("i")))));
        var palindrome = Call("Palindrome", Call("ofFn", indexed));
        return Disp(All("s", N(), All("k", N(), Imp(palindrome, LeF(V("k"), D(1))))));
    }
}
