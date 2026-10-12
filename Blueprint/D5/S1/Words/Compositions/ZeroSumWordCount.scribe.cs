using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Compositions;

internal sealed class ZeroSumWordCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Compositions/ZeroSumWordCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Factorial bounds for zero-sum words with distinct letters.",
        H("Zero-sum word counts"),
        Blocks(
            Paragraph(Text("For a finite integer alphabet S, an ordering is a list using each "
                + "letter of S exactly once. A weak word has nonnegative sums for all prefixes. "
                + "A strict word has positive sums for all nonempty proper prefixes. The "
                + "functions weakCount and strictCount count these words. The alphabet sum "
                + "is the sum of its integer letters. Subtraction in factorial arguments "
                + "is natural subtraction.")),
            Node("strictCount_le_factorial", "Upper bound for strict words", ZeroSumFormula(Q(
                Call("strictCount", V("S")), Le, ReducedFactorial())),
                "Rotate each strict word to a fixed initial letter. Two words with the "
                + "same image lie in the same rotation class. For a zero-sum word, two "
                + "different strict rotations would give a segment with both positive "
                + "and negative sum. The map into anchored orderings is therefore injective."),
            Node("factorial_le_weakCount", "Lower bound for weak words", ZeroSumFormula(Q(
                ReducedFactorial(), Le, Call("weakCount", V("S")))),
                "Cut each zero-sum word after a minimum prefix sum. The resulting rotation "
                + "has nonnegative prefix sums, so every rotation class contains a weak "
                + "word. Rotating weak words to a fixed letter maps onto all anchored "
                + "orderings. There are exactly (|S|-1)! anchored orderings."),
            Node("weakCount_le_factorial", "Trivial upper bound", All(V("S"), Alphabet(), Q(
                Call("weakCount", V("S")), Le,
                Call("factorial", Call("card", V("S"))))),
                "Weak words form a subset of all orderings, whose number is |S|!."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("zero-sum-word-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Alphabet() => Call("Finset", Seq(Mathbb, Grp(V("Z"))));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula ReducedFactorial() =>
        Call("factorial", Seq(Open, Call("card", V("S")), Sp, Minus, Sp, D(1), Close));
    private static Formula ZeroSumFormula(Formula body) => All(V("S"), Alphabet(), Q(
        Call("sum", V("S")), Eq, D(0), Implies,
        Call("Nonempty", V("S")), Implies, body));
    private static Formula Q(params Formula[] items)
    {
        var spaced = new Formula[items.Length * 2 - 1];
        for (var i = 0; i < items.Length; i++)
        {
            spaced[2 * i] = items[i];
            if (i + 1 < items.Length) spaced[2 * i + 1] = Sp;
        }
        return Seq(spaced);
    }
}
