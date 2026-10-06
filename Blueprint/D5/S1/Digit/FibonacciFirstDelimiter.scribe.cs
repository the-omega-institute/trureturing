using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class FibonacciFirstDelimiterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Appending one terminal bit to a positive canonical Fibonacci word determines its first delimiter and preserves every following bit.",
        H("The First Fibonacci Delimiter"),
        Blocks(
            Paragraph(Text(
                "Fibonacci weights begin with one and two. A positive natural number has "
                + "canonical occupied indices with no adjacent indices. The dense word lists "
                + "their bits from least to most significant, ending at the highest occupied bit.")),
            Paragraph(Text(
                "The return blocks are zero and one followed by zero. Expansion with the "
                + "transient terminal channel adds a final one after these blocks. Thus a word "
                + "in this form has no consecutive ones internally and ends in one.")),
            Paragraph(Text(
                "The function parseF reads zero as a zero block and one followed by zero as "
                + "a oneZero block. It stops immediately at two consecutive ones and returns "
                + "the accumulated blocks with the untouched suffix. Empty input and a lone "
                + "one fail because they contain no complete delimiter.")),
            Describe.Lean(
                DescribeId.Create("positive-word-first-delimiter"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/FibonacciFirstDelimiter.positive_word_first_delimiter"),
                H("Every positive canonical word has its exact first-delimiter parse"),
                StatementSource.FromAuthor(DelimiterFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here append is list concatenation, some denotes a successful optional "
                        + "result, and transient specifies the final one in the expansion. "
                        + "The suffix is any binary list, including a list beginning with two ones.")),
                    Paragraph(Text(
                        "Canonicality separates occupied indices. Induction on the remaining "
                        + "display length constructs zero or oneZero blocks until the highest "
                        + "occupied bit, which supplies the transient terminal one. A second "
                        + "induction checks that the parser consumes exactly these blocks and "
                        + "the extra terminal one. Injectivity of expansion gives uniqueness.")),
                    Paragraph(Text(
                        "For the number one there are no return blocks: its data word is a "
                        + "single one and its completed message consists of two ones. Positivity "
                        + "excludes the zero word, whose highest displayed bit is zero."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S0/Automata/BinaryZeckendorfBlockSkeletonCore")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Digit/ZeckendorfResidueTransducer")),
        ]));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula DelimiterFormula()
    {
        Formula natural = F.Id("n");
        Formula suffix = F.Id("suffix");
        Formula blocks = F.Id("blocks");
        Formula word = Call("zeckendorfLSDWord", Call("wdigits", natural));
        Formula terminal = F.Id("transient");
        Formula extraOne = Seq(OpenBracket, D(1), CloseBracket);
        Formula completed = Call("append", Call("append", word, extraOne), suffix);
        Formula pair = Seq(Open, blocks, Comma, Sp, suffix, Close);

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, natural, Sp, InMacro, Sp,
                Seq(Mathbb, Grp(F.Id("N"))), Comma),
            Seq(D(0), Sp, Lt, Sp, natural, Sp, Implies, Sp,
                Forall, Sp, suffix, Sp, InMacro, Sp,
                Call("List", Call("Fin", D(2))), Comma),
            Seq(Exists, Bang, Sp, blocks, Sp, InMacro, Sp,
                Call("List", F.Id("ReturnBlock")), Comma),
            Seq(word, Sp, Eq, Sp, Call("expand", blocks, terminal), Sp, Land),
            Seq(Call("parseF", completed), Sp, Eq, Sp, Call("some", pair), Dot),
        ]));
    }
}
