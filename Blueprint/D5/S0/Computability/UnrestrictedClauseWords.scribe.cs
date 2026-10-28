using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class UnrestrictedClauseWordsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original binary-name CNF encoding has an unrestricted total decoder and a "
            + "fixed finite parser with a linear transition bound.",
        H("Unrestricted Original Clause Words"),
        Blocks(
            Paragraph(Text(
                "A formula is an ordered list of clauses over the original Boolean-name "
                + "literals. A canonical name is a nonempty most significant bit first "
                + "binary spelling beginning in one. Its bits are escaped as one-bit pairs "
                + "and terminated by zero. Literal tags, polarity, clause delimiters, and "
                + "the final two zeros are exactly those of Conventional.formulaWord. "
                + "There is no variable-universe header and no numerical bound on a name.")),
            Describe.Lean(
                DescribeId.Create("original-word-codec"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/UnrestrictedClauseWords.word_codec"),
                H("Exact unrestricted decoding and malformed rejection"),
                StatementSource.FromAuthor(CodecStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every raw word and formula, decoding returns that formula "
                        + "exactly when all its names are canonical and the raw word is "
                        + "its original encoding. This gives both the encoded roundtrip "
                        + "and rejection of every word outside the canonical encoded range.")),
                    Paragraph(Text(
                        "Clause widths are arbitrary finite lengths. The cursor appends "
                        + "the original signed literals in order, preserving repeated "
                        + "clauses, repeated names, and tautologies. The empty conjunction "
                        + "and empty clauses retain their original encodings and semantics. "
                        + "The decoder never constructs a replacement variable dictionary.")),
                    Paragraph(Text(
                        "The proof reconstructs the exact consumed prefix at every live "
                        + "cursor transition and preserves canonical names. Induction on "
                        + "name bits, literals, and clauses proves that each original "
                        + "encoding reaches its corresponding completed cursor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-unrestricted-parser"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/UnrestrictedClauseWords.parser_run"),
                H("Actual finite parsing in linear charged time"),
                StatementSource.FromAuthor(ParserStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The parser is a fixed FinTM2 with Boolean stack alphabets and "
                        + "finite labels and control. Erasing the mathematical cursor's "
                        + "unbounded buffers leaves exactly its lexical control. No clause "
                        + "width counter is installed. Each input bit is read and saved by "
                        + "one actual transition; the machine then copies an accepted word "
                        + "or clears a rejected word before writing its result flag.")),
                    Paragraph(Text(
                        "For every raw word of length L, execution reaches the standard "
                        + "halt configuration in at most two times L plus three transitions. "
                        + "Rejection returns the singleton false. Success returns true "
                        + "followed by the unchanged original encoding of the decoded "
                        + "formula. All scratch stacks are empty and finite control is "
                        + "reset. Missing names, noncanonical leading bits, malformed "
                        + "delimiters, truncation, and trailing symbols all reject.")),
                    Paragraph(Text(
                        "This theorem supplies syntax validation and a typed encoded "
                        + "result. Construction and execution of a literal evaluation "
                        + "graph require separate mathematical statements."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Computability/ConventionalClauseWords"))]));
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula CodecStatement()
    {
        var w = Id("w");
        var formula = Id("F");
        var law = new Formula.Logic(
            Equal(Call("readWord", w), Call("some", formula)),
            FormulaLogicOperator.Iff,
            new Formula.Logic(Call("Canonical", formula), FormulaLogicOperator.And,
                Equal(w, Call("formulaWord", formula))));
        return All("w", Call("List", Id("Bool")), All("F", Id("Formula"), law));
    }

    private static Formula ParserStatement()
    {
        var w = Id("w");
        var result = Call("some", Call("resultWord", Call("readWord", w)));
        var bound = Add(Multiply(Num(2), Call("length", w)), Num(3));
        var law = Call("Nonempty", Call("TM2OutputsInTime", Id("parser"), w, result, bound));
        return All("w", Call("List", Id("Bool")), law);
    }

}
