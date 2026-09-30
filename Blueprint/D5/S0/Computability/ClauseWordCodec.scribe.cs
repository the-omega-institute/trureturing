using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class ClauseWordCodecDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Total decoding determines every raw clause and the exact physical query framing.",
        H("Raw Clause Word Codec"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("codec-exact"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/ClauseWordCodec.codec_exact"),
                H("Soundness, roundtrip and unique complete syntax"),
                StatementSource.FromAuthor(Presentation()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For either source or physical mode, an arbitrary Boolean word "
                        + "decodes to universe n and formula F exactly when it is the "
                        + "complete encoding of those raw clauses and each clause has "
                        + "at most three literals. The parser receives no decoding witness. "
                        + "It checks terminated unary indices against the parsed universe, "
                        + "and the physical mode checks each coefficient equals n plus one.")),
                    Paragraph(Text(
                        "Source words have the explicit unary universe, clause and literal "
                        + "tags, polarities and final delimiter. Physical words additionally "
                        + "have the fixed query prefix, beta and visible tokens, and one "
                        + "terminated coefficient per raw clause. Every bit is consumed. "
                        + "Empty formulas, empty clauses, zero variables, unused variables, "
                        + "repeated literals and tautologies retain their exact syntax.")),
                    Paragraph(Text(
                        "The recursive proof establishes soundness of every accepted "
                        + "literal and clause and completeness with fuel derived from "
                        + "the word length. A deterministic decoder makes accepted "
                        + "encodings unique. This result supplies the raw-word codec; "
                        + "the universal malformed finite-machine run, physical oracle "
                        + "relation and conventional counting transducers remain separate "
                        + "counting reduction obligations."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Computability/ClauseQueryPreprocessor"))]));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Presentation()
    {
        var p = Id("physical");
        var w = Id("w");
        var n = Id("n");
        var f = Id("F");
        var pair = new Formula.LatexSequence([
            new Formula.LatexMacro(FormulaLatexMacro.Langle),
            new Formula.LatexSpace(),
            new Formula.LatexWord(FormulaIdentifier.Create("n")),
            new Formula.LatexSymbol(FormulaLatexSymbol.Comma),
            new Formula.LatexWord(FormulaIdentifier.Create("F")),
            new Formula.LatexMacro(FormulaLatexMacro.Rangle)]);
        var parsed = Equal(Call("readWord", p, w), Call("some", pair));
        var width = All("c", f, new Formula.Relation(Call("length", Id("c")),
            FormulaRelationOperator.LessThanOrEqual, Num(3)));
        var encoded = new Formula.Logic(Equal(w, Call("encodeWord", p, f)),
            FormulaLogicOperator.And, width);
        return All("physical", Id("Bool"), All("w", Call("List", Id("Bool")),
            All("n", Id("Nat"), All("F", Call("UnaryFormula", n),
                new Formula.Logic(parsed, FormulaLogicOperator.Iff, encoded)))));
    }
}
