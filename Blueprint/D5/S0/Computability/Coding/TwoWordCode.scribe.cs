using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.Coding;

internal sealed class TwoWordCodeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two labelled words are uniquely decodable exactly when they do not commute.",
        H("Labelled Two-Word Unique Decoding"),
        Blocks(
            Paragraph(Text(
                "Fix any universe u and any alphabet alpha of type Type u. A message is a finite "
                + "list of Boolean labels. Replace false by a and true by b, then concatenate "
                + "the resulting words. The criterion characterizes injectivity on all finite "
                + "label lists; it assumes neither decidable equality nor finiteness, inhabitation, "
                + "or nonemptiness of the alphabet.")),
            Describe.Lean(
                DescribeId.Create("injective-iff-noncommuting"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Coding/TwoWordCode.injective_iff_noncommuting"),
                H("Exact labelled criterion"),
                StatementSource.FromAuthor(Criterion()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "In the formula choose(t,a,b) is b when t is true and a when t is false; "
                        + "flatMap performs this substitution followed by concatenation. The "
                        + "symbol ++ denotes list concatenation. Injective compares the label "
                        + "lists themselves, so the two labels remain distinct even when a = b.")),
                    Paragraph(Text(
                        "An empty codeword prevents injectivity: inserting its label changes the "
                        + "message without changing its encoding. Equal words also prevent it. "
                        + "All these cases commute and are included in the equivalence. "
                        + "Nonempty overlapping words are allowed; for example [false] and "
                        + "[false,true] satisfy the criterion although the first prefixes the second.")),
                    Paragraph(Text(
                        "If the words commute, the distinct label messages [false,true] and "
                        + "[true,false] have the same encoding. Conversely, descent on the sum "
                        + "of the word lengths removes a shorter nonempty prefix from the longer "
                        + "word. The reduced pair still fails to commute. The substitution "
                        + "false to [false], true to [false,true] transports decoding back to the "
                        + "original pair; its injectivity follows by reversal from prefix-free "
                        + "decoding. When neither word prefixes the other, the original pair is "
                        + "prefix-free and the same decoding theorem applies directly.")),
                    Paragraph(Text(
                        "This is a mathematical characterization of finite word encodings. It "
                        + "asserts no decoding complexity bound, physical implementation, or "
                        + "literature novelty."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Criterion()
    {
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula s = F.Id("s");
        Formula t = F.Id("t");
        Formula alpha = F.Id("alpha");
        Formula substitution = Parenthesized(Seq(
            t, Sp, Colon, Sp, Call("Bool"), Sp, Mapsto, Sp,
            Call("choose", t, a, b)));
        Formula encoding = Parenthesized(Seq(
            s, Sp, Colon, Sp, Call("List", Call("Bool")), Sp, Mapsto, Sp,
            Call("flatMap", s, substitution)));
        return Disp(Seq(
            Forall, Sp, F.Id("u"), Sp, Colon, Sp, Call("Level"), Comma, Sp,
            Forall, Sp, alpha, Sp, Colon, Sp, Call("Type", F.Id("u")), Comma, Sp,
            Forall, Sp, a, Sp, Colon, Sp, Call("List", alpha), Comma, Sp,
            Forall, Sp, b, Sp, Colon, Sp, Call("List", alpha), Comma, Sp,
            Call("Injective", encoding), Sp, Leftrightarrow, Sp,
            a, Sp, Plus, Plus, Sp, b, Sp, Neq, Sp,
            b, Sp, Plus, Plus, Sp, a, Dot));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
