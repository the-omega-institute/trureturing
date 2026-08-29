using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Agency.Holonomy;

internal sealed class MemoryTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Agency/Holonomy/MemoryTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sequential memory transport along concatenated action words composes.",
        H("Memory Transport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("transport-along-concatenated-words-composes"),
                DeclarationHandle.Create(Prefix + "transportWord_append"),
                H("Transport along concatenated words composes"),
                StatementSource.FromAuthor(AppendStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A transport word is a finite list of memory endomorphisms executed from "
                            + "left to right.")),
                    Paragraph(Text(
                        "Executing first ++ second at a memory state equals executing first and "
                            + "then executing second from the resulting memory."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-empty-word-has-trivial-transport"),
                DeclarationHandle.Create(Prefix + "transportWord_nil"),
                H("The empty word has trivial transport"),
                StatementSource.FromAuthor(EmptyStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The empty update list performs no memory transformation.")),
                    Paragraph(Text(
                        "Its transport therefore returns every input memory state unchanged."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula WordType() =>
        Call("List", Grp(Arrow(F.Id("M"), F.Id("M"))));

    private static Formula AppendStatement()
    {
        Formula first = F.Id("first");
        Formula second = F.Id("second");
        Formula memory = F.Id("m");
        return Disp(Seq(
            Forall, Sp, first, Comma, Sp, second, Colon, Sp, WordType(), Comma, Sp,
            memory, Colon, Sp, F.Id("M"), Comma, Sp,
            Call("transportWord", Seq(first, Sp, Plus, Plus, Sp, second), memory),
            Sp, Eq, Sp,
            Call("transportWord", second, Call("transportWord", first, memory)), Dot));
    }

    private static Formula EmptyStatement()
    {
        Formula memory = F.Id("m");
        return Disp(Seq(
            Forall, Sp, memory, Colon, Sp, F.Id("M"), Comma, Sp,
            Call("transportWord", Seq(OpenBracket, CloseBracket), memory),
            Sp, Eq, Sp, memory, Dot));
    }
}
