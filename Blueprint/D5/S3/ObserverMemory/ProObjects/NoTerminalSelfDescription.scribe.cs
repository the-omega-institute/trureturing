using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.ProObjects;

internal sealed class NoTerminalSelfDescriptionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A terminal pro-object stage cannot contain its twisted self-evaluation concept.",
        H("No Terminal Self-Description"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("no-terminal-self-description"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/ProObjects/NoTerminalSelfDescription."
                        + "no_terminal_self_description"),
                H("A twisted self-evaluation escapes every terminal-stage listing"),
                StatementSource.FromAuthor(StatementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be a cofiltered stage diagram and let stage i faithfully "
                            + "represent its whole pro-object through the displayed isomorphism "
                            + "with the constant object on X_i.")),
                    Paragraph(Text(
                        "A listing e assigns to every stage coordinate a same-typed concept "
                            + "from X_i to Y. Its self-evaluation is formed at x by evaluating "
                            + "the x-th listed concept at x and then applying tau.")),
                    Paragraph(Text(
                        "When tau has no fixed point, this explicit concept is outside the "
                            + "range of e. Thus the listing cannot contain every same-typed "
                            + "concept, even under the terminal faithful-stage claim.")),
                    Paragraph(Text(
                        "The exact repository theorem relative_diagonal_escape proves the range "
                            + "exclusion directly; the canonical pro-object constructions are "
                            + "imported rather than redeclared."))),
                DescribeRole.Theorem))));

    private static Formula StatementFormula()
    {
        Formula diagram = F.Id("X");
        Formula stage = Call("Stage", F.Id("X"), F.Id("i"));
        Formula output = F.Id("Y");
        Formula enumeration = F.Id("e");
        Formula twist = F.Id("tau");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula evaluation = Seq(
            twist, Open, enumeration, Open, x, Close, Open, x, Close, Close);

        return Disp(Seq(
            Forall, Sp, F.Id("J"), Comma, Sp, output, Comma, Esc,
            OpenBracket, Call("SmallCategory", F.Id("J")), CloseBracket,
            Comma, Sp,
            OpenBracket, Call("IsFiltered", F.Id("J")), CloseBracket,
            Comma, Esc,
            diagram, Colon, Sp, Call("Opposite", F.Id("J")), Sp, To, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            F.Id("i"), InMacro, Sp, Call("Opposite", F.Id("J")), Comma, Esc,
            Call("Presented", diagram), Sp, Equiv, Sp, Call("Const", stage),
            Sp, Implies, Sp, Forall, Sp,
            enumeration, Colon, Sp, stage, Sp, To, Sp,
            Open, stage, Sp, To, Sp, output, Close, Comma, Sp,
            twist, Colon, Sp, output, Sp, To, Sp, output, Comma, Esc,
            Open, Forall, Sp, y, Comma, Sp,
            twist, Open, y, Close, Sp, Neq, Sp, y, Close,
            Sp, Implies, Sp,
            Neg, Sp, Open,
            Open, x, Sp, Mapsto, Sp, evaluation, Close,
            Sp, InMacro, Sp, Call("range", enumeration), Close, Dot));
    }
}
