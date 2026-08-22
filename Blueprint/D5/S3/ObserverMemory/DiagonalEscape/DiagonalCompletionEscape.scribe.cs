using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.DiagonalEscape;

internal sealed class DiagonalCompletionEscapeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary finite prefixes admit a compatible diagonal escape sequence.",
        H("Diagonal Completion Escape"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("diagonal-completion-escape"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/DiagonalEscape/DiagonalCompletionEscape"
                        + ".diagonal_completion_escape"),
                H("Diagonal escape through compatible binary prefixes"),
                StatementSource.FromAuthor(DiagonalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At stage n, the binary word is a function on Fin n. The restriction "
                            + "channel from stage j to stage i forgets coordinates after i, and "
                            + "the prefix probe reads the first n entries of an infinite Boolean "
                            + "sequence.")),
                    Paragraph(Text(
                        "For any proposed enumeration of Boolean sequences, choose the diagonal "
                            + "entry to be false when the enumerated sequence is true at its own "
                            + "coordinate, and true otherwise. The canonical completion map then "
                            + "packages its finite prefixes as a CompatibleStageFamily.")),
                    Paragraph(Text(
                        "The resulting section satisfies every restriction equation and differs "
                            + "from the sequence at its self-coordinate for every enumeration "
                            + "index. The construction uses the source binary stages and channels "
                            + "rather than defining an object from the desired conclusion."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula DiagonalFormula()
    {
        Formula n = F.Id("n");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula h = F.Id("h");
        Formula diagonal = F.Id("d");
        Formula enumeration = F.Id("x");
        Formula section = F.Id("s");
        Formula prefix = F.Id("P");
        Formula restrict = F.Id("r");
        Formula familyType = Call("CompatibleStageFamily", F.Id("S"));
        Formula complement = Apply(diagonal, n);
        Formula enumeratedSelf = Apply(Apply(enumeration, n), n);
        Formula prefixAt = Apply(Apply(prefix, n), diagonal);
        Formula sectionAt = Seq(section, Underscore, Grp(n));
        Formula restrictionAt = Call("restrict", h);

        Formula diagonalClause = Seq(
            Forall, Sp, n, Comma, Sp,
            complement, Sp, Eq, Sp,
            Grp(Seq(F.Id("if"), Open, enumeratedSelf, Close, Sp,
                F.Id("then"), Sp, F.Id("false"), Sp,
                F.Id("else"), Sp, F.Id("true"))));

        Formula sectionClause = Seq(
            Forall, Sp, n, Comma, Sp, sectionAt, Sp, Eq, Sp, prefixAt);

        Formula compatibilityClause = Seq(
            Forall, Sp, i, Comma, Sp, j, Comma, Sp,
            h, Sp, Colon, Sp, i, Sp, Leq, Sp, j, Comma, Sp,
            Apply(restrictionAt, Apply(Apply(prefix, j), diagonal)),
            Sp, Eq, Sp, Apply(Apply(prefix, i), diagonal));

        Formula escapeClause = Seq(
            Forall, Sp, n, Comma, Sp,
            diagonal, Sp, Neq, Sp, Apply(enumeration, n));

        Formula sequenceType = Seq(F.Id("Nat"), Sp, To, Sp,
            F.Id("Nat"), Sp, To, Sp, F.Id("Bool"));

        return Disp(Seq(
            Forall, Sp, enumeration, Colon, Sp, sequenceType, Comma, Sp,
            Open,
            Exists, Sp, diagonal, Colon, Sp, F.Id("Nat"), Sp, To, Sp,
            F.Id("Bool"), Comma, Sp,
            Exists, Sp, section, Colon, Sp, familyType, Comma, Sp,
            Open, diagonalClause, Sp, Land, Sp,
            sectionClause, Sp, Land, Sp,
            compatibilityClause, Sp, Land, Sp,
            escapeClause, Close, Close, Dot));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
