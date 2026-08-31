using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencySelf;

internal sealed class AgencySelfUniversalMinimalityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencySelf/AgencySelfUniversalMinimality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A sufficient history interface uniquely maps its effective image to the agency-self quotient.",
        H("Agency Self Universal Minimality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-sufficient-interface-has-a-unique-agency-self-factor"),
                DeclarationHandle.Create(Prefix + "agency_self_universal_minimality"),
                H("A sufficient interface has a unique agency-self factor"),
                StatementSource.FromAuthor(TheoremStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume the complete future-interaction profile is decoded from a history "
                            + "interface.")),
                    Paragraph(Text(
                        "The interface then induces a factor from its realized range to histories "
                            + "quotiented by equality of complete interaction profiles.")),
                    Paragraph(Text(
                        "The factor sends every realized interface value to the corresponding "
                            + "profile class and is unique with this property, including when the "
                            + "history type is empty."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula TheoremStatement()
    {
        Formula historyType = F.Id("H");
        Formula interventionType = F.Id("I");
        Formula interactionType = F.Id("O");
        Formula interfaceType = F.Id("R");
        Formula type = F.Id("Type");
        Formula profile = F.Id("Gamma");
        Formula historyInterface = F.Id("r");
        Formula decoder = F.Id("F");
        Formula factor = F.Id("rbar");
        Formula history = F.Id("h");
        Formula profileValue = Call("PMF", interactionType);
        Formula profileType = Arrow(
            historyType, Arrow(interventionType, profileValue));
        Formula quotientType = Call("Quotient", Call("ker", profile));
        Formula rangeType = Call("range", historyInterface);
        Formula factorization = Seq(
            Call("class", history), Sp, Eq, Sp,
            Call("rbar", Call("rangePoint", Call("r", history))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, historyType, Comma, Sp, interventionType, Comma, Sp,
            interactionType, Comma, Sp, interfaceType, Colon, Sp, type,
            Comma, RowBreak, Grp(),
            profile, Colon, Sp, profileType, Comma, Sp,
            historyInterface, Colon, Sp, Arrow(historyType, interfaceType),
            Comma, RowBreak, Grp(),
            decoder, Colon, Sp,
            Arrow(interfaceType, Arrow(interventionType, profileValue)),
            Comma, RowBreak, Grp(),
            profile, Sp, Eq, Sp, decoder, Sp, Circ, Sp, historyInterface,
            Sp, Rightarrow, RowBreak, Grp(),
            Exists, Bang, Sp, factor, Colon, Sp,
            Arrow(rangeType, quotientType), Comma, Sp,
            Forall, Sp, history, Colon, Sp, historyType, Comma, Sp,
            factorization, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
