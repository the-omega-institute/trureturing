using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class FiniteInternalProtocolNoGoDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite internal protocol indexing cannot realize every response table.",
        H("Finite Internal Protocol Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-internal-protocol-no-go"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Budget/FiniteInternalProtocolNoGo."
                        + "finite_internal_protocol_no_go"),
                H("Finite internal protocol indexing is not response complete"),
                StatementSource.FromAuthor(ObstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The evaluation channel sends each protocol to its complete response "
                            + "table on the state carrier. Response completeness would make this "
                            + "map surjective onto all Lambda-valued tables.")),
                    Paragraph(Text(
                        "There are card(Lambda)^card(X) such tables. With at least two responses "
                            + "this is strictly larger than card(X), while internal indexing "
                            + "allows at most card(X) protocols, contradicting surjectivity.")),
                    Paragraph(Text(
                        "The source assumes a nonempty state carrier. The machine theorem is "
                            + "stronger and also proves the empty-carrier case, so that premise "
                            + "is not needed."))),
                DescribeRole.Theorem))));

    private static Formula Type() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Card(Formula carrier) =>
        Call("card", carrier);

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula Fintype(Formula carrier) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, carrier, CloseBracket);

    private static Formula ObstructionFormula()
    {
        Formula state = F.Id("X");
        Formula protocol = F.Id("P");
        Formula response = F.Id("Lambda");
        Formula evaluation = F.Id("e");
        Formula table = F.Id("f");
        Formula selected = F.Id("p");
        Formula point = F.Id("x");
        Formula responseComplete = Seq(
            Forall, Sp, table, Colon, Sp, state, Sp, To, Sp, response, Comma, Sp,
            Exists, Sp, selected, Colon, Sp, protocol, Comma, Sp,
            Forall, Sp, point, Colon, Sp, state, Comma, Sp,
            Call("e", point, selected), Sp, Eq, Sp, Call("f", point));
        Formula power = Power(Card(response), Card(state));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, protocol, Comma, Sp, response,
            Colon, Sp, Type(), Comma, RowBreak, Grp(),
            Fintype(state), Sp, Fintype(protocol), Sp, Fintype(response), Comma,
            RowBreak, Grp(),
            evaluation, Colon, Sp, state, Sp, To, Sp, protocol, Sp, To, Sp, response,
            Comma, RowBreak, Grp(),
            Open, D(2), Sp, Leq, Sp, Card(response), Sp, Land, Sp,
            Card(protocol), Sp, Leq, Sp, Card(state), Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Open, Card(state), Sp, Lt, Sp, power, Close,
            Sp, Land, RowBreak, Grp(),
            Neg, Open, responseComplete, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
