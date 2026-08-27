using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class ResponseCompletenessCardinalityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Budget/ResponseCompletenessCardinality."
            + "response_complete_card_lower_bound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Response completeness forces enough protocol response classes for every table.",
        H("Response-Completeness Cardinality Bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("response-completeness-cardinality"),
            DeclarationHandle.Create(Declaration),
            H("Complete response columns satisfy the finite counting bound"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The evaluation channel sends each protocol to its complete response "
                        + "column on X. Response completeness makes this map surjective onto "
                        + "all Lambda-valued response tables.")),
                Paragraph(Text(
                    "The equality-kernel quotient is canonically equivalent to the realized "
                        + "range, so it has at least card(Lambda)^card(X) classes. The proof "
                        + "uses the kernel quotient itself rather than choosing representatives.")),
                Paragraph(Text(
                    "The source assumes card(X) at least one and card(Lambda) at least two. "
                        + "Neither numerical bound is needed for this counting implication, "
                        + "so the machine theorem also covers empty or singleton carriers."))),
            DescribeRole.Theorem))));

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

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula protocolType = F.Id("P");
        Formula responseType = F.Id("Lambda");
        Formula type = F.Id("Type");
        Formula evaluation = F.Id("e");
        Formula table = F.Id("f");
        Formula protocol = F.Id("p");
        Formula state = F.Id("x");

        Formula responseComplete = Seq(
            Forall, Sp, table, Colon, Sp,
            Arrow(stateType, responseType), Comma, Sp,
            Exists, Sp, protocol, Colon, Sp, protocolType, Comma, Sp,
            Forall, Sp, state, Colon, Sp, stateType, Comma, Sp,
            Call("e", state, protocol), Sp, Eq, Sp, Call("f", state));
        Formula protocolBehavior = Lambda(protocol,
            Lambda(state, Call("e", state, protocol)));
        Formula quotient = Call("Quotient", Call("ker", protocolBehavior));
        Formula tableCount = new Formula.Power(
            Call("card", responseType), Call("card", stateType));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, protocolType, Comma, Sp,
            responseType, Colon, Sp, type, Comma, RowBreak, Grp(),
            Call("Fintype", stateType), Comma, Sp,
            Call("Fintype", responseType), Comma, RowBreak, Grp(),
            evaluation, Colon, Sp,
            Arrow(stateType, Arrow(protocolType, responseType)), Comma,
            RowBreak, Grp(),
            Grp(responseComplete), Sp, Rightarrow, RowBreak, Grp(),
            tableCount, Sp, Leq, Sp, Call("card", quotient), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
