using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Refinement;

internal sealed class StateProtocolQuotientOrderCommutationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Refinement/StateProtocolQuotientOrderCommutation."
            + "state_protocol_quotient_order_commutes";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quotienting equal evaluation rows and columns commutes by canonical carrier equivalences.",
        H("State-Protocol Quotient Order Commutation"),
        Blocks(Describe.Lean(
            DescribeId.Create("state-protocol-quotient-order-commutes"),
            DeclarationHandle.Create(Declaration),
            H("The two quotient orders are canonically equivalent"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The state and protocol relations are constructed from equality of the "
                        + "evaluation rows and columns. Each second-stage relation tests the "
                        + "induced evaluation on every class of the first quotient.")),
                Paragraph(Text(
                    "The two comparison equivalences are the identity on representatives. "
                        + "Their displayed computation rules make both carrier isomorphisms "
                        + "canonical, while the final conjunct identifies the two descended "
                        + "evaluation maps under those equivalences."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("State");
        Formula protocolType = F.Id("Protocol");
        Formula valueType = F.Id("Value");
        Formula evaluation = F.Id("e");
        Formula state = F.Id("x");
        Formula protocol = F.Id("p");
        Formula stateClass = F.Id("xbar");
        Formula protocolClass = F.Id("pbar");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula evaluationType = Arrow(stateType, Arrow(protocolType, valueType));
        Formula rowKernel = Call("ker", evaluation);
        Formula columnKernel = Call("ker", Grp(
            Lambda, Sp, protocol, Comma, Sp,
            Lambda, Sp, state, Comma, Sp,
            Apply(evaluation, state, protocol)));
        Formula afterState = Call("protocolAfterStateSetoid", evaluation);
        Formula afterProtocol = Call("stateAfterProtocolSetoid", evaluation);
        Formula stateSourceClass = Call("QuotientMk", rowKernel, state);
        Formula stateTargetClass = Call("QuotientMk", afterProtocol, state);
        Formula protocolSourceClass = Call("QuotientMk", afterState, protocol);
        Formula protocolTargetClass = Call("QuotientMk", columnKernel, protocol);
        Formula stateRule = Seq(
            Forall, Sp, Typed(state, stateType), Comma, Sp,
            Apply(Call("stateOrderEquiv", evaluation), stateSourceClass),
            Sp, Eq, Sp, stateTargetClass);
        Formula protocolRule = Seq(
            Forall, Sp, Typed(protocol, protocolType), Comma, Sp,
            Apply(Call("protocolOrderEquiv", evaluation), protocolSourceClass),
            Sp, Eq, Sp, protocolTargetClass);
        Formula stateClassType = Call("Quotient", rowKernel);
        Formula protocolClassType = Call("Quotient", afterState);
        Formula evaluationRule = Seq(
            Forall, Sp, Typed(stateClass, stateClassType), Comma, Sp,
            Typed(protocolClass, protocolClassType), Comma, Sp,
            Call("stateFirstEvaluation", evaluation, stateClass, protocolClass),
            Sp, Eq, Sp,
            Call("protocolFirstEvaluation", evaluation,
                Apply(Call("stateOrderEquiv", evaluation), stateClass),
                Apply(Call("protocolOrderEquiv", evaluation), protocolClass)));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp,
                Typed(
                    Seq(stateType, Comma, Sp, protocolType, Comma, Sp, valueType),
                    type),
                Comma),
            Seq(
                Grp(), Forall, Sp, Typed(evaluation, evaluationType), Comma),
            Seq(Grp(), Open, stateRule, Close, Sp, Land),
            Seq(Grp(), Open, protocolRule, Close, Sp, Land),
            Seq(Grp(), Open, evaluationRule, Close, Dot),
        ]));
    }

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

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
}
