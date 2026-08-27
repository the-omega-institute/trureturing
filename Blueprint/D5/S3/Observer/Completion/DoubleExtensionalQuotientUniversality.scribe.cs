using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class DoubleExtensionalQuotientUniversalityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Completion/DoubleExtensionalQuotientUniversality."
            + "double_extensional_quotient_universal_minimality";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two-sided extensional quotient is uniquely equivalent to every extensional factorization.",
        H("Double Extensional Quotient Universality"),
        Blocks(Describe.Lean(
            DescribeId.Create("double-extensional-quotient-universal-minimality"),
            DeclarationHandle.Create(Declaration),
            H("The double extensional quotient is universally minimal"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The source evaluation supplies a behavior row for every state and a "
                        + "behavior column for every protocol. The two canonical quotient "
                        + "carriers are the equality kernels of those rows and columns.")),
                Paragraph(Text(
                    "A pair of surjections to extensional target carriers, together with the "
                        + "commuting evaluation square, induces a unique equivalence from each "
                        + "canonical quotient. The displayed equations expose the canonical maps "
                        + "and their action on every source state and protocol.")),
                Paragraph(Text(
                    "No exact dual quotient theorem was found in D5 or pinned Mathlib. The proof "
                        + "uses quotient lifting, representative induction, and Equiv.ofBijective "
                        + "directly on the source evaluation primitives."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

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

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula protocolType = F.Id("P");
        Formula outputType = F.Id("Lambda");
        Formula targetStateType = F.Id("XPrime");
        Formula targetProtocolType = F.Id("PPrime");
        Formula type = F.Id("Type");
        Formula evaluation = F.Id("e");
        Formula stateMap = F.Id("a");
        Formula protocolMap = F.Id("b");
        Formula targetEvaluation = F.Id("ePrime");
        Formula equivalences = F.Id("E");
        Formula state = F.Id("x");
        Formula protocol = F.Id("p");
        Formula firstState = F.Id("x");
        Formula secondState = F.Id("y");
        Formula firstProtocol = F.Id("p");
        Formula secondProtocol = F.Id("q");
        Formula targetStatePoint = F.Id("z");
        Formula quotientState = Call(
            "quotient", Call("ker", Call("stateBehavior", evaluation)));
        Formula quotientProtocol = Call(
            "quotient", Call("ker", Call("protocolBehavior", evaluation)));
        Formula pairType = Call(
            "Prod", Call("Equiv", quotientState, targetStateType),
            Call("Equiv", quotientProtocol, targetProtocolType));
        Formula stateRepresentative = Call(
            "quotientClass", Call("ker", Call("stateBehavior", evaluation)), state);
        Formula protocolRepresentative = Call(
            "quotientClass", Call("ker", Call("protocolBehavior", evaluation)), protocol);
        Formula factorization = Seq(
            Forall, Sp, Typed(state, stateType), Comma, Sp,
            Typed(protocol, protocolType), Comma, Sp,
            Apply(Apply(evaluation, state), protocol), Sp, Eq, Sp,
            Apply(Apply(targetEvaluation, Apply(stateMap, state)), Apply(protocolMap, protocol)));
        Formula stateExtensional = Seq(
            Forall, Sp, Typed(firstState, targetStateType), Comma, Sp,
            Typed(secondState, targetStateType), Comma, Sp,
            Open, Forall, Sp, Typed(protocol, targetProtocolType), Comma, Sp,
            Apply(Apply(targetEvaluation, firstState), protocol), Sp, Eq, Sp,
            Apply(Apply(targetEvaluation, secondState), protocol), Close,
            Sp, Rightarrow, Sp, firstState, Sp, Eq, Sp, secondState);
        Formula protocolExtensional = Seq(
            Forall, Sp, Typed(firstProtocol, targetProtocolType), Comma, Sp,
            Typed(secondProtocol, targetProtocolType), Comma, Sp,
            Open, Forall, Sp, Typed(targetStatePoint, targetStateType), Comma, Sp,
            Apply(Apply(targetEvaluation, targetStatePoint), firstProtocol), Sp, Eq, Sp,
            Apply(Apply(targetEvaluation, targetStatePoint), secondProtocol), Close,
            Sp, Rightarrow, Sp, firstProtocol, Sp, Eq, Sp, secondProtocol);
        Formula stateEquation = Seq(
            Forall, Sp, Typed(state, stateType), Comma, Sp,
            Apply(Call("fst", equivalences), stateRepresentative), Sp, Eq, Sp,
            Apply(stateMap, state));
        Formula protocolEquation = Seq(
            Forall, Sp, Typed(protocol, protocolType), Comma, Sp,
            Apply(Call("snd", equivalences), protocolRepresentative), Sp, Eq, Sp,
            Apply(protocolMap, protocol));
        Formula square = Seq(
            Forall, Sp, Typed(state, stateType), Comma, Sp,
            Typed(protocol, protocolType), Comma, Sp,
            Apply(Apply(evaluation, state), protocol), Sp, Eq, Sp,
            Apply(Apply(targetEvaluation,
                Apply(Call("fst", equivalences), stateRepresentative)),
                Apply(Call("snd", equivalences), protocolRepresentative)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, protocolType, Comma, Sp,
            outputType, Comma, Sp, targetStateType, Comma, Sp,
            targetProtocolType, Colon, Sp, type, Comma, RowBreak, Grp(),
            evaluation, Colon, Sp, stateType, Sp, To, Sp,
            Arrow(protocolType, outputType), Comma, Sp,
            stateMap, Colon, Sp, stateType, Sp, To, Sp, targetStateType, Comma, Sp,
            protocolMap, Colon, Sp, protocolType, Sp, To, Sp, targetProtocolType, Comma, Sp,
            targetEvaluation, Colon, Sp, targetStateType, Sp, To, Sp,
            Arrow(targetProtocolType, outputType), Comma, RowBreak, Grp(),
            Call("Surjective", stateMap), Comma, Sp,
            Call("Surjective", protocolMap), Comma, RowBreak, Grp(),
            factorization, Comma, RowBreak, Grp(),
            stateExtensional, Comma, RowBreak, Grp(),
            protocolExtensional, Sp, Rightarrow, RowBreak, Grp(),
            Exists, Bang, Sp, equivalences, Colon, Sp, pairType, Comma, RowBreak, Grp(),
            stateEquation, Sp, Land, Sp, protocolEquation, Sp, Land, Sp, square, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
