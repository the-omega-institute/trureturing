using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Interventions;

internal sealed class ExperimentalQuotientUniversalityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Intervention traces have the canonical empirical quotient universal property.",
        H("Experimental Quotient Universality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("experimental-quotient-universality"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Interventions/"
                        + "ExperimentalQuotientUniversality."
                        + "experimental_quotient_universality"),
                H("The experimental quotient has the universal property"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A protocol is a finite action list. Its trace is constructed from the "
                            + "intervention channel and public readout by recording the initial "
                            + "observation and every successive post-intervention observation.")),
                    Paragraph(Text(
                        "The quotient and class map are the canonical objects imported from the "
                            + "empirical-identifiability family, instantiated with that trace "
                            + "readout rather than redefined for this theorem.")),
                    Paragraph(Text(
                        "Every trace coordinate has a unique quotient factor. Independently, an "
                            + "arbitrary target has a unique quotient factor when it is constant "
                            + "on states with all the same traces.")),
                    Paragraph(Text(
                        "Both clauses apply the existing unique-descent theorem directly. The "
                            + "converse constancy premise is local to the target clause."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
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

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Compose(Formula left, Formula right) =>
        Seq(left, Sp, Circ, Sp, right);

    private static Formula TheoremFormula()
    {
        Formula actionType = F.Id("A");
        Formula stateType = F.Id("X");
        Formula observationType = F.Id("B");
        Formula targetType = F.Id("Y");
        Formula intervene = F.Id("F");
        Formula observe = F.Id("O");
        Formula target = F.Id("T");
        Formula actions = F.Id("alpha");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula trace = Apply(F.Id("experimentTrace"), intervene, observe);
        Formula quotient = Apply(F.Id("EmpiricalQuotient"), trace);
        Formula classMap = Apply(F.Id("empiricalClass"), trace);
        Formula traceAtActions = Apply(trace, actions);
        Formula protocolDescend = new Formula.Subscript(F.Id("d"), actions);
        Formula targetDescend = new Formula.Subscript(F.Id("d"), target);
        Formula actionList = Apply(F.Id("List"), actionType);
        Formula observationList = Apply(F.Id("List"), observationType);
        Formula sameTraces = Seq(
            Forall, Sp, actions, Colon, Sp, actionList, Comma, Sp,
            Apply(trace, actions, x), Sp, Eq, Sp, Apply(trace, actions, y));
        Formula targetConstant = Seq(
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, stateType, Comma, Sp,
            Open, sameTraces, Close, Sp, Rightarrow, Sp,
            Apply(target, x), Sp, Eq, Sp, Apply(target, y));
        Formula everyProtocolDescends = Seq(
            Forall, Sp, actions, Colon, Sp, actionList, Comma, Sp,
            Exists, Bang, Sp, protocolDescend, Colon, Sp,
            Arrow(quotient, observationList), Comma, Sp,
            traceAtActions, Sp, Eq, Sp, Compose(protocolDescend, classMap));
        Formula everyConstantTargetDescends = Seq(
            Open, targetConstant, Close, Sp, Rightarrow, Sp,
            Exists, Bang, Sp, targetDescend, Colon, Sp,
            Arrow(quotient, targetType), Comma, Sp,
            target, Sp, Eq, Sp, Compose(targetDescend, classMap));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, actionType, Comma, Sp, stateType, Comma, Sp,
            observationType, Comma, Sp, targetType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            intervene, Colon, Sp, actionType, Sp, To, Sp, stateType, Sp, To, Sp,
            stateType, Comma, Sp,
            observe, Colon, Sp, stateType, Sp, To, Sp, observationType, Comma, Sp,
            target, Colon, Sp, stateType, Sp, To, Sp, targetType, Comma,
            RowBreak, Grp(),
            OpenBracket, everyProtocolDescends, RowBreak, Grp(),
            Land, Sp, Open, everyConstantTargetDescends, Close, CloseBracket, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
