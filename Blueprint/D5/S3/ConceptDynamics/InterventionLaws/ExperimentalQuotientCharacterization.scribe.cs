using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InterventionLaws;

internal sealed class ExperimentalQuotientCharacterizationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Experimental targets are exactly functions on the empirical quotient.",
        H("Experimental Quotient Characterization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("experimental-quotient-characterization"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/InterventionLaws/"
                        + "ExperimentalQuotientCharacterization."
                        + "experimental_quotient_characterization"),
                H("Experimental targets are quotient functions"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The protocol trace is the existing recursive trajectory constructed "
                            + "from the intervention channel and public readout. The quotient "
                            + "and class map are the canonical empirical objects for that trace.")),
                    Paragraph(Text(
                        "Every trace coordinate has a unique quotient factor. For an arbitrary "
                            + "target, unique factorization is equivalent to constancy on states "
                            + "with every trace equal.")),
                    Paragraph(Text(
                        "The final public clause is the converse obstruction: two states with all "
                            + "traces equal but different target values rule out every quotient "
                            + "factor for that target."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.AddRange([Comma, Sp]);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Compose(Formula left, Formula right) =>
        Seq(left, Sp, Circ, Sp, right);

    private static Formula TheoremFormula()
    {
        Formula action = F.Id("A");
        Formula state = F.Id("X");
        Formula observation = F.Id("B");
        Formula targetType = F.Id("Y");
        Formula intervene = F.Id("F");
        Formula observe = F.Id("O");
        Formula target = F.Id("T");
        Formula actions = F.Id("a");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula descend = F.Id("d");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula actionList = Call("List", action);
        Formula observationList = Call("List", observation);
        Formula trace = Call("experimentTrace", intervene, observe);
        Formula quotient = Call("EmpiricalQuotient", trace);
        Formula classMap = Call("empiricalClass", trace);
        Formula traceAt = Apply(trace, actions);
        Formula protocolDescend = new Formula.Subscript(descend, actions);
        Formula targetDescend = new Formula.Subscript(descend, target);

        Formula allTracesEqual = Seq(
            Forall, Sp, Typed(actions, actionList), Comma, Sp,
            Apply(trace, actions, x), Sp, Eq, Sp, Apply(trace, actions, y));
        Formula targetConstant = Seq(
            Forall, Sp, Typed(x, state), Comma, Sp, Typed(y, state), Comma, Sp,
            Open, allTracesEqual, Close, Sp, Rightarrow, Sp,
            Apply(target, x), Sp, Eq, Sp, Apply(target, y));
        Formula traceFactor = Seq(
            Forall, Sp, Typed(actions, actionList), Comma, Sp,
            Exists, Bang, Sp,
            Typed(protocolDescend, Arrow(quotient, observationList)), Comma, Sp,
            traceAt, Sp, Eq, Sp, Compose(protocolDescend, classMap));
        Formula targetFactor = Seq(
            Exists, Bang, Sp,
            Typed(targetDescend, Arrow(quotient, targetType)), Comma, Sp,
            target, Sp, Eq, Sp, Compose(targetDescend, classMap));
        Formula varyingPair = Seq(
            Exists, Sp, Typed(x, state), Comma, Sp, Typed(y, state), Comma, Sp,
            Open, allTracesEqual, Close, Sp, Land, Sp,
            Apply(target, x), Sp, Neq, Sp, Apply(target, y));
        Formula noTargetFactor = Seq(
            Neg, Sp, Exists, Sp,
            Typed(descend, Arrow(quotient, targetType)), Comma, Sp,
            target, Sp, Eq, Sp, Compose(descend, classMap));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(action, type), Comma, Sp, Typed(state, type),
                Comma, Sp, Typed(observation, type), Comma, Sp,
                Typed(targetType, type), Comma),
            Seq(
                Typed(intervene, Arrow(action, Arrow(state, state))), Comma, Sp,
                Typed(observe, Arrow(state, observation)), Comma, Sp,
                Typed(target, Arrow(state, targetType)), Comma),
            Seq(Open, traceFactor, Close, Sp, Land),
            Seq(
                Grp(), OpenBracket, Open, targetFactor, Sp, Iff, Sp,
                targetConstant, Close, Sp, Land),
            Seq(
                Open, Open, varyingPair, Close, Sp, Rightarrow, Sp,
                noTargetFactor, Close, CloseBracket, Dot),
        ]));
    }
}
