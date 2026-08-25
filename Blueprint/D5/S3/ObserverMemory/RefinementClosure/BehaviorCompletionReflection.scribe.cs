using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.RefinementClosure;

internal sealed class BehaviorCompletionReflectionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Behavior completion is left adjoint to the inclusion of stable interfaces.",
        H("Behavior Completion Reflection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("behavior-completion-reflection"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionReflection."
                        + "behavior_completion_reflection"),
                H("Behavior completion has the stable-interface reflection property"),
                StatementSource.FromAuthor(ReflectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F update a state space X. Let q and r be interfaces onto their "
                            + "effective codomains, and suppose r carries an induced update "
                            + "commuting with F.")),
                    Paragraph(Text(
                        "The behavior completion of q is the realized range of its full future "
                            + "itinerary. Refinement is stated by a unique factor map, matching "
                            + "the source interface order rather than hiding uniqueness in an "
                            + "auxiliary lemma.")),
                    Paragraph(Text(
                        "If completion factors through r, its time-zero readout factor composes "
                            + "with that map to factor q through r. Surjectivity of r proves the "
                            + "composite factor is unique.")),
                    Paragraph(Text(
                        "Conversely, the canonical behavior-completion minimality theorem sends "
                            + "any stable refinement of q uniquely onto the realized completion. "
                            + "Together the two implications are the reflection equivalence."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

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

    private static Formula ReflectionFormula()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("B");
        Formula stableType = F.Id("R");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula stable = F.Id("r");
        Formula induced = F.Id("G");
        Formula completionFactor = F.Id("Phi");
        Formula readoutFactor = Pi;
        Formula completion = Call("completeItinerary", update, readout);
        Formula completionRange = Call("ItineraryRange", update, readout);
        Formula completionProjection = Call("rangeFactorization", completion);
        Formula stablePremise = Seq(
            Call("Surjective", readout), Sp, Land, Sp,
            Call("Surjective", stable), Sp, Land,
            RowBreak, Grp(),
            Open, Exists, Sp,
            Typed(induced, Arrow(stableType, stableType)), Comma, Sp,
            stable, Sp, Circ, Sp, update, Sp, Eq, Sp,
            induced, Sp, Circ, Sp, stable, Close);
        Formula completionRefines = Seq(
            Exists, Bang, Sp,
            Typed(completionFactor, Arrow(stableType, completionRange)), Comma, Sp,
            completionProjection, Sp, Eq, Sp,
            completionFactor, Sp, Circ, Sp, stable);
        Formula readoutRefines = Seq(
            Exists, Bang, Sp,
            Typed(readoutFactor, Arrow(stableType, output)), Comma, Sp,
            readout, Sp, Eq, Sp, readoutFactor, Sp, Circ, Sp, stable);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Comma, Sp, stableType, Comma,
            RowBreak, Grp(),
            Typed(update, Arrow(state, state)), Comma, Sp,
            Typed(readout, Arrow(state, output)), Comma, Sp,
            Typed(stable, Arrow(state, stableType)), Comma,
            RowBreak, Grp(), Open, stablePremise, Close, Sp, Rightarrow,
            RowBreak, Grp(),
            Open, completionRefines, Close, Sp, Iff, Sp,
            Open, readoutRefines, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
