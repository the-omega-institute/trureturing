using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.RefinementClosure;

internal sealed class CompletionKernelGreatestFixedPointDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ObserverMemory/RefinementClosure/CompletionKernelGreatestFixedPoint."
            + "completion_kernel_is_greatest_fixed_point";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The completed observation kernel is the greatest forward-invariant kernel relation.",
        H("Completion Kernel Greatest Fixed Point"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("completion-kernel-is-greatest-fixed-point"),
                DeclarationHandle.Create(Declaration),
                H("The completion kernel is the greatest fixed point"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an update tau and readout q, the completed kernel relates states "
                            + "whose canonical complete itineraries agree.")),
                    Paragraph(Text(
                        "The one-step refinement operator intersects the current observation "
                            + "kernel with the pullback of a candidate relation through tau.")),
                    Paragraph(Text(
                        "The completed kernel is its greatest fixed point. The public statement "
                            + "also exposes containment in the current kernel, forward "
                            + "invariance, and maximality among every relation with those two "
                            + "properties."))),
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

    private static Formula Pair(Formula left, Formula right) =>
        Seq(Open, left, Comma, Sp, right, Close);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula InRelation(Formula pair, Formula relation) =>
        Seq(pair, Sp, InMacro, Sp, relation);

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula state = F.Id("Y");
        Formula output = F.Id("O");
        Formula update = Tau;
        Formula readout = F.Id("q");
        Formula pair = F.Id("p");
        Formula relation = F.Id("R");
        Formula statePair = Seq(state, Sp, Times, Sp, state);
        Formula relationType = Call("Set", statePair);
        Formula completedKernel = Call("ker", Call("completeItinerary", update, readout));
        Formula currentKernel = Call("observationKernel", readout);
        Formula refined = Call("refinementOperator", update, readout);
        Formula advancedPair = Pair(
            Apply(update, Call("fst", pair)),
            Apply(update, Call("snd", pair)));
        Formula invariant = Seq(
            Forall, Sp, Typed(pair, statePair), Comma, Sp,
            InRelation(pair, completedKernel), Sp, Rightarrow, Sp,
            InRelation(advancedPair, completedKernel));
        Formula candidateInvariant = Seq(
            Forall, Sp, Typed(pair, statePair), Comma, Sp,
            InRelation(pair, relation), Sp, Rightarrow, Sp,
            InRelation(advancedPair, relation));
        Formula maximal = Seq(
            Forall, Sp, Typed(relation, relationType), Comma, Sp,
            relation, Sp, Subseteq, Sp, currentKernel, Sp, Rightarrow, Sp,
            Open, candidateInvariant, Close, Sp, Rightarrow, Sp,
            relation, Sp, Subseteq, Sp, completedKernel);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(state, type), Comma, Sp, Typed(output, type), Comma,
            RowBreak, Grp(),
            Typed(update, Arrow(state, state)), Comma, Sp,
            Typed(readout, Arrow(state, output)), Comma,
            RowBreak, Grp(),
            completedKernel, Sp, Eq, Sp, Call("gfp", refined), Sp, Land,
            RowBreak, Grp(),
            completedKernel, Sp, Subseteq, Sp, currentKernel, Sp, Land,
            RowBreak, Grp(),
            Open, invariant, Close, Sp, Land,
            RowBreak, Grp(),
            maximal, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
