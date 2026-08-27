using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.RefinementClosure;

internal sealed class PredictiveCompletionMaximalInvariantQuotientDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ObserverMemory/RefinementClosure/PredictiveCompletionMaximalInvariantQuotient."
            + "predictive_completion_maximal_invariant_quotient";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The maximal invariant future kernel carries the canonical predictive quotient.",
        H("Predictive Completion as a Maximal Invariant Quotient"),
        Blocks(Describe.Lean(
            DescribeId.Create("predictive-completion-maximal-invariant-quotient"),
            DeclarationHandle.Create(Declaration),
            H("The complete-future kernel yields the coarsest predictive refinement"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The completed kernel is the equality kernel of the canonical complete "
                        + "itinerary. The projection is the canonical map to its kernel quotient, "
                        + "and the statement explicitly identifies the projection kernel with the "
                        + "completed kernel.")),
                Paragraph(Text(
                    "The completed kernel is the greatest fixed point of one-step refinement. It "
                        + "lies inside the current readout kernel, is forward invariant, and "
                        + "contains every relation satisfying those two conditions.")),
                Paragraph(Text(
                    "The quotient itself is public: both the current readout and source update "
                        + "descend uniquely through its surjective canonical projection. The proof "
                        + "applies the frozen greatest-fixed-point theorem and pinned quotient "
                        + "exactness and surjectivity rules."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Define(Formula name, Formula value) =>
        Seq(name, Sp, Colon, Eq, Sp, value);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Pair(Formula left, Formula right) =>
        Seq(Open, left, Comma, Sp, right, Close);

    private static Formula InRelation(Formula pair, Formula relation) =>
        Seq(pair, Sp, InMacro, Sp, relation);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula state = F.Id("Y");
        Formula output = F.Id("O");
        Formula update = F.Id("tau");
        Formula readout = F.Id("q");
        Formula pair = F.Id("p");
        Formula relation = F.Id("R");
        Formula completedKernel = F.Id("Kinf");
        Formula projection = F.Id("piInf");
        Formula projectionKernel = F.Id("Kpi");
        Formula descendedReadout = F.Id("readoutBar");
        Formula descendedUpdate = F.Id("updateBar");
        Formula statePair = Seq(state, Sp, Times, Sp, state);
        Formula relationType = Call("Set", statePair);
        Formula completedState = Call("CompletedState", update, readout);
        Formula completedItinerary = Call("completeItinerary", update, readout);
        Formula currentKernel = Call("observationKernel", readout);
        Formula refinement = Call("refinementOperator", update, readout);
        Formula advancedPair = Pair(
            Apply(update, Call("fst", pair)), Apply(update, Call("snd", pair)));
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
        Formula uniqueReadout = Seq(
            Exists, Bang, Sp,
            Typed(descendedReadout, Arrow(completedState, output)), Comma, Sp,
            readout, Sp, Eq, Sp, descendedReadout, Sp, Circ, Sp, projection);
        Formula uniqueUpdate = Seq(
            Exists, Bang, Sp,
            Typed(descendedUpdate, Arrow(completedState, completedState)), Comma, Sp,
            projection, Sp, Circ, Sp, update, Sp, Eq, Sp,
            descendedUpdate, Sp, Circ, Sp, projection);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(Seq(state, Comma, Sp, output), type), Comma,
            RowBreak, Grp(),
            Typed(update, Arrow(state, state)), Comma, Sp,
            Typed(readout, Arrow(state, output)), Comma, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            Define(completedKernel, Call("ker", completedItinerary)), Comma,
            RowBreak, Grp(),
            Define(projection, Call("completionProjection", update, readout)), Comma,
            RowBreak, Grp(),
            Define(projectionKernel, Call("ker", projection)), RowBreak, Grp(),
            Operatorname, Grp(F.Id("in")), Sp,
            OpenBracket,
            projectionKernel, Sp, Eq, Sp, completedKernel, Sp, Land,
            RowBreak, Grp(),
            completedKernel, Sp, Eq, Sp, Call("gfp", refinement), Sp, Land,
            RowBreak, Grp(),
            completedKernel, Sp, Subseteq, Sp, currentKernel, Sp, Land,
            RowBreak, Grp(),
            Open, invariant, Close, Sp, Land, RowBreak, Grp(),
            Open, maximal, Close, Sp, Land, RowBreak, Grp(),
            Open, uniqueReadout, Close, Sp, Land, RowBreak, Grp(),
            uniqueUpdate,
            CloseBracket, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
