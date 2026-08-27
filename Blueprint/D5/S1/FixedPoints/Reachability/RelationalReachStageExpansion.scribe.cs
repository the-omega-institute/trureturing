using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.FixedPoints.Reachability;

internal sealed class RelationalReachStageExpansionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A relation-generated reachability operator expands from the empty and initial "
            + "stages through every finite successor stage.",
        H("Relational Reach Stage Expansion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("relational-reachability-initial-and-successor-stages"),
                DeclarationHandle.Create(
                    "D5/S1/FixedPoints/Reachability/RelationalReachStageExpansion."
                        + "finite_step_expansion_with_initial_stages"),
                H("Relational reachability expands through all finite stages"),
                StatementSource.FromAuthor(ReachExpansionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The transition relation R and initial set I0 construct the canonical "
                            + "operator Phi(S) = I0 union image_R(S). No reachability object is "
                            + "defined by the conclusion it is meant to satisfy.")),
                    Paragraph(Text(
                        "The frozen finite-step theorem supplies arbitrary-union preservation "
                            + "and identifies the least fixed point with the union of all finite "
                            + "iterates from the empty set.")),
                    Paragraph(Text(
                        "The restored public clauses expose the zeroth and first iterates and "
                            + "the successor recurrence. Thus every later stage keeps I0 and "
                            + "adds one further direct relational image.")),
                    Paragraph(Text(
                        "Repository body-shape search found the canonical reachStep primitive "
                            + "and no existing public theorem carrying all restored stage clauses. "
                            + "Pinned Mathlib's iterate identities discharge those clauses."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S1/FixedPoints/RelationalReachExpansion"))]));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula RelationImage(Formula relation, Formula states) =>
        Seq(Operatorname, Grp(F.Id("image")), Underscore, Grp(relation),
            Open, states, Close);

    private static Formula ReachOperator(
        Formula initial, Formula relation, Formula argument) =>
        Seq(initial, Sp, UnionSymbol(), Sp, RelationImage(relation, argument));

    private static Formula Iterate(
        Formula reachOperator, Formula exponent, Formula argument) =>
        Seq(
            reachOperator, Caret, Grp(OpenBracket, exponent, CloseBracket),
            Open, argument, Close);

    private static Formula ReachExpansionFormula()
    {
        Formula state = F.Id("X");
        Formula index = F.Id("J");
        Formula relation = F.Id("R");
        Formula initial = Seq(F.Id("I"), Underscore, Grp(D(0)));
        Formula family = F.Id("A");
        Formula i = F.Id("i");
        Formula n = F.Id("n");
        Formula argument = F.Id("S");
        Formula powerset = Call("Set", state);
        Formula relationType = Call("Set", Seq(state, Sp, Times, Sp, state));
        Formula familyUnion = Seq(
            UnionSymbol(), Underscore, Grp(i, InMacro, Sp, index), Sp,
            Apply(family, i));
        Formula reachOperator = Seq(
            Open, argument, Sp, Mapsto, Sp,
            ReachOperator(initial, relation, argument), Close);
        Formula zeroStage = Iterate(reachOperator, D(0), Emptyset);
        Formula oneStage = Iterate(reachOperator, D(1), Emptyset);
        Formula nthStage = Iterate(reachOperator, n, Emptyset);
        Formula successorStage = Iterate(
            reachOperator, Seq(n, Sp, Plus, Sp, D(1)), Emptyset);

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, index, Colon, Sp, F.Id("Type"), Comma,
            RowBreak, Grp(), relation, Colon, Sp, relationType, Comma, Sp,
            initial, Colon, Sp, powerset, Comma, Sp,
            family, Colon, Sp, index, Sp, To, Sp, powerset, Comma,
            RowBreak, Grp(),
            RelationImage(relation, familyUnion), Sp, Eq, Sp,
            UnionSymbol(), Underscore, Grp(i, InMacro, Sp, index), Sp,
            RelationImage(relation, Apply(family, i)), Sp, Land,
            RowBreak, Grp(),
            Call("lfp", reachOperator), Sp, Eq, Sp,
            UnionSymbol(), Underscore, Grp(n, InMacro, Sp, Mathbb, Grp(F.Id("N"))),
            Sp, nthStage, Sp, Land,
            RowBreak, Grp(), zeroStage, Sp, Eq, Sp, Emptyset, Sp, Land,
            RowBreak, Grp(), oneStage, Sp, Eq, Sp, initial, Sp, Land,
            RowBreak, Grp(), Forall, Sp, n, InMacro, Sp, Mathbb, Grp(F.Id("N")),
            Comma, Sp, successorStage, Sp, Eq, Sp,
            ReachOperator(initial, relation, nthStage), Dot));
    }

    private static Formula UnionSymbol() =>
        Seq(Operatorname, Grp(F.Id("union")));
}
