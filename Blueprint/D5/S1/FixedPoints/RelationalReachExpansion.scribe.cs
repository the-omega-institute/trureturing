using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.FixedPoints;

internal sealed class RelationalReachExpansionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A transition relation's direct image preserves arbitrary unions, and its reachability "
        + "least fixed point is the union of all finite stages.",
        H("Relational Reachability Expansion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("relational-reachability-has-a-finite-stage-expansion"),
                DeclarationHandle.Create(
                    "D5/S1/FixedPoints/RelationalReachExpansion."
                    + "finite_step_expansion"),
                H("Relational reachability expands through finite stages"),
                StatementSource.FromAuthor(ReachExpansionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The transition relation is supplied as a set of state pairs. Its direct "
                            + "image sends a set of current states to all one-step successors. The "
                            + "first public conjunct states preservation of an arbitrary indexed "
                            + "union, including an empty family.")),
                    Paragraph(Text(
                        "The reachability operator is constructed from the source primitives as "
                            + "Phi(A) = I0 union image_R(A). Reachability is its independently "
                            + "defined least fixed point, rather than a name assigned to the target "
                            + "stage union.")),
                    Paragraph(Text(
                        "Mathlib's exact SetRel.image_iUnion theorem proves the first conjunct and "
                            + "makes the constructed operator omega-Scott-continuous. The frozen "
                            + "Kleene-stage theorem is then applied directly to obtain the second "
                            + "conjunct."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S1/FixedPoints/KleeneStageLimit"))]));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula RelationImage(Formula relation, Formula states) =>
        Seq(Operatorname, Grp(F.Id("image")), Underscore, Grp(relation),
            Open, states, Close);

    private static Formula ReachOperator(
        Formula initial, Formula relation, Formula argument) =>
        Seq(initial, Sp, UnionSymbol(), Sp, RelationImage(relation, argument));

    private static Formula ReachExpansionFormula()
    {
        Formula state = F.Id("X");
        Formula index = F.Id("J");
        Formula relation = F.Id("R");
        Formula initial = F.Id("I");
        Formula family = F.Id("A");
        Formula i = F.Id("i");
        Formula n = F.Id("n");
        Formula argument = F.Id("S");
        Formula powerset = Seq(
            Operatorname, Grp(F.Id("Set")), Open, state, Close);
        Formula relationType = Seq(
            Operatorname, Grp(F.Id("Set")), Open,
            state, Sp, Times, Sp, state, Close);
        Formula familyUnion = Seq(
            UnionSymbol(), Underscore, Grp(i, InMacro, Sp, index), Sp, Apply(family, i));
        Formula reachOperator = Seq(
            Open, argument, Sp, Mapsto, Sp,
            ReachOperator(initial, relation, argument), Close);
        Formula stage = Seq(
            reachOperator, Caret, Grp(OpenBracket, n, CloseBracket), Open, Emptyset, Close);

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, index, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak,
            relation, Colon, Sp, relationType, Comma, Sp,
            initial, Colon, Sp, powerset, Comma, Sp,
            family, Colon, Sp, index, Sp, To, Sp, powerset, Comma, RowBreak,
            RelationImage(relation, familyUnion), Sp, Eq, Sp,
            UnionSymbol(), Underscore, Grp(i, InMacro, Sp, index), Sp,
            RelationImage(relation, Apply(family, i)), Sp, Land, RowBreak,
            Operatorname, Grp(F.Id("lfp")), Open, reachOperator, Close, Sp, Eq, Sp,
            UnionSymbol(), Underscore,
            Grp(n, InMacro, Sp, Mathbb, Grp(F.Id("N"))), Sp, stage, Dot));
    }

    private static Formula UnionSymbol() =>
        Seq(Operatorname, Grp(F.Id("union")));
}
