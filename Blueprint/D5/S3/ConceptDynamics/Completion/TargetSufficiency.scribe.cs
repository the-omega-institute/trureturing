using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Completion;

internal sealed class TargetSufficiencyDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Completion/TargetSufficiency.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Target residual emptiness is exactly target stability on local observation fibers.",
        H("Target Sufficiency"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("empty-target-residuals-are-target-closure-fixed-points"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "target_residual_empty_iff_target_closure_fixed"),
                H("Empty target residuals are target-closure fixed points"),
                StatementSource.FromAuthor(ClosureBridgeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an inhabited state type, the newly named target residual is the "
                            + "existing defect relation. Its emptiness is therefore the existing "
                            + "fiber-constancy condition.")),
                    Paragraph(Text(
                        "The imported target-closure theorem identifies fixed points with "
                            + "canonical target refinement, while the existing universal "
                            + "factorization theorem identifies that refinement with the same "
                            + "fiber condition."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("the-three-target-sufficiency-conditions-are-equivalent"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "target_sufficiency_three_way"),
                H("The three target-sufficiency conditions are equivalent"),
                StatementSource.FromAuthor(ThreeWayFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The target residual is empty exactly when every pair with the same "
                            + "single-readout coordinate has the same target value. Thus local "
                            + "indistinguishability means literal equality under q.")),
                    Paragraph(Text(
                        "Mathlib's factors-through criterion turns fiber constancy into a total "
                            + "decoder on the raw codomain of q. Nonempty Y supplies a value on "
                            + "coordinates outside the realized range of q.")),
                    Paragraph(Text(
                        "This single-readout statement uses q in place of the source's q_all. "
                            + "A quotient lift would avoid choice only after replacing q by its "
                            + "kernel quotient projection, which is a different factorization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("inhabited-states-are-needed-by-the-closure-bridge"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "nonempty_state_hypothesis_is_necessary"),
                H("Inhabited states are needed by the closure bridge"),
                StatementSource.FromAuthor(StateNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take Empty states, Unit observations, and an Empty-valued target. The "
                            + "target residual is empty because there are no state pairs.")),
                    Paragraph(Text(
                        "Target closure nevertheless has an empty target-image coordinate. A "
                            + "reverse refinement from Unit would construct an element of that "
                            + "empty image, so closure equivalence fails."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("an-empty-target-type-blocks-a-total-decoder"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "nonempty_target_hypothesis_is_necessary"),
                H("An empty target type blocks a total decoder"),
                StatementSource.FromAuthor(TargetNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Again use Empty states, Unit observations, and an Empty target type. "
                            + "Residual emptiness and fiber constancy both hold vacuously.")),
                    Paragraph(Text(
                        "A total factor through the raw observation codomain would include a "
                            + "function from Unit to Empty. Evaluating it at the unit value is "
                            + "impossible, so target inhabitedness cannot simply be deleted."))),
                DescribeRole.Lemma))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Residual(Formula readout, Formula target) =>
        Call("targetResidual", readout, target);

    private static Formula Closure(Formula readout, Formula target) =>
        Call("targetClosure", readout, target);

    private static Formula FiberCondition(
        Formula state,
        Formula readout,
        Formula target,
        Formula left,
        Formula right) =>
        Seq(
            Forall, Sp, Typed(Seq(left, Comma, Sp, right), state), Comma, Sp,
            Apply(readout, left), Sp, Eq, Sp, Apply(readout, right), Sp,
            Rightarrow, Sp,
            Apply(target, left), Sp, Eq, Sp, Apply(target, right));

    private static Formula FactorCondition(
        Formula observation,
        Formula targetType,
        Formula readout,
        Formula target) =>
        Seq(
            Exists, Sp,
            Typed(F.Id("barT"), Arrow(observation, targetType)), Comma, Sp,
            target, Sp, Eq, Sp, F.Id("barT"), Sp, Circ, Sp, readout);

    private static Formula QuantifiedInputs(
        Formula state,
        Formula observation,
        Formula targetType,
        Formula readout,
        Formula target) =>
        Seq(
            Forall, Sp,
            Typed(
                Seq(state, Comma, Sp, observation, Comma, Sp, targetType),
                TypeUniverse()),
            Comma, Sp,
            Typed(readout, Arrow(state, observation)), Comma, Sp,
            Typed(target, Arrow(state, targetType)), Comma);

    private static Formula ClosureBridgeFormula()
    {
        Formula state = F.Id("X");
        Formula observation = F.Id("B");
        Formula targetType = F.Id("Y");
        Formula readout = F.Id("q");
        Formula target = F.Id("t");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            QuantifiedInputs(state, observation, targetType, readout, target),
            RowBreak, Grp(),
            OpenBracket, Call("Nonempty", state), CloseBracket, Comma, Sp,
            Residual(readout, target), Sp, Eq, Sp, Emptyset, Sp,
            Iff, Sp,
            Call("ConceptEquivalent", Closure(readout, target), readout), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ThreeWayFormula()
    {
        Formula state = F.Id("X");
        Formula observation = F.Id("B");
        Formula targetType = F.Id("Y");
        Formula readout = F.Id("q");
        Formula target = F.Id("t");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula residualEmpty = Seq(
            Residual(readout, target), Sp, Eq, Sp, Emptyset);
        Formula fiber = FiberCondition(state, readout, target, left, right);
        Formula factor = FactorCondition(observation, targetType, readout, target);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            QuantifiedInputs(state, observation, targetType, readout, target),
            RowBreak, Grp(),
            OpenBracket, Call("Nonempty", targetType), CloseBracket, Comma, Sp,
            Open, residualEmpty, Sp, Iff, Sp, fiber, Close, Sp, Land,
            RowBreak, Grp(),
            Open, fiber, Sp, Iff, Sp, factor, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula StateNecessityFormula()
    {
        Formula empty = F.Id("Empty");
        Formula readout = F.Id("qEmpty");
        Formula target = F.Id("tEmpty");

        return Disp(Seq(
            Typed(readout, Arrow(empty, F.Id("Unit"))), Comma, Sp,
            Typed(target, Arrow(empty, empty)), Comma, Sp,
            Residual(readout, target), Sp, Eq, Sp, Emptyset, Sp, Land, Sp,
            Neg, Sp,
            Call("ConceptEquivalent", Closure(readout, target), readout), Dot));
    }

    private static Formula TargetNecessityFormula()
    {
        Formula empty = F.Id("Empty");
        Formula unit = F.Id("Unit");
        Formula readout = F.Id("qEmpty");
        Formula target = F.Id("tEmpty");
        Formula left = F.Id("x");
        Formula right = F.Id("y");

        return Disp(Seq(
            Typed(readout, Arrow(empty, unit)), Comma, Sp,
            Typed(target, Arrow(empty, empty)), Comma, RowBreak, Grp(),
            Residual(readout, target), Sp, Eq, Sp, Emptyset, Sp, Land, Sp,
            FiberCondition(empty, readout, target, left, right), Sp, Land,
            RowBreak, Grp(),
            Neg, Sp, FactorCondition(unit, empty, readout, target), Dot));
    }
}
