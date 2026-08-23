using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Completion;

internal sealed class TargetClosureOperatorDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Completion/TargetClosureOperator.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joining a concept with the canonical target readout defines a closure operation.",
        H("Target Closure Operator"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("target-completion-obeys-the-three-closure-laws"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "target_closure_three_laws"),
                H("Target completion obeys the three closure laws"),
                StatementSource.FromAuthor(ThreeClosureLawsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Target completion adjoins the canonical target-image readout to a "
                            + "concept readout. Projection onto the original coordinate shows "
                            + "that completion is extensive in the refinement order.")),
                    Paragraph(Text(
                        "A factor map between two concept readouts lifts to their completions "
                            + "by applying it to the concept coordinate and preserving the "
                            + "shared target coordinate, which proves monotonicity.")),
                    Paragraph(Text(
                        "Completing twice adds a second copy of the same target coordinate. "
                            + "Duplicating that coordinate and forgetting the duplicate give "
                            + "mutual refinements, so idempotence holds up to concept "
                            + "equivalence despite the changed product codomain."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fixed-points-are-exactly-target-sufficient-concepts"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "target_closure_equivalent_iff_target_sufficient"),
                H("Fixed points are exactly target-sufficient concepts"),
                StatementSource.FromAuthor(FixedPointFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A concept is unchanged by target completion, up to mutual refinement, "
                            + "exactly when its readout already determines the canonical target "
                            + "readout. In that case adjoining the target adds no distinctions.")),
                    Paragraph(Text(
                        "Conversely, if completion is equivalent to the original concept, the "
                            + "target projection through the completed readout composes with "
                            + "that equivalence to factor the target through the original "
                            + "concept."))),
                DescribeRole.Lemma))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Readout(Formula index) =>
        new Formula.Subscript(F.Id("q"), index);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Closure(Formula concept, Formula target) =>
        Call("targetClosure", concept, target);

    private static Formula ThreeClosureLawsFormula()
    {
        Formula state = F.Id("X");
        Formula conceptType = F.Id("B");
        Formula comparisonType = F.Id("D");
        Formula targetType = F.Id("Y");
        Formula concept = Readout(F.Id("C"));
        Formula comparison = Readout(F.Id("D"));
        Formula target = F.Id("T");
        Formula completedConcept = Closure(concept, target);
        Formula completedComparison = Closure(comparison, target);
        Formula completedTwice = Closure(completedConcept, target);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(
                Seq(
                    state, Comma, Sp, conceptType, Comma, Sp,
                    comparisonType, Comma, Sp, targetType),
                TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(concept, Arrow(state, conceptType)), Comma, Sp,
            Typed(comparison, Arrow(state, comparisonType)), Comma, Sp,
            Typed(target, Arrow(state, targetType)), Comma, RowBreak, Grp(),
            Call("Refines", concept, completedConcept), Sp, Land, RowBreak, Grp(),
            Open,
            Call("Refines", concept, comparison), Sp, Rightarrow, Sp,
            Call("Refines", completedConcept, completedComparison),
            Close, Sp, Land, RowBreak, Grp(),
            Call("ConceptEquivalent", completedTwice, completedConcept), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula FixedPointFormula()
    {
        Formula state = F.Id("X");
        Formula conceptType = F.Id("B");
        Formula targetType = F.Id("Y");
        Formula concept = Readout(F.Id("C"));
        Formula target = F.Id("T");
        Formula canonicalTarget = Call("canonicalTargetReadout", target);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(
                Seq(state, Comma, Sp, conceptType, Comma, Sp, targetType),
                TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(concept, Arrow(state, conceptType)), Comma, Sp,
            Typed(target, Arrow(state, targetType)), Comma, RowBreak, Grp(),
            Call("ConceptEquivalent", Closure(concept, target), concept), Sp,
            Iff, Sp,
            Call("Refines", canonicalTarget, concept), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
