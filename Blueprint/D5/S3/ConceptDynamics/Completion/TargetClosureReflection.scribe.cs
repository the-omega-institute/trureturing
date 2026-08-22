using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Completion;

internal sealed class TargetClosureReflectionDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Completion/TargetClosureReflection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Target closure is the least target-sufficient refinement and reflects into the "
            + "target-sufficient concepts.",
        H("Target Closure Reflection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("target-sufficiency-is-fiber-constancy"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "target_sufficient_iff_fiber_constant"),
                H("Target sufficiency is constancy on concept fibers"),
                StatementSource.FromAuthor(FiberConstancyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On a nonempty state space, a concept is target-sufficient exactly when "
                            + "the target takes the same value on every pair of states that the "
                            + "concept readout identifies.")),
                    Paragraph(Text(
                        "Equivalently, the canonical target-image readout factors through the "
                            + "concept precisely when the target is constant on each concept "
                            + "fiber."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("target-closure-has-the-reflection-universal-property"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "target_closure_reflection_universal"),
                H("Target closure has the reflection universal property"),
                StatementSource.FromAuthor(ReflectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a target-sufficient comparison concept. The target closure of a "
                            + "concept refines that comparison exactly when the original concept "
                            + "already refines it.")),
                    Paragraph(Text(
                        "One direction follows because the original concept refines its closure. "
                            + "For the other, the comparison receives both the original concept "
                            + "and the canonical target readout, so the universal property of "
                            + "their join supplies the required factorization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("target-closure-is-the-least-target-sufficient-refinement"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "target_closure_is_least_target_sufficient_refinement"),
                H("Target closure is the least target-sufficient refinement"),
                StatementSource.FromAuthor(LeastRefinementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Target closure is itself target-sufficient and refines the original "
                            + "concept by adjoining only the canonical target coordinate.")),
                    Paragraph(Text(
                        "Every target-sufficient concept that refines the original concept also "
                            + "receives a factor map from the closure. These three properties make "
                            + "the closure the least target-sufficient refinement in the concept "
                            + "refinement order."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("target-closure-is-a-target-sufficient-fixed-point"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "target_closure_is_target_sufficient_fixed_point"),
                H("Target closure is a target-sufficient fixed point"),
                StatementSource.FromAuthor(FixedPointFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Completing a concept makes the target recoverable from its readout. "
                            + "Completing the result again adds no new distinctions: the twice-"
                            + "completed readout and the once-completed readout mutually refine "
                            + "one another.")),
                    Paragraph(Text(
                        "Thus target closure lands among the target-sufficient concepts and is "
                            + "idempotent there up to concept equivalence."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("target-sufficiency-is-necessary-for-reflection"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "target_sufficiency_hypothesis_is_necessary"),
                H("Target sufficiency is necessary for the reflection equivalence"),
                StatementSource.FromAuthor(NecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take both concepts to be the constant readout from the two Boolean "
                            + "states to the one-point type, and take the target to be the Boolean "
                            + "identity. The two concepts refine one another, but neither can "
                            + "recover the target.")),
                    Paragraph(Text(
                        "The target closure records the Boolean target coordinate and therefore "
                            + "distinguishes false from true. It cannot factor through the "
                            + "one-point comparison concept, which witnesses failure of the "
                            + "reflection equivalence when target sufficiency is omitted."))),
                DescribeRole.Lemma))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Readout(Formula index) =>
        new Formula.Subscript(F.Id("q"), index);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Closure(Formula concept, Formula target) =>
        Call("targetClosure", concept, target);

    private static Formula Sufficient(Formula concept, Formula target) =>
        Call("TargetSufficient", concept, target);

    private static Formula RefinesConcept(Formula coarse, Formula fine) =>
        Call("Refines", coarse, fine);

    private static Formula FiberConstancyFormula()
    {
        Formula state = F.Id("X");
        Formula conceptType = F.Id("D");
        Formula targetType = F.Id("Y");
        Formula concept = Readout(F.Id("D"));
        Formula target = F.Id("T");
        Formula x = F.Id("x");
        Formula y = F.Id("y");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(state, Comma, Sp, conceptType, Comma, Sp, targetType),
                TypeUniverse()),
            Comma, RowBreak, Grp(),
            Call("Nonempty", state), Comma, Sp,
            Typed(concept, Arrow(state, conceptType)), Comma, Sp,
            Typed(target, Arrow(state, targetType)), Comma, RowBreak, Grp(),
            Sufficient(concept, target), Sp, Iff, Sp,
            Forall, Sp, Typed(Seq(x, Comma, Sp, y), state), Comma, Sp,
            Apply(concept, x), Sp, Eq, Sp, Apply(concept, y), Sp,
            Rightarrow, Sp,
            Apply(target, x), Sp, Eq, Sp, Apply(target, y), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ReflectionFormula()
    {
        Formula state = F.Id("X");
        Formula conceptType = F.Id("B");
        Formula comparisonType = F.Id("D");
        Formula targetType = F.Id("Y");
        Formula concept = Readout(F.Id("C"));
        Formula comparison = Readout(F.Id("D"));
        Formula target = F.Id("T");
        Formula closure = Closure(concept, target);

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
            Sufficient(comparison, target), Sp, Rightarrow, Sp,
            Open,
            RefinesConcept(closure, comparison), Sp, Iff, Sp,
            RefinesConcept(concept, comparison),
            Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula LeastRefinementFormula()
    {
        Formula state = F.Id("X");
        Formula conceptType = F.Id("B");
        Formula comparisonType = F.Id("D");
        Formula targetType = F.Id("Y");
        Formula concept = Readout(F.Id("C"));
        Formula comparison = Readout(F.Id("D"));
        Formula target = F.Id("T");
        Formula closure = Closure(concept, target);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(state, Comma, Sp, conceptType, Comma, Sp, targetType),
                TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(concept, Arrow(state, conceptType)), Comma, Sp,
            Typed(target, Arrow(state, targetType)), Comma, RowBreak, Grp(),
            Sufficient(closure, target), Sp, Land, RowBreak, Grp(),
            RefinesConcept(concept, closure), Sp, Land, RowBreak, Grp(),
            Forall, Sp, Typed(comparisonType, TypeUniverse()), Comma, Sp,
            Typed(comparison, Arrow(state, comparisonType)), Comma, RowBreak, Grp(),
            Open,
            Sufficient(comparison, target), Sp, Land, Sp,
            RefinesConcept(concept, comparison),
            Close, Sp, Rightarrow, Sp,
            RefinesConcept(closure, comparison), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula FixedPointFormula()
    {
        Formula state = F.Id("X");
        Formula conceptType = F.Id("B");
        Formula targetType = F.Id("Y");
        Formula concept = Readout(F.Id("C"));
        Formula target = F.Id("T");
        Formula closure = Closure(concept, target);
        Formula closureTwice = Closure(closure, target);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(state, Comma, Sp, conceptType, Comma, Sp, targetType),
                TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(concept, Arrow(state, conceptType)), Comma, Sp,
            Typed(target, Arrow(state, targetType)), Comma, RowBreak, Grp(),
            Sufficient(closure, target), Sp, Land, RowBreak, Grp(),
            Call("ConceptEquivalent", closureTwice, closure), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula NecessityFormula()
    {
        Formula concept = Readout(F.Id("C"));
        Formula comparison = Readout(F.Id("D"));
        Formula boolType = F.Id("Bool");
        Formula unitType = F.Id("Unit");
        Formula identity = new Formula.Subscript(F.Id("id"), boolType);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Exists, Sp,
            Typed(
                Seq(concept, Comma, Sp, comparison),
                Call("Concept", boolType, unitType)),
            Comma, RowBreak, Grp(),
            Neg, Sp, Sufficient(comparison, identity), Sp, Land, RowBreak, Grp(),
            RefinesConcept(concept, comparison), Sp, Land, RowBreak, Grp(),
            Neg, Sp, RefinesConcept(Closure(concept, identity), comparison), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
