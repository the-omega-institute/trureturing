using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Completion;

internal sealed class TargetFamilyCompletionMinimalityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjoining an entire target family is the coarsest jointly sufficient refinement.",
        H("Minimal Target-Family Completion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("target-family-completion-is-coarsest"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Completion/TargetFamilyCompletionMinimality."
                        + "target_family_completion_is_coarsest"),
                H("Target-family completion is coarsest"),
                StatementSource.FromAuthor(MinimalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The completion is constructed canonically by joining the current "
                            + "interface with the dependent readout of every target value.")),
                    Paragraph(Text(
                        "Projection to the first coordinate recovers the current interface. "
                            + "Projection to the joint-target coordinate followed by evaluation "
                            + "recovers every member of the target family.")),
                    Paragraph(Text(
                        "Any interface that recovers both the current readout and every target "
                            + "receives the paired factor map from this completion. Thus the same "
                            + "construction covers factual, predictive, causal, sequential-effect, "
                            + "indexed-readout, strategy, and self-relevant target families."))),
                DescribeRole.Theorem))));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Refines(Formula coarse, Formula fine) =>
        Call("Refines", coarse, fine);

    private static Formula MinimalityFormula()
    {
        Formula stateType = F.Id("X");
        Formula indexType = F.Id("I");
        Formula currentType = F.Id("Q");
        Formula targetTypes = F.Id("Y");
        Formula current = F.Id("q");
        Formula targets = F.Id("T");
        Formula index = F.Id("i");
        Formula candidateType = F.Id("D");
        Formula candidate = F.Id("r");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula targetType = Apply(targetTypes, index);
        Formula target = Apply(targets, index);
        Formula joint = Call("jointTarget", targets);
        Formula completion = Call("conceptJoin", current, joint);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(stateType, Comma, Sp, indexType, Comma, Sp, currentType), type),
            Comma, Sp,
            Typed(targetTypes, new Formula.TypeArrow(indexType, type)),
            Comma, RowBreak, Grp(),
            Typed(current, new Formula.TypeArrow(stateType, currentType)),
            Comma, RowBreak, Grp(),
            Typed(targets,
                Seq(Forall, Sp, Typed(index, indexType), Comma, Sp,
                    new Formula.TypeArrow(stateType, targetType))),
            Comma, RowBreak, Grp(),
            Refines(current, completion), Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, Typed(index, indexType), Comma, Sp,
            Refines(target, completion), Close, Sp, Land, RowBreak, Grp(),
            Forall, Sp, Typed(candidateType, type), Comma, Sp,
            Typed(candidate, new Formula.TypeArrow(stateType, candidateType)),
            Comma, RowBreak, Grp(),
            Refines(current, candidate), Sp, Land, Sp,
            Open, Forall, Sp, Typed(index, indexType), Comma, Sp,
            Refines(target, candidate), Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Refines(completion, candidate), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
