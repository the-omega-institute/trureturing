using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Completion;

internal sealed class FixedTargetCompletionFlatnessDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Completion/FixedTargetCompletionFlatness."
            + "fixed_target_completion_curvature_empty";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed target completions have empty order curvature.",
        H("Fixed-Target Completion Flatness"),
        Blocks(Describe.Lean(
            DescribeId.Create("fixed-target-completion-curvature-empty"),
            DeclarationHandle.Create(Declaration),
            H("Fixed target completion has zero curvature"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The concept readout and both fixed target maps are independent source "
                        + "primitives. Each completion is the canonical join with the target's "
                        + "image-valued readout.")),
                Paragraph(Text(
                    "The displayed curvature is the symmetric difference of the two kernels, "
                        + "where each kernel is viewed as its exact set of related state pairs.")),
                Paragraph(Text(
                    "In either completion order, two states remain equivalent exactly when "
                        + "their original concept values and both fixed target values agree. "
                        + "The two kernel sets therefore coincide.")),
                Paragraph(Text(
                    "Repository searches found no exact fixed-target zero-curvature theorem. "
                        + "The proof imports the canonical target-closure construction and "
                        + "applies Mathlib's symmetric-difference equality criterion."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula stateType = F.Id("X");
        Formula conceptType = F.Id("C");
        Formula firstType = F.Id("S");
        Formula secondType = F.Id("T");
        Formula concept = F.Id("concept");
        Formula firstTarget = F.Id("firstTarget");
        Formula secondTarget = F.Id("secondTarget");
        Formula firstAfterSecond = Call(
            "targetClosure",
            Call("targetClosure", concept, secondTarget),
            firstTarget);
        Formula secondAfterFirst = Call(
            "targetClosure",
            Call("targetClosure", concept, firstTarget),
            secondTarget);
        Formula curvature = Call(
            "symmDiff",
            Call("ker", firstAfterSecond),
            Call("ker", secondAfterFirst));
        Formula inputs = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("concept", Arrow(stateType, conceptType)),
                Bound("firstTarget", Arrow(stateType, firstType)),
                Bound("secondTarget", Arrow(stateType, secondType)),
            ],
            Relation(
                curvature,
                FormulaRelationOperator.Equal,
                new Formula.SetLiteral([])));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", type),
                Bound("C", type),
                Bound("S", type),
                Bound("T", type),
            ],
            inputs));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Relation(
        Formula left,
        FormulaRelationOperator operation,
        Formula right) => new Formula.Relation(left, operation, right);
}
