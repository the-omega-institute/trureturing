using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.MoralLuck;

internal sealed class MaximalControlCompatibleEvaluationDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/MoralLuck/MaximalControlCompatibleEvaluation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The common coarsening of evaluation and control is the maximal "
            + "control-compatible evaluation.",
        H("Maximal Control-Compatible Evaluation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fair-kernel"),
                DeclarationHandle.Create(DeclarationPrefix + "fairKernel"),
                H("Fair evaluation kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The fair kernel is the least equivalence relation containing both equality "
                        + "of full evaluations and equality of control readouts."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fair-evaluation"),
                DeclarationHandle.Create(DeclarationPrefix + "fairEvaluation"),
                H("Fair evaluation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The fair evaluation sends a state to its quotient class under the fair "
                        + "kernel. Its coordinate type is a quotient rather than the original "
                        + "evaluation codomain."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("maximal-control-compatible-evaluation"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "maximal_control_compatible_evaluation"),
                H("The fair evaluation is the greatest common coarsening"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The state type is explicitly nonempty so factor maps can be extended "
                            + "from reachable evaluation and control coordinates to their full "
                            + "codomains.")),
                    Paragraph(Text(
                        "The first two public conjuncts state that the fair evaluation refines "
                            + "both the full evaluation and the control concept.")),
                    Paragraph(Text(
                        "The third public conjunct states maximality: every candidate refining "
                            + "both source concepts factors through the same quotient. Mathlib's "
                            + "setoid supremum is exactly the required equivalence closure."))),
                DescribeRole.Theorem))));

    private static Formula Refines(Formula coarse, Formula fine) =>
        Seq(coarse, Sp, Leq, Sp, fine);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula evaluationType = F.Id("L");
        Formula controlType = F.Id("B");
        Formula candidateType = F.Id("A");
        Formula evaluation = Seq(F.Id("E"), Underscore, F.Id("J"));
        Formula control = Seq(F.Id("C"), Underscore, Grp(F.Id("ctl")));
        Formula candidate = F.Id("K");
        Formula fair = Seq(F.Id("J"), Underscore, Grp(F.Id("fair")));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, evaluationType, Comma, Sp,
            controlType, Comma, Sp, candidateType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            stateType, Sp, Neq, Sp, Varnothing, Comma, RowBreak, Grp(),
            evaluation, Colon, Sp, stateType, Sp, To, Sp, evaluationType, Comma, Sp,
            control, Colon, Sp, stateType, Sp, To, Sp, controlType, Comma, Sp,
            candidate, Colon, Sp, stateType, Sp, To, Sp, candidateType, Comma, RowBreak, Grp(),
            Refines(fair, evaluation), Sp, Land, RowBreak, Grp(),
            Refines(fair, control), Sp, Land, RowBreak, Grp(),
            Open, Refines(candidate, evaluation), Sp, Land, Sp,
            Refines(candidate, control), Close, Sp, Rightarrow, Sp,
            Refines(candidate, fair), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
