using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence.CompleteHockeyStick;

internal sealed class NonlinearCurveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At fixed gamma greater than one, the complete curve loses a quadratic amount near zero under the full Kraus-product span and Choi support hypotheses.",
        H("Quadratic loss of the complete hockey-stick curve"),
        Blocks(
          Describe.Lean(
            DescribeId.Create("complete-hockey-stick-curve"),
            DeclarationHandle.Create("D5/S3/Quantum/Divergence/CompleteHockeyStick/NonlinearCurve.completeCurve"),
            H("Complete curve at an input budget"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/hirchegeorgenuradhawilde2026conditional")),
            Blocks(
                Paragraph(Text("Take the supremum of the output hockey-stick divergence over every finite reference and every pair of density matrices with equal reference marginals and input divergence at most the budget. Include zero in the supremum."))),
            DescribeRole.Definition),
          Describe.Lean(
            DescribeId.Create("complete-hockey-stick-quadratic-loss"),
            DeclarationHandle.Create("D5/S3/Quantum/Divergence/CompleteHockeyStick/NonlinearCurve.quadratic_loss_near_zero"),
            H("Two-sided quadratic loss"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/hirchegeorgenuradhawilde2026conditional")),
            Blocks(
                Paragraph(Text("Fix gamma greater than one. Suppose the input matrix algebra is spanned by the Kraus products and the normalized Choi support contains no full reference fiber over a nonzero output vector. For all sufficiently small positive budgets a, the loss a minus the complete curve lies between positive channel- and parameter-dependent multiples of a squared.")),
                Paragraph(Text("The uniform upper bound for a single pair is increasing in its input divergence, so it also bounds the supremum at the budget. For the other direction, a finite Choi orbit with zero common support gives a classical-input preparation. Calibrating the simplex makes its divergence equal to the budget, and its graph effect gives payoff at least a divided by (1 + D a). Bell preparation preserves equal marginals and the output payoff while respecting the input budget. One finite reference dimension suffices for every small budget in this construction.")),
                Paragraph(Text("Hirche, George, Nuradha and Wilde propose nonlinear inequalities with references in arXiv:2608.27171v1, Section 9, fourth bullet. Nuradha, George and Hirche give the ordinary curve in arXiv:2512.16778, Equation (4.1). The simplex and graph effect use Eriksson’s classical-input achievability mechanism. The quadratic estimate concerns the equal-reference-marginal curve near zero under the two stated channel hypotheses."))),
            DescribeRole.Theorem))));
}
