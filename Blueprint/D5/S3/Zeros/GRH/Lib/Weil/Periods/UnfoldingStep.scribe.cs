using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Periods;

internal sealed class UnfoldingStepDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unfolding Step", H("Unfolding Step"),
        Blocks(
            Paragraph(Text("Surviving rational orbit by Witt's theorem, its stabiliser, twists killing other terms. Constant terms along graded isotropic subspaces: substitution rules, Fourier expansion, next generic function. One unfolding step transferring Bessel or Fourier-Jacobi periods across a theta lift.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Periods/UnfoldingStep.integral_besselGroup_unfold"),
                H("integral_besselGroup_unfold"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("One unfolding step, s = s' + 1: for P as in Grading.IsGeneric and y rapid continuous on [G'], the [B]-period at x of P times the theta integral of y is ∫ P'_x·y over B'(E⁺)∖G'(𝔸), which converges absolutely.")))))));
}
