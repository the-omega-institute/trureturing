using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Seesaw;

internal sealed class AdmissibleEvaluationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Admissible Evaluation", H("Admissible Evaluation"),
        Blocks(
            Paragraph(Text("Denominator control under adjoints and conjugation; membership in the glued lattice. Evaluated vacua are admissible translates of the neighbour-lattice vacuum, the sum τ_N.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Seesaw/AdmissibleEvaluation.isAdmissibleEval_finEval"),
                H("isAdmissibleEval_finEval"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("In the setting of exists_isAdmissibleEval_std, with Y' of lattice Grading.SpansLattice a π u and δ = (ᾱ/α)(a/ā): if the embedding of X⁻ ⊕ X'' respects the weights (hA) and maps scaled IsNeighbourVector vectors into the lattices of V, V'' (hM), then ArrowPair.finEval satisfies IsAdmissibleEval for β and κ = 1.")))))));
}
