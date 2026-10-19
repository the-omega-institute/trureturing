using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Subentropy;

internal sealed class GuessingProbabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite positive operator-valued measurements define an honest supremum guessing probability.",
        H("Guessing probability"),
        Blocks(
            Describe.Lean(DescribeId.Create("measurement-success-probability"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/GuessingProbability.successProbability"),
                H("The success probability of a labelled measurement"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy")),
                Blocks(
                    Paragraph(Text("For a finite ensemble of density states rho_x with label weights p_x, successProbability is sum_x p_x Re Tr(M_x rho_x). The finite measurement has exactly one output for each guessed label."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("measurement-success-set"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/GuessingProbability.successProbabilitySet"),
                H("The genuine POVM success set"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy")),
                Blocks(
                    Paragraph(Text("successProbabilitySet consists of exactly the success probabilities of matrices M_x that are positive semidefinite and sum to the identity. No restriction to projective measurements is imposed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("optimal-guessing-probability"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/GuessingProbability.pGuess"),
                H("The optimal guessing probability"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy")),
                Blocks(
                    Paragraph(Text("pGuess is the supremum of successProbabilitySet. For nonnegative normalized ensemble weights, pGuess_bounds establishes that the set is nonempty and bounded above, and that 0<pGuess<=1 and 1-pGuess<=-log pGuess. Positivity follows from the deterministic measurement guessing a positive-weight label; normalization itself excludes an empty label type. The same proof establishes that any bound q<=1-successProbability valid for every labelled POVM implies q<=1-pGuess. It requires no attainment theorem for an optimal POVM.")),
                    Paragraph(Text("These probability and supremum statements do not assert a bound on conditional subentropy. That further conclusion requires the separate matrix pinching-gap inequality for every POVM."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("guessing-probability-bounds"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/GuessingProbability.pGuess_bounds"),
                H("Bounded positive guessing probability and supremum transfer"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy")),
                Blocks(Paragraph(Text("For every finite nonnegative normalized ensemble, the genuine POVM success set is nonempty and bounded above, and its supremum lies in (0,1]. The logarithmic comparison 1-pGuess<=-log pGuess follows from log p<=p-1. Every bound q<=1-successProbability valid for all finite POVMs transfers to q<=1-pGuess by the defining least-upper-bound property. No optimal measurement or supremum attainment is assumed."))), DescribeRole.Theorem))));
}
