using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockNormalCurrentCommutatorDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Current commutation on every normal-polynomial state",
        H("Current commutation on every normal-polynomial state"),
        Blocks(
            Paragraph(Text("The actual normalPolynomial is the existing symmetric normalWord reconstruction over the original charge field. The argument covers arbitrary multivariate polynomials, repeated oscillator occurrences and empty words.")),
            Describe.Lean(
                DescribeId.Create("latticehalffocknormalcurrentcommutator-normal-polynomial-current-commutator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockNormalCurrentCommutator.normalPolynomial_current_commutator"),
                H("Current commutation on every normal-polynomial state"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The normal current commutator is proved by full polynomial induction. The charged Ward is only the constant base case. Multiplication by an actual source variable uses the finite normalInsertion_current_commutator together with the proved nativeDelta_X_mul and the actual ordinary-mode product recurrence."))),
                DescribeRole.Theorem),
            Paragraph(Text("No twisted Jacobi, translation, stored module identity or altered field assignment is an input. The current contractions are actual tensorCurrent/jetCurrent contractions; all infinite-looking sums have already been reduced to genuine statewise finite supports.")),
            Paragraph(Text("The owning Reg mirrors provide exact dependent-telescope readouts and compiled source equivalence bridges for the substantive commutator and correction identities. They do not provide completed four-slot Contract.Registration inhabitants: variation, sensitivity and observational-dependence evidence remain admission obligations. Consumed algebraic and support helpers are proof organization, not separate new mathematical content.")),
            Paragraph(Text("This is the classical twisted lattice current law in the native constructors, not a claim of literature novelty. The established FLM background and the existing normal-support source attribution remain in force. Full all-state twisted Jacobi, the larger VOA/CFT, BRST/no-ghost, anomaly/fusion, string and AdS/CFT objectives remain open.")))));
}
