using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockCurrentNormalRecurrenceDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite native half-current normal-insertion recurrence",
        H("Finite native half-current normal-insertion recurrence"),
        Blocks(
            Paragraph(Text("normalInsertion, flatCoefficient, jetCurrent and all signed integer tuples are the original native definitions. insertionTerm_finite calls the latest flatTerm_finite supplier with the singleton word; its finite tuple bound is not replaced by an aggregate normal-word order.")),
            Describe.Lean(
                DescribeId.Create("latticehalffockcurrentnormalrecurrence-normal-insertion-current-commutator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockCurrentNormalRecurrence.normalInsertion_current_commutator"),
                H("Finite native half-current normal-insertion recurrence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The actual half-current Heisenberg law contracts exactly currentMode=-mode-1. A proved commutator of the inner field extends through the normal insertion with the additional actual jet contraction. This auxiliary premise is proved by induction in normalPolynomial_current_commutator; it is absent from the all-source endpoint."))),
                DescribeRole.Theorem),
            Paragraph(Text("A common finite union contains the actual supports on vector, current(vector) and the derived inner field. Mapping, subtraction and addition of finsums happen only after these finite supports are established. The negative and nonnegative current branches are retained. normalInsertionLinear and signed coverShift preserve the original fields and coefficients.")),
            Paragraph(Text("The owning Reg mirrors provide exact dependent-telescope readouts and compiled source equivalence bridges for the substantive commutator and correction identities. They do not provide completed four-slot Contract.Registration inhabitants: variation, sensitivity and observational-dependence evidence remain admission obligations. Consumed algebraic and support helpers are proof organization, not separate new mathematical content.")),
            Paragraph(Text("This is the classical twisted lattice current law in the native constructors, not a claim of literature novelty. The established FLM background and the existing normal-support source attribution remain in force. Full all-state twisted Jacobi, the larger VOA/CFT, BRST/no-ghost, anomaly/fusion, string and AdS/CFT objectives remain open.")))));
}
