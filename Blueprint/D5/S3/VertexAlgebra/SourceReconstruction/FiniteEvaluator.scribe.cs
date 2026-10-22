using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.SourceReconstruction;

internal sealed class FiniteEvaluatorDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite reconstruction of the original native twisted fields",
        H("Finite reconstruction of the original native twisted fields"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sourcereconstruction-finiteevaluator-native-terms-vanish"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceReconstruction/FiniteEvaluator.native_terms_vanish"),
                H("A finite common range for all native terms"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The first cutoff uses the existing normal-polynomial lower order of the smaller original source. The second uses a chosen proven tensor-current bound. The third uses original source-current truncation. All three terms vanish beyond their common finite maximum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcereconstruction-finiteevaluator-wordStep-agrees"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceReconstruction/FiniteEvaluator.wordStep_agrees"),
                H("A genuine weight-lowering reconstruction step"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For a nonempty occurrence word the native recurrence calls only the shorter source and the strictly lower-weight correction sources. The empty word uses the original chargedField on the exact ActualTensor. No charged all-j iterate, AOPE, generator module law or full twisted Jacobi is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcereconstruction-finiteevaluator-evaluateFuel-agrees"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceReconstruction/FiniteEvaluator.evaluateFuel_agrees"),
                H("Natural-weight recursion on all original sources"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Finite charge and monomial expansion reduces every source to its actual occurrence words. Induction on natural fuel proves agreement whenever the original algebraic oscillator bound is at most the fuel. The base contains only original charged grounds. Every recursive summation is an explicit finite Finset range."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcereconstruction-finiteevaluator-evaluate-agrees"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceReconstruction/FiniteEvaluator.evaluate_agrees"),
                H("Coefficientwise agreement on every original source"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Choosing fuel equal to sourceWeightBound reconstructs every coefficient of the literal original Ytw, for arbitrary original source, cover exponent and target vector, with only the existing determinant-unit premise of ActualTensor. Cutoff selection uses classical choice and existing normal-polynomial orders: this is a finite algebraic recursive evaluator, not a claim of an effective complex-number computation. It does not establish charged both-sheet iterates, full twisted Jacobi, fusion, string theory or AdS/CFT."))),
                DescribeRole.Theorem))));
}
