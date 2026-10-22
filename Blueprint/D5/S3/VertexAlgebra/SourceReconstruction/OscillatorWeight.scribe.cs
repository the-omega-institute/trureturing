using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.SourceReconstruction;

internal sealed class OscillatorWeightDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Algebraic oscillator weight and strict descent",
        H("Algebraic oscillator weight and strict descent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sourcereconstruction-oscillatorweight-polynomial-pderiv-weight-le"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceReconstruction/OscillatorWeight.polynomial_pderiv_weight_le"),
                H("Polynomial differentiation does not increase oscillator weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("A nonzero derivative coefficient comes from the original exponent plus one occurrence of the differentiated label. Its weight is bounded by the original polynomial weighted degree. The argument is coefficientwise and preserves multiplicity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcereconstruction-oscillatorweight-polynomial-correction-weight-lt"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceReconstruction/OscillatorWeight.polynomial_correction_weight_lt"),
                H("All three original current cases lower descendant weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Negative modes multiply by an oscillator of weight d-j. The zero mode is the original charge scalar. Positive modes are the original Gram-weighted polynomial derivatives. Each correction has weight strictly below wt(u)+d+1; no lattice norm or energy cutoff is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcereconstruction-oscillatorweight-correction-source-weight-lt"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceReconstruction/OscillatorWeight.correction_source_weight_lt"),
                H("Strict lowering on every finite charge-supported source"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The actual current preserves charge and acts on each original polynomial component. Finite support gives a natural maximum oscillator weight. Every correction source, including zero, is strictly lower than the new descendant bound. FiniteEvaluator.wordStep_agrees consumes this inequality."))),
                DescribeRole.Theorem))));
}
