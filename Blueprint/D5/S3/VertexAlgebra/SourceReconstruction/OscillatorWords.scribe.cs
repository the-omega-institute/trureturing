using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.SourceReconstruction;

internal sealed class OscillatorWordsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All-charge original oscillator words",
        H("All-charge original oscillator words"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sourcereconstruction-oscillatorwords-negative-current-single"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceReconstruction/OscillatorWords.negative_current_single"),
                H("The actual negative current acts by multiplication"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The current is the original sourceCurrent with a single basis coefficient. Its normalized negative mode multiplies the original charge-sector polynomial by X(i,d). No determinant, rank or positive-definiteness assumption occurs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcereconstruction-oscillatorwords-finite-source-expansion"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceReconstruction/OscillatorWords.finite_source_expansion"),
                H("Finite generation with every original charge ground"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Every original state is a finite charge sum and a finite monomial sum of actual current words on its own charged ground. The existing occurrences product keeps repeated labels and multiplicities. This is not finite generation by a positive-lattice charge subset."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcereconstruction-oscillatorwords-oscillatorWordSpan-eq-top"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceReconstruction/OscillatorWords.oscillatorWordSpan_eq_top"),
                H("The original all-charge oscillator span is the whole carrier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The finite source expansion supplies the spanning argument. These source interfaces are consumed by both finite reconstruction evaluators."))),
                DescribeRole.Theorem))));
}
