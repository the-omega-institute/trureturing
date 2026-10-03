using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class MonsterShortSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/MonsterShortSupport.";
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/macwilliams1977binaryrepetition");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd binary relations have unique representatives of weight at most half.",
        H("Odd Binary Relations and Unique Short Supports"),
        Blocks(
            Paragraph(Text("The seven nonzero ground sections have one repetition relation. "
                + "Consequently each finite six-bit label has a unique coefficient vector "
                + "whose Hamming support has size at most three.")),
            Describe.Lean(
                DescribeId.Create("unique-seven-section-short-support"),
                DeclarationHandle.Create(Prefix + "unique_short_support"),
                H("Unique short support representative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The proof combines the kernel characterization from "
                    + "MonsterFusionSpan with the odd complement argument for the binary "
                    + "repetition code. It is a finite label theorem only: it does not assert "
                    + "a VOA realization, an OPE coefficient, or a Monster action."))),
                DescribeRole.Theorem))));
}
