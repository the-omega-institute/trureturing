using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class TimeOrderedMemoryMatrixRepresentationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The frozen timed memory cocycle is the upper-right entry of a matrix word.",
        H("Time-Ordered Memory Matrix Representation"),
        Blocks(
            Definition("state-vector", "memoryStateVector",
                "Memory state column",
                "The memory and scalar coordinates are placed in a two-component complex column vector."),
            Definition("event-matrix", "timedEventMatrix",
                "Timed event matrix",
                "One frozen affine event update is represented by an upper-triangular two-by-two complex matrix."),
            Definition("word-matrix", "timeOrderedWordMatrix",
                "Chronological word matrix",
                "A finite word matrix stores the stable power, memory cocycle, zero lower-left entry, and scalar cocycle."),
            Definition("matrix-product", "chronologicalMatrixProduct",
                "Reverse-ordered matrix product",
                "The head event acts first, so later event matrices multiply on the left of earlier event matrices."),
            Describe.Lean(
                DescribeId.Create("memory-entry"),
                DeclarationHandle.Create(
                    Prefix + "time_ordered_word_matrix_upper_right"),
                H("Memory cocycle is the upper-right entry"),
                StatementSource.FromAuthor(UpperRightFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Matrix-vector multiplication reproduces the existing timed affine update exactly, so the closed word matrix acts as the frozen list evolution on every memory/scalar state; a one-event word summary is exactly the corresponding event matrix, and concatenation is represented by the later word matrix multiplied by the earlier word matrix.")),
                    Paragraph(Text(
                        "The event-by-event matrix product equals the matrix assembled from the existing scalar and memory cocycles, identifying the complete finite memory summary with the upper-right coefficient and the scalar word cocycle with the lower-right coefficient.")),
                    Paragraph(Text(
                        "Swapping two timed events changes the upper-right coefficient by the already frozen prime swap curvature."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle")),
        ]));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);


    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula UpperRightFormula() => Disp(Seq(
        Call("timeOrderedWordMatrix", F.Id("s"), F.Id("w"), D(0), D(1)),
        Sp, Eq, Sp,
        Call("timeOrderedMemoryCocycle", F.Id("s"), F.Id("w"))));
}
