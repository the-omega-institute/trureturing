using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.JainAbsCosine;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Absolute cosine matrix powers and their Fourier modes. The matrix and conjecture are those of Jain.",
        H("Odd order absolute cosine powers"), Blocks(
            Entry("jain-angle", "angle", "Angular step", "For order 2m+1 the angular step is pi divided by 2m+1."),
            Entry("jain-absolute-power", "absCosPow", "Entrywise real powers", "The matrix entry at a,b is the real power r of the absolute value of cos((a-b) pi/(2m+1))."),
            Entry("jain-mode-value", "modeValue", "Real Fourier mode", "The j-th mode is one plus twice the sum over l from one to m of cos(2jl pi/(2m+1)) times cos(l pi/(2m+1)) to the real power r."),
            Entry("jain-root-product", "rootProduct", "Even root product", "The product over s less than j of r-2s records the proposed roots and their signs."),
            Entry("jain-multiplicity-claim", "claim", "Nonzero eigenvalue multiplicity", "For m at least one and nonnegative r, every nonzero root of the characteristic polynomial other than mode zero has root multiplicity exactly two."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Quantum/Matrix/JainAbsCosine/Defs." + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/jain2017hadamard")),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
