using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class CirculantCharpolyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/CirculantCharpoly";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourier modes factor circulant characteristic polynomials.",
        H("Circulants and odd cosine pairing"), Blocks(
            Item("circulant_charpoly", "Complex circulant factorization", "The characteristic polynomial of a complex circulant is the product of X minus its discrete Fourier values. This theorem is existing repository content reused from the Roldan circulant energy development.", DescribeRole.Theorem),
            Item("dft_real_of_even", "Reality of even Fourier values", "The discrete Fourier value of an even real function is real. This theorem is existing repository content reused from the Roldan circulant energy development.", DescribeRole.Theorem),
            Item("real_circulant_charpoly", "Real circulant factorization", "An even real circulant has the product of X minus the real parts of its Fourier values. This theorem is existing repository content reused from the Roldan circulant energy development.", DescribeRole.Theorem),
            Item("realCirculant", "Real residue entries", "For order 2m+1, the circulant entry is f at the least nonnegative residue.", DescribeRole.Definition),
            Item("cosineValue", "Cosine mode values", "The real mode is f(0) plus twice the cosine sum from one through m.", DescribeRole.Definition),
            Item("realCirculant_charpoly", "Odd paired factorization", "For an even generating function, the odd real characteristic polynomial has one constant factor and squared factors for modes one through m. Pairing opposite residues gives the cosine formula and pairing opposite modes gives the squares. This odd pairing factorization is proved here.", DescribeRole.Theorem))));

    private static DocumentBlock Item(string name, string title, string explanation, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("circulant-charpoly-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/jain2017hadamard")),
            Blocks(Paragraph(Text(explanation))), role);
}
