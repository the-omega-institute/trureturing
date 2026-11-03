using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class CirculantCharpolyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/CirculantCharpoly";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourier modes factor circulant characteristic polynomials.",
        H("Circulants and odd cosine pairing"), Blocks(
            Describe.Lean(DescribeId.Create("circulant-charpoly-transform-det-ne-zero"),
                DeclarationHandle.Create(Module + ".transform_det_ne_zero"),
                H("Fourier transform determinant"), StatementSource.FromAuthor(TransformDetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The normalized Fourier matrix has nonzero determinant because its conjugate transpose is an inverse."))),
                DescribeRole.Theorem),
            Item("circulant_charpoly", "Complex circulant factorization", "The characteristic polynomial of a complex circulant is the product of X minus its discrete Fourier values. This theorem is existing repository content reused from the Roldan circulant energy development.", DescribeRole.Theorem),
            Item("dft_real_of_even", "Reality of even Fourier values", "The discrete Fourier value of an even real function is real. This theorem is existing repository content reused from the Roldan circulant energy development.", DescribeRole.Theorem),
            Item("real_circulant_charpoly", "Real circulant factorization", "An even real circulant has the product of X minus the real parts of its Fourier values. This theorem is existing repository content reused from the Roldan circulant energy development.", DescribeRole.Theorem),
            Item("realCirculant", "Real residue entries", "For order 2m+1, the circulant entry is f at the least nonnegative residue.", DescribeRole.Definition),
            Item("cosineValue", "Cosine mode values", "The real mode is f(0) plus twice the cosine sum from one through m.", DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("circulant-charpoly-character-pair"),
                DeclarationHandle.Create(Module + ".character_pair"), H("Opposite character values"),
                StatementSource.FromAuthor(CharacterPairFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the standard complex additive character on ZMod n, opposite residues pair to twice the cosine of their angle; natural arguments are cast into ZMod n and the real right side is cast into the complex numbers."))),
                DescribeRole.Theorem),
            Item("realCirculant_charpoly", "Odd paired factorization", "For an even generating function, the odd real characteristic polynomial has one constant factor and squared factors for modes one through m. Pairing opposite residues gives the cosine formula and pairing opposite modes gives the squares. This odd pairing factorization is proved here.", DescribeRole.Theorem))));

    private static Formula TransformDetFormula()
    {
        Formula n = F.Id("n");
        return Disp(Seq(Forall, n, InMacro, Mathbb, Grp(F.Id("N")), Comma,
            n, Neq, D(0), Implies,
            Operatorname, Grp(F.Id("det")), Open,
            Operatorname, Grp(F.Id("transform")), Open, n, Close, Close, Neq, D(0)));
    }

    private static Formula CharacterPairFormula()
    {
        Formula n = F.Id("n"), j = F.Id("j"), l = F.Id("l");
        Formula character = Seq(Operatorname, Grp(F.Id("stdAddChar")), Underscore, Grp(n));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula angle = Seq(Frac, Grp(D(2), Pi, j, l), Grp(n));
        return Disp(Seq(Forall, n, InMacro, natural, Comma, n, Neq, D(0), Implies,
            Forall, j, Comma, l, InMacro, natural, Comma, l, Leq, n, Implies,
            character, Open, j, l, Close, Plus,
            character, Open, j, Open, n, Minus, l, Close, Close, Eq,
            D(2), Operatorname, Grp(F.Id("cos")), Open, angle, Close));
    }

    private static DocumentBlock Item(string name, string title, string explanation, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("circulant-charpoly-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/jain2017hadamard")),
            Blocks(Paragraph(Text(explanation))), role);
}
