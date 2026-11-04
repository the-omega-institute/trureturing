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
        Formula transform = OwnerAt(OwnerQualified("D5", "S3", "Quantum", "Dynamics", "PolygonalFourierCouplings", "transform"), n);
        return Disp(OwnerAll(n, OwnerNaturals(), Seq(OpenBracket, OwnerAt(OwnerQualified("NeZero"), n), CloseBracket, Sp,
            new Formula.Relation(OwnerAt(OwnerQualified("Matrix", "det"), transform), FormulaRelationOperator.NotEqual,
                OwnerTyped(D(0), OwnerComplexes())))));
    }

    private static Formula CharacterPairFormula()
    {
        Formula n = F.Id("n"), j = F.Id("j"), l = F.Id("l");
        Formula residueType = OwnerAt(OwnerQualified("ZMod"), n);
        Formula jResidue = OwnerTyped(j, residueType), lResidue = OwnerTyped(l, residueType);
        Formula opposite = OwnerTyped(OwnerTyped(new Formula.Binary(n, FormulaBinaryOperator.Subtract, l), OwnerNaturals()), residueType);
        Formula Character(Formula value) => OwnerAt(OwnerQualified("ZMod", "stdAddChar"), value);
        Formula left = new Formula.Binary(Character(OwnerMultiply(jResidue, lResidue)), FormulaBinaryOperator.Add,
            Character(OwnerMultiply(jResidue, opposite)));
        Formula angle = new Formula.Fraction(OwnerMultiply(OwnerMultiply(OwnerMultiply(OwnerTyped(D(2), OwnerReals()),
            OwnerQualified("Real", "pi")), OwnerTyped(j, OwnerReals())), OwnerTyped(l, OwnerReals())), OwnerTyped(n, OwnerReals()));
        Formula right = OwnerTyped(OwnerTyped(OwnerMultiply(OwnerTyped(D(2), OwnerReals()),
            OwnerAt(OwnerQualified("Real", "cos"), angle)), OwnerReals()), OwnerComplexes());
        Formula equality = new Formula.Relation(left, FormulaRelationOperator.Equal, right);
        Formula bound = new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual, n);
        return Disp(OwnerAll(n, OwnerNaturals(), Seq(OpenBracket, OwnerAt(OwnerQualified("NeZero"), n), CloseBracket, Sp,
            OwnerAll(j, OwnerNaturals(), OwnerAll(l, OwnerNaturals(), OwnerImplication(bound, equality))))));
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula OwnerTyped(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula OwnerAll(Formula value, Formula type, Formula body) => Seq(Forall, Sp, OwnerTyped(value, type), Comma, Sp, Parenthesized(body));
    private static Formula OwnerImplication(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula OwnerMultiply(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula OwnerAt(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula OwnerNaturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula OwnerReals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula OwnerComplexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula OwnerQualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }

    private static DocumentBlock Item(string name, string title, string explanation, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("circulant-charpoly-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/jain2017hadamard")),
            Blocks(Paragraph(Text(explanation))), role);
}
