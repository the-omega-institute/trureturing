using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.WordSpans;

internal sealed class ShitovSizeThreeDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Matrix/WordSpans/ShitovSizeThree.";
    private static readonly LibraryNoteRef Shitov =
        LibraryNoteRef.Create("D5/L/HilbertOperators/shitov2023growthmatrixalgebras");
    private static readonly LibraryNoteRef Yu =
        LibraryNoteRef.Create("D5/L/HilbertOperators/yu2026wielandtlowerbound");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Seven is the least universal exact word length for eventually full complex matrix spans in size three.",
        H("Shitov's exact word length in size three"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("shitov-size-three-exact-word-span"),
                DeclarationHandle.Create(Owner + "exactWordSpan"),
                H("Exact word span"),
                StatementSource.FromAuthor(Disp(SpanFormula())),
                AssessedProvenance.FromLiterature(Shitov),
                Blocks(Paragraph(Text(
                    "In Remark 1, the product uses precisely k factors. The index runs in increasing "
                    + "order, with one independently chosen member of S at each position. The empty "
                    + "product is the identity. Fullness in Question 2 is tested at positive lengths."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("shitov-size-three-least-universal-length"),
                DeclarationHandle.Create(Owner + "result"),
                H("Least universal length"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Shitov, Yu),
                Blocks(
                    Paragraph(Text(
                        "Shitov's Question 2 asks for the universal index. Here S ranges over every "
                        + "subset of the complex three-by-three matrix algebra. If the span is full "
                        + "at any positive exact length m, it is full at length seven. Seven is the "
                        + "least positive length with this property.")),
                    Paragraph(Text(
                        "The span of the exact words is the corresponding power of the generator "
                        + "subspace. Fullness at positive length persists. An invertible element "
                        + "in degree s enforces strict dimension growth in steps of s until fullness. "
                        + "For an invertible generator the rank-one return analysis gives enough "
                        + "growth, with the scalar-cube case excluded by its cyclic orbit lines. "
                        + "For a singular generator space the alternating normal form gives a full "
                        + "square, and the compression normal form gives a unit in degree two and "
                        + "at least seven dimensions in degree three.")),
                    Paragraph(Text(
                        "The lower witness is Yi Yu's published pair in Theorem 1.2, specialized to "
                        + "size three. A linear functional vanishes on every six-letter word, and "
                        + "nine seven-letter words form a basis. By persistence, a universal positive "
                        + "length below seven would make the sixth span full for Yu's pair."))),
                DescribeRole.Theorem))));

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula MatrixSpace => Seq(F.Id("M"), Underscore, Grp(D(3)), Parenthesized(Complex));
    private static Formula GeneratorSets => Call("Set", MatrixSpace);
    private static Formula WordSpan(Formula s, Formula k) => Call("exactWordSpan", s, k);

    private static Formula SpanFormula()
    {
        Formula s = F.Id("S"), k = F.Id("k"), f = F.Id("f"), i = F.Id("i");
        Formula factors = Seq(Call("Fin", k), Sp, To, Sp, s);
        Formula product = Seq(Prod, Underscore, Grp(i, Sp, InMacro, Sp, Call("Fin", k)),
            Sp, Seq(f, Parenthesized(i)));
        Formula words = Seq(OpenBrace, Sp, product, Sp, Mid, Sp, f, Sp, Colon, Sp, factors,
            Sp, CloseBrace);
        Formula span = Seq(Operatorname, Grp(F.Id("span")), Underscore, Grp(Complex), Parenthesized(words));
        return All("S", GeneratorSets, All("k", Naturals, Equal(WordSpan(s, k), span)));
    }

    private static Formula ResultFormula()
    {
        Formula s = F.Id("S"), k = F.Id("k"), m = F.Id("m");
        Formula fullAtM = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("m"),
            Naturals, And(Positive(m), Equal(WordSpan(s, m), MatrixSpace)));
        Formula universal = All("S", GeneratorSets,
            new Formula.Logic(fullAtM, FormulaLogicOperator.Implies, Equal(WordSpan(s, k), MatrixSpace)));
        Formula lengths = Seq(OpenBrace, Sp, k, Sp, InMacro, Sp, Naturals, Sp, Mid, Sp,
            And(Positive(k), universal), Sp, CloseBrace);
        return Call("IsLeast", lengths, D(7));
    }

    private static Formula Positive(Formula k) =>
        new Formula.Relation(D(0), FormulaRelationOperator.LessThan, k);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
}
