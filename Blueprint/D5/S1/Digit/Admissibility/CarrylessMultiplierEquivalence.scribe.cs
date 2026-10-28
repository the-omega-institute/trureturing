using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Admissibility;

internal sealed class CarrylessMultiplierEquivalenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/Admissibility/CarrylessMultiplierEquivalence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Digit/oeis2026a115801");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two ordinary versus binary carryless multiplier equations define the same natural numbers.",
        H("Equivalent Binary Carryless Multiplier Conditions"),
        Blocks(
            Paragraph(Text("Every variable ranges over the natural numbers, including zero. "
                + "Ordinary multiplication and binary carryless multiplication are different operations. "
                + "The carryless product C uses the binary digits as polynomial coefficients over GF(2). Bit(n,i) is the i-th binary digit, indexed from zero at the least significant bit, and has value zero or one.")),
            Describe.Lean(DescribeId.Create("carryless-convolution-product"),
                DeclarationHandle.Create(Prefix + "carryless"), H("Binary convolution"),
                StatementSource.FromAuthor(ConvolutionFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For each degree t, the sum runs through all pairs i and t-i "
                    + "of nonnegative indices. Taking its remainder modulo two gives the output digit. "
                    + "Finite binary support makes these digits the expansion of a unique natural number."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("carryless-multiplier-equivalence"),
                DeclarationHandle.Create(Prefix + "result"), H("The two conditions agree"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A binary digit step records the ordinary multiplication carry "
                    + "and the remaining exclusive-OR mask. A finite relation between the two pairs of "
                    + "states has matching terminal conditions and is closed under both input digits. "
                    + "Binary induction therefore establishes both implications for every natural number. "
                    + "There is no upper bound on the input; at zero both equalities read zero equals zero."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a115801-carryless-multiplier-equivalence"),
                    ResolutionKind.Proved)))));

    private static Formula ConvolutionFormula()
    {
        var u = F.Id("u"); var k = F.Id("k"); var t = F.Id("t"); var i = F.Id("i");
        var summand = Multiply(Call("bit", u, i), Call("bit", k,
            new Formula.Binary(t, FormulaBinaryOperator.Subtract, i)));
        var sum = Seq(new Formula.Subscript(Sum, Seq(D(0), Sp, Le, Sp, i, Sp, Le, Sp, t)), Sp, summand);
        return Disp(Universal("u", Universal("k", Universal("t",
            Equal(Call("bit", Call("C", u, k), t), Call("mod", sum, D(2)))))));
    }

    private static Formula ResultFormula()
    {
        var k = F.Id("k");
        return Disp(Universal("k", new Formula.Logic(
            Equal(Multiply(D(9), k), Call("C", D(2, 5), k)), FormulaLogicOperator.Iff,
            Equal(Multiply(D(1, 5), k), Call("C", D(1, 9), k)))));
    }
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [..args]);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Universal(string name, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), F.Id("Nat"), body);
}
