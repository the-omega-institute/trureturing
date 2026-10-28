using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Admissibility;

internal sealed class CarrylessSevenFiveEquivalenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/Admissibility/CarrylessSevenFiveEquivalence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Digit/oeis2025a115770");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Seven and five define equivalent ordinary versus binary carryless multiplier conditions.",
        H("Seven and Five Carryless Multiplier Equivalence"),
        Blocks(
            Paragraph(Text("All variables range over the natural numbers, including zero. "
                + "C(u,k) denotes binary coefficient convolution over GF(2): its bit of degree t "
                + "is the parity of the sum of bit(u,i) times bit(k,t-i) for 0 <= i <= t. "
                + "Multiplication outside C is ordinary natural-number multiplication.")),
            Describe.Lean(DescribeId.Create("seven-five-carryless-equivalence"),
                DeclarationHandle.Create(Prefix + "result"), H("The two equations agree"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A state consists of the ordinary multiplication carry and "
                    + "the remaining exclusive-OR mask, or a rejecting state. Starting from the pair "
                    + "of zero carries and zero masks, fifteen paired states are closed under reading "
                    + "either binary digit from least to most significant. At every pair, the two "
                    + "equations have the same truth value when the remaining input is zero. "
                    + "The digit-step equivalence and binary induction give the equivalence for "
                    + "every natural input. Thus the finite relation establishes an unbounded "
                    + "statement; at zero, both equations are zero equals zero."))),
                DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var k = F.Id("k");
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("k"),
            F.Id("Nat"), new Formula.Logic(
                Equal(Multiply(D(7), k), Call("C", D(1, 1), k)), FormulaLogicOperator.Iff,
                Equal(Multiply(D(5), k), Call("C", D(1, 3), k)))));
    }
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [..args]);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
