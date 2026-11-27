using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class PowerResidueRecursionFiveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every index at which OEIS A374911 takes value five is even.",
        H("Parity of the Indices at Value Five in OEIS A374911"),
        Blocks(Describe.Lean(
            DescribeId.Create("a374911-value-five-even"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Congruence/PowerResidueRecursionFive.oeisA374911_valueFive_even"),
            H("Value five forces an even index"),
            StatementSource.FromAuthor(ResultFormula()),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/ArithSums/oeis2024a374911")),
            Blocks(Paragraph(Text(
                "The sequence is the power-residue recursion with initial value one. "
                + "The classifications at one through four force the ordered recursive values "
                + "to be three and two when the sum is five. Equivalently, the remainder "
                + "of three to the index is one, and the remainder of two to the index "
                + "is a positive power of two, in each case modulo the index. "
                + "For an index greater than one, if a base raised to the index is congruent "
                + "to one modulo the index, its order modulo the least prime factor divides "
                + "both the index and that prime minus one. These two numbers are coprime. "
                + "The base is therefore one modulo the least prime factor. Base two "
                + "rules out a left recursive value of two. Base three forces the least "
                + "prime factor to be two."))),
            DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var valueFive = new Formula.Relation(Call("seq", n), FormulaRelationOperator.Equal, D(5));
        var even = new Formula.Relation(D(2), FormulaRelationOperator.Divides, n);
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"),
            Seq(Mathbb, Grp(F.Id("N"))),
            new Formula.Logic(valueFive, FormulaLogicOperator.Implies, even)));
    }
}
