using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SubsetSpectrum;

internal sealed class DigitDiagonalCapacityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SubsetSpectrum/DigitDiagonalCapacity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A bound on integer masses represented by two bounded digits.",
        H("Counting integer levels along digit diagonals"),
        Blocks(Describe.Lean(
            DescribeId.Create("integer-levels-bounded-by-diagonal-code-count"),
            DeclarationHandle.Create(Prefix + "integral_range_le_diagonal_codes"),
            H("The integer-level count is bounded by the diagonal code count"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let k and n be natural numbers. Suppose two real weights a and z sum to c divided "
                    + "by b, where c and b are coprime natural numbers and b is positive. Coverage(k,n,a,z) "
                    + "means each integer level from zero through n minus one is a weighted sum of "
                    + "two digits between zero and k. DiagonalCodeCount(k,b) is the number of distinct "
                    + "triples obtained from all such digit pairs. The first two entries are the two "
                    + "truncated differences of the digits. The third entry is their minimum divided "
                    + "by b, rounded down.")),
                Paragraph(Text(
                    "The first two entries determine the diagonal. Two representations of integers on the "
                    + "same diagonal differ in mass by c divided by b times the change of position. "
                    + "Coprimality forces those positions to agree modulo b. Matching quotients then give "
                    + "the same position and the same represented integer. Choosing one representation "
                    + "per covered integer injects the interval into the finite set of codes.")),
                Paragraph(Text(
                    "A diagonal of length L contributes the ceiling of L divided by b codes. For "
                    + "k equal to eight and b equal to four, the central diagonal contributes three "
                    + "and the remaining diagonals contribute twenty-four."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Statement()
    {
        Formula k = F.Id("k");
        Formula n = F.Id("n");
        Formula b = F.Id("b");
        Formula c = F.Id("c");
        Formula a = F.Id("a");
        Formula z = F.Id("z");
        return Disp(Seq(Forall, Sp, k, Sp, n, Sp, b, Sp, c, Sp, a, Sp, z, Comma, Sp,
            D(0), Sp, Lt, Sp, b, Sp, Land, Sp, Call("Coprime", c, b), Sp, Land, Sp,
            a, Plus, z, Eq, new Formula.Fraction(c, b), Sp, Land, Sp, Call("Coverage", k, n, a, z),
            Sp, Rightarrow, Sp, n, Le, Sp, Call("DiagonalCodeCount", k, b)));
    }
}
