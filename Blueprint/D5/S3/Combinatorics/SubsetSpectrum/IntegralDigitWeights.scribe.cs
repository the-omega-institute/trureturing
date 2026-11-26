using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SubsetSpectrum;

internal sealed class IntegralDigitWeightsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real digit weights have small integral multiples once calibrated levels exceed the capacity of one fewer coordinate.",
        H("Integral multiples of digit weights"),
        Blocks(Describe.Lean(
            DescribeId.Create("integral-multiple-of-capacity-gap"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/SubsetSpectrum/IntegralDigitWeights.exists_integral_multiple_of_capacity_gap"),
            H("Integral multiples from a strict count bound"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let J be a finite coordinate type. Suppose the integers from zero through L minus one "
                    + "are all represented by dot products of real weights with digit vectors in Fin b. "
                    + "If L exceeds the number of vectors on all but one coordinate, each weight has an "
                    + "integral multiple by some positive integer strictly below b.")),
                Paragraph(Text(
                    "Fix one coordinate and project every calibrated digit vector to the other coordinates. "
                    + "The strict count bound prevents injectivity. Two distinct integer levels with the same "
                    + "projection differ by a nonzero multiple of the weight at the deleted coordinate. "
                    + "The multiplier is the absolute difference of the two digits, so it is less than b.")),
                Paragraph(
                    Text("With two digit values and the strict count bound, the weight itself is an integer. "
                        + "With three digit values and the strict count bound, twice the weight is an integer. "
                        + "In an even-denominator covariant grid with r exchanged pairs, scale the weights "
                        + "by the denominator m and require "),
                    Math(Seq(F.Id("m"), Sp, Plus, Sp, D(1), Sp, Gt, Sp,
                        D(3), Caret, Grp(F.Id("r"), Sp, Minus, Sp, D(1)))),
                    Text("."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Statement()
    {
        Formula coords = F.Id("J");
        Formula digitBase = F.Id("b");
        Formula levels = F.Id("L");
        Formula weight = F.Id("w");
        Formula digits = F.Id("x");
        Formula coordinate = F.Id("j");
        Formula multiple = F.Id("d");
        Formula integer = F.Id("z");
        Formula exponent = Grp(Call("card", coords), Sp, Minus, Sp, D(1));
        return Disp(Seq(
            Forall, Sp, coords, Sp, digitBase, Sp, levels, Sp, weight, Sp, digits, Comma, Sp,
            Call("Calibrated", digits, weight), Sp, Land, Sp,
            digitBase, Caret, exponent, Sp, Lt, Sp, levels, Sp, Rightarrow, Sp,
            Forall, Sp, coordinate, Colon, coords, Comma, Sp, Exists, Sp, multiple, Sp, integer, Comma, Sp,
            D(0), Sp, Lt, Sp, multiple, Sp, Land, Sp, multiple, Sp, Lt, Sp, digitBase, Sp, Land, Sp,
            multiple, Sp, Cdot, Sp, Call("w", coordinate), Sp, Eq, Sp, integer));
    }
}
