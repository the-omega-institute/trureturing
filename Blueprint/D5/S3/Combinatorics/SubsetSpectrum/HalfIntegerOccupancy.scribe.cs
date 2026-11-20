using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SubsetSpectrum;

internal sealed class HalfIntegerOccupancyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SubsetSpectrum/HalfIntegerOccupancy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parity limits integer mass coverage when some ternary weights are half-integers.",
        H("Integer coverage by half-integer weights"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mixed-half-weights-bound"),
                DeclarationHandle.Create(Prefix + "mixed_half_weights_bound"),
                H("Integer coverage bound with two kinds of weights"),
                StatementSource.FromAuthor(BoundStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let h doubled weights be odd integers and let t other weights be integers. "
                        + "Every weight has a ternary occupancy. If the dot products realize every integer "
                        + "level from zero to L minus one, the count of these levels is bounded by the "
                        + "number of even ternary words on h coordinates times three to the power t.")),
                    Paragraph(Text(
                        "An integer mass forces the sum of the first h digits to be even. Ternary coding "
                        + "preserves parity because the base is odd. The even code values run from zero "
                        + "through the largest even number below three to the power h. Calibration makes "
                        + "the map of levels to the two occupancy words injective."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "To attain the bound for even h, take doubled half-integer weights equal to the first "
                + "h powers of three. Let W be the number of even ternary codes. Take the remaining "
                + "t integer weights to be W times the first t powers of three. One plus the total "
                + "pair mass is W times three to the power t. The total is even.")),
            Paragraph(Text(
                "The quotient and remainder on division by W give the two occupancy words, with "
                + "the remainder encoded at twice its value. For a positive total, divide the weights "
                + "by that total. At the midpoint select one seed per pair. Extend the lower events "
                + "by swapping pairs and taking complements.")))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula BoundStatement()
    {
        Formula h = F.Id("h");
        Formula t = F.Id("t");
        Formula levels = F.Id("L");
        return Disp(Seq(Forall, Sp, h, Sp, t, Sp, levels, Comma, Sp,
            Call("IntegerCoverage", h, t, levels), Sp, Rightarrow, Sp,
            levels, Sp, Le, Sp, Frac, Grp(D(3), Caret, h, Sp, Plus, Sp, D(1)), Grp(D(2)),
            Sp, Cdot, Sp, D(3), Caret, t));
    }

}
