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
            Describe.Lean(
                DescribeId.Create("mixed-half-weights-sharp"),
                DeclarationHandle.Create(Prefix + "mixed_half_weights_sharp"),
                H("Attainment and normalization for even h"),
                StatementSource.FromAuthor(SharpStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For even h, choose doubled half-integer weights equal to the first h powers of "
                        + "three. Put W equal to the number of even codes. The other t weights are W times "
                        + "the first t powers of three. The total pair mass is even, and one plus that "
                        + "total equals W times three to the power t.")),
                    Paragraph(Text(
                        "For a level k, divide by W. The remainder is encoded by the even word of value "
                        + "twice the remainder, and the quotient by an unrestricted word multiplied by W. "
                        + "The combined mass is k. This supplies every level up to the total."))),
                DescribeRole.Theorem))));

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

    private static Formula SharpStatement()
    {
        Formula h = F.Id("h");
        Formula t = F.Id("t");
        Formula total = Call("Total", h, t);
        return Disp(Seq(Forall, Sp, h, Sp, t, Comma, Sp, Call("Even", h), Sp, Rightarrow, Sp,
            total, Sp, Plus, Sp, D(1), Sp, Eq, Sp,
            Frac, Grp(D(3), Caret, h, Sp, Plus, Sp, D(1)), Grp(D(2)), Sp, Cdot, Sp,
            D(3), Caret, t, Sp, Land, Sp, Call("Even", total), Sp, Land, Sp,
            Call("IntegerCoverage", h, t, Seq(total, Sp, Plus, Sp, D(1)))));
    }
}
