using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class FirstOffLineHeightDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/FirstOffLineHeight.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strip-bounded off-line zeros of a nonzero entire function have a first positive height.",
        H("First Off-Line Height"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-off-line-heights"),
                DeclarationHandle.Create(Prefix + "positiveOffLineHeights"),
                H("Positive off-line heights"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This set records the positive imaginary parts of zeros whose real part "
                        + "differs from the proposed midline."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("first-off-line-height-exists"),
                DeclarationHandle.Create(Prefix + "first_off_line_height_exists"),
                H("Existence of the first off-line height"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The theorem makes explicit the bounded-strip hypothesis used by the "
                            + "source's compact-rectangle argument. Entirety alone is insufficient: "
                            + "zeros can escape horizontally while their positive heights tend to "
                            + "zero.")),
                    Paragraph(Text(
                        "A supplied nonzero value rules out the identically zero function. Mathlib's "
                            + "isolated-zero theorem makes the zero set codiscrete, so its intersection "
                            + "with a compact ball is finite.")),
                    Paragraph(Text(
                        "Starting from one positive off-line height, the proof restricts to heights "
                            + "below it. The strip bound puts all corresponding zeros in one compact "
                            + "ball, and the minimum of the resulting nonempty finite set is the "
                            + "required first height."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula function = F.Id("F");
        Formula midline = F.Id("c");
        Formula bound = F.Id("B");
        Formula point = F.Id("z");
        Formula witness = F.Id("w");
        Formula height = F.Id("t");
        Formula first = F.Id("T");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula heights = Call("H", function, midline);

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, function, Colon, Sp, complex, Sp, To, Sp, complex, Comma, Sp,
                midline, Comma, Sp, bound, Colon, Sp, real, Comma, Sp,
                witness, Colon, Sp, complex, Comma),
            Seq(Apply(function, witness), Sp, Neq, Sp, D(0), Sp, Land, Sp,
                D(0), Sp, Leq, Sp, bound, Comma),
            Seq(Open, Forall, Sp, point, Comma, Sp,
                Apply(function, point), Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp,
                new Formula.Absolute(Call("re", point)), Sp, Leq, Sp, bound, Close, Sp,
                Land, Sp, Call("Entire", function), Sp, Land, Sp,
                Call("Nonempty", heights), Sp, Rightarrow),
            Seq(Exists, Sp, first, InMacro, Sp, heights, Comma, Sp,
                Forall, Sp, height, InMacro, Sp, heights, Comma, Sp,
                first, Sp, Leq, Sp, height, Dot),
        ]));
    }
}
