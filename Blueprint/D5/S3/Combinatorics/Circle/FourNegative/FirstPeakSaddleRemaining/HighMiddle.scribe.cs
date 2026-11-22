using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining;

internal sealed class HighMiddleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unbounded high-middle choices",
        H("The region b>c+d"),
        Blocks(
            Describe.Lean(DescribeId.Create("helper-high-middle-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HighMiddle.high_interpolate"),
                H("Interpolate the high-middle margins"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The h=0 and maximal-h charts and the t=2z boundary provide three families of four exact margins. Their sparse integer polynomials are written in Horner form and verified by ring normalization and nonnegative shifted variables. high_interpolate extends the two h endpoints, and high_arithmetic chooses the integer residue and capacities."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("helper-high-middle-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HighMiddle.high_middle_choice_exists"),
                H("All strict saddles with high middle exponent"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a>b>d>c>=2 and b>c+d, the integer construction becomes a NativeChoice through native_of_selection. The 12 polynomial margins apply to the full unbounded parameter region. Native subsequently converts its fixed-q rectangle to the physical twelve gates; this module does not identify rectangle feasibility with a physical word on its own."))), DescribeRole.Lemma),
            Paragraph(Text("These existing private declarations are consumed by the strict-saddle endpoint. This mirror documents their stated hypotheses and use; it makes no independent literature-novelty claim, no claim of a four-slot registration for every helper, and no claim to settle unrestricted four-gap J or Circle Conjecture 3.1."))), []));
}
