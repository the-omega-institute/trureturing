using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroData;

internal sealed class PairedXiExpansionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZeroData/PairedXiExpansion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The paired logarithmic derivative expansion of xi is an explicit hypothesis.",
        H("Paired xi expansion away from poles"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("paired-xi-pole-free"),
                DeclarationHandle.Create(Prefix + "PoleFree"),
                H("Avoiding the paired spectral poles"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a positive spectrum, the pole-free set consists of "
                    + "complex points different from both i times each ordinate and its negative."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("paired-xi-expansion"),
                DeclarationHandle.Create(Prefix + "PairedXiExpansion"),
                H("A convergent paired expansion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume RH and use the positive zeta ordinate spectrum with "
                        + "analytic multiplicities. At every pole-free complex point s, require "
                        + "the sum of m times (1/(s-i gamma) + 1/(s+i gamma)) to converge to the "
                        + "logarithmic derivative of xiReading at 1/2+s.")),
                    Paragraph(Text("Here xiReading is the repository's entire completed zeta "
                        + "function. HasSum asserts convergence as well as the value of the "
                        + "paired sum. This definition introduces a hypothesis and does not "
                        + "prove that hypothesis from RH or from zero counting."))),
                DescribeRole.Definition))));
}
