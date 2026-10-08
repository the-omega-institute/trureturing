using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.BalancedThreshold;

internal sealed class BalancedThresholdDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bispecial factors descend through the characteristic mechanical block coding.",
        H("Mechanical bispecial descent"),
        Blocks(Describe.Lean(
            DescribeId.Create("balanced-threshold-mechanical-bispecial-descent"),
            DeclarationHandle.Create(
                "D5/S1/Words/BalancedThreshold/"
                + "BalancedThresholdDescent.mechanical_bispecial_descent"),
            H("Shorter bispecial factors with exact occurrence correspondence"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every frequency alpha strictly between zero and one half, "
                + "a nonempty bispecial factor of the characteristic mechanical word "
                + "is the image of a strictly shorter bispecial factor of the ratio "
                + "word at alpha/(1-alpha), followed by one false letter. The coding "
                + "maps false to [false] and true to [false,true]. Inductive unique "
                + "decoding with the terminal false letter identifies every occurrence "
                + "through its majority rank. Both special extensions transfer to the "
                + "ratio word. The physical endpoint of each lifted occurrence is "
                + "identified exactly. Rational frequencies and the empty descended "
                + "factor are included. This is one descent step; the full "
                + "continued-fraction return classification remains a separate obligation."))),
            DescribeRole.Theorem))));
}
