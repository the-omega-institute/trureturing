using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Zigzag;

internal sealed class EvenPathsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Zigzag/EvenPaths.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every balanced choice with even parameter has a unique signed zero-charge path, including its antipodal terminal pair.",
        H("Even Balanced-Choice Correspondence"),
        Blocks(
            Describe.Lean(DescribeId.Create("even-charge-reflection"),
                DeclarationHandle.Create(Prefix + "evenPathReflection_charge"),
                H("Reflection negates the even path charge"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The reflection changes every start, transition, and antipodal terminal to its explicitly labelled opposite-sector partner. It negates the accumulated integer charge, yielding an equivalence of the two zero-charge path sets while preserving labelled multiplicity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("even-choice-surjectivity"),
                DeclarationHandle.Create(Prefix + "evenBalancedChoicesEquiv"),
                H("Balanced even choices are exactly zero-charge paths"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every r>=1, this is an equivalence from literal balanced Choices (2r) to the disjoint union of positive and negative EvenPaths with 3r-3 interior steps and charge zero. Its surjectivity proof decodes arbitrary choice labels using retired-vertex zero flow and the exhaustive transition table; the even terminal labels are forced at the antipode. At the remaining semitone vertex, balance forces charge zero. Injectivity is supplied by DecodedBalance."))),
                DescribeRole.Definition)), []));
}
