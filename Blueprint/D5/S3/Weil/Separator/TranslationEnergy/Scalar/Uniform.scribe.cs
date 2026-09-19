using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator.TranslationEnergy.Scalar;

internal sealed class UniformDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cutoff acceptance at every binary precision.",
        H("Cutoff acceptance at every binary precision"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("scalar-uniform-checkcutofflogistic-all-precision"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/Scalar/Uniform.checkCutoffLogistic_all_precision"),
                H("Uniform finite Taylor depth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every rational t and natural m, the exact rational cutoff checker succeeds with Taylor depth 4m+4. Its endpoints are ordered, lie in [0,1], and differ by at most 2^-m.")),
                    Paragraph(Text("The Taylor factorial estimate controls the scaled exponential width uniformly. The construction uses exact rational arithmetic, endpoint cases and reflection, and requires no supplied success hypothesis."))),
                DescribeRole.Theorem)),
        []));
}
