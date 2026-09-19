using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator.TranslationEnergy;

internal sealed class CutoffIntervalsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spatial cutoff interval widths.",
        H("Spatial cutoff interval widths"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cutoffintervals-cutoffinterval-certificate"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/CutoffIntervals.cutoffInterval_certificate"),
                H("Two scalar endpoints"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For ordered rational arguments ta<=tb and every natural precision m, the two exact scalar intervals give an ordered enclosure contained in [0,1]. Its width is at most 9(tb-ta)+2*2^-m, using the global nine-Lipschitz bound for the smooth transition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cutoffintervals-shiftedcutoffinterval-certificate"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/CutoffIntervals.shiftedCutoffInterval_certificate"),
                H("An entire shifted cell"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive rational radius r, an ordered rational cell [a,b], rational translation c and natural precision m, the constructed interval encloses smoothTransition(2-|x+c|/r) for every real x in that cell. Its width is at most 9(b-a)/r+2*2^-m, and its endpoints remain in [0,1]."))),
                DescribeRole.Theorem)),
        []));
}
