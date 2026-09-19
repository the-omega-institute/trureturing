using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator.TranslationEnergy.Polynomial;

internal sealed class HornerIntervalsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rational Horner interval factories.",
        H("Rational Horner interval factories"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("polynomial-hornerintervals-horner-check"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/Polynomial/HornerIntervals.horner_check"),
                H("Structural checker acceptance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every ordered rational interval and finite coefficient list, the recursively constructed Horner expression passes the annotated rational expression checker. The singleton case is a constant expression; longer lists multiply the tail by the input and add the leading coefficient."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("polynomial-hornerintervals-horner-interval-bounds"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/Polynomial/HornerIntervals.horner_interval_bounds"),
                H("Amplitude and width budgets"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("On an interval [a,b] contained in [-B,B], the Horner enclosure for coefficients cs lies in [-A(cs),A(cs)] and has width at most D(cs)(b-a). The recurrences are A(c::cs)=|c|+B A(cs) and D(c::cs)=A(cs)+B D(cs), with zero empty-list budgets."))),
                DescribeRole.Theorem)),
        []));
}
