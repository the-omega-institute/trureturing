using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Automata;

internal sealed class PrimeHistoryNormalFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete guarded prime histories have canonical interval-translation semantics.",
        H("Prime History Normal Forms"),
        Blocks(
            Paragraph(Text(
                "A true command raises the excursion by one, and a false command lowers it "
                + "by one. The frozen word coordinates are the least and greatest "
                + "prefix displacements, including the empty prefix, and the final displacement. "
                + "These are not independently selected edge witnesses.")),
            Describe.Lean(
                DescribeId.Create("prime-history-evaluate-injective"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/PrimeHistoryNormalForm.evaluate_injective"),
                H("Evaluation determines an interval translation"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("Injective"), Open, F.Id("evaluate"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The defined and undefined inputs recover the source interval. Evaluating "
                    + "its lower endpoint then recovers the translation shift, while the empty "
                    + "map is distinguished from every nonempty interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-history-realize-signature"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/PrimeHistoryNormalForm.realize_signature"),
                H("The explicit realization has the prescribed signature"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("low"), Open, F.Id("realize"), Open, F.Id("t"), Close, Close,
                    Sp, Eq, Sp, Neg, Sp, F.Id("lo"), Open, F.Id("t"), Close,
                    Sp, Land, Sp,
                    F.Id("high"), Open, F.Id("realize"), Open, F.Id("t"), Close, Close,
                    Sp, Eq, Sp, F.Id("a"), Sp, Minus, Sp, F.Id("hi"), Open, F.Id("t"), Close,
                    Sp, Land, Sp, F.Id("displacement"), Open, F.Id("realize"), Open,
                    F.Id("t"), Close, Close, Sp, Eq, Sp, F.Id("shift"), Open, F.Id("t"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The three monotone legs visit the prescribed lower and upper extremes "
                    + "and finish at the prescribed translation shift. Their nonnegative "
                    + "lengths follow from the interval-map bounds."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-history-constructive-realization"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/PrimeHistoryNormalForm.normal_surjective"),
                H("Every admissible interval translation is actually realizable"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("range"), Open, F.Id("normal"), Open, F.Id("a"), Close, Close,
                    Sp, Eq, Sp, F.Id("allIntervalMaps")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a nonempty form [l,u] with shift d, run l divisions, a-u+l "
                    + "multiplications and a-u-d divisions. Its three extrema are derived "
                    + "from the actual concatenation signatures. The admissibility conditions "
                    + "prove that all lengths are nonnegative. Capacity+1 multiplications "
                    + "realize the empty map. Thus the carrier has neither unrealized forms "
                    + "nor multiple encodings of the empty behavior."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The three-invariant word structure is classical: the monogenic free inverse "
                + "monoid uses precisely a visited interval and a terminal displacement. "
                + "See Silva, arXiv:2205.08854v2, Section 2.2, equation (1). The present "
                + "source establishes its concrete bounded-prime execution and realization, "
                + "not a new discovery of that abstract normal form or a full formalization "
                + "of the free inverse monoid universal property."))),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Factorization/Automata/WordExcursionLowerBound"))]));
}
