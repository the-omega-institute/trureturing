using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal;

internal sealed class EscapeAsymptoticsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "Finite diagonal escape ratios tend to one as listing size grows.",
            H("Diagonal Escape Asymptotics"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("escape-ratio-tends-to-one"),
                    DeclarationHandle.Create("D5/S0/Diagonal/EscapeAsymptotics.escape_ratio_tendsto_one"),
                    H("The escape ratio tends to one"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Lim, Underscore, Grp(F.Id("N"), To, Infty),
                        Left, Open, D(1), Minus, Frac, Grp(F.Id("k")),
                        Grp(F.Id("n"), Caret, F.Id("N")), Right, Close,
                        Caret, F.Id("N"), Eq, D(1), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For fixed natural value count n at least two and fixed-point count "
                        + "k at most n, the N-th power of one minus k divided by n to the "
                        + "N-th power tends to one. This asymptotic statement is expressed "
                        + "as a real-valued ratio; the finite counting truth source remains "
                        + "the exact escaped-listing cardinality theorem in EscapeCount."))),
                    DescribeRole.Theorem))));
}
