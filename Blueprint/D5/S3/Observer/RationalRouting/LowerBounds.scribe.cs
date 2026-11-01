using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.RationalRouting;

internal sealed class LowerBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original recovery requires at least two acquired actions and at least four preset actions.",
        H("Incompatible attained grids"),
        Blocks(
            Paragraph(Text("Use the same positive-rational source, chronological L and R, two-band prior, complete dyadic floor ports and finite instruction-run relation. An action cap bounds the final chronological word on every terminating prior run. A preset controller's final words follow one common schedule: letter k equals schedule(k). Pauses, local computations, exponents, read counts and early stopping remain report-dependent. The lower bound even allows arbitrary, rather than just effectively generated, public schedules.")),
            Describe.Lean(DescribeId.Create("original-rational-action-lower-bounds"),
                DeclarationHandle.Create("D5/S3/Observer/RationalRouting/LowerBounds.original_action_lower_bounds"),
                H("Universal action lower bounds"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every state type, output type, common initial state and deterministic instruction function, let the original target be injective on the whole prior and require finite correct completion everywhere. Every uniform action cap h is then at least 2. If all completed words follow one common public schedule, h is at least 4. Quantification is over all those controllers; it is not restricted to a displayed implementation or an assumed replay certificate.")),
                    Paragraph(Text("Every endpoint run must contain an actual grid read. At lengths at most three the only qualifying prefixes for 1/6 are LL and LLR, and those for 2/3 are RL and RLR. The rational denominator at a grid divides a power of two. Exact arithmetic for all fifteen words of lengths zero through three leaves precisely those routes; every excluded denominator has an odd prime divisor. Prefixes at actual reads remain prefixes of the final word, including across arbitrary local steps and adaptive reads.")),
                    Paragraph(Text("No qualifying prefix has length zero or one. With at most three actions the endpoint 1/6 therefore requires first letter L, whereas 2/3 requires first letter R. A common preset schedule cannot have both first letters. This obstruction concerns actual noncommuting source actions and an injective original output; a band bit alone is not the target."))),
                DescribeRole.Theorem))));

    private static Formula Statement() => Disp(Seq(
        Operatorname, Grp(F.Id("Correct")), Open, F.Id("C"), Comma, F.Id("V"), Close,
        Land, Sp, Operatorname, Grp(F.Id("InjOn")), Open, F.Id("V"), Comma, F.Id("P"), Close,
        Longrightarrow, Sp,
        Open, Forall, Sp, F.Id("h"), Comma, Sp, Call("Cap", F.Id("C"), F.Id("h")), Longrightarrow, D(2), Leq, Sp, F.Id("h"), Close,
        Land, Sp,
        Open, Forall, Sp, F.Id("v"), Comma, F.Id("h"), Comma, Sp,
        Call("Preset", F.Id("C"), F.Id("v")), Land, Call("Cap", F.Id("C"), F.Id("h")), Longrightarrow, D(4), Leq, Sp, F.Id("h"), Close));
}
