using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class TraceMapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Per-axis admissible-word partial sums satisfy the closed golden trace-map recursion.",
H("The Per-Axis Trace-Map Recursion"),
Blocks(
            Describe.Lean(
                DescribeId.Create("per-axis-trace-map-recursion"),
                DeclarationHandle.Create("D5/S1/Recurrence/TraceMap.trace_map_recursion"),
                H("Partial sums and weights close under the trace-map recursion"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("W"), Underscore, Grp(F.Id("K"), Plus, D(1)), Eq,
                    F.Id("W"), Underscore, F.Id("K"), Plus,
                    F.Id("t"), Underscore, Grp(F.Id("K"), Plus, D(1)),
                    F.Id("W"), Underscore, Grp(F.Id("K"), Minus, D(1)),
                    Comma, Sp,
                    F.Id("t"), Underscore, Grp(F.Id("K"), Plus, D(1)), Eq,
                    F.Id("t"), Underscore, F.Id("K"),
                    F.Id("t"), Underscore, Grp(F.Id("K"), Minus, D(1))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The per-axis partial sum of bit depth K ranges over admissible "
                        + "words: sets of Zeckendorf indices from one to K with no two "
                        + "consecutive indices selected. Each index is weighted by an "
                        + "exponential reading of the two faces, the expansion variable "
                        + "against the golden ratio power and the contraction variable "
                        + "against the golden conjugate power, one past the index. The "
                        + "theorem records that these partial sums and weights close as a "
                        + "recursion pair: the sum of depth K plus two splits along its top "
                        + "bit, whose use forces the neighbouring bit empty and so leaves a "
                        + "word two depths down, while the top weight itself is the product "
                        + "of the two preceding weights.")),
                    Paragraph(Text(
                        "The first equation is pure finite combinatorics over an arbitrary "
                        + "weight sequence: the admissible words of a given depth partition "
                        + "into those avoiding the top bit, which are exactly the words one "
                        + "depth down, and those using it, which are top-bit insertions of "
                        + "words two depths down. The second equation is the golden "
                        + "instance: both golden powers satisfy the Fibonacci recurrence, "
                        + "so the exponential weights are multiplicative along consecutive "
                        + "indices. Together the pair drives the whole tower of per-axis "
                        + "partial sums from its two lowest depths, which is the "
                        + "trace-map mechanism of the source atom."))),
                DescribeRole.Theorem))));
}
