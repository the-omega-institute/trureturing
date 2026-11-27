using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.LocalWiring;

internal sealed class PhysicalBirthClockDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/FibonacciAtomic/LocalWiring/PhysicalBirthClock.";

    private static Formula N => F.Id("n");
    private static Formula T => F.Id("t");
    private static Formula Sub(string head, Formula index) => Seq(F.Id(head), Underscore, Grp(index));
    private static Formula Fib(Formula index) => Sub("F", index);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fixed source stream advances once at each actual beta split. The birth clock "
        + "records those events in the physical order of the old leaves, not the order of "
        + "semantic occurrences or a physical duration.",
        H("Physical birth clock of the fixed locally wired source"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gpo-fixed-source-physical-birth-clock"),
                DeclarationHandle.Create(Prefix + "physical_birth_clock"),
                H("Ordered physical births and their Fibonacci clock"),
                StatementSource.FromAuthor(Disp(Seq(
                    Sub("B", N), Eq, Sum, Underscore, Grp(Seq(T, Eq, D(2))), Caret, Grp(N),
                    Fib(Seq(T, Minus, D(1))), Eq, Fib(Seq(N, Plus, D(1))), Minus, D(1), Quad, Sp,
                    Sub("v", N), Eq, Sub("B", Seq(N, Minus, D(1))), Eq, Fib(N), Minus, D(1), Quad, Sp,
                    Sub("B", N), Minus, Sub("v", N), Eq, Fib(Seq(N, Minus, D(1)))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Start at the actual known alpha leaf with cursor zero. A round recursively "
                        + "visits only the old physical children, left before right. An old alpha "
                        + "turns into beta without requesting a bit. An old beta requests exactly "
                        + "the next source bit and places beta at a for true and at b for false. "
                        + "The two new leaves are not visited by that round.")),
                    Paragraph(Text(
                        "Each event records its one-based serial birth, its actual completed update "
                        + "number, its physical parent word, and its consumed bit. A round visits "
                        + "each old beta site just once, and the produced subtree has exactly the "
                        + "recorded orientation at that site. The accumulated list is strictly "
                        + "ordered by completed update, then by physical lexicographic address.")),
                    Paragraph(Text(
                        "The displayed mature and newest-batch identities apply for n≥2. "
                        + "The older restriction is exactly the previous cut's complete list. "
                        + "At the first two cuts, before the second update, no source bit has "
                        + "been consumed. The finite run including its tree, cursor and events "
                        + "depends only on its used prefix, not on a future source bit.")),
                    Paragraph(Text(
                        "The source stream and its start alignment are supplied premises. "
                        + "The event list is not a new observer read port. No prediction of the "
                        + "generator, incidence inverse, timing bound or physical-time claim is made."))),
                DescribeRole.Theorem))));
}
