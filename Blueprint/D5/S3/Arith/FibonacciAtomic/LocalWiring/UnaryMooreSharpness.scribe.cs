using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.LocalWiring;

internal sealed class UnaryMooreSharpnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/LocalWiring/UnaryMooreSharpness.";
    private static Formula K => F.Id("K");
    private static Formula V => F.Id("v");
    private static Formula I => F.Id("i");
    private static Formula At(string id, Formula i) => new Formula.Subscript(F.Id(id), i);
    private static Formula Sharp => Seq(
        Open, D(1), Le, Sp, K, Sp, Land, Sp, D(0), Le, Sp, V, Lt, D(2), K, Minus, D(1), Close,
        Sp, Implies, Sp, Exists, Sp, F.Id("s"), Comma, F.Id("t"), Sp, InMacro, Sp,
        new Formula.Subscript(Seq(Mathcal, Grp(F.Id("M"))), K), Comma, Sp,
        Open, Forall, Sp, I, Lt, V, Comma, Sp, At("s", I), Eq, At("t", I), Close,
        Sp, Land, Sp, At("s", V), Neq, Sp, At("t", V));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At every shorter length two unary Moore sources with at most K states " +
        "can agree throughout the prefix and disagree on its next output. " +
        "Thus 2K−1 is the least uniform sufficient prefix length.",
        H("Sharp uniform prefix separation for unary Moore sources"),
        Blocks(Describe.Lean(
            DescribeId.Create("gpo-unary-moore-uniform-sharpness"),
            DeclarationHandle.Create(Prefix + "unary_moore_sharpness"),
            H("Actual unary witness machines for every shorter prefix"),
            StatementSource.FromAuthor(Disp(Sharp)),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Both tables are autonomous and unary, with one actual start state and " +
                    "one Boolean output per state. The initial state's output is index zero. " +
                    "The public bound K is positive and each table uses at most K states.")),
                Paragraph(Text(
                    "At K=1 the one-state machines have opposite constant labels. Otherwise " +
                    "use a K-cycle and a source with a transient state zero feeding the " +
                    "cycle on states one through K−1. Both first emit one at K−1, and the " +
                    "second source, but not the first, emits one at 2K−2.")),
                Paragraph(Text(
                    "For the requested cut v, advance each start along its own actual " +
                    "transition by 2K−2−v. The shifted trajectories agree at every index " +
                    "below v and emit opposite bits at v. Together with the frozen upper " +
                    "bound this proves the uniform threshold, not a fixed hard pair across " +
                    "all cuts or a statement about comparative observation costs."))),
            DescribeRole.Theorem))));
}
