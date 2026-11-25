using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.LocalWiring;

internal sealed class BoundedBinaryRecurrenceSharpnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/LocalWiring/BoundedBinaryRecurrenceSharpness.";
    private static Formula Dd => F.Id("d");
    private static Formula V => F.Id("v");
    private static Formula I => F.Id("i");
    private static Formula At(string id, Formula i) => new Formula.Subscript(F.Id(id), i);
    private static Formula Sharp => Seq(
        Open, D(1), Le, Sp, Dd, Sp, Land, Sp, D(0), Le, Sp, V, Lt, D(2), Dd, Close,
        Sp, Implies, Sp, Exists, Sp, F.Id("s"), Comma, F.Id("t"), Sp, InMacro, Sp,
        new Formula.Subscript(Seq(Mathcal, Grp(F.Id("R"))), Dd), Comma, Sp,
        Open, Forall, Sp, I, Lt, V, Comma, Sp, At("s", I), Eq, At("t", I), Close,
        Sp, Land, Sp, At("s", V), Neq, Sp, At("t", V));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For each shorter cut, two actual binary recurrence streams share the " +
        "observed prefix but give opposite next digits. Together with sufficiency, " +
        "this makes twice the order bound the least uniform separating length.",
        H("Sharp uniform prefix separation for bounded binary recurrences"),
        Blocks(Describe.Lean(
            DescribeId.Create("gpo-bounded-binary-uniform-sharpness"),
            DeclarationHandle.Create(Prefix + "bounded_binary_recurrence_sharpness"),
            H("Lawful witnesses for every shorter prefix"),
            StatementSource.FromAuthor(Disp(Sharp)),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For each positive public bound d and each natural cut v below 2d, the "
                    + "executable constructor gives an actual pair of forward-recurring "
                    + "Boolean streams of order at most d. They have equal outputs at every "
                    + "index before v and first differ exactly at v.")),
                Paragraph(Text(
                    "Below d, compare zero with a single impulse at v. The impulse has "
                    + "an all-zero-tap presentation of order v+1. For d≤v<2d, put r=v−d; "
                    + "compare an impulse at r with the d-periodic stream supported on "
                    + "residue r. The periodic row copies its zero-lag input forward by d. "
                    + "Before v both streams have their sole one at r, and only the "
                    + "periodic stream has a one at v.")),
                Paragraph(Text(
                    "The uniform separation characterization uses the frozen sufficient "
                    + "bound: for positive d a length works for all legal pairs exactly "
                    + "when it is at least 2d. It does not require one fixed pair to oppose "
                    + "all shorter cuts, infer any individual stream's least order, or "
                    + "price paid observations."))),
            DescribeRole.Theorem))));
}
