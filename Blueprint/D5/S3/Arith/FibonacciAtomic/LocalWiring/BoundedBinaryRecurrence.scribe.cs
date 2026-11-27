using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.LocalWiring;

internal sealed class BoundedBinaryRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/LocalWiring/BoundedBinaryRecurrence.";
    private static Formula Bound => F.Id("d");
    private static Formula Index => F.Id("i");
    private static Formula At(string id, Formula i) => new Formula.Subscript(F.Id(id), i);
    private static Formula Count => new Formula.Power(D(2), Bound);
    private static Formula Separation => Seq(
        Open, Forall, Sp, Index, Lt, D(2), Bound, Comma, Sp, At("s", Index), Eq, At("t", Index), Close,
        Sp, Implies, Sp, Open, Forall, Sp, Index, Comma, Sp, At("s", Index), Eq, At("t", Index), Close);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An authentic initial block of 2d bits determines every digit of any binary "
        + "forward-recurring stream of order at most d. Fixed finite enumeration "
        + "recovers a generator for that behavior.",
        H("Finite separation and synthesis for bounded binary recurrences"),
        Blocks(Describe.Lean(
            DescribeId.Create("gpo-bounded-binary-recurrence"),
            DeclarationHandle.Create(Prefix + "bounded_binary_recurrence"),
            H("Sufficient initial comparison and first matching forward generator"),
            StatementSource.FromAuthor(Disp(Separation)),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Both streams are actual Boolean sequences satisfying a forward binary "
                    + "recurrence at every index, with possibly different orders and coefficients. "
                    + "Both orders are at most d. The initial block starts at index zero and "
                    + "the recurrence is the finite coefficient dot product reduced modulo two.")),
                Paragraph(Text(
                    "The monic shift operator for each stream annihilates it. The two shift "
                    + "operators commute, so their product annihilates the difference. Its "
                    + "highest shift is the sum of the two orders, at most 2d. If that many "
                    + "initial differences vanish, the highest-term equation determines every "
                    + "later difference to be zero; the calculation never runs backward.")),
                Paragraph(Text(
                    "Prepend zero taps to obtain an order-d row without changing the predicted "
                    + "terminal digit. The search enumerates all "), Math(Count),
                    Text(" Boolean rows in a fixed mask order, installs the same first d observed "
                    + "bits into each one, and returns the first row whose first 2d digits match. "
                    + "A lawful word guarantees at least one match; the selected generator agrees "
                    + "at every index. At d=0 this gives the zero generator.")),
                Paragraph(Text(
                    "No minimality or invertibility is required: zero taps, transients and "
                    + "singular recurrences are allowed. This determines output behavior, not "
                    + "private coefficients, state, or original seed presentation. No sharpness, "
                    + "sampling-price or optimal-running-time claim is made."))),
            DescribeRole.Theorem))));
}
