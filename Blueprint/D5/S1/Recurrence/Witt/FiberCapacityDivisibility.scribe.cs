using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Witt;

internal sealed class FiberCapacityDivisibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A consecutive fiber polynomial has the factor X plus one exactly when its capacity is even.",
        H("Fiber Capacity and Divisibility"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fiber-capacity-controls-divisibility"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/Witt/FiberCapacityDivisibility."
                        + "one_add_x_dvd_fiber_polynomial_iff"),
                H("Even capacity is equivalent to the alternating factor"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("m"), Comma, Sp, F.Id("c"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Open, D(1), Plus, F.Id("X"), Close, Sp, Mid, Sp,
                    F.Id("X"), Caret, Grp(F.Id("m")), Sp,
                    Sum, Underscore, Grp(F.Id("i"), Lt, F.Id("c")), Sp,
                    F.Id("X"), Caret, Grp(F.Id("i")), Sp,
                    Iff, Sp, D(2), Sp, Mid, Sp, F.Id("c")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Evaluation at minus one turns the consecutive fiber polynomial into "
                            + "an alternating geometric sum. Its value vanishes exactly at even "
                            + "capacity, independently of the starting exponent.")),
                    Paragraph(Text(
                        "The proof combines Mathlib's linear-factor criterion, polynomial "
                            + "geometric-sum evaluation, and exact parity formula for a geometric "
                            + "sum at minus one. No duplicate factor theorem is introduced.")),
                    Paragraph(Text(
                        "This closes only the capacity-divisibility mechanism in source theorem "
                            + "6.49. It does not assert the explicit g-row identities, the Witt "
                            + "exponent tables, the finite-window row-four tail, or the Sturmian "
                            + "classification stated elsewhere in that atom."))),
                DescribeRole.Theorem))));
}
