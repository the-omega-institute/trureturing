using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class OccupiedLogEnvelopeDocument : IScribeDocumentDefinition
{
    private static Formula T => F.Id("t");
    private static Formula Z => F.Id("z");
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Integers => Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula Envelope() => Disp(Seq(
        Exists, Sp, T, InMacro, Sp, Reals, Comma, Quad, D(0), Lt, T, Sp, Land, Sp,
        Open, Forall, Sp, Z, InMacro, Sp, Integers, Comma, Quad, Sp,
        T, Cdot, Sp, Call("discrepancyProfile", Z), Le, Sp, Call("rawOccupation", Z),
        Quad, Land, Quad, Frac, Grp(D(2)), Grp(F.Id("a")), Cdot, Sp, T, Cdot, Sp,
        Call("discrepancyProfile", Z), Le, Sp, Call("occupation", Z), Close));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One positive logarithmic scale bounds both actual occupation masses at every integer.",
        H("Global logarithmic lower envelope for actual occupation"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-raw-and-normalized-log-envelope"),
            DeclarationHandle.Create(
                "D5/S1/Words/Patterns/Separable/OccupiedLogEnvelope.actual_raw_occupation_log_envelope"),
            H("A common scale for raw and normalized mass"),
            StatementSource.FromAuthor(Envelope()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The discrepancy profile is the reciprocal of the product of the square root "
                    + "and logarithm of two plus the absolute position. It is strictly positive and "
                    + "is largest at the origin, which supplies one upper bound on the whole integer lattice.")),
                Paragraph(Text(
                    "Both the compensated gain and the quadratic cost use the same two neighbors at each "
                    + "positive jump length. The fixed point comparison balances the linear gain with "
                    + "the quadratic cost on the tails and uses the positive forcing in the finite core. "
                    + "Multiplication by the positive normalizing factor carries the raw bound to "
                    + "normalized occupation without changing the chosen scale."))),
            DescribeRole.Theorem))));
}
