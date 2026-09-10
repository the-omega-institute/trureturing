using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels.ProjectionDiagnostics;

internal sealed class MonitoredReturnConservationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Monitored return amplitudes and survival probabilities obey exact finite conservation.",
        H("Monitored Return Conservation"),
        Blocks(Describe.Lean(
            DescribeId.Create("monitored-return-conservation"),
            DeclarationHandle.Create("D5/S3/QuantumChannels/ProjectionDiagnostics/MonitoredReturnConservation.monitored_return_conservation"),
            H("Monitored stepwise and finite conservation"),
            StatementSource.FromAuthor(ConservationFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Let U be unitary on a complex Hilbert space and v a unit vector. "
                + "P is the orthogonal projection onto the span of v, and Q is I minus P. "
                + "The monitored history at time n is (QU) to the nth power applied to v; "
                + "s is its squared norm. At positive time n, the return amplitude is "
                + "the inner product of v with U applied to the previous monitored history, "
                + "and p is its squared modulus. The repository interface applies Mathlib's "
                + "orthogonal projection norm identity and finite telescoping sum."))),
            DescribeRole.Theorem))));

    private static Formula ConservationFormula()
    {
        Formula n = F.Id("n");
        Formula horizon = F.Id("N");
        Formula next = Seq(n, Plus, D(1));
        Formula s(Formula index) => Seq(F.Id("s"), Underscore, Grp(index));
        Formula p(Formula index) => Seq(F.Id("p"), Underscore, Grp(index));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        return Disp(Seq(
            s(D(0)), Eq, D(1), Comma, Quad,
            Forall, Sp, n, Sp, InMacro, Sp, naturals, Comma, Sp,
            p(next), Eq, s(n), Minus, s(next), Comma, Quad,
            Forall, Sp, horizon, Sp, InMacro, Sp, naturals, Comma, Sp,
            Sum, Underscore, Grp(n, Eq, D(0)), Caret, Grp(horizon, Minus, D(1)),
            p(next), Plus, s(horizon), Eq, D(1)));
    }
}
