using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Dynamics;

internal sealed class FiniteNoFixedPointOrbitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every orbit of a finite fixed-point-free map enters a nontrivial cycle.",
        H("Finite No-Fixed-Point Orbits"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-fixed-point-free-orbits-enter-nontrivial-cycles"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Dynamics/FiniteNoFixedPointOrbit."
                        + "finite_no_fixed_point_orbit_eventually_periodic"),
                H("Finite fixed-point-free orbits enter nontrivial cycles"),
                StatementSource.FromAuthor(PeriodFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be a finite state carrier, T a self-map without fixed points, "
                            + "and x0 an initial state. There are a tail index mu and a period "
                            + "p whose sum is no larger than the number of states.")),
                    Paragraph(Text(
                        "The period is at least two, and every time at or after mu returns to "
                            + "the same state after p further updates. This closes qdo-v1 "
                            + "theorem/38.8, atom qdo-residual-21a05dfa718331655905d64d470bc9e"
                            + "364bd37cfa07ff496de3eaa98fa613754.")),
                    Paragraph(Text(
                        "Repository search supplied the quantitative finite-orbit theorem "
                            + "finite_orbit_and_readout_eventually_periodic, which is applied "
                            + "directly. Pinned Mathlib supplies its pigeonhole and iterate "
                            + "ingredients, but no declaration combining eventual periodicity "
                            + "with the fixed-point-free exclusion of period one."))),
                DescribeRole.Theorem))));

    private static Formula Iterate(Formula exponent, Formula state) =>
        Seq(F.Id("T"), Caret, Grp(exponent), Open, state, Close);

    private static Formula Card(Formula type) =>
        Seq(Operatorname, Grp(F.Id("card")), Open, type, Close);

    private static Formula PeriodFormula()
    {
        Formula carrier = F.Id("X");
        Formula state = F.Id("x");
        Formula initial = Seq(F.Id("x"), Underscore, Grp(D(0)));
        Formula mu = F.Id("mu");
        Formula period = F.Id("p");
        Formula time = F.Id("t");

        return Disp(Seq(
            Forall, Sp, carrier, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, carrier, CloseBracket,
            Comma, Esc,
            F.Id("T"), Colon, Sp, carrier, Sp, To, Sp, carrier, Comma, Esc,
            Open, Forall, Sp, state, InMacro, Sp, carrier, Comma, Sp,
            F.Id("T"), Open, state, Close, Sp, Neq, Sp, state, Close, Sp,
            Rightarrow, Sp, Forall, Sp, initial, InMacro, Sp, carrier, Comma, Esc,
            Exists, Sp, mu, Comma, Sp, period, InMacro, Sp,
            Mathbb, Grp(F.Id("N")), Comma, Esc,
            mu, Plus, period, Sp, Leq, Sp, Card(carrier), Sp, Land, Sp,
            D(2), Sp, Leq, Sp, period, Sp, Land, Sp,
            Forall, Sp, time, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            mu, Sp, Leq, Sp, time, Sp, Rightarrow, Sp,
            Iterate(Seq(time, Plus, period), initial), Sp, Eq, Sp,
            Iterate(time, initial), Dot));
    }
}
