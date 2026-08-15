using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class FiniteOrbitPeriodBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite deterministic orbits and their readouts have a cardinality-bounded tail period.",
        H("Finite Orbit Period Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-orbits-have-cardinality-bounded-tail-periods"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound."
                    + "finite_orbit_and_readout_eventually_periodic"),
                H("Finite orbits have cardinality-bounded tail periods"),
                StatementSource.FromAuthor(PeriodBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y be a finite state carrier, F a deterministic self-map, q any "
                            + "readout, and y0 an initial state. Some strictly positive period "
                            + "p begins after a tail index mu, with mu+p no larger than the "
                            + "number of states.")),
                    Paragraph(Text(
                        "For every time t at or after mu, shifting by p preserves the state. "
                            + "Applying q to that state equality gives the same period for every "
                            + "deterministic readout.")),
                    Paragraph(Text(
                        "Pinned Mathlib and Loogle gave the exact pigeonhole declaration "
                            + "Fintype.exists_ne_map_eq_of_card_lt. The proof applies it to the "
                            + "first card(Y)+1 orbit points and uses Function.iterate_add_apply "
                            + "to propagate the collision. Pinned-Mathlib and repository searches "
                            + "found no equal or stronger quantitative theorem. LeanSearch's API "
                            + "endpoint returned HTTP 404 and supplied no search conclusion."))),
                DescribeRole.Theorem))));

    private static Formula Iterate(Formula exponent, Formula state) =>
        Seq(F.Id("F"), Caret, Grp(exponent), Open, state, Close);

    private static Formula Read(Formula state) =>
        Seq(F.Id("q"), Open, state, Close);

    private static Formula Card(Formula type) =>
        Seq(Operatorname, Grp(F.Id("card")), Open, type, Close);

    private static Formula PeriodBoundFormula()
    {
        Formula carrier = F.Id("Y");
        Formula output = F.Id("O");
        Formula mu = F.Id("mu");
        Formula period = F.Id("p");
        Formula time = F.Id("t");
        Formula initial = Seq(F.Id("y"), Underscore, Grp(D(0)));
        Formula shifted = Iterate(Seq(time, Plus, period), initial);
        Formula current = Iterate(time, initial);
        return Disp(Seq(
            Forall, Sp, carrier, Comma, Sp, output, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, carrier, CloseBracket,
            Comma, Esc,
            F.Id("F"), Colon, Sp, carrier, Sp, To, Sp, carrier, Comma, Sp,
            F.Id("q"), Colon, Sp, carrier, Sp, To, Sp, output, Comma, Esc,
            Forall, Sp, initial, InMacro, Sp, carrier, Comma, Esc,
            Exists, Sp, mu, Comma, Sp, period, InMacro, Sp,
            Mathbb, Grp(F.Id("N")), Comma, Esc,
            D(0), Sp, Lt, Sp, period, Sp, Land, Sp,
            mu, Plus, period, Sp, Leq, Sp, Card(carrier), Sp, Land, Sp,
            Forall, Sp, time, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            mu, Sp, Leq, Sp, time, Sp, Rightarrow, Sp,
            Open, shifted, Sp, Eq, Sp, current, Sp, Land, Sp,
            Read(shifted), Sp, Eq, Sp, Read(current), Close, Dot));
    }
}
