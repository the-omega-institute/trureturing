using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class FiniteEnergyRadiationBudgetDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Dynamics/FiniteEnergyRadiationBudget.";

    public DocumentDefinition Create()
    {
        Formula start = Seq(F.Id("u"), Underscore, Grp(Num(0)));
        Formula duration = Delta;
        Formula power = Seq(F.Id("P"), Underscore, Grp(Num(0)));
        Formula initialEnergy = Call("E", start);
        Formula total = Seq(Int, Underscore, Grp(start), Caret, Grp(Infty), Sp,
            Call("P", F.Id("u")), Sp, F.Id("d"), F.Id("u"));
        return DocumentDefinition.Create(ScribeNode.Create(
            "A nonnegative energy reservoir bounds integrated radiation and constant-power duration.",
            H("Finite energy radiation budget"),
            Blocks(
                Paragraph(Text(
                    "Let E and P be real functions of real time, with initial time u0. "
                    + "Assume E has derivative -P(u) for every u > u0, E is continuous from "
                    + "the right at u0, and E(u) and P(u) are nonnegative for every u >= u0. "
                    + "These hypotheses describe energy loss through radiation without an incoming source.")),
                Describe.Lean(
                    DescribeId.Create("finite-energy-radiation-budget"),
                    DeclarationHandle.Create(Module + "finite_energy_radiation_budget"),
                    H("Total radiated energy"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("IntegrableOn", F.Id("P"), Call("Ioi", start)), Sp, Land, Sp,
                        total, Sp, Le, Sp, initialEnergy))),
                    AssessedProvenance.FromLiterature(
                        LibraryNoteRef.Create("D5/L/Quantum/mathlib2026radiationbudget")),
                    Blocks(
                        Paragraph(Text(
                            "The energy is antitone on the closed ray. Extending it by "
                            + "E(max(u0,u)) gives an antitone function on the whole real line "
                            + "with lower bound zero. Its infimum L is nonnegative, and E(u) "
                            + "tends to L as u tends to infinity.")),
                        Paragraph(Text(
                            "A derivative of one sign whose primitive has a finite limit is "
                            + "integrable on the ray. The fundamental theorem of calculus "
                            + "then gives the total radiated energy as E(u0)-L, at most E(u0). "
                            + "Right continuity at the initial time identifies the boundary "
                            + "term with E(u0)."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("constant-power-duration-bound"),
                    DeclarationHandle.Create(Module + "constant_power_duration_le"),
                    H("Duration of constant positive power"),
                    StatementSource.FromAuthor(Disp(Seq(duration, Sp, Le, Sp,
                        Frac, Grp(initialEnergy), Grp(power)))),
                    AssessedProvenance.FromLiterature(
                        LibraryNoteRef.Create("D5/L/Quantum/mathlib2026radiationbudget")),
                    Blocks(
                        Paragraph(Text(
                            "Under the same assumptions, let Delta be nonnegative and P0 "
                            + "strictly positive. Suppose P(u)=P0 on [u0,u0+Delta]. "
                            + "The radiation integral over this interval equals Delta times P0. "
                            + "Nonnegativity of P bounds it by the total radiation, which is "
                            + "at most E(u0). Division by P0 gives the duration bound.")),
                        Paragraph(Text(
                            "Thus a fixed positive power cannot persist for arbitrarily long "
                            + "initial intervals when the initial energy is finite."))),
                    DescribeRole.Theorem))));
    }
}
