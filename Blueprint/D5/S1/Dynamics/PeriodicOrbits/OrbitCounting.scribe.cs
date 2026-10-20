using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.PeriodicOrbits;

internal sealed class OrbitCountingDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/puri2001arithmetic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual forward cycles explain the arithmetic of finite periodic-point counts.",
        H("Periodic Orbits, Phases and Divisor Counts"),
        Blocks(
            Paragraph(Text("Let f be a self-map. A point has least period n when n is its "
                + "minimal positive return time. The type Stratum consists of such points, "
                + "and Orbits is the image of their actual periodic cycles under cyclic "
                + "change of starting point. Every theorem here using a period assumes it "
                + "is positive. Transient points have minimal period zero and contribute "
                + "to none of these strata. No injectivity of f is assumed.")),
            Paragraph(Text("In the formulas, P(f,n) denotes Stratum, O(f,n) denotes Orbits, "
                + "m(f,n) denotes cycleLengthMultiplicity, and A(f,n) denotes fixedCount. "
                + "The symbol card is finite cardinality, val forgets a subtype proof, "
                + "and rep is the chosen representative. Integer products on the right "
                + "of a delta identity use the natural-to-integer cast.")),
            new DocumentBlock.DisplayFormula(Disp(Seq(Delta, Open, F.Id("a"), Comma, F.Id("n"), Close, Eq,
                Sum, Underscore, Grp(Open, F.Id("u"), Comma, F.Id("v"), Close,
                    InMacro, Sp, Call("divisorsAntidiagonal", F.Id("n"))),
                Mu, Open, F.Id("u"), Close, F.Id("a"), Open, F.Id("v"), Close))),
            Node("orbit_phase_decomposition", "Reconstruct each point from its orbit and phase",
                "Choosing one actual representative of each cycle gives an equivalence "
                + "from Orbits times Fin n to Stratum. Its value at an orbit and phase i is "
                + "the ith iterate of that representative. Distinct phases are distinct by "
                + "minimality of the period; every point on the cycle occurs at one phase. "
                + "This statement does not require the ambient carrier to be finite."),
            Node("stratum_card", "Each orbit contributes exactly one period of points",
                "For a finite carrier, taking cardinalities of the phase equivalence "
                + "gives n times the number of actual cycles. Empty strata are included."),
            Node("multiplicity_eq_orbit_card", "Division counts genuine cycles",
                "The existing cycleLengthMultiplicity divides the stratum size by n. "
                + "The exact phase decomposition shows that this quotient equals the "
                + "cardinality of the actual orbit type."),
            Node("fixed_count_divisor_sum", "Fixed counts sum over least-period divisors",
                "A point is fixed by the nth iterate exactly when its least period divides "
                + "n. Partitioning that finite fixed set and counting phases gives the sum "
                + "of d times cycleLengthMultiplicity over the positive divisors d of n."),
            Node("delta_fixed_count", "Mobius inversion recovers complete cycles",
                "The integer transform delta sums mu(u) times the fixed count at v over "
                + "positive factor pairs u times v equal to n. Mathlib's Mobius inversion "
                + "identifies it with n times the actual number of n-cycles, explaining "
                + "both its nonnegativity and its divisibility by n."),
            Paragraph(Text("For the deterministic transition operator in "
                + "TraceRankCombinatorics.trace_rank_combinatorial_meaning, the trace at "
                + "positive time is precisely this actual fixed-point count. Thus the "
                + "divisor sum supplies the cycle-trace equation used by "
                + "TraceRankJordanRecovery. That recovery also requires its separate "
                + "zero-block rank equations; periodic counts alone do not supply them "
                + "and do not classify attached transient trees."))
        )));

    private static DocumentBlock Node(string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(declaration.Replace('_', '-')),
            DeclarationHandle.Create("D5/S1/Dynamics/PeriodicOrbits/OrbitCounting." + declaration),
            H(title), StatementSource.FromAuthor(Statement(declaration)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Statement(string name)
    {
        Formula f = F.Id("f"), n = F.Id("n"), o = F.Id("o"), i = F.Id("i");
        Formula p = Call("P", f, n), orbits = Call("O", f, n);
        Formula m = Call("m", f, n), count = Call("A", f, n);
        Formula result = name switch
        {
            "orbit_phase_decomposition" => Seq(
                Exists, Sp, F.Id("e"), Colon, orbits, Times, Sp, Call("Fin", n), Equiv, Sp, p,
                Comma, Sp, Forall, Sp, o, Colon, orbits, Comma, Sp,
                i, Colon, Call("Fin", n), Comma, Sp,
                Call("val", Call("e", o, i)), Eq,
                f, Caret, Grp(Call("val", i)), Open,
                Call("val", Call("rep", f, n, o)), Close),
            "stratum_card" => Seq(Call("card", p), Eq, n, Cdot, Sp, Call("card", orbits)),
            "multiplicity_eq_orbit_card" => Seq(m, Eq, Call("card", orbits)),
            "fixed_count_divisor_sum" => Seq(count, Eq, Sum, Underscore,
                Grp(F.Id("d"), Mid, Sp, n), F.Id("d"), Cdot, Sp, Call("m", f, F.Id("d"))),
            "delta_fixed_count" => Seq(Delta, Open, Call("A", f), Comma, n, Close,
                Eq, n, Cdot, Sp, m),
            _ => throw new ArgumentException("Unknown orbit-counting declaration.", nameof(name))
        };
        Formula carrier = F.Id("X");
        Formula finite = name == "orbit_phase_decomposition" ? Sp :
            Seq(OpenBracket, Call("Fintype", carrier), CloseBracket, Comma, Sp);
        return Disp(Seq(Forall, Sp, carrier, Colon, Operatorname, Grp(F.Id("Type")),
            Comma, Sp, finite, f, Colon, carrier, To, Sp, carrier, Comma, Sp,
            n, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp, D(0), Lt, n,
            Rightarrow, Sp, result));
    }

}
