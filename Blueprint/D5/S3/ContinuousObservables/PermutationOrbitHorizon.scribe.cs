using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class PermutationOrbitHorizonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full permutation readouts place the horizon exactly outside the cyclic update orbit.",
        H("Permutation-Orbit Horizon"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("full-readout-horizon-is-the-cyclic-orbit-complement"),
                DeclarationHandle.Create(
                    "D5/S3/ContinuousObservables/PermutationOrbitHorizon."
                        + "permutation_observer_horizon_eq_orbit_complement"),
                H("The full-readout horizon is the cyclic-orbit complement"),
                StatementSource.FromAuthor(Disp(TheoremFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The update orbit is Mathlib's canonical orbit of the subgroup generated "
                            + "by all integer powers of the permutation. A bounded indicator of "
                            + "one such orbit is update-invariant, so distinct orbits have infinite "
                            + "observer distance by the frozen invariant-leaf theorem.")),
                    Paragraph(Text(
                        "On a common orbit, the unit edge bound telescopes along positive powers. "
                            + "For a negative power, the proof telescopes forward from that iterate "
                            + "back to the origin and swaps the distance endpoints. This gives the "
                            + "absolute integer bound without assuming the carrier is finite.")),
                    Paragraph(Text(
                        "The horizon and finite-distance ball are defined directly as the top and "
                            + "non-top fibers of the existing observer distance. Their displayed set "
                            + "equalities are public conjuncts of the same theorem."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula carrier = F.Id("I");
        Formula update = F.Id("tau");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula origin = F.Id("o");
        Formula exponent = F.Id("n");
        Formula orbitX = Call("Orb", update, x);
        Formula orbitY = Call("Orb", update, y);
        Formula orbitOrigin = Call("Orb", update, origin);
        Formula distanceXY = Call("observerDistance", update, x, y);
        Formula poweredUpdate = new Formula.Power(update, exponent);

        return Seq(
            Forall, Sp, carrier, Comma, Sp,
            update, Sp, InMacro, Sp, Call("EquivPerm", carrier), Comma, Sp,
            x, Comma, Sp, y, Comma, Sp, origin, Sp, InMacro, Sp, carrier, Comma, Esc,
            Open, distanceXY, Sp, Eq, Sp, Infty, Sp, Iff, Sp,
            orbitX, Sp, Neq, Sp, orbitY, Close, Sp, Land, Esc,
            Open, Forall, Sp, exponent, Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Sp,
            y, Sp, Eq, Sp, Call("act", poweredUpdate, x), Sp, Rightarrow, Sp,
            distanceXY, Sp, Leq, Sp, new Formula.Absolute(exponent), Close, Sp, Land, Esc,
            Call("horizonSet", update, origin), Sp, Eq, Sp,
            carrier, Sp, Setminus, Sp, orbitOrigin, Sp, Land, Esc,
            Call("finiteDistanceBall", update, origin), Sp, Eq, Sp, orbitOrigin, Dot);
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
