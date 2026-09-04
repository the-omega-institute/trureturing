using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class FreePermutationObserverDistanceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Free update orbits have exact integer distance, while both off-orbit sectors are infinitely far.",
        H("Free Permutation Observer Distance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("free-orbits-have-exact-observer-distance"),
                DeclarationHandle.Create(
                    "D5/S3/ContinuousObservables/FreePermutationObserverDistance."
                        + "free_permutation_observer_distance"),
                H("Free orbits have exact observer distance"),
                StatementSource.FromAuthor(Disp(TheoremFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The integer-power action is required to be free. This premise is necessary: "
                            + "on a periodic orbit a nonzero period returns to the starting point, so "
                            + "the distance is zero rather than the absolute value of that period.")),
                    Paragraph(Text(
                        "For the missing lower bound, the proof assigns each point of the selected "
                            + "orbit its unique integer coordinate and clips its distance from zero at "
                            + "the requested radius. This readout is bounded, changes by at most one "
                            + "under one update, and attains the full integer displacement.")),
                    Paragraph(Text(
                        "The same-fiber off-orbit clause uses the frozen characterization of infinite "
                            + "distance by distinct cyclic update orbits. The distinct-fiber clause "
                            + "applies the frozen invariant-leaf separator directly."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula carrier = F.Id("I");
        Formula fiberType = F.Id("Fiber");
        Formula update = F.Id("tau");
        Formula fiber = F.Id("fiber");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula exponent = F.Id("n");
        Formula poweredUpdate = new Formula.Power(update, exponent);
        Formula distanceXY = Call("observerDistance", update, x, y);

        return Seq(
            Forall, Sp, carrier, Comma, Sp, fiberType, Comma, Sp,
            update, Sp, InMacro, Sp, Call("EquivPerm", carrier), Comma, Sp,
            fiber, Sp, InMacro, Sp, Call("Map", carrier, fiberType), Comma, Esc,
            Call("Free", update), Sp, Land, Sp, Call("Invariant", fiber, update),
            Sp, Rightarrow, Sp, Esc,
            Open, Forall, Sp, x, Sp, InMacro, Sp, carrier, Comma, Sp,
            exponent, Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Sp,
            Call("observerDistance", update, x, Call("act", poweredUpdate, x)),
            Sp, Eq, Sp, new Formula.Absolute(exponent), Close, Sp, Land, Esc,
            Open, Forall, Sp, x, Comma, Sp, y, Sp, InMacro, Sp, carrier, Comma, Sp,
            fiber, Open, x, Close, Sp, Eq, Sp, fiber, Open, y, Close, Sp, Land, Sp,
            NotMember(y, Call("Orb", update, x)), Sp, Rightarrow, Sp,
            distanceXY, Sp, Eq, Sp, Infty, Close, Sp, Land, Esc,
            Open, Forall, Sp, x, Comma, Sp, y, Sp, InMacro, Sp, carrier, Comma, Sp,
            fiber, Open, x, Close, Sp, Neq, Sp, fiber, Open, y, Close,
            Sp, Rightarrow, Sp, distanceXY, Sp, Eq, Sp, Infty, Close, Dot);
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

    private static Formula NotMember(Formula value, Formula set) =>
        new Formula.Not(new Formula.Relation(value, FormulaRelationOperator.MemberOf, set));
}
