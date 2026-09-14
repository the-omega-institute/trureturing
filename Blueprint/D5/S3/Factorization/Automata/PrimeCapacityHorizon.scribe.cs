using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Automata;

internal sealed class PrimeCapacityHorizonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The entire finite-continuation profile is exactly the clipped remaining-capacity vector.",
        H("Prime Capacity and Observation Horizon"),
        Blocks(
            Paragraph(Text(
                "Fix a finite register-index type I and capacities a(i). A live state r gives "
                + "the remaining amount 0<=r(i)<=a(i). An actual continuation word is a List(I); "
                + "it fits precisely when count_i(word)<=r(i) for every register. With distinct "
                + "prime labels p_i and current product d=product(p_i^(a_i-r_i)), unique "
                + "factorization identifies this condition with d*value(word) dividing "
                + "N=product(p_i^a_i). The Lean theorem below is over the exact word-count "
                + "capacity semantics; the integer divisor DFAO is owned by GuardedPrimeProduct.")),
            Paragraph(Text(
                "Capacity(a) is the finite product of Fin(a_i+1), Profile(a,H) is the product "
                + "of Fin(min(a_i,H)+1), and clipState maps remaining capacities coordinatewise "
                + "to their minima with H. Both carriers explicitly include an Option none "
                + "reject state. allowed(none,w) is false; allowed(some r,w) is the count guard. "
                + "The empty continuation is included.")),
            Describe.Lean(
                DescribeId.Create("prime-capacity-exact-horizon-quotient"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/PrimeCapacityHorizon.finite_horizon_state_classification"),
                H("Exact kernel, attainable profiles and cardinality for every horizon"),
                StatementSource.FromAuthor(StateClassificationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The theorem proves that clipState is onto the stated finite carrier "
                        + "and that two states have the same signature if and only if every "
                        + "actual word of total length at most H has the same admissibility "
                        + "from both. Thus the displayed cardinality is the number of complete "
                        + "observation profiles, not an assumed encoding size or a sample count.")),
                    Paragraph(Text(
                        "For sufficiency, each letter count is at most the whole word length, "
                        + "so clipping a remaining amount at H cannot alter admissibility. "
                        + "For necessity, repeat one letter min(r_i,H) times; transferring "
                        + "admissibility to the other state bounds its remaining amount. "
                        + "Doing this in both directions gives equality of clipped coordinates. "
                        + "Every profile is attained by choosing those same finite coordinates "
                        + "as the original remaining amounts. Rejection is separated from "
                        + "each live state by the empty word.")),
                    Paragraph(Text(
                        "For capacities (4,2,1,1), the complete profile counts at horizons "
                        + "0,1,2,3,4 are 2,17,37,49,61. At horizon four all states are separated. "
                        + "This does not claim that a fixed-H summary remains closed under a "
                        + "new input. Remaining amounts H and H+1 can agree now and differ "
                        + "after one consumption. It is a bounded-horizon observer quotient, "
                        + "not silently an exact autonomous state model."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Capacity() => Call("Capacity", F.Id("a"));

    private static Formula Profile() => Call("Profile", F.Id("a"), F.Id("H"));

    private static Formula Allowed(string state) =>
        Call("allowed", F.Id("a"), F.Id(state), F.Id("w"));

    private static Formula StateClassificationFormula() => Disp(Seq(
        Forall, Sp, F.Id("I"), Colon, Sp, F.Id("Type"), Comma, Sp,
        Open, Call("DecidableEq", F.Id("I")), Sp, Land, Sp, Call("Fintype", F.Id("I")), Close,
        Sp, Rightarrow, Sp,
        Forall, Sp, F.Id("a"), Colon, Sp, F.Id("I"), Sp, To, Sp, Naturals(), Comma, Sp,
        Forall, Sp, F.Id("H"), Sp, InMacro, Sp, Naturals(), Comma, Sp,
        Call("Surjective", Call("clipState", F.Id("a"), F.Id("H"))), Sp, Land, Sp,
        Open, Forall, Sp, F.Id("s"), Comma, Sp, F.Id("t"), Colon, Sp,
        Call("Option", Capacity()), Comma, Sp,
        Open, Forall, Sp, F.Id("w"), Colon, Sp, Call("List", F.Id("I")), Comma, Sp,
        Call("length", F.Id("w")), Sp, Leq, Sp, F.Id("H"), Sp, Rightarrow, Sp,
        Open, Allowed("s"), Sp, Iff, Sp, Allowed("t"), Close, Close,
        Sp, Iff, Sp,
        Call("clipState", F.Id("a"), F.Id("H"), F.Id("s")), Sp, Eq, Sp,
        Call("clipState", F.Id("a"), F.Id("H"), F.Id("t")), Close,
        Sp, Land, Sp,
        Call("card", Call("Option", Profile())), Sp, Eq, Sp, D(1), Sp, Plus, Sp,
        Prod, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("I")), Sp,
        Open, Call("min", Call("a", F.Id("i")), F.Id("H")), Sp, Plus, Sp, D(1), Close));
}
