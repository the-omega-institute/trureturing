using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class TableOrbitWeightsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Attribution/TableOrbitWeights.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orbit mass variables for invariant probability tables and their event constraints.",
        H("The orbit program for finite equivariant probability kernels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("invariant-event-masses-iff"),
                DeclarationHandle.Create(Prefix + "invariant_event_masses_iff"),
                H("Invariant event masses are exactly the linear combinations of orbit frequencies"),
                StatementSource.FromAuthor(EventEquivalence()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let G be a group acting on a finite type T, and let I be any index type. "
                        + "The three types may belong to independent universes. For each i in I take a finite "
                        + "subset A(i) of T and a real prescribed mass m(i). Write Q for the type of G-orbits "
                        + "in T. The frequency of an event C in an orbit o is the cardinality of their "
                        + "intersection divided by the cardinality of o.")),
                    Paragraph(Math(Call("Law", F.Id("p"))), Text(" means that p is nonnegative on T, "
                        + "sums to one on T, satisfies p(g acting on t) = p(t) for every g and t, and "
                        + "sums to m(i) over A(i) for every i in I. "), Math(Call("Feasible", F.Id("z"))),
                        Text(" means that z is nonnegative on Q, sums to one on Q, and for every i in I "
                            + "the sum over all orbits o of z(o) times the frequency of A(i) in o equals m(i).")),
                    Paragraph(Text("To obtain z from p, sum p over each orbit. To obtain p from z, divide "
                        + "each orbit total by the orbit cardinality and assign the result to every point "
                        + "in that orbit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("maximal-invariant-event-mass"),
                DeclarationHandle.Create(Prefix + "maximal_invariant_event_mass"),
                H("The orbit program attains the maximum invariant mass of the target event"),
                StatementSource.FromAuthor(EventMaximum()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let G act on a finite type T and let I be arbitrary, with independent "
                        + "universes as in the event equivalence. Fix finite subsets A(i) of T and real "
                        + "masses m(i) for every i in I. Fix a finite target subset B of T. Assume there "
                        + "is a single real function p on T satisfying Law(p) for all the events A(i).")),
                    Paragraph(Text("For any real function w on Q, Score(w) is the sum over orbits o of "
                        + "w(o) times the frequency of B in o. TargetMass(p) is the sum of p over B. "
                        + "Law and Feasible have the same meaning as in the event equivalence. The "
                        + "maximizing z is feasible, and each real a is realized as TargetMass by some "
                        + "law if and only if it is realized as Score by some feasible vector.")),
                    Paragraph(Text("The feasible orbit vectors form a nonempty closed subset of the "
                        + "compact box with coordinates in the unit interval. Continuity gives attainment. "
                        + "Adjoining the target event to the indexed family gives the equality of attainable "
                        + "values while keeping all the original event constraints on the same law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("maximal-table-fixed-mass"),
                DeclarationHandle.Create(Prefix + "maximal_table_fixed_mass"),
                H("An arbitrary subgroup's fixed seed mass is the attained orbit program optimum"),
                StatementSource.FromAuthor(KernelMaximum()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let G be a group acting on a nonempty finite input type X in universe v "
                        + "and a finite output type Y in universe w. The tables are the functions from X to Y. "
                        + "Fix any subgroup H of G "
                        + "and a real function P on X times Y. Its entries are nonnegative, its rows sum "
                        + "to one, and P(g acting on x, g acting on y) = P(x,y) for every g, x and y.")),
                    Paragraph(Text("The G-action on a table t sends it under g to the table that takes x "
                        + "to g acting on t evaluated at the inverse translate of x. Let Q be its orbit "
                        + "type. For each cell (x,y), take the event of tables with t(x) = y. Feasible(z) "
                        + "means that z is nonnegative on Q, sums to one there, and for every x and y "
                        + "the sum of z(o) times the cell frequency in o over all o equals P(x,y). "
                        + "Score(z) sums z(o) times the H-fixed-table frequency in o over all o.")),
                    Paragraph(Text("UniversalBound(z) means that for every finite seed type U in any "
                        + "universe s with a G-action, every real weight function a on U, and every "
                        + "readout f from X times U to Y, the following implication holds. If a is "
                        + "nonnegative and G-invariant, f is pointwise G-equivariant, and for every x "
                        + "and y the sum of a over seeds with f(x,u) = y equals P(x,y), then the sum "
                        + "of a over seeds fixed by all of H is at most Score(z).")),
                    Paragraph(Text("PositiveAttainment(z) means that there exists a finite seed type "
                        + "U in the maximum of v and w, a G-action on U, a real weight function a "
                        + "on U, and a readout f from X times U to Y. The weights are strictly "
                        + "positive, sum to one and are G-invariant. The readout is pointwise "
                        + "G-equivariant, its weighted marginals equal P at every cell, and "
                        + "the total weight of H-fixed seeds equals Score(z).")),
                    Paragraph(Text("Pushing seeds to their tables preserves the row marginals and "
                        + "can increase the fixed mass. Each positive-weight table can also serve "
                        + "as a seed with evaluation as the readout. For the universal bound, summing "
                        + "the marginal equations at any one input already shows that the weights "
                        + "sum to one. Weight invariance makes the table law constant on orbits "
                        + "and readout equivariance transports fixed seeds into fixed tables."))),
                DescribeRole.Theorem))));

    private static Formula Typed(Formula name, Formula type) => Seq(name, Colon, type);
    private static Formula FunctionType(Formula domain, Formula codomain) => Seq(domain, Sp, To, Sp, codomain);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula EventFamily(Formula consequence)
    {
        Formula index = F.Id("I");
        return Seq(Forall, Sp, F.Id("G"), Comma, Sp, F.Id("T"), Comma, Sp, index, Comma, Sp,
            Typed(F.Id("A"), FunctionType(index, Call("Finset", F.Id("T")))), Comma, Sp,
            Typed(F.Id("m"), FunctionType(index, Reals())), Comma, Sp, consequence);
    }

    private static Formula Witness(Formula variable, Formula domain, Formula predicate) =>
        Seq(Exists, Sp, Typed(variable, FunctionType(domain, Reals())), Comma, Sp, predicate);

    private static Formula EventEquivalence()
    {
        Formula p = F.Id("p");
        Formula z = F.Id("z");
        return Disp(EventFamily(Seq(Open, Witness(p, F.Id("T"), Call("Law", p)), Close,
            Sp, Iff, Sp, Open, Witness(z, F.Id("Q"), Call("Feasible", z)), Close)));
    }

    private static Formula EventMaximum()
    {
        Formula t = F.Id("T");
        Formula q = F.Id("Q");
        Formula p = F.Id("p");
        Formula z = F.Id("z");
        Formula w = F.Id("w");
        Formula a = F.Id("a");
        Formula law = Call("Law", p);
        Formula feasible = Call("Feasible", w);
        return Disp(EventFamily(Seq(Typed(F.Id("B"), Call("Finset", t)), Comma, Sp,
            Open, Witness(p, t, law), Close, Sp, Rightarrow, Sp,
            Witness(z, q, Seq(Call("Feasible", z), Sp, Land, Sp, ScoreBound(z, q),
                Sp, Land, Sp, Open, Forall, Sp, Typed(a, Reals()), Comma, Sp,
                Open, Witness(p, t, Seq(law, Sp, Land, Sp, Call("TargetMass", p), Eq, a)), Close,
                Sp, Iff, Sp,
                Open, Witness(w, q, Seq(feasible, Sp, Land, Sp, Call("Score", w), Eq, a)), Close,
                Close)))));
    }

    private static Formula ScoreBound(Formula z, Formula orbitType)
    {
        Formula w = F.Id("w");
        return Seq(Open, Forall, Sp, Typed(w, FunctionType(orbitType, Reals())), Comma, Sp,
            Call("Feasible", w), Sp, Rightarrow, Sp, Call("Score", w), Sp, Le, Sp, Call("Score", z),
            Close);
    }

    private static Formula KernelMaximum()
    {
        Formula g = F.Id("G");
        Formula x = F.Id("X");
        Formula y = F.Id("Y");
        Formula z = F.Id("z");
        Formula q = F.Id("Q");
        return Disp(Seq(Forall, Sp, g, Comma, Sp, x, Comma, Sp, y, Comma, Sp,
            Typed(F.Id("H"), Call("Subgroup", g)), Comma, Sp,
            Typed(F.Id("P"), FunctionType(Seq(x, Sp, Times, Sp, y), Reals())), Comma, Sp,
            Call("CovariantProbabilityKernel", F.Id("P")), Sp, Rightarrow, Sp,
            Witness(z, q, Seq(Call("Feasible", z), Sp, Land, Sp, ScoreBound(z, q),
                Sp, Land, Sp, Call("UniversalBound", z), Sp, Land, Sp, Call("PositiveAttainment", z)))));
    }
}
