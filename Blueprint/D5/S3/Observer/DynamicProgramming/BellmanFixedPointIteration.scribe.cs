using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.DynamicProgramming;

internal sealed class BellmanFixedPointIterationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula valueSpace = F.Id("V");
        Formula experiment = F.Id("I");
        Formula experimentIndex = F.Id("i");
        Formula discount = GammaLower;
        Formula stop = F.Id("G");
        Formula continuation = F.Id("Q");
        Formula bellman = F.Id("T");
        Formula value = F.Id("v");
        Formula valueStar = Seq(F.Id("v"), Underscore, Star);
        Formula initial = Seq(F.Id("v"), Underscore, D(0));
        Formula candidate = F.Id("w");
        Formula iteration = F.Id("n");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula valueMap = Arrow(valueSpace, valueSpace);
        Formula continuationType = Arrow(experiment, valueMap);
        Formula bellmanAtValue = Apply(bellman, value);
        Formula bellmanDefinition = Seq(
            bellmanAtValue, Sp, Colon, Eq, Sp,
            Call("min", stop, Seq(
                Operatorname, Grp(F.Id("inf")), Underscore,
                experimentIndex, InMacro, Sp, experiment, Sp,
                Apply(Apply(continuation, experimentIndex), value))));
        Formula fixedAtStar = Seq(
            Apply(bellman, valueStar), Sp, Eq, Sp, valueStar);
        Formula fixedAtCandidate = Seq(
            Apply(bellman, candidate), Sp, Eq, Sp, candidate);
        Formula iterated = Apply(
            new Formula.Power(bellman, iteration), initial);
        Formula geometric = Seq(
            new Formula.Power(discount, iteration), Sp,
            Call("dist", initial, valueStar));
        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, valueSpace, Comma, Sp, experiment, Colon, Sp, type,
            Comma, Sp, Call("CompleteMetricSpace", valueSpace), Comma, Sp,
            Call("Nonempty", valueSpace), Comma, Sp,
            Call("SemilatticeInf", valueSpace), Comma,
            RowBreak, Grp(),
            Call("FiniteNonempty", experiment), Comma, Sp,
            stop, Colon, Sp, valueSpace, Comma, Sp,
            continuation, Colon, Sp, continuationType, Comma, RowBreak, Grp(),
            bellmanDefinition, Comma, Sp,
            D(0), Sp, Lt, Sp, discount, Sp, Lt, Sp, D(1), Comma,
            RowBreak, Grp(),
            Call("LipschitzWith", discount, bellman), Sp, Rightarrow,
            RowBreak, Grp(),
            Call("ContractingWith", discount, bellman), Sp, Land,
            RowBreak, Grp(),
            Exists, Sp, valueStar, Colon, Sp, valueSpace, Comma, Sp,
            fixedAtStar, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, candidate, Colon, Sp, valueSpace, Comma, Sp,
            fixedAtCandidate, Sp, Rightarrow, Sp,
            candidate, Sp, Eq, Sp, valueStar, Close, Sp, Land,
            RowBreak, Grp(),
            Forall, Sp, initial, Colon, Sp, valueSpace, Comma, Sp,
            iteration, InMacro, Sp, naturals, Comma, RowBreak, Grp(),
            Call("dist", iterated, valueStar), Sp, Le, Sp, geometric, Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A contractive active Bellman operator has one value and geometric iteration.",
            H("Active Bellman Fixed Point and Value Iteration"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("active-bellman-unique-fixed-point-and-iteration"),
                    DeclarationHandle.Create(
                        "D5/S3/Observer/DynamicProgramming/BellmanFixedPointIteration."
                            + "bellman_contraction_unique_fixed_point_and_iteration_bound"),
                    H("The active Bellman value is unique and reached geometrically"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The value carrier is an arbitrary complete metric semilattice. "
                                + "For bounded belief-value functions this lattice infimum is "
                                + "pointwise minimum, so T(v) is constructed as the minimum of "
                                + "the stopping value G and the least continuation Q_i(v).")),
                        Paragraph(Text(
                            "The displayed Lipschitz premise is the contraction estimate established "
                                + "immediately before the source theorem: every continuation changes "
                                + "future value by at most the discount factor. Together with gamma "
                                + "strictly below one it makes the constructed T a strict contraction.")),
                        Paragraph(Text(
                            "Mathlib's canonical contraction fixed point supplies v star and proves "
                                + "that every other fixed value equals it. Iterating the Lipschitz "
                                + "estimate and using that every iterate fixes v star gives exactly "
                                + "the stated gamma-to-n distance bound for every initial value."))),
                    DescribeRole.Theorem))));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);
}
