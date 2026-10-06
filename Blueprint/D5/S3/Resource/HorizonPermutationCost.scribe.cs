using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Resource;

internal sealed class HorizonPermutationCostDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact number of internal states needed to reproduce a finite self-map "
            + "through a prescribed horizon by initialized permutation dynamics.",
        H("Finite-Horizon Permutation Simulation Cost"),
        Blocks(
            Paragraph(Text(
                "Let X be any finite set, f a self-map of X, and H a natural number. "
                    + "A simulation consists of a finite state set E, a permutation P of E, "
                    + "a fixed total readout r from E to X, and an initialization i from X "
                    + "to E. For every x and every natural t at most H, the readout of "
                    + "P iterated t times at i(x) equals f iterated t times at x. "
                    + "Write S(f,H) for the collection of all such simulations. "
                    + "All internal state coordinates count toward the cardinality of E.")),
            Describe.Lean(
                DescribeId.Create("finite-horizon-permutation-cost"),
                DeclarationHandle.Create("D5/S3/Resource/HorizonPermutationCost.result"),
                H("The lower bound is attained"),
                StatementSource.FromAuthor(CostFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every finite X, every f and every H, all simulations have "
                            + "at least |X| + H times |X minus f(X)| states, and some "
                            + "simulation has exactly that many. Empty X, horizon zero, "
                            + "and bijective f are included. The readout has no time "
                            + "argument, and the simulation law is required only on "
                            + "initialized trajectories through H.")),
                    Paragraph(Text(
                        "At time H, initialized trajectories give |X| distinct states. "
                            + "For each point without a predecessor, its states at times "
                            + "zero through H minus one are distinct from each other and "
                            + "from the time-H states. Cancelling the earlier permutation "
                            + "iterate would otherwise put a point without a predecessor "
                            + "in the image of a positive iterate of f.")),
                    Paragraph(Text(
                        "Choose one predecessor of each image point and extend these "
                            + "selected edges to a permutation q of X. Every q-edge "
                            + "entering an image point is then an f-edge. Subdivide each "
                            + "remaining edge, which enters a missing-image point, by "
                            + "H new states. Read an added state by applying the "
                            + "corresponding positive iterate of f to that edge's source. "
                            + "An initialized trajectory enters an added segment only "
                            + "after a positive number of steps, so it cannot leave that "
                            + "segment within H steps. The construction adds exactly "
                            + "H states per missing-image point."))),
                DescribeRole.Theorem))));

    private static Formula Card(Formula set) => F.Seq(F.Lvert, set, F.Rvert);

    private static Formula CostFormula()
    {
        var x = F.Id("X");
        var f = F.Id("f");
        var h = F.Id("H");
        var e = F.Id("E");
        var tuple = F.Seq(F.Open, e, F.Comma, F.Id("P"), F.Comma,
            F.Id("r"), F.Comma, F.Id("i"), F.Close);
        var simulations = F.Seq(F.Id("S"), F.Open, f, F.Comma, h, F.Close);
        var image = F.Seq(f, F.Open, x, F.Close);
        var cost = F.Seq(Card(x), F.Sp, F.Plus, F.Sp, h, F.Cdot,
            Card(F.Seq(x, F.Setminus, image)));
        return F.Disp(F.Seq(
            F.Forall, F.Sp, x, F.Comma, F.Sp,
            F.Operatorname, F.Grp(F.Id("Finite")), F.Open, x, F.Close, F.Comma,
            F.Sp, F.Forall, F.Sp, f, F.Colon, x, F.To, x, F.Comma,
            F.Sp, F.Forall, F.Sp, h, F.InMacro, F.Mathbb, F.Grp(F.Id("N")),
            F.Comma, F.RowBreak,
            F.Open, F.Forall, F.Sp, tuple, F.InMacro, simulations, F.Comma,
            F.Sp, cost, F.Leq, Card(e), F.Close, F.RowBreak,
            F.Land, F.Sp, F.Open, F.Exists, F.Sp, tuple, F.InMacro, simulations,
            F.Comma, F.Sp, Card(e), F.Eq, cost, F.Close));
    }
}
