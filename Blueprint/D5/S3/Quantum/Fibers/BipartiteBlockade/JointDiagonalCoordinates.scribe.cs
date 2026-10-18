using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers.BipartiteBlockade;

internal sealed class JointDiagonalCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Fibers/BipartiteBlockade/JointDiagonalCoordinates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent blocking coordinates admit joint signed-diagonal realization.",
        H("Joint Blocking Coordinates and the Compatible Residual"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("arbitrary-diagonal-blocking-coordinates"),
                DeclarationHandle.Create(Prefix + "arbitrary_diagonal_blocking_coordinates"),
                H("Arbitrary joint signed-diagonal coordinates"),
                StatementSource.FromAuthor(RealizationStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite simple graph G and a finite family F of distinct independent "
                    + "vertex sets, each of size at least two, let x assign an arbitrary real "
                    + "number to every member of F. There exists a real signed measure delta "
                    + "on the actual independent configurations of G whose total mass is zero, "
                    + "whose expectation of every single occupation is zero, and whose blocking "
                    + "expectation for N is x(N), simultaneously for all N in F. The proof "
                    + "uses the independence of the blocking functions modulo constants and "
                    + "single occupations to prove full row rank of the complete moment matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("residual-dimension-exact"),
                DeclarationHandle.Create(Prefix + "residual_dimension_exact"),
                H("Exact compatible signed-diagonal residual dimension"),
                StatementSource.FromAuthor(DimensionStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the same graph and independent-family hypotheses, choose a real "
                        + "weight on F with at least one nonzero coefficient. Consider the actual "
                        + "blocking coordinate image of zero-mass, fixed-single-occupation signed "
                        + "measures satisfying the one weighted blocking equation. That image is "
                        + "exactly the kernel of the weighted sum, so its real vector-space "
                        + "dimension is the cardinality of F minus one.")),
                    Paragraph(Text(
                        "This statement concerns signed diagonal directions. It supplies the "
                        + "joint-coordinate and exact-dimension step of the blockade problem. "
                        + "Identifying the weight with a bipartite graph's class coefficients, "
                        + "canceling accelerations by coherent edge terms, and obtaining positive "
                        + "density matrices are separate realization bridges."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);

    private static Formula C(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula SharedAssumptions() => Seq(
        Forall, Sp, V("V"), Colon, Sp, C("Type"), Comma, Sp,
        OpenBracket, C("Fintype", V("V")), CloseBracket, Comma, Sp,
        OpenBracket, C("DecidableEq", V("V")), CloseBracket, Comma, Sp,
        V("G"), Colon, Sp, C("SimpleGraph", V("V")), Comma, Sp,
        V("F"), Colon, Sp, C("Finset", C("Finset", V("V"))), Comma, Sp,
        Open, Forall, Sp, V("N"), InMacro, Sp, V("F"), Comma, Sp,
        C("independent", V("G"), V("N")), Close, Rightarrow, Sp,
        Open, Forall, Sp, V("N"), InMacro, Sp, V("F"), Comma, Sp,
        D(2), Le, Sp, C("card", V("N")), Close, Rightarrow, Sp);

    private static Formula RealizationStatement() => Disp(Seq(
        SharedAssumptions(), Forall, Sp, V("x"), Colon, Sp, V("F"), Rightarrow, Sp,
        C("Real"), Comma, Sp, Exists, Sp, V("delta"), Colon, Sp,
        C("Configuration", V("G")), Rightarrow, Sp, C("Real"), Comma, Sp,
        C("sum", V("delta")), Eq, D(0), Sp, Land, Sp,
        Open, Forall, Sp, V("v"), Comma, Sp,
        C("occupationMoment", V("delta"), V("v")), Eq, D(0), Close, Sp, Land, Sp,
        Open, Forall, Sp, V("N"), InMacro, Sp, V("F"), Comma, Sp,
        C("blockingMoment", V("G"), V("N"), V("delta")), Eq,
        C("x", V("N")), Close, Dot));

    private static Formula DimensionStatement() => Disp(Seq(
        SharedAssumptions(), Forall, Sp, V("weight"), Colon, Sp, V("F"), Rightarrow, Sp,
        C("Real"), Comma, Sp,
        Open, Exists, Sp, V("N"), Comma, Sp, C("weight", V("N")), Ne, D(0), Close,
        Rightarrow, Sp,
        C("finrank", C("Real"), C("attainableResidual", V("G"), V("F"), V("weight"))),
        Eq, C("card", V("F")), Minus, D(1), Dot));
}
