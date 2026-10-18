using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers.BipartiteBlockade;

internal sealed class GraphResidualDimensionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Fibers/BipartiteBlockade/GraphResidualDimension.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The distinct nonlinear neighborhoods carry one bipartite compatibility equation.",
        H("The Graph Residual and Its Coherent Lift"),
        Blocks(Describe.Lean(
            DescribeId.Create("graph-residual-dimension-and-realization"),
            DeclarationHandle.Create(Prefix + "graph_residual_dimension_and_realization"),
            H("Exact graph coordinate dimension and coherent realization"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let G be a finite simple graph with a proper Boolean coloring, and let "
                    + "every real drive amplitude be nonzero. Let F contain precisely the "
                    + "distinct open neighborhoods having at least two vertices, and assume F "
                    + "is nonempty. For each N in F, its coefficient is the sum of the signed "
                    + "drive squares over all vertices whose open neighborhood equals N. All "
                    + "these vertices have one color, so every coefficient is nonzero.")),
                Paragraph(Text(
                    "The actual blocking-coordinate image of zero-trace, fixed-single-mean "
                    + "signed diagonals satisfying the weighted compatibility equation has "
                    + "dimension exactly card(F) minus one. Every coordinate vector in that "
                    + "kernel is jointly realized by one signed diagonal on legal independent "
                    + "configurations. Open neighborhoods of size zero or one contribute no "
                    + "change when trace and single occupations are fixed, so summing by "
                    + "neighborhood class gives exactly the original vertex compatibility sum.")),
                Paragraph(Text(
                    "If G is connected, every such diagonal perturbation also admits a "
                    + "Hermitian coherent lift R with zero trace, zero single-site expectations, "
                    + "and zero actual double-commutator acceleration at every site. Its "
                    + "blocking expectations equal those of the chosen diagonal. The theorem "
                    + "therefore realizes every compatible correlation direction by an actual "
                    + "matrix perturbation. There is a positive eta for which every real t "
                    + "with absolute value below eta gives the strictly positive density "
                    + "matrix I/card(Configuration G) plus t R. Its trace is one, all means "
                    + "and single-setting accelerations equal those at the maximally mixed "
                    + "state, and each blocking expectation changes by t times the specified "
                    + "diagonal blocking moment. Thus every compatible direction occurs "
                    + "arbitrarily close to the same full-rank center."))),
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("local-density-residual-dimension"),
                DeclarationHandle.Create(Prefix + "local_density_residual_dimension"),
                H("Exact affine dimension in every physical neighborhood"),
                StatementSource.FromAuthor(LocalStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume additionally that G is connected. For every strictly positive "
                        + "radius, consider all positive semidefinite density matrices inside that "
                        + "operator-norm ball about the maximally mixed state which share its "
                        + "complete occupation data and its acceleration data for the chosen "
                        + "nonzero drive. Record their blocking-coordinate displacements on F. "
                        + "The span of this actual Born-readout set equals the explicit "
                        + "class-weight compatibility hyperplane. Both this span and the "
                        + "direction of the set's affine hull have real dimension card(F) minus one.")),
                    Paragraph(Text(
                        "For the upper bound, bipartite signed conservation forces every "
                        + "physical displacement into the same hyperplane. For the lower bound, "
                        + "each compatible vector has a coherent Hermitian lift and a positive "
                        + "density path through the same maximally mixed center. A sufficiently "
                        + "small nonzero path parameter enters any prescribed positive radius; "
                        + "rescaling that actual displacement recovers the original direction. "
                        + "The center itself belongs to the set, so its affine-direction span "
                        + "is exactly its linear span."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("full-blocking-residual-dimension"),
                DeclarationHandle.Create(Prefix + "full_blocking_residual_dimension"),
                H("The complete vertex blocking vector has the same affine dimension"),
                StatementSource.FromAuthor(FullStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same connected bipartite graph, nonzero drive, nonempty F, "
                    + "and positive radius hypotheses, consider the complete vertex-indexed "
                    + "vector of blocking-readout changes for actual density matrices in the "
                    + "same local data fiber. This actual set equals the image of the "
                    + "distinct-neighborhood coordinate set under class expansion. Expansion "
                    + "copies one coordinate to every vertex with that nonlinear neighborhood "
                    + "and puts zero at vertices of degree zero or one. Every coordinate class "
                    + "occurs at a vertex, so expansion is injective. Hence both the linear "
                    + "span and the affine-hull direction of the complete b-vector residual "
                    + "have dimension card(F) minus one."))),
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

    private static Formula FullStatement() => Disp(Seq(
        Forall, Sp, V("G"), Comma, Sp, C("Connected", V("G")), Rightarrow, Sp,
        C("proper", V("G"), V("color")), Rightarrow, Sp,
        Open, Forall, Sp, V("v"), Comma, Sp, C("Omega", V("v")), Ne, D(0), Close,
        Rightarrow, Sp, C("Nonempty", C("nonlinearNeighborhoods", V("G"))), Rightarrow, Sp,
        Forall, Sp, V("r"), Comma, Sp, D(0), Lt, V("r"), Rightarrow, Sp,
        C("fullPhysicalBlockingResiduals", V("G"), V("Omega"), V("r")), Eq,
        C("image", C("classExpansion", V("G")),
            C("physicalBlockingResiduals", V("G"), V("Omega"), V("r"))), Sp, Land, Sp,
        C("Injective", C("classExpansion", V("G"))), Sp, Land, Sp,
        C("finrank", C("Real"), C("span", C("fullPhysicalBlockingResiduals", V("G"), V("Omega"), V("r")))),
        Eq, C("card", C("nonlinearNeighborhoods", V("G"))), Minus, D(1), Sp, Land, Sp,
        C("finrank", C("Real"), C("direction", C("affineSpan",
            C("fullPhysicalBlockingResiduals", V("G"), V("Omega"), V("r"))))),
        Eq, C("card", C("nonlinearNeighborhoods", V("G"))), Minus, D(1), Dot));

    private static Formula LocalStatement() => Disp(Seq(
        Forall, Sp, V("G"), Comma, Sp, C("Connected", V("G")), Rightarrow, Sp,
        C("proper", V("G"), V("color")), Rightarrow, Sp,
        Open, Forall, Sp, V("v"), Comma, Sp, C("Omega", V("v")), Ne, D(0), Close,
        Rightarrow, Sp, C("Nonempty", C("nonlinearNeighborhoods", V("G"))), Rightarrow, Sp,
        Forall, Sp, V("r"), Comma, Sp, D(0), Lt, V("r"), Rightarrow, Sp,
        C("span", C("Real"), C("physicalBlockingResiduals", V("G"), V("Omega"), V("r"))),
        Eq, C("ker", C("compatibility", C("classWeight", V("G"), V("color"), V("Omega")))),
        Sp, Land, Sp,
        C("finrank", C("Real"), C("span", C("physicalBlockingResiduals", V("G"), V("Omega"), V("r")))),
        Eq, C("card", C("nonlinearNeighborhoods", V("G"))), Minus, D(1), Sp, Land, Sp,
        C("finrank", C("Real"), C("direction", C("affineSpan",
            C("physicalBlockingResiduals", V("G"), V("Omega"), V("r"))))),
        Eq, C("card", C("nonlinearNeighborhoods", V("G"))), Minus, D(1), Dot));

    private static Formula Statement() => Disp(Seq(
        Forall, Sp, V("V"), Colon, Sp, C("Type"), Comma, Sp,
        OpenBracket, C("Fintype", V("V")), CloseBracket, Comma, Sp,
        OpenBracket, C("DecidableEq", V("V")), CloseBracket, Comma, Sp,
        V("G"), Colon, Sp, C("SimpleGraph", V("V")), Comma, Sp,
        V("color"), Colon, Sp, V("V"), Rightarrow, Sp, C("Bool"), Comma, Sp,
        C("proper", V("G"), V("color")), Rightarrow, Sp,
        Forall, Sp, V("Omega"), Colon, Sp, V("V"), Rightarrow, Sp, C("Real"), Comma, Sp,
        Open, Forall, Sp, V("v"), Comma, Sp, C("Omega", V("v")), Ne, D(0), Close,
        Rightarrow, Sp, C("Nonempty", C("nonlinearNeighborhoods", V("G"))), Rightarrow, Sp,
        C("finrank", C("Real"), C("attainableResidual", V("G"),
            C("nonlinearNeighborhoods", V("G")), C("classWeight", V("G"), V("color"), V("Omega")))),
        Eq, C("card", C("nonlinearNeighborhoods", V("G"))), Minus, D(1), Sp, Land, Sp,
        C("jointBalancedDiagonalRealization", V("G"), V("color"), V("Omega")), Sp, Land, Sp,
        Open, C("Connected", V("G")), Rightarrow, Sp,
        C("coherentLift", V("G"), V("Omega")), Close, Dot));
}
