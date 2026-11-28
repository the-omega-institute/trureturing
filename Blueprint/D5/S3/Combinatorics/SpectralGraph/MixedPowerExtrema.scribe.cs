using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class MixedPowerExtremaDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/dasashnisangeetha2026graphpowers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The path and the complete graph attain the two mixed spectral extrema over all finite connected simple graphs of a given order.",
        H("Mixed spectral extrema of distance powers"),
        Blocks(Describe.Lean(
            DescribeId.Create("spectral-extrema"),
            DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/MixedPowerExtrema.result"),
            H("The lower and upper extrema with equality"),
            StatementSource.FromAuthor(ResultFormula()),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text("Question 5.1 in Das–Ashni–Sangeetha, arXiv:2611.29397v1, printed p. 17, asks for the extrema of the largest eigenvalue of the mixed degree–adjacency matrix of a graph power. Both matrices use the power graph. The existing graphPower joins distinct vertices at base distance at most k on connected graphs. The OmegaMath theorem mixedTop_isGreatest identifies mixedTop with the greatest element of the real matrix spectrum.")),
                Paragraph(Text("A spanning tree reduces the lower bound to trees. Reflected coordinates compare the edge energies under a terminal-leaf transfer, and a sum of rooted distance deficits gives a finite descent to a path. The last transfer is strict for a nonpath tree above the complete-power range. A chord on a spanning path gives an extra power edge. For the upper equality, strict spectral monotonicity and the complete graph's row sum identify exactly the complete powers."))),
            DescribeRole.Theorem,
            new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("das-ashni-sangeetha-2026-mixed-power-extrema"),
                ResolutionKind.Proved))),
        []));

    private static Formula ResultFormula()
    {
        var vertexType = F.Id("V");
        var graph = F.Id("G");
        var power = F.Id("k");
        var alpha = Alpha;
        var order = Apply(Qualified("Fintype", "card"), vertexType);
        var path = Apply(Qualified("SimpleGraph", "pathGraph"), order);
        var graphValue = Apply(Qualified("OmegaMath", "MixedAdjacency", "mixedTop"), Power(graph, power), alpha);
        var pathValue = Apply(Qualified("OmegaMath", "MixedAdjacency", "mixedTop"), Power(path, power), alpha);
        var maximum = Seq(Par(Seq(order, Sp, Colon, Sp, Real())), Sp, Minus, Sp, D(1));
        var lowerCase = Both(Compare(order, Le, Seq(power, Sp, Plus, Sp, D(1))), Lor,
            Apply(Qualified("Nonempty"), Apply(Qualified("SimpleGraph", "Iso"), path, graph)));
        var distance = Apply(Qualified("SimpleGraph", "dist"), graph, F.Id("i"), F.Id("j"));
        var upperCase = All("i", vertexType, All("j", vertexType, Compare(distance, Le, power)));
        var result = Both(Compare(pathValue, Le, graphValue), Land,
            Both(Compare(graphValue, Le, maximum), Land,
                Both(Both(Compare(graphValue, Eq, pathValue), Iff, lowerCase), Land,
                    Both(Compare(graphValue, Eq, maximum), Iff, upperCase))));
        return Disp(All("V", Seq(Qualified("Type"), Sp, F.Id("u")),
            Instance(Apply(Qualified("Fintype"), vertexType),
                Instance(Apply(Qualified("DecidableEq"), vertexType),
                    All("G", Apply(Qualified("SimpleGraph"), vertexType),
                        Imp(Apply(Qualified("SimpleGraph", "Connected"), graph),
                            All("k", Qualified("Nat"), Imp(Compare(D(1), Le, power),
                                Bind(Alpha, Real(), Imp(Compare(D(0), Le, alpha),
                                    Imp(Compare(alpha, Lt, D(1)), result)))))))))));
    }

    private static Formula Power(Formula graph, Formula k) =>
        Apply(Qualified("D5", "S3", "Combinatorics", "Graph", "ZeroForcing",
            "GridPowerZeroForcingRefutation", "graphPower"), graph, k);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Apply(Formula head, params Formula[] args) => new Formula.Apply(head, [.. args]);
    private static Formula Qualified(params string[] names) =>
        Seq(Operatorname, Grp(Seq(names.SelectMany((name, i) =>
            i == 0 ? new Formula[] { F.Id(name) } : [Dot, F.Id(name)]).ToArray())));
    private static Formula All(string name, Formula domain, Formula body) => Bind(F.Id(name), domain, body);
    private static Formula Bind(Formula name, Formula domain, Formula body) =>
        Seq(Forall, Sp, Par(Seq(name, Sp, Colon, Sp, domain)), Comma, Sp, body);
    private static Formula Instance(Formula domain, Formula body) =>
        Seq(Forall, Sp, OpenBracket, domain, CloseBracket, Comma, Sp, body);
    private static Formula Compare(Formula a, Formula op, Formula b) => Seq(a, Sp, op, Sp, b);
    private static Formula Both(Formula a, Formula op, Formula b) => Par(Seq(a, Sp, op, Sp, b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, To, Sp, b);
}
