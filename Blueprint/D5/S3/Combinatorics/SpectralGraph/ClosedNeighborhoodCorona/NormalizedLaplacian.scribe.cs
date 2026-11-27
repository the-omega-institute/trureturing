using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.ClosedNeighborhoodCorona;

internal sealed class NormalizedLaplacianDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/NormalizedLaplacian.";
    private static readonly LibraryNoteRef Survey =
        LibraryNoteRef.Create("D5/L/AdjacencyProduct/sasonkrupnikhamudberman2025spectraldetermination");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacency-cospectral regular factors give normalized-Laplacian cospectral closed-neighborhood coronas in both orders.",
        H("Normalized-Laplacian cospectrality of closed-neighborhood coronas"),
        Blocks(
            Describe.Lean(DescribeId.Create("corona-normalized-laplacian-both-orders"),
                DeclarationHandle.Create(Prefix + "normalized_laplacian_charpoly_corona"),
                H("Question 5.21 holds in both factor orders"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(Survey),
                Blocks(
                    Paragraph(Text(
                        "The vertex types are independently finite. The function A assigns the real adjacency "
                        + "matrix and L assigns the real normalized Laplacian. The latter is the ordinary "
                        + "Laplacian scaled on both sides by the diagonal inverse square-root degree, with "
                        + "scale zero at degree zero. The corona attaches one copy of its second graph to "
                        + "the closed neighborhood of each vertex of its first graph.")),
                    Paragraph(Text(
                        "The adjacency characteristic polynomial determines the vertex count. After relabeling, "
                        + "spectral conjugacy followed by a reflection in the common row-sum eigenspace gives "
                        + "an orthogonal intertwiner U that fixes the constant vector. When the regular graph "
                        + "is the base, U acts on the base and on the index of each copy. When the regular "
                        + "graph is attached, U acts within each copy and the base is fixed.")),
                    Paragraph(Text(
                        "In both orders the lifted intertwiner has nonzero entries only between vertices of "
                        + "equal degree, so it also intertwines the degree diagonal and inverse square-root "
                        + "diagonal. Orthogonal similarity gives equality of characteristic polynomials. "
                        + "The proof imposes no connectedness or positive-degree condition."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("sason-et-al-2025-corona-normalized-laplacian-question-5-21"),
                    ResolutionKind.Proved)))));

    private static Formula Symbol(string name) => FormulaDsl.Id(name);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(Symbol(name))), [.. arguments]);

    private static Formula Typed(Formula variable, Formula type) => Seq(variable, Colon, Sp, type);

    private static Formula Instance(string name, Formula argument) =>
        Seq(OpenBracket, Call(name, argument), CloseBracket);

    private static Formula Statement()
    {
        Formula v = Symbol("V"), w = Symbol("W"), z = Symbol("Z");
        Formula g = new Formula.Subscript(Symbol("G"), D(1));
        Formula k = new Formula.Subscript(Symbol("G"), D(2));
        Formula h = Symbol("H");
        Formula d = new Formula.Subscript(Symbol("d"), D(1));
        Formula e = new Formula.Subscript(Symbol("d"), D(2));
        Formula graph(Formula vertex) => Call("SimpleGraph", vertex);
        Formula adj(Formula x) => Seq(x, Dot, Symbol("Adj"));
        Formula chi(Formula x) => Call("charpoly", x);
        Formula lap(Formula x, Formula y) => chi(Call("L", Call("corona", x, y)));
        return new Formula.Aligned([
            Seq(Amp, Forall, Sp, Typed(Seq(v, Comma, z, Comma, w), Symbol("Type")), Comma, Sp,
                Instance("Fintype", v), Instance("Fintype", z), Instance("Fintype", w), Sp,
                Instance("DecidableEq", v), Instance("DecidableEq", z), Instance("DecidableEq", w), Comma),
            Seq(Amp, Quad, Forall, Sp, Typed(g, graph(v)), Comma, Sp,
                Typed(k, graph(z)), Comma, Sp, Typed(h, graph(w)), Comma, Sp,
                Instance("DecidableRel", adj(g)), Instance("DecidableRel", adj(k)),
                Instance("DecidableRel", adj(h)), Comma),
            Seq(Amp, Quad, Forall, Sp, Typed(Seq(d, Comma, e), Seq(Mathbb, Grp(Symbol("N")))), Comma, Sp,
                Call("IsRegularOfDegree", g, d), Sp, Rightarrow, Sp,
                Call("IsRegularOfDegree", k, e), Sp, Rightarrow),
            Seq(Amp, Quad, chi(Call("A", g)), Sp, Eq, Sp, chi(Call("A", k)), Sp, Rightarrow),
            Seq(Amp, Quad, Open, lap(g, h), Sp, Eq, Sp, lap(k, h), Close, Sp, Land, Sp,
                Open, lap(h, g), Sp, Eq, Sp, lap(h, k), Close)
        ]);
    }
}
