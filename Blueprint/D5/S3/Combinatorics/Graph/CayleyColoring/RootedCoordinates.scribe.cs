using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.CayleyColoring;

internal sealed class CayleyTreeRootedCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A zero color-difference mark identifies a conflict at the edge to the parent.",
        H("Rooted tree color coordinates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zero-mark"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.zero_pattern_iff"),
                H("Zero marks and equal colors"),
                StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Asymptotics/depanafieu2026stabilization")),
                Blocks(Paragraph(Text("Each non-root vertex indexes its edge to its parent. The color equivalence stores the root color and the differences on these edges. Evaluation at the indexed edge gives zero exactly when the endpoints started with the same color. This is the edge-coordinate version of the independent conflicts used in Theorem 10."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-colors-away"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.Away"),
                H("Away"),
                StatementSource.FromAuthor(Disp(CayleyColorsAway())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-colors-edge-color-equiv"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.edgeColorEquiv"),
                H("Edge Color Equiv"),
                StatementSource.FromAuthor(Disp(CayleyColorsEdgecolorequiv())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-colors-edge-equiv"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.edgeEquiv"),
                H("Edge Equiv"),
                StatementSource.FromAuthor(Disp(CayleyColorsEdgeequiv())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The equivalence sends a vertex away from the root to its unordered edge to its parent."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-colors-edge-orientation"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.edge_orientation"),
                H("Edge orientation"),
                StatementSource.FromAuthor(Disp(CayleyColorsEdgeOrientation())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-colors-parent"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.parent"),
                H("Parent"),
                StatementSource.FromAuthor(Disp(CayleyColorsParent())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The parent is the unique adjacent vertex at smaller distance from the root."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-colors-parent-spec"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.parent_spec"),
                H("Parent spec"),
                StatementSource.FromAuthor(Disp(CayleyColorsParentSpec())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-colors-parent-unique"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.parent_unique"),
                H("Parent unique"),
                StatementSource.FromAuthor(Disp(CayleyColorsParentUnique())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-colors-reconstruct"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.reconstruct"),
                H("Reconstruct"),
                StatementSource.FromAuthor(Disp(CayleyColorsReconstruct())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-parent-hits"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.Hits"),
                H("Hits"),
                StatementSource.FromAuthor(Disp(CayleyParentHits())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-parent-root-map"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.RootMap"),
                H("Root Map"),
                StatementSource.FromAuthor(Disp(CayleyParentRootmap())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-parent-depth"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.depth"),
                H("Depth"),
                StatementSource.FromAuthor(Disp(CayleyParentDepth())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("Depth counts the least number of parent steps needed to reach the root."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-parent-depth-hits"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.depth_hits"),
                H("Depth hits"),
                StatementSource.FromAuthor(Disp(CayleyParentDepthHits())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-parent-depth-min"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.depth_min"),
                H("Depth min"),
                StatementSource.FromAuthor(Disp(CayleyParentDepthMin())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-parent-depth-step"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.depth_step"),
                H("Depth step"),
                StatementSource.FromAuthor(Disp(CayleyParentDepthStep())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-parent-depth-zero"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.depth_zero"),
                H("Depth zero"),
                StatementSource.FromAuthor(Disp(CayleyParentDepthZero())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-parent-from-tree"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.fromTree"),
                H("From Tree"),
                StatementSource.FromAuthor(Disp(CayleyParentFromtree())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-parent-from-tree-child"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.fromTree_child"),
                H("From Tree child"),
                StatementSource.FromAuthor(Disp(CayleyParentFromtreeChild())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-parent-hits-refl"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.hits_refl"),
                H("Hits refl"),
                StatementSource.FromAuthor(Disp(CayleyParentHitsRefl())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-parent-hits-step"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.hits_step"),
                H("Hits step"),
                StatementSource.FromAuthor(Disp(CayleyParentHitsStep())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-parent-hits-trans"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.hits_trans"),
                H("Hits trans"),
                StatementSource.FromAuthor(Disp(CayleyParentHitsTrans())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-parent-root-map-equiv"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.rootMapEquiv"),
                H("Root Map Equiv"),
                StatementSource.FromAuthor(Disp(CayleyParentRootmapequiv())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-parent-to-graph"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.toGraph"),
                H("To Graph"),
                StatementSource.FromAuthor(Disp(CayleyParentTograph())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-parent-to-tree"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.toTree"),
                H("To Tree"),
                StatementSource.FromAuthor(Disp(CayleyParentTotree())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition)),
        []));

    private static Formula Statement1()
    {
        var v = F.Id("V");
        var a = F.Id("A");
        var t = F.Id("T");
        var r = F.Id("r");
        var c = F.Id("c");
        var x = F.Id("x");
        var marks = Call("snd", At(Call("edgeColorEquiv", t, r), c));
        var zero = Equal(At(marks, Call("edgeEquiv", t, r, x)), D(0));
        var conflict = Equal(At(c, Call("val", x)), At(c, Call("parent", t, r, x)));
        var point = All("x", Call("Away", v, r), Seq(zero, Sp, Iff, Sp, conflict));
        return All("V", F.Id("Type"), All("A", F.Id("Type"), Seq(Instance("AddGroup", a),
            All("T", Call("Tree", v), All("r", v, All("c", Arrow(v, a), point))))));
    }

    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);

    private static Formula Arrow(Formula source, Formula target) => new Formula.TypeArrow(source, target);

    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(x), Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula Instance(string type, Formula parameter) =>
        Seq(OpenBracket, Call(type, parameter), CloseBracket, Sp);

    private static Formula CayleyColorsAway() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Open, DefinitionDsl.Id("Away"), Sp,
        F.Id("V"), Sp, F.Id("r"), Sp, Colon, Sp, DefinitionDsl.Id("Type"), Sp, Open,
        DefinitionDsl.Id("max"), Sp, D(0), Sp, F.Id("u"), Close, Close, Sp, Eq, Sp, OpenBrace, Sp,
        F.Id("v"), Sp, Colon, Sp, F.Id("V"), Sp, Sp, Bar, Sp, Sp, F.Id("v"), Sp, Neq, Sp, F.Id("r"), Sp,
        CloseBrace);

    private static Formula CayleyColorsEdgecolorequiv() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("AddGroup"), Sp, F.Id("A"), CloseBracket, Sp, Forall, Sp, Open, F.Id("T"), Colon,
        Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("edgeColorEquiv"), Sp, F.Id("V"), Sp, F.Id("A"), Sp, F.Id("T"), Sp, F.Id("r"), Sp,
        Colon, Sp, Open, F.Id("V"), Sp, To, Sp, F.Id("A"), Close, Sp, Equiv, Sp, F.Id("A"), Sp, Times, Sp,
        Open, DefinitionDsl.Id("val"), Sp, Open, DefinitionDsl.Id("val"), Sp, F.Id("T"), Close, Dot,
        DefinitionDsl.Id("edgeSet"), Sp, To, Sp, F.Id("A"), Close, Close, Sp, Eq, Sp, Open,
        DefinitionDsl.Id("colorEquiv"), Sp, F.Id("T"), Sp, F.Id("r"), Close, Dot, DefinitionDsl.Id("trans"),
        Sp, Open, Open, DefinitionDsl.Id("Equiv"), Dot, DefinitionDsl.Id("refl"), Sp, F.Id("A"), Close, Dot,
        DefinitionDsl.Id("prodCongr"), Sp, Open, Open, DefinitionDsl.Id("edgeEquiv"), Sp, F.Id("T"), Sp,
        F.Id("r"), Close, Dot, DefinitionDsl.Id("arrowCongr"), Sp, Open, DefinitionDsl.Id("Equiv"), Dot,
        DefinitionDsl.Id("refl"), Sp, F.Id("A"), Close, Close, Close);

    private static Formula CayleyColorsEdgeequiv() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("T"), Colon, Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp,
        F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("v"), Sp, Colon, Sp, DefinitionDsl.Id("Away"), Sp, F.Id("r"), Close, Comma,
        Sp, DefinitionDsl.Id("val"), Sp, Open, DefinitionDsl.Id("edgeEquiv"), Sp, F.Id("T"), Sp, F.Id("r"),
        Sp, F.Id("v"), Close, Sp, Eq, Sp, DefinitionDsl.Id("Sym2"), Dot, DefinitionDsl.Id("mk"), Sp, Open,
        F.Id("v"), Dot, DefinitionDsl.Id("val"), Comma, Sp, DefinitionDsl.Id("parent"), Sp, F.Id("T"), Sp,
        F.Id("r"), Sp, F.Id("v"), Close);

    private static Formula CayleyColorsEdgeOrientation() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("T"), Colon, Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp,
        F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("v"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("w"),
        Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("h"), Colon, Sp, Open,
        DefinitionDsl.Id("val"), Sp, F.Id("T"), Close, Dot, DefinitionDsl.Id("Adj"), Sp, F.Id("v"), Sp,
        F.Id("w"), Close, Comma, Sp, Open, Exists, Sp, Open, DefinitionDsl.Id("hv"), Sp, Colon, Sp,
        F.Id("v"), Sp, Neq, Sp, F.Id("r"), Close, Comma, Sp, DefinitionDsl.Id("parent"), Sp, F.Id("T"), Sp,
        F.Id("r"), Sp, Langle, Sp, F.Id("v"), Comma, Sp, DefinitionDsl.Id("hv"), Rangle, Sp, Eq, Sp,
        F.Id("w"), Close, Sp, Lor, Sp, Exists, Sp, Open, DefinitionDsl.Id("hw"), Sp, Colon, Sp, F.Id("w"),
        Sp, Neq, Sp, F.Id("r"), Close, Comma, Sp, DefinitionDsl.Id("parent"), Sp, F.Id("T"), Sp, F.Id("r"),
        Sp, Langle, Sp, F.Id("w"), Comma, Sp, DefinitionDsl.Id("hw"), Rangle, Sp, Eq, Sp, F.Id("v"));

    private static Formula CayleyColorsParent() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("T"), Colon, Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp,
        F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("v"), Colon, Sp, DefinitionDsl.Id("CayleyColors"), Dot,
        DefinitionDsl.Id("Away"), Sp, F.Id("r"), Close, Comma, Sp, Open, DefinitionDsl.Id("parent"), Sp,
        F.Id("V"), Sp, F.Id("T"), Sp, F.Id("r"), Sp, F.Id("v"), Sp, Colon, Sp, F.Id("V"), Close, Sp, Eq, Sp,
        DefinitionDsl.Id("choose"), Sp, Open, DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp, Colon, Sp,
        F.Id("V"), Close, Sp, Mapsto, Sp, F.Id("T"), Dot, DefinitionDsl.Id("val"), Dot,
        DefinitionDsl.Id("Adj"), Sp, F.Id("v"), Dot, DefinitionDsl.Id("val"), Sp, F.Id("x"), Sp, Land, Sp,
        F.Id("T"), Dot, DefinitionDsl.Id("val"), Dot, DefinitionDsl.Id("dist"), Sp, F.Id("r"), Sp,
        F.Id("x"), Sp, Lt, Sp, F.Id("T"), Dot, DefinitionDsl.Id("val"), Dot, DefinitionDsl.Id("dist"), Sp,
        F.Id("r"), Sp, F.Id("v"), Dot, DefinitionDsl.Id("val"), Close);

    private static Formula CayleyColorsParentSpec() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("T"), Colon, Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp,
        F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("v"), Colon, Sp, DefinitionDsl.Id("CayleyColors"), Dot,
        DefinitionDsl.Id("Away"), Sp, F.Id("r"), Close, Comma, Sp, Open, DefinitionDsl.Id("val"), Sp,
        F.Id("T"), Close, Dot, DefinitionDsl.Id("Adj"), Sp, Open, DefinitionDsl.Id("val"), Sp, F.Id("v"),
        Close, Sp, Open, DefinitionDsl.Id("parent"), Sp, F.Id("T"), Sp, F.Id("r"), Sp, F.Id("v"), Close, Sp,
        Land, Sp, Open, DefinitionDsl.Id("val"), Sp, F.Id("T"), Close, Dot, DefinitionDsl.Id("dist"), Sp,
        F.Id("r"), Sp, Open, DefinitionDsl.Id("parent"), Sp, F.Id("T"), Sp, F.Id("r"), Sp, F.Id("v"), Close,
        Sp, Lt, Sp, Open, DefinitionDsl.Id("val"), Sp, F.Id("T"), Close, Dot, DefinitionDsl.Id("dist"), Sp,
        F.Id("r"), Sp, DefinitionDsl.Id("val"), Sp, F.Id("v"));

    private static Formula CayleyColorsParentUnique() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("T"), Colon, Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp,
        F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("v"), Colon, Sp, DefinitionDsl.Id("CayleyColors"), Dot,
        DefinitionDsl.Id("Away"), Sp, F.Id("r"), Close, Comma, Sp, Forall, Sp, Open, F.Id("w"), Colon, Sp,
        F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, DefinitionDsl.Id("hadj"), Colon, Sp, Open,
        DefinitionDsl.Id("val"), Sp, F.Id("T"), Close, Dot, DefinitionDsl.Id("Adj"), Sp, Open,
        DefinitionDsl.Id("val"), Sp, F.Id("v"), Close, Sp, F.Id("w"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hlt"), Colon, Sp, Open, DefinitionDsl.Id("val"), Sp, F.Id("T"), Close, Dot,
        DefinitionDsl.Id("dist"), Sp, F.Id("r"), Sp, F.Id("w"), Sp, Lt, Sp, Open, DefinitionDsl.Id("val"),
        Sp, F.Id("T"), Close, Dot, DefinitionDsl.Id("dist"), Sp, F.Id("r"), Sp, DefinitionDsl.Id("val"), Sp,
        F.Id("v"), Close, Comma, Sp, F.Id("w"), Sp, Eq, Sp, DefinitionDsl.Id("parent"), Sp, F.Id("T"), Sp,
        F.Id("r"), Sp, F.Id("v"));

    private static Formula CayleyColorsReconstruct() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("AddGroup"), Sp, F.Id("A"), CloseBracket, Sp, Forall, Sp, Open, F.Id("T"), Colon,
        Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("base"), Colon, Sp, F.Id("A"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("diff"), Colon, Sp, DefinitionDsl.Id("CayleyColors"), Dot,
        DefinitionDsl.Id("Away"), Sp, F.Id("r"), Sp, To, Sp, F.Id("A"), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("v"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Open, DefinitionDsl.Id("reconstruct"), Sp,
        F.Id("V"), Sp, F.Id("A"), Sp, F.Id("T"), Sp, F.Id("r"), Sp, DefinitionDsl.Id("base"), Sp,
        DefinitionDsl.Id("diff"), Sp, F.Id("v"), Sp, Colon, Sp, F.Id("A"), Close, Sp, Eq, Sp,
        DefinitionDsl.Id("WellFounded"), Dot, DefinitionDsl.Id("Nat"), Dot, DefinitionDsl.Id("fix"), Sp,
        Open, DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp, Colon, Sp, F.Id("V"), Close, Sp, Mapsto, Sp,
        Open, DefinitionDsl.Id("val"), Sp, F.Id("T"), Close, Dot, DefinitionDsl.Id("dist"), Sp, F.Id("r"),
        Sp, F.Id("x"), Close, Sp, DefinitionDsl.Id("fun"), Sp, Open, F.Id("v"), Sp, Colon, Sp, F.Id("V"),
        Close, Sp, Open, F.Id("a"), Sp, Colon, Sp, Open, F.Id("y"), Sp, Colon, Sp, F.Id("V"), Close, Sp, To,
        Sp, DefinitionDsl.Id("InvImage"), Sp, Open, DefinitionDsl.Id("fun"), Sp, Open,
        DefinitionDsl.Id("x1"), Sp, DefinitionDsl.Id("x2"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))),
        Close, Sp, Mapsto, Sp, DefinitionDsl.Id("x1"), Sp, Lt, Sp, DefinitionDsl.Id("x2"), Close, Sp, Open,
        DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp, Colon, Sp, F.Id("V"), Close, Sp, Mapsto, Sp, Open,
        DefinitionDsl.Id("val"), Sp, F.Id("T"), Close, Dot, DefinitionDsl.Id("dist"), Sp, F.Id("r"), Sp,
        F.Id("x"), Close, Sp, F.Id("y"), Sp, F.Id("v"), Sp, To, Sp, F.Id("A"), Close, Sp, Mapsto, Sp,
        DefinitionDsl.Id("if"), Sp, DefinitionDsl.Id("hv"), Sp, Colon, Sp, F.Id("v"), Sp, Eq, Sp, F.Id("r"),
        Sp, DefinitionDsl.Id("then"), Sp, DefinitionDsl.Id("base"), Sp, DefinitionDsl.Id("else"), Sp,
        DefinitionDsl.Id("diff"), Sp, Langle, Sp, F.Id("v"), Comma, Sp, DefinitionDsl.Id("hv"), Rangle, Sp,
        Plus, Sp, F.Id("a"), Sp, Open, DefinitionDsl.Id("parent"), Sp, F.Id("T"), Sp, F.Id("r"), Sp, Langle,
        Sp, F.Id("v"), Comma, Sp, DefinitionDsl.Id("hv"), Rangle, Sp, Close);

    private static Formula CayleyParentHits() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("f"), Colon, Sp, F.Id("V"), Sp, To, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("x"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("y"), Colon, Sp,
        F.Id("V"), Close, Comma, Sp, Open, DefinitionDsl.Id("Hits"), Sp, F.Id("V"), Sp, F.Id("f"), Sp,
        F.Id("x"), Sp, F.Id("y"), Sp, Colon, Sp, DefinitionDsl.Id("Prop"), Close, Sp, Eq, Sp, Exists, Sp,
        Open, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, F.Id("f"), Caret,
        OpenBracket, F.Id("m"), CloseBracket, Sp, F.Id("x"), Sp, Eq, Sp, F.Id("y"));

    private static Formula CayleyParentRootmap() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Open, DefinitionDsl.Id("RootMap"), Sp,
        F.Id("V"), Sp, F.Id("r"), Sp, Colon, Sp, DefinitionDsl.Id("Type"), Sp, Open,
        DefinitionDsl.Id("max"), Sp, D(0), Sp, F.Id("u"), Close, Close, Sp, Eq, Sp, OpenBrace, Sp,
        F.Id("f"), Sp, Colon, Sp, F.Id("V"), Sp, To, Sp, F.Id("V"), Sp, Sp, Bar, Sp, Sp, F.Id("f"), Sp,
        F.Id("r"), Sp, Eq, Sp, F.Id("r"), Sp, Land, Sp, Forall, Sp, Open, F.Id("v"), Sp, Colon, Sp,
        F.Id("V"), Close, Comma, Sp, DefinitionDsl.Id("CayleyParent"), Dot, DefinitionDsl.Id("Hits"), Sp,
        F.Id("f"), Sp, F.Id("v"), Sp, F.Id("r"), Sp, CloseBrace);

    private static Formula CayleyParentDepth() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("f"), Colon, Sp,
        DefinitionDsl.Id("CayleyParent"), Dot, DefinitionDsl.Id("RootMap"), Sp, F.Id("r"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("v"), Colon, Sp, F.Id("V"), Close, Comma, Sp, DefinitionDsl.Id("depth"), Sp,
        F.Id("r"), Sp, F.Id("f"), Sp, F.Id("v"), Sp, Eq, Sp, DefinitionDsl.Id("min"), Sp, OpenBrace,
        F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Sp, Bar, Sp, Sp, Open, F.Id("f"), Dot,
        DefinitionDsl.Id("val"), Caret, OpenBracket, F.Id("m"), CloseBracket, Close, Sp, F.Id("v"), Sp, Eq,
        Sp, F.Id("r"), CloseBrace);

    private static Formula CayleyParentDepthHits() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("f"), Colon, Sp,
        DefinitionDsl.Id("CayleyParent"), Dot, DefinitionDsl.Id("RootMap"), Sp, F.Id("r"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("v"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Open, DefinitionDsl.Id("val"),
        Sp, F.Id("f"), Close, Caret, OpenBracket, DefinitionDsl.Id("depth"), Sp, F.Id("r"), Sp, F.Id("f"),
        Sp, F.Id("v"), CloseBracket, Sp, F.Id("v"), Sp, Eq, Sp, F.Id("r"));

    private static Formula CayleyParentDepthMin() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("f"), Colon, Sp,
        DefinitionDsl.Id("CayleyParent"), Dot, DefinitionDsl.Id("RootMap"), Sp, F.Id("r"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("v"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("d"),
        Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open, F.Id("h"), Colon, Sp,
        Open, DefinitionDsl.Id("val"), Sp, F.Id("f"), Close, Caret, OpenBracket, F.Id("d"), CloseBracket,
        Sp, F.Id("v"), Sp, Eq, Sp, F.Id("r"), Close, Comma, Sp, DefinitionDsl.Id("depth"), Sp, F.Id("r"),
        Sp, F.Id("f"), Sp, F.Id("v"), Sp, Leq, Sp, F.Id("d"));

    private static Formula CayleyParentDepthStep() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("f"), Colon, Sp,
        DefinitionDsl.Id("CayleyParent"), Dot, DefinitionDsl.Id("RootMap"), Sp, F.Id("r"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("v"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hv"), Colon, Sp, F.Id("v"), Sp, Neq, Sp, F.Id("r"), Close, Comma, Sp,
        DefinitionDsl.Id("depth"), Sp, F.Id("r"), Sp, F.Id("f"), Sp, F.Id("v"), Sp, Eq, Sp,
        DefinitionDsl.Id("depth"), Sp, F.Id("r"), Sp, F.Id("f"), Sp, Open, DefinitionDsl.Id("val"), Sp,
        F.Id("f"), Sp, F.Id("v"), Close, Sp, Plus, Sp, D(1));

    private static Formula CayleyParentDepthZero() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("f"), Colon, Sp,
        DefinitionDsl.Id("CayleyParent"), Dot, DefinitionDsl.Id("RootMap"), Sp, F.Id("r"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("v"), Colon, Sp, F.Id("V"), Close, Comma, Sp, DefinitionDsl.Id("depth"), Sp,
        F.Id("r"), Sp, F.Id("f"), Sp, F.Id("v"), Sp, Eq, Sp, D(0), Sp, Iff, Sp, F.Id("v"), Sp, Eq, Sp,
        F.Id("r"));

    private static Formula CayleyParentFromtree() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("T"), Colon, Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp,
        F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("a"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("fromTree"), Sp, F.Id("V"), Sp, F.Id("T"), Sp, F.Id("r"), Sp, F.Id("a"), Sp, Colon,
        Sp, F.Id("V"), Close, Sp, Eq, Sp, DefinitionDsl.Id("if"), Sp, DefinitionDsl.Id("hv"), Sp, Colon, Sp,
        F.Id("v"), Sp, Eq, Sp, F.Id("r"), Sp, DefinitionDsl.Id("then"), Sp, F.Id("r"), Sp,
        DefinitionDsl.Id("else"), Sp, DefinitionDsl.Id("parent"), Sp, F.Id("T"), Sp, F.Id("r"), Sp, Langle,
        Sp, F.Id("v"), Comma, Sp, DefinitionDsl.Id("hv"), Rangle);

    private static Formula CayleyParentFromtreeChild() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("T"), Colon, Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp,
        F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("v"), Colon, Sp, DefinitionDsl.Id("CayleyColors"), Dot,
        DefinitionDsl.Id("Away"), Sp, F.Id("r"), Close, Comma, Sp, DefinitionDsl.Id("fromTree"), Sp,
        F.Id("T"), Sp, F.Id("r"), Sp, DefinitionDsl.Id("val"), Sp, F.Id("v"), Sp, Eq, Sp,
        DefinitionDsl.Id("parent"), Sp, F.Id("T"), Sp, F.Id("r"), Sp, F.Id("v"));

    private static Formula CayleyParentHitsRefl() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("f"), Colon, Sp, F.Id("V"), Sp, To, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("x"), Colon, Sp, F.Id("V"), Close, Comma, Sp, DefinitionDsl.Id("CayleyParent"), Dot,
        DefinitionDsl.Id("Hits"), Sp, F.Id("f"), Sp, F.Id("x"), Sp, F.Id("x"));

    private static Formula CayleyParentHitsStep() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("f"), Colon, Sp, F.Id("V"), Sp, To, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("x"), Colon, Sp, F.Id("V"), Close, Comma, Sp, DefinitionDsl.Id("CayleyParent"), Dot,
        DefinitionDsl.Id("Hits"), Sp, F.Id("f"), Sp, F.Id("x"), Sp, Open, F.Id("f"), Sp, F.Id("x"), Close);

    private static Formula CayleyParentHitsTrans() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("f"), Colon, Sp, F.Id("V"), Sp, To, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("x"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("y"), Colon, Sp,
        F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("z"), Colon, Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, DefinitionDsl.Id("hxy"), Colon, Sp, DefinitionDsl.Id("CayleyParent"), Dot,
        DefinitionDsl.Id("Hits"), Sp, F.Id("f"), Sp, F.Id("x"), Sp, F.Id("y"), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hyz"), Colon, Sp, DefinitionDsl.Id("CayleyParent"), Dot,
        DefinitionDsl.Id("Hits"), Sp, F.Id("f"), Sp, F.Id("y"), Sp, F.Id("z"), Close, Comma, Sp,
        DefinitionDsl.Id("CayleyParent"), Dot, DefinitionDsl.Id("Hits"), Sp, F.Id("f"), Sp, F.Id("x"), Sp,
        F.Id("z"));

    private static Formula CayleyParentRootmapequiv() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Open, DefinitionDsl.Id("rootMapEquiv"), Sp,
        F.Id("V"), Sp, F.Id("r"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyProbe"), Dot,
        DefinitionDsl.Id("Tree"), Sp, F.Id("V"), Sp, Equiv, Sp, DefinitionDsl.Id("CayleyParent"), Dot,
        DefinitionDsl.Id("RootMap"), Sp, F.Id("r"), Close, Sp, Eq, Sp, OpenBrace, Sp,
        DefinitionDsl.Id("toFun"), Sp, Colon, Eq, Sp, DefinitionDsl.Id("fun"), Sp, Open, F.Id("T"), Sp,
        Colon, Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp, F.Id("V"), Close, Sp,
        Mapsto, Sp, Langle, Sp, DefinitionDsl.Id("fromTree"), Sp, F.Id("T"), Sp, F.Id("r"), Rangle, Sp,
        Comma, Sp, DefinitionDsl.Id("invFun"), Sp, Colon, Eq, Sp, DefinitionDsl.Id("toTree"), Sp, F.Id("r"),
        Sp, CloseBrace);

    private static Formula CayleyParentTograph() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("f"), Colon, Sp,
        DefinitionDsl.Id("CayleyParent"), Dot, DefinitionDsl.Id("RootMap"), Sp, F.Id("r"), Close, Comma, Sp,
        Open, DefinitionDsl.Id("toGraph"), Sp, F.Id("V"), Sp, F.Id("r"), Sp, F.Id("f"), Sp, Colon, Sp,
        DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Sp, Eq, Sp, OpenBrace, Sp,
        DefinitionDsl.Id("Adj"), Sp, Colon, Eq, Sp, DefinitionDsl.Id("fun"), Sp, Open, F.Id("v"), Sp,
        F.Id("w"), Sp, Colon, Sp, F.Id("V"), Close, Sp, Mapsto, Sp, F.Id("v"), Sp, Neq, Sp, F.Id("r"), Sp,
        Land, Sp, DefinitionDsl.Id("val"), Sp, F.Id("f"), Sp, F.Id("v"), Sp, Eq, Sp, F.Id("w"), Sp, Lor, Sp,
        F.Id("w"), Sp, Neq, Sp, F.Id("r"), Sp, Land, Sp, DefinitionDsl.Id("val"), Sp, F.Id("f"), Sp,
        F.Id("w"), Sp, Eq, Sp, F.Id("v"), Sp, CloseBrace);

    private static Formula CayleyParentTotree() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("f"), Colon, Sp,
        DefinitionDsl.Id("CayleyParent"), Dot, DefinitionDsl.Id("RootMap"), Sp, F.Id("r"), Close, Comma, Sp,
        Open, DefinitionDsl.Id("toTree"), Sp, F.Id("V"), Sp, F.Id("r"), Sp, F.Id("f"), Sp, Colon, Sp,
        DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp, F.Id("V"), Close, Sp, Eq, Sp,
        Langle, Sp, DefinitionDsl.Id("toGraph"), Sp, F.Id("r"), Sp, F.Id("f"), Rangle);
}
