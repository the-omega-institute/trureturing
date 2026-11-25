using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.CayleyColoring;

internal sealed class CayleyTreeTreeDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed-root bijection sends peaks to leaves in cardinality.",
        H("Peaks and leaves of a native rooted tree"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("peak-leaf"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.fixedRootEquiv_filterCard"),
                H("Peak and rooted-leaf counts"),
                StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/seitz2011labelledtrees")),
                Blocks(Paragraph(Text("A peak has no greater-labeled neighbor. A rooted leaf has no adjacent vertex farther from the root. For local minima, Seitz reroots at the greatest label, recursively transforms the attached branches, and finally swaps that label with the original root label. Reversing the label order gives the peak-to-leaf equivalence. It cuts at the least label, recursively replaces the attached branches, and swaps the least label with the specified root. See Seitz, Corollary 5.2.2 and §5.3.1.2, and de Panafieu et al., Proposition 5."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-probe-frame"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.Frame"),
                H("Frame"),
                StatementSource.FromAuthor(Disp(CayleyProbeFrame())),
                AssessedProvenance.FromRepo(),
                Blocks(new DocumentBlock.DisplayFormula(Disp(CayleyProbeFrameConstructor1()))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-probe-frame-branches"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.Branches"),
                H("Branches"),
                StatementSource.FromAuthor(Disp(CayleyProbeFrameBranches())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-probe-frame-assemble"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.assemble"),
                H("Assemble"),
                StatementSource.FromAuthor(Disp(CayleyProbeFrameAssemble())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-probe-frame-depth"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.depth"),
                H("Depth"),
                StatementSource.FromAuthor(Disp(CayleyProbeFrameDepth())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-probe-frame-glue"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.glue"),
                H("Glue"),
                StatementSource.FromAuthor(Disp(CayleyProbeFrameGlue())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-probe-frame-mem-part-at"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.mem_partAt"),
                H("Mem part At"),
                StatementSource.FromAuthor(Disp(CayleyProbeFrameMemPartat())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-probe-frame-part-at"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.partAt"),
                H("Part At"),
                StatementSource.FromAuthor(Disp(CayleyProbeFramePartat())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The cover and disjointness of the parts identify the unique part containing x away from the pivot p."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-probe-peak"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.Peak"),
                H("Peak"),
                StatementSource.FromAuthor(Disp(CayleyProbePeak())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-probe-rooted-leaf"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.RootedLeaf"),
                H("Rooted Leaf"),
                StatementSource.FromAuthor(Disp(CayleyProbeRootedleaf())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-probe-tree"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.Tree"),
                H("Tree"),
                StatementSource.FromAuthor(Disp(CayleyProbeTree())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-probe-cut"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.cut"),
                H("Cut"),
                StatementSource.FromAuthor(Disp(CayleyProbeCut())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-probe-cut-parts"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.cutParts"),
                H("Cut Parts"),
                StatementSource.FromAuthor(Disp(CayleyProbeCutparts())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-probe-decompose"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.decompose"),
                H("Decompose"),
                StatementSource.FromAuthor(Disp(CayleyProbeDecompose())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-probe-decompose-equiv"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.decomposeEquiv"),
                H("Decompose Equiv"),
                StatementSource.FromAuthor(Disp(CayleyProbeDecomposeequiv())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-probe-decompose-frame"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.decomposeFrame"),
                H("Decompose Frame"),
                StatementSource.FromAuthor(Disp(CayleyProbeDecomposeframe())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-probe-filter-card"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.filterCard"),
                H("Filter Card"),
                StatementSource.FromAuthor(Disp(CayleyProbeFiltercard())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-probe-filter-card-eq-nat-card"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.filterCard_eq_natCard"),
                H("Filter Card eq nat Card"),
                StatementSource.FromAuthor(Disp(CayleyProbeFiltercardEqNatcard())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-probe-fixed-root-equiv"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.fixedRootEquiv"),
                H("Fixed Root Equiv"),
                StatementSource.FromAuthor(Disp(CayleyProbeFixedrootequiv())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-probe-relabel-equiv"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.relabelEquiv"),
                H("Relabel Equiv"),
                StatementSource.FromAuthor(Disp(CayleyProbeRelabelequiv())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-probe-relabel-tree"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.relabelTree"),
                H("Relabel Tree"),
                StatementSource.FromAuthor(Disp(CayleyProbeRelabeltree())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-probe-shorter-neighbor"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.shorterNeighbor"),
                H("Shorter Neighbor"),
                StatementSource.FromAuthor(Disp(CayleyProbeShorterneighbor())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-probe-tree-of-depth"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.tree_of_depth"),
                H("Tree of depth"),
                StatementSource.FromAuthor(Disp(CayleyProbeTreeOfDepth())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Statement1()
    {
        var v = F.Id("V");
        var r = F.Id("r");
        var t = F.Id("T");
        var peakCount = Call("filterCard", Call("Peak", Call("graph", t)));
        var converted = At(Call("fixedRootEquiv", r), t);
        var leafCount = Call("filterCard", Call("RootedLeaf", Call("graph", converted), r));
        return All("V", F.Id("Type"), Seq(
            Instance("Fintype", v), Instance("LinearOrder", v),
            All("r", v, All("T", Call("Tree", v), Equal(peakCount, leafCount)))));
    }

    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);

    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(x), Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula Instance(string type, Formula parameter) =>
        Seq(OpenBracket, Call(type, parameter), CloseBracket, Sp);

    private static Formula CayleyProbeFrameConstructor1() =>
        Seq(
        OpenBrace, F.Id("V"), Sp, Colon, Sp, DefinitionDsl.Id("Type"), CloseBrace, Sp, To, Sp, OpenBrace,
        F.Id("p"), Sp, Colon, Sp, F.Id("V"), CloseBrace, Sp, To, Sp, Open, DefinitionDsl.Id("parts"), Sp,
        Colon, Sp, DefinitionDsl.Id("Set"), Sp, Open, DefinitionDsl.Id("Set"), Sp, F.Id("V"), Close, Close,
        Sp, To, Sp, Open, Forall, Sp, Open, F.Id("v"), Sp, Colon, Sp, F.Id("V"), Close, Comma, Sp,
        F.Id("v"), Sp, Neq, Sp, F.Id("p"), Sp, Iff, Sp, Exists, Sp, F.Id("s"), Sp, InMacro, Sp,
        DefinitionDsl.Id("parts"), Comma, Sp, F.Id("v"), Sp, InMacro, Sp, F.Id("s"), Close, Sp, To, Sp,
        Open, Forall, Sp, Open, F.Id("s"), Sp, F.Id("t"), Sp, Colon, Sp, DefinitionDsl.Id("Set"), Sp,
        F.Id("V"), Close, Comma, Sp, F.Id("s"), Sp, InMacro, Sp, DefinitionDsl.Id("parts"), Sp, To, Sp,
        F.Id("t"), Sp, InMacro, Sp, DefinitionDsl.Id("parts"), Sp, To, Sp, Forall, Sp, Open, F.Id("v"), Sp,
        Colon, Sp, F.Id("V"), Close, Comma, Sp, F.Id("v"), Sp, InMacro, Sp, F.Id("s"), Sp, To, Sp,
        F.Id("v"), Sp, InMacro, Sp, F.Id("t"), Sp, To, Sp, F.Id("s"), Sp, Eq, Sp, F.Id("t"), Close, Sp, To,
        Sp, Open, Open, F.Id("s"), Sp, Colon, Sp, DefinitionDsl.Id("val"), Sp, DefinitionDsl.Id("parts"),
        Close, Sp, To, Sp, DefinitionDsl.Id("coe"), Sp, F.Id("s"), Close, Sp, To, Sp,
        DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Frame"), Sp, F.Id("p"));

    private static Formula CayleyProbeFrame() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, F.Id("V"), Close, Comma, Sp, DefinitionDsl.Id("Frame"), Sp, F.Id("V"),
        Sp, F.Id("p"), Sp, Colon, Sp, DefinitionDsl.Id("Type"));

    private static Formula CayleyProbeFrameBranches() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("F"), Colon, Sp,
        DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Frame"), Sp, F.Id("p"), Close, Comma, Sp,
        Open, DefinitionDsl.Id("Branches"), Sp, F.Id("V"), Sp, F.Id("p"), Sp, F.Id("F"), Sp, Colon, Sp,
        DefinitionDsl.Id("Type"), Close, Sp, Eq, Sp, Open, F.Id("s"), Sp, Colon, Sp,
        DefinitionDsl.Id("val"), Sp, F.Id("F"), Dot, DefinitionDsl.Id("parts"), Close, Sp, To, Sp,
        DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp, DefinitionDsl.Id("coe"), Sp,
        F.Id("s"));

    private static Formula CayleyProbeFrameAssemble() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("F"), Colon, Sp,
        DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Frame"), Sp, F.Id("p"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("T"), Colon, Sp, F.Id("F"), Dot, DefinitionDsl.Id("Branches"), Close, Comma,
        Sp, Open, DefinitionDsl.Id("assemble"), Sp, F.Id("V"), Sp, F.Id("p"), Sp, F.Id("F"), Sp, F.Id("T"),
        Sp, Colon, Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp, F.Id("V"), Close,
        Sp, Eq, Sp, Langle, Sp, F.Id("F"), Dot, DefinitionDsl.Id("glue"), Sp, F.Id("T"), Rangle);

    private static Formula CayleyProbeFrameDepth() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("F"), Colon, Sp,
        DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Frame"), Sp, F.Id("p"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("T"), Colon, Sp, F.Id("F"), Dot, DefinitionDsl.Id("Branches"), Close, Comma,
        Sp, Forall, Sp, Open, F.Id("x"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("depth"), Sp, F.Id("V"), Sp, F.Id("p"), Sp, F.Id("F"), Sp, F.Id("T"), Sp,
        F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Sp, Eq, Sp, DefinitionDsl.Id("if"),
        Sp, F.Id("h"), Sp, Colon, Sp, F.Id("x"), Sp, Neq, Sp, F.Id("p"), Sp, DefinitionDsl.Id("then"), Sp,
        Open, DefinitionDsl.Id("val"), Sp, Open, F.Id("T"), Sp, Open, F.Id("F"), Dot,
        DefinitionDsl.Id("partAt"), Sp, F.Id("h"), Close, Close, Close, Dot, DefinitionDsl.Id("dist"), Sp,
        Open, F.Id("F"), Dot, DefinitionDsl.Id("root"), Sp, Open, F.Id("F"), Dot,
        DefinitionDsl.Id("partAt"), Sp, F.Id("h"), Close, Close, Sp, Langle, Sp, F.Id("x"), Rangle, Sp,
        Plus, Sp, D(1), Sp, DefinitionDsl.Id("else"), Sp, D(0));

    private static Formula CayleyProbeFrameGlue() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("F"), Colon, Sp,
        DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Frame"), Sp, F.Id("p"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("T"), Colon, Sp, F.Id("F"), Dot, DefinitionDsl.Id("Branches"), Close, Comma,
        Sp, Open, DefinitionDsl.Id("glue"), Sp, F.Id("V"), Sp, F.Id("p"), Sp, F.Id("F"), Sp, F.Id("T"), Sp,
        Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Sp, Eq, Sp, OpenBrace, Sp,
        DefinitionDsl.Id("Adj"), Sp, Colon, Eq, Sp, DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp,
        F.Id("y"), Sp, Colon, Sp, F.Id("V"), Close, Sp, Mapsto, Sp, Open, F.Id("x"), Sp, Eq, Sp, F.Id("p"),
        Sp, Land, Sp, Exists, Sp, Open, F.Id("s"), Sp, Colon, Sp, DefinitionDsl.Id("val"), Sp, F.Id("F"),
        Dot, DefinitionDsl.Id("parts"), Close, Comma, Sp, F.Id("y"), Sp, Eq, Sp, DefinitionDsl.Id("val"),
        Sp, Open, F.Id("F"), Dot, DefinitionDsl.Id("root"), Sp, F.Id("s"), Close, Close, Sp, Lor, Sp, Open,
        F.Id("y"), Sp, Eq, Sp, F.Id("p"), Sp, Land, Sp, Exists, Sp, Open, F.Id("s"), Sp, Colon, Sp,
        DefinitionDsl.Id("val"), Sp, F.Id("F"), Dot, DefinitionDsl.Id("parts"), Close, Comma, Sp, F.Id("x"),
        Sp, Eq, Sp, DefinitionDsl.Id("val"), Sp, Open, F.Id("F"), Dot, DefinitionDsl.Id("root"), Sp,
        F.Id("s"), Close, Close, Sp, Lor, Sp, Exists, Sp, Open, F.Id("s"), Sp, Colon, Sp,
        DefinitionDsl.Id("val"), Sp, F.Id("F"), Dot, DefinitionDsl.Id("parts"), Close, Sp, Open,
        DefinitionDsl.Id("hx"), Sp, Colon, Sp, F.Id("x"), Sp, InMacro, Sp, DefinitionDsl.Id("val"), Sp,
        F.Id("s"), Close, Sp, Open, DefinitionDsl.Id("hy"), Sp, Colon, Sp, F.Id("y"), Sp, InMacro, Sp,
        DefinitionDsl.Id("val"), Sp, F.Id("s"), Close, Comma, Sp, Open, DefinitionDsl.Id("val"), Sp, Open,
        F.Id("T"), Sp, F.Id("s"), Close, Close, Dot, DefinitionDsl.Id("Adj"), Sp, Langle, Sp, F.Id("x"),
        Comma, Sp, DefinitionDsl.Id("hx"), Rangle, Sp, Langle, Sp, F.Id("y"), Comma, Sp,
        DefinitionDsl.Id("hy"), Rangle, Sp, CloseBrace);

    private static Formula CayleyProbeFrameMemPartat() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("F"), Colon, Sp,
        DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Frame"), Sp, F.Id("p"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("x"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hx"), Colon, Sp, F.Id("x"), Sp, Neq, Sp, F.Id("p"), Close, Comma, Sp, F.Id("x"),
        Sp, InMacro, Sp, DefinitionDsl.Id("val"), Sp, Open, F.Id("F"), Dot, DefinitionDsl.Id("partAt"), Sp,
        DefinitionDsl.Id("hx"), Close);

    private static Formula CayleyProbeFramePartat() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("F"), Colon, Sp,
        DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Frame"), Sp, F.Id("p"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("x"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hx"), Colon, Sp, F.Id("x"), Sp, Neq, Sp, F.Id("p"), Close, Comma, Sp,
        DefinitionDsl.Id("partAt"), Sp, F.Id("F"), Sp, F.Id("x"), Sp, DefinitionDsl.Id("hx"), Sp, Eq, Sp,
        DefinitionDsl.Id("choose"), Sp, Open, DefinitionDsl.Id("fun"), Sp, Open, F.Id("s"), Sp, Colon, Sp,
        F.Id("F"), Dot, DefinitionDsl.Id("parts"), Close, Sp, Mapsto, Sp, F.Id("x"), Sp, InMacro, Sp,
        F.Id("s"), Dot, DefinitionDsl.Id("val"), Close);

    private static Formula CayleyProbePeak() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("LT"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("G"), Colon, Sp,
        DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("v"),
        Colon, Sp, F.Id("V"), Close, Comma, Sp, Open, DefinitionDsl.Id("Peak"), Sp, F.Id("V"), Sp,
        F.Id("G"), Sp, F.Id("v"), Sp, Colon, Sp, DefinitionDsl.Id("Prop"), Close, Sp, Eq, Sp, Forall, Sp,
        Open, F.Id("w"), Sp, Colon, Sp, F.Id("V"), Close, Comma, Sp, F.Id("G"), Dot,
        DefinitionDsl.Id("Adj"), Sp, F.Id("v"), Sp, F.Id("w"), Sp, To, Sp, F.Id("w"), Sp, Lt, Sp, F.Id("v"));

    private static Formula CayleyProbeRootedleaf() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("G"), Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("v"),
        Colon, Sp, F.Id("V"), Close, Comma, Sp, Open, DefinitionDsl.Id("RootedLeaf"), Sp, F.Id("V"), Sp,
        F.Id("G"), Sp, F.Id("r"), Sp, F.Id("v"), Sp, Colon, Sp, DefinitionDsl.Id("Prop"), Close, Sp, Eq, Sp,
        Neg, Sp, Exists, Sp, Open, F.Id("w"), Sp, Colon, Sp, F.Id("V"), Close, Comma, Sp, F.Id("G"), Dot,
        DefinitionDsl.Id("Adj"), Sp, F.Id("v"), Sp, F.Id("w"), Sp, Land, Sp, F.Id("G"), Dot,
        DefinitionDsl.Id("dist"), Sp, F.Id("r"), Sp, F.Id("v"), Sp, Lt, Sp, F.Id("G"), Dot,
        DefinitionDsl.Id("dist"), Sp, F.Id("r"), Sp, F.Id("w"));

    private static Formula CayleyProbeTree() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("Tree"), Sp, F.Id("V"), Sp, Colon, Sp, DefinitionDsl.Id("Type"), Sp, Open,
        DefinitionDsl.Id("max"), Sp, D(0), Sp, F.Id("u"), Close, Close, Sp, Eq, Sp, OpenBrace, Sp,
        F.Id("G"), Sp, Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Sp, Sp, Bar, Sp, Sp,
        F.Id("G"), Dot, DefinitionDsl.Id("IsTree"), Sp, CloseBrace);

    private static Formula CayleyProbeCut() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("G"), Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("p"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Open, DefinitionDsl.Id("cut"),
        Sp, F.Id("V"), Sp, F.Id("G"), Sp, F.Id("p"), Sp, Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp,
        F.Id("V"), Close, Sp, Eq, Sp, OpenBrace, Sp, DefinitionDsl.Id("Adj"), Sp, Colon, Eq, Sp,
        DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp, F.Id("y"), Sp, Colon, Sp, F.Id("V"), Close, Sp,
        Mapsto, Sp, F.Id("x"), Sp, Neq, Sp, F.Id("p"), Sp, Land, Sp, F.Id("y"), Sp, Neq, Sp, F.Id("p"), Sp,
        Land, Sp, F.Id("G"), Dot, DefinitionDsl.Id("Adj"), Sp, F.Id("x"), Sp, F.Id("y"), Sp, CloseBrace);

    private static Formula CayleyProbeCutparts() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("G"), Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("p"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("cutParts"), Sp, F.Id("V"), Sp, F.Id("G"), Sp, F.Id("p"), Sp, Colon, Sp,
        DefinitionDsl.Id("Set"), Sp, Open, DefinitionDsl.Id("Set"), Sp, F.Id("V"), Close, Close, Sp, Eq, Sp,
        OpenBrace, F.Id("s"), Sp, Colon, Sp, DefinitionDsl.Id("Set"), Sp, F.Id("V"), Sp, Bar, Sp, Exists,
        Sp, Open, F.Id("x"), Sp, Colon, Sp, F.Id("V"), Close, Comma, Sp, F.Id("x"), Sp, Neq, Sp, F.Id("p"),
        Sp, Land, Sp, F.Id("s"), Sp, Eq, Sp, Open, Open, DefinitionDsl.Id("cut"), Sp, F.Id("G"), Sp,
        F.Id("p"), Close, Dot, DefinitionDsl.Id("connectedComponentMk"), Sp, F.Id("x"), Close, Dot,
        DefinitionDsl.Id("supp"), CloseBrace);

    private static Formula CayleyProbeDecompose() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("T"), Colon, Sp,
        DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp, F.Id("V"), Close, Comma, Sp,
        Open, DefinitionDsl.Id("decompose"), Sp, F.Id("V"), Sp, F.Id("p"), Sp, F.Id("T"), Sp, Colon, Sp,
        Open, F.Id("F"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Frame"), Sp,
        F.Id("p"), Close, Sp, Times, Sp, F.Id("F"), Dot, DefinitionDsl.Id("Branches"), Close, Sp, Eq, Sp,
        Langle, Sp, DefinitionDsl.Id("decomposeFrame"), Sp, F.Id("T"), Sp, F.Id("p"), Comma, Sp,
        DefinitionDsl.Id("decomposeBranches"), Sp, F.Id("T"), Sp, F.Id("p"), Rangle);

    private static Formula CayleyProbeDecomposeequiv() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Open, DefinitionDsl.Id("decomposeEquiv"),
        Sp, F.Id("V"), Sp, F.Id("p"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyProbe"), Dot,
        DefinitionDsl.Id("Tree"), Sp, F.Id("V"), Sp, Equiv, Sp, Open, F.Id("F"), Sp, Colon, Sp,
        DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Frame"), Sp, F.Id("p"), Close, Sp, Times,
        Sp, F.Id("F"), Dot, DefinitionDsl.Id("Branches"), Close, Sp, Eq, Sp, OpenBrace, Sp,
        DefinitionDsl.Id("toFun"), Sp, Colon, Eq, Sp, DefinitionDsl.Id("decompose"), Sp, F.Id("p"), Comma,
        Sp, DefinitionDsl.Id("invFun"), Sp, Colon, Eq, Sp, DefinitionDsl.Id("fun"), Sp, Open, F.Id("a"), Sp,
        Colon, Sp, Open, F.Id("F"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyProbe"), Dot,
        DefinitionDsl.Id("Frame"), Sp, F.Id("p"), Close, Sp, Times, Sp, F.Id("F"), Dot,
        DefinitionDsl.Id("Branches"), Close, Sp, Mapsto, Sp, DefinitionDsl.Id("CayleyProbe"), Dot,
        DefinitionDsl.Id("Frame"), Dot, DefinitionDsl.Id("assemble"), Sp, F.Id("a"), Dot,
        DefinitionDsl.Id("snd"), Sp, CloseBrace);

    private static Formula CayleyProbeDecomposeframe() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("T"), Colon, Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp,
        F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("p"), Colon, Sp, F.Id("V"), Close, Comma, Sp,
        Open, DefinitionDsl.Id("decomposeFrame"), Sp, F.Id("V"), Sp, F.Id("T"), Sp, F.Id("p"), Sp, Colon,
        Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Frame"), Sp, F.Id("p"), Close, Sp, Eq,
        Sp, OpenBrace, Sp, DefinitionDsl.Id("parts"), Sp, Colon, Eq, Sp, DefinitionDsl.Id("cutParts"), Sp,
        Open, DefinitionDsl.Id("val"), Sp, F.Id("T"), Close, Sp, F.Id("p"), Comma, Sp,
        DefinitionDsl.Id("cover"), Sp, Colon, Eq, Comma, Sp, DefinitionDsl.Id("separate"), Sp, Colon, Eq,
        Comma, Sp, DefinitionDsl.Id("root"), Sp, Colon, Eq, Sp, DefinitionDsl.Id("fun"), Sp, Open,
        F.Id("s"), Sp, Colon, Sp, DefinitionDsl.Id("val"), Sp, Open, DefinitionDsl.Id("cutParts"), Sp, Open,
        DefinitionDsl.Id("val"), Sp, F.Id("T"), Close, Sp, F.Id("p"), Close, Close, Sp, Mapsto, Sp, Langle,
        Sp, F.Id("h"), Dot, DefinitionDsl.Id("choose"), Rangle, Sp, CloseBrace);

    private static Formula CayleyProbeFiltercard() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Fintype"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("p"), Colon,
        Sp, F.Id("V"), Sp, To, Sp, DefinitionDsl.Id("Prop"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("filterCard"), Sp, F.Id("V"), Sp, F.Id("p"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("N"))), Close, Sp, Eq, Sp, Open, DefinitionDsl.Id("Finset"), Dot,
        DefinitionDsl.Id("filter"), Sp, F.Id("p"), Sp, DefinitionDsl.Id("Finset"), Dot,
        DefinitionDsl.Id("univ"), Close, Dot, DefinitionDsl.Id("card"));

    private static Formula CayleyProbeFiltercardEqNatcard() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Fintype"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("P"), Colon,
        Sp, F.Id("V"), Sp, To, Sp, DefinitionDsl.Id("Prop"), Close, Comma, Sp,
        DefinitionDsl.Id("filterCard"), Sp, F.Id("P"), Sp, Eq, Sp, DefinitionDsl.Id("Nat"), Dot,
        DefinitionDsl.Id("card"), Sp, OpenBrace, Sp, F.Id("x"), Sp, Colon, Sp, F.Id("V"), Sp, Sp, Bar, Sp,
        Sp, F.Id("P"), Sp, F.Id("x"), Sp, CloseBrace);

    private static Formula CayleyProbeFixedrootequiv() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Finite"), Sp, F.Id("V"), CloseBracket, Sp, OpenBracket,
        DefinitionDsl.Id("LinearOrder"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("r"),
        Colon, Sp, F.Id("V"), Close, Comma, Sp, Open, DefinitionDsl.Id("fixedRootEquiv"), Sp, F.Id("V"), Sp,
        F.Id("r"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp,
        F.Id("V"), Sp, Equiv, Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp,
        F.Id("V"), Close, Sp, Eq, Sp, DefinitionDsl.Id("val"), Sp, Open,
        DefinitionDsl.Id("fixedRootEquivSized"), Sp, Open, DefinitionDsl.Id("Nat"), Dot,
        DefinitionDsl.Id("card"), Sp, F.Id("V"), Close, Sp, F.Id("V"), Sp, F.Id("r"), Close);

    private static Formula CayleyProbeRelabelequiv() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("e"), Colon, Sp, F.Id("V"), Sp, Equiv, Sp, F.Id("V"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("relabelEquiv"), Sp, F.Id("V"), Sp, F.Id("e"), Sp, Colon, Sp,
        DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp, F.Id("V"), Sp, Equiv, Sp,
        DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp, F.Id("V"), Close, Sp, Eq, Sp,
        OpenBrace, Sp, DefinitionDsl.Id("toFun"), Sp, Colon, Eq, Sp, DefinitionDsl.Id("relabelTree"), Sp,
        F.Id("e"), Comma, Sp, DefinitionDsl.Id("invFun"), Sp, Colon, Eq, Sp,
        DefinitionDsl.Id("relabelTree"), Sp, F.Id("e"), Dot, DefinitionDsl.Id("symm"), Sp, CloseBrace);

    private static Formula CayleyProbeRelabeltree() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("e"), Colon, Sp, F.Id("V"), Sp, Equiv, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("T"), Colon, Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp, F.Id("V"),
        Close, Comma, Sp, Open, DefinitionDsl.Id("relabelTree"), Sp, F.Id("V"), Sp, F.Id("e"), Sp,
        F.Id("T"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp,
        F.Id("V"), Close, Sp, Eq, Sp, Langle, Sp, DefinitionDsl.Id("SimpleGraph"), Dot,
        DefinitionDsl.Id("comap"), Sp, DefinitionDsl.Id("coe"), Sp, F.Id("e"), Dot,
        DefinitionDsl.Id("symm"), Sp, DefinitionDsl.Id("val"), Sp, F.Id("T"), Rangle);

    private static Formula CayleyProbeShorterneighbor() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("G"), Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, DefinitionDsl.Id("hG"), Colon, Sp, F.Id("G"), Dot, DefinitionDsl.Id("IsTree"),
        Close, Comma, Sp, Forall, Sp, Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("v"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, DefinitionDsl.Id("hv"),
        Colon, Sp, F.Id("v"), Sp, Neq, Sp, F.Id("r"), Close, Comma, Sp, Exists, Sp, Bang, Sp, F.Id("w"), Sp,
        Colon, Sp, F.Id("V"), Comma, Sp, F.Id("G"), Dot, DefinitionDsl.Id("Adj"), Sp, F.Id("v"), Sp,
        F.Id("w"), Sp, Land, Sp, F.Id("G"), Dot, DefinitionDsl.Id("dist"), Sp, F.Id("r"), Sp, F.Id("w"), Sp,
        Lt, Sp, F.Id("G"), Dot, DefinitionDsl.Id("dist"), Sp, F.Id("r"), Sp, F.Id("v"));

    private static Formula CayleyProbeTreeOfDepth() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("G"), Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("d"),
        Colon, Sp, F.Id("V"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("zero"), Colon, Sp, Forall, Sp, Open, F.Id("v"), Sp, Colon, Sp, F.Id("V"), Close,
        Comma, Sp, F.Id("d"), Sp, F.Id("v"), Sp, Eq, Sp, D(0), Sp, Iff, Sp, F.Id("v"), Sp, Eq, Sp,
        F.Id("r"), Close, Comma, Sp, Forall, Sp, Open, DefinitionDsl.Id("step"), Colon, Sp, Forall, Sp,
        Open, F.Id("v"), Sp, F.Id("w"), Sp, Colon, Sp, F.Id("V"), Close, Comma, Sp, F.Id("G"), Dot,
        DefinitionDsl.Id("Adj"), Sp, F.Id("v"), Sp, F.Id("w"), Sp, To, Sp, F.Id("d"), Sp, F.Id("v"), Sp, Eq,
        Sp, F.Id("d"), Sp, F.Id("w"), Sp, Plus, Sp, D(1), Sp, Lor, Sp, F.Id("d"), Sp, F.Id("w"), Sp, Eq, Sp,
        F.Id("d"), Sp, F.Id("v"), Sp, Plus, Sp, D(1), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("parent"), Colon, Sp, Forall, Sp, Open, F.Id("v"), Sp, Colon, Sp, F.Id("V"), Close,
        Comma, Sp, F.Id("v"), Sp, Neq, Sp, F.Id("r"), Sp, To, Sp, Exists, Sp, Bang, Sp, F.Id("w"), Sp,
        Colon, Sp, F.Id("V"), Comma, Sp, F.Id("G"), Dot, DefinitionDsl.Id("Adj"), Sp, F.Id("v"), Sp,
        F.Id("w"), Sp, Land, Sp, F.Id("d"), Sp, F.Id("w"), Sp, Lt, Sp, F.Id("d"), Sp, F.Id("v"), Close,
        Comma, Sp, F.Id("G"), Dot, DefinitionDsl.Id("IsTree"), Sp, Land, Sp, Forall, Sp, Open, F.Id("v"),
        Sp, Colon, Sp, F.Id("V"), Close, Comma, Sp, F.Id("G"), Dot, DefinitionDsl.Id("dist"), Sp, F.Id("r"),
        Sp, F.Id("v"), Sp, Eq, Sp, F.Id("d"), Sp, F.Id("v"));
}
