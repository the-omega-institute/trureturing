using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.CayleyColoring;

internal sealed class CayleyTreeForestReassemblyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reassembling the conflict components turns peaks into vertices without retained children.",
        H("Peak transport in a retained forest"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("forest-peaks"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.forestEquiv_peaks"),
                H("Count transport for marked trees"),
                StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Asymptotics/depanafieu2026stabilization")),
                Blocks(Paragraph(Text("The sample consists of a tree and a spanning subgraph obtained by retaining some edges. Each component is rooted at its entry vertex on paths from the ambient root. Replace its tree by the fixed-root image and leave all intercomponent edges in place. This relates its original peak count to the number of vertices with no retained child in the new rooted tree."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-forest-family"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.Family"),
                H("Family"),
                StatementSource.FromAuthor(Disp(CayleyForestFamily())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-forest-no-retained-child"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.NoRetainedChild"),
                H("No Retained Child"),
                StatementSource.FromAuthor(Disp(CayleyForestNoretainedchild())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-forest-sample"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.Sample"),
                H("Sample"),
                StatementSource.FromAuthor(Disp(CayleyForestSample())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-forest-block"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.block"),
                H("Block"),
                StatementSource.FromAuthor(Disp(CayleyForestBlock())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-forest-entry"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.entry"),
                H("Entry"),
                StatementSource.FromAuthor(Disp(CayleyForestEntry())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The minimum is taken over the finite component with distance measured in the original tree."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-forest-forest-equiv"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.forestEquiv"),
                H("Forest Equiv"),
                StatementSource.FromAuthor(Disp(CayleyForestForestequiv())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-forest-local-tree"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.localTree"),
                H("Local Tree"),
                StatementSource.FromAuthor(Disp(CayleyForestLocaltree())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The underlying graph is the induced retained graph on the component. Acyclicity of the original tree and connectivity of the component supply its tree certificate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-forest-parts"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.parts"),
                H("Parts"),
                StatementSource.FromAuthor(Disp(CayleyForestParts())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-forest-replace"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.replace"),
                H("Replace"),
                StatementSource.FromAuthor(Disp(CayleyForestReplace())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-forest-union-graph"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.unionGraph"),
                H("Union Graph"),
                StatementSource.FromAuthor(Disp(CayleyForestUniongraph())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-marks-deleted"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.Deleted"),
                H("Deleted"),
                StatementSource.FromAuthor(Disp(CayleyMarksDeleted())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-marks-has-target"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.HasTarget"),
                H("Has Target"),
                StatementSource.FromAuthor(Disp(CayleyMarksHastarget())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-marks-marked"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.Marked"),
                H("Marked"),
                StatementSource.FromAuthor(Disp(CayleyMarksMarked())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-marks-conflict-retained"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.conflict_retained"),
                H("Conflict retained"),
                StatementSource.FromAuthor(Disp(CayleyMarksConflictRetained())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-marks-fill"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.fill"),
                H("Fill"),
                StatementSource.FromAuthor(Disp(CayleyMarksFill())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-marks-join"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.join"),
                H("Join"),
                StatementSource.FromAuthor(Disp(CayleyMarksJoin())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-marks-join-retained"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.join_retained"),
                H("Join retained"),
                StatementSource.FromAuthor(Disp(CayleyMarksJoinRetained())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-marks-marked-equiv"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.markedEquiv"),
                H("Marked Equiv"),
                StatementSource.FromAuthor(Disp(CayleyMarksMarkedequiv())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-marks-marked-forest-equiv"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.markedForestEquiv"),
                H("Marked Forest Equiv"),
                StatementSource.FromAuthor(Disp(CayleyMarksMarkedforestequiv())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-marks-retained"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.retained"),
                H("Retained"),
                StatementSource.FromAuthor(Disp(CayleyMarksRetained())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-marks-retained-child-iff"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.retained_child_iff"),
                H("Retained child iff"),
                StatementSource.FromAuthor(Disp(CayleyMarksRetainedChildIff())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-marks-retained-le"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.retained_le"),
                H("Retained le"),
                StatementSource.FromAuthor(Disp(CayleyMarksRetainedLe())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-marks-split"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.split"),
                H("Split"),
                StatementSource.FromAuthor(Disp(CayleyMarksSplit())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition)),
        []));

    private static Formula Statement1()
    {
        var v = F.Id("V");
        var r = F.Id("r");
        var s = F.Id("S");
        var image = At(Call("forestEquiv", r), s);
        var oldPeaks = Call("card", Call("PeakSet", Call("retained", s)));
        var newLeaves = Call("card", Call("NoRetainedChildSet",
            Call("tree", image), Call("retained", image), r));
        return All("V", F.Id("Type"), Seq(Instance("Fintype", v), Instance("LinearOrder", v),
            All("r", v, All("S", Call("ForestSample", v), Equal(oldPeaks, newLeaves)))));
    }

    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);

    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(x), Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula Instance(string type, Formula parameter) =>
        Seq(OpenBracket, Call(type, parameter), CloseBracket, Sp);

    private static Formula CayleyForestFamily() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("P"), Colon, Sp, DefinitionDsl.Id("Set"), Sp, Open, DefinitionDsl.Id("Set"), Sp,
        F.Id("V"), Close, Close, Comma, Sp, Open, DefinitionDsl.Id("Family"), Sp, F.Id("V"), Sp, F.Id("P"),
        Sp, Colon, Sp, DefinitionDsl.Id("Type"), Close, Sp, Eq, Sp, Open, F.Id("s"), Sp, Colon, Sp,
        DefinitionDsl.Id("val"), Sp, F.Id("P"), Close, Sp, To, Sp, DefinitionDsl.Id("CayleyProbe"), Dot,
        DefinitionDsl.Id("Tree"), Sp, DefinitionDsl.Id("coe"), Sp, F.Id("s"));

    private static Formula CayleyForestNoretainedchild() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("T"), Colon, Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp,
        F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("H"), Colon, Sp,
        DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("r"),
        Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("v"), Colon, Sp, F.Id("V"), Close,
        Comma, Sp, Open, DefinitionDsl.Id("NoRetainedChild"), Sp, F.Id("V"), Sp, F.Id("T"), Sp, F.Id("H"),
        Sp, F.Id("r"), Sp, F.Id("v"), Sp, Colon, Sp, DefinitionDsl.Id("Prop"), Close, Sp, Eq, Sp, Neg, Sp,
        Exists, Sp, Open, F.Id("w"), Sp, Colon, Sp, F.Id("V"), Close, Comma, Sp, F.Id("H"), Dot,
        DefinitionDsl.Id("Adj"), Sp, F.Id("v"), Sp, F.Id("w"), Sp, Land, Sp, Open, DefinitionDsl.Id("val"),
        Sp, F.Id("T"), Close, Dot, DefinitionDsl.Id("dist"), Sp, F.Id("r"), Sp, F.Id("v"), Sp, Lt, Sp, Open,
        DefinitionDsl.Id("val"), Sp, F.Id("T"), Close, Dot, DefinitionDsl.Id("dist"), Sp, F.Id("r"), Sp,
        F.Id("w"));

    private static Formula CayleyForestSample() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("Sample"), Sp, F.Id("V"), Sp, Colon, Sp, DefinitionDsl.Id("Type"), Sp, Open,
        DefinitionDsl.Id("max"), Sp, D(0), Sp, F.Id("u"), Close, Close, Sp, Eq, Sp, OpenBrace, Sp,
        F.Id("s"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp,
        F.Id("V"), Sp, Times, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Sp, Sp, Bar, Sp, Sp,
        F.Id("s"), Dot, D(2), Sp, Leq, Sp, DefinitionDsl.Id("val"), Sp, F.Id("s"), Dot, D(1), Sp, CloseBrace);

    private static Formula CayleyForestBlock() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("P"), Colon, Sp, DefinitionDsl.Id("Set"), Sp, Open, DefinitionDsl.Id("Set"), Sp,
        F.Id("V"), Close, Close, Comma, Sp, Forall, Sp, Open, F.Id("U"), Colon, Sp,
        DefinitionDsl.Id("CayleyForest"), Dot, DefinitionDsl.Id("Family"), Sp, F.Id("P"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("s"), Colon, Sp, DefinitionDsl.Id("val"), Sp, F.Id("P"), Close, Comma, Sp,
        Open, DefinitionDsl.Id("block"), Sp, F.Id("V"), Sp, F.Id("P"), Sp, F.Id("U"), Sp, F.Id("s"), Sp,
        Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Sp, Eq, Sp,
        DefinitionDsl.Id("SimpleGraph"), Dot, DefinitionDsl.Id("map"), Sp, DefinitionDsl.Id("coe"), Sp,
        Open, DefinitionDsl.Id("Function"), Dot, DefinitionDsl.Id("Embedding"), Dot,
        DefinitionDsl.Id("subtype"), Sp, DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp, Colon, Sp,
        F.Id("V"), Close, Sp, Mapsto, Sp, F.Id("x"), Sp, InMacro, Sp, DefinitionDsl.Id("val"), Sp,
        F.Id("s"), Close, Sp, DefinitionDsl.Id("val"), Sp, Open, F.Id("U"), Sp, F.Id("s"), Close);

    private static Formula CayleyForestEntry() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Finite"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("T"), Colon, Sp,
        DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("H"),
        Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("s"), Colon, Sp, DefinitionDsl.Id("Set"), Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hs"), Colon, Sp, F.Id("s"), Sp, InMacro, Sp, DefinitionDsl.Id("parts"), Sp,
        F.Id("H"), Close, Comma, Sp, DefinitionDsl.Id("entry"), Sp, F.Id("T"), Sp, F.Id("r"), Sp, F.Id("H"),
        Sp, F.Id("s"), Sp, DefinitionDsl.Id("hs"), Sp, Eq, Sp, DefinitionDsl.Id("argmin"), Sp, Open,
        DefinitionDsl.Id("fun"), Sp, Open, F.Id("v"), Sp, Colon, Sp, F.Id("s"), Close, Sp, Mapsto, Sp,
        F.Id("T"), Dot, DefinitionDsl.Id("val"), Dot, DefinitionDsl.Id("dist"), Sp, F.Id("r"), Sp,
        F.Id("v"), Dot, DefinitionDsl.Id("val"), Close);

    private static Formula CayleyForestForestequiv() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Finite"), Sp, F.Id("V"), CloseBracket, Sp, OpenBracket,
        DefinitionDsl.Id("LinearOrder"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("r"),
        Colon, Sp, F.Id("V"), Close, Comma, Sp, Open, DefinitionDsl.Id("forestEquiv"), Sp, F.Id("V"), Sp,
        F.Id("r"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyForest"), Dot, DefinitionDsl.Id("Sample"), Sp,
        F.Id("V"), Sp, Equiv, Sp, DefinitionDsl.Id("CayleyForest"), Dot, DefinitionDsl.Id("Sample"), Sp,
        F.Id("V"), Close, Sp, Eq, Sp, OpenBrace, Sp, DefinitionDsl.Id("toFun"), Sp, Colon, Eq, Sp,
        DefinitionDsl.Id("fun"), Sp, Open, F.Id("S"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyForest"), Dot,
        DefinitionDsl.Id("Sample"), Sp, F.Id("V"), Close, Sp, Mapsto, Sp, DefinitionDsl.Id("transform"), Sp,
        F.Id("r"), Sp, F.Id("S"), Sp, DefinitionDsl.Id("false"), Comma, Sp, DefinitionDsl.Id("invFun"), Sp,
        Colon, Eq, Sp, DefinitionDsl.Id("fun"), Sp, Open, F.Id("S"), Sp, Colon, Sp,
        DefinitionDsl.Id("CayleyForest"), Dot, DefinitionDsl.Id("Sample"), Sp, F.Id("V"), Close, Sp, Eq, Gt,
        Sp, DefinitionDsl.Id("transform"), Sp, F.Id("r"), Sp, F.Id("S"), Sp, DefinitionDsl.Id("true"), Sp,
        CloseBrace);

    private static Formula CayleyForestLocaltree() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("T"), Colon, Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp,
        F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("H"), Colon, Sp,
        DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("h"),
        Colon, Sp, F.Id("H"), Sp, Leq, Sp, DefinitionDsl.Id("val"), Sp, F.Id("T"), Close, Comma, Sp, Forall,
        Sp, Open, F.Id("s"), Colon, Sp, DefinitionDsl.Id("Set"), Sp, F.Id("V"), Close, Comma, Sp, Forall,
        Sp, Open, DefinitionDsl.Id("hs"), Colon, Sp, F.Id("s"), Sp, InMacro, Sp, DefinitionDsl.Id("parts"),
        Sp, F.Id("H"), Close, Comma, Sp, DefinitionDsl.Id("val"), Sp, Open, DefinitionDsl.Id("localTree"),
        Sp, F.Id("T"), Sp, F.Id("H"), Sp, F.Id("h"), Sp, F.Id("s"), Sp, DefinitionDsl.Id("hs"), Close, Sp,
        Eq, Sp, DefinitionDsl.Id("SimpleGraph"), Dot, DefinitionDsl.Id("induce"), Sp, F.Id("s"), Sp,
        F.Id("H"));

    private static Formula CayleyForestParts() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("H"), Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("parts"), Sp, F.Id("V"), Sp, F.Id("H"), Sp, Colon, Sp, DefinitionDsl.Id("Set"), Sp,
        Open, DefinitionDsl.Id("Set"), Sp, F.Id("V"), Close, Close, Sp, Eq, Sp, DefinitionDsl.Id("Set"),
        Dot, DefinitionDsl.Id("range"), Sp, DefinitionDsl.Id("fun"), Sp, Open, F.Id("c"), Sp, Colon, Sp,
        F.Id("H"), Dot, DefinitionDsl.Id("ConnectedComponent"), Close, Sp, Mapsto, Sp, F.Id("c"), Dot,
        DefinitionDsl.Id("supp"));

    private static Formula CayleyForestReplace() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Finite"), Sp, F.Id("V"), CloseBracket, Sp, Forall, Sp, Open, F.Id("S"), Colon, Sp,
        DefinitionDsl.Id("CayleyForest"), Dot, DefinitionDsl.Id("Sample"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("U"), Colon, Sp, DefinitionDsl.Id("CayleyForest"), Dot,
        DefinitionDsl.Id("Family"), Sp, Open, DefinitionDsl.Id("parts"), Sp, Open, DefinitionDsl.Id("val"),
        Sp, F.Id("S"), Close, Dot, D(2), Close, Close, Comma, Sp, Open, DefinitionDsl.Id("replace"), Sp,
        F.Id("V"), Sp, F.Id("S"), Sp, F.Id("U"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyForest"), Dot,
        DefinitionDsl.Id("Sample"), Sp, F.Id("V"), Close, Sp, Eq, Sp, DefinitionDsl.Id("let"), Sp,
        F.Id("T"), Sp, Colon, Eq, Sp, Open, DefinitionDsl.Id("val"), Sp, F.Id("S"), Close, Dot, D(1), Semi,
        Sp, DefinitionDsl.Id("let"), Sp, F.Id("H"), Sp, Colon, Eq, Sp, Open, DefinitionDsl.Id("val"), Sp,
        F.Id("S"), Close, Dot, D(2), Semi, Sp, DefinitionDsl.Id("let"), Sp, F.Id("C"), Sp, Colon, Eq, Sp,
        DefinitionDsl.Id("val"), Sp, F.Id("T"), Sp, Setminus, Sp, F.Id("H"), Semi, Sp,
        DefinitionDsl.Id("let"), Sp, DefinitionDsl.Id("Hnew"), Sp, Colon, Eq, Sp,
        DefinitionDsl.Id("unionGraph"), Sp, F.Id("U"), Semi, Sp, Langle, Sp, Open, Langle, Sp, F.Id("C"),
        Sp, Operatorname, Grp(F.Id("sup")), Sp, DefinitionDsl.Id("Hnew"), Comma, Sp, DefinitionDsl.Id("ht"),
        Rangle, Sp, Comma, Sp, DefinitionDsl.Id("Hnew"), Close, Rangle);

    private static Formula CayleyForestUniongraph() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("P"), Colon, Sp, DefinitionDsl.Id("Set"), Sp, Open, DefinitionDsl.Id("Set"), Sp,
        F.Id("V"), Close, Close, Comma, Sp, Forall, Sp, Open, F.Id("U"), Colon, Sp,
        DefinitionDsl.Id("CayleyForest"), Dot, DefinitionDsl.Id("Family"), Sp, F.Id("P"), Close, Comma, Sp,
        Open, DefinitionDsl.Id("unionGraph"), Sp, F.Id("V"), Sp, F.Id("P"), Sp, F.Id("U"), Sp, Colon, Sp,
        DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Sp, Eq, Sp, Operatorname, Grp(F.Id("iSup")),
        Sp, Open, F.Id("s"), Sp, Colon, Sp, DefinitionDsl.Id("val"), Sp, F.Id("P"), Close, Comma, Sp,
        DefinitionDsl.Id("block"), Sp, F.Id("U"), Sp, F.Id("s"));

    private static Formula CayleyMarksDeleted() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("S"), Colon, Sp, DefinitionDsl.Id("CayleyForest"), Dot, DefinitionDsl.Id("Sample"), Sp,
        F.Id("V"), Close, Comma, Sp, Open, DefinitionDsl.Id("Deleted"), Sp, F.Id("V"), Sp, F.Id("S"), Sp,
        Colon, Sp, DefinitionDsl.Id("Type"), Sp, Open, DefinitionDsl.Id("max"), Sp, D(0), Sp, F.Id("u"),
        Close, Close, Sp, Eq, Sp, OpenBrace, Sp, F.Id("e"), Sp, Colon, Sp, DefinitionDsl.Id("Sym2"), Sp,
        F.Id("V"), Sp, Sp, Bar, Sp, Sp, F.Id("e"), Sp, InMacro, Sp, Open, DefinitionDsl.Id("val"), Sp, Open,
        DefinitionDsl.Id("val"), Sp, F.Id("S"), Close, Dot, D(1), Close, Dot, DefinitionDsl.Id("edgeSet"),
        Sp, Land, Sp, F.Id("e"), Sp, Neg, Sp, InMacro, Sp, Open, DefinitionDsl.Id("val"), Sp, F.Id("S"),
        Close, Dot, D(2), Dot, DefinitionDsl.Id("edgeSet"), Sp, CloseBrace);

    private static Formula CayleyMarksHastarget() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Zero"), Sp, F.Id("A"), CloseBracket, Sp, Forall, Sp, Open, F.Id("T"), Colon, Sp,
        DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("d"),
        Colon, Sp, DefinitionDsl.Id("CayleyColors"), Dot, DefinitionDsl.Id("Away"), Sp, F.Id("r"), Sp, To,
        Sp, F.Id("A"), Close, Comma, Sp, Forall, Sp, Open, F.Id("w"), Colon, Sp, F.Id("V"), Close, Comma,
        Sp, Open, DefinitionDsl.Id("HasTarget"), Sp, F.Id("V"), Sp, F.Id("A"), Sp, F.Id("T"), Sp, F.Id("r"),
        Sp, F.Id("d"), Sp, F.Id("w"), Sp, Colon, Sp, DefinitionDsl.Id("Prop"), Close, Sp, Eq, Sp, Exists,
        Sp, Open, F.Id("v"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyColors"), Dot, DefinitionDsl.Id("Away"),
        Sp, F.Id("r"), Close, Comma, Sp, DefinitionDsl.Id("parent"), Sp, F.Id("T"), Sp, F.Id("r"), Sp,
        F.Id("v"), Sp, Eq, Sp, F.Id("w"), Sp, Land, Sp, F.Id("d"), Sp, F.Id("v"), Sp, Eq, Sp, D(0));

    private static Formula CayleyMarksMarked() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Zero"), Sp, F.Id("A"), CloseBracket, Sp, Open, DefinitionDsl.Id("Marked"), Sp,
        F.Id("V"), Sp, F.Id("A"), Sp, Colon, Sp, DefinitionDsl.Id("Type"), Sp, Open,
        DefinitionDsl.Id("max"), Sp, F.Id("u"), Sp, F.Id("u"), Sp, F.Id("w"), Close, Close, Sp, Eq, Sp,
        Open, F.Id("S"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyForest"), Dot, DefinitionDsl.Id("Sample"),
        Sp, F.Id("V"), Close, Sp, Times, Sp, Open, DefinitionDsl.Id("CayleyMarks"), Dot,
        DefinitionDsl.Id("Deleted"), Sp, F.Id("S"), Sp, To, Sp, OpenBrace, Sp, F.Id("x"), Sp, Colon, Sp,
        F.Id("A"), Sp, Sp, Bar, Sp, Sp, F.Id("x"), Sp, Neq, Sp, D(0), Sp, CloseBrace, Close);

    private static Formula CayleyMarksConflictRetained() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("AddGroup"), Sp, F.Id("A"), CloseBracket, Sp, Forall, Sp, Open, F.Id("T"), Colon,
        Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("c"),
        Colon, Sp, F.Id("V"), Sp, To, Sp, F.Id("A"), Close, Comma, Sp, DefinitionDsl.Id("retained"), Sp,
        F.Id("T"), Sp, Open, Open, DefinitionDsl.Id("edgeColorEquiv"), Sp, F.Id("T"), Sp, F.Id("r"), Close,
        Sp, F.Id("c"), Close, Dot, D(2), Sp, Eq, Sp, DefinitionDsl.Id("conflict"), Sp, Open,
        DefinitionDsl.Id("val"), Sp, F.Id("T"), Close, Sp, F.Id("c"));

    private static Formula CayleyMarksFill() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Zero"), Sp, F.Id("A"), CloseBracket, Sp, Forall, Sp, Open, F.Id("x"), Colon, Sp,
        DefinitionDsl.Id("CayleyMarks"), Dot, DefinitionDsl.Id("Marked"), Sp, F.Id("V"), Sp, F.Id("A"),
        Close, Comma, Sp, Forall, Sp, Open, F.Id("e"), Colon, Sp, DefinitionDsl.Id("val"), Sp, Open,
        DefinitionDsl.Id("val"), Sp, Open, DefinitionDsl.Id("val"), Sp, F.Id("x"), Dot,
        DefinitionDsl.Id("fst"), Close, Dot, D(1), Close, Dot, DefinitionDsl.Id("edgeSet"), Close, Comma,
        Sp, Open, DefinitionDsl.Id("fill"), Sp, F.Id("V"), Sp, F.Id("A"), Sp, F.Id("x"), Sp, F.Id("e"), Sp,
        Colon, Sp, F.Id("A"), Close, Sp, Eq, Sp, DefinitionDsl.Id("if"), Sp, F.Id("h"), Sp, Colon, Sp,
        DefinitionDsl.Id("val"), Sp, F.Id("e"), Sp, InMacro, Sp, Open, DefinitionDsl.Id("val"), Sp,
        F.Id("x"), Dot, DefinitionDsl.Id("fst"), Close, Dot, D(2), Dot, DefinitionDsl.Id("edgeSet"), Sp,
        DefinitionDsl.Id("then"), Sp, D(0), Sp, DefinitionDsl.Id("else"), Sp, DefinitionDsl.Id("val"), Sp,
        Open, F.Id("x"), Dot, DefinitionDsl.Id("snd"), Sp, Langle, Sp, DefinitionDsl.Id("val"), Sp,
        F.Id("e"), Rangle, Sp, Close);

    private static Formula CayleyMarksJoin() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Zero"), Sp, F.Id("A"), CloseBracket, Sp, Forall, Sp, Open, F.Id("x"), Colon, Sp,
        DefinitionDsl.Id("CayleyMarks"), Dot, DefinitionDsl.Id("Marked"), Sp, F.Id("V"), Sp, F.Id("A"),
        Close, Comma, Sp, Open, DefinitionDsl.Id("join"), Sp, F.Id("V"), Sp, F.Id("A"), Sp, F.Id("x"), Sp,
        Colon, Sp, Open, F.Id("T"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyProbe"), Dot,
        DefinitionDsl.Id("Tree"), Sp, F.Id("V"), Close, Sp, Times, Sp, Open, DefinitionDsl.Id("val"), Sp,
        Open, DefinitionDsl.Id("val"), Sp, F.Id("T"), Close, Dot, DefinitionDsl.Id("edgeSet"), Sp, To, Sp,
        F.Id("A"), Close, Close, Sp, Eq, Sp, Langle, Sp, Open, DefinitionDsl.Id("val"), Sp, F.Id("x"), Dot,
        DefinitionDsl.Id("fst"), Close, Dot, D(1), Comma, Sp, DefinitionDsl.Id("fill"), Sp, F.Id("x"),
        Rangle);

    private static Formula CayleyMarksJoinRetained() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Zero"), Sp, F.Id("A"), CloseBracket, Sp, Forall, Sp, Open, F.Id("x"), Colon, Sp,
        DefinitionDsl.Id("CayleyMarks"), Dot, DefinitionDsl.Id("Marked"), Sp, F.Id("V"), Sp, F.Id("A"),
        Close, Comma, Sp, DefinitionDsl.Id("retained"), Sp, Open, DefinitionDsl.Id("val"), Sp, F.Id("x"),
        Dot, DefinitionDsl.Id("fst"), Close, Dot, D(1), Sp, Open, DefinitionDsl.Id("fill"), Sp, F.Id("x"),
        Close, Sp, Eq, Sp, Open, DefinitionDsl.Id("val"), Sp, F.Id("x"), Dot, DefinitionDsl.Id("fst"),
        Close, Dot, D(2));

    private static Formula CayleyMarksMarkedequiv() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Zero"), Sp, F.Id("A"), CloseBracket, Sp, Open, DefinitionDsl.Id("markedEquiv"),
        Sp, F.Id("V"), Sp, F.Id("A"), Sp, Colon, Sp, Open, F.Id("T"), Sp, Colon, Sp,
        DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp, F.Id("V"), Close, Sp, Times, Sp,
        Open, DefinitionDsl.Id("val"), Sp, Open, DefinitionDsl.Id("val"), Sp, F.Id("T"), Close, Dot,
        DefinitionDsl.Id("edgeSet"), Sp, To, Sp, F.Id("A"), Close, Sp, Equiv, Sp,
        DefinitionDsl.Id("CayleyMarks"), Dot, DefinitionDsl.Id("Marked"), Sp, F.Id("V"), Sp, F.Id("A"),
        Close, Sp, Eq, Sp, OpenBrace, Sp, DefinitionDsl.Id("toFun"), Sp, Colon, Eq, Sp,
        DefinitionDsl.Id("split"), Comma, Sp, DefinitionDsl.Id("invFun"), Sp, Colon, Eq, Sp,
        DefinitionDsl.Id("join"), Sp, CloseBrace);

    private static Formula CayleyMarksMarkedforestequiv() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Zero"), Sp, F.Id("A"), CloseBracket, Sp, OpenBracket, DefinitionDsl.Id("Finite"),
        Sp, F.Id("V"), CloseBracket, Sp, OpenBracket, DefinitionDsl.Id("LinearOrder"), Sp, F.Id("V"),
        CloseBracket, Sp, Forall, Sp, Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("markedForestEquiv"), Sp, F.Id("V"), Sp, F.Id("A"), Sp, F.Id("r"), Sp, Colon, Sp,
        DefinitionDsl.Id("CayleyMarks"), Dot, DefinitionDsl.Id("Marked"), Sp, F.Id("V"), Sp, F.Id("A"), Sp,
        Equiv, Sp, DefinitionDsl.Id("CayleyMarks"), Dot, DefinitionDsl.Id("Marked"), Sp, F.Id("V"), Sp,
        F.Id("A"), Close, Sp, Eq, Sp, Open, DefinitionDsl.Id("forestEquiv"), Sp, F.Id("r"), Close, Dot,
        DefinitionDsl.Id("sigmaCongr"), Sp, DefinitionDsl.Id("fun"), Sp, Open, F.Id("S"), Sp, Colon, Sp,
        DefinitionDsl.Id("CayleyForest"), Dot, DefinitionDsl.Id("Sample"), Sp, F.Id("V"), Close, Sp, Eq, Gt,
        Sp, DefinitionDsl.Id("have"), Sp, F.Id("e"), Sp, Colon, Eq, Sp, DefinitionDsl.Id("Set"), Dot,
        DefinitionDsl.Id("equivOfEq"), Semi, Sp, Open, Open, DefinitionDsl.Id("deletedEquiv"), Sp,
        F.Id("S"), Close, Dot, DefinitionDsl.Id("trans"), Sp, Open, F.Id("e"), Dot,
        DefinitionDsl.Id("trans"), Sp, Open, DefinitionDsl.Id("deletedEquiv"), Sp, Open, Open,
        DefinitionDsl.Id("forestEquiv"), Sp, F.Id("r"), Close, Sp, F.Id("S"), Close, Close, Dot,
        DefinitionDsl.Id("symm"), Close, Close, Dot, DefinitionDsl.Id("arrowCongr"), Sp, Open,
        DefinitionDsl.Id("Equiv"), Dot, DefinitionDsl.Id("refl"), Sp, OpenBrace, Sp, F.Id("x"), Sp, Colon,
        Sp, F.Id("A"), Sp, Sp, Bar, Sp, Sp, F.Id("x"), Sp, Neq, Sp, D(0), Sp, CloseBrace, Close);

    private static Formula CayleyMarksRetained() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Zero"), Sp, F.Id("A"), CloseBracket, Sp, Forall, Sp, Open, F.Id("T"), Colon, Sp,
        DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("d"), Colon, Sp, DefinitionDsl.Id("val"), Sp, Open, DefinitionDsl.Id("val"),
        Sp, F.Id("T"), Close, Dot, DefinitionDsl.Id("edgeSet"), Sp, To, Sp, F.Id("A"), Close, Comma, Sp,
        Open, DefinitionDsl.Id("retained"), Sp, F.Id("V"), Sp, F.Id("A"), Sp, F.Id("T"), Sp, F.Id("d"), Sp,
        Colon, Sp, DefinitionDsl.Id("SimpleGraph"), Sp, F.Id("V"), Close, Sp, Eq, Sp,
        DefinitionDsl.Id("SimpleGraph"), Dot, DefinitionDsl.Id("fromEdgeSet"), Sp, OpenBrace, F.Id("e"), Sp,
        Colon, Sp, DefinitionDsl.Id("Sym2"), Sp, F.Id("V"), Sp, Bar, Sp, Exists, Sp, Open, F.Id("h"), Sp,
        Colon, Sp, F.Id("e"), Sp, InMacro, Sp, Open, DefinitionDsl.Id("val"), Sp, F.Id("T"), Close, Dot,
        DefinitionDsl.Id("edgeSet"), Close, Comma, Sp, F.Id("d"), Sp, Langle, Sp, F.Id("e"), Comma, Sp,
        F.Id("h"), Rangle, Sp, Eq, Sp, D(0), CloseBrace);

    private static Formula CayleyMarksRetainedChildIff() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Zero"), Sp, F.Id("A"), CloseBracket, Sp, Forall, Sp, Open, F.Id("T"), Colon, Sp,
        DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("r"), Colon, Sp, F.Id("V"), Close, Comma, Sp, Forall, Sp, Open, F.Id("d"),
        Colon, Sp, DefinitionDsl.Id("val"), Sp, Open, DefinitionDsl.Id("val"), Sp, F.Id("T"), Close, Dot,
        DefinitionDsl.Id("edgeSet"), Sp, To, Sp, F.Id("A"), Close, Comma, Sp, Forall, Sp, Open, F.Id("w"),
        Colon, Sp, F.Id("V"), Close, Comma, Sp, Open, Exists, Sp, Open, F.Id("v"), Sp, Colon, Sp, F.Id("V"),
        Close, Comma, Sp, Open, DefinitionDsl.Id("retained"), Sp, F.Id("T"), Sp, F.Id("d"), Close, Dot,
        DefinitionDsl.Id("Adj"), Sp, F.Id("w"), Sp, F.Id("v"), Sp, Land, Sp, Open, DefinitionDsl.Id("val"),
        Sp, F.Id("T"), Close, Dot, DefinitionDsl.Id("dist"), Sp, F.Id("r"), Sp, F.Id("w"), Sp, Lt, Sp, Open,
        DefinitionDsl.Id("val"), Sp, F.Id("T"), Close, Dot, DefinitionDsl.Id("dist"), Sp, F.Id("r"), Sp,
        F.Id("v"), Close, Sp, Iff, Sp, DefinitionDsl.Id("CayleyMarks"), Dot, DefinitionDsl.Id("HasTarget"),
        Sp, F.Id("T"), Sp, F.Id("r"), Sp, Open, F.Id("d"), Sp, Circ, Sp, DefinitionDsl.Id("coe"), Sp, Open,
        DefinitionDsl.Id("edgeEquiv"), Sp, F.Id("T"), Sp, F.Id("r"), Close, Close, Sp, F.Id("w"));

    private static Formula CayleyMarksRetainedLe() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Zero"), Sp, F.Id("A"), CloseBracket, Sp, Forall, Sp, Open, F.Id("T"), Colon, Sp,
        DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp, F.Id("V"), Close, Comma, Sp,
        Forall, Sp, Open, F.Id("d"), Colon, Sp, DefinitionDsl.Id("val"), Sp, Open, DefinitionDsl.Id("val"),
        Sp, F.Id("T"), Close, Dot, DefinitionDsl.Id("edgeSet"), Sp, To, Sp, F.Id("A"), Close, Comma, Sp,
        DefinitionDsl.Id("retained"), Sp, F.Id("T"), Sp, F.Id("d"), Sp, Leq, Sp, DefinitionDsl.Id("val"),
        Sp, F.Id("T"));

    private static Formula CayleyMarksSplit() =>
        Seq(
        Forall, Sp, Open, F.Id("V"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("A"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("Zero"), Sp, F.Id("A"), CloseBracket, Sp, Forall, Sp, Open, F.Id("x"), Colon, Sp,
        Open, F.Id("T"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyProbe"), Dot, DefinitionDsl.Id("Tree"), Sp,
        F.Id("V"), Close, Sp, Times, Sp, Open, DefinitionDsl.Id("val"), Sp, Open, DefinitionDsl.Id("val"),
        Sp, F.Id("T"), Close, Dot, DefinitionDsl.Id("edgeSet"), Sp, To, Sp, F.Id("A"), Close, Close, Comma,
        Sp, Open, DefinitionDsl.Id("split"), Sp, F.Id("V"), Sp, F.Id("A"), Sp, F.Id("x"), Sp, Colon, Sp,
        DefinitionDsl.Id("CayleyMarks"), Dot, DefinitionDsl.Id("Marked"), Sp, F.Id("V"), Sp, F.Id("A"),
        Close, Sp, Eq, Sp, DefinitionDsl.Id("let"), Sp, F.Id("H"), Sp, Colon, Eq, Sp,
        DefinitionDsl.Id("retained"), Sp, F.Id("x"), Dot, DefinitionDsl.Id("fst"), Sp, F.Id("x"), Dot,
        DefinitionDsl.Id("snd"), Semi, Sp, Langle, Sp, Langle, Sp, Open, F.Id("x"), Dot,
        DefinitionDsl.Id("fst"), Comma, Sp, F.Id("H"), Close, Rangle, Sp, Comma, Sp,
        DefinitionDsl.Id("fun"), Sp, Open, F.Id("e"), Sp, Colon, Sp, DefinitionDsl.Id("CayleyMarks"), Dot,
        DefinitionDsl.Id("Deleted"), Sp, Langle, Sp, Open, F.Id("x"), Dot, DefinitionDsl.Id("fst"), Comma,
        Sp, F.Id("H"), Close, Rangle, Sp, Close, Sp, Mapsto, Sp, Langle, Sp, F.Id("x"), Dot,
        DefinitionDsl.Id("snd"), Sp, Langle, Sp, DefinitionDsl.Id("val"), Sp, F.Id("e"), Comma, Sp,
        DefinitionDsl.Id("he"), Rangle, Sp, Rangle, Sp, Rangle);
}
