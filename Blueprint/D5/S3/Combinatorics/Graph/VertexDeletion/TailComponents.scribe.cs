using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.VertexDeletion;

internal sealed class TailComponentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/ugurlu2026objectivetransfer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual tail runs and induced survivor scores for exact vertex cuts.",
        H("Induced survivor components and tail runs"),
        Blocks(
            Describe.Lean(DescribeId.Create("vertex"), DeclarationHandle.Create(Prefix + "Vertex"),
                H("Vertex"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Open, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Comma, Sp, Word("Vertex"), Sp, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Eq, Sp, Word("Fin"), Sp, Open, Id("p"), Sp, Plus, Sp, Id("t"), Close, Sp, new Formula.NamedConstant(FormulaIdentifier.Create("Sum")), Sp, Open, Word("Fin"), Sp, Id("b"), Sp, Times, Sp, Word("Fin"), Sp, Id("k"), Close))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Use a disjoint sum of spine positions and the pairs of hub and leaf indices."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("host"), DeclarationHandle.Create(Prefix + "host"),
                H("Host"), StatementSource.FromAuthor(Disp(Seq(Word("host"), Sp, Colon, Sp, OpenBrace, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Rightarrow, Sp, Open, Word("Fin"), Sp, Id("b"), Sp, Rightarrow, Sp, Word("Fin"), Sp, Id("p"), Close, Sp, Rightarrow, Sp, Word("SimpleGraph"), Sp, Open, Word("Vertex"), Sp, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Close))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("The spine edges form a path and every leaf is adjacent to its indexed hub."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("position"), DeclarationHandle.Create(Prefix + "position"),
                H("Position"), StatementSource.FromAuthor(Disp(Seq(Word("position"), Sp, Colon, Sp, OpenBrace, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Rightarrow, Sp, Open, Word("Fin"), Sp, Id("b"), Sp, Rightarrow, Sp, Word("Fin"), Sp, Id("p"), Close, Sp, Rightarrow, Sp, Word("Vertex"), Sp, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Rightarrow, Sp, Seq(Mathbb, Grp(Id("N")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Project a spine vertex to its index and a leaf to its hub index."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("tail-vertex"), DeclarationHandle.Create(Prefix + "tailVertex"),
                H("Tail vertex"), StatementSource.FromAuthor(Disp(Seq(Word("tailVertex"), Sp, Colon, Sp, OpenBrace, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Rightarrow, Sp, Word("Fin"), Sp, Id("t"), Sp, Rightarrow, Sp, Word("Vertex"), Sp, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Insert the tail index after all p prefix positions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("survivors"), DeclarationHandle.Create(Prefix + "survivors"),
                H("Survivors"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, OpenBracket, Word("DecidableEq"), Sp, Id("V"), CloseBracket, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Comma, Sp, Word("survivors"), Sp, Id("D"), Sp, Eq, Sp, OpenBrace, Id("v"), Sp, Colon, Sp, Id("V"), Sp, Mid, Sp, Id("v"), Sp, Seq(Neg, InMacro), Sp, Id("D"), CloseBrace))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("The carrier contains precisely the vertices outside the deletion finset."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("survivor-graph"), DeclarationHandle.Create(Prefix + "survivorGraph"),
                H("Survivor graph"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, OpenBracket, Word("DecidableEq"), Sp, Id("V"), CloseBracket, Sp, Open, Id("G"), Sp, Colon, Sp, Word("SimpleGraph"), Sp, Id("V"), Close, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Comma, Sp, Word("survivorGraph"), Sp, Id("G"), Sp, Id("D"), Sp, Eq, Sp, Id("G"), Dot, Word("induce"), Sp, Open, Word("survivors"), Sp, Id("D"), Close))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("The adjacency relation is induced by the original graph on the surviving carrier."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("host-adj-position"), DeclarationHandle.Create(Prefix + "host_adj_position"),
                H("Host adj position"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Open, Word("hub"), Sp, Colon, Sp, Word("Fin"), Sp, Id("b"), Sp, Rightarrow, Sp, Word("Fin"), Sp, Id("p"), Close, Sp, Open, Id("u"), Sp, Id("v"), Sp, Colon, Sp, Word("Vertex"), Sp, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Close, Comma),
                Seq(Open, Word("host"), Sp, Word("hub"), Close, Dot, Word("Adj"), Sp, Id("u"), Sp, Id("v"), Sp, Rightarrow),
                Seq(Word("position"), Sp, Word("hub"), Sp, Id("u"), Sp, Eq, Sp, Word("position"), Sp, Word("hub"), Sp, Id("v"), Sp, Lor),
                Seq(Word("position"), Sp, Word("hub"), Sp, Id("u"), Sp, Plus, Sp, D(1), Sp, Eq, Sp, Word("position"), Sp, Word("hub"), Sp, Id("v"), Sp, Lor),
                Seq(Word("position"), Sp, Word("hub"), Sp, Id("v"), Sp, Plus, Sp, D(1), Sp, Eq, Sp, Word("position"), Sp, Word("hub"), Sp, Id("u"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Every edge preserves the spine coordinate or changes it by one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("surviving-tail-vertex"), DeclarationHandle.Create(Prefix + "survivingTailVertex"),
                H("Surviving tail vertex"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Word("survivingTailVertex"), Sp, Colon, Sp, OpenBrace, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Rightarrow),
                Seq(Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Open, Word("Vertex"), Sp, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Close, Close, Sp, Rightarrow, Sp, Open, Id("i"), Sp, Colon, Sp, Word("Fin"), Sp, Id("t"), Close, Sp, Rightarrow, Sp, Word("tailVertex"), Sp, Id("i"), Sp, Seq(Neg, InMacro), Sp, Id("D"), Sp, Rightarrow, Sp, Word("coe"), Open, Word("survivors"), Sp, Id("D"), Close)
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Use the given survival proof to enter the induced graph carrier."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("tail-interval-reachable"), DeclarationHandle.Create(Prefix + "tail_interval_reachable"),
                H("Tail interval reachable"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Open, Word("hub"), Sp, Colon, Sp, Word("Fin"), Sp, Id("b"), Sp, Rightarrow, Sp, Word("Fin"), Sp, Id("p"), Close, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Open, Word("Vertex"), Sp, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Close, Close, Sp, OpenBrace, Id("x"), Sp, Id("y"), Sp, Colon, Sp, Word("Fin"), Sp, Id("t"), CloseBrace),
                Seq(Open, Word("hx"), Sp, Colon, Sp, Word("tailVertex"), Sp, Id("x"), Sp, Seq(Neg, InMacro), Sp, Id("D"), Close, Sp, Open, Word("hy"), Sp, Colon, Sp, Word("tailVertex"), Sp, Id("y"), Sp, Seq(Neg, InMacro), Sp, Id("D"), Close, Comma),
                Seq(Word("coe"), Id("x"), Sp, Leq, Sp, Word("coe"), Id("y"), Sp, Rightarrow),
                Seq(Open, Forall, Sp, Open, Id("z"), Sp, Colon, Sp, Word("Fin"), Sp, Id("t"), Close, Comma, Sp, Word("coe"), Id("x"), Sp, Leq, Sp, Word("coe"), Id("z"), Sp, Rightarrow, Sp, Word("coe"), Id("z"), Sp, Leq, Sp, Word("coe"), Id("y"), Sp, Rightarrow, Sp, Word("tailVertex"), Sp, Id("z"), Sp, Seq(Neg, InMacro), Sp, Id("D"), Close, Sp, Rightarrow),
                Seq(Open, Word("survivorGraph"), Sp, Open, Word("host"), Sp, Word("hub"), Close, Sp, Id("D"), Close, Dot, Word("Reachable"), Sp, Open, Word("survivingTailVertex"), Sp, Id("D"), Sp, Id("x"), Sp, Word("hx"), Close),
                Seq(Open, Word("survivingTailVertex"), Sp, Id("D"), Sp, Id("y"), Sp, Word("hy"), Close)
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Consecutive surviving tail positions form an induced path through the interval."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tail-component-eq-iff"), DeclarationHandle.Create(Prefix + "tail_component_eq_iff"),
                H("Tail component eq iff"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Open, Word("hub"), Sp, Colon, Sp, Word("Fin"), Sp, Id("b"), Sp, Rightarrow, Sp, Word("Fin"), Sp, Id("p"), Close, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Open, Word("Vertex"), Sp, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Close, Close, Sp, OpenBrace, Id("x"), Sp, Id("y"), Sp, Colon, Sp, Word("Fin"), Sp, Id("t"), CloseBrace),
                Seq(Open, Word("hx"), Sp, Colon, Sp, Word("tailVertex"), Sp, Id("x"), Sp, Seq(Neg, InMacro), Sp, Id("D"), Close, Sp, Open, Word("hy"), Sp, Colon, Sp, Word("tailVertex"), Sp, Id("y"), Sp, Seq(Neg, InMacro), Sp, Id("D"), Close, Comma),
                Seq(Word("coe"), Id("x"), Sp, Leq, Sp, Word("coe"), Id("y"), Sp, Rightarrow),
                Seq(Open, Open, Word("survivorGraph"), Sp, Open, Word("host"), Sp, Word("hub"), Close, Sp, Id("D"), Close, Dot, Word("connectedComponentMk")),
                Seq(Open, Word("survivingTailVertex"), Sp, Id("D"), Sp, Id("x"), Sp, Word("hx"), Close, Sp, Eq),
                Seq(Open, Word("survivorGraph"), Sp, Open, Word("host"), Sp, Word("hub"), Close, Sp, Id("D"), Close, Dot, Word("connectedComponentMk")),
                Seq(Open, Word("survivingTailVertex"), Sp, Id("D"), Sp, Id("y"), Sp, Word("hy"), Close, Sp, Iff),
                Seq(Forall, Sp, Open, Id("z"), Sp, Colon, Sp, Word("Fin"), Sp, Id("t"), Close, Comma, Sp, Word("coe"), Id("x"), Sp, Leq, Sp, Word("coe"), Id("z"), Sp, Rightarrow, Sp, Word("coe"), Id("z"), Sp, Leq, Sp, Word("coe"), Id("y"), Sp, Rightarrow, Sp, Word("tailVertex"), Sp, Id("z"), Sp, Seq(Neg, InMacro), Sp, Id("D"), Close)
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("A gap separates the two endpoints, and a fully surviving interval connects them."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tail-run-component"), DeclarationHandle.Create(Prefix + "component"),
                H("Tail run component"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Word("TailRun"), Dot, Word("component"), Sp, Colon, Sp, OpenBrace, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Rightarrow),
                Seq(Open, Word("hub"), Sp, Colon, Sp, Word("Fin"), Sp, Id("b"), Sp, Rightarrow, Sp, Word("Fin"), Sp, Id("p"), Close, Sp, Rightarrow),
                Seq(Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Open, Word("Vertex"), Sp, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Close, Close, Sp, Rightarrow),
                Seq(Word("TailRun"), Sp, Id("D"), Sp, Rightarrow, Sp, Open, Word("survivorGraph"), Sp, Open, Word("host"), Sp, Word("hub"), Close, Sp, Id("D"), Close, Dot, Word("ConnectedComponent"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Take the actual induced graph component of the first vertex in the run."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("tail-run-component-eq"), DeclarationHandle.Create(Prefix + "component_eq"),
                H("Tail run component eq"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Open, Word("hub"), Sp, Colon, Sp, Word("Fin"), Sp, Id("b"), Sp, Rightarrow, Sp, Word("Fin"), Sp, Id("p"), Close, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Open, Word("Vertex"), Sp, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Close, Close, Sp, Open, Id("r"), Sp, Colon, Sp, Word("TailRun"), Sp, Id("D"), Close, Sp, Open, Id("z"), Sp, Colon, Sp, Word("Fin"), Sp, Id("t"), Close),
                Seq(Open, Word("hl"), Sp, Colon, Sp, Word("coe"), Id("r"), Dot, Word("first"), Sp, Leq, Sp, Word("coe"), Id("z"), Close, Sp, Open, Word("hr"), Sp, Colon, Sp, Word("coe"), Id("z"), Sp, Leq, Sp, Word("coe"), Id("r"), Dot, Word("last"), Close, Comma),
                Seq(Word("TailRun"), Dot, Word("component"), Sp, Word("hub"), Sp, Id("D"), Sp, Id("r"), Sp, Eq),
                Seq(Open, Word("survivorGraph"), Sp, Open, Word("host"), Sp, Word("hub"), Close, Sp, Id("D"), Close, Dot, Word("connectedComponentMk"), Sp, Open, Word("survivingTailVertex"), Sp, Id("D"), Sp, Id("z"), Sp, Id("proof"), Close)
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Every tail vertex of the run lies in the component of its first vertex."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tail-run-component-injective"), DeclarationHandle.Create(Prefix + "tail_run_component_injective"),
                H("Tail run component injective"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Open, Word("hub"), Sp, Colon, Sp, Word("Fin"), Sp, Id("b"), Sp, Rightarrow, Sp, Word("Fin"), Sp, Id("p"), Close, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Open, Word("Vertex"), Sp, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Close, Close, Comma),
                Seq(Word("Function"), Dot, Word("Injective"), Sp, Open, Word("TailRun"), Dot, Word("component"), Sp, Word("hub"), Sp, Id("D"), Close)
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Between distinct positive surviving tail runs there is a deleted spine position which no projected survivor walk can cross."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-hub"), DeclarationHandle.Create(Prefix + "uniformHub"),
                H("Uniform hub"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Open, Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Sp, Open, Id("i"), Sp, Colon, Sp, Word("Fin"), Sp, Id("b"), Close, Comma, Sp, Word("coe"), Open, Word("uniformHub"), Sp, Id("b"), Sp, Id("i"), Close, Sp, Eq, Sp, D(2), Sp, Cdot, Sp, Word("coe"), Id("i"), Sp, Plus, Sp, D(1)))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Use the odd spine indices among the first 2b positions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("uniform-hubs-independent"), DeclarationHandle.Create(Prefix + "uniform_hubs_independent"),
                H("Uniform hubs independent"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, Open, Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Comma),
                Seq(Word("Function"), Dot, Word("Injective"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Sp, Land),
                Seq(Forall, Sp, Open, Id("i"), Sp, Id("j"), Sp, Colon, Sp, Word("Fin"), Sp, Id("b"), Close, Comma, Sp, Neg, Open, Word("SimpleGraph"), Dot, Word("pathGraph"), Sp, Open, D(2), Sp, Cdot, Sp, Id("b"), Close, Close, Dot, Word("Adj"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Sp, Id("i"), Close, Sp, Open, Word("uniformHub"), Sp, Id("b"), Sp, Id("j"), Close)
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Distinct odd positions are distinct vertices and cannot be consecutive."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-tail-length"), DeclarationHandle.Create(Prefix + "uniformTailLength"),
                H("Uniform tail length"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Open, Id("b"), Sp, Id("k"), Sp, Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Comma, Sp, Word("uniformTailLength"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Sp, Eq, Sp, Open, Id("b"), Sp, Plus, Sp, D(1), Close, Sp, Cdot, Sp, Id("q"), Sp, Plus, Sp, Id("b"), Sp, Minus, Sp, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Set the tail length so that b+1 parts of size q remain after deleting b vertices."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("uniform-vertex"), DeclarationHandle.Create(Prefix + "UniformVertex"),
                H("Uniform vertex"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Open, Id("b"), Sp, Id("k"), Sp, Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Comma, Sp, Word("UniformVertex"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Sp, Eq, Sp, Word("Vertex"), Sp, Open, D(2), Sp, Cdot, Sp, Id("b"), Close, Sp, Open, Word("uniformTailLength"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close, Sp, Id("b"), Sp, Id("k")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Use the tail length and the prefix of length 2b from the uniform host construction."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("uniform-host"), DeclarationHandle.Create(Prefix + "uniformHost"),
                H("Uniform host"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Open, Id("b"), Sp, Id("k"), Sp, Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Comma, Sp, Word("uniformHost"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Sp, Eq, Sp, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Place k leaves at every odd prefix position."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("uniform-survivor-card"), DeclarationHandle.Create(Prefix + "uniform_survivor_card"),
                H("Uniform survivor card"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("b"), Sp, Id("k"), Sp, Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Comma),
                Seq(D(2), Sp, Cdot, Sp, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Sp, Leq, Sp, Id("q"), Sp, Rightarrow, Sp, Forall, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Open, Word("UniformVertex"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close, Close, Comma, Sp, Id("D"), Dot, Word("card"), Sp, Eq, Sp, Id("b"), Sp, Rightarrow, Sp, Id("D"), Seq(Caret, Grp(Id("c"))), Dot, Word("card"), Sp, Eq, Sp, Open, Id("b"), Sp, Plus, Sp, D(1), Close, Sp, Cdot, Sp, Id("q"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Subtract b from the total number of spine and leaf vertices."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("inst-fintype-survivors"), DeclarationHandle.Create(Prefix + "instFintypeSurvivors"),
                H("Inst fintype survivors"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Word("instFintypeSurvivors"), Sp, Colon, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, Rightarrow, Sp, OpenBracket, Word("DecidableEq"), Sp, Id("V"), CloseBracket, Sp, Rightarrow, Sp, OpenBracket, Word("Fintype"), Sp, Id("V"), CloseBracket, Sp, Rightarrow, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Sp, Rightarrow),
                Seq(Word("Fintype"), Sp, Word("coe"), Open, Word("survivors"), Sp, Id("D"), Close)
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Enumerate the finite complement of the deletion."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("inst-decidable-survivor-adj"), DeclarationHandle.Create(Prefix + "instDecidableSurvivorAdj"),
                H("Inst decidable survivor adj"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Word("instDecidableSurvivorAdj"), Sp, Colon, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, Rightarrow),
                Seq(Grp(), OpenBracket, Word("DecidableEq"), Sp, Id("V"), CloseBracket, Sp, Rightarrow),
                Seq(Open, Id("G"), Sp, Colon, Sp, Word("SimpleGraph"), Sp, Id("V"), Close, Sp, Rightarrow, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Sp, Rightarrow, Sp, OpenBracket, Word("DecidableRel"), Sp, Id("G"), Dot, Word("Adj"), CloseBracket, Sp, Rightarrow, Sp, Word("DecidableRel"), Sp, Open, Word("survivorGraph"), Sp, Id("G"), Sp, Id("D"), Close, Dot, Word("Adj"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Restrict the original adjacency decision to the surviving carrier."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("component-sizes"), DeclarationHandle.Create(Prefix + "componentSizes"),
                H("Component sizes"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, OpenBracket, Word("DecidableEq"), Sp, Id("V"), CloseBracket, Sp, OpenBracket, Word("Fintype"), Sp, Id("V"), CloseBracket, Sp, Open, Id("G"), Sp, Colon, Sp, Word("SimpleGraph"), Sp, Id("V"), Close, Sp, OpenBracket, Word("DecidableRel"), Sp, Id("G"), Dot, Word("Adj"), CloseBracket, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Comma),
                Seq(Word("componentSizes"), Sp, Id("G"), Sp, Id("D"), Sp, Eq, Sp, Word("Finset"), Dot, Word("univ"), Dot, Word("val"), Dot, Word("map"), Sp, Open, LambdaLower, Sp, Id("C"), Sp, Colon, Sp, Open, Word("survivorGraph"), Sp, Id("G"), Sp, Id("D"), Close, Dot, Word("ConnectedComponent"), Sp, Mapsto),
                Seq(Id("C"), Dot, Word("supp"), Dot, Word("toFinset"), Dot, Word("card"), Close)
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Take the multiset of sizes of the actual connected components of the induced survivor graph. Repeated sizes are counted with multiplicity."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nc-damage"), DeclarationHandle.Create(Prefix + "ncDamage"),
                H("Nc damage"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, OpenBracket, Word("DecidableEq"), Sp, Id("V"), CloseBracket, Sp, OpenBracket, Word("Fintype"), Sp, Id("V"), CloseBracket, Sp, Open, Id("G"), Sp, Colon, Sp, Word("SimpleGraph"), Sp, Id("V"), Close, Sp, OpenBracket, Word("DecidableRel"), Sp, Id("G"), Dot, Word("Adj"), CloseBracket, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Comma),
                Seq(Word("ncDamage"), Sp, Id("G"), Sp, Id("D"), Sp, Eq, Sp, Open, Word("componentSizes"), Sp, Id("G"), Sp, Id("D"), Close, Dot, Word("card"), Sp, Minus, Sp, D(1))
            ]))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(DefinitionDsl.Text("Section 2 defines component-count damage as the increase in the number of components. For a connected host the original count is one, and the natural-number subtraction truncates at zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pc-damage"), DeclarationHandle.Create(Prefix + "pcDamage"),
                H("Pc damage"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, OpenBracket, Word("DecidableEq"), Sp, Id("V"), CloseBracket, Sp, OpenBracket, Word("Fintype"), Sp, Id("V"), CloseBracket, Sp, Open, Id("G"), Sp, Colon, Sp, Word("SimpleGraph"), Sp, Id("V"), Close, Sp, OpenBracket, Word("DecidableRel"), Sp, Id("G"), Dot, Word("Adj"), CloseBracket, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Comma),
                Seq(Word("pcDamage"), Sp, Id("G"), Sp, Id("D"), Sp, Eq, Sp, Open, Word("Fintype"), Dot, Word("card"), Sp, Id("V"), Close, Dot, Word("choose"), Sp, D(2), Sp, Minus, Sp, Open, Open, Word("componentSizes"), Sp, Id("G"), Sp, Id("D"), Close, Dot, Word("map"), Sp, Open, LambdaLower, Sp, Id("c"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Sp, Mapsto, Sp, Id("c"), Dot, Word("choose"), Sp, D(2), Close, Close, Dot, Word("sum"))
            ]))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(DefinitionDsl.Text("Section 2 counts all original pairs and subtracts the pairs within each surviving component. Deleted vertices are included in the damage."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lcc-damage"), DeclarationHandle.Create(Prefix + "lccDamage"),
                H("Lcc damage"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, OpenBracket, Word("DecidableEq"), Sp, Id("V"), CloseBracket, Sp, OpenBracket, Word("Fintype"), Sp, Id("V"), CloseBracket, Sp, Open, Id("G"), Sp, Colon, Sp, Word("SimpleGraph"), Sp, Id("V"), Close, Sp, OpenBracket, Word("DecidableRel"), Sp, Id("G"), Dot, Word("Adj"), CloseBracket, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Comma),
                Seq(Word("lccDamage"), Sp, Id("G"), Sp, Id("D"), Sp, Eq, Sp, Word("Fintype"), Dot, Word("card"), Sp, Id("V"), Sp, Minus, Sp, Open, Word("componentSizes"), Sp, Id("G"), Sp, Id("D"), Close, Dot, Word("sup"))
            ]))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(DefinitionDsl.Text("Section 2 subtracts the largest surviving component size from the original order."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("damage-maximum"), DeclarationHandle.Create(Prefix + "damageMaximum"),
                H("Damage maximum"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, OpenBracket, Word("Fintype"), Sp, Id("V"), CloseBracket, Sp, Open, Word("score"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Sp, Rightarrow, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Sp, Open, Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Comma, Sp, Word("damageMaximum"), Sp, Word("score"), Sp, Id("b"), Sp, Eq, Sp, Open, Open, Word("Finset"), Dot, Word("univ"), Sp, Colon),
                Seq(Word("Finset"), Sp, Id("V"), Close, Dot, Word("powersetCard"), Sp, Id("b"), Close, Dot, Word("sup"), Sp, Word("score"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("The supremum is taken over the finset of subsets with cardinality exactly the budget."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("inst-decidable-rel-vertex-adj-host"), DeclarationHandle.Create(Prefix + "instDecidableRelVertexAdjHost"),
                H("Inst decidable rel vertex adj host"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Word("instDecidableRelVertexAdjHost"), Sp, Colon, Sp, OpenBrace, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Rightarrow, Sp, Open, Word("hub"), Sp, Colon, Sp, Word("Fin"), Sp, Id("b"), Sp, Rightarrow, Sp, Word("Fin"), Sp, Id("p"), Close, Sp, Rightarrow, Sp, Word("DecidableRel")),
                Seq(Open, Word("host"), Sp, Word("hub"), Close, Dot, Word("Adj"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Decide spine adjacency or check whether the spine vertex is the specified hub."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("deleted-tail-indices"), DeclarationHandle.Create(Prefix + "deletedTailIndices"),
                H("Deleted tail indices"), StatementSource.FromAuthor(Disp(Seq(Word("deletedTailIndices"), Sp, Colon, Sp, OpenBrace, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Rightarrow, Sp, Word("Finset"), Sp, Open, Word("Vertex"), Sp, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Close, Sp, Rightarrow, Sp, Word("Finset"), Sp, Open, Word("Fin"), Sp, Id("t"), Close))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Filter the tail positions by whether their vertices are deleted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("surviving-tail-vertices"), DeclarationHandle.Create(Prefix + "survivingTailVertices"),
                H("Surviving tail vertices"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Word("survivingTailVertices"), Sp, Colon, Sp, OpenBrace, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Rightarrow, Sp, Open, Word("Fin"), Sp, Id("b"), Sp, Rightarrow, Sp, Word("Fin"), Sp, Id("p"), Close, Sp, Rightarrow, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Open, Word("Vertex"), Sp, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Close, Close),
                Seq(Rightarrow, Sp, Word("Finset"), Sp, Word("coe"), Open, Word("survivors"), Sp, Id("D"), Close)
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Select the survivors whose spine coordinates lie in the tail."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("positive-tail-components"), DeclarationHandle.Create(Prefix + "positiveTailComponents"),
                H("Positive tail components"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Word("positiveTailComponents"), Sp, Colon, Sp, OpenBrace, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Rightarrow),
                Seq(Open, Word("hub"), Sp, Colon, Sp, Word("Fin"), Sp, Id("b"), Sp, Rightarrow, Sp, Word("Fin"), Sp, Id("p"), Close, Sp, Rightarrow),
                Seq(Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Open, Word("Vertex"), Sp, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Close, Close, Sp, Rightarrow),
                Seq(Word("Finset"), Sp, Open, Word("survivorGraph"), Sp, Open, Word("host"), Sp, Word("hub"), Close, Sp, Id("D"), Close, Dot, Word("ConnectedComponent"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Take the image of the surviving tail vertices under the actual component map."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mem-deleted-tail-indices"), DeclarationHandle.Create(Prefix + "mem_deletedTailIndices"),
                H("Mem deleted tail indices"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Open, Word("Vertex"), Sp, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Close, Close, Sp, Open, Id("i"), Sp, Colon, Sp, Word("Fin"), Sp, Id("t"), Close, Comma),
                Seq(Id("i"), Sp, InMacro, Sp, Word("deletedTailIndices"), Sp, Id("D"), Sp, Iff, Sp, Word("tailVertex"), Sp, Id("i"), Sp, InMacro, Sp, Id("D"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Membership is exactly deletion of the associated tail vertex."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("surviving-tail-vertex-mem"), DeclarationHandle.Create(Prefix + "survivingTailVertex_mem"),
                H("Surviving tail vertex mem"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Open, Word("hub"), Sp, Colon, Sp, Word("Fin"), Sp, Id("b"), Sp, Rightarrow, Sp, Word("Fin"), Sp, Id("p"), Close, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Open, Word("Vertex"), Sp, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Close, Close, Sp, Open, Id("i"), Sp, Colon, Sp, Word("Fin"), Sp, Id("t"), Close),
                Seq(Open, Word("hi"), Sp, Colon, Sp, Word("tailVertex"), Sp, Id("i"), Sp, Seq(Neg, InMacro), Sp, Id("D"), Close, Comma, Sp, Word("survivingTailVertex"), Sp, Id("D"), Sp, Id("i"), Sp, Word("hi"), Sp, InMacro, Sp, Word("survivingTailVertices"), Sp, Word("hub"), Sp, Id("D"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Every surviving tail index gives a vertex in this finset."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exists-surviving-tail-vertex"), DeclarationHandle.Create(Prefix + "exists_survivingTailVertex"),
                H("Exists surviving tail vertex"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Open, Word("hub"), Sp, Colon, Sp, Word("Fin"), Sp, Id("b"), Sp, Rightarrow, Sp, Word("Fin"), Sp, Id("p"), Close, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Open, Word("Vertex"), Sp, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Close, Close, Sp, OpenBrace, Id("v"), Sp, Colon, Sp, Word("coe"), Open, Word("survivors"), Sp, Id("D"), Close, CloseBrace, Comma),
                Seq(Id("v"), Sp, InMacro, Sp, Word("survivingTailVertices"), Sp, Word("hub"), Sp, Id("D"), Sp, Rightarrow),
                Seq(Exists, Sp, Id("i"), Comma, Sp, Exists, Sp, Open, Word("hi"), Sp, Colon, Sp, Word("tailVertex"), Sp, Id("i"), Sp, Seq(Neg, InMacro), Sp, Id("D"), Close, Comma, Sp, Word("survivingTailVertex"), Sp, Id("D"), Sp, Id("i"), Sp, Word("hi"), Sp, Eq, Sp, Id("v"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Every vertex in this finset has a surviving tail index."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("surviving-tail-vertices-card"), DeclarationHandle.Create(Prefix + "survivingTailVertices_card"),
                H("Surviving tail vertices card"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Open, Word("hub"), Sp, Colon, Sp, Word("Fin"), Sp, Id("b"), Sp, Rightarrow, Sp, Word("Fin"), Sp, Id("p"), Close, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Open, Word("Vertex"), Sp, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Close, Close, Comma),
                Seq(Open, Word("survivingTailVertices"), Sp, Word("hub"), Sp, Id("D"), Close, Dot, Word("card"), Sp, Eq, Sp, Id("t"), Sp, Minus, Sp, Open, Word("deletedTailIndices"), Sp, Id("D"), Close, Dot, Word("card"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("The surviving tail indices are in bijection with the surviving tail vertices."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-tail-component-has-run"), DeclarationHandle.Create(Prefix + "positiveTailComponent_has_run"),
                H("Positive tail component has run"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Open, Word("hub"), Sp, Colon, Sp, Word("Fin"), Sp, Id("b"), Sp, Rightarrow, Sp, Word("Fin"), Sp, Id("p"), Close, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Open, Word("Vertex"), Sp, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Close, Close),
                Seq(OpenBrace, Id("C"), Sp, Colon, Sp, Open, Word("survivorGraph"), Sp, Open, Word("host"), Sp, Word("hub"), Close, Sp, Id("D"), Close, Dot, Word("ConnectedComponent"), CloseBrace, Comma),
                Seq(Id("C"), Sp, InMacro, Sp, Word("positiveTailComponents"), Sp, Word("hub"), Sp, Id("D"), Sp, Rightarrow, Sp, Exists, Sp, Id("r"), Comma, Sp, Word("TailRun"), Dot, Word("component"), Sp, Word("hub"), Sp, Id("D"), Sp, Id("r"), Sp, Eq, Sp, Id("C"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Take the maximal surviving interval through a tail vertex in the component."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tail-run-predecessor-or-first"), DeclarationHandle.Create(Prefix + "predecessorOrFirst"),
                H("Tail run predecessor or first"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Word("TailRun"), Dot, Word("predecessorOrFirst"), Sp, Colon, Sp, OpenBrace, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Rightarrow),
                Seq(Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Open, Word("Vertex"), Sp, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Close, Close, Sp, Rightarrow, Sp, Word("TailRun"), Sp, Id("D"), Sp, Rightarrow, Sp, Word("Option"), Sp, Word("Subtype"), Open, Word("deletedTailIndices"), Sp, Id("D"), Close)
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Use no predecessor for an initial run and otherwise record its deleted predecessor."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("tail-run-predecessor-or-first-injective"), DeclarationHandle.Create(Prefix + "predecessorOrFirst_injective"),
                H("Tail run predecessor or first injective"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Open, Word("Vertex"), Sp, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Close, Close, Comma, Sp, Word("Function"), Dot, Word("Injective")),
                Seq(Open, Word("TailRun"), Dot, Word("predecessorOrFirst"), Sp, Id("D"), Close)
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("The predecessor determines the first vertex, and maximality determines the last vertex."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-tail-component-count-and-mass"), DeclarationHandle.Create(Prefix + "uniform_tail_component_count_and_mass"),
                H("Uniform tail component count and mass"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("b"), Sp, Id("k"), Sp, Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Comma),
                Seq(D(2), Sp, Leq, Sp, Id("b"), Sp, Rightarrow),
                Seq(D(1), Sp, Leq, Sp, Id("k"), Sp, Rightarrow),
                Seq(D(2), Sp, Cdot, Sp, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Sp, Leq, Sp, Id("q"), Sp, Rightarrow),
                Seq(Forall, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Open, Word("UniformVertex"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close, Close, Comma),
                Seq(Id("D"), Dot, Word("card"), Sp, Eq, Sp, Id("b"), Sp, Rightarrow),
                Seq(Word("let"), Sp, Id("t"), Sp, Colon, Sp, Eq, Sp, Word("uniformTailLength"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Semi),
                Seq(Word("let"), Sp, Id("G"), Sp, Colon, Sp, Eq, Sp, Word("survivorGraph"), Sp, Open, Word("uniformHost"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close, Sp, Id("D"), Semi),
                Seq(Word("have"), Sp, Id("I"), Sp, Colon, Sp, Eq, Sp, OpenBrace, Id("i"), Sp, Mid, Sp, Word("tailVertex"), Sp, Id("i"), Sp, InMacro, Sp, Id("D"), CloseBrace, Semi),
                Seq(Word("have"), Sp, Id("A"), Sp, Colon, Sp, Eq, Sp, OpenBrace, Id("v"), Sp, Mid, Sp, D(2), Sp, Cdot, Sp, Id("b"), Sp, Leq, Sp, Word("position"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Sp, Word("coe"), Id("v"), CloseBrace, Semi),
                Seq(Word("have"), Sp, Id("J"), Sp, Colon, Sp, Eq, Sp, Word("Finset"), Dot, Word("image"), Sp, Id("G"), Dot, Word("connectedComponentMk"), Sp, Id("A"), Semi),
                Seq(Word("have"), Sp, Id("w"), Sp, Colon, Sp, Eq, Sp, LambdaLower, Sp, Id("C"), Sp, Mapsto, Sp, OpenBrace, Id("v"), Sp, InMacro, Sp, Id("A"), Sp, Mid, Sp, Id("G"), Dot, Word("connectedComponentMk"), Sp, Id("v"), Sp, Eq, Sp, Id("C"), CloseBrace, Dot, Word("card"), Semi),
                Seq(Id("J"), Dot, Word("card"), Sp, Leq, Sp, Id("I"), Dot, Word("card"), Sp, Plus, Sp, D(1), Sp, Land, Sp, Sum, Sp, Id("C"), Sp, InMacro, Sp, Id("J"), Comma, Sp, Id("w"), Sp, Id("C"), Sp, Eq, Sp, Id("t"), Sp, Minus, Sp, Id("I"), Dot, Word("card"), Sp, Land, Sp, Forall, Sp, Id("C"), Sp, InMacro, Sp, Id("J"), Comma, Sp, Id("w"), Sp, Id("C"), Sp, Leq, Sp, Id("C"), Dot, Word("supp"), Dot, Word("toFinset"), Dot, Word("card"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Charge the start of each positive tail run to its deleted predecessor or the initial position. Summing the tail mass counts each surviving tail vertex once."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sum-component-card"), DeclarationHandle.Create(Prefix + "sum_component_card"),
                H("Sum component card"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, OpenBracket, Word("DecidableEq"), Sp, Id("V"), CloseBracket, Sp, OpenBracket, Word("Fintype"), Sp, Id("V"), CloseBracket, Sp, Open, Id("G"), Sp, Colon, Sp, Word("SimpleGraph"), Sp, Id("V"), Close, Sp, OpenBracket, Word("DecidableRel"), Sp, Id("G"), Dot, Word("Adj"), CloseBracket, Comma),
                Seq(Sum, Sp, Id("C"), Comma, Sp, Id("C"), Dot, Word("supp"), Dot, Word("toFinset"), Dot, Word("card"), Sp, Eq, Sp, Word("Fintype"), Dot, Word("card"), Sp, Id("V"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Partition the carrier by its actual component and sum the corresponding fiber sizes."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("twice-choose-two-add"), DeclarationHandle.Create(Prefix + "twice_choose_two_add"),
                H("Twice choose two add"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Open, Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Comma, Sp, D(2), Sp, Cdot, Sp, Id("n"), Dot, Word("choose"), Sp, D(2), Sp, Plus, Sp, Id("n"), Sp, Eq, Sp, Id("n"), Sp, Caret, D(2)))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Rewrite the binomial coefficient with its explicit formula and simplify."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-fewer-tail-components-strict-score-comparisons"), DeclarationHandle.Create(Prefix + "uniform_fewer_tail_components_strict_score_comparisons"),
                H("Uniform fewer tail components strict score comparisons"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("b"), Sp, Id("k"), Sp, Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Comma),
                Seq(D(2), Sp, Leq, Sp, Id("b"), Sp, Rightarrow),
                Seq(D(1), Sp, Leq, Sp, Id("k"), Sp, Rightarrow),
                Seq(D(2), Sp, Cdot, Sp, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Sp, Leq, Sp, Id("q"), Sp, Rightarrow),
                Seq(Forall, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Open, Word("UniformVertex"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close, Close, Comma),
                Seq(Id("D"), Dot, Word("card"), Sp, Eq, Sp, Id("b"), Sp, Rightarrow),
                Seq(Open, Word("positiveTailComponents"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Sp, Id("D"), Close, Dot, Word("card"), Sp, Leq, Sp, Id("b"), Sp, Rightarrow),
                Seq(Word("let"), Sp, Id("G"), Sp, Colon, Sp, Eq, Sp, Word("survivorGraph"), Sp, Open, Word("uniformHost"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close, Sp, Id("D"), Semi),
                Seq(Word("have"), Sp, Id("n"), Sp, Colon, Sp, Eq, Sp, Word("Fintype"), Dot, Word("card"), Sp, Open, Word("UniformVertex"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close, Semi),
                Seq(Open, Id("b"), Sp, Plus, Sp, D(1), Close, Sp, Cdot, Sp, Id("q"), Dot, Word("choose"), Sp, D(2), Sp, FormulaDsl.Lt, Sp, Sum, Sp, Id("C"), Comma, Sp, Id("C"), Dot, Word("supp"), Dot, Word("toFinset"), Dot, Word("card"), Dot, Word("choose"), Sp, D(2), Sp, Land),
                Seq(Word("pcDamage"), Sp, Open, Word("uniformHost"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close, Sp, Id("D"), Sp, FormulaDsl.Lt, Sp, Id("n"), Dot, Word("choose"), Sp, D(2), Sp, Minus, Sp, Open, Id("b"), Sp, Plus, Sp, D(1), Close, Sp, Cdot, Sp, Id("q"), Dot, Word("choose"), Sp, D(2), Sp, Land),
                Seq(Word("lccDamage"), Sp, Open, Word("uniformHost"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close, Sp, Id("D"), Sp, FormulaDsl.Lt, Sp, Id("n"), Sp, Minus, Sp, Id("q"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("When the tail mass lies in at most b components, its total and the sum-of-squares bound force a larger maximum part and more within-component pairs than the balanced profile."))), DescribeRole.Theorem)),
        []));

    private static Formula Id(string name) => FormulaDsl.Id(name);

    private static Formula Word(string name) =>
        new Formula.NamedConstant(FormulaIdentifier.Create(name));
}
