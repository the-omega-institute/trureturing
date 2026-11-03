using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class FiniteMatchingClosureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Topology/FiniteMatchingClosure.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit contraction of matching networks preserves their actual connected components.",
        H("Finite matching networks and series contraction"),
        Blocks(
            Paragraph(Text("A matching on V is a fixed-point-free involution mate:V to V. Component(r) is the quotient by the reflexive, symmetric and transitive closure of the edge relation r. Parallel edges with different colors remain allowed. Coloring(r,C) consists of functions V to C constant along each r-edge. Types and relations retain their independent universes; FiniteType means an arbitrary finite type, including the empty type.")),
            Describe.Lean(DescribeId.Create("series-contraction"), Handle("contractionEquiv"),
                H("Series contraction by actual paths"), StatementSource.FromAuthor(Disp(
                    All("V", Id("Type"), All("W", Id("Type"),
                    All("r", Call("Relation", Id("V")), All("s", Call("Relation", Id("W")),
                    All("f", Call("Maps", Id("V"), Id("W")), All("g", Call("Maps", Id("W"), Id("V")),
                    Imp(And(All("y", Id("W"), Equal(Call("f", Call("g", Id("y"))), Id("y"))),
                        And(All("x", Id("V"), All("y", Id("V"), Imp(Call("r", Id("x"), Id("y")),
                            Call("EqvGen", Id("s"), Call("f", Id("x")), Call("f", Id("y")))))),
                        And(All("x", Id("W"), All("y", Id("W"), Imp(Call("s", Id("x"), Id("y")),
                            Call("EqvGen", Id("r"), Call("g", Id("x")), Call("g", Id("y")))))),
                            All("x", Id("V"), Call("EqvGen", Id("r"), Id("x"), Call("g", Call("f", Id("x")))))))),
                        Call("Equiv", Call("Component", Id("r")), Call("Component", Id("s")))))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The map f retracts onto g: f(g(y))=y. Each source edge maps to a target path, each target edge lifts to a source path, and every source vertex is connected to g(f(x)). The induced quotient maps are inverse. No component count or matching identity is assumed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("overlay-components"), Handle("overlay_component_card"),
                H("Suppressing the overlay wires"), StatementSource.FromAuthor(Disp(
                    All("V", Id("Type"), All("s", Call("Maps", Id("V"), Id("V")),
                    All("t", Call("Maps", Id("V"), Id("V")),
                        Equal(Call("card", Call("Component", Call("overlayStep", Id("s"), Id("t")))),
                            Call("card", Call("Component", Call("twoStep", Id("s"), Id("t")))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("OverlayStep has two copies of V, the s-edges in the first copy, the t-edges in the second, and wires joining equal labels across copies. TwoStep has y=s(x) or y=t(x). The contraction uses Sum.elim(id,id) and the first inclusion, so the component equivalence holds even without finiteness or involutivity. Here card is Nat.card; no finite-cardinality interpretation is asserted for an infinite component type."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("component-colors"), Handle("coloring_card"),
                H("One independent color per component"), StatementSource.FromAuthor(Disp(
                    All("V", Id("FiniteType"), All("C", Id("Type"), All("r", Call("Relation", Id("V")),
                        Equal(Call("card", Call("Coloring", Id("r"), Id("C"))),
                            Call("power", Call("card", Id("C")), Call("card", Call("Component", Id("r")))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Quotient lifting identifies edge-constant functions with arbitrary functions on Component(r). Finite V makes its component quotient finite; C remains arbitrary. The equation uses Nat.card, including its infinite-type convention."))), DescribeRole.Theorem),
            Paragraph(Text("Boundary(N) is Bool times Fin N, with false the top and true the bottom. The identity matching reverses Bool. For j+1<N, cupcapMatching pairs positions j and j+1 separately on each boundary and reverses Bool at every other position. Its involutivity and absence of fixed points hold for every valid index. GluingVertex(N) has three levels; upper and lower embed the two matching boundaries, and outer selects levels zero and two. InternalComponent consists exactly of quotient components meeting no outer vertex. These are all pairings, without a planarity or faithfulness assertion.")))));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create(Prefix + name);
    private static Formula Id(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
