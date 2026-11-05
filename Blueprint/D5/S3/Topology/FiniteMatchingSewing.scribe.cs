using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class FiniteMatchingSewingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Topology/FiniteMatchingSewing.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual component labels partition sewn matching networks into untouched components and the sewn boundary quotient.",
        H("Sewing inventories and cyclic closure"),
        Blocks(
            Paragraph(Text("Let r be any edge relation on X, a:B to X a boundary map, d a matching on B and t:B to B arbitrary. EndpointCharacterization(r,a,d) abbreviates the exact assertion: for all b,c in B, q(r,a(b))=q(r,a(c)) if and only if c=b or c=mate(d,b). No finiteness is required. SewStep(r,a,t) adds all edges from a(b) to a(t(b)). Unmarked(r,a) is the subtype of components of r containing no a(b). TwoStep(f,g) has edges y=f(x) or y=g(x). Component is the actual equivalence-closure quotient, and Equiv denotes a constructed bijection.")),
            Describe.Lean(DescribeId.Create("sewing-inventory"), Handle("sewingInventory"),
                H("A component inventory constructed by labels"), StatementSource.FromAuthor(Disp(SewingParameters(
                    Imp(Call("EndpointCharacterization", Id("r"), Id("a"), Id("d")),
                        Call("Equiv", Call("Component", Call("sewStep", Id("r"), Id("a"), Id("t"))),
                            Call("Sum", Call("Unmarked", Id("r"), Id("a")),
                                Call("Component", Call("twoStep", Call("mate", Id("d")), Id("t"))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("An old component with no boundary point retains its own label. For a component meeting the boundary, choose one boundary representative and use its class in the twoStep quotient. The partner characterization makes the choice independent of the representative. Added sewing edges preserve that label. Conversely, untouched components embed into the sewn network and boundary classes map through a. These maps are inverse on the actual quotients."))), DescribeRole.Definition),
            Paragraph(Text("For the following formulas N is any natural number, Boundary(N)=Bool times Fin N and d,e are arbitrary matchings of that boundary. InternalLoopCount counts internal components of the first-return gluing. ClosedComponent(d) is Component(twoStep(mate(d),mate(identityMatching(N)))); closedCount(d) is its Nat.card. ClosedStackStep(d,e) is the actual disjoint two-matching network with both seam and closure wires. Sum means disjoint union and add is natural-number addition.")),
            Describe.Lean(DescribeId.Create("closed-stack-inventory"), Handle("closedStackInventory"),
                H("Close before or after actual matching composition"), StatementSource.FromAuthor(Disp(Diagrams(
                    Call("Equiv", Call("Component", Call("closedStackStep", Id("d"), Id("e"))),
                        Call("Sum", Call("halfEdgeInternalComponent", Id("d"), Id("e")),
                            Call("ClosedComponent", Call("composite", Id("d"), Id("e")))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Closing the exposed boundary is sewing with the identity matching. The actual first-return component theorem discharges EndpointCharacterization; it is not an extra hypothesis of this result. A direct equivalence identifies the sewn graph with the literal closed stack. Thus every closed component is either an internal gluing component or a component of the closed composite."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cyclic-closure-count"), Handle("closed_weight_cyclic"),
                H("Cyclic closure preserves the complete circle exponent"), StatementSource.FromAuthor(Disp(Diagrams(
                    Equal(Weight(Id("d"), Id("e")), Weight(Id("e"), Id("d")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Weight(d,e) abbreviates internalLoopCount(d,e)+closedCount(composite(d,e)). The inventory identifies this sum with the number of components of the actual closed stack. Exchanging the two tagged layers preserves every matching edge and closure wire. The resulting quotient equivalence proves Weight(d,e)=Weight(e,d). This is a count identity for all pairings; no planarity, coefficient ring, invertible circle value or supplied trace identity is involved."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("identity-closure"), Handle("closedCount_identity"),
                H("The identity has exactly N closure circles"), StatementSource.FromAuthor(Disp(
                    All("N", Id("Nat"), Equal(Call("closedCount", Call("identityMatching", Id("N"))), Id("N"))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The index projection identifies each closed identity component with its Fin N label. In particular N=0 contributes zero circles, without an extra empty-diagram circle. Every matching on Boundary(0) equals identityMatching(0) by extensionality on the empty boundary, so the same count applies to every empty matching."))), DescribeRole.Theorem),
            Paragraph(Text("Straight matchings are also proved to be left and right units for the actual composite, with zero internal loops. The unit contractions retain every outer boundary vertex. This is the classical Brauer pairing and circle-removal construction. Associative multiplication on the free module, the tower inclusion, the local Temperley--Lieb relations and Jones identification are separate assertions.")))));

    private static Formula Weight(Formula d, Formula e) => Call("add", Call("internalLoopCount", d, e), Call("closedCount", Call("composite", d, e)));
    private static Formula Boundary => Call("Boundary", Id("N"));
    private static Formula Diagrams(Formula body) => All("N", Id("Nat"), All("d", Call("Matching", Boundary), All("e", Call("Matching", Boundary), body)));
    private static Formula SewingParameters(Formula body) => All("X", Id("Type"), All("B", Id("Type"), All("r", Call("Relation", Id("X")), All("a", Call("Maps", Id("B"), Id("X")), All("d", Call("Matching", Id("B")), All("t", Call("Maps", Id("B"), Id("B")), body))))));
    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create(Prefix + name);
    private static Formula Id(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
