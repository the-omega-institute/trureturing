using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class FiniteMatchingCompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Topology/FiniteMatchingComposition.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual finite first-return pairing is exactly the outer partner relation of a glued matching network.",
        H("First-return matching composition"),
        Blocks(
            Paragraph(Text("For finite X and involutive permutations s,r, let E=Fix(r) and P=endpointPairing(s,r). P uses the least positive return to E under s*r. The first-return construction and its involutivity come from FiniteEndpointPairing. InvolutionOrbitSplit supplies alternating connectivity as the union of two product orbits. Component(r) means the quotient by EqvGen(r); q(r,x) denotes the quotient class. Type parameters may occupy independent universes.")),
            Describe.Lean(DescribeId.Create("first-return-components"), Handle("endpoint_component_iff"),
                H("Completeness of the actual endpoint pairing"), StatementSource.FromAuthor(Disp(
                    All("X", Id("FiniteType"), All("s", Call("Perm", Id("X")), All("r", Call("Perm", Id("X")),
                    Imp(And(Call("Involutive", Id("s")), Call("Involutive", Id("r"))),
                    All("x", Call("Fix", Id("r")), All("y", Call("Fix", Id("r")),
                        Iff(Equal(Call("q", Call("twoStep", Id("s"), Id("r")), Call("val", Id("x"))),
                                  Call("q", Call("twoStep", Id("s"), Id("r")), Call("val", Id("y")))),
                            Or(Equal(Id("y"), Id("x")), Equal(Id("y"), Call("P", Id("s"), Id("r"), Id("x"))))))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("At an r-fixed endpoint, s(x)=(s*r)(x), so the two candidate product orbits coincide. Reattachment with the identity identifies that orbit with the orbit of the actual first-return involution. Such an involution has only x and P(x) in the orbit. The theorem allows fixed points of s; freeness is required later to obtain distinct partners."))), DescribeRole.Theorem),
            Paragraph(Text("For N natural, Boundary(N)=Bool times Fin N. Piece(N) is one tagged copy of each input boundary. PiecesMate applies d on the first copy and e on the second. SeamMate exchanges the bottom of d with the top of e and fixes the exposed top and bottom. ExposedEquiv identifies those fixed points with Boundary(N). Composite(d,e) transports the actual endpoint pairing through this equivalence. Since both input matchings are free, Composite is a free involution as well. N=0 and N=1 are included.")),
            Describe.Lean(DescribeId.Create("three-level-partners"), Handle("triple_component_iff"),
                H("The first-return output is the genuine glued partner"), StatementSource.FromAuthor(Disp(
                    Diagrams(All("a", Boundary, All("b", Boundary,
                        Iff(Equal(Call("q", Call("gluingStep", Id("d"), Id("e")), Call("outer", Id("a"))),
                                  Call("q", Call("gluingStep", Id("d"), Id("e")), Call("outer", Id("b")))),
                            Or(Equal(Id("b"), Id("a")), Equal(Id("b"), Call("mate", Call("composite", Id("d"), Id("e")), Id("a")))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The explicit map collapse suppresses the seam wires onto the three-level graph. Retain chooses the upper copy of each seam vertex. Matching edges map to actual gluing edges; the only nontrivial fiber path is a seam edge. These maps induce halfToTripleEquiv and carry the actual exposed vertices to outer(a). Transporting the endpoint characterization proves the displayed equivalence."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("internal-loop-transport"), Handle("internalLoopCount_eq"),
                H("The same contraction preserves internal loops"), StatementSource.FromAuthor(Disp(
                    Diagrams(Equal(Call("internalLoopCount", Id("d"), Id("e")),
                        Call("card", Call("InternalComponent", Id("d"), Id("e"))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("InternalLoopCount counts half-edge components with no exposed endpoint. HalfToTripleEquiv preserves each boundary class, hence restricts to an equivalence with InternalComponent in the literal three-level graph. This transports the actual component subtype, rather than postulating a circle-count identity."))), DescribeRole.Theorem),
            Paragraph(Text("The construction is classical finite matching calculus, with the existing first-return and orbit theorems reused directly. Four-layer associativity and the corresponding internal-loop inventory require further component-separation proofs. They are not assertions of this module.")))));

    private static Formula Boundary => Call("Boundary", Id("N"));
    private static Formula Diagrams(Formula body) => All("N", Id("Nat"), All("d", Call("Matching", Boundary), All("e", Call("Matching", Boundary), body)));
    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create(Prefix + name);
    private static Formula Id(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
