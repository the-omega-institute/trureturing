using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class DeformedJucysMurphyComponentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete native components supply the live rotation coordinates used in the cut counts.",
        H("Complete Components and Rotation Coordinates"),
        Blocks(
            Describe.Lean(DescribeId.Create("rotation-component-cardinality"),
                DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyComponents.rotation_card"),
                H("A Rotation Orbit Has the Component's Identity-Edge Count"),
                StatementSource.FromAuthor(Disp(All("k", V("Nat"), All("p", Call("P", V("k")),
                    All("x", Call("Fin", Call("Twice", V("k"))),
                        Equal(Call("OrbitCard", V("p"), V("x")),
                            Call("ComponentEdgeCard", V("p"), V("x")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Rotation is matchingPerm(p)*matchingPerm(e(k)). OrbitCard "
                    + "counts the full SameCycle orbit of x. ComponentEdgeCard counts the literal "
                    + "identity edges in x's component. The orbit-to-edge bijection is used by the "
                    + "actual rotation cut proof; doubled edges and singleton orbits remain in scope."))),
                DescribeRole.Theorem),
            Paragraph(Text("The full product-rotation orbit-size multiset is two copies of the complete "
                + "coset-type multiset, including parts of size one. This is a reused consequence of "
                + "the frozen InvolutionOrbitSplit.component_split and component_orbit_classes: "
                + "each component consists of two nonempty disjoint rotation orbits, exchanged by "
                + "the identity matching, and each orbit contains exactly one endpoint of every "
                + "identity edge. Thus a component with r edges contributes two orbits of size r; "
                + "a doubled edge contributes two fixed points. This source correspondence is "
                + "recorded without a separate new multiset theorem.")))));
    private static Formula V(string s) => F.Id(s);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
}
