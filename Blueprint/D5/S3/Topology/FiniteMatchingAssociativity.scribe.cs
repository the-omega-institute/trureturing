using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class FiniteMatchingAssociativityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Associative matching sewing", H("Associative matching sewing"), Blocks(
            Paragraph(Text("Boundary(n) is Bool times Fin(n). Composite follows paths in the glued middle boundary. InternalLoopCount counts connected components avoiding every exposed endpoint. No planarity assumption is used. A closed triple network is partitioned into the components removed in the first sewing and those removed in the second sewing; rotating its three matching layers preserves the closed inventory.")),
            Describe.Lean(DescribeId.Create("composite-assoc"), DeclarationHandle.Create("D5/S3/Topology/FiniteMatchingAssociativity.composite_assoc"),
                H("composite_assoc"), StatementSource.FromAuthor(Disp(All("n", Id("Nat"), All("d", Call("Matching", Call("Boundary", Id("n"))), All("e", Call("Matching", Call("Boundary", Id("n"))), All("f", Call("Matching", Call("Boundary", Id("n"))), Equal(Call("composite", Call("composite", Id("d"), Id("e")), Id("f")), Call("composite", Id("d"), Call("composite", Id("e"), Id("f")))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Both bracketings induce the same equivalence relation on the exterior boundary through partitionProduct associativity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("internalloopcount-cocycle"), DeclarationHandle.Create("D5/S3/Topology/FiniteMatchingAssociativity.internalLoopCount_cocycle"),
                H("internalLoopCount_cocycle"), StatementSource.FromAuthor(Disp(All("n", Id("Nat"), All("d", Call("Matching", Call("Boundary", Id("n"))), All("e", Call("Matching", Call("Boundary", Id("n"))), All("f", Call("Matching", Call("Boundary", Id("n"))), Equal(Call("Add", Call("internalLoopCount", Id("d"), Id("e")), Call("internalLoopCount", Call("composite", Id("d"), Id("e")), Id("f"))), Call("Add", Call("internalLoopCount", Id("e"), Id("f")), Call("internalLoopCount", Id("d"), Call("composite", Id("e"), Id("f"))))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The two sums count the same closed components of the triple gluing. The disjoint component equivalences retain internal components from both stages."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("internalloopcount-pos-assoc"), DeclarationHandle.Create("D5/S3/Topology/FiniteMatchingAssociativity.internalLoopCount_pos_assoc"),
                H("internalLoopCount_pos_assoc"), StatementSource.FromAuthor(Disp(All("n", Id("Nat"), All("d", Call("Matching", Call("Boundary", Id("n"))), All("e", Call("Matching", Call("Boundary", Id("n"))), All("f", Call("Matching", Call("Boundary", Id("n"))), Iff(Or(Call("Positive", Call("internalLoopCount", Id("d"), Id("e"))), Call("Positive", Call("internalLoopCount", Call("composite", Id("d"), Id("e")), Id("f")))), Or(Call("Positive", Call("internalLoopCount", Id("e"), Id("f"))), Call("Positive", Call("internalLoopCount", Id("d"), Call("composite", Id("e"), Id("f")))))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The integer component identity implies equivalence of the two loop flags."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
}
