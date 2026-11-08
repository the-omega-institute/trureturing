using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.VertexModels;

internal sealed class PonciniRasmussenNineEdgesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reindexing the generator edges", H("Reindexing the generator edges"), Blocks(
            Paragraph(Text("Incoming and outgoing lists contain pairs (target,source), with source embedded in Fin(8192). Multiplicities remain present. Kernel reduction checks equality of their sorted lists; mergeSort permutation transfers the exact finite sum. The calculation applies to every additive commutative group.")),
            Describe.Lean(DescribeId.Create("incoming"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.incoming"),
                H("incoming"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num(8192)), Equal(Call("incoming", Id("i")), Call("get", Id("rows"), Call("val", Id("i"))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The fixed binary tree contains the same incoming source lists used by sparseHamiltonian."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sparsehamiltonian-eq"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.sparseHamiltonian_eq"),
                H("sparseHamiltonian_eq"), StatementSource.FromAuthor(Disp(All("v", Call("Function", Call("Fin", Num(8192)), Id("Int")), All("i", Call("Fin", Num(8192)), Equal(Call("sparseHamiltonian", Id("v"), Id("i")), Call("Negate", Call("FoldLeft", Call("incoming", Id("i")), Call("AddIncomingCoefficient", Id("v"), Num(8192)), Num(0)))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("AddIncomingCoefficient(s,j) is s+v(j modulo 8192)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("incomingedges"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.incomingEdges"),
                H("incomingEdges"), StatementSource.FromAuthor(Disp(Equal(Id("incomingEdges"), Call("FlatMap", Call("finRange", Num(4862)), Call("IncomingTargetSourcePairs", Id("incoming"), Num(8192)))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For target t, map every source s in incoming(t) to (t,s modulo 8192)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("outgoingedges"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.outgoingEdges"),
                H("outgoingEdges"), StatementSource.FromAuthor(Disp(Equal(Id("outgoingEdges"), Call("FlatMap", Call("finRange", Num(4862)), Call("FilterMap", Call("finRange", Num(8)), Id("NonzeroTransitionTargetSource")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For each source s and generator g, include (transition(g,s),s) precisely when the transition is below 4862."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("edges-perm"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.edges_perm"),
                H("edges_perm"), StatementSource.FromAuthor(Disp(Call("Perm", Id("incomingEdges"), Id("outgoingEdges")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The edge multiset is preserved exactly."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sparse-sum"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.sparse_sum"),
                H("sparse_sum"), StatementSource.FromAuthor(Disp(All("A", Id("AddCommGroup"), All("b", Call("Function", Call("Fin", Num(4862)), Id("A")), All("v", Call("Function", Call("Fin", Num(8192)), Id("Int")), Equal(Call("Sum", Id("t"), Call("Fin", Num(4862)), Call("IntegerSMul", Call("sparseHamiltonian", Id("v"), Call("CastFin", Id("t"), Num(8192))), Call("b", Id("t")))), Call("Negate", Call("Sum", Id("s"), Call("Fin", Num(4862)), Call("Sum", Id("g"), Call("Fin", Num(8)), Call("IfLess", Call("val", Call("transition", Id("g"), Id("s"))), Num(4862), Call("IntegerSMul", Call("v", Call("CastFin", Id("s"), Num(8192))), Call("b", Call("transition", Id("g"), Id("s")))), Num(0))))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Integer scalar multiplication distributes over the finite incoming rows. The edge permutation gives the equality in any additive commutative group."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
}
