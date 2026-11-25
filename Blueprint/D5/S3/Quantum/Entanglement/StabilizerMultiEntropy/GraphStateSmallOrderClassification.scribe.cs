using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy;

internal sealed class GraphStateSmallOrderClassificationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateSmallOrderClassification.";
    private static readonly LibraryNoteRef Gce =
        LibraryNoteRef.Create("D5/L/QuantumStates/liu2025generalized");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rank-one pair classes separate connected graph states with low-order hit laws from those with a finite forbidden interval.",
        H("Which connected graph states admit arbitrarily low real GCE orders?"),
        Blocks(Describe.Lean(DescribeId.Create("physical-gap-readout"),
            DeclarationHandle.Create(Owner + "physical_gap_readout"),
            H("A finite parity inequality detects an actual negative Walsh mass"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(Gce),
            Blocks(
                Paragraph(Text("Take a finite connected simple graph with no isolated vertices. If it is neither a star nor a clique, cutting a proper rank-one pair class C leaves cut rank one, whereas every pair meeting both sides has cut rank two. The actual trace moments therefore force singleton hit probability p and independent cross-class hit pairs.")),
                Paragraph(Text("The whole hit set has even parity. If its intersection with C is odd, there is at least one crossing pair. A nonnegative law would require p at most m times the square of p, with m the product of the two side sizes. Below that threshold a straddling even coefficient of the actual physical Walsh transform is strictly negative.")),
                Paragraph(Text("Stars and cliques satisfy the exact converse at all real orders. Their law is a mixture of the empty-set atom and the uniform even law. The same finite parity comparison certifies a negative rate for every other connected graph, which is equivalent to failure of conditional negative definiteness. Disconnected component transport and infinite divisibility under XOR are not claimed in this formal module."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var p = F.Id("p");
        var m = F.Id("m");
        return Disp(new Formula.Relation(p, FormulaRelationOperator.LessThanOrEqual, Seq(m, p, p)));
    }
}
