using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SymmetricExtensions;

internal sealed class BoseComponentProjectorDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseComponentProjector.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tensor factorization of the graph component Bose projector in the original tensor basis.",
        H("Component Bose projectors"),
        Blocks(
            Paragraph(Text("The register type I and local alphabet L are finite. G is any simple graph "
                + "on I. All matrices below use computational tensor words I to L. The construction "
                + "keeps every connected component, including isolated vertices.")),
            Describe.Lean(DescribeId.Create("bose-component-tensor-projector"),
                DeclarationHandle.Create(Prefix + "tensorProjector"),
                H("The tensor product over connected components"),
                StatementSource.FromAuthor(Disp(F.Seq(
                    Call("tensorProjector", F.Id("G"), F.Id("x"), F.Id("y")), Eq,
                    Call("ProductOverComponents", F.Id("G"), F.Id("P"), F.Id("x"), F.Id("y"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each connected component C, restrict x and y to its vertex "
                    + "set and evaluate the existing symmetric projector P on those restricted words. "
                    + "The matrix entry is the product of these entries over all C. This is the tensor "
                    + "product transported back to the original register basis. No reordering or "
                    + "normalization factor is inserted. A singleton component contributes the identity "
                    + "on its local register; the empty product is one."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bose-component-factorization"),
                DeclarationHandle.Create(Prefix + "factorization"),
                H("The component average equals the tensor product"),
                StatementSource.FromAuthor(Disp(F.Seq(
                    Call("componentProjector", F.Id("G")), Eq,
                    Call("tensorProjector", F.Id("G"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite graph, the actual component-preserving "
                    + "permutation average is exactly this tensor-product matrix. The proof constructs "
                    + "the equivalence between component-preserving permutations and independent "
                    + "permutations of each component, factors the permutation-matrix entries, and "
                    + "reindexes the finite average. The cardinality factor is the product of the "
                    + "component permutation cardinalities. The theorem assumes neither connectedness "
                    + "nor a nonempty vertex set."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bosecomponentprojector-disconnected-counterexample"),
                DeclarationHandle.Create(Prefix + "disconnected_counterexample"),
                H("Disconnected components admit a rank-one boundary"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The statement fixes the word w by assigning one basis label on the component of a and a distinct label elsewhere, and asserts positivity, all edge support constraints and failure of full support for the actual projector |w><w|. The sole edge on registers 0 and 1 with labels 0,0,1 specializes to the original three-qubit boundary. The proof uses exact tensor entries and projector identities."))),
                DescribeRole.Theorem))));
}
