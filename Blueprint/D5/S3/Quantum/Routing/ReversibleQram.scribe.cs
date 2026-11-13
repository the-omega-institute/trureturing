using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Routing;

internal sealed class ReversibleQramDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Routing/ReversibleQram.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/arunachalam2015robustness");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A reversible Boolean routing network selects one memory leaf, restores its workspace, "
            + "and acts coherently on arbitrary complex amplitudes.",
        H("Reversible QRAM routing and coherent readout"),
        Blocks(
            Paragraph(Text(
                "Addresses are binary words of any natural length n. Address 0 has one empty word; "
                    + "Address (n + 1) is Bool times Address n. Wires 0 is one Boolean wire, and "
                    + "Wires (n + 1) consists of two Wires n registers. The leftmost wire is the root "
                    + "input. The state clean n e puts e at that root and false at every scratch wire. "
                    + "The layout reuses each parent enable as its left output. Intermediate enables "
                    + "are therefore stored in place rather than retained in additional node registers.")),
            Describe.Lean(DescribeId.Create("qram-local-split"),
                DeclarationHandle.Create(Module + "split"), H("One routing split"),
                StatementSource.FromLean(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For address bit b, first XOR b AND the left root into the right root. "
                        + "Then XOR the resulting right root into the left root. These are the "
                        + "Toffoli and CNOT operations of Section IV. Starting with root values "
                        + "(e,false), their outputs are (e AND NOT b,e AND b). Other wires are "
                        + "untouched by this split. With e true at the first level, the Toffoli "
                        + "reduces to the address-copy CNOT described there. Both gates are "
                        + "permutations on arbitrary dirty wire configurations."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qram-routing"),
                DeclarationHandle.Create(Module + "route"), H("The recursive gate network"),
                StatementSource.FromLean(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "At depth zero route is the identity. At depth n + 1 it applies split "
                        + "with the first address bit, then routes both subregisters using the "
                        + "remaining address. Thus the network is defined by local gates; its "
                        + "definition does not use the one-hot specification. The separate function "
                        + "oneHot places e at the addressed leaf and false at every other leaf. "
                        + "The function leaf reads an individual leaf, with false and true leading "
                        + "bits selecting the left and right subregisters."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qram-leaf-additions"),
                DeclarationHandle.Create(Module + "readLeaves"), H("Leaf-controlled additions"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Fix a classical memory D from Address n to an additive commutative group G. "
                        + "At each leaf, its Boolean wire controls addition of that leaf's datum "
                        + "to the bus. A fork first reads its left subtree and then its right "
                        + "subtree into the same bus. Product equivalences only rearrange the "
                        + "register coordinates around those additions. The resulting permutation "
                        + "preserves every routing wire. The recursively defined readAmount is "
                        + "the sum of the enabled data, and describes the effect of this sequence. "
                        + "The paper's Boolean readout is the special case of addition modulo two; "
                        + "arbitrary additive commutative data groups are the extension used here."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qram-query"),
                DeclarationHandle.Create(Module + "query"), H("Compute, read, and uncompute"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The address controls route, the leaf additions follow, and the inverse "
                        + "route is then applied. The inverse reverses the order of the local "
                        + "gates. This composition defines query on all basis configurations, "
                        + "without an initialization hypothesis. For dirty wires w, it preserves "
                        + "the address and w and adds readAmount n D (route n a w) to the bus. "
                        + "For clean n true, this amount is exactly D(a)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qram-matrix"),
                DeclarationHandle.Create(Module + "queryMatrix"), H("The complex query matrix"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For finite G with decidable equality, queryMatrix is Mathlib's "
                        + "Matrix.permMatrixHom applied directly to query. Its rows and columns "
                        + "are indexed by Address n times (Wires n times G). The homomorphism "
                        + "uses the inverse permutation: forward movement of basis states "
                        + "therefore acts on amplitudes by pullback along the inverse. "
                        + "The function initialized embeds an arbitrary complex amplitude "
                        + "function on Address n times G into the full basis by making it "
                        + "zero whenever the routing workspace differs from clean n true."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("qram-correctness"),
                DeclarationHandle.Create(Module + "correctness"),
                H("Correctness at every natural depth"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For every natural n, every address a, every leaf i and either Boolean "
                            + "enable e, routing clean n e gives leaf value e when i = a and "
                            + "false otherwise. In particular an enabled root produces exactly "
                            + "one excited leaf, and a disabled root produces only zero leaves. "
                            + "The empty address at n = 0 is included. The proof inducts through "
                            + "the actual split and both recursive gate networks.")),
                    Paragraph(Text(
                        "For every additive commutative G, memory D, address a, dirty workspace "
                            + "w and initial bus r, query preserves a and w and changes the bus "
                            + "to r + readAmount n D (route n a w). For w = clean n true it "
                            + "changes the bus to r + D(a), restoring every scratch wire and the "
                            + "root enable. The readout proof follows the successive additions; "
                            + "the routing induction supplies the addressed datum.")),
                    Paragraph(Text(
                        "For every finite additive commutative G with decidable equality and "
                            + "every D, queryMatrix has both adjoint products equal to the identity. "
                            + "For every complex amplitude function psi on Address n times G, "
                            + "multiplying initialized psi by queryMatrix yields initialized "
                            + "of the function (a,r) mapped to psi(a,r - D(a)). This is the exact "
                            + "coherent action for arbitrary superpositions of addresses and bus "
                            + "values. It preserves support on the initialized routing workspace. "
                            + "Unitarity and the inverse-permutation action use the pinned "
                            + "permutation-matrix identities directly.")),
                    Paragraph(Text(
                        "The memory D is fixed classical data. These statements concern an ideal "
                            + "reversible Boolean circuit and its complex linear action. They "
                            + "establish no physical locality of the bus, noise guarantee, primitive "
                            + "gate count or depth, three-state router implementation, or copying "
                            + "of unknown quantum memories. Section IV itself warns that its bus "
                            + "interacts with all memory bits. Page-Wootters claims and the original "
                            + "three-state bucket-brigade construction require separate arguments."))),
                DescribeRole.Theorem))));
}
