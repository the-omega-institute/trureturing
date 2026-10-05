using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class RawEndpointPeelingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/RawEndpointPeeling.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Raw leaf peeling follows one target while separating branch and absent reply groups, and completes each selected source with its entire labelled leaf frontier.",
        H("Raw Endpoint Leaf Peeling"),
        Blocks(
            Paragraph(Text("The sources and four replies are the actual ordered binary trees and their original readout. A strategy uses a single deterministic policy, starts with an empty history on every source, and terminates correctly on every finite source. Fees count the distinct addresses actually requested. L(U) is the existing leafAddresses(U).")),
            Def("Peels", "Safe target-leaf lists",
                "For a finite family F, target z, survivor set S and finite address list qs, Peels recursively requires each address to be a leaf of F(z). The branch and absent response groups in S each have at most one member. The next survivor set is the group reporting the target's actual reply. At the end every survivor is z. When S initially contains z, it retains z throughout. For a nonconflicting family, every leaf reply matches the target label, so the recursion deletes exactly the two nonleaf groups and leaves no competitor at the end."),
            Def("peelController", "Actual raw peeling controller",
                "The controller actually requests the next address. A target reply continues with its response group. A different reply whose group is a singleton starts that source's complete leaf verifier with a fresh logical history; any other reply starts the existing acquisition fallback. Exhausting the list starts the target's complete verifier. The verifier accepts only the complete matching labelled frontier, and mismatches enter acquisition. The paid set comes from the resulting execution history."))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("raw-endpoint-peeling-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
