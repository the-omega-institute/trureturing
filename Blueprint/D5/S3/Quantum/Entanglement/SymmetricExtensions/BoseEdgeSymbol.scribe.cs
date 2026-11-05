using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SymmetricExtensions;

internal sealed class BoseEdgeSymbolDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The existing tensor marginal adjoint in coherent coordinates",
        H("The existing tensor marginal adjoint in coherent coordinates"), Blocks(
            Paragraph(Text("This module contains private proof helpers consumed by BoseHierarchy.gnp_characterization. They reuse DickeExtension's actual edgeSplit and edgeLift, factor the coherent tensor across the two retained registers and their complement, and evaluate the complementary norm sum. There is one tensor model and one unnormalized partial trace throughout.")),
            Paragraph(Text("The resulting polynomial multiplier in the complete-graph characterization is the norm sum to the power r-2. The mathematical characterization is prior Gulati-Nechita-Park Theorem 8.16; the star applications are from Haobo Ma then Wenlin Zhang. This helper module introduces no separate public characterization or application theorem.")))));
}
