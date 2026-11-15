using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Core.Base;

internal sealed class TensorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Core Base Tensor", H("Core Base Tensor"), Blocks(
            Paragraph(Text("This module makes the certified tensor constructions available to the addressed circuit operators.")))));
}
