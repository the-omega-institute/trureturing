using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.NormCompression;

internal sealed class ThreePointPositivityGateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite 3-by-3 positivity shell.", H("ThreePointPositivityGate"), Blocks(
            Paragraph(Text("The abstract one-versus-many inequality used in the three-point trace positivity argument implies positive semidefiniteness of a real 3-by-3 matrix. Same-sign vectors use entrywise nonnegativity; mixed signs reduce to the sum of the squares (c w - L)^2 and (c S - L^2). This module records only the finite algebraic gate; the analytic Carlen--Lieb input remains separate.")))));
}
