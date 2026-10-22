using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockPhysicalWordLocalityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary Dong applies to the actual physical normal words",
        H("Ordinary Dong applies to the actual physical normal words"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("latticehalffockphysicalword-locality"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockPhysicalWordLocality.physicalWord_locality"),
                H("All physical normal words are mutually local"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The completed original charged coefficient physical locality is evaluated at the exact parity-slice exponents. Its doubled cover shifts become ordinary integer-mode shifts with killing order the absolute charge pairing. The jet/charge and jet/jet localities are separately proved on the same actual carrier. Two finite word inductions consume the existing normalMinusOne_locality theorem through FiniteFieldLocality.localNormal; its sum of the three input orders gives a genuine sufficient bound independent of every target vector."))),
                DescribeRole.Theorem),
            Paragraph(Text("physicalWord is constructed from actual lower-truncated integer fields. Existing normal-product pointwise support proofs justify Dong's residue interchanges. No all-state twisted locality or twisted module identity is assumed. The full original VOA/string/AdS objective remains open.")))));
}
