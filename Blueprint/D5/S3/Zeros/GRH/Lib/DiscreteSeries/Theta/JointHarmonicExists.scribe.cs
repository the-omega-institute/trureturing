using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Theta;

internal sealed class JointHarmonicExistsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint Harmonic Exists", H("Joint Harmonic Exists"),
        Blocks(
            Paragraph(Text("Products of minors are joint harmonics; existence for matched parameters.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Theta/JointHarmonicExists.exists_isJointHarmonic"),
                H("exists_isJointHarmonic"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If the parameters l, l' match for T (IsMatch), then there is a joint harmonic polynomial Φ in the sense of IsJointHarmonic: nonzero and highest for both lowest K-types Λ and Λ'.")))))));
}
