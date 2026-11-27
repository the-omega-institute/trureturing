using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Theta;

internal sealed class JointHarmonicUniqueDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint Harmonic Unique", H("Joint Harmonic Unique"),
        Blocks(
            Paragraph(Text("Weights of matched parameters; uniqueness up to scalar of the joint harmonic.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Theta/JointHarmonicUnique.unique"),
                H("unique"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For matching parameters l, l' (IsMatch), any two polynomials P, Q satisfying FockDualPair.IsPreJointHarmonic are proportional: P = cQ for some complex number c.")))))));
}
