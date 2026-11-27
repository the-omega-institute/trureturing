using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Theta;

internal sealed class LocalThetaCorrespondenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local Theta Correspondence", H("Local Theta Correspondence"),
        Blocks(
            Paragraph(Text("Local theta correspondence: positivity, fixed by partner projector, generation by the joint harmonic.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Theta/LocalThetaCorrespondence.exists_bump_integratedRep_eq"),
                H("exists_bump_integratedRep_eq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For an oscillator pair π, π' on Fock space, a joint harmonic Φ of parameters λ, λ' and any polynomial P, there is a compactly supported smooth α on the second group with π(e_λ)P = π'(α)π(e_λ)Φ.")))))));
}
