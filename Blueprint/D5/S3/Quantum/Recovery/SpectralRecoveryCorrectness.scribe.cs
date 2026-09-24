using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class SpectralRecoveryCorrectnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The computed spectral transpose recovery is exact whenever any represented Kraus left inverse exists. The proof derives observable intertwining from that inverse, then reuses cfc commutation and the computed support identity. Together with the finite Kraus criterion this closes the three-way equivalence in the finite representation.",
        H("SpectralRecoveryCorrectness"),
        Blocks(new[]
        {
            "left_inverse_observable_intertwines",
            "computed_recovery_of_kraus_left_inverse",
            "scalar_condition_iff_spectral_left_inverse"
        }.Select(name => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/SpectralRecoveryCorrectness." + name),
            H(name.Replace('_', ' ')),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/barnumknill2002reversal"),
                LibraryNoteRef.Create("D5/L/nayaksen2007invertible"),
                LibraryNoteRef.Create("D5/L/choijohnstonkribs2009multiplicative")),
            Blocks(Paragraph(Text("The computed spectral transpose recovery is exact whenever any represented Kraus left inverse exists. The proof derives observable intertwining from that inverse, then reuses cfc commutation and the computed support identity. Together with the finite Kraus criterion this closes the three-way equivalence in the finite representation."))),
            DescribeRole.Theorem)).ToArray())));
}
