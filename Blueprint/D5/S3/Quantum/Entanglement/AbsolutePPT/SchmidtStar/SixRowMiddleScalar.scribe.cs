using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar;
internal sealed class SixRowMiddleScalarDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Assuming W>=T138 gives a0<=a without requiring a0>=0. The positive denominator 2-3r clears the head cap and head-box bounds with the correct inequality directions. Mass and the stronger tail cap give H,D<=3 and q<=2. This module assumes scalar consequences; deriving them from arbitrary APPT spectra, concentration, attainment and uniqueness belongs to the full six-row proof and is not asserted here.", H("SixRowMiddleScalar"), Blocks(
            Paragraph(Text("Assuming W>=T138 gives a0<=a without requiring a0>=0. The positive denominator 2-3r clears the head cap and head-box bounds with the correct inequality directions. Mass and the stronger tail cap give H,D<=3 and q<=2. This module assumes scalar consequences; deriving them from arbitrary APPT spectra, concentration, attainment and uniqueness belongs to the full six-row proof and is not asserted here.")),
            Describe.Lean(DescribeId.Create("sixrowmiddlescalar-hyp6"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleScalar.Hyp6"),
                H("Hyp6"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nonnegative H,D,q; mass, tail box/mass/cap, head square/cap/box, squared same-vector coupling, and centered variance premises."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sixrowmiddlescalar-middle-strict"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleScalar.middle_strict"),
                H("middle_strict"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Hyp6 r H D a q -> 1/5 <= r -> r <= 3/10 -> W r H D a q < T138 r."))), DescribeRole.Theorem)
        )));
}
