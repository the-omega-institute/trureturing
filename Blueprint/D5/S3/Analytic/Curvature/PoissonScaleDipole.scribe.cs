using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Curvature;

internal sealed class PoissonScaleDipoleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reflected off-line curvature dipole is the scale derivative of the real "
            + "Poisson kernel and retains its zero-total-mass law.",
        H("Poisson Scale Dipole"),
        Blocks(Describe.Lean(
            DescribeId.Create("poisson-scale-dipole"),
            DeclarationHandle.Create(
                "D5/S3/Analytic/Curvature/PoissonScaleDipole.poisson_scale_dipole"),
            H("The off-line curvature dipole is a Poisson scale derivative"),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The pointwise identity differentiates the actual real Poisson kernel in its "
                    + "positive scale parameter. Integrability and zero total mass are "
                    + "transported from the frozen off-line curvature theorem, so this is a "
                    + "representation bridge and introduces no RH premise."))),
            DescribeRole.Theorem))));
}
