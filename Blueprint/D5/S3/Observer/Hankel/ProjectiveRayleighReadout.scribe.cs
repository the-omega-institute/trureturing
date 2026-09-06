using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hankel;

internal sealed class ProjectiveRayleighReadoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex projective eigenmode recovery and goal-oriented scalar-readout guarantees.",
        H("Projective Rayleigh Readout"),
        Blocks(
            Describe.Lean(DescribeId.Create("overlap-nonzero"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectiveRayleighReadout.rayleigh_overlap_ne_zero"), H("Nonzero candidate overlap"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual eigenvector with nonzero image and eigenvalue below the candidate-orthogonal coercivity threshold has nonzero overlap. No unit eigenvector or bounded extension of the operator is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("error-energy"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectiveRayleighReadout.projective_error_energy_identity"), H("Actual normalized error identity"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The error obtained by dividing the actual eigenvector by its candidate overlap is orthogonal to the unit candidate. Its energy identity is derived from the complex linear domain action and domain symmetry."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("budget-transfer"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectiveRayleighReadout.projective_budget_transfer"), H("Two-sided enclosure budget"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Transfers the actual residual-energy inequality to the budget (upper-lower)/(threshold-lower). The hypotheses imply both nonnegativity and strict upper bound one; an extra width condition is unnecessary."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("projective-enclosure"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectiveRayleighReadout.rayleigh_projective_enclosure"), H("Complex projective enclosure"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("From a genuine possibly unbounded operator domain and energy data, proves nonzero overlap, orthogonality and the projective norm error. The eigenvector need not be normalized, and its eigenvalue is not separately assumed below the candidate Rayleigh quotient."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("readout-geometry"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectiveRayleighReadout.readout_orthogonal_geometry"), H("Candidate-adapted readout geometry"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Projects the actual readout representer off the unit candidate and proves the exact Pythagorean norm difference."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("readout-error"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectiveRayleighReadout.centered_readout_error_bound"), H("Goal-oriented readout error"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Only the orthogonal part of the readout can see the normalized state error. Cauchy--Schwarz gives the error square as the projected readout norm squared times the projective budget, rather than the full readout norm."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("readout-nonzero"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/ProjectiveRayleighReadout.readout_ne_zero_of_margin"), H("Certified nonzero readout"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A strict candidate readout margin excludes a zero for every orthogonal perturbation within the certified budget. This does not identify an arithmetic determinant or prove a scale limit to Xi."))), DescribeRole.Theorem)),
        []));
}
