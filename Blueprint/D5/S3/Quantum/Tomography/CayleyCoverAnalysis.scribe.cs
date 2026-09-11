using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class CayleyCoverAnalysisDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Analytic interfaces for compact chart coverage, local uniqueness, root migration and global residual barriers.",
        H("Cayley Cover Analysis"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("compact-signed-cayley-cover"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/CayleyCoverAnalysis.compact_signed_cayley_cover"),
                H("Two compact charts cover each unit-circle coordinate"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("CompactSignedCayleyCover"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every unit-circle coordinate is represented by one of two closed signed Cayley charts with t in [-1,1]. Applied to five dephased phases, this gives the 32 compact charts including their seams. The theorem does not trust an external subdivision result."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("preconditioned-residual-displacement"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/CayleyCoverAnalysis.preconditioned_residual_controls_displacement"),
                H("Derivative bounds imply quantitative local uniqueness"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("PreconditionedResidualControlsDisplacement"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On a convex set, if C times the actual Frechet derivative differs from the identity by operator norm at most q, then (1-q) times the distance between two points is bounded by their preconditioned residual difference. For q<1, a convex box contains at most one root. The proof consumes Mathlib's Frechet mean-value inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("preconditioned-root-migration"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/CayleyCoverAnalysis.root_displacement_le_of_preconditioned_parameter_perturbation"),
                H("A small parameter perturbation bounds root motion"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("PreconditionedRootMigration"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If roots of two parameter instances remain in one convex uniqueness box and the preconditioned residual perturbation is at most rho, their displacement is at most rho/(1-q). The theorem assumes the second root exists; it is a continuation bound, not a numerical existence oracle."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-residual-root-cover"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/CayleyCoverAnalysis.root_mem_iUnion_of_uniform_residual_gap"),
                H("A residual gap prevents roots outside the certified cover"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("UniformResidualRootCover"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Suppose the center-parameter residual is at least eta outside a union of certified root neighborhoods, while changing the parameter perturbs the residual by at most rho<eta. Then every root at the perturbed parameter remains inside that union. Compactness and interval arithmetic are deliberately external hypotheses to be discharged by later analytic reflection, rather than hidden inside this theorem."))),
                DescribeRole.Theorem))));
}
