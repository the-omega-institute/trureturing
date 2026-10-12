using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class RiemannianCriticalLineInterfaceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The existing critical-line criterion is represented by hyperbolic fixed points and zero displacement.",
        H("Riemannian Critical-Line Interface"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normal-translation-fixed-point-criterion"),
                DeclarationHandle.Create("D5/S3/Zeros/RiemannianCriticalLineInterface.normal_translation_fixed_iff"),
                H("Normal translation fixes the basepoint exactly on the critical line"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The signed offset Re(rho)-1/2 acts as a horizontal isometry of the real hyperbolic upper-half-space model. Its canonical basepoint is fixed exactly when the offset vanishes. This is a geometric interface and adds no zero-free hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rh-normal-displacement-equivalence"),
                DeclarationHandle.Create("D5/S3/Zeros/RiemannianCriticalLineInterface.rh_iff_all_normal_displacements_zero"),
                H("RH is equivalent to zero hyperbolic normal displacement of every actual zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The equivalence quantifies over the repository's actual Zeta23.IsNontrivialZero predicate and rewrites the existing RH-to-critical-line theorem. It is a reformulation, not a proof of RH."))),
                DescribeRole.Theorem))));
}
