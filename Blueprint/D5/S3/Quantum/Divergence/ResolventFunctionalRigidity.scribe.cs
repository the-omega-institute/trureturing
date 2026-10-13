using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class ResolventFunctionalRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Resolvents determine finite spectral intertwining.",
        H("Resolvents determine finite spectral intertwining"), Blocks(
            Describe.Lean(
                DescribeId.Create("cfc-shift-inverse"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/ResolventFunctionalRigidity.cfc_shift_inverse"),
                H("Shifted inverse as finite functional calculus"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/meiburg2026relative")),
                Blocks(Paragraph(Text("For every positive shift and positive semidefinite finite complex matrix, the inverse of "
                        + "A+t I is the actual CFC of x -> 1/(x+t). This organizing helper is consumed by logarithmic "
                        + "rigidity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-resolvent-defects-force-functional-intertwining"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/ResolventFunctionalRigidity.zero_resolvent_defects_force_functional_intertwining"),
                H("All spectral functions intertwine"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/meiburg2026relative")),
                Blocks(Paragraph(Text("Under the norm-saturated contraction comparison, equality of every positive-shift "
                        + "resolvent quadratic form forces f(A) Vb = V f(B)b for every real function f. Repeated "
                        + "eigenvalues are grouped and finite rational residues determine each eigenspace "
                        + "coefficient. No global continuity of f is required because the finite spectra are "
                        + "discrete. The theorem is used in the logarithm-to-Petz proof."))),
                DescribeRole.Theorem))));
}
