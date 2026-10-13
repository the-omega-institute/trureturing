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
                DescribeId.Create("finite-resolvent-defects-force-functional-intertwining"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/ResolventFunctionalRigidity.finite_resolvent_defects_force_functional_intertwining"),
                H("Finite positive samples determine the spectral calculus"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyi2017reversibility")),
                Blocks(Paragraph(Text("Let A and B be arbitrary finite positive semidefinite complex matrices and V a "
                        + "contraction with V* A V <= B. Suppose V preserves the norm of the distinguished vector b. "
                        + "If the actual resolvent quadratic defects vanish at an injective finite family of "
                        + "positive shifts, and the number of shifts is at least the number of distinct eigenvalues "
                        + "in the union of the two spectra, then f(A) Vb = V f(B)b for every real function f. "
                        + "The two matrix carriers and the sampling carrier have independent universes; empty "
                        + "carriers, repeated eigenvalues and zero eigenvalues remain in scope.")),
                    Paragraph(Text("Group repeated spectral values before clearing the common resolvent denominator. "
                        + "The numerator has degree at most the number of distinct spectral sites minus one. "
                        + "Its distinct positive sample roots force it to vanish, and evaluation at each negative "
                        + "spectral site isolates its residue. The contraction defect identity supplies actual "
                        + "resolvent-vector equality; finite spectral expansion then supplies every f. No "
                        + "continuity of f and no recovery equation are assumed. The existing all-positive-shift "
                        + "theorem consumes this finite result in the live logarithm-to-Petz proof.")),
                    Paragraph(Text("Hiai and Mosonyi's Theorem 3.18 identifies the related spectral-cardinality "
                        + "support condition for standard quantum f-divergence reversibility. This result supplies "
                        + "the finite spectral rigidity step. A representing measure, its support-to-defect bridge "
                        + "and the singular standard f-divergence boundary terms are separate obligations; this "
                        + "theorem does not establish the full f-divergence recovery equivalence."))),
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
