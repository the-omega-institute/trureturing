using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class LabelResetBandwidthDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Decoherence/LabelResetBandwidth.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Feasibility and exact minimum Gibbs bandwidth for ambient label reset with the average record preserved.",
        H("Exact finite Gibbs-bath label reset"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("average-record-support"),
                DeclarationHandle.Create(Module + "average_support_eq_span"),
                H("Support of the average record"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/mohammady2016minimising")),
                Blocks(
                    Paragraph(Text("For a uniform finite family of pure records the support of the average operator is the span of the record vectors. Positive spectral coordinates on that span give the compressed record state."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("faithful-bath-rank-obstruction"),
                DeclarationHandle.Create(Module + "reset_requires_independent"),
                H("Dependent records obstruct every faithful-bath reset"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/mohammady2016minimising"), LibraryNoteRef.Create("D5/L/Entropy/reeb2014improved")),
                Blocks(
                    Paragraph(Text("The orthogonal classical labels give input rank db for any full-rank bath of dimension b. A prescribed pure output label and preservation of the average record constrain the output rank to at most rb, where r is the record support dimension. Since b > 0 and r ≤ d, a successful reset forces r = d."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ambient-reset-reduced-orbit"),
                DeclarationHandle.Create(Module + "reset_unitary_orbit_iff"),
                H("Equivalence with maximally mixed preparation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/allahverdyan2011thermodynamic"), LibraryNoteRef.Create("D5/L/Entropy/mohammady2016minimising")),
                Blocks(
                    Paragraph(Text("With label-sized orthonormal coordinates of the record support and a faithful bath, ambient reset is equivalent to preparation of the compressed record marginal from a maximally mixed memory with that same bath. The lifting theorem constructs a unitary on label, bath and ambient record and fixes its action on every input column."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ambient-aligned-gibbs-reset"),
                DeclarationHandle.Create(Module + "thermal_reset_attained"),
                H("The aligned Gibbs bath and lifted swap attain the minimum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/reeb2014improved")),
                Blocks(
                    Paragraph(Text("The input is the uniform label ensemble of normalized pure record vectors, tensored with an independent bath. A bath with one basis element per label, in the aligned Gibbs state, and the lifted tensor swap reset the label to any prescribed normalized vector and retain the average record."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("retained-record-gibbs-minimum"),
                DeclarationHandle.Create(Module + "thermal_reset_minimum"),
                H("Minimum bandwidth on the full ambient orbit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/allahverdyan2011thermodynamic"), LibraryNoteRef.Create("D5/L/Entropy/reeb2011hilbert"), LibraryNoteRef.Create("D5/L/Entropy/reeb2014improved"), LibraryNoteRef.Create("D5/L/Entropy/mohammady2016minimising"), LibraryNoteRef.Create("D5/L/Entropy/delrio2011thermodynamic"), LibraryNoteRef.Create("D5/L/Entropy/clivaz2019unifying")),
                Blocks(
                    Paragraph(Text("For linearly independent normalized records, the exact minimum is β⁻¹ log(μ_max/μ_min) for β > 0. The eigenvalues are the positive eigenvalues of the ambient average record. Every admissible bath has b ≥ dμ_max, and a bath of dimension d attains the bandwidth minimum.")),
                    Paragraph(Text("This is a retained-record corollary of the support reduction, the two spectral endpoint bounds and the aligned swap. The output unitary is unrestricted and the preserved quantity is the average record marginal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gibbs-reset-iff-independent"),
                DeclarationHandle.Create(Module + "independent_iff_exists_gibbs_reset"),
                H("Linear independence characterizes Gibbs reset feasibility"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/mohammady2016minimising")),
                Blocks(
                    Paragraph(Text("At each positive inverse temperature, existence of an exact finite Gibbs reset is equivalent to linear independence of the records. The forward construction uses a bath indexed by the labels, and the rank obstruction holds for every finite faithful bath."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("qubit-reset-compatibility"),
                DeclarationHandle.Create(Module + "qubit_output_orbit_iff"),
                H("Compatibility with the qubit erasure orbit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The parent exact qubit erasure package supplies the characterization in its original register order. An admissible full output lies in the input orbit precisely when its label trace lies in the supported two-qubit orbit."))),
                DescribeRole.Theorem))));
}
