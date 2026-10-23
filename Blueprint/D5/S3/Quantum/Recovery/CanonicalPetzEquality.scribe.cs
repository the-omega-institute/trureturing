using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class CanonicalPetzEqualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Supported entropy equality exactly characterizes fixed Petz recovery.",
        H("Supported entropy equality exactly characterizes fixed Petz recovery"), Blocks(
            Describe.Lean(
                DescribeId.Create("equality-intertwining"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/CanonicalPetzEquality.equality_intertwining"),
                H("Actual entropy equality controls modular functions"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/meiburg2026relative")),
                Blocks(Paragraph(Text("Equality of the supported canonical finite relative entropy for the actual channel model "
                        + "gives f(A) xi = V f(B) eta for every real f. The model is constructed from the same actual "
                        + "channel and states; it is not an arbitrary abstract witness supplied as the conclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("inverse-sqrt-coordinates"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/CanonicalPetzEquality.inverse_sqrt_coordinates"),
                H("Actual inverse-square-root recovery coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/meiburg2026relative")),
                Blocks(Paragraph(Text("Apply the functional intertwining to the inverse square root on the positive relative "
                        + "modular spectrum. The resulting coordinates give the input support columns of the actual "
                        + "adjoint recovery core."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("supported-entropy-equality-iff-fixed-petz-recovery"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/CanonicalPetzEquality.supported_entropy_equality_iff_fixed_petz_recovery"),
                H("One fixed channel, then all supported input states"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/meiburg2026relative")),
                Blocks(Paragraph(Text("For arbitrary finite decidable nonempty input and output carriers, every bundled quantum "
                        + "channel Phi and density sigma admit one completed Petz recovery channel. The statement "
                        + "first fixes its full-matrix action and proves recovery of sigma, then quantifies over "
                        + "every rho with ker sigma contained in ker rho. For every such rho, equality of finite "
                        + "trace-log relative entropy before and after Phi is equivalent to recovery of rho by that "
                        + "same channel. All inverse square roots are spectral pseudoinverses; no full-rank, "
                        + "commutativity, or dimension-specific assumption is imposed. The unsupported "
                        + "infinite-entropy branch is outside this equivalence: infinity=infinity is not a recovery "
                        + "criterion. The forward implication consumes log rigidity, spectral support reconstruction, "
                        + "Schwarz and equal-trace positive-order rigidity; the converse consumes the existing DPI "
                        + "twice. This is a formalization of the classical Petz sufficiency theorem, not a claim of "
                        + "literature novelty. See Hiai-Mosonyi-Petz-Beny, Quantum f-divergences and error "
                        + "correction, arXiv:1008.2529, equation (3.2), Lemma 3.2 and Theorem 5.1, with the "
                        + "full-space CPTP completion following that theorem."))),
                DescribeRole.Theorem))));
}
