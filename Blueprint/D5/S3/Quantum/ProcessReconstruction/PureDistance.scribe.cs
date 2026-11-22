using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class PureDistanceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/PureDistance";
    private static readonly LibraryNoteRef Johnston = LibraryNoteRef.Create("D5/L/ProcessReconstruction/johnston2009computing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An overlap estimate for the trace distance between pure unitary outputs.",
        H("Pure Output Trace Distance"),
        Blocks(
            Describe.Lean(DescribeId.Create("trace-norm-pure-difference"),
                DeclarationHandle.Create(Module + ".traceNorm_pure_sub_le"),
                H("Trace norm bounded by the orthogonal residual"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Johnston),
                Blocks(Paragraph(Text(
                    "For unit Euclidean vectors x and y, the trace norm of the difference of "
                    + "their outer projectors is at most twice the square root of one minus the "
                    + "squared modulus of their inner product. The proof splits the projector "
                    + "difference into two outer products and applies the rank-one trace-norm estimate."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("pure-reference-output"),
                DeclarationHandle.Create(Module + ".pure_referenceError_le"),
                H("Pure joint inputs to two unitary channels"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Johnston),
                Blocks(Paragraph(Text(
                    "Represent a pure state on an arbitrary finite reference and the global input "
                    + "by a unit vector. The unhalved reference error between its two conjugation "
                    + "outputs is bounded by the same overlap expression for the vectors produced "
                    + "by the reference-amplified unitaries."))), DescribeRole.Lemma))));
}
