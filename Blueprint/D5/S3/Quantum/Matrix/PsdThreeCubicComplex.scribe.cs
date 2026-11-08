using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class PsdThreeCubicComplexDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/PsdThreeCubicComplex";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex PSD3 cubic geometry and exact scalar coefficients.",
        H("PsdThreeCubicComplex"),
        Blocks(
            Entry("Mat", "Mat",
                "The existing Mathlib matrix carrier specialized to complex three by three matrices.", DescribeRole.Definition),
            Entry("cycle", "cycle",
                "The actual oriented complex product S01 S12 S20.", DescribeRole.Definition),
            Entry("matrixPair", "matrixPair",
                "The three nonnegative pair terms use the original source diagonal real parts and squared complex entry norms.", DescribeRole.Definition),
            Entry("cubic", "cubic",
                "The weighted matrix pair energy plus k times the real part of the oriented source cycle.", DescribeRole.Definition),
            Entry("negative_cycle_gram", "negative cycle gram",
                "For a complex PSD matrix with negative real cycle, the explicitly scaled vector (xyu,-conj(S01)yv,conj(S01 S12)w) gives a real quadratic-form constraint on the same three diagonal entries. No rank, inverse or external diagonal frame is assumed.", DescribeRole.Theorem),
            Entry("cubic_nonneg", "cubic nonneg",
                "Every complex PSD three by three matrix has nonnegative cubic whenever a,b,c,k are nonnegative and k <= allowance(a,b,c). This includes singular matrices, arbitrary phases and zero weights; the coefficient hypotheses require an independent application-specific proof.", DescribeRole.Theorem),
            Paragraph(Text("The statements concern the explicitly defined closed algebraic kernels. "
                + "The commutant equality classification, identification with the original integrals, "
                + "dominated differentiation and original HSF derivative/source bridge remain outside these results. "
                + "No assertion about arbitrary matrix dimension or literature novelty follows.")))));

    private static DocumentBlock Entry(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("psdthreecubiccomplex-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
