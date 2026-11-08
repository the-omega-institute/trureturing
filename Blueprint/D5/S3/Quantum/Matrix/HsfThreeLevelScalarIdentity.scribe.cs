using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HsfThreeLevelScalarIdentityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HsfThreeLevelScalarIdentity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uncompiled mathematical source candidate: complex PSD3 cubic geometry and exact scalar coefficients.",
        H("HsfThreeLevelScalarIdentity"),
        Blocks(
            Entry("p396_identity", "p396 identity",
                "Exact P396 factorization: p396=pqr Q^2(p-q)^2(q-r)^2(r-p)^2 positiveCertificate. Raw degree-72 expansion is replaced by smaller elementary-symmetric identities. Its Lean elaboration cost is unmeasured.", DescribeRole.Theorem),
            Entry("p396_nonneg", "p396 nonneg",
                "The actual P396 polynomial is nonnegative for every positive triple, including collisions.", DescribeRole.Theorem),
            Entry("p396_pos", "p396 pos",
                "The actual P396 polynomial is strictly positive at pairwise distinct positive levels.", DescribeRole.Theorem),
            Paragraph(Text("These are source candidates, not compiled or frozen results. "
                + "The scalar P396 source was inspected as fallible mathematical input; "
                + "its separate independent audit was not read. No novelty is claimed. "
                + "The commutant equality classification, original integral-to-moment bridge "
                + "and original HSF derivative/source bridge remain unformalized here. "
                + "Required Lean, axiom, Scribe and registration checks have not run.")))));

    private static DocumentBlock Entry(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("hsfthreelevelscalaridentity-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
