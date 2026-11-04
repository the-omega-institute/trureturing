using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BurriReverseSourceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Recovery/BurriReverseSource.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The physical complementary state and the source-ordered polar matrix.",
        H("The literal source spaces"),
        Blocks(
            Paragraph(Text("The purified amplitude is obtained by applying the specified physical isometry V to the canonical maximally mixed qubit purification. Its row space is the reference qubit times the complete twelve-dimensional environment; all zero coordinates are retained.")),
            Entry("state", "complementary_state", "The actual complementary state",
                "Tracing out the physical output gives X = J (Y squared / 62) J-adjoint, where J is the prescribed six-dimensional injection. The positive square root is J Y J-adjoint divided by sqrt(62)."),
            Entry("marginals", "physical_marginals", "The physical marginals",
                "The reference marginal is I/2. The environment marginal is diagonal, with active entries (11,10,10)/31 and zero elsewhere. These are partial traces of the same actual purified state."),
            Entry("product", "product_marginal_root", "The product-marginal square root",
                "The positive root of the tensor product of these actual marginals is the active diagonal (s,t,t,s,t,t)/sqrt(62), extended by zero, with s = sqrt(11) and t = sqrt(10)."),
            Entry("matrix", "source_matrix", "Appendix A's ordered matrix",
                "Taking the transpose of sqrt(rho tensor sigmaE) times sqrt(X) gives the exact padded matrix J activeM J-adjoint. Here activeM = Y diag(s,t,t,s,t,t)/62. The prescribed identity-padded rotation makes this full right-polar product positive semidefinite."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
