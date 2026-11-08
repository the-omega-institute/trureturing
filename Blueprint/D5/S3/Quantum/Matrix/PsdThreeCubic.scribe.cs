using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class PsdThreeCubicDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/PsdThreeCubic";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex PSD3 cubic geometry and exact scalar coefficients.",
        H("PsdThreeCubic"),
        Blocks(
            Entry("root3", "root3",
                "The real power t^(1/3), used only on nonnegative products in the estimates.", DescribeRole.Definition),
            Entry("allowance", "allowance",
                "For nonnegative edge weights a,b,c, the bound is 2(sqrt(a)sqrt(b)+sqrt(b)sqrt(c)+sqrt(c)sqrt(a))+6(abc)^(1/3).", DescribeRole.Definition),
            Entry("pairEnergy", "pairEnergy",
                "The weighted real pair energy a(d+e)x^2+b(e+f)y^2+c(f+d)z^2.", DescribeRole.Definition),
            Entry("negative_pair_bound", "negative pair bound",
                "If the single real quadratic form with diagonal d,e,f and off-diagonal -x,-y,-z is nonnegative on every real vector, its weighted pair energy dominates allowance(a,b,c)xyz. All weights and edges may vanish. A Gram test vector and three-term AM-GM supply the estimate.", DescribeRole.Theorem),
            Entry("allowance_of_p396", "allowance of p396",
                "For nonnegative a,b,c,k with positive sum of weights, the polynomial bound (a+b+c)k^2 <= 4(a+b+c)(ab+bc+ca)+396abc implies k <= allowance(a,b,c). This is a sufficient comparison and asserts no necessity.", DescribeRole.Theorem),
            Paragraph(Text("The statements concern the explicitly defined closed algebraic kernels. "
                + "The commutant equality classification, identification with the original integrals, "
                + "dominated differentiation and original HSF derivative/source bridge remain outside these results. "
                + "No assertion about arbitrary matrix dimension or literature novelty follows.")))));

    private static DocumentBlock Entry(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("psdthreecubic-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
