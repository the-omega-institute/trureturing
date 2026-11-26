using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower;

internal sealed class SeventhCutoffDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SeventhCutoff";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed sixth and seventh prime-power contributions",
        H("From the finite exponent sum to the normalized tail"),
        Blocks(
            Entry("seventh-cutoff-bound", "abs_psi_sub_roots_add_theta_sixth_sub_seventh_le", "The finite signed correction",
                "Subtract θ(t) and the square, cube and fifth ψ cutoffs from ψ(t). "
                + "The common finite exponent sum has coefficients -1, +1 and 0 at exponents six, seven "
                + "and eight. Adding θ(t^(1/6)) and subtracting θ(t^(1/7)) leaves an absolute error at "
                + "most 4 log(t)t^(1/9) for every t ≥ 2.",
                DescribeRole.Theorem),
            Entry("sixth-seventh-normalized", "sixth_seventh_normalized", "The scaled tail and its uniform error",
                "Under RH the two θ terms can be replaced by their powers with a pointwise error of order t^(1/8). "
                + "Integrate against t^(-2) from x to infinity and multiply by sqrt(x). "
                + "The sixth and seventh terms become -(6/5)x^(-1/3) and +(7/6)x^(-5/14). "
                + "The resulting absolute error is bounded by a positive constant times x^(-3/8) for all x ≥ 5000^7.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(
        string id, string name, string heading, string explanation, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + "." + name),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), role);
}
