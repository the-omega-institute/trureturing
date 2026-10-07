using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Contact;

internal sealed class Lemma43BDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contact profile counts and accumulated projection dimension.",
        H("Lemma43B"),
        Blocks(
            Paragraph(Text("Contact profile counts and accumulated projection dimension. The results below relate lemma43b to the stochastic ellipsoid construction.")),
            Node("claim-1", "mul_exp_neg_le", "mul exp neg le",
                "s·e^{-s} ≤ e⁻¹ for every real s. One application of 1 + x ≤ e^x at x = s - 1.", DescribeRole.Theorem),
            Node("claim-2", "sq_mul_exp_le_four", "sq mul exp le four",
                "b²·e^{-b²/8} ≤ 4. This is what makes the near piece of the split integrate to ≤ 2/b.", DescribeRole.Theorem),
            Node("claim-3", "integral_shifted_gaussian", "integral shifted gaussian",
                "The total mass of the shifted Gaussian.", DescribeRole.Theorem),
            Node("claim-8", "norm_le_of_mem_cube", "norm le of mem cube",
                "Every point of the unit cube at y has norm within √n/2 of ‖y‖.", DescribeRole.Theorem),
            Node("claim-9", "dom_of_antitone", "dom of antitone",
                "Worst-point domination from antitonicity. With f r = g (r − √n/2) for an antitone g, the weight g ‖toE n y‖ is dominated by f ‖x‖ at *every* x in the cube at y.", DescribeRole.Theorem),
            Node("claim-10", "subst", "subst",
                "The substitution y ↦ r = (a₀ − s·y)^{−1/2}, with s = √t.", DescribeRole.Definition),
            Node("claim-11", "substDeriv", "subst Deriv",
                "Its derivative, s / (2·u^{3/2}) with u = a₀ − s·y.", DescribeRole.Definition),
            Node("claim-13", "subst_sq", "subst sq",
                "(a₀ − s·y) = 1/(subst a₀ s y)²: the substitution inverts r ↦ (a₀ − r^{−2})/s.", DescribeRole.Theorem),
            Node("claim-15", "strictMonoOn_subst", "strict Mono On subst",
                "The substitution is strictly increasing where it is defined (s > 0).", DescribeRole.Theorem),
            Node("claim-16", "subst_integrand", "subst integrand",
                "The substituted integrand. |φ'(y)|·φ(y)^{n−1} = (s/2)·(a₀ − s·y)^{−(n+2)/2} — the exponent (n+2)/2 of eq. (56), assembled from r^{n−1} and the Jacobian's u^{−3/2}.", DescribeRole.Theorem),
            Node("claim-17", "rpow_neg_le_of_one_le", "rpow neg le of one le",
                "The a₀ ≥ 1 normalisation (p. 20): (a₀ − u)^{−c} ≤ (1 − u)^{−c}, which is how the substituted integrand (a₀ − s·y)^{−(n+2)/2} is handed to Lemma43.integrand_le, whose statement is normalised at a₀ = 1. The paper writes this as a₀^{−(n+2)/2} ≤ 1.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
