using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Contact;

internal sealed class Lemma43Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contact profile counts and accumulated projection dimension.",
        H("Lemma43"),
        Blocks(
            Paragraph(Text("Contact profile counts and accumulated projection dimension. The results below relate lemma43 to the stochastic ellipsoid construction.")),
            Node("claim-1", "neg_log_one_sub_le", "neg log one sub le",
                "The sharp bound. -log(1-x) ≤ x + x² for 0 ≤ x ≤ 1/2. This is the step that fixes the 1/8. The crude -log(1-x) ≤ 2x, also true on [0,1/2], would put γ = 1/2 and destroy the n².", DescribeRole.Theorem),
            Node("claim-2", "rpow_one_sub_le_exp", "rpow one sub le exp",
                "(1 - x)^{-m/2} ≤ exp((m/2)·(x + x²)) for 0 ≤ x ≤ 1/2 and 0 ≤ m.", DescribeRole.Theorem),
            Node("claim-3", "neg_sq_half_add_mul", "neg sq half add mul",
                "-y²/2 + b·y = -(y-b)²/2 + b²/2.", DescribeRole.Theorem),
            Node("claim-4", "half_sq_drift", "half sq drift",
                "The 1/8. With drift b = n√t/2, the Legendre value is b²/2 = n²t/8.", DescribeRole.Theorem),
            Node("claim-5", "integrand_le", "integrand le",
                "Lemma 4.3's integrand, bounded, with the 1/8 explicit. For y > 0 with y√t ≤ 1/2, Φ(y)·(1 - y√t)^{-(n+2)/2} ≤ (e^J / (√(2π)·y)) · e^{n²t/8} · e^{-(y - n√t/2)²/2} where J bounds the junk y√t + ((n+2)/2)·(y√t)². On the paper's range (1 ≤ y ≤ log n, √t ≤ 5√(log n)/n) the junk is o(1), so J may be taken to be any fixed positive number for n past a threshold — but nothing here needs that: J is a hypothesis, so the statement has no n₀. The three ingredients are PaddedTail.Phi's 1/r branch, rpow_one_sub_le_exp (the sharp log bound), and neg_sq_half_add_mul + half_sq_drift (completing the square).", DescribeRole.Theorem),
            Node("claim-6", "lintegral_radial_le", "lintegral radial le",
                "The radial reduction. For a non-negative radial integrand, ∫⁻ x, ofReal (f ‖x‖) ≤ ofReal (n · κ_n · C) whenever the one-dimensional integral is ≤ C.", DescribeRole.Theorem),
            Node("claim-7", "weight_bound_of_radial", "weight bound of radial",
                "ChainData.weight_bound from a radial one-dimensional bound. This is the exact statement the interface consumes: give a non-negative radial profile f dominating the contact weight on each unit cube, an integrability certificate, and a bound C on ∫₀^∞ yⁿ⁻¹ f(y) dy; the Markov threshold field follows.", DescribeRole.Theorem),
            Node("claim-8", "oneDim_le", "one Dim le",
                "I₂ with e^{n²t/8} factored out. The remaining integral is Gaussian.", DescribeRole.Theorem),
            Node("claim-9", "prefactor_cancel", "prefactor cancel",
                "The prefactor cancels. Eq. (56)'s prefactor is n√t/2 = b; the paper's Gaussian bound is K ≤ (2 + 2√(2π))/b. Their product is an absolute constant, with no n and no t left.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
