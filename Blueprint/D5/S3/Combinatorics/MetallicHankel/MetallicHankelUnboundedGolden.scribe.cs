using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MetallicHankel;

internal sealed class MetallicHankelUnboundedGoldenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedGolden.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/han2025hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three-periodic golden continued fraction gives integral convergents with explicit approximation order and leading error coefficient.",
        H("Convergent Approximation for the Golden Tail"),
        Blocks(
            Node("metallic-hankel-unbounded-golden-golden-approximation", "The golden tail and its convergent errors", "golden_approximation",
                "For each nonnegative integer p, set k_p = 1 when p is congruent to two modulo three and k_p = 0 otherwise. Set v_0 = 1; at positive p, set v_p = 1 when p is congruent to one modulo three and v_p = -1 otherwise. Set D_p = 1+q-q^2 when p is congruent to two modulo three and D_p = 1+q otherwise. Let s_0 = 0, s_{p+1} = s_p+k_p+1, h_0 = v_0 and h_{p+1} = h_p v_{p+1}. Let Q_0 = 1, Q_1 = D_0, N_0 = 0 and N_1 = v_0 q^{k_0}. Suppose both Q and N satisfy U_{p+2} = D_{p+1} U_{p+1} - v_{p+1} q^{k_p+k_{p+1}+2} U_p over integral formal power series. There is a family F of integral formal power series such that q^3 F_0^2 + (1+q-q^2)F_0 = 1. For every p, Q_p has constant coefficient one and no coefficients above degree s_p, while N_p has no coefficients at degrees at least s_p. Moreover, for every p there is an integral formal power series R_p with Q_p F_0 - N_p = q^{2s_p+k_p} R_p and constant coefficient of R_p equal to h_p.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
