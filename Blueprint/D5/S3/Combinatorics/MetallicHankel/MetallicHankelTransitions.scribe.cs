using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MetallicHankel;

internal sealed class MetallicHankelTransitionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MetallicHankel/MetallicHankelTransitions.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/han2025hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The quadratic tail cycle produces integral continuants with prescribed degrees and leading approximation errors.",
        H("Integral Metallic Continuant Approximations"),
        Blocks(
            Node("metallic-hankel-transitions-approximation", "The continuant approximation and its leading error", "metallic_approximation",
                "Let n be at least two and let a_p start at v_2 and follow the quadratic state transitions. Read k_p,b_p,D_p from its fraction data, and put v_0 = 1 and v_p = b_p for positive p. Assume s_0 = 0, s_{p+1} = s_p+k_p+1, h_0 = v_0 and h_{p+1} = h_p v_{p+1}. Let Q_0 = 1, Q_1 = D_0, N_0 = 0 and N_1 = v_0 q^{k_0}. Both continuants Y = Q and Y = N satisfy Y_{p+2} = D_{p+1}Y_{p+1} - v_{p+1}q^{k_p+k_{p+1}+2}Y_p. There exists a family of integral formal power series F_p such that q^{n+2} F_0^2 + T F_0 = q^{n-1}, where T = q(1-q^n)/(1-q) + (1+q^n)(1-q). Every Q_p has constant coefficient one and coefficients above degree s_p equal to zero; every N_p has coefficients at degrees at least s_p equal to zero. For every p there is an integral formal power series R_p with Q_p F_0 - N_p = q^{2s_p+k_p}R_p and constant coefficient h_p. Thus the error includes its exact leading coefficient.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
