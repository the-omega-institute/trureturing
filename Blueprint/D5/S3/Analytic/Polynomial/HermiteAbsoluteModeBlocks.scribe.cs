using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Polynomial;

internal sealed class HermiteAbsoluteModeBlocksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Polynomial/HermiteAbsoluteModeBlocks.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026hermitesignedmode");

    private static DocumentBlock Def(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The absolute Hermite mode has a quadratic threshold and a floor formula, its differences form "
            + "blocks (1,−1) and (1,1,−1), ties sit at b and b + 2, and it interlaces the signed mode.",
        H("The absolute Hermite mode and its interlacing with the signed mode"),
        Blocks(
            Def("hermite-abs-h", "hOffset", "The offset h_k", "h_k is the least j with (j + 1)(j + 2) ≥ 4k."),
            Def("hermite-abs-start", "absStart", "The block start m_k", "m_k = 2k + h_k, so m_0 = 0."),
            Def("hermite-abs-l", "L", "The long-block indices", "L_j = ⌊(j + 1)(j + 2)/4⌋."),
            Def("hermite-abs-signedmax", "signedMax", "The signed maximum B(n)",
                "B(n) is the coefficient of H_n at the signed mode a(n)."),
            Def("hermite-abs-absmax", "absMax", "The absolute maximum M(n)",
                "M(n) is the absolute value of the coefficient of H_n at the absolute mode b(n)."),
            Describe.Lean(DescribeId.Create("hermite-abs-blocks-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Threshold, floor formula, blocks, ties and interlacing"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let b(n) be the least exponent of a largest absolute coefficient of the physicists' "
                        + "H_n and t(n) = (n − b(n))/2. Then b(n) ≡ n (mod 2), and for j ≡ n (mod 2), b(n) ≤ j "
                        + "exactly when j² + 5j + 2 ≥ 2n. Every degree has a unique absolute maximum or exactly two, "
                        + "and the maximum is unique exactly off the tie degrees N_m. Moreover "
                        + "t(n) = ⌊(2n + 5 − √(8n + 17))/4⌋, b(n)² ≤ 2n (equality only at n = 0, 2) and −5/2 < b(n) − √(2n). The difference "
                        + "b(n + 1) − b(n) is −1 exactly when n + 1 = m_k; m_0 = 0, m_1 = 3 and m_{k+1} − m_k "
                        + "∈ {2, 3}, with gap three exactly when k = L_j, m_{L_j} = 2L_j + j, and gap two strictly "
                        + "between consecutive L_j. At a tie degree the maximizing exponents are b(n) and b(n) + 2, "
                        + "their coefficients have opposite signs and B(n) = M(n); in general B(n) = M(n) exactly "
                        + "at tie degrees or when t(n) is even; and a(n) − b(n) ∈ {−2, 0, 2}.")),
                    Paragraph(Text(
                        "The coefficient at exponent n − 2r is (−1)^r times its absolute value U_{n,r}, and the "
                        + "ratios U_{n,r}/U_{n,r−1} = (j + 1)(j + 2)/(4r), j = n − 2r, strictly decrease. So U rises "
                        + "strictly up to t(n) − 1, weakly to t(n), and strictly falls afterwards; the threshold "
                        + "and the floor formula follow from solving (2j + 5)² ≥ 8n + 17. The signed maximum is the "
                        + "largest U at an even index; by the shape of U that index is t(n) or a neighbour, giving "
                        + "the interlacing, and it equals M(n) exactly when t(n) is even or, at a tie degree, when the "
                        + "second maximizing index t(n) − 1 is even. Substituting n = 2k + j in the threshold gives the block starts m_k, and "
                        + "(j + 1)(j + 2) increases by 2j + 4 ≥ 4, so h_{k+1} − h_k ∈ {0, 1}, with a jump exactly at "
                        + "k = L_{h_k}. The bound b(n)² ≤ 2n uses the failure of the threshold at b(n) − 2. This covers "
                        + "Corollary 4 and the clauses of Theorem 3 not already in the frozen HermiteAbsoluteMode "
                        + "and HermiteAbsoluteTieOrders results, from H. Ma and W. Zhang (DOI 10.5281/zenodo.23957586), "
                        + "on questions of Mike Sheppard in OEIS A381423, A381524 and A381737."))),
                DescribeRole.Theorem))));
}
