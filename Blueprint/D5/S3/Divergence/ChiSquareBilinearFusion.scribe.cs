using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class ChiSquareBilinearFusionDocument : IScribeDocumentDefinition
{
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Capacity(Formula channel) =>
        Seq(F.Id("C"), Underscore, Grp(D(2)), Open, channel, Close);

    public DocumentDefinition Create()
    {
        var i = F.Id("I");
        var y = F.Id("Y");
        var z = F.Id("Z");
        var p = F.Id("P");
        var q = F.Id("Q");
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var type = Seq(Operatorname, Grp(F.Id("Type")));
        var estimate = Seq(
            Call("Nonnegative", p), Sp, Rightarrow, Sp,
            Call("Nonnegative", q), Sp, Rightarrow, Sp,
            Call("RowStochastic", p), Sp, Rightarrow, Sp,
            Call("RowStochastic", q), Sp, Rightarrow, Sp,
            Capacity(Call("star", p, q)), Le, Sp,
            Capacity(p), Plus, Capacity(q), Plus,
            new Formula.Number(16), Sp, Call("card", i), Sp, Capacity(p), Sp, Capacity(q));
        var tables = All("P", Seq(i, Sp, To, Sp, y, Sp, To, Sp, real),
            All("Q", Seq(i, Sp, To, Sp, z, Sp, To, Sp, real), estimate));
        var statement = All("I", type, All("Y", type, All("Z", type, Seq(
            OpenBracket, Call("Fintype", i), CloseBracket, Sp,
            OpenBracket, Call("Nonempty", i), CloseBracket, Sp,
            OpenBracket, Call("Fintype", y), CloseBracket, Sp,
            OpenBracket, Call("Fintype", z), CloseBracket, Comma, Sp, tables))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A uniform bilinear chi-square bound for finite observations of a common hidden input.",
            H("Bilinear Chi-Square Fusion for Finite Channels"),
            Blocks(Describe.Lean(
                DescribeId.Create("finite-channel-bilinear-chi-square-fusion"),
                DeclarationHandle.Create("D5/S3/Divergence/ChiSquareBilinearFusion.bilinear_fusion_bound"),
                H("Arbitrary channel tables and finite output alphabets"),
                StatementSource.FromAuthor(Disp(statement)),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/gupolyanskiy2023potts")),
                Blocks(
                    Paragraph(Text(
                        "I is any nonempty finite input type, n = |I|, and the hidden input is uniform on I. " +
                        "Y and Z are arbitrary finite output types. Nonnegative(P) means P(i,y) ≥ 0 for every " +
                        "input and output, and RowStochastic(P) means Σ_y P(i,y) = 1 for each input; Q has " +
                        "the corresponding conditions. No permutation symmetry is required.")),
                    Paragraph(Text(
                        "The output margin is m_P(y) = n⁻¹ Σ_i P(i,y), and the capacity is " +
                        "C₂(P) = n⁻¹ Σ_y (Σ_i P(i,y)²)/m_P(y) − 1. The product table is " +
                        "star(P,Q)(i,(y,z)) = P(i,y)Q(i,z). Thus the outputs are conditionally independent " +
                        "given the same input. Real division retains 0/0 = 0. Zero entries, zero output " +
                        "columns, redundant symbols and zero overlap are all included.")),
                    Paragraph(Text(
                        "Write E for uniform input averaging. The likelihood x_y(i) is P(i,y)/m_P(y) on " +
                        "a positive-mass column and one on a zero column. Its mean is one, its range is " +
                        "[0,n], and Σ_y m_P(y)x_y(i) = 1 for each input i. The zero-column convention " +
                        "has zero weight and satisfies the exact reconstruction m_P(y)x_y(i) = P(i,y). " +
                        "The same identities hold for the likelihood r of Q.")),
                    Paragraph(Text(
                        "For a = x − 1 and b = r − 1, put A = E(a²), B = E(b²), c = E(ab), " +
                        "d = E(a²b), e = E(ab²), and H = E(x²r²)/E(xr) − 1. The rational estimate is " +
                        "H ≤ A + B + (3 − A − B)c + 2d + 2e + 16nAB. On 1 + c ≥ 1/2 an exact " +
                        "numerator expansion and Cauchy–Schwarz control its remainder. On the complementary " +
                        "region, E|ab| ≥ 1/2 forces AB ≥ 1/4; the zero-inclusive bound H ≤ n(1+c) − 1 " +
                        "controls the small denominator.")),
                    Paragraph(Text(
                        "Averaging over the two output-margin weights cancels the terms c, Ac, Bc, d and e " +
                        "by coordinate calibration. The average of AB factors into the two capacities. " +
                        "These auxiliary product weights do not replace the actual joint output margin, " +
                        "which is m_P(y)m_Q(z)E(x_y r_z). The exact ratio reconstruction gives the stated " +
                        "bound, independent of both output cardinalities. In particular, for n ≥ 2 one " +
                        "may take the positive coefficient K_n = 16n.")),
                    Paragraph(Text(
                        "This finite-channel estimate is an ingredient for information combining and asymmetric " +
                        "noisy observations. The research anchor is the Gu–Polyanskiy Potts-model question on BP " +
                        "uniqueness, boundary irrelevance and global stability above the Kesten–Stigum threshold " +
                        "(arXiv:2303.14688v2, Appendix H). This theorem does not establish convergence of an " +
                        "iterated tree recursion, the conjectured global stability, infinite output extensions, " +
                        "an optimal coefficient, or mathematical novelty."))),
                DescribeRole.Theorem))));
    }
}
