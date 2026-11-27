using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class MontgomeryMatchingCapDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Analytic/Oscillation/MontgomeryMatchingCap";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Disjoint close-pair defects amplify into a strict Lorentz cap under a zero-phase bound.",
        H("Disjoint close-pair defects and a strict Lorentz cap"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-matching-defect"),
                DeclarationHandle.Create(Owner + ".finite_matching_defect"),
                H("Finite matching defect inequality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take any finite set of copies with real ordinates γ(u). Repeated ordinates are allowed. "
                        + "Let M be a matching of ordered pairs (u,v) of these copies, with all endpoints "
                        + "distinct and |γ(u)−γ(v)| ≤ 1 for every pair. Let C(u) count all copies whose "
                        + "ordinate is within distance one of γ(u), including the boundary.")),
                    Paragraph(Text(
                        "For real t, let G(t) be the sum of K(γ(i)−γ(j)) cos(t(γ(i)−γ(j))) over all "
                        + "ordered pairs (i,j) of copies, where K(d) = 4/(4+d²). Then")),
                    MatchingBound(),
                    Paragraph(Text(
                        "For each column in the first endpoint's neighborhood, the two Lorentz weights "
                        + "are at least four fifths and one half, respectively. The square of the sum "
                        + "of the chord lengths from the two endpoint phases to the column phase is "
                        + "at most thirteen fourths of their weighted squared sum. The triangle "
                        + "inequality and the squared chord identity give the stated lower bound per "
                        + "column. Disjoint endpoints let us sum distinct rows. All omitted terms are nonnegative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("spectrum-matching-defect"),
                DeclarationHandle.Create(Owner + ".spectrum_matching_defect"),
                H("Defect for a spectrum with multiplicities"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a spectrum truncated at a real height H, retain each ordinate at or below H "
                        + "with its full multiplicity. Use the same oriented matching of distinct retained "
                        + "endpoints at distance at most one, and count neighborhoods among the retained "
                        + "copies. For this cutoff, G(t) is the ordered Montgomery sum, with each ordinate "
                        + "pair weighted by the product of its multiplicities. At every real t the deficit satisfies")),
                    MatchingBound(),
                    Paragraph(Text(
                        "Expanding every multiplicity into distinct copies identifies both Montgomery sums "
                        + "with the corresponding finite sums at zero and at t."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("strict-normalized-cap-of-matching"),
                DeclarationHandle.Create(Owner + ".strict_normalized_cap_of_matching"),
                H("Conditional normalized cap"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose H > 1, c₂ ≥ 0 and c₃ ≥ 0. At the tested frequency t the same matching "
                        + "has at least c₁ H log H pairs. Each pair has phase residual at least c₂, and "
                        + "its first endpoint's closed neighborhood contains at least c₃ log H copies.")),
                    Paragraph(Text(
                        "Divide both ordered sums by H(log H)². If the normalized zero-frequency sum is at "
                        + "most κ − η + 4c₁c₂c₃/13, the normalized sum at t is at most κ − η. A positive η "
                        + "gives a strict bound below κ. Obtaining sufficiently many such close pairs "
                        + "with a uniform phase residual for actual zeta zeros across a long frequency "
                        + "band remains open."))),
                DescribeRole.Theorem))));

    private static DocumentBlock MatchingBound()
    {
        var pair = F.Seq(F.Open, F.Id("u"), F.Comma, F.Id("v"), F.Close);
        var gap = F.Seq(F.GammaLower, F.Open, F.Id("u"), F.Close, F.Minus,
            F.GammaLower, F.Open, F.Id("v"), F.Close);
        return new DocumentBlock.DisplayFormula(F.Seq(
            F.Frac, F.Grp(F.D(4)), F.Grp(F.D(1, 3)),
            F.Sum, F.Underscore, F.Grp(pair, F.InMacro, F.Sp, F.Id("M")),
            Call("C", Id("u")),
            F.OpenBracket, F.D(1), F.Minus, F.Operatorname, F.Grp(F.Id("cos")),
            F.Open, F.Id("t"), F.Open, gap, F.Close, F.Close, F.CloseBracket,
            F.Leq, Call("G", Num(0)), F.Minus, Call("G", Id("t"))));
    }
}
