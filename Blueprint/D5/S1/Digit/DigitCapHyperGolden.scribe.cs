using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class DigitCapHyperGoldenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/DigitCapHyperGolden.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/coonsspiegelhofer2017hyper");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The digit cap ell at radix ell has upper growth exponent log_ell φ, for the count at n "
            + "and for the hyper-expansion convention at n−1.",
        H("Hyper-ell-ary expansions and the golden ratio"),
        Blocks(
            Describe.Lean(DescribeId.Create("digit-cap-hyper-golden-shifted"),
                DeclarationHandle.Create(Prefix + "hyperExponent"),
                H("The exponent in the source convention"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "hyperExponent ell is the infimum over N≥2 of the supremum over n≥N of "
                    + "log b(n−1)/log n, where b counts representations with digits 0,…,ell. "
                    + "Coons and Spiegelhofer write s_ell(n) for the number of "
                    + "hyper-(ell-ary)-expansions of n−1."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("digit-cap-hyper-golden-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The exponent log_ell φ"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every natural ell≥2, both the upper exponent of the cap ell at radix ell "
                    + "and hyperExponent ell equal log_ell φ with φ=(1+√5)/2. Theorem 1 (Defant) "
                    + "in Coons–Spiegelhofer gives the sharper statement that s_ell(m)/m^(log_ell φ) "
                    + "has limsup φ^(log_ell(ell^2−1))/√5."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("digit-cap-hyper-golden-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Proof by Fibonacci envelopes and alternating digits"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The lowest-digit recursion gives b(ell·q)=b(q)+b(q−1) and b(ell·q+r)=b(q) "
                    + "for 1≤r<ell. Of two consecutive integers at most one is divisible by ell, "
                    + "so if X bounds the pair window b(q)+b(q−1) and Y the single values below "
                    + "ell^m, then below ell^(m+1) the pair window is at most X+Y and the single "
                    + "values at most X. These Fibonacci envelopes give b(n)≤2·b(0)·φ^m for "
                    + "n<ell^(m+1), so log b(t)/log n≤log_ell φ+log(2·b(0))/log n whenever t≤n. "
                    + "Along quotients whose last digits alternate 0, 1 the pair window v(k) "
                    + "satisfies v(k+2)=v(k+1)+v(k) exactly, so φ·v(k)≥φ^k, and the readouts at "
                    + "n=ell·q(k) and at n=ell·q(k)+1 are at least log_ell φ·(k−1)/(k+2). A common "
                    + "squeeze of the infimum of tail suprema then gives log_ell φ in both "
                    + "conventions."))),
                DescribeRole.Theorem))));
}
