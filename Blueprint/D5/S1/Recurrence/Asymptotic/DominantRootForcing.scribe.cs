using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Asymptotic;

internal sealed class DominantRootForcingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Asymptotic/DominantRootForcing.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026a400645siblings");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A forced linear recurrence whose characteristic polynomial has a simple dominant real "
            + "root R has solutions L R^j + O(q^j), and L R^j + O(R^(j/2)) under square-root "
            + "forcing.",
        H("Dominant-root forcing for linear recurrences"),
        Blocks(
            Describe.Lean(DescribeId.Create("dominant-root-forcing"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Dominant-root forcing"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let P be a real polynomial with a simple root R, and let real sequences "
                        + "b and e satisfy the sum over k from 0 to deg P of P_k b_(j+k) = e_j "
                        + "for every j. (1) If 0 < q < R, every other complex root of P has "
                        + "modulus below q, and e = O(q^j), then b_j = L R^j + O(q^j) for some "
                        + "real L. (2) If R > 1, every other complex root of P has modulus below "
                        + "√R, b_j ~ L R^j for a real L, and e_j = O(√b_j), then "
                        + "b_j = L R^j + O(R^(j/2)).")),
                    Paragraph(Text(
                        "Proof. Write S for the shift of complex sequences, so the recurrence "
                        + "reads P(S) b = e. Factor P = (X − R) Q over ℝ; Q(R) ≠ 0 since R is "
                        + "simple, and Q splits over ℂ into factors X − z with |z| < q. "
                        + "Put d = Q(S) b, so that d_(j+1) − R d_j = e_j. The series of "
                        + "e_i / R^(i+1) converges geometrically because q < R, and "
                        + "d_j = R^j (d_0 + the partial sum) differs from L' R^j, with L' the "
                        + "full sum, by R^j times a tail of size O((q/R)^j); hence "
                        + "d = L' R^j + O(q^j). Then c = b − (L'/Q(R)) R^j satisfies "
                        + "Q(S) c = d − L' R^j = O(q^j). A factor S − z with |z| < q gives "
                        + "|u_(j+1)| ≤ |z| |u_j| + C q^j, and induction yields "
                        + "|u_j| ≤ M q^j with M = max(|u_0|, C/(q − |z|)); peeling the roots of "
                        + "Q one by one gives c = O(q^j). Taking real parts gives (1) with "
                        + "L = Re(L'/Q(R)).")),
                    Paragraph(Text(
                        "For (2), b ~ L R^j gives b = O(R^j), hence √b = O(R^(j/2)) and "
                        + "e = O(R^(j/2)). Part (1) with q = √R, which lies strictly between 0 "
                        + "and R because R > 1, gives b = L' R^j + O(R^(j/2)) for some L'. "
                        + "Dividing by R^j, b_j/R^j tends to L' and also to L, since "
                        + "b − L R^j = o(R^j); so L' = L.")),
                    Paragraph(Text(
                        "This is Lemma 2 in Section 4 of H. Ma and W. Zhang's note on OEIS "
                        + "A400645 (DOI 10.5281/zenodo.24369110), which assumes P monic with "
                        + "distinct roots, the other roots of modulus at most one, q > 1 and "
                        + "L > 0. Here P need not be monic, only R must be simple, roots of "
                        + "modulus in [1, q) are allowed, q may be at most one, and L may have "
                        + "any sign. Simplicity of R cannot be dropped: P = (X − 2)^2 and "
                        + "e = 0 admit b_j = j 2^j, which is not 2^j L + O(q^j) for any "
                        + "q < 2. The modulus bound is also needed: for P = (X − 3)(X − 2) "
                        + "and q = 3/2, b_j = 2^j solves the homogeneous recurrence and is not "
                        + "L 3^j + O((3/2)^j). Other roots of modulus exactly q are excluded: "
                        + "a double root z there gives the solution j z^j, which is not "
                        + "O(q^j)."))),
                DescribeRole.Theorem))));
}
