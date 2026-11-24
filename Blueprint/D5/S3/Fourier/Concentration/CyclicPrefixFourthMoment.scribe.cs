using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class CyclicPrefixFourthMomentDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/CyclicPrefixFourthMoment";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact fourth moment of a cyclic prefix character sum includes the contribution of wrapped differences.",
        H("The fourth moment of a cyclic prefix"),
        Blocks(Describe.Lean(
            DescribeId.Create("cyclic-prefix-fourth-moment"),
            DeclarationHandle.Create(Owner + ".sum_prefixCharacter_norm_four"),
            H("Exact fourth moment of the prefix character sum"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Write B_N(k) for the character sum at the first N natural-number indices. "
                    + "The residue difference r of an ordered pair has representative 0 ≤ r < q. "
                    + "Its possible integer differences are r and r−q. They occur with counts "
                    + "(N−r)_+ and (N−(q−r))_+, respectively. Positive parts truncate at zero.")),
                Paragraph(Text(
                    "The Fourier transform of the pair count is the squared norm of B_N(k). "
                    + "Fourier inversion identifies the sum of its squared norms with q times "
                    + "the sum of squared pair counts. The two individual squares sum to "
                    + "N(2N²+1)/3. Both counts are positive on q−N+1 ≤ r < N, an interval "
                    + "of length m. The cross term there is twice the sum of j(m+1−j) for "
                    + "1 ≤ j ≤ m, giving the cubic correction after multiplication by three.")),
                Paragraph(Text(
                    "For N > 0, dividing by q²N² gives the squared mass of the normalized "
                    + "Fourier weights |B_N(k)|²/(qN). Cauchy–Schwarz then bounds the mass "
                    + "of any exceptional set using its cardinality and that squared mass."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var q = F.Id("q");
        var n = F.Id("N");
        var k = F.Id("k");
        var m = F.Id("m");
        var naturals = Seq(Mathbb, Grp(F.Id("N")));
        var residues = Seq(Mathbb, Grp(F.Id("Z")), Slash, q, Mathbb, Grp(F.Id("Z")));
        var window = new Formula.Apply(new Formula.Subscript(F.Id("B"), n), [k]);
        var correction = new Formula.Subscript(Seq(Open, D(2), n, Minus, q, Minus, D(1), Close), Plus);
        return Disp(new Formula.Aligned([
            Seq(Amp, Forall, Sp, q, Comma, n, Colon, naturals, Comma, Quad,
                q, Gt, D(0), Comma, Quad, n, Le, q, Comma, Quad, m, Eq, correction, Comma),
            Seq(Amp, D(3), new Formula.Subscript(Sum, Seq(k, InMacro, residues)), Sp,
                new Formula.Power(Seq(Bar, window, Bar), D(4)), Sp, Eq, Sp,
                q, Open, n, Open, D(2), new Formula.Power(n, D(2)), Plus, D(1), Close, Plus,
                m, Open, m, Plus, D(1), Close, Open, m, Plus, D(2), Close, Close, Dot)
        ]));
    }
}
