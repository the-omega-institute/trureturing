using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class AggregateCosineBalanceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/AggregateCosineBalance";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One cutoff can separate the first two real cosine moments on every cycle of size at least seven.",
        H("Failure of a shared cosine cutoff"),
        Blocks(
            Paragraph(Text(
                "For a modulus q, use the residues k from 0 to q−1. "
                + "Let c(k) = cos(2πk/q) and d(k) = cos(4πk/q). All sums run over these residues.")),
            Describe.Lean(
                DescribeId.Create("aggregate-cosine-imbalance"),
                DeclarationHandle.Create(Owner + ".aggregate_cosine_imbalance"),
                H("The signed squared readout and the zero cutoff"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The Fourier expansion of (c−d)(c+d)² has frequencies between −6 and 6. "
                        + "The only constant contribution comes from c²d, where the terms 1+1−2 "
                        + "and −1−1+2 each contribute 1/8. Every nonconstant term sums to zero "
                        + "by character orthogonality when q ≥ 7.")),
                    Paragraph(Text(
                        "The double-angle identity gives c+d = (2c−1)(c+1) and "
                        + "c−d = (1−c)(2c+1). A residue with c+d > 0 has c > 1/2, "
                        + "so every term in the clipped sum is nonnegative. At k=1 the angle "
                        + "lies strictly between zero and π/3, which makes this term positive.")),
                    Paragraph(Text(
                        "Normalizing the positive part of c+d gives a probability weight "
                        + "because its value at k=0 is two. The clipped sum then shows that "
                        + "the first moment is strictly larger than the second."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var q = F.Id("q");
        var k = F.Id("k");
        var c = Call("c", k);
        var d = Call("d", k);
        var sum = new Formula.Subscript(Sum, k);
        var aggregate = Seq(Open, c, Plus, d, Close);
        var delta = Seq(Open, c, Minus, d, Close);
        var positivePart = Call("max", Seq(D(0), Comma, Sp, c, Plus, d));
        return Disp(new Formula.Aligned([
            Seq(Amp, Forall, Sp, q, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")),
                Comma, Quad, Sp, q, Sp, Ge, Sp, D(7), Colon),
            Seq(Amp, sum, delta, new Formula.Power(aggregate, D(2)), Eq,
                Frac, Grp(q), Grp(D(4)), Comma),
            Seq(Amp, D(0), Lt, sum, delta, positivePart, Dot)
        ]));
    }
}
