using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class CenteredDisjointCharacterBoundDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/CenteredDisjointCharacterBound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Centering the local exponential difference preserves the signed phase sum and a quadratic penalty.",
        H("Centered disjoint coefficient bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("centered-overlap-bound"),
            DeclarationHandle.Create(Owner + ".centered_overlap_bound"),
            H("Quadratic exponential majorant"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For any finite subset T, complex phases a(j), complex c and natural "
                    + "degree d, put k=|T|, u=c−(sum of a(j) over T)/2 and v=(sum of |a(j)|² over T)/24. "
                    + "Write C(T) for the degree-d coefficient of exp(cx) times the product over T "
                    + "of exp(−a(j)x)−1. If d<k this coefficient vanishes. Otherwise put n=d−k and "
                    + "use the displayed finite sum over m from 0 to the floor of n/2.")),
                Paragraph(Text("The local centered identity expresses the exponential difference as "
                    + "−a(j)x exp(−a(j)x/2) multiplied by an even series. Its degree-2m coefficient "
                    + "is (a(j)/2)^(2m)/(2m+1)!, also when a(j)=0. The established factorial inequality "
                    + "6^m m! ≤ (2m+1)! bounds its modulus by (|a(j)|²/24)^m/m!; odd coefficients are zero.")),
                Paragraph(Text("Extracting the k linear factors and combining the complex exponentials yields "
                    + "exp(ux). The Cauchy product propagates the coefficientwise domination, so the even "
                    + "factors are majorized by the coefficients of exp(v x²). Their product with the "
                    + "majorant exp(|u|x) gives the finite sum after reindexing the even powers. The bound "
                    + "retains the complex center u for each subset and the total squared local phase norms.")),
                Paragraph(Text("This estimate can replace the earlier degree-sensitive overlap bound in the "
                    + "signed parity remainder. Estimating the resulting sums over subsets and characters "
                    + "at the resolution of actual zeta-zero near-collisions remains a separate arithmetic problem."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var t = F.Id("T");
        var j = F.Id("j");
        var k = F.Id("k");
        var d = F.Id("d");
        var n = F.Id("n");
        var m = F.Id("m");
        var c = Call("C", t);
        var r = Seq(n, Minus, D(2), m);
        var product = new Formula.Subscript(Prod, Seq(j, Sp, InMacro, Sp, t));
        var sum = new Formula.Subscript(Sum, Seq(D(0), Sp, Le, Sp, m, Sp, Le, Sp,
            Call("floor", Seq(n, Slash, D(2)))));
        return Disp(new Formula.Aligned([
            Seq(Amp, d, Lt, k, Implies, c, Eq, D(0)),
            Seq(Amp, d, Sp, Ge, Sp, k, Implies, Bar, c, Bar, Sp, Le, Sp, product,
                Bar, Call("a", j), Bar, sum, Frac,
                Grp(new Formula.Power(Seq(Bar, F.Id("u"), Bar), r), new Formula.Power(F.Id("v"), m)),
                Grp(Open, r, Close, Bang, m, Bang))]));
    }
}
