using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CyclicGrowingCoupledFitDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/CyclicGrowingCoupledFit";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A growing front window and a fixed rear window admit an invertible joint moment fit.",
        H("Coupled cyclic moment matrices"),
        Blocks(
            Paragraph(Text(
                "Let n run through the natural numbers and fix a finite set S of real rear offsets r. " +
                "At mesh h use u=nh. On the integer front window from −n to n, use x=j/n, " +
                "F=(1+cos(xu))/2, X=sin²(xu)/u², and W=1−F. At u=0, X=x². " +
                "At each rear offset r put W=(1+cos(rh))/2, F=1−W, and X=r² sinc²(rh)/n². " +
                "For positive n and nonzero h the rear feature is sin²(rh)/(nh)². " +
                "The coefficient row is (F/n,X/n,W/n³) and the moment row is (F,X,n³W²). " +
                "The coupled matrix M is the sum of the outer products of the moment and coefficient rows, " +
                "over both windows, for positive n. Assume n³(nh)⁴→0. Since n≥1 eventually, this implies nh→0 and h→0.")),
            Describe.Lean(DescribeId.Create("coupled-moment-limit"),
                DeclarationHandle.Create(Owner + ".coupledMatrix_tendsto"),
                H("Limit of the three scaled moment rows"),
                StatementSource.FromAuthor(Limit()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The upper left front block converges to the two-feature lattice matrix. " +
                    "On the front, W≤u²/4 and F,X∈[0,1]. Hence the mixed upper column is " +
                    "bounded by 3u²/(4n²), the mixed lower row by 3n³u⁴/16, " +
                    "and the final entry by 3nu⁶/64. Each tends to zero. At a fixed rear offset, " +
                    "the scaled moment r² sinc²(rh) tends to r² and W tends to one. " +
                    "Since n²F≤r²(nh)²/4, the rear contribution to the first column also vanishes."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eventual-coupled-fit"),
                DeclarationHandle.Create(Owner + ".coupledFit_eventually"),
                H("Eventual unique fit to arbitrary three moments"),
                StatementSource.FromAuthor(Fit()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Suppose additionally that S is nonempty and b(n) is any sequence of real three-vectors. " +
                    "For a coefficient vector a the readout Q(n,a) is the sum, over both windows, " +
                    "of the moment row multiplied by the dot product of the coefficient row with a. " +
                    "The limiting matrix has determinant 16|S|/45, which is positive. " +
                    "Continuity of the determinant makes the finite matrices invertible eventually. " +
                    "For positive n the readout is exactly M(n)a, so inverse multiplication supplies " +
                    "the unique coefficient vector for each prescribed moment target. " +
                    "The coefficient fit permits signed weights. Positivity on the proposed cyclic support " +
                    "requires additional boundary estimates."))),
                DescribeRole.Theorem))));

    private static Formula Limit()
    {
        var n = F.Id("n");
        var s = F.Id("S");
        var matrix = Call("MatrixThree", F.D(2), new Formula.Fraction(F.D(2), F.D(3)), F.D(0),
            new Formula.Fraction(F.D(2), F.D(3)), new Formula.Fraction(F.D(2), F.D(5)), F.D(0),
            F.D(0), Call("RearSquareSum", s), Call("Card", s));
        return F.Disp(Eq(Call("Limit", Call("M", s, n, Call("h", n))), matrix));
    }

    private static Formula Fit()
    {
        var n = F.Id("n");
        var a = F.Id("a");
        return F.Disp(Call("EventuallyUnique", n, a, Eq(Call("Q", n, a), Call("b", n))));
    }

    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
}
