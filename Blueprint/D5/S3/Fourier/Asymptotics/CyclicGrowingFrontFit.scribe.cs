using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CyclicGrowingFrontFitDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/CyclicGrowingFrontFit";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The front moment matrix admits a uniform mesh error and an exact lattice reference solution.",
        H("Moment matrices on growing cyclic windows"),
        Blocks(
            Describe.Lean(DescribeId.Create("uniform-front-gram-error"),
                DeclarationHandle.Create(Owner + ".frontGram_sub_le"),
                H("Uniform error in each matrix entry"),
                StatementSource.FromAuthor(Error()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On the integer window from −n to n, use x=j/n and the scaled mesh u. " +
                    "The two features are (1+cos(xu))/2 and sin²(xu)/u². At u=0 they are 1 and x². " +
                    "The matrix G sums their pair products and divides by n. Both features lie in [0,1]. " +
                    "The cubic sine remainder bounds the error in the second feature by u²/3, " +
                    "uniformly in the window. The first feature has error at most u²/4. " +
                    "The product difference and the exact cardinality 2n+1 give the entrywise bound."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("growing-front-gram-limit"),
                DeclarationHandle.Create(Owner + ".frontGram_tendsto"),
                H("Limit along any vanishing scaled mesh"),
                StatementSource.FromAuthor(Limit()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At zero mesh the normalized sums of 1, x², and x⁴ give the three matrix entries. " +
                    "The uniform bound makes the difference tend to zero for every real sequence u tending to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("growing-front-reference-fit"),
                DeclarationHandle.Create(Owner + ".frontGram_reference_fit"),
                H("The reference fit at the interior lattice budget"),
                StatementSource.FromAuthor(Fit()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each positive integer n, put m=n(n+1)/5 and t=n(n+1)−1/2. " +
                    "The normalizer Z is the sum of t−j² over the window. The stated matrix equation " +
                    "certifies mass one and normalized second moment m/n² for the lattice parabola. " +
                    "Using the exact finite reference retains the boundary margin lost in the limiting parabola."))),
                DescribeRole.Theorem))));

    private static Formula Error()
    {
        var n = F.Id("n");
        var u = F.Id("u");
        var i = F.Id("i");
        var j = F.Id("j");
        var error = Call("Abs", Subtract(Call("G", n, u, i, j), Call("G", n, F.D(0), i, j)));
        return F.Disp(F.Seq(Lt(F.D(0), n), F.Comma, F.Sp,
            Le(error, Multiply(F.D(2), Sq(u)))));
    }

    private static Formula Limit()
    {
        var n = F.Id("n");
        var u = F.Id("u");
        var mesh = Call("u", n);
        var limit = Call("SymmetricTwoByTwo", F.D(2), new Formula.Fraction(F.D(2), F.D(3)),
            new Formula.Fraction(F.D(2), F.D(5)));
        return F.Disp(new Formula.Logic(Eq(Call("Limit", mesh), F.D(0)),
            FormulaLogicOperator.Implies, Eq(Call("Limit", Call("G", n, mesh)), limit)));
    }

    private static Formula Fit()
    {
        var n = F.Id("n");
        var t = F.Id("t");
        var m = F.Id("m");
        var z = F.Id("Z");
        var reference = Call("Column", new Formula.Fraction(Multiply(n, t), z),
            new Formula.Fraction(Subtract(F.D(0), new Formula.Power(n, F.D(3))), z));
        return F.Disp(F.Seq(Lt(F.D(0), n), F.Comma, F.Sp,
            Eq(Multiply(Call("G", n, F.D(0)), reference),
                Call("Column", F.D(1), new Formula.Fraction(m, Sq(n))))));
    }

    private static Formula Sq(Formula a) => new Formula.Power(a, F.D(2));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
}
