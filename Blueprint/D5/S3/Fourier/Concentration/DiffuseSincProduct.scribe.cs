using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class DiffuseSincProductDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/DiffuseSincProduct";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A reciprocal quadratic controls the finite sinc product under a dispersion condition.",
        H("Euclidean-Scale Bound for Diffuse Sinc Products"),
        Blocks(
            Paragraph(Text(
                "Let A be a finite index set and c a family of real coefficients. Write "
                + "S for the sum of the squares of c(j) over A, and suppose c(j)²≤S/2 "
                + "for each j in A. Here sinc(x)=sin(x)/x for nonzero x and sinc(0)=1.")),
            Describe.Lean(
                DescribeId.Create("diffuse-sinc-product-le"),
                DeclarationHandle.Create(Owner + ".diffuse_sinc_product_le"),
                H("Reciprocal quadratic envelope"),
                StatementSource.FromAuthor(Bound()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The scalar bound is sinc(x)²(1+x²/12)≤1. On 0≤x≤2, integrate "
                        + "cos(t)≤1−t²/8 to get sinc(x)≤1−x²/24. If a=x²/24, then "
                        + "(1−a)²(1+2a)=1−a²(3−2a)≤1. For x≥2, use |sin(x)|≤1 "
                        + "and 1+x²/12≤x². Evenness extends the bound to all real x.")),
                    Paragraph(Text(
                        "Set b(j)=(c(j)t)²/12 and U equal to their sum. The product of 1+b(j) "
                        + "dominates 1+U+(U²−Σb(j)²)/2 by multiplying out the nonnegative "
                        + "terms. The diffuse hypothesis implies Σb(j)²≤U²/2. The lower "
                        + "bound is therefore at least (1+U/2)². Combine this with "
                        + "the scalar estimate multiplied over A and take the nonnegative "
                        + "square root.")),
                    Paragraph(Text(
                        "The formula includes vanishing coefficients and an empty index set. "
                        + "For S>0 its right side is integrable on the real line with integral "
                        + "π√(24/S). This is the characteristic function envelope for an "
                        + "independent uniform perturbation. Using it for interval probabilities "
                        + "requires a separate estimate passing from the characteristic function "
                        + "to the measure of a short interval."))),
                DescribeRole.Theorem))));

    private static Formula Bound()
    {
        var j = F.Id("j");
        var t = F.Id("t");
        var c = new Formula.FunctionCall(FormulaIdentifier.Create("c"), [j]);
        var sinc = Seq(Operatorname, Grp(F.Id("sinc")), Open, c, t, Close);
        var product = Seq(new Formula.Subscript(Prod, Seq(j, Sp, InMacro, Sp, F.Id("A"))),
            new Formula.Absolute(sinc));
        var quadratic = new Formula.Fraction(Seq(F.Id("S"), new Formula.Power(t, D(2))), D(2, 4));
        var envelope = new Formula.Fraction(D(1), Add(D(1), quadratic));
        return Disp(new Formula.Relation(product, FormulaRelationOperator.LessThanOrEqual, envelope));
    }
}
