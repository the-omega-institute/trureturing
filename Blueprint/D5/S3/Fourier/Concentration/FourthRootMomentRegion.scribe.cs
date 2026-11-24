using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class FourthRootMomentRegionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/FourthRootMomentRegion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two squared Fourier magnitudes of a probability weight on the cyclic group of order four have an exact joint range.",
        H("Joint Fourier Moments on the Cyclic Group of Order Four"),
        Blocks(
            Paragraph(Text(
                "A probability weight w on the cyclic group of order four assigns nonnegative "
                + "real masses summing to one to the four residues. Use the unnormalized discrete "
                + "Fourier transform. A pair (u,v) is attainable if a common weight has squared "
                + "Fourier magnitudes u at frequency one and v at frequency two.")),
            Describe.Lean(
                DescribeId.Create("dft-four-squared-region"),
                DeclarationHandle.Create(Owner + ".dft_four_squared_region"),
                H("The exact joint range of the first two squared magnitudes"),
                StatementSource.FromAuthor(JointRange()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If e and o are the even and odd masses, the squared second magnitude is "
                    + "(e−o) squared. The two signed differences of masses within each parity "
                    + "can independently fill [−e,e] and [−o,o]. Their squared sum is at most "
                    + "e squared plus o squared, which is (1+v)/2. To attain any allowed pair, "
                    + "take e=(1+sqrt(v))/2 and o=(1−sqrt(v))/2. Vary both signed differences "
                    + "by the same fraction of their endpoint values."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Fix a natural number p at least two. For a real weight w of total mass one, "
                + "write M(w) for the vector of Fourier coefficients at 0, 1, 2 and 3 of the "
                + "singleton cyclic collision masses of the degree-p lattice sums. The lattice coordinate "
                + "is its representative in {0,1,2,3}. With nonnegative w these masses form "
                + "the law of the difference between two independent p-fold sums. Let A be the "
                + "maximum coefficient at frequency one among probability weights with coefficient "
                + "zero at frequency two. Let B be the maximum "
                + "nonnegative first coefficient among probability laws with Fourier "
                + "coefficient vector (1,B,0,B).")),
            Describe.Lean(
                DescribeId.Create("four-first-moment-maxima"),
                DeclarationHandle.Create(Owner + ".four_first_moment_maxima"),
                H("Different attained maxima for the powered moments and their relaxation"),
                StatementSource.FromAuthor(Maxima()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The singleton cyclic collision formula and Fourier inversion recover each "
                    + "coefficient from the same weight. The first and third Fourier magnitudes "
                    + "agree because the weights are real. At v=0 the preceding interval ends "
                    + "at one half. Taking the p-th power gives the first attained maximum. "
                    + "In the relaxation, the vanishing second coefficient makes both parity "
                    + "masses one half. A real first coefficient forces the masses at one and three "
                    + "to agree, and the coefficient equals the difference of the masses at zero and two. The "
                    + "weight (1/2,1/4,0,1/4) attains one half."))),
                DescribeRole.Theorem))));

    private static Formula JointRange()
    {
        var u = F.Id("u");
        var v = F.Id("v");
        var condition = new Formula.FunctionCall(FormulaIdentifier.Create("Attainable"), [u, v]);
        var vRange = Seq(D(0), Sp, Leq, Sp, v, Sp, Leq, Sp, D(1));
        var uRange = Seq(D(0), Sp, Leq, Sp, u, Sp, Leq, Sp, new Formula.Fraction(Add(D(1), v), D(2)));
        return Disp(Seq(condition, Sp, Iff, Sp, new Formula.Logic(vRange, FormulaLogicOperator.And, uRange)));
    }

    private static Formula Maxima()
    {
        var p = F.Id("p");
        var half = new Formula.Fraction(D(1), D(2));
        var trueMaximum = new Formula.Power(Seq(Open, half, Close), p);
        var first = new Formula.Power(F.Id("u"), p);
        var second = new Formula.Power(F.Id("v"), p);
        var coefficients = new Formula.FunctionCall(FormulaIdentifier.Create("M"), [F.Id("w")]);
        var values = Seq(Open, D(1), Comma, Sp, first, Comma, Sp, second, Comma, Sp, first, Close);
        var attained = Seq(F.Id("A"), Sp, Eq, Sp, trueMaximum, Sp, Lt, Sp, half, Sp, Eq, Sp, F.Id("B"));
        return Disp(new Formula.Logic(Seq(coefficients, Sp, Eq, Sp, values), FormulaLogicOperator.And, attained));
    }
}
