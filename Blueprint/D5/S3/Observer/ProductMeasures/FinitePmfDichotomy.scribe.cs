using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProductMeasures;

internal sealed class FinitePmfDichotomyDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ProductMeasures/FinitePmfDichotomy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Locally equivalent finite coordinate laws satisfy Kakutani's dichotomy.",
        H("Kakutani Dichotomy for Finite PMF Products"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-pmf-kakutani-dichotomy"),
                DeclarationHandle.Create(Prefix + "finite_pmf_kakutani_dichotomy"),
                H("Energy summability exactly separates the two product-law regimes"),
                StatementSource.FromAuthor(DichotomyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Coordinatewise mutual absolute continuity makes the finite likelihood "
                            + "ratios well behaved. Summable squared Hellinger energy yields "
                            + "mutual absolute continuity of the countable product laws.")),
                    Paragraph(Text(
                        "When the real-valued energy sequence is not summable, a geometric "
                            + "subsequence of prefix affinities and Borel--Cantelli produce a "
                            + "measurable separating event, so the product laws are singular."))),
                DescribeRole.Theorem))));

    private static Formula DichotomyFormula()
    {
        Formula p = Call("productLaw", F.Id("p"));
        Formula q = Call("productLaw", F.Id("q"));
        Formula energy = Call("energySequence", F.Id("p"), F.Id("q"));
        Formula singular = Call("MutuallySingular", p, q);
        Formula equivalent = Call("MutuallyAbsolutelyContinuous", p, q);
        Formula divergent = Seq(Neg, Sp, Call("Summable", energy));
        Formula summable = Call("Summable", energy);
        return Disp(And(
            new Formula.Logic(singular, FormulaLogicOperator.Iff, divergent),
            new Formula.Logic(equivalent, FormulaLogicOperator.Iff, summable)));
    }

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
