using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.GoldenEuler;

internal sealed class GoldenLocalEulerTrichotomyDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/PrimeForms/GoldenEuler/GoldenLocalEulerTrichotomy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The neutral and quadratic charge denominator specializes to split, inert, and ramified golden local Euler forms.",
        H("Golden Local Euler Trichotomy"),
        Blocks(
            Theorem("split-local-denominator", "split_local_denominator",
                "Split Charge Gives a Squared Linear Denominator", SplitLocalDenominatorFormula(),
                "Substituting charge plus one makes both linear denominator factors equal, yielding the square of one minus X.",
                "The equality is polynomial and remains independent of any convergence interpretation of X."),
            Theorem("inert-local-denominator", "inert_local_denominator",
                "Inert Charge Gives a Quadratic Denominator", InertLocalDenominatorFormula(),
                "Substituting charge minus one multiplies one minus X by one plus X, giving one minus X squared.",
                "This algebraic factor fusion does not assert that X is a prime monomial."),
            Theorem("ramified-local-denominator", "ramified_local_denominator",
                "Ramified Charge Leaves One Linear Denominator", RamifiedLocalDenominatorFormula(),
                "At zero charge the quadratic-channel factor is one, leaving the neutral factor one minus X.",
                "The statement records the ramified specialization only at the level of the totalized real denominator."),
            Theorem("split-local-factor", "split_local_factor",
                "The Split Local Factor Is the Inverse Squared Denominator", SplitLocalFactorFormula(),
                "The totalized split local factor is the reciprocal of the squared linear denominator.",
                "Because inversion is totalized over the reals, no nonvanishing premise is claimed or required."),
            Theorem("inert-local-factor", "inert_local_factor",
                "The Inert Local Factor Is the Inverse Quadratic Denominator", InertLocalFactorFormula(),
                "The totalized inert local factor is the reciprocal of one minus X squared.",
                "The equality specializes the definition and makes no analytic assertion about an Euler product."),
            Theorem("ramified-local-factor", "ramified_local_factor",
                "The Ramified Local Factor Is the Inverse Linear Denominator", RamifiedLocalFactorFormula(),
                "The totalized ramified local factor is the reciprocal of one minus X.",
                "This completes the three charge specializations without adding a prime-classification claim."))));

    private static DocumentBlock.Describe Theorem(string id, string declaration,
        string heading, Formula formula, string firstParagraph, string secondParagraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(firstParagraph)), Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);

    private static Formula SplitLocalDenominatorFormula() => DenominatorFormula(
        D(1), Pow(OneMinus(F.Id("X")), D(2)));

    private static Formula InertLocalDenominatorFormula() => DenominatorFormula(
        NegativeOne(), OneMinus(Pow(F.Id("X"), D(2))));

    private static Formula RamifiedLocalDenominatorFormula() => DenominatorFormula(
        D(0), OneMinus(F.Id("X")));

    private static Formula SplitLocalFactorFormula() => FactorFormula(
        D(1), Inverse(Pow(OneMinus(F.Id("X")), D(2))));

    private static Formula InertLocalFactorFormula() => FactorFormula(
        NegativeOne(), Inverse(OneMinus(Pow(F.Id("X"), D(2)))));

    private static Formula RamifiedLocalFactorFormula() => FactorFormula(
        D(0), Inverse(OneMinus(F.Id("X"))));

    private static Formula DenominatorFormula(Formula charge, Formula result)
    {
        Formula x = F.Id("X");
        return Statement([Typed(x, Reals())], Seq(
            Call("goldenLocalDenominator", charge, x), Sp, Eq, Sp, result));
    }

    private static Formula FactorFormula(Formula charge, Formula result)
    {
        Formula x = F.Id("X");
        return Statement([Typed(x, Reals())], Seq(
            Call("goldenLocalFactor", charge, x), Sp, Eq, Sp, result));
    }

    private static Formula Statement(Formula[] binders, Formula conclusion)
    {
        List<Formula> items = [];
        if (binders.Length > 0)
        {
            items.Add(Forall); items.Add(Sp);
            for (int index = 0; index < binders.Length; index++)
            {
                if (index > 0) { items.Add(Comma); items.Add(Sp); }
                items.Add(binders[index]);
            }
            items.Add(Comma); items.Add(RowBreak); items.Add(Grp());
        }
        items.Add(Seq(Open, conclusion, Close)); items.Add(Dot);
        return Disp(Seq([.. items]));
    }

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula NegativeOne() => Seq(Minus, D(1));
    private static Formula OneMinus(Formula value) => Seq(D(1), Sp, Minus, Sp, value);
    private static Formula Pow(Formula value, Formula exponent) => Seq(Grp(value), Caret, Grp(exponent));
    private static Formula Inverse(Formula value) => Seq(Grp(value), Caret, Grp(Minus, D(1)));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
}
