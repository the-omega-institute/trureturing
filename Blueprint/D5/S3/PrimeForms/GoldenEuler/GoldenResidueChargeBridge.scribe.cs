using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.GoldenEuler;

internal sealed class GoldenResidueChargeBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/PrimeForms/GoldenEuler/GoldenResidueChargeBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Residues modulo five select the split, inert, and ramified charge values used by the golden local Euler factor.",
        H("Golden Residue Charge Bridge"),
        Blocks(
            Theorem("golden-residue-charge-split", "golden_residue_charge_split",
                "Split Residues Have Positive Charge", GoldenResidueChargeSplitFormula(),
                "A natural number congruent to one or four modulo five is assigned golden residue charge plus one.",
                "The theorem translates the stated residue premise only; primality and splitting are not inferred here."),
            Theorem("golden-residue-charge-inert", "golden_residue_charge_inert",
                "Inert Residues Have Negative Charge", GoldenResidueChargeInertFormula(),
                "A natural number congruent to two or three modulo five is assigned golden residue charge minus one.",
                "The disjunctive residue hypothesis remains explicit, and no converse classification is asserted."),
            Theorem("golden-residue-charge-five", "golden_residue_charge_five",
                "Five Has Zero Golden Residue Charge", GoldenResidueChargeFiveFormula(),
                "The natural number five falls outside the split and inert residue branches and therefore receives charge zero.",
                "This evaluates the distinguished ramified input without generalizing to every multiple of five."),
            Theorem("split-residue-local-denominator", "split_residue_local_denominator",
                "Split Residues Select the Squared Denominator", SplitResidueLocalDenominatorFormula(),
                "Under the split residue premise, the charge bridge feeds plus one into the local denominator and yields the squared linear form.",
                "The conclusion is algebraic in the real variable X and does not assert convergence of a local or global Euler product."),
            Theorem("inert-residue-local-denominator", "inert_residue_local_denominator",
                "Inert Residues Select the Quadratic Denominator", InertResidueLocalDenominatorFormula(),
                "Under the inert residue premise, the bridge feeds minus one into the local denominator and yields one minus X squared.",
                "Only the supplied residue class is used; the statement adds no independent prime-splitting theorem."),
            Theorem("ramified-five-local-denominator", "ramified_five_local_denominator",
                "Five Selects the Ramified Linear Denominator", RamifiedFiveLocalDenominatorFormula(),
                "The zero charge assigned to five removes the nontrivial charge factor and leaves one minus X.",
                "This is the single ramified specialization at five and remains a totalized real polynomial identity."))));

    private static DocumentBlock.Describe Theorem(string id, string declaration,
        string heading, Formula formula, string firstParagraph, string secondParagraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(firstParagraph)), Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);

    private static Formula GoldenResidueChargeSplitFormula()
    {
        Formula p = F.Id("p");
        return Statement([Typed(p, Naturals())], [SplitPremise(p)],
            Seq(Call("goldenResidueCharge", p), Sp, Eq, Sp, D(1)));
    }

    private static Formula GoldenResidueChargeInertFormula()
    {
        Formula p = F.Id("p");
        return Statement([Typed(p, Naturals())], [InertPremise(p)],
            Seq(Call("goldenResidueCharge", p), Sp, Eq, Sp, Minus, D(1)));
    }

    private static Formula GoldenResidueChargeFiveFormula() =>
        Statement([], [], Seq(Call("goldenResidueCharge", D(5)), Sp, Eq, Sp, D(0)));

    private static Formula SplitResidueLocalDenominatorFormula() =>
        ResidueDenominatorFormula(true, Pow(OneMinus(F.Id("X")), D(2)));

    private static Formula InertResidueLocalDenominatorFormula() =>
        ResidueDenominatorFormula(false, OneMinus(Pow(F.Id("X"), D(2))));

    private static Formula RamifiedFiveLocalDenominatorFormula()
    {
        Formula x = F.Id("X");
        return Statement([Typed(x, Reals())], [], Seq(
            Call("goldenLocalDenominator", Call("goldenResidueCharge", D(5)), x),
            Sp, Eq, Sp, OneMinus(x)));
    }

    private static Formula ResidueDenominatorFormula(bool split, Formula result)
    {
        Formula p = F.Id("p"); Formula x = F.Id("X");
        Formula premise = split ? SplitPremise(p) : InertPremise(p);
        return Statement([Typed(p, Naturals()), Typed(x, Reals())], [premise], Seq(
            Call("goldenLocalDenominator", Call("goldenResidueCharge", p), x),
            Sp, Eq, Sp, result));
    }

    private static Formula SplitPremise(Formula p) => Disjunction(
        ResidueEquality(p, D(1)), ResidueEquality(p, D(4)));

    private static Formula InertPremise(Formula p) => Disjunction(
        ResidueEquality(p, D(2)), ResidueEquality(p, D(3)));

    private static Formula ResidueEquality(Formula p, Formula residue) =>
        Seq(Call("mod", p, D(5)), Sp, Eq, Sp, residue);

    private static Formula Disjunction(Formula left, Formula right) =>
        Seq(Open, left, Close, Sp, Lor, Sp, Open, right, Close);

    private static Formula Statement(Formula[] binders, Formula[] hypotheses, Formula conclusion)
    {
        List<Formula> items = [];
        if (binders.Length > 0)
        {
            items.Add(Forall); items.Add(Sp); AddSeparated(items, binders, Comma);
            items.Add(Comma); items.Add(RowBreak); items.Add(Grp());
        }
        if (hypotheses.Length > 0)
        {
            AddSeparated(items, hypotheses.Select(h => Seq(Open, h, Close)).ToArray(), Land);
            items.Add(Sp); items.Add(Rightarrow); items.Add(RowBreak); items.Add(Grp());
        }
        items.Add(Seq(Open, conclusion, Close)); items.Add(Dot);
        return Disp(Seq([.. items]));
    }

    private static void AddSeparated(List<Formula> items, Formula[] values, Formula separator)
    {
        for (int index = 0; index < values.Length; index++)
        {
            if (index > 0) { items.Add(Sp); items.Add(separator); items.Add(Sp); }
            items.Add(values[index]);
        }
    }

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula OneMinus(Formula value) => Seq(D(1), Sp, Minus, Sp, value);
    private static Formula Pow(Formula value, Formula exponent) => Seq(Grp(value), Caret, Grp(exponent));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
