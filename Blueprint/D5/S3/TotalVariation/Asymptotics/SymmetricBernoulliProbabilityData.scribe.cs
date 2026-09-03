using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation.Asymptotics;

internal sealed class SymmetricBernoulliProbabilityDataDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliProbabilityData.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The symmetric Bernoulli bias laws have unit mass at every real bias and are "
            + "nonnegative on the closed probability range.",
        H("Symmetric Bernoulli Probability Data"),
        Blocks(
            Paragraph(Text(
                "Both laws are mass functions on Bool. The function positiveBiasLaw delta "
                    + "sends true to one half plus delta and false to one half minus delta. "
                    + "The function negativeBiasLaw delta reverses those two masses.")),
            Paragraph(Text(
                "The value here is API, not mathematical novelty. At the component level, "
                    + "the unit-mass proofs evaluate the two-point sum directly, and the "
                    + "nonnegativity proofs are a case split on Bool plus one linear "
                    + "arithmetic step; "
                    + "the bundled theorem only pairs the four component results.")),
            Paragraph(Text(
                "SymmetricBernoulliSecondOrder and FourLocalEvidenceClosedForms carry "
                    + "byte-identical private copies of the bundled statement. The second "
                    + "module imports the first. Both modules are frozen, so neither can "
                    + "import this module, and this change removes neither private copy.")),
            Paragraph(Text(
                "This module has zero consumers today. It does not prevent another future "
                    + "copy; what it adds is an available public name. The private copies "
                    + "assume the strict range |delta| < 1/2. In contrast, unit mass needs no "
                    + "hypothesis, while nonnegativity needs only the closed range "
                    + "|delta| <= 1/2. Separating the components makes those bounds visible.")),
            Describe.Lean(
                DescribeId.Create("positive-bias-law-sum"),
                DeclarationHandle.Create(DeclarationPrefix + "positiveBiasLaw_sum"),
                H("The positive-bias law has unit mass at every real bias"),
                StatementSource.FromAuthor(SumFormula(PositiveApplied)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real delta, including values outside the probability range, "
                        + "the two positive-bias masses add to one. No bound on delta is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("negative-bias-law-sum"),
                DeclarationHandle.Create(DeclarationPrefix + "negativeBiasLaw_sum"),
                H("The negative-bias law has unit mass at every real bias"),
                StatementSource.FromAuthor(SumFormula(NegativeApplied)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real delta, the reversed pair of masses also adds to one. "
                        + "This normalization identity likewise has no bias hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-bias-law-nonnegative"),
                DeclarationHandle.Create(DeclarationPrefix + "positiveBiasLaw_nonneg"),
                H("The positive-bias law is nonnegative on the closed bias range"),
                StatementSource.FromAuthor(NonnegativeFormula(PositiveApplied)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If |delta| <= 1/2, both values of positiveBiasLaw delta are "
                        + "nonnegative. Equality is permitted, so this includes either "
                        + "endpoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("negative-bias-law-nonnegative"),
                DeclarationHandle.Create(DeclarationPrefix + "negativeBiasLaw_nonneg"),
                H("The negative-bias law is nonnegative on the closed bias range"),
                StatementSource.FromAuthor(NonnegativeFormula(NegativeApplied)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same closed bound |delta| <= 1/2, reversing the two masses "
                        + "preserves pointwise nonnegativity on Bool."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bias-laws-probability-data"),
                DeclarationHandle.Create(DeclarationPrefix + "bias_laws_probability_data"),
                H("Both bias laws are probability data on the closed bias range"),
                StatementSource.FromAuthor(ProbabilityDataFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On |delta| <= 1/2, the positive law's pointwise nonnegativity and unit "
                        + "mass are paired first. The corresponding negative-law pair follows, "
                        + "and the theorem conjoins those two pairs in that order."))),
                DescribeRole.Theorem))));

    private static Formula Half() =>
        Seq(Frac, Grp(Num(1)), Grp(Num(2)));

    private static Formula RealType() =>
        Seq(Mathbb, Grp(F.Id("R")));

    private static Formula PositiveApplied(Formula delta, Formula bit) =>
        Seq(Call("positiveBiasLaw", delta), Open, bit, Close);

    private static Formula NegativeApplied(Formula delta, Formula bit) =>
        Seq(Call("negativeBiasLaw", delta), Open, bit, Close);

    private static Formula ClosedBound(Formula delta) =>
        Seq(new Formula.Absolute(delta), Sp, Leq, Sp, Half());

    private static Formula SumClause(Formula applied, Formula bit) =>
        Seq(
            Sum, Underscore, Grp(bit, Sp, InMacro, Sp, F.Id("Bool")), Sp,
            applied, Sp, Eq, Sp, Num(1));

    private static Formula NonnegativeClause(Formula applied, Formula bit) =>
        Seq(
            Forall, Sp, bit, Colon, Sp, F.Id("Bool"), Comma, Sp,
            Num(0), Sp, Leq, Sp, applied);

    private static Formula SumFormula(Func<Formula, Formula, Formula> applyLaw)
    {
        Formula delta = DeltaLower;
        Formula bit = F.Id("b");

        return Disp(Seq(
            Forall, Sp, delta, Colon, Sp, RealType(), Comma, Sp,
            SumClause(applyLaw(delta, bit), bit), Dot));
    }

    private static Formula NonnegativeFormula(Func<Formula, Formula, Formula> applyLaw)
    {
        Formula delta = DeltaLower;
        Formula bit = F.Id("b");

        return Disp(Seq(
            Forall, Sp, delta, Colon, Sp, RealType(), Comma, Sp,
            ClosedBound(delta), Sp, Rightarrow, Sp,
            NonnegativeClause(applyLaw(delta, bit), bit), Dot));
    }

    private static Formula ProbabilityDataFormula()
    {
        Formula delta = DeltaLower;
        Formula bit = F.Id("b");
        Formula positiveNonnegative =
            NonnegativeClause(PositiveApplied(delta, bit), bit);
        Formula positiveSum = SumClause(PositiveApplied(delta, bit), bit);
        Formula negativeNonnegative =
            NonnegativeClause(NegativeApplied(delta, bit), bit);
        Formula negativeSum = SumClause(NegativeApplied(delta, bit), bit);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, delta, Colon, Sp, RealType(), Comma, Sp,
                ClosedBound(delta), Sp, Rightarrow),
            Seq(
                Open, Open, positiveNonnegative, Close, Sp, Land, Sp, positiveSum, Close,
                Sp, Land),
            Seq(
                Open, Open, negativeNonnegative, Close, Sp, Land, Sp, negativeSum, Close,
                Dot),
        ]));
    }
}
