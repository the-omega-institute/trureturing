using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability.DiscardedOccupancy;

internal sealed class DiscardedOccupancyCharacteristicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The explicit finite word measure is the product of the individual throw measures.",
        H("Occupancy word laws and characteristic functions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("word-product"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.wordMeasure_eq_pi"),
                H("The finite word measure is a product"),
                StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A throw is discarded with probability one minus p and each ordinary bin has mass p divided by n. The mass of a word is the product of the coordinate masses. The transition calculation for the characteristic function uses this same law and conditions on the count of occupied bins after the prefix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-centered-bernoulli"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.centeredBernoulli"),
                H("Centered Bernoulli"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyCenteredbernoulli())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-char-fun-standardized-law"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.charFun_standardizedLaw"),
                H("Char Fun standardized Law"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyCharfunStandardizedlaw())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-conditional-comparison"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.conditional_comparison"),
                H("Conditional comparison"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyConditionalComparison())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-expect-sub"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.expect_sub"),
                H("Expect sub"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyExpectSub())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-fluctuation-bound"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.fluctuationBound"),
                H("Fluctuation Bound"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyFluctuationbound())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-gaussian-factor"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.gaussianFactor"),
                H("Gaussian Factor"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyGaussianfactor())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-inst-measurable-singleton-class-option-fin-d5"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.instMeasurableSingletonClassOptionFin_d5"),
                H("Inst Measurable Singleton Class Option Fin d5"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyInstmeasurablesingletonclassoptionfinD5())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-inst-measurable-space-option-fin-d5"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.instMeasurableSpaceOptionFin_d5"),
                H("Inst Measurable Space Option Fin d5"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyInstmeasurablespaceoptionfinD5())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-integral-count"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.integral_count"),
                H("Integral count"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyIntegralCount())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-mem-occupied-iff"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.mem_occupied_iff"),
                H("Mem occupied iff"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyMemOccupiedIff())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-norm-expect-le"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.norm_expect_le"),
                H("Norm expect le"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyNormExpectLe())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-norm-gaussian-factor-le"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.norm_gaussianFactor_le"),
                H("Norm gaussian Factor le"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyNormGaussianfactorLe())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-palette-p"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.paletteP"),
                H("Palette P"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyPalettep())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-palette-bounds"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.palette_bounds"),
                H("Palette bounds"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyPaletteBounds())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-palette-throw-mass"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.palette_throw_mass"),
                H("Palette throw mass"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyPaletteThrowMass())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-phase"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.phase"),
                H("Phase"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyPhase())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-predictable-variance"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.predictableVariance"),
                H("Predictable Variance"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyPredictablevariance())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-row-law"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.rowLaw"),
                H("Row Law"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyRowlaw())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The row with index N uses N throws and N plus one ordinary bins with retention probability one over k."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-row-phase"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.rowPhase"),
                H("Row Phase"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyRowphase())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-row-phase-zero"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.rowPhase_zero"),
                H("Row Phase zero"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyRowphaseZero())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-standardized"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.standardized"),
                H("Standardized"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyStandardized())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-standardized-law"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.standardizedLaw"),
                H("Standardized Law"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyStandardizedlaw())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-throw-pmf"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.throwPMF"),
                H("Throw PMF"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyThrowpmf())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-variance-count"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.variance_count"),
                H("Variance count"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyVarianceCount())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-variance-fluctuation"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.variance_fluctuation"),
                H("Variance fluctuation"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyVarianceFluctuation())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-weight"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.weight"),
                H("Weight"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyWeight())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-word-pmf"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic.wordPMF"),
                H("Word PMF"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyWordpmf())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition)),
        []));

    private static Formula Statement1()
    {
        var n = F.Id("n");
        var p = F.Id("p");
        var j = F.Id("j");
        var product = Seq(new Formula.Subscript(Prod, Seq(F.Id("i"), Colon, Sp, Call("Fin", j))),
            Sp, Call("toMeasure", Call("throwPMF", n, p)));
        var equation = Equal(Call("toMeasure", Call("wordPMF", n, p, j)), product);
        return All("n", Nat, All("p", Real, All("j", Nat,
            Seq(D(0), Lt, n, Sp, Implies, Sp, D(0), Sp, Leq, Sp, p, Sp, Implies, Sp,
                p, Sp, Leq, Sp, D(1), Sp, Implies, Sp, equation))));
    }

    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(x), Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula DiscardedOccupancyCenteredbernoulli() =>
        Seq(
        Forall, Sp, Open, F.Id("r"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("s"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Open,
        DefinitionDsl.Id("centeredBernoulli"), Sp, F.Id("r"), Sp, F.Id("s"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("C"))), Close, Sp, Eq, Sp, Open, D(1), Sp, Minus, Sp, F.Id("r"), Close, Sp, Cdot, Sp,
        DefinitionDsl.Id("phase"), Sp, Open, F.Id("s"), Sp, Cdot, Sp, Minus, F.Id("r"), Close, Sp, Plus, Sp,
        F.Id("r"), Sp, Cdot, Sp, DefinitionDsl.Id("phase"), Sp, Open, F.Id("s"), Sp, Cdot, Sp, Open, D(1),
        Sp, Minus, Sp, F.Id("r"), Close, Close);

    private static Formula DiscardedOccupancyCharfunStandardizedlaw() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hn"), Colon, Sp, D(0), Sp, Lt, Sp, F.Id("n"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hp"), Colon, Sp, D(0), Sp, Leq, Sp, F.Id("p"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hpUpper"), Colon, Sp, F.Id("p"), Sp, Leq, Sp, D(1), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("t"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp,
        DefinitionDsl.Id("MeasureTheory"), Dot, DefinitionDsl.Id("charFun"), Sp, Open,
        DefinitionDsl.Id("val"), Sp, Open, DefinitionDsl.Id("standardizedLaw"), Sp, DefinitionDsl.Id("hn"),
        Sp, DefinitionDsl.Id("hp"), Sp, DefinitionDsl.Id("hpUpper"), Sp, F.Id("j"), Close, Close, Sp,
        F.Id("t"), Sp, Eq, Sp, DefinitionDsl.Id("expect"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp,
        DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Sp,
        Mapsto, Sp, DefinitionDsl.Id("phase"), Sp, Open, F.Id("t"), Sp, Cdot, Sp,
        DefinitionDsl.Id("standardized"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp, F.Id("x"), Close);

    private static Formula DiscardedOccupancyConditionalComparison() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hn"), Colon, Sp, D(0), Sp, Lt, Sp, F.Id("n"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hp"), Colon, Sp, D(0), Sp, Leq, Sp, F.Id("p"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hpUpper"), Colon, Sp, F.Id("p"), Sp, Leq, Sp, D(1), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hj"), Colon, Sp, F.Id("j"), Sp, Leq, Sp, F.Id("n"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("s"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hs"), Colon, Sp, Bar, F.Id("s"), Bar, Sp, Leq, Sp, D(1), Close, Comma, Sp, Vert,
        Sp, DefinitionDsl.Id("rowPhase"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, Open, F.Id("j"), Sp, Plus, Sp,
        D(1), Close, Sp, F.Id("s"), Sp, Minus, Sp, DefinitionDsl.Id("rowPhase"), Sp, F.Id("n"), Sp,
        F.Id("p"), Sp, F.Id("j"), Sp, Open, F.Id("a"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, Cdot, Sp,
        F.Id("s"), Close, Sp, Cdot, Sp, DefinitionDsl.Id("gaussianFactor"), Sp, F.Id("s"), Sp, Open,
        DefinitionDsl.Id("predictableVariance"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Close, Vert,
        Sp, Leq, Sp, Open, DefinitionDsl.Id("Real"), Dot, DefinitionDsl.Id("exp"), Sp, D(1), Sp, Plus, Sp,
        D(1), Close, Sp, Cdot, Sp, Bar, F.Id("s"), Bar, Sp, Caret, Sp, D(3), Sp, Plus, Sp, F.Id("s"), Sp,
        Caret, Sp, D(2), Sp, Slash, Sp, D(2), Sp, Cdot, Sp, DefinitionDsl.Id("fluctuationBound"), Sp,
        F.Id("n"), Sp, F.Id("p"));

    private static Formula DiscardedOccupancyExpectSub() =>
        Seq(
        Forall, Sp, Open, F.Id("E"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("AddCommGroup"), Sp, F.Id("E"), CloseBracket, Sp, OpenBracket, Mathrm,
        Grp(F.Id("anonymous")), DefinitionDsl.Id("root"), Mathrm, Grp(F.Id("anonymous")), Dot,
        DefinitionDsl.Id("Module"), Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, F.Id("E"), CloseBracket, Sp,
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open, F.Id("f"),
        Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, F.Id("E"), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("g"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, F.Id("E"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("expect"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp,
        DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Sp,
        Mapsto, Sp, F.Id("f"), Sp, F.Id("x"), Sp, Minus, Sp, F.Id("g"), Sp, F.Id("x"), Close, Sp, Eq, Sp,
        DefinitionDsl.Id("expect"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp, F.Id("f"), Sp, Minus,
        Sp, DefinitionDsl.Id("expect"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp, F.Id("g"));

    private static Formula DiscardedOccupancyFluctuationbound() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Open,
        DefinitionDsl.Id("fluctuationBound"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("R"))), Close, Sp, Eq, Sp, F.Id("p"), Sp, Slash, Sp, DefinitionDsl.Id("val"), Sp,
        F.Id("n"), Sp, Cdot, Sp, Operatorname, Grp(F.Id("sqrt")), Sp, DefinitionDsl.Id("val"), Sp, F.Id("n"));

    private static Formula DiscardedOccupancyGaussianfactor() =>
        Seq(
        Forall, Sp, Open, F.Id("s"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("u"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Open,
        DefinitionDsl.Id("gaussianFactor"), Sp, F.Id("s"), Sp, F.Id("u"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("C"))), Close, Sp, Eq, Sp, DefinitionDsl.Id("val"), Sp, Open, DefinitionDsl.Id("Real"),
        Dot, DefinitionDsl.Id("exp"), Sp, Open, Minus, F.Id("s"), Sp, Caret, Sp, D(2), Sp, Cdot, Sp,
        F.Id("u"), Sp, Slash, Sp, D(2), Close, Close);

    private static Formula DiscardedOccupancyInstmeasurablesingletonclassoptionfinD5() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp,
        DefinitionDsl.Id("MeasurableSingletonClass"), Sp, Open, DefinitionDsl.Id("Option"), Sp, Open,
        DefinitionDsl.Id("Fin"), Sp, F.Id("n"), Close, Close);

    private static Formula DiscardedOccupancyInstmeasurablespaceoptionfinD5() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Open,
        DefinitionDsl.Id("instMeasurableSpaceOptionFin"), Mathrm, Grp(F.Id("anonymous")),
        DefinitionDsl.Id("d5"), Sp, F.Id("n"), Sp, Colon, Sp, DefinitionDsl.Id("MeasurableSpace"), Sp, Open,
        DefinitionDsl.Id("Option"), Sp, Open, DefinitionDsl.Id("Fin"), Sp, F.Id("n"), Close, Close, Close,
        Sp, Eq, Sp, Operatorname, Grp(F.Id("top")));

    private static Formula DiscardedOccupancyIntegralCount() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hn"), Colon, Sp, D(0), Sp, Lt, Sp, F.Id("n"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hp"), Colon, Sp, D(0), Sp, Leq, Sp, F.Id("p"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hpUpper"), Colon, Sp, F.Id("p"), Sp, Leq, Sp, D(1), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Int, Sp, Open, Omega, Sp,
        Colon, Sp, DefinitionDsl.Id("DiscardedOccupancy"), Dot, DefinitionDsl.Id("History"), Sp, F.Id("n"),
        Sp, F.Id("j"), Close, Comma, Sp, DefinitionDsl.Id("val"), Sp, Open, DefinitionDsl.Id("count"), Sp,
        F.Id("n"), Sp, F.Id("j"), Sp, Omega, Close, Sp, F.Id("d"), Sp, Open, DefinitionDsl.Id("wordPMF"),
        Sp, DefinitionDsl.Id("hn"), Sp, DefinitionDsl.Id("hp"), Sp, DefinitionDsl.Id("hpUpper"), Sp,
        F.Id("j"), Close, Dot, DefinitionDsl.Id("toMeasure"), Sp, Eq, Sp, DefinitionDsl.Id("mean"), Sp,
        F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"));

    private static Formula DiscardedOccupancyMemOccupiedIff() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("i"), Colon, Sp, DefinitionDsl.Id("Fin"), Sp, F.Id("n"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open, Omega,
        Colon, Sp, DefinitionDsl.Id("DiscardedOccupancy"), Dot, DefinitionDsl.Id("History"), Sp, F.Id("n"),
        Sp, F.Id("j"), Close, Comma, Sp, F.Id("i"), Sp, InMacro, Sp, DefinitionDsl.Id("occupied"), Sp,
        F.Id("n"), Sp, F.Id("j"), Sp, Omega, Sp, Iff, Sp, Exists, Sp, Open, F.Id("t"), Sp, Colon, Sp,
        DefinitionDsl.Id("Fin"), Sp, F.Id("j"), Close, Comma, Sp, Omega, Sp, F.Id("t"), Sp, Eq, Sp,
        DefinitionDsl.Id("some"), Sp, F.Id("i"));

    private static Formula DiscardedOccupancyNormExpectLe() =>
        Seq(
        Forall, Sp, Open, F.Id("E"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("NormedAddCommGroup"), Sp, F.Id("E"), CloseBracket, Sp, OpenBracket,
        DefinitionDsl.Id("NormedSpace"), Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, F.Id("E"), CloseBracket, Sp,
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hp"), Colon, Sp, D(0), Sp, Leq, Sp, F.Id("p"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hpUpper"), Colon, Sp, F.Id("p"), Sp, Leq, Sp, D(1), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("f"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, F.Id("E"), Close, Comma, Sp,
        Vert, Sp, DefinitionDsl.Id("expect"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp, F.Id("f"),
        Vert, Sp, Leq, Sp, DefinitionDsl.Id("expect"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp,
        DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Sp,
        Mapsto, Sp, Vert, Sp, F.Id("f"), Sp, F.Id("x"), Vert);

    private static Formula DiscardedOccupancyNormGaussianfactorLe() =>
        Seq(
        Forall, Sp, Open, F.Id("s"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("u"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hu"), Colon, Sp, D(0), Sp, Leq, Sp, F.Id("u"), Close, Comma, Sp, Vert, Sp,
        DefinitionDsl.Id("gaussianFactor"), Sp, F.Id("s"), Sp, F.Id("u"), Vert, Sp, Leq, Sp, D(1));

    private static Formula DiscardedOccupancyPalettep() =>
        Seq(
        Forall, Sp, Open, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Open,
        DefinitionDsl.Id("paletteP"), Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Sp,
        Eq, Sp, Open, DefinitionDsl.Id("val"), Sp, F.Id("k"), Close, Sp, Caret, Open, Minus, D(1), Close);

    private static Formula DiscardedOccupancyPaletteBounds() =>
        Seq(
        Forall, Sp, Open, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hk"), Colon, Sp, D(2), Sp, Leq, Sp, F.Id("k"), Close, Comma, Sp, D(0), Sp,
        Lt, Sp, DefinitionDsl.Id("paletteP"), Sp, F.Id("k"), Sp, Land, Sp, DefinitionDsl.Id("paletteP"), Sp,
        F.Id("k"), Sp, Lt, Sp, D(1));

    private static Formula DiscardedOccupancyPaletteThrowMass() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hn"), Colon, Sp, D(0), Sp, Lt, Sp, F.Id("n"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hk"), Colon, Sp, D(2), Sp, Leq, Sp, F.Id("k"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("throwPMF"), Sp, F.Id("n"), Sp, Open, DefinitionDsl.Id("paletteP"), Sp, F.Id("k"),
        Close, Close, Dot, DefinitionDsl.Id("toMeasure"), Sp, OpenBrace, DefinitionDsl.Id("none"),
        CloseBrace, Sp, Eq, Sp, DefinitionDsl.Id("ENNReal"), Dot, DefinitionDsl.Id("ofReal"), Sp, Open,
        D(1), Sp, Minus, Sp, D(1), Sp, Slash, Sp, DefinitionDsl.Id("val"), Sp, F.Id("k"), Close, Sp, Land,
        Sp, Forall, Sp, Open, F.Id("i"), Sp, Colon, Sp, DefinitionDsl.Id("Fin"), Sp, F.Id("n"), Close,
        Comma, Sp, Open, DefinitionDsl.Id("throwPMF"), Sp, F.Id("n"), Sp, Open,
        DefinitionDsl.Id("paletteP"), Sp, F.Id("k"), Close, Close, Dot, DefinitionDsl.Id("toMeasure"), Sp,
        OpenBrace, DefinitionDsl.Id("some"), Sp, F.Id("i"), CloseBrace, Sp, Eq, Sp,
        DefinitionDsl.Id("ENNReal"), Dot, DefinitionDsl.Id("ofReal"), Sp, Open, D(1), Sp, Slash, Sp, Open,
        DefinitionDsl.Id("val"), Sp, F.Id("k"), Sp, Cdot, Sp, DefinitionDsl.Id("val"), Sp, F.Id("n"), Close,
        Close);

    private static Formula DiscardedOccupancyPhase() =>
        Seq(
        Forall, Sp, Open, F.Id("s"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Open,
        DefinitionDsl.Id("phase"), Sp, F.Id("s"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))), Close, Sp, Eq,
        Sp, DefinitionDsl.Id("Complex"), Dot, DefinitionDsl.Id("exp"), Sp, Open, DefinitionDsl.Id("val"),
        Sp, F.Id("s"), Sp, Cdot, Sp, DefinitionDsl.Id("Complex"), Dot, F.Id("I"), Close);

    private static Formula DiscardedOccupancyPredictablevariance() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Open,
        DefinitionDsl.Id("predictableVariance"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp, Colon, Sp,
        Seq(Mathbb, Grp(F.Id("R"))), Close, Sp, Eq, Sp, F.Id("v"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, Open,
        DefinitionDsl.Id("mean"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Close);

    private static Formula DiscardedOccupancyRowlaw() =>
        Seq(
        Forall, Sp, Open, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hk"), Colon, Sp, D(2), Sp, Leq, Sp, F.Id("k"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("N"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp,
        DefinitionDsl.Id("rowLaw"), Sp, F.Id("k"), Sp, DefinitionDsl.Id("hk"), Sp, F.Id("N"), Sp, Eq, Sp,
        DefinitionDsl.Id("standardizedLaw"), Sp, Open, F.Id("N"), Sp, Plus, Sp, D(1), Close, Sp, Open,
        DefinitionDsl.Id("paletteP"), Sp, F.Id("k"), Close, Sp, F.Id("N"));

    private static Formula DiscardedOccupancyRowphase() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open, F.Id("s"),
        Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Open, DefinitionDsl.Id("rowPhase"), Sp,
        F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp, F.Id("s"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))),
        Close, Sp, Eq, Sp, DefinitionDsl.Id("expect"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp,
        DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Sp,
        Mapsto, Sp, DefinitionDsl.Id("phase"), Sp, Open, F.Id("s"), Sp, Cdot, Sp, Open,
        DefinitionDsl.Id("val"), Sp, F.Id("x"), Sp, Minus, Sp, DefinitionDsl.Id("mean"), Sp, F.Id("n"), Sp,
        F.Id("p"), Sp, F.Id("j"), Close, Close);

    private static Formula DiscardedOccupancyRowphaseZero() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("s"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, DefinitionDsl.Id("rowPhase"),
        Sp, F.Id("n"), Sp, F.Id("p"), Sp, D(0), Sp, F.Id("s"), Sp, Eq, Sp, D(1));

    private static Formula DiscardedOccupancyStandardized() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open, F.Id("x"),
        Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Open, DefinitionDsl.Id("standardized"),
        Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("R"))), Close, Sp, Eq, Sp, Open, DefinitionDsl.Id("val"), Sp, F.Id("x"), Sp, Minus, Sp,
        DefinitionDsl.Id("mean"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Close, Sp, Slash, Sp,
        Operatorname, Grp(F.Id("sqrt")), Sp, Open, DefinitionDsl.Id("variance"), Sp, F.Id("n"), Sp,
        F.Id("p"), Sp, F.Id("j"), Close);

    private static Formula DiscardedOccupancyStandardizedlaw() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hn"), Colon, Sp, D(0), Sp, Lt, Sp, F.Id("n"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hp"), Colon, Sp, D(0), Sp, Leq, Sp, F.Id("p"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hpUpper"), Colon, Sp, F.Id("p"), Sp, Leq, Sp, D(1), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Open,
        DefinitionDsl.Id("standardizedLaw"), Sp, F.Id("n"), Sp, DefinitionDsl.Id("hn"), Sp, F.Id("p"), Sp,
        DefinitionDsl.Id("hp"), Sp, DefinitionDsl.Id("hpUpper"), Sp, F.Id("j"), Sp, Colon, Sp,
        DefinitionDsl.Id("MeasureTheory"), Dot, DefinitionDsl.Id("ProbabilityMeasure"), Sp, Seq(Mathbb,
        Grp(F.Id("R"))), Close, Sp, Eq, Sp, Langle, Sp, DefinitionDsl.Id("MeasureTheory"), Dot,
        DefinitionDsl.Id("Measure"), Dot, DefinitionDsl.Id("map"), Sp, Open, DefinitionDsl.Id("fun"), Sp,
        Open, Omega, Sp, Colon, Sp, DefinitionDsl.Id("DiscardedOccupancy"), Dot,
        DefinitionDsl.Id("History"), Sp, F.Id("n"), Sp, F.Id("j"), Close, Sp, Mapsto, Sp,
        DefinitionDsl.Id("standardized"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp, Open,
        DefinitionDsl.Id("count"), Sp, F.Id("n"), Sp, F.Id("j"), Sp, Omega, Close, Close, Sp, Open,
        DefinitionDsl.Id("wordPMF"), Sp, DefinitionDsl.Id("hn"), Sp, DefinitionDsl.Id("hp"), Sp,
        DefinitionDsl.Id("hpUpper"), Sp, F.Id("j"), Close, Dot, DefinitionDsl.Id("toMeasure"), Rangle);

    private static Formula DiscardedOccupancyThrowpmf() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hn"), Colon, Sp, D(0), Sp, Lt, Sp, F.Id("n"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hp"), Colon, Sp, D(0), Sp, Leq, Sp, F.Id("p"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hpUpper"), Colon, Sp, F.Id("p"), Sp, Leq, Sp, D(1), Close, Comma, Sp, Open,
        DefinitionDsl.Id("throwPMF"), Sp, F.Id("n"), Sp, DefinitionDsl.Id("hn"), Sp, F.Id("p"), Sp,
        DefinitionDsl.Id("hp"), Sp, DefinitionDsl.Id("hpUpper"), Sp, Colon, Sp, DefinitionDsl.Id("PMF"), Sp,
        Open, DefinitionDsl.Id("Option"), Sp, Open, DefinitionDsl.Id("Fin"), Sp, F.Id("n"), Close, Close,
        Close, Sp, Eq, Sp, DefinitionDsl.Id("PMF"), Dot, DefinitionDsl.Id("ofFintype"), Sp, Open,
        DefinitionDsl.Id("fun"), Sp, Open, F.Id("b"), Sp, Colon, Sp, DefinitionDsl.Id("Option"), Sp, Open,
        DefinitionDsl.Id("Fin"), Sp, F.Id("n"), Close, Close, Sp, Mapsto, Sp, DefinitionDsl.Id("ENNReal"),
        Dot, DefinitionDsl.Id("ofReal"), Sp, Open, DefinitionDsl.Id("throwMass"), Sp, F.Id("n"), Sp,
        F.Id("p"), Sp, F.Id("b"), Close, Close);

    private static Formula DiscardedOccupancyVarianceCount() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hn"), Colon, Sp, D(0), Sp, Lt, Sp, F.Id("n"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hp"), Colon, Sp, D(0), Sp, Leq, Sp, F.Id("p"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hpUpper"), Colon, Sp, F.Id("p"), Sp, Leq, Sp, D(1), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp,
        DefinitionDsl.Id("ProbabilityTheory"), Dot, DefinitionDsl.Id("variance"), Sp, Open,
        DefinitionDsl.Id("fun"), Sp, Open, Omega, Sp, Colon, Sp, DefinitionDsl.Id("DiscardedOccupancy"),
        Dot, DefinitionDsl.Id("History"), Sp, F.Id("n"), Sp, F.Id("j"), Close, Sp, Mapsto, Sp,
        DefinitionDsl.Id("val"), Sp, Open, DefinitionDsl.Id("count"), Sp, F.Id("n"), Sp, F.Id("j"), Sp,
        Omega, Close, Close, Sp, Open, DefinitionDsl.Id("wordPMF"), Sp, DefinitionDsl.Id("hn"), Sp,
        DefinitionDsl.Id("hp"), Sp, DefinitionDsl.Id("hpUpper"), Sp, F.Id("j"), Close, Dot,
        DefinitionDsl.Id("toMeasure"), Sp, Eq, Sp, DefinitionDsl.Id("variance"), Sp, F.Id("n"), Sp,
        F.Id("p"), Sp, F.Id("j"));

    private static Formula DiscardedOccupancyVarianceFluctuation() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hn"), Colon, Sp, D(0), Sp, Lt, Sp, F.Id("n"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hp"), Colon, Sp, D(0), Sp, Leq, Sp, F.Id("p"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hpUpper"), Colon, Sp, F.Id("p"), Sp, Leq, Sp, D(1), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hj"), Colon, Sp, F.Id("j"), Sp, Leq, Sp, F.Id("n"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("expect"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp,
        DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Sp,
        Mapsto, Sp, Bar, F.Id("v"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, DefinitionDsl.Id("val"), Sp,
        F.Id("x"), Sp, Minus, Sp, DefinitionDsl.Id("predictableVariance"), Sp, F.Id("n"), Sp, F.Id("p"), Sp,
        F.Id("j"), Bar, Close, Sp, Leq, Sp, DefinitionDsl.Id("fluctuationBound"), Sp, F.Id("n"), Sp,
        F.Id("p"));

    private static Formula DiscardedOccupancyWeight() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("m"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open, F.Id("j"),
        Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Open, DefinitionDsl.Id("weight"), Sp,
        F.Id("n"), Sp, F.Id("p"), Sp, F.Id("m"), Sp, F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))),
        Close, Sp, Eq, Sp, F.Id("a"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, Caret, Sp, Open, F.Id("m"), Sp,
        Minus, Sp, F.Id("j"), Close);

    private static Formula DiscardedOccupancyWordpmf() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hn"), Colon, Sp, D(0), Sp, Lt, Sp, F.Id("n"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hp"), Colon, Sp, D(0), Sp, Leq, Sp, F.Id("p"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hpUpper"), Colon, Sp, F.Id("p"), Sp, Leq, Sp, D(1), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Open,
        DefinitionDsl.Id("wordPMF"), Sp, F.Id("n"), Sp, DefinitionDsl.Id("hn"), Sp, F.Id("p"), Sp,
        DefinitionDsl.Id("hp"), Sp, DefinitionDsl.Id("hpUpper"), Sp, F.Id("j"), Sp, Colon, Sp,
        DefinitionDsl.Id("PMF"), Sp, Open, DefinitionDsl.Id("DiscardedOccupancy"), Dot,
        DefinitionDsl.Id("History"), Sp, F.Id("n"), Sp, F.Id("j"), Close, Close, Sp, Eq, Sp,
        DefinitionDsl.Id("PMF"), Dot, DefinitionDsl.Id("ofFintype"), Sp, Open, DefinitionDsl.Id("fun"), Sp,
        Open, F.Id("w"), Sp, Colon, Sp, DefinitionDsl.Id("History"), Sp, F.Id("n"), Sp, F.Id("j"), Close,
        Sp, Mapsto, Sp, DefinitionDsl.Id("ENNReal"), Dot, DefinitionDsl.Id("ofReal"), Sp, Open,
        DefinitionDsl.Id("wordMass"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("w"), Close, Close);
}
