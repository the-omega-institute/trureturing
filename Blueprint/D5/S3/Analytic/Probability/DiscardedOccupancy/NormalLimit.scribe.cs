using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability.DiscardedOccupancy;

internal sealed class DiscardedOccupancyNormalLimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The count of distinct ordinary bins hit has a standard Gaussian weak limit after exact row standardization.",
        H("Gaussian limit for occupancy with discarded throws"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("occupancy-limit"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.exact_occupancy_normal_limit"),
                H("Gaussian limit of literal occupancy"),
                StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Row N has N plus one ordinary bins and N independent throws. The ordinary-bin masses are one divided by k times the number of bins, and each remaining mass belongs to the discard outcome. Standardization uses the expectation and variance under the product measure in that row. The proof telescopes the conditional characteristic-function comparisons and applies Lévy continuity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-deterministic-variance"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.deterministicVariance"),
                H("Deterministic Variance"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyDeterministicvariance())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-gaussian-product"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.gaussianProduct"),
                H("Gaussian Product"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyGaussianproduct())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-inst-is-probability-measure-forall-fin-option-literal-measure"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.instIsProbabilityMeasureForallFinOptionLiteralMeasure"),
                H("Inst Is Probability Measure Forall Fin Option Literal Measure"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyInstisprobabilitymeasureforallfinoptionliteralmeasure())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-literal-count"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.literalCount"),
                H("Literal Count"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyLiteralcount())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-literal-law"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.literalLaw"),
                H("Literal Law"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyLiterallaw())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-literal-measure"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.literalMeasure"),
                H("Literal Measure"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyLiteralmeasure())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-literal-standardized"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.literalStandardized"),
                H("Literal Standardized"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyLiteralstandardized())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-literal-moments"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.literal_moments"),
                H("Literal moments"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyLiteralMoments())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("For a word of m independent throws on n ordinary bins, the real-valued count has the mean and variance of the occupancy recurrence at retention probability one over k."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-literal-variance-eventually-positive"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.literal_variance_eventually_positive"),
                H("Literal variance eventually positive"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyLiteralVarianceEventuallyPositive())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-literal-variance-positive"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.literal_variance_positive"),
                H("Literal variance positive"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyLiteralVariancePositive())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Statement1()
    {
        var k = F.Id("k");
        var n = F.Id("N");
        var rows = Lam("N", Nat, Call("literalLaw", k, n));
        var convergence = Call("Tendsto", rows, F.Id("atTop"),
            Call("nhds", Call("gaussianReal", D(0), D(1))));
        return All("k", Nat, Seq(D(2), Sp, Leq, Sp, k, Sp, Implies, Sp, convergence));
    }

    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(x), Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula Lam(string x, Formula type, Formula body) =>
        Seq(Open, F.Id(x), Colon, Sp, type, Sp, Mapsto, Sp, body, Close);

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula DiscardedOccupancyDeterministicvariance() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("m"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Open,
        DefinitionDsl.Id("deterministicVariance"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("m"), Sp, Colon,
        Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Sp, Eq, Sp, Sum, Sp, F.Id("j"), Sp, InMacro, Sp,
        DefinitionDsl.Id("Finset"), Dot, DefinitionDsl.Id("range"), Sp, F.Id("m"), Comma, Sp,
        DefinitionDsl.Id("weight"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("m"), Sp, Open, F.Id("j"), Sp,
        Plus, Sp, D(1), Close, Sp, Caret, Sp, D(2), Sp, Cdot, Sp, DefinitionDsl.Id("predictableVariance"),
        Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"));

    private static Formula DiscardedOccupancyGaussianproduct() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("m"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open, Tau, Colon,
        Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open, F.Id("j"), Colon, Sp,
        Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Open, DefinitionDsl.Id("gaussianProduct"), Sp,
        F.Id("n"), Sp, F.Id("p"), Sp, F.Id("m"), Sp, Tau, Sp, F.Id("j"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("C"))), Close, Sp, Eq, Sp, Prod, Sp, F.Id("i"), Sp, InMacro, Sp,
        DefinitionDsl.Id("Finset"), Dot, DefinitionDsl.Id("range"), Sp, F.Id("j"), Comma, Sp,
        DefinitionDsl.Id("gaussianFactor"), Sp, Open, DefinitionDsl.Id("weight"), Sp, F.Id("n"), Sp,
        F.Id("p"), Sp, F.Id("m"), Sp, Open, F.Id("i"), Sp, Plus, Sp, D(1), Close, Sp, Cdot, Sp, Tau, Close,
        Sp, Open, DefinitionDsl.Id("predictableVariance"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("i"),
        Close);

    private static Formula DiscardedOccupancyInstisprobabilitymeasureforallfinoptionliteralmeasure() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hn"), Colon, Sp, D(0), Sp, Lt, Sp, F.Id("n"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hk"), Colon, Sp, D(2), Sp, Leq, Sp, F.Id("k"), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("m"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp,
        DefinitionDsl.Id("MeasureTheory"), Dot, DefinitionDsl.Id("IsProbabilityMeasure"), Sp, Open,
        DefinitionDsl.Id("literalMeasure"), Sp, DefinitionDsl.Id("hn"), Sp, DefinitionDsl.Id("hk"), Sp,
        F.Id("m"), Close);

    private static Formula DiscardedOccupancyLiteralcount() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("m"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open, Omega,
        Colon, Sp, DefinitionDsl.Id("Fin"), Sp, F.Id("m"), Sp, To, Sp, DefinitionDsl.Id("Option"), Sp, Open,
        DefinitionDsl.Id("Fin"), Sp, F.Id("n"), Close, Close, Comma, Sp, Open,
        DefinitionDsl.Id("literalCount"), Sp, F.Id("n"), Sp, F.Id("m"), Sp, Omega, Sp, Colon, Sp,
        Seq(Mathbb, Grp(F.Id("R"))), Close, Sp, Eq, Sp, DefinitionDsl.Id("val"), Sp, OpenBrace, F.Id("i"),
        Sp, Colon, Sp, DefinitionDsl.Id("Fin"), Sp, F.Id("n"), Sp, Bar, Sp, Exists, Sp, Open, F.Id("t"), Sp,
        Colon, Sp, DefinitionDsl.Id("Fin"), Sp, F.Id("m"), Close, Comma, Sp, Omega, Sp, F.Id("t"), Sp, Eq,
        Sp, DefinitionDsl.Id("some"), Sp, F.Id("i"), CloseBrace, Dot, DefinitionDsl.Id("card"));

    private static Formula DiscardedOccupancyLiterallaw() =>
        Seq(
        Forall, Sp, Open, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hk"), Colon, Sp, D(2), Sp, Leq, Sp, F.Id("k"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("N"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Open,
        DefinitionDsl.Id("literalLaw"), Sp, F.Id("k"), Sp, DefinitionDsl.Id("hk"), Sp, F.Id("N"), Sp, Colon,
        Sp, DefinitionDsl.Id("MeasureTheory"), Dot, DefinitionDsl.Id("ProbabilityMeasure"), Sp, Seq(Mathbb,
        Grp(F.Id("R"))), Close, Sp, Eq, Sp, DefinitionDsl.Id("Measure"), Dot, DefinitionDsl.Id("map"), Sp,
        Open, DefinitionDsl.Id("literalStandardized"), Sp, Open, F.Id("N"), Sp, Plus, Sp, D(1), Close, Sp,
        F.Id("k"), Sp, F.Id("N"), Close, Sp, Open, DefinitionDsl.Id("literalMeasure"), Sp, Open, F.Id("N"),
        Sp, Plus, Sp, D(1), Close, Sp, F.Id("k"), Sp, F.Id("N"), Close);

    private static Formula DiscardedOccupancyLiteralmeasure() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hn"), Colon, Sp, D(0), Sp, Lt, Sp, F.Id("n"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hk"), Colon, Sp, D(2), Sp, Leq, Sp, F.Id("k"), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("m"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Open,
        DefinitionDsl.Id("literalMeasure"), Sp, F.Id("n"), Sp, DefinitionDsl.Id("hn"), Sp, F.Id("k"), Sp,
        DefinitionDsl.Id("hk"), Sp, F.Id("m"), Sp, Colon, Sp, DefinitionDsl.Id("MeasureTheory"), Dot,
        DefinitionDsl.Id("Measure"), Sp, Open, DefinitionDsl.Id("Fin"), Sp, F.Id("m"), Sp, To, Sp,
        DefinitionDsl.Id("Option"), Sp, Open, DefinitionDsl.Id("Fin"), Sp, F.Id("n"), Close, Close, Close,
        Sp, Eq, Sp, DefinitionDsl.Id("Measure"), Dot, DefinitionDsl.Id("pi"), Sp, Open,
        DefinitionDsl.Id("fun"), Sp, Open, F.Id("i"), Sp, Colon, Sp, DefinitionDsl.Id("Fin"), Sp, F.Id("m"),
        Close, Sp, Eq, Gt, Sp, Open, DefinitionDsl.Id("throwPMF"), Sp, F.Id("n"), Sp, Open,
        DefinitionDsl.Id("paletteP"), Sp, F.Id("k"), Close, Close, Dot, DefinitionDsl.Id("toMeasure"), Close);

    private static Formula DiscardedOccupancyLiteralstandardized() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hn"), Colon, Sp, D(0), Sp, Lt, Sp, F.Id("n"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hk"), Colon, Sp, D(2), Sp, Leq, Sp, F.Id("k"), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("m"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open, Omega, Colon,
        Sp, DefinitionDsl.Id("Fin"), Sp, F.Id("m"), Sp, To, Sp, DefinitionDsl.Id("Option"), Sp, Open,
        DefinitionDsl.Id("Fin"), Sp, F.Id("n"), Close, Close, Comma, Sp, Open,
        DefinitionDsl.Id("literalStandardized"), Sp, F.Id("n"), Sp, DefinitionDsl.Id("hn"), Sp, F.Id("k"),
        Sp, DefinitionDsl.Id("hk"), Sp, F.Id("m"), Sp, Omega, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))),
        Close, Sp, Eq, Sp, Open, DefinitionDsl.Id("literalCount"), Sp, F.Id("n"), Sp, F.Id("m"), Sp, Omega,
        Sp, Minus, Sp, Int, Sp, Open, F.Id("y"), Sp, Colon, Sp, DefinitionDsl.Id("Fin"), Sp, F.Id("m"), Sp,
        To, Sp, DefinitionDsl.Id("Option"), Sp, Open, DefinitionDsl.Id("Fin"), Sp, F.Id("n"), Close, Close,
        Comma, Sp, DefinitionDsl.Id("literalCount"), Sp, F.Id("n"), Sp, F.Id("m"), Sp, F.Id("y"), Sp,
        F.Id("d"), Sp, DefinitionDsl.Id("literalMeasure"), Sp, DefinitionDsl.Id("hn"), Sp,
        DefinitionDsl.Id("hk"), Sp, F.Id("m"), Close, Sp, Slash, Sp, Operatorname, Grp(F.Id("sqrt")), Sp,
        Open, DefinitionDsl.Id("ProbabilityTheory"), Dot, DefinitionDsl.Id("variance"), Sp, Open,
        DefinitionDsl.Id("literalCount"), Sp, F.Id("n"), Sp, F.Id("m"), Close, Sp, Open,
        DefinitionDsl.Id("literalMeasure"), Sp, DefinitionDsl.Id("hn"), Sp, DefinitionDsl.Id("hk"), Sp,
        F.Id("m"), Close, Close);

    private static Formula DiscardedOccupancyLiteralMoments() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hn"), Colon, Sp, D(0), Sp, Lt, Sp, F.Id("n"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hk"), Colon, Sp, D(2), Sp, Leq, Sp, F.Id("k"), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("m"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Int, Sp, Open, Omega, Sp,
        Colon, Sp, DefinitionDsl.Id("Fin"), Sp, F.Id("m"), Sp, To, Sp, DefinitionDsl.Id("Option"), Sp, Open,
        DefinitionDsl.Id("Fin"), Sp, F.Id("n"), Close, Close, Comma, Sp, DefinitionDsl.Id("literalCount"),
        Sp, F.Id("n"), Sp, F.Id("m"), Sp, Omega, Sp, F.Id("d"), Sp, DefinitionDsl.Id("literalMeasure"), Sp,
        DefinitionDsl.Id("hn"), Sp, DefinitionDsl.Id("hk"), Sp, F.Id("m"), Sp, Eq, Sp,
        DefinitionDsl.Id("mean"), Sp, F.Id("n"), Sp, Open, DefinitionDsl.Id("paletteP"), Sp, F.Id("k"),
        Close, Sp, F.Id("m"), Sp, Land, Sp, DefinitionDsl.Id("ProbabilityTheory"), Dot,
        DefinitionDsl.Id("variance"), Sp, Open, DefinitionDsl.Id("literalCount"), Sp, F.Id("n"), Sp,
        F.Id("m"), Close, Sp, Open, DefinitionDsl.Id("literalMeasure"), Sp, DefinitionDsl.Id("hn"), Sp,
        DefinitionDsl.Id("hk"), Sp, F.Id("m"), Close, Sp, Eq, Sp, DefinitionDsl.Id("variance"), Sp,
        F.Id("n"), Sp, Open, DefinitionDsl.Id("paletteP"), Sp, F.Id("k"), Close, Sp, F.Id("m"));

    private static Formula DiscardedOccupancyLiteralVarianceEventuallyPositive() =>
        Seq(
        Forall, Sp, Open, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hk"), Colon, Sp, D(2), Sp, Leq, Sp, F.Id("k"), Close, Comma, Sp,
        DefinitionDsl.Id("Eventually"), Sp, Open, F.Id("N"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))),
        Close, Sp, DefinitionDsl.Id("in"), Sp, DefinitionDsl.Id("Filter"), Dot, DefinitionDsl.Id("atTop"),
        Comma, Sp, D(0), Sp, Lt, Sp, DefinitionDsl.Id("ProbabilityTheory"), Dot,
        DefinitionDsl.Id("variance"), Sp, Open, DefinitionDsl.Id("literalCount"), Sp, Open, F.Id("N"), Sp,
        Plus, Sp, D(1), Close, Sp, F.Id("N"), Close, Sp, Open, DefinitionDsl.Id("literalMeasure"), Sp, Open,
        F.Id("N"), Sp, Plus, Sp, D(1), Close, Sp, F.Id("k"), Sp, F.Id("N"), Close);

    private static Formula DiscardedOccupancyLiteralVariancePositive() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hn"), Colon, Sp, D(2), Sp, Leq, Sp, F.Id("n"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hk"), Colon, Sp, D(2), Sp, Leq, Sp, F.Id("k"), Close, Comma, Sp, D(0), Sp, Lt, Sp,
        DefinitionDsl.Id("ProbabilityTheory"), Dot, DefinitionDsl.Id("variance"), Sp, Open,
        DefinitionDsl.Id("literalCount"), Sp, F.Id("n"), Sp, Open, F.Id("n"), Sp, Minus, Sp, D(1), Close,
        Close, Sp, Open, DefinitionDsl.Id("literalMeasure"), Sp, F.Id("n"), Sp, F.Id("k"), Sp, Open,
        F.Id("n"), Sp, Minus, Sp, D(1), Close, Close);
}
