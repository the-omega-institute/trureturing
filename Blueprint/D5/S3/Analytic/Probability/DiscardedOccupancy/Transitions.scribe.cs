using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability.DiscardedOccupancy;

internal sealed class DiscardedOccupancyTransitionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A lower bound on early conditional variances gives a linear lower bound for the terminal variance.",
        H("Transitions of occupancy with discarded throws"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("variance-lower"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.variance_lower"),
                H("Variance from the early throws"),
                StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here n is the number of ordinary bins and p is the total probability of assigning a throw to an ordinary bin. The trial following x occupied bins increases the count with probability p times one minus x divided by n. The exact weighted variance recursion yields the displayed bound from the first floor of n divided by two increments."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-history"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.History"),
                H("History"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyHistory())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-a"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.a"),
                H("A"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyA())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-a-bounds"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.a_bounds"),
                H("A bounds"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyABounds())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-average"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.average"),
                H("Average"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyAverage())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-count"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.count"),
                H("Count"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyCount())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-expect"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.expect"),
                H("Expect"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyExpect())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-expect-add"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.expect_add"),
                H("Expect add"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyExpectAdd())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-expect-congr"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.expect_congr"),
                H("Expect congr"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyExpectCongr())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-expect-const"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.expect_const"),
                H("Expect const"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyExpectConst())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-expect-mono"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.expect_mono"),
                H("Expect mono"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyExpectMono())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-expect-smul"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.expect_smul"),
                H("Expect smul"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyExpectSmul())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-expect-succ"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.expect_succ"),
                H("Expect succ"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyExpectSucc())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-expect-zero-time"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.expect_zero_time"),
                H("Expect zero time"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyExpectZeroTime())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-insert-throw"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.insertThrow"),
                H("Insert Throw"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyInsertthrow())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-mean"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.mean"),
                H("Mean"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyMean())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-mean-bounds"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.mean_bounds"),
                H("Mean bounds"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyMeanBounds())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-mean-succ"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.mean_succ"),
                H("Mean succ"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyMeanSucc())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-occupied"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.occupied"),
                H("Occupied"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyOccupied())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-q"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.q"),
                H("Q"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyQ())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-q-bounds"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.q_bounds"),
                H("Q bounds"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyQBounds())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-throw-mass"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.throwMass"),
                H("Throw Mass"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyThrowmass())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-v"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.v"),
                H("V"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyV())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-v-bounds"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.v_bounds"),
                H("V bounds"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyVBounds())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-variance"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.variance"),
                H("Variance"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyVariance())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-variance-le-time"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.variance_le_time"),
                H("Variance le time"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyVarianceLeTime())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-variance-nonneg"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.variance_nonneg"),
                H("Variance nonneg"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyVarianceNonneg())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-weighted-variance"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.weighted_variance"),
                H("Weighted variance"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyWeightedVariance())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-word-mass"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.wordMass"),
                H("Word Mass"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyWordmass())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed formula specifies the construction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discarded-occupancy-word-mass-nonneg"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions.wordMass_nonneg"),
                H("Word Mass nonneg"),
                StatementSource.FromAuthor(Disp(DiscardedOccupancyWordmassNonneg())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text("The displayed equality or implication states the law."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Statement1()
    {
        var n = F.Id("n");
        var p = F.Id("p");
        var oneMinus = Subtract(D(1), p);
        var floor = Seq(Lfloor, Sp, new Formula.Fraction(n, D(2)), Sp, Rfloor);
        var coefficient = new Formula.Fraction(Multiply(p,
            new Formula.Power(Seq(Open, oneMinus, Close), D(3))), D(2));
        var lower = Seq(Multiply(floor, coefficient), Sp, Leq, Sp,
            Call("variance", n, p, Subtract(n, D(1))));
        return All("n", Nat, All("p", Real,
            Seq(D(0), Lt, n, Sp, Implies, Sp, D(0), Sp, Leq, Sp, p, Sp, Implies, Sp,
                p, Sp, Leq, Sp, D(1), Sp, Implies, Sp, lower)));
    }

    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(x), Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula DiscardedOccupancyHistory() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Open,
        DefinitionDsl.Id("History"), Sp, F.Id("n"), Sp, F.Id("j"), Sp, Colon, Sp, DefinitionDsl.Id("Type"),
        Close, Sp, Eq, Sp, DefinitionDsl.Id("Fin"), Sp, F.Id("j"), Sp, To, Sp, DefinitionDsl.Id("Option"),
        Sp, Open, DefinitionDsl.Id("Fin"), Sp, F.Id("n"), Close);

    private static Formula DiscardedOccupancyA() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Open, F.Id("a"), Sp,
        F.Id("n"), Sp, F.Id("p"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Sp, Eq, Sp, D(1), Sp,
        Minus, Sp, F.Id("p"), Sp, Slash, Sp, DefinitionDsl.Id("val"), Sp, F.Id("n"));

    private static Formula DiscardedOccupancyABounds() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hn"), Colon, Sp, D(0), Sp, Lt, Sp, F.Id("n"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hp"), Colon, Sp, D(0), Sp, Leq, Sp, F.Id("p"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hpUpper"), Colon, Sp, F.Id("p"), Sp, Leq, Sp, D(1), Close, Comma, Sp, D(0), Sp,
        Leq, Sp, F.Id("a"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, Land, Sp, F.Id("a"), Sp, F.Id("n"), Sp,
        F.Id("p"), Sp, Leq, Sp, D(1));

    private static Formula DiscardedOccupancyAverage() =>
        Seq(
        Forall, Sp, Open, F.Id("E"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("AddCommMonoid"), Sp, F.Id("E"), CloseBracket, Sp, OpenBracket, Mathrm,
        Grp(F.Id("anonymous")), DefinitionDsl.Id("root"), Mathrm, Grp(F.Id("anonymous")), Dot,
        DefinitionDsl.Id("Module"), Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, F.Id("E"), CloseBracket, Sp,
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open, F.Id("f"),
        Colon, Sp, DefinitionDsl.Id("DiscardedOccupancy"), Dot, DefinitionDsl.Id("History"), Sp, F.Id("n"),
        Sp, F.Id("j"), Sp, To, Sp, F.Id("E"), Close, Comma, Sp, Open, DefinitionDsl.Id("average"), Sp,
        F.Id("E"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp, F.Id("f"), Sp, Colon, Sp, F.Id("E"),
        Close, Sp, Eq, Sp, Sum, Sp, Omega, Sp, Colon, Sp, DefinitionDsl.Id("DiscardedOccupancy"), Dot,
        DefinitionDsl.Id("History"), Sp, F.Id("n"), Sp, F.Id("j"), Comma, Sp, DefinitionDsl.Id("wordMass"),
        Sp, F.Id("n"), Sp, F.Id("p"), Sp, Omega, Sp, Cdot, Sp, F.Id("f"), Sp, Omega);

    private static Formula DiscardedOccupancyCount() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open, Omega,
        Colon, Sp, DefinitionDsl.Id("DiscardedOccupancy"), Dot, DefinitionDsl.Id("History"), Sp, F.Id("n"),
        Sp, F.Id("j"), Close, Comma, Sp, Open, DefinitionDsl.Id("count"), Sp, F.Id("n"), Sp, F.Id("j"), Sp,
        Omega, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Sp, Eq, Sp, Open,
        DefinitionDsl.Id("occupied"), Sp, F.Id("n"), Sp, F.Id("j"), Sp, Omega, Close, Dot,
        DefinitionDsl.Id("card"));

    private static Formula DiscardedOccupancyExpect() =>
        Seq(
        Forall, Sp, Open, F.Id("E"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("AddCommMonoid"), Sp, F.Id("E"), CloseBracket, Sp, OpenBracket, Mathrm,
        Grp(F.Id("anonymous")), DefinitionDsl.Id("root"), Mathrm, Grp(F.Id("anonymous")), Dot,
        DefinitionDsl.Id("Module"), Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, F.Id("E"), CloseBracket, Sp,
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open, F.Id("f"),
        Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, F.Id("E"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("expect"), Sp, F.Id("E"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp,
        F.Id("f"), Sp, Colon, Sp, F.Id("E"), Close, Sp, Eq, Sp, DefinitionDsl.Id("average"), Sp, F.Id("n"),
        Sp, F.Id("p"), Sp, F.Id("j"), Sp, DefinitionDsl.Id("fun"), Sp, Open, Omega, Sp, Colon, Sp,
        DefinitionDsl.Id("DiscardedOccupancy"), Dot, DefinitionDsl.Id("History"), Sp, F.Id("n"), Sp,
        F.Id("j"), Close, Sp, Mapsto, Sp, F.Id("f"), Sp, Open, DefinitionDsl.Id("count"), Sp, F.Id("n"), Sp,
        F.Id("j"), Sp, Omega, Close);

    private static Formula DiscardedOccupancyExpectAdd() =>
        Seq(
        Forall, Sp, Open, F.Id("E"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("AddCommMonoid"), Sp, F.Id("E"), CloseBracket, Sp, OpenBracket, Mathrm,
        Grp(F.Id("anonymous")), DefinitionDsl.Id("root"), Mathrm, Grp(F.Id("anonymous")), Dot,
        DefinitionDsl.Id("Module"), Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, F.Id("E"), CloseBracket, Sp,
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open, F.Id("f"),
        Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, F.Id("E"), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("g"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, F.Id("E"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("expect"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp,
        DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Sp,
        Mapsto, Sp, F.Id("f"), Sp, F.Id("x"), Sp, Plus, Sp, F.Id("g"), Sp, F.Id("x"), Close, Sp, Eq, Sp,
        DefinitionDsl.Id("expect"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp, F.Id("f"), Sp, Plus,
        Sp, DefinitionDsl.Id("expect"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp, F.Id("g"));

    private static Formula DiscardedOccupancyExpectCongr() =>
        Seq(
        Forall, Sp, Open, F.Id("E"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("AddCommMonoid"), Sp, F.Id("E"), CloseBracket, Sp, OpenBracket, Mathrm,
        Grp(F.Id("anonymous")), DefinitionDsl.Id("root"), Mathrm, Grp(F.Id("anonymous")), Dot,
        DefinitionDsl.Id("Module"), Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, F.Id("E"), CloseBracket, Sp,
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open, F.Id("f"),
        Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, F.Id("E"), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("g"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, F.Id("E"), Close, Comma, Sp, Forall,
        Sp, Open, F.Id("h"), Colon, Sp, Forall, Sp, F.Id("x"), Sp, Leq, Sp, F.Id("j"), Comma, Sp, F.Id("x"),
        Sp, Leq, Sp, F.Id("n"), Sp, To, Sp, F.Id("f"), Sp, F.Id("x"), Sp, Eq, Sp, F.Id("g"), Sp, F.Id("x"),
        Close, Comma, Sp, DefinitionDsl.Id("expect"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp,
        F.Id("f"), Sp, Eq, Sp, DefinitionDsl.Id("expect"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp,
        F.Id("g"));

    private static Formula DiscardedOccupancyExpectConst() =>
        Seq(
        Forall, Sp, Open, F.Id("E"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("AddCommMonoid"), Sp, F.Id("E"), CloseBracket, Sp, OpenBracket, Mathrm,
        Grp(F.Id("anonymous")), DefinitionDsl.Id("root"), Mathrm, Grp(F.Id("anonymous")), Dot,
        DefinitionDsl.Id("Module"), Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, F.Id("E"), CloseBracket, Sp,
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hn"), Colon, Sp, D(0), Sp, Lt, Sp, F.Id("n"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open, F.Id("c"),
        Colon, Sp, F.Id("E"), Close, Comma, Sp, Open, DefinitionDsl.Id("expect"), Sp, F.Id("n"), Sp,
        F.Id("p"), Sp, F.Id("j"), Sp, DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp, Colon, Sp,
        Seq(Mathbb, Grp(F.Id("N"))), Close, Sp, Mapsto, Sp, F.Id("c"), Close, Sp, Eq, Sp, F.Id("c"));

    private static Formula DiscardedOccupancyExpectMono() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hp"), Colon, Sp, D(0), Sp, Leq, Sp, F.Id("p"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hpUpper"), Colon, Sp, F.Id("p"), Sp, Leq, Sp, D(1), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("f"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))),
        Close, Comma, Sp, Forall, Sp, Open, F.Id("g"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp,
        Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open, F.Id("h"), Colon, Sp, Forall, Sp,
        F.Id("x"), Sp, Leq, Sp, F.Id("j"), Comma, Sp, F.Id("x"), Sp, Leq, Sp, F.Id("n"), Sp, To, Sp,
        F.Id("f"), Sp, F.Id("x"), Sp, Leq, Sp, F.Id("g"), Sp, F.Id("x"), Close, Comma, Sp,
        DefinitionDsl.Id("expect"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp, F.Id("f"), Sp, Leq, Sp,
        DefinitionDsl.Id("expect"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp, F.Id("g"));

    private static Formula DiscardedOccupancyExpectSmul() =>
        Seq(
        Forall, Sp, Open, F.Id("E"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("AddCommMonoid"), Sp, F.Id("E"), CloseBracket, Sp, OpenBracket, Mathrm,
        Grp(F.Id("anonymous")), DefinitionDsl.Id("root"), Mathrm, Grp(F.Id("anonymous")), Dot,
        DefinitionDsl.Id("Module"), Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, F.Id("E"), CloseBracket, Sp,
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open, F.Id("c"),
        Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open, F.Id("f"), Colon, Sp,
        Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, F.Id("E"), Close, Comma, Sp, Open,
        DefinitionDsl.Id("expect"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp,
        DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Sp,
        Mapsto, Sp, F.Id("c"), Sp, Cdot, Sp, F.Id("f"), Sp, F.Id("x"), Close, Sp, Eq, Sp, F.Id("c"), Sp,
        Cdot, Sp, DefinitionDsl.Id("expect"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp, F.Id("f"));

    private static Formula DiscardedOccupancyExpectSucc() =>
        Seq(
        Forall, Sp, Open, F.Id("E"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("AddCommMonoid"), Sp, F.Id("E"), CloseBracket, Sp, OpenBracket, Mathrm,
        Grp(F.Id("anonymous")), DefinitionDsl.Id("root"), Mathrm, Grp(F.Id("anonymous")), Dot,
        DefinitionDsl.Id("Module"), Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, F.Id("E"), CloseBracket, Sp,
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hn"), Colon, Sp, D(0), Sp, Lt, Sp, F.Id("n"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open, F.Id("f"),
        Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, F.Id("E"), Close, Comma, Sp,
        DefinitionDsl.Id("expect"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, Open, F.Id("j"), Sp, Plus, Sp, D(1),
        Close, Sp, F.Id("f"), Sp, Eq, Sp, DefinitionDsl.Id("expect"), Sp, F.Id("n"), Sp, F.Id("p"), Sp,
        F.Id("j"), Sp, DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb,
        Grp(F.Id("N"))), Close, Sp, Mapsto, Sp, Open, D(1), Sp, Minus, Sp, F.Id("q"), Sp, F.Id("n"), Sp,
        F.Id("p"), Sp, DefinitionDsl.Id("val"), Sp, F.Id("x"), Close, Sp, Cdot, Sp, F.Id("f"), Sp,
        F.Id("x"), Sp, Plus, Sp, F.Id("q"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, DefinitionDsl.Id("val"), Sp,
        F.Id("x"), Sp, Cdot, Sp, F.Id("f"), Sp, Open, F.Id("x"), Sp, Plus, Sp, D(1), Close);

    private static Formula DiscardedOccupancyExpectZeroTime() =>
        Seq(
        Forall, Sp, Open, F.Id("E"), Colon, Sp, DefinitionDsl.Id("Type"), Close, Comma, Sp, OpenBracket,
        DefinitionDsl.Id("AddCommMonoid"), Sp, F.Id("E"), CloseBracket, Sp, OpenBracket, Mathrm,
        Grp(F.Id("anonymous")), DefinitionDsl.Id("root"), Mathrm, Grp(F.Id("anonymous")), Dot,
        DefinitionDsl.Id("Module"), Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, F.Id("E"), CloseBracket, Sp,
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("f"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, F.Id("E"), Close, Comma, Sp,
        DefinitionDsl.Id("expect"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, D(0), Sp, F.Id("f"), Sp, Eq, Sp,
        F.Id("f"), Sp, D(0));

    private static Formula DiscardedOccupancyInsertthrow() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("s"), Colon, Sp, DefinitionDsl.Id("Finset"), Sp, Open, DefinitionDsl.Id("Fin"), Sp,
        F.Id("n"), Close, Close, Comma, Sp, Forall, Sp, Open, F.Id("a"), Colon, Sp,
        DefinitionDsl.Id("Option"), Sp, Open, DefinitionDsl.Id("Fin"), Sp, F.Id("n"), Close, Close, Comma,
        Sp, Open, DefinitionDsl.Id("insertThrow"), Sp, F.Id("n"), Sp, F.Id("s"), Sp, F.Id("a"), Sp, Colon,
        Sp, DefinitionDsl.Id("Finset"), Sp, Open, DefinitionDsl.Id("Fin"), Sp, F.Id("n"), Close, Close, Sp,
        Eq, Sp, DefinitionDsl.Id("match"), Sp, F.Id("x"), Sp, DefinitionDsl.Id("with"), Sp, Bar, Sp,
        DefinitionDsl.Id("none"), Sp, Mapsto, Sp, F.Id("s"), Sp, Bar, Sp, DefinitionDsl.Id("some"), Sp,
        F.Id("x"), Sp, Mapsto, Sp, DefinitionDsl.Id("insert"), Sp, F.Id("x"), Sp, F.Id("s"));

    private static Formula DiscardedOccupancyMean() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Open, DefinitionDsl.Id("mean"),
        Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Sp,
        Eq, Sp, DefinitionDsl.Id("expect"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp,
        DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Sp,
        Mapsto, Sp, DefinitionDsl.Id("val"), Sp, F.Id("x"));

    private static Formula DiscardedOccupancyMeanBounds() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hn"), Colon, Sp, D(0), Sp, Lt, Sp, F.Id("n"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hp"), Colon, Sp, D(0), Sp, Leq, Sp, F.Id("p"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hpUpper"), Colon, Sp, F.Id("p"), Sp, Leq, Sp, D(1), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, D(0), Sp, Leq, Sp,
        DefinitionDsl.Id("mean"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp, Land, Sp,
        DefinitionDsl.Id("mean"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp, Leq, Sp,
        DefinitionDsl.Id("val"), Sp, F.Id("n"));

    private static Formula DiscardedOccupancyMeanSucc() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hn"), Colon, Sp, D(0), Sp, Lt, Sp, F.Id("n"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, DefinitionDsl.Id("mean"), Sp,
        F.Id("n"), Sp, F.Id("p"), Sp, Open, F.Id("j"), Sp, Plus, Sp, D(1), Close, Sp, Eq, Sp, F.Id("a"), Sp,
        F.Id("n"), Sp, F.Id("p"), Sp, Cdot, Sp, DefinitionDsl.Id("mean"), Sp, F.Id("n"), Sp, F.Id("p"), Sp,
        F.Id("j"), Sp, Plus, Sp, F.Id("p"));

    private static Formula DiscardedOccupancyOccupied() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("a"), Colon, Sp, DefinitionDsl.Id("DiscardedOccupancy"), Dot, DefinitionDsl.Id("History"), Sp,
        F.Id("n"), Sp, F.Id("j"), Close, Comma, Sp, Open, DefinitionDsl.Id("occupied"), Sp, F.Id("n"), Sp,
        F.Id("j"), Sp, F.Id("a"), Sp, Colon, Sp, DefinitionDsl.Id("Finset"), Sp, Open,
        DefinitionDsl.Id("Fin"), Sp, F.Id("n"), Close, Close, Sp, Eq, Sp, DefinitionDsl.Id("Nat"), Dot,
        DefinitionDsl.Id("brecOn"), Sp, Open, DefinitionDsl.Id("motive"), Sp, Colon, Eq, Sp,
        DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Sp,
        Mapsto, Sp, DefinitionDsl.Id("DiscardedOccupancy"), Dot, DefinitionDsl.Id("History"), Sp, F.Id("n"),
        Sp, F.Id("x"), Sp, To, Sp, DefinitionDsl.Id("Finset"), Sp, Open, DefinitionDsl.Id("Fin"), Sp,
        F.Id("n"), Close, Close, Sp, DefinitionDsl.Id("xOne"), Sp, Open, DefinitionDsl.Id("occupied"), Dot,
        Mathrm, Grp(F.Id("anonymous")), F.Id("f"), Sp, F.Id("n"), Close, Sp, F.Id("x"));

    private static Formula DiscardedOccupancyQ() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("x"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Open, F.Id("q"), Sp, F.Id("n"),
        Sp, F.Id("p"), Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Sp, Eq, Sp,
        F.Id("p"), Sp, Cdot, Sp, Open, D(1), Sp, Minus, Sp, F.Id("x"), Sp, Slash, Sp,
        DefinitionDsl.Id("val"), Sp, F.Id("n"), Close);

    private static Formula DiscardedOccupancyQBounds() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("x"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hp"), Colon, Sp, D(0), Sp, Leq, Sp, F.Id("p"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hx"), Colon, Sp, D(0), Sp, Leq, Sp, F.Id("x"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hx"), Apos, Colon, Sp, F.Id("x"), Sp, Leq, Sp, DefinitionDsl.Id("val"), Sp,
        F.Id("n"), Close, Comma, Sp, D(0), Sp, Leq, Sp, F.Id("q"), Sp, F.Id("n"), Sp, F.Id("p"), Sp,
        F.Id("x"), Sp, Land, Sp, F.Id("q"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("x"), Sp, Leq, Sp,
        F.Id("p"));

    private static Formula DiscardedOccupancyThrowmass() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("a"), Colon, Sp, DefinitionDsl.Id("Option"), Sp, Open, DefinitionDsl.Id("Fin"), Sp, F.Id("n"),
        Close, Close, Comma, Sp, Open, DefinitionDsl.Id("throwMass"), Sp, F.Id("n"), Sp, F.Id("p"), Sp,
        F.Id("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Sp, Eq, Sp, DefinitionDsl.Id("match"),
        Sp, F.Id("x"), Sp, DefinitionDsl.Id("with"), Sp, Bar, Sp, DefinitionDsl.Id("none"), Sp, Mapsto, Sp,
        D(1), Sp, Minus, Sp, F.Id("p"), Sp, Bar, Sp, DefinitionDsl.Id("some"), Sp, DefinitionDsl.Id("val"),
        Sp, Mapsto, Sp, F.Id("p"), Sp, Slash, Sp, DefinitionDsl.Id("val"), Sp, F.Id("n"));

    private static Formula DiscardedOccupancyV() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("x"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Open, F.Id("v"), Sp, F.Id("n"),
        Sp, F.Id("p"), Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Sp, Eq, Sp,
        F.Id("q"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("x"), Sp, Cdot, Sp, Open, D(1), Sp, Minus, Sp,
        F.Id("q"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("x"), Close);

    private static Formula DiscardedOccupancyVBounds() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("x"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hp"), Colon, Sp, D(0), Sp, Leq, Sp, F.Id("p"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hpUpper"), Colon, Sp, F.Id("p"), Sp, Leq, Sp, D(1), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hx"), Colon, Sp, D(0), Sp, Leq, Sp, F.Id("x"), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hx"), Apos, Colon, Sp, F.Id("x"), Sp, Leq, Sp, DefinitionDsl.Id("val"), Sp,
        F.Id("n"), Close, Comma, Sp, D(0), Sp, Leq, Sp, F.Id("v"), Sp, F.Id("n"), Sp, F.Id("p"), Sp,
        F.Id("x"), Sp, Land, Sp, F.Id("v"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("x"), Sp, Leq, Sp, D(1));

    private static Formula DiscardedOccupancyVariance() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Open,
        DefinitionDsl.Id("variance"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp, Colon, Sp,
        Seq(Mathbb, Grp(F.Id("R"))), Close, Sp, Eq, Sp, DefinitionDsl.Id("expect"), Sp, F.Id("n"), Sp,
        F.Id("p"), Sp, F.Id("j"), Sp, DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp, Colon, Sp,
        Seq(Mathbb, Grp(F.Id("N"))), Close, Sp, Mapsto, Sp, Open, DefinitionDsl.Id("val"), Sp, F.Id("x"),
        Sp, Minus, Sp, DefinitionDsl.Id("mean"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Close, Sp,
        Caret, Sp, D(2));

    private static Formula DiscardedOccupancyVarianceLeTime() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hn"), Colon, Sp, D(0), Sp, Lt, Sp, F.Id("n"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hp"), Colon, Sp, D(0), Sp, Leq, Sp, F.Id("p"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hpUpper"), Colon, Sp, F.Id("p"), Sp, Leq, Sp, D(1), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp,
        DefinitionDsl.Id("variance"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp, Leq, Sp,
        DefinitionDsl.Id("val"), Sp, F.Id("j"));

    private static Formula DiscardedOccupancyVarianceNonneg() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hn"), Colon, Sp, D(0), Sp, Lt, Sp, F.Id("n"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hp"), Colon, Sp, D(0), Sp, Leq, Sp, F.Id("p"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hpUpper"), Colon, Sp, F.Id("p"), Sp, Leq, Sp, D(1), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, D(0), Sp, Leq, Sp,
        DefinitionDsl.Id("variance"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"));

    private static Formula DiscardedOccupancyWeightedVariance() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, DefinitionDsl.Id("hn"), Colon, Sp, D(0), Sp, Lt, Sp, F.Id("n"), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("m"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, DefinitionDsl.Id("variance"),
        Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("m"), Sp, Eq, Sp, Sum, Sp, F.Id("j"), Sp, InMacro, Sp,
        DefinitionDsl.Id("Finset"), Dot, DefinitionDsl.Id("range"), Sp, F.Id("m"), Comma, Sp, Open,
        F.Id("a"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, Caret, Sp, Open, F.Id("m"), Sp, Minus, Sp, Open,
        F.Id("j"), Sp, Plus, Sp, D(1), Close, Close, Close, Sp, Caret, Sp, D(2), Sp, Cdot, Sp,
        DefinitionDsl.Id("expect"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, F.Id("j"), Sp,
        DefinitionDsl.Id("fun"), Sp, Open, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Sp,
        Mapsto, Sp, F.Id("v"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, DefinitionDsl.Id("val"), Sp, F.Id("x"));

    private static Formula DiscardedOccupancyWordmass() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open, Omega, Colon,
        Sp, DefinitionDsl.Id("DiscardedOccupancy"), Dot, DefinitionDsl.Id("History"), Sp, F.Id("n"), Sp,
        F.Id("j"), Close, Comma, Sp, Open, DefinitionDsl.Id("wordMass"), Sp, F.Id("n"), Sp, F.Id("p"), Sp,
        F.Id("j"), Sp, Omega, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Sp, Eq, Sp, Prod, Sp,
        F.Id("i"), Sp, Colon, Sp, DefinitionDsl.Id("Fin"), Sp, F.Id("j"), Comma, Sp,
        DefinitionDsl.Id("throwMass"), Sp, F.Id("n"), Sp, F.Id("p"), Sp, Open, Omega, Sp, F.Id("i"), Close);

    private static Formula DiscardedOccupancyWordmassNonneg() =>
        Seq(
        Forall, Sp, Open, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("p"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hp"), Colon, Sp, D(0), Sp, Leq, Sp, F.Id("p"), Close, Comma, Sp, Forall, Sp, Open,
        DefinitionDsl.Id("hpUpper"), Colon, Sp, F.Id("p"), Sp, Leq, Sp, D(1), Close, Comma, Sp, Forall, Sp,
        Open, F.Id("j"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Close, Comma, Sp, Forall, Sp, Open, Omega,
        Colon, Sp, DefinitionDsl.Id("DiscardedOccupancy"), Dot, DefinitionDsl.Id("History"), Sp, F.Id("n"),
        Sp, F.Id("j"), Close, Comma, Sp, D(0), Sp, Leq, Sp, DefinitionDsl.Id("wordMass"), Sp, F.Id("n"), Sp,
        F.Id("p"), Sp, Omega);
}
