using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.LinearMemory;

internal sealed class EpsilonSelfDimensionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/LinearMemory/EpsilonSelfDimension."
            + "epsilon_self_dimension_eq_threshold_count";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a decreasing singular-value profile, epsilon self-dimension is the number of "
            + "singular values strictly above epsilon.",
        H("Epsilon Self-Dimension"),
        Blocks(Describe.Lean(
            DescribeId.Create("epsilon-self-dimension-threshold-count"),
            DeclarationHandle.Create(Declaration),
            H("The first acceptable rank equals the strict threshold count"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The Eckart-Young approximation identity is an explicit premise. The proof "
                        + "uses only the antitone order of the zero-indexed singular values: the "
                        + "values strictly above epsilon form the initial interval before the "
                        + "first acceptable rank.")),
                Paragraph(Text(
                    "Nonemptiness of the acceptable-rank set is explicit, so the minimum has no "
                        + "empty-set convention. Zero-based sigma(k) corresponds to the source's "
                        + "one-based sigma_(k+1), and strict greater-than complements less-than-or-"
                        + "equal at equality thresholds."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula sigma = F.Id("sigma");
        Formula error = F.Id("e");
        Formula epsilon = F.Id("epsilon");
        Formula index = F.Id("i");
        Formula rank = F.Id("k");
        Formula naturals = F.Id("N");
        Formula errorAtRank = Apply(error, rank);
        Formula sigmaAtRank = Apply(sigma, rank);
        Formula sigmaAtIndex = Apply(sigma, index);
        Formula acceptable = Seq(
            OpenBrace, rank, Sp, InMacro, Sp, naturals, Sp, Mid, Sp,
            errorAtRank, Sp, Leq, Sp, epsilon, CloseBrace);
        Formula above = Seq(
            OpenBrace, index, Sp, InMacro, Sp, naturals, Sp, Mid, Sp,
            epsilon, Sp, Lt, Sp, sigmaAtIndex, CloseBrace);
        Formula nonnegative = Grp(Seq(
            Forall, Sp, index, Sp, InMacro, Sp, naturals, Comma, Sp,
            D(0), Sp, Leq, Sp, sigmaAtIndex));
        Formula eventuallyAcceptable = Grp(Seq(
            Exists, Sp, rank, Sp, InMacro, Sp, naturals, Comma, Sp,
            errorAtRank, Sp, Leq, Sp, epsilon));
        Formula eckartYoung = Grp(Seq(
            Forall, Sp, rank, Sp, InMacro, Sp, naturals, Comma, Sp,
            errorAtRank, Sp, Eq, Sp, sigmaAtRank));

        return Disp(Seq(
            Forall, Sp, sigma, Comma, Sp, error, Colon, Sp,
            naturals, Sp, To, Sp, F.Id("R"), Comma, Sp,
            epsilon, Sp, InMacro, Sp, F.Id("R"), Comma, RowBreak, Grp(),
            Apply("Antitone", sigma), Sp, Land, Sp,
            nonnegative, Sp, Land, RowBreak, Grp(),
            eventuallyAcceptable, Sp, Land, RowBreak, Grp(),
            eckartYoung, Sp, Rightarrow, RowBreak, Grp(),
            Apply("min", acceptable), Sp, Eq, Sp, Apply("ncard", above), Dot));
    }

    private static Formula Apply(string name, params Formula[] arguments) =>
        Apply(F.Id(name), arguments);

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var argumentIndex = 0; argumentIndex < arguments.Length; argumentIndex++)
        {
            if (argumentIndex > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[argumentIndex]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
