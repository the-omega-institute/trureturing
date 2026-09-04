using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Sharpness;

internal sealed class MaximalSpectralSharpnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spectral sharpness is the attained distance-normalized capacity, with its median-cut witness, qubit formula, endpoints, and data-processing law.",
        H("The Maximal Spectral Sharpness Theorem"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("maximal-spectral-sharpness"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Sharpness/MaximalSpectralSharpness."
                    + "maximal_spectral_sharpness"),
                H("Spectral sharpness is the attained normalized capacity"),
                StatementSource.FromAuthor(MaximalSharpnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let r be a nonnegative, nonincreasing, unit-sum spectrum in dimension "
                        + "N = n + 2. Its spectral sharpness Sharp(r) is one half the l1 distance "
                        + "from r to its reversal. For a nonincreasing observable spectrum a, "
                        + "D(a) is half its endpoint range. The first clause identifies D(a) as "
                        + "the least uniform bound on distance from a constant spectrum, so it is "
                        + "exactly the operator-norm distance from the observable to the center.")),
                    Paragraph(Text(
                        "Sharp(r) is the greatest attained value of C_a(r)/D(a) over noncentral "
                        + "nonincreasing observables. The explicit median-cut question Q_n has "
                        + "only plus-or-minus-one values, is nonincreasing, has D(Q_n) = 1, and "
                        + "attains the greatest value. Thus the variational maximum and the "
                        + "yes/no maximizer are both addressable parts of the public statement.")),
                    Paragraph(Text(
                        "For a two-point unit-sum spectrum q, Sharp(q) equals the square root of "
                        + "twice its quadratic purity minus one, the spectral form of the qubit "
                        + "Bloch radius. The same statement gives Sharp(r) = 1 exactly when the "
                        + "nonzero support has size at most N/2, and Sharp(r) = 0 exactly when r "
                        + "is uniform.")),
                    Paragraph(Text(
                        "Finally, if r = S r' for a doubly stochastic matrix S and both spectra "
                        + "are nonincreasing, then Sharp(r) <= Sharp(r'). This is the spectral "
                        + "majorization form of the unital-channel data-processing law. The proof "
                        + "uses the same median question on both sides and applies the frozen "
                        + "spectral-pairing comparison, rather than introducing a second channel "
                        + "or majorization carrier.")),
                    Paragraph(Text(
                        "Dimension at least two is encoded by N = n + 2 because the normalized "
                        + "ratio ranges over observables outside the center. The numerical trials "
                        + "and decimal certificate accompanying the source statement are empirical "
                        + "checks and are not theorem clauses."))),
                DescribeRole.Theorem))));

    private static Formula MaximalSharpnessFormula()
    {
        Formula n = F.Id("n");
        Formula dimension = Grp(n, Plus, D(2));
        Formula i = F.Id("i");
        Formula r = F.Id("r");
        Formula rPrime = Seq(r, Apos);
        Formula a = F.Id("a");
        Formula q = F.Id("q");
        Formula d = F.Id("d");
        Formula c = F.Id("c");
        Formula value = F.Id("v");
        Formula matrix = F.Id("S");
        Formula question = Seq(F.Id("Q"), Underscore, n);

        Formula Fin(Formula size) =>
            Seq(Operatorname, Grp(F.Id("Fin")), Open, size, Close);
        Formula RealType() => Seq(Mathbb, Grp(F.Id("R")));
        Formula At(Formula function, Formula index) =>
            Seq(function, Underscore, index);
        Formula Apply(Formula function, Formula argument) =>
            Seq(function, Open, argument, Close);
        Formula Sharp(Formula spectrum) =>
            Seq(Operatorname, Grp(F.Id("Sharp")), Open, spectrum, Close);
        Formula Distance(Formula observable) =>
            Seq(F.Id("D"), Open, observable, Close);
        Formula Capacity(Formula observable, Formula spectrum) =>
            Seq(F.Id("C"), Underscore, Grp(observable), Open, spectrum, Close);
        Formula Antitone(Formula function) =>
            Seq(Operatorname, Grp(F.Id("Antitone")), Open, function, Close);
        Formula SumValues(Formula function) =>
            Seq(Sum, Underscore, i, At(function, i));
        Formula FinFunctionType(Formula size) =>
            Seq(Fin(size), To, RealType());

        Formula centerBounds = Seq(
            Left, OpenBrace, d, Sp, Mid, Sp,
            Exists, Sp, c, Sp, InMacro, Sp, RealType(), Comma, Sp,
            Forall, Sp, i, Comma, Sp,
            Lvert, Sp, At(a, i), Minus, c, Sp, Rvert, Sp, Le, Sp, d,
            Right, CloseBrace);

        Formula normalizedValues = Seq(
            Left, OpenBrace, value, Sp, Mid, Sp,
            Exists, Sp, a, Colon, Sp, FinFunctionType(dimension), Comma, Sp,
            Antitone(a), Sp, Land, Sp, D(0), Sp, Lt, Sp, Distance(a), Sp, Land, Sp,
            Frac, Grp(Capacity(a, r)), Grp(Distance(a)), Eq, value,
            Right, CloseBrace);

        Formula support = Seq(
            Lvert, Left, OpenBrace, i, Sp, Mid, Sp,
            At(r, i), Sp, Neq, Sp, D(0), Right, CloseBrace, Rvert);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, n, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            r, Colon, Sp, FinFunctionType(dimension), Comma, RowBreak,
            Open, Forall, Sp, i, Comma, Sp, D(0), Sp, Le, Sp, At(r, i), Close,
            Sp, Land, Sp, Antitone(r), Sp, Land, Sp,
            SumValues(r), Eq, D(1), Sp, Rightarrow, RowBreak,
            Open,
            Forall, Sp, a, Colon, Sp, FinFunctionType(dimension), Comma, Sp,
            Antitone(a), Sp, Rightarrow, Sp,
            Operatorname, Grp(F.Id("IsLeast")), Open,
            centerBounds, Comma, Sp, Distance(a), Close,
            Close, Sp, Land, RowBreak,
            Operatorname, Grp(F.Id("IsGreatest")), Open,
            normalizedValues, Comma, Sp, Sharp(r), Close, Sp, Land, RowBreak,
            Open,
            Open, Forall, Sp, i, Comma, Sp,
            Apply(question, i), Eq, D(1), Sp, Lor, Sp,
            Apply(question, i), Eq, Minus, D(1), Close,
            Sp, Land, Sp, Antitone(question), Sp, Land, Sp,
            Frac, Grp(Capacity(question, r)), Grp(Distance(question)),
            Eq, Sharp(r), Close, Sp, Land, RowBreak,
            Open,
            Forall, Sp, q, Colon, Sp, FinFunctionType(D(2)), Comma, Sp,
            SumValues(q), Eq, D(1), Sp, Rightarrow, Sp,
            Sharp(q), Eq, Sqrt, Grp(
                D(2), Sum, Underscore, i, At(q, i), Caret, Grp(D(2)), Minus, D(1)),
            Close, Sp, Land, RowBreak,
            Open, Sharp(r), Eq, D(1), Sp, Iff, Sp,
            support, Sp, Le, Sp, Frac, Grp(dimension), Grp(D(2)), Close,
            Sp, Land, RowBreak,
            Open, Sharp(r), Eq, D(0), Sp, Iff, Sp,
            Forall, Sp, i, Comma, Sp,
            At(r, i), Eq, Frac, Grp(D(1)), Grp(dimension), Close,
            Sp, Land, RowBreak,
            Open,
            Forall, Sp, rPrime, Colon, Sp, FinFunctionType(dimension), Comma, Sp,
            matrix, Colon, Sp,
            Operatorname, Grp(F.Id("Matrix")), Open,
            Fin(dimension), Comma, Sp, Fin(dimension), Comma, Sp, RealType(), Close,
            Comma, Sp, Antitone(rPrime), Sp, Land, Sp,
            Operatorname, Grp(F.Id("DS")), Open, matrix, Close, Sp, Land, Sp,
            r, Eq, matrix, rPrime, Sp, Rightarrow, Sp,
            Sharp(r), Sp, Le, Sp, Sharp(rPrime), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
