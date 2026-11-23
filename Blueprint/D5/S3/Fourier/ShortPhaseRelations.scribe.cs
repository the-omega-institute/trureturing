using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class ShortPhaseRelationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Short incompatible integer relations compare the weighted cost of deletion "
        + "with the common-time sine deficit.",
        H("Short Integer Relations and Weighted Compatible Deletion"),
        Blocks(
            Paragraph(Text(
                "Let S be a finite set of indices with real frequencies γ and nonnegative "
                + "weights w on S. The total weight is positive so the normalized quantities "
                + "are defined. A subset U of S is compatible if every integer "
                + "relation on U has coefficient sum divisible by four. The deleted fraction P "
                + "is the minimum of the total weight on S minus U divided by the total weight "
                + "on S over compatible U. The empty subset is compatible. The deficit D is one "
                + "minus the supremum over t in T of the weighted sine score "
                + "Σⱼ wⱼ sin(γⱼ t) divided by the total weight.")),
            Describe.Lean(
                DescribeId.Create("weighted-compatible-deletion"),
                DeclarationHandle.Create("D5/S3/Fourier/ShortPhaseRelations.weighted_deletion_bounds"),
                H("Weighted comparison"),
                StatementSource.FromAuthor(WeightedFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the lower bound take a nonempty real time set T and H > 0. "
                        + "Short(S,g,H) says that each incompatible U contains an integer relation "
                        + "of coefficient sum nonzero modulo four and coefficient ℓ¹ length at "
                        + "most H. At each time retain exactly the coordinates with sine loss "
                        + "strictly below 1/H². If a short incompatible relation were supported "
                        + "there, its character on the orbit would be one and its value at the "
                        + "common quarter phase would be a nontrivial fourth root of unity, "
                        + "at distance at least √2 from one. The coordinate chord squared "
                        + "equals twice the sine loss. The character chord bound "
                        + "would therefore give a distance strictly below H · √2/H = √2. "
                        + "The orbit character, quarter character, and chord identity are supplied "
                        + "by Weighted Integer Relations. The retained set is compatible. Its "
                        + "complement costs at least P of the total weight and each deleted coordinate pays at "
                        + "least 1/H² of its weight.")),
                    Paragraph(Text(
                        "For the upper bound assume that T contains an upper ray. For any "
                        + "compatible U, the orbit closure on the retained coordinates "
                        + "contains the common quarter phase on every upper ray. The retained "
                        + "score approaches its full weight by continuity. The omitted score "
                        + "is bounded below by minus the omitted weight, so the total loss is "
                        + "at most twice the omitted weight in the infimum. Minimizing over U "
                        + "gives the upper bound for any such T.")),
                    Paragraph(Text(
                        "A finite H exists for every fixed finite frequency system. Choose one "
                        + "incompatible witness per incompatible subset and take the maximum "
                        + "of their lengths and 1. For actual ζ ordinates, the open question "
                        + "is quantitative control of H, such as a uniform bound or a bound "
                        + "in terms of the ordinate cutoff strong enough to yield an asymptotic conclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("consecutive-pair-separation"),
                DeclarationHandle.Create("D5/S3/Fourier/ShortPhaseRelations.consecutive_pair_separation"),
                H("Quadratic separation for consecutive frequencies"),
                StatementSource.FromAuthor(PairFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take the frequencies (n,n + 1) with n a natural number and any equal "
                    + "positive weights. The time set T contains an upper ray. The relation "
                    + "(n + 1,−n) has coefficient sum one and length H = 2n + 1. "
                    + "The full pair is incompatible, and the singleton {n + 1} is compatible, "
                    + "so the deleted fraction is 1/2. For n > 0 both singletons are "
                    + "compatible. At n = 0 the singleton {0} has a length-one incompatible "
                    + "relation. Thus the short relation condition holds at H for all n. "
                    + "At time π/H the phases are "
                    + "π/2 ± π/(2H). Adding nonnegative integral multiples of 2π puts "
                    + "this time in any upper ray while preserving the score. The pointwise "
                    + "deficit there is 1 − cos(π/(2H)), at most π²/(8H²). The weighted "
                    + "lower bound gives 1/(2H²)."))),
                DescribeRole.Theorem))));

    private static Formula P => F.Id("P");
    private static Formula Deficit => F.Id("D");
    private static Formula Length => F.Id("H");
    private static Formula Time => F.Id("T");
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula H2 => new Formula.Power(Length, D(2));
    private static Formula Short => Call("Short", F.Id("S"), F.Id("g"), Length);
    private static Formula CosineBound => new Formula.Binary(
        D(1), FormulaBinaryOperator.Subtract, Call("cos", Frac(Pi, Mul(D(2), Length))));
    private static Formula Frac(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula AtMost(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Parens(Formula x) => Seq(Open, x, Close);
    private static Formula Quantify(FormulaQuantifier quantifier, string name, Formula body) =>
        new Formula.BindMany(quantifier, [new Formula.BoundVariable(FormulaIdentifier.Create(name), Reals)], body);

    private static Formula WeightedFormula()
    {
        var nonempty = new Formula.Relation(Time, FormulaRelationOperator.NotEqual, Emptyset);
        var positiveLength = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, Length);
        var ray = new Formula.Relation(Seq(OpenBracket, F.Id("a"), Comma, Infty, Close),
            FormulaRelationOperator.SubsetOf, Time);
        var lower = Quantify(FormulaQuantifier.ForAll, "H",
            Imp(And(nonempty, And(positiveLength, Short)), AtMost(Frac(P, H2), Deficit)));
        var upper = Imp(Parens(Quantify(FormulaQuantifier.Exists, "a", ray)), AtMost(Deficit, Mul(D(2), P)));
        return Disp(And(Parens(lower), Parens(upper)));
    }

    private static Formula PairFormula()
    {
        var lower = AtMost(Frac(D(1), Mul(D(2), H2)), Deficit);
        var quadraticBound = Frac(new Formula.Power(Pi, D(2)), Mul(D(8), H2));
        var upper = And(AtMost(Deficit, CosineBound), AtMost(CosineBound, quadraticBound));
        return Disp(And(Equal(P, Frac(D(1), D(2))), And(Short, And(lower, upper))));
    }
}
