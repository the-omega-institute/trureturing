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
                "Let S be a nonempty finite set of indices with real frequencies γ and "
                + "positive weights w on S. A subset U of S is compatible if every integer "
                + "relation on U has coefficient sum divisible by four. The deleted fraction P "
                + "is the minimum of the total weight on S minus U divided by the total weight "
                + "on S over compatible U. The empty subset is compatible. The deficit D is one "
                + "minus the supremum over t in T of the weighted sine score "
                + "Σⱼ wⱼ sin(γⱼ t) divided by the total weight. The real time set T contains "
                + "an upper ray [a,∞) for some real a.")),
            Describe.Lean(
                DescribeId.Create("weighted-compatible-deletion"),
                DeclarationHandle.Create("D5/S3/Fourier/ShortPhaseRelations.weighted_deletion_bounds"),
                H("Weighted comparison"),
                StatementSource.FromAuthor(WeightedFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume H ≥ 1 and that each incompatible U contains an integer relation "
                        + "of coefficient sum nonzero modulo four and coefficient ℓ¹ length at "
                        + "most H. At each time retain exactly the coordinates with sine loss "
                        + "strictly below 1/H². If a short incompatible relation were supported "
                        + "there, its character on the orbit would be one and its value at the "
                        + "common quarter phase would be a nontrivial fourth root of unity, "
                        + "at distance at least √2 from one. The coordinate chord squared "
                        + "equals twice the sine loss. The character chord bound "
                        + "would therefore give a distance strictly below H · √2/H = √2. "
                        + "The retained set is compatible. Its complement costs at "
                        + "least P of the total weight and each deleted coordinate pays at "
                        + "least 1/H² of its weight.")),
                    Paragraph(Text(
                        "For any compatible U, the orbit closure on the retained coordinates "
                        + "contains the common quarter phase on every upper ray. The retained "
                        + "score approaches its full weight by continuity. The omitted score "
                        + "is bounded below by minus the omitted weight, so the total loss is "
                        + "at most twice the omitted weight in the infimum. Minimizing over U "
                        + "gives the upper bound independently of the short relation condition.")),
                    Paragraph(Text(
                        "The short relation condition for finite sets of actual ζ ordinates "
                        + "remains open."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("consecutive-pair-separation"),
                DeclarationHandle.Create("D5/S3/Fourier/ShortPhaseRelations.consecutive_pair_separation"),
                H("Quadratic separation for consecutive frequencies"),
                StatementSource.FromAuthor(PairFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take the frequencies (n,n + 1) with positive integer n and any equal "
                    + "positive weights. The relation (n + 1,−n) has coefficient sum one "
                    + "and length H = 2n + 1. The full pair is incompatible, and every "
                    + "proper subset is compatible, so the short relation condition holds at "
                    + "H and the deleted fraction is 1/2. At time π/H the phases are "
                    + "π/2 ± π/(2H). Adding nonnegative integral multiples of 2π puts "
                    + "this time in any upper ray while preserving the score. The pointwise "
                    + "deficit there is 1 − cos(π/(2H)), at most π²/(8H²). The weighted "
                    + "lower bounds give the two corresponding lower constants."))),
                DescribeRole.Theorem))));

    private static Formula P => F.Id("P");
    private static Formula Deficit => F.Id("D");
    private static Formula H2 => new Formula.Power(F.Id("H"), D(2));
    private static Formula Frac(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula AtMost(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);

    private static Formula WeightedFormula() =>
        Disp(And(AtMost(Frac(P, Mul(D(2), H2)), Deficit),
            And(AtMost(Deficit, Mul(D(2), P)), AtMost(Frac(P, H2), Deficit))));

    private static Formula PairFormula() =>
        Disp(And(Equal(P, Frac(D(1), D(2))),
            And(Call("Short", F.Id("S"), F.Id("g"), F.Id("H")),
                And(AtMost(Frac(D(1), Mul(D(4), H2)), Deficit),
                    And(AtMost(Deficit, Frac(new Formula.Power(Pi, D(2)), Mul(D(8), H2))),
                        AtMost(Frac(D(1), Mul(D(2), H2)), Deficit))))));
}
