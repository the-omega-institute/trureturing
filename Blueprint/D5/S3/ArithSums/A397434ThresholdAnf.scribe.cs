using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class A397434ThresholdAnfDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Oeis =
        LibraryNoteRef.Create("D5/L/ArithSums/oeis2026a397434");
    private static readonly LibraryNoteRef ThresholdAnf =
        LibraryNoteRef.Create("D5/L/ArithSums/meaux2021threshold");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reduced-coefficient count sequence has adjacent values equal "
            + "exactly when the lower dimension is two modulo four.",
        H("A397434: adjacent reduced-coefficient counts"),
        Blocks(
            Paragraph(Text(
                "The Lean module defines a(n) from reducedCoeffBit, and "
                    + "thresholdAnfSupport filters that same reduced bit. It proves the "
                    + "adjacent classification for this reduced-coefficient count "
                    + "sequence. The intended identification with the OEIS ANF support "
                    + "counts uses Meaux's ANF coefficient reduction, stated separately "
                    + "below, but the main proof does not consume that declaration; the "
                    + "Boolean-function -> Mobius-coefficients -> reduced-bit -> "
                    + "support-count semantic bridge is therefore not machine-closed "
                    + "in this module.")),
            Describe.Lean(
                DescribeId.Create("threshold-anf-coefficient-reduction"),
                DeclarationHandle.Create(
                    "D5/S3/ArithSums/A397434ThresholdAnf."
                        + "threshold_anf_coefficient_reduction"),
                H("Threshold coefficients reduce to one binomial coefficient"),
                StatementSource.FromAuthor(CoefficientReduction()),
                AssessedProvenance.FromLiterature(ThresholdAnf),
                Blocks(
                    Paragraph(Text(
                        "Boolean-lattice Mobius inversion gives the sum of choose(d,j) "
                            + "from j=t through d. The complete binomial sum vanishes in "
                            + "characteristic two, and Pascal cancellation leaves "
                            + "choose(d-1,t-1)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("adjacent-support-count-classification"),
                DeclarationHandle.Create(
                    "D5/S3/ArithSums/A397434ThresholdAnf.a_eq_succ_iff_mod_four"),
                H("Adjacent counts agree exactly at residue two modulo four"),
                StatementSource.FromAuthor(AdjacentEquality()),
                AssessedProvenance.FromRepo(Oeis),
                Blocks(
                    Paragraph(Text(
                        "The direct definitions identify the filtered reduced-bit "
                            + "support cardinality with the binomially weighted count "
                            + "defining a. The two cardinality statements are used when "
                            + "deriving the exact difference between adjacent even and "
                            + "odd rows.")),
                    Paragraph(Text(
                        "For an even lower dimension 2m, the difference is twice a nonnegative "
                            + "binomial sum over degrees d for which both choose(d-1,m) and "
                            + "choose(d,m) are odd. This degree set is empty for odd m; for "
                            + "positive even m it contains m+1, making the sum positive.")),
                    Paragraph(Text(
                        "At an odd lower dimension, adding a variable contributes a positive "
                            + "shifted row, so equality is impossible. Combining the odd and "
                            + "even cases gives the residue-class characterization."))),
                DescribeRole.Theorem))));

    private static Formula CoefficientReduction()
    {
        Formula t = F.Id("t");
        Formula d = F.Id("d");
        Formula positive = And(LessThanOrEqual(F.D(1), t), LessThanOrEqual(F.D(1), d));
        Formula rhs = Call("cast", Call("choose", Subtract(d, F.D(1)), Subtract(t, F.D(1))),
            Call("ZMod", F.D(2)));
        Formula equality = Equal(Call("thresholdAnfCoeff", t, d), rhs);
        return F.Disp(new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("t"), Naturals(),
            new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("d"), Naturals(),
                new Formula.Logic(positive, FormulaLogicOperator.Implies, equality))));
    }

    private static Formula AdjacentEquality()
    {
        Formula n = F.Id("n");
        Formula left = Equal(Call("a", n), Call("a", Add(n, F.D(1))));
        Formula right = Equal(new Formula.Modulo(n, F.D(4)), F.D(2));
        Formula conclusion = new Formula.Logic(left, FormulaLogicOperator.Iff, right);
        return F.Disp(new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"), Naturals(),
            new Formula.Logic(LessThanOrEqual(F.D(1), n),
                FormulaLogicOperator.Implies, conclusion)));
    }

    private static Formula Naturals() => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
}
