using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MeasureSeparation;

internal sealed class ZeroBayesResidualCriterionDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Observer/MeasureSeparation/ZeroBayesResidualCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal-prior statistical residual vanishes exactly when the transcript laws are "
            + "mutually singular.",
        H("Zero Bayes Residual Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("equal-prior-statistical-residual"),
                DeclarationHandle.Create(DeclarationPrefix + "statisticalResidual"),
                H("Statistical residual is half the common mass"),
                StatementSource.FromAuthor(DefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The infimum of two measures is their canonical common mass. For two "
                        + "probability laws, half of its mass on the full transcript space is "
                        + "the equal-prior optimal binary error, equivalently the Le Cam "
                        + "one-minus-total-variation formula."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zero-statistical-residual-iff-mutually-singular"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "statistical_residual_eq_zero_iff_mutually_singular"),
                H("Zero residual is equivalent to mutual singularity"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The transcript carrier is arbitrary and both state-indexed laws are "
                            + "probability measures on its measurable structure.")),
                    Paragraph(Text(
                        "Zero residual is zero total common mass. That is exactly a zero "
                            + "measure infimum, hence lattice disjointness; the pinned Mathlib "
                            + "equivalence identifies disjoint measures with mutually singular "
                            + "measures."))),
                DescribeRole.Theorem))));

    private static Formula DefinitionFormula()
    {
        Formula transcript = F.Id("Omega");
        Formula probabilityX = Probability(F.Id("x"));
        Formula probabilityY = Probability(F.Id("y"));
        Formula commonMass = Call(
            "measureReal",
            Call("measureInf", probabilityX, probabilityY),
            F.Id("univ"));
        Formula residual = Call("statisticalResidual", probabilityX, probabilityY);
        return Disp(Seq(
            Forall, Sp, transcript, Colon, Sp, Call("Type"), Comma, Sp,
            OpenBracket, Call("MeasurableSpace", transcript), CloseBracket,
            Comma, RowBreak, Grp(),
            probabilityX, Comma, Sp, probabilityY, Colon, Sp,
            Call("Measure", transcript), Comma, RowBreak, Grp(),
            residual, Sp, Eq, Sp,
            new Formula.Fraction(commonMass, D(2)), Dot));
    }

    private static Formula TheoremFormula()
    {
        Formula transcript = F.Id("Omega");
        Formula probabilityX = Probability(F.Id("x"));
        Formula probabilityY = Probability(F.Id("y"));
        Formula assumptions = new Formula.Logic(
            Call("ProbabilityMeasure", probabilityX),
            FormulaLogicOperator.And,
            Call("ProbabilityMeasure", probabilityY));
        Formula criterion = new Formula.Logic(
            new Formula.Relation(
                Call("statisticalResidual", probabilityX, probabilityY),
                FormulaRelationOperator.Equal,
                D(0)),
            FormulaLogicOperator.Iff,
            Call("MutuallySingular", probabilityX, probabilityY));
        return Disp(Seq(
            Forall, Sp, transcript, Colon, Sp, Call("Type"), Comma, Sp,
            OpenBracket, Call("MeasurableSpace", transcript), CloseBracket,
            Comma, RowBreak, Grp(),
            probabilityX, Comma, Sp, probabilityY, Colon, Sp,
            Call("Measure", transcript), Comma, RowBreak, Grp(),
            assumptions, Sp, Rightarrow, Sp, criterion, Dot));
    }

    private static Formula Probability(Formula state) =>
        new Formula.Subscript(F.Id("P"), state);
}
