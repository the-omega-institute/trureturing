using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.Hardness;

internal sealed class RationalSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var hurwitz = LibraryNoteRef.Create("D5/L/Tower/hurwitz1891irrational");
        var carrier = F.Id("X");
        var types = F.Id("Type");
        var reals = F.Id("R");
        var beta = F.Id("beta");
        var x = F.Id("x");
        var hardness = Call("hardnessSpectrum", beta);
        var hurwitzConstant = new Formula.Fraction(Num(1), Call("sqrt", Num(5)));

        var spectrumDefinition = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("X"), types),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("beta"),
                    new Formula.TypeArrow(carrier, reals)),
            ],
            Equal(hardness, Call("range", beta)));
        var badlyApproximableDefinition = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("X"), types),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("beta"),
                    new Formula.TypeArrow(carrier, reals)),
                new Formula.BoundVariable(FormulaIdentifier.Create("x"), carrier),
            ],
            new Formula.Logic(
                Call("BadlyApproximable", beta, x),
                FormulaLogicOperator.Iff,
                new Formula.Relation(
                    Num(0),
                    FormulaRelationOperator.LessThan,
                    Call("apply", beta, x))));
        var sharpBottom = Call(
            "IsLeast",
            Call("upperBounds", Call("hardnessSpectrum", F.Id("rationalHardness"))),
            hurwitzConstant);
        var goldenAttainment = Equal(
            Call("rationalHardness", F.Id("goldenRatioPoint")),
            hurwitzConstant);
        var statement = new Formula.Logic(
            Seq(Open, spectrumDefinition, Close),
            FormulaLogicOperator.And,
            new Formula.Logic(
                Seq(Open, badlyApproximableDefinition, Close),
                FormulaLogicOperator.And,
                new Formula.Logic(
                    sharpBottom,
                    FormulaLogicOperator.And,
                    goldenAttainment)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The rational-tower hardness spectrum has the sharp Hurwitz extremum attained by the golden tail.",
            H("Rational-Tower Hardness Spectrum"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("rational-tower-hardness-spectrum"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Hardness/RationalSpectrum."
                        + "rational_tower_hardness_spectrum"),
                    H("Definition 4.1 and the sharp Hurwitz extremum"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromLiterature(hurwitz),
                    Blocks(
                        Paragraph(Text(
                            "For any point type X and hardness function beta, the hardness spectrum "
                            + "is the range of beta, and BadlyApproximable(beta,x) holds exactly "
                            + "when beta(x) is positive. These are the first two, definitional, "
                            + "clauses of the packaged declaration.")),
                        Paragraph(Text(
                            "A rational-tower point is represented in normalized regular-continued-"
                            + "fraction coordinates by positive partial quotients and the exact "
                            + "forward- and backward-tail recurrences. Its approximation coefficient "
                            + "is q_n^2 times the convergent error, and rationalHardness is its "
                            + "filter liminf.")),
                        Paragraph(Text(
                            "The sharp proof is not assumed by the point structure. If the center "
                            + "coefficient exceeds 1/sqrt(5), a factorization using sqrt(5)^2=5 "
                            + "forces one adjacent coefficient below that constant. Every block of "
                            + "three indices therefore supplies a hit arbitrarily far out, yielding "
                            + "the universal liminf upper bound.")),
                        Paragraph(Text(
                            "The all-one continued-fraction tail is the golden-ratio class. Its two "
                            + "normalized tails equal the inverse golden ratio, so every coefficient "
                            + "is exactly 1/sqrt(5). Consequently the set of upper bounds of the "
                            + "hardness spectrum has 1/sqrt(5) as its least element, and the golden "
                            + "point attains that value. This is the order-correct meaning of the "
                            + "source phrase 'bottom of the supremum structure'.")),
                        Paragraph(Text(
                            "The D5 formal library was searched first. Its golden-ratio lower bound "
                            + "and Fibonacci approximation limit cover only the extremal point, not "
                            + "the universal Hurwitz bound. Pinned Mathlib, Loogle, LeanSearch, and "
                            + "GitHub Lean code supplied Dirichlet and Legendre results but no exact "
                            + "sharp theorem, so the local proof fills the missing universal layer."))),
                    DescribeRole.Theorem))));
    }
}
