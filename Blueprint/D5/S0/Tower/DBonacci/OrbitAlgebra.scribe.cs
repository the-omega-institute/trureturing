using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacci;

internal sealed class DBonacciOrbitAlgebraDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var d = Id("d");
        var q = Id("Q");
        var k = Id("k");
        var x = Id("x");
        var letter = Id("letter");
        var leftArm = Id("L");
        var rightArm = Id("R");
        var beta = Call("dbonacciPerronRoot", d);
        var predecessor = Call("predecessor", letter);
        var top = Call("topGapLetter", d);

        Formula OrbitGap(Formula level, Formula gapLetter, Formula left, Formula right) =>
            Call("IsDBonacciLetterOrbitGap", d, level, x, gapLetter, left, right);

        var rightChildFormula = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("letter"),
            Call("nonzeroGapLetter", d),
            Equal(
                Call("rightChild", OrbitGap(q, letter, leftArm, rightArm)),
                OrbitGap(
                    Add(q, Num(1)),
                    predecessor,
                    Subtract(Multiply(beta, leftArm), Num(1)),
                    Multiply(beta, rightArm))));
        var leftChildFormula = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("letter"),
            Call("nonzeroGapLetter", d),
            Equal(
                Call("leftChild", OrbitGap(q, letter, leftArm, rightArm)),
                OrbitGap(
                    Add(q, Num(1)),
                    top,
                    Multiply(beta, leftArm),
                    Subtract(Num(1), Multiply(beta, leftArm)))));
        var periodFormula = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("k"),
            Id("N"),
            Call("topPredecessorPeriodTwoOrbit", d, k, x));
        var fourFormula = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("k"),
            Id("N"),
            Call("fourChampionGapOrbit", k));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Typed d-bonacci refinement isolates the uniform interval algebra of the period-two orbit.",
            H("D-Bonacci Orbit Algebra"),
            Blocks(
                Paragraph(Text(
                    "A gap is indexed by a letter in Fin d and carries its two endpoint arms. "
                    + "Strict monotonicity of gap lengths identifies the geometric substitution "
                    + "witness with that same typed letter.")),
                Describe.Lean(
                    DescribeId.Create("general-right-child-orbit-algebra"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/OrbitAlgebra.letter_orbit_gap_right_child"),
                    H("Right-child affine arm law"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(rightChildFormula)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For every order d at least two and every nonzero gap letter, the right "
                        + "child has predecessor letter. Its normalized arms are beta times the "
                        + "old arms, with one unit removed from the left arm."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("general-left-child-orbit-algebra"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/OrbitAlgebra.letter_orbit_gap_left_child"),
                    H("Left-child affine arm law"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(leftChildFormula)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The left child returns to the top letter. Its left arm is beta times "
                        + "the old left arm and its right arm is the complementary quantity."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("general-top-predecessor-period-two-orbit"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/OrbitAlgebra.top_predecessor_period_two_orbit"),
                    H("Uniform top-predecessor period two"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(periodFormula)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For arbitrary d at least three, a typed top-gap base case and four scalar "
                        + "beta arm identities imply the full right-left period-two orbit by induction."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("four-bonacci-orbit-reproved-from-general-algebra"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/OrbitAlgebra.four_champion_gap_orbit_reproved"),
                    H("Order four is one substitution instance"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(fourFormula)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The frozen order-four base gap and scalar identities instantiate the "
                        + "uniform theorem and recover the exact original orbit statement."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacci/GapAlphabet")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacci/ChampionOrbit")),
            ]));
    }
}
