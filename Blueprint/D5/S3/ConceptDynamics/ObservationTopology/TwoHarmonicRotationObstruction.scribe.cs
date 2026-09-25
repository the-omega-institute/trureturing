using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationTopology;

internal sealed class TwoHarmonicRotationObstructionDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ConceptDynamics/ObservationTopology/TwoHarmonicRotationObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coprime frequency pairs meet a sharp half-cosine barrier at angle pi/6.",
        H("Two-Harmonic Rotation Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coprime-two-frequency-cosine-obstruction"),
                DeclarationHandle.Create(Owner + "coprime_two_frequency_cosine_obstruction"),
                H("Coprime frequency pairs cannot both avoid the half-cosine barrier"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Reducing a frequency modulo six lists every possible cosine magnitude "
                            + "at a rotation angle of pi over six. A magnitude strictly below "
                            + "one half forces residue three.")),
                    Paragraph(Text(
                        "If both frequencies had magnitude below one half, both would be "
                            + "divisible by three. That common divisor contradicts their "
                            + "coprimality, so at least one magnitude reaches the barrier."))),
                DescribeRole.Theorem),
            Paragraph(
                Text("The discrete frequency obstruction applies to the stable-rank "
                    + "measurement-design question of Eftekhari et al. (2018), recorded in "
                    + "Library/ConceptDynamics/eftekhari2018embedology.md, when the sensor class "
                    + "is restricted to paired circle harmonics at "
                    + "a pi/6 delay. It does not by itself assert "
                    + "the analytic stable-rank formula or a dimension bound for arbitrary "
                    + "smooth sensors.")))));

    private static Formula Natural => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);

    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Div(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Magnitude(Formula frequency) =>
        new Formula.Absolute(Call("cos", Mul(Call("real", frequency), Div(Pi, Num(6)))));

    private static Formula TheoremFormula()
    {
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        Formula half = Div(Num(1), Num(2));
        return Disp(All(
            [Bound("m", Natural), Bound("n", Natural)],
            Implies(
                Call("Coprime", m, n),
                Le(half, Call("max", Magnitude(m), Magnitude(n))))));
    }
}
