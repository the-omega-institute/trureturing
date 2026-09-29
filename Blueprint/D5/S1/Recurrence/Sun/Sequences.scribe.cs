using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Sun;

internal sealed class SequencesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Sun/Sequences.";
    private static readonly LibraryNoteRef Sun =
        LibraryNoteRef.Create("D5/L/Recurrence/sun2026generalizations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two lowercase polynomial sequences are defined by Sun's literal initial values and three-term recurrences over the reals.",
        H("Sun's Lowercase Recurrence Sequences"),
        Blocks(
            Paragraph(Text("The natural index starts at zero; x is real. Each recurrence is "
                + "implemented at successor index n+1 for n at least one. Division by the "
                + "positive square or cube of n+1 is definitionally equivalent to the "
                + "multiplied equation displayed below. These are the lowercase g and v, "
                + "not the older uppercase G and V obtained by a separate substitution.")),
            Describe.Lean(
                DescribeId.Create("sun-lowercase-g"), DeclarationHandle.Create(Prefix + "g"),
                H("The lowercase g sequence"), StatementSource.FromAuthor(GRecurrence()),
                AssessedProvenance.FromLiterature(Sun),
                Blocks(Paragraph(Text("For every real x, the first values are g(0)=1 and "
                    + "g(1)=(x+1)/2. The displayed equation is the defining recurrence "
                    + "for every n at least one, including its quadratic scale."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sun-lowercase-v"), DeclarationHandle.Create(Prefix + "v"),
                H("The lowercase v sequence"), StatementSource.FromAuthor(VRecurrence()),
                AssessedProvenance.FromLiterature(Sun),
                Blocks(Paragraph(Text("For every real x, the first values are v(0)=1 and "
                    + "v(1)=x. The displayed equation is the defining recurrence "
                    + "for every n at least one, including its cubic scale."))),
                DescribeRole.Definition))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, byte n) => new Formula.Power(a, D(n));
    private static Formula EqF(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula N => F.Id("n");
    private static Formula X => F.Id("x");
    private static Formula Next => Add(N, D(1));
    private static Formula Prev => Sub(N, D(1));

    private static Formula GRecurrence() => Disp(new Formula.Aligned([
        EqF(Call("g", X, D(0)), D(1)),
        EqF(Call("g", X, D(1)), Div(Add(X, D(1)), D(2))),
        EqF(Mul(Pow(Next, 2), Call("g", X, Next)),
            Sub(Mul(Add(Mul(Mul(D(2), N), Next), Div(Add(X, D(1)), D(2))),
                    Call("g", X, N)),
                Mul(Pow(N, 2), Call("g", X, Prev))))
    ]));

    private static Formula VRecurrence() => Disp(new Formula.Aligned([
        EqF(Call("v", X, D(0)), D(1)),
        EqF(Call("v", X, D(1)), X),
        EqF(Mul(Pow(Next, 3), Call("v", X, Next)),
            Sub(Mul(Mul(Add(Mul(D(2), N), D(1)), Add(Mul(N, Next), X)),
                    Call("v", X, N)),
                Mul(Pow(N, 3), Call("v", X, Prev))))
    ]));
}
