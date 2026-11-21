using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class BooleanDeletionParityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mass differences on a finite Boolean cube with equal deletion marginals.",
        H("A parity formula for the mass difference"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("boolean-deletion-mass-difference"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/BooleanDeletionParity.boolean_deletion_mass_difference"),
                H("Agreement after deleting each coordinate"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take two real mass functions on a finite indexed Boolean cube. For each "
                        + "coordinate and assignment of the other bits, assume the two functions "
                        + "have equal sums over the two values of the omitted bit. Write d for "
                        + "the full parity sign moment of the first function minus that of the "
                        + "second. In the formula, x[i mapped to b] updates only coordinate i, "
                        + "and the exponent uses the bit value zero or one. At each vector, "
                        + "the mass difference is d divided by the size "
                        + "of the cube, times the vector's parity sign. Total variation is half "
                        + "the absolute value of d.")),
                    Paragraph(Text(
                        "Equal deletion marginals force the mass difference to change sign at "
                        + "each single-bit flip. Flipping the coordinates in the support of a "
                        + "vector recovers its difference from the value at the all-zero vector. "
                        + "Summation against the parity sign fixes the coefficient. For a "
                        + "minimal dependent group of binary outputs, the joint law and the "
                        + "product of its marginals agree after every deletion, so this "
                        + "identity gives the distance between those two laws."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula i = F.Id("i");
        Formula index = F.Id("I");
        Formula x = F.Id("x");
        Formula d = F.Id("d");
        Formula sign = F.Id("s");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula vector = Seq(index, Sp, To, Sp, Name("Bool"));
        Formula mass = Seq(Parenthesized(vector), Sp, To, Sp, real);
        Formula atZero = Update(x, i, D(0));
        Formula atOne = Update(x, i, D(1));
        Formula difference = Seq(At(Mu, x), Minus, At(Nu, x));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(index, Name("Type")),
                OpenBracket, At(Name("Fintype"), index), CloseBracket,
                OpenBracket, At(Name("DecidableEq"), index), CloseBracket,
                Typed(Mu, mass), Typed(Nu, mass), Comma),
            Seq(Name("let"), Sp, At(sign, Typed(x, vector)), Colon, Eq,
                FiniteOperator(Prod, i, index),
                new Formula.Power(Parenthesized(Seq(Minus, D(1))), At(x, i)), Comma),
            Seq(Name("let"), Sp, d, Colon, Eq,
                FiniteOperator(Sum, x, Parenthesized(vector)),
                Parenthesized(difference), At(sign, x), Sp, Name("in")),
            Seq(Open, Forall, Sp, Typed(i, index), Typed(x, vector), Comma,
                At(Mu, atZero), Plus, At(Mu, atOne), Eq,
                At(Nu, atZero), Plus, At(Nu, atOne), Close, Sp, Longrightarrow),
            Seq(Open, Forall, Sp, Typed(x, vector), Comma, difference, Eq,
                new Formula.Fraction(d, new Formula.Power(D(2), new Formula.Absolute(index))),
                At(sign, x), Close, Sp, Land, Sp,
                Seq(Name("TV"), Open, Mu, Comma, Nu, Close), Eq,
                new Formula.Fraction(new Formula.Absolute(d), D(2))),
        ]));
    }

    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Parenthesized(argument));
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Update(Formula x, Formula i, Formula bit) =>
        Seq(x, OpenBracket, i, Sp, Mapsto, Sp, bit, CloseBracket);
    private static Formula FiniteOperator(Formula symbol, Formula variable, Formula domain) =>
        new Formula.Subscript(symbol, Seq(variable, Sp, InMacro, Sp, domain));
}
