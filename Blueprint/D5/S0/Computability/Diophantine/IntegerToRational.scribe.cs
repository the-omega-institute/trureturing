using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class DiophantineIntegerToRationalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite polynomial definition of the integers yields a joint-assignment solvability reduction.",
        H("Conditional Integer-to-Rational Polynomial Reduction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("integer-to-rational-solvability"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Diophantine/IntegerToRational.solvability"),
                H("The finite joint-assignment reduction"),
                StatementSource.FromAuthor(Presentation()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix an integer polynomial P in one input coordinate and m witness "
                        + "coordinates that existentially defines the integers inside the rationals. "
                        + "For an arbitrary input polynomial f in n integer variables, the compiler "
                        + "uses n disjoint blocks of m+1 rational coordinates. The first coordinate "
                        + "of each block is the corresponding input variable; the remaining m "
                        + "coordinates are that variable's defining witnesses.")),
                    Paragraph(Text(
                        "The output is one integer-coefficient polynomial: the square of f on the "
                        + "first coordinates plus the sum of the squares of the n translated copies "
                        + "of P. Every equation is evaluated under one joint assignment. A zero sum "
                        + "of rational squares forces every summand to vanish, giving soundness; an "
                        + "integer zero of f and one defining witness block per coordinate give "
                        + "completeness. The proof includes n=0, constant and zero inputs, signs and "
                        + "all finite dimensions.")),
                    Paragraph(Text(
                        "This is conditional. It neither constructs the defining polynomial P nor "
                        + "proves integer Hilbert-tenth undecidability. The semantic compiler is "
                        + "formalized here; an explicit standard polynomial-code implementation and "
                        + "its compiled computability proof remain a separate downstream obligation "
                        + "before the full effective H10-END interface can be claimed."))),
                DescribeRole.Theorem))));

    private static Formula A(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula E(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula Presentation()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var p = F.Id("P");
        var f = F.Id("f");
        var lhs = E("x", Call("FinRatVec", Call("mul", n, Call("succ", m))),
            Call("evalCompiled", p, f, F.Id("x"), F.Id("zero")));
        var rhs = E("z", Call("FinIntVec", n),
            Call("evalInput", f, F.Id("z"), F.Id("zero")));
        var body = F.Seq(
            Call("DefinesIntegers", p), F.Sp, Rightarrow, F.Sp,
            F.Open, lhs, F.Close, F.Sp, Iff, F.Sp, F.Open, rhs, F.Close);
        return F.Disp(A("n", F.Id("N"), A("m", F.Id("N"),
            A("P", Call("IntegerPolynomial", Call("succ", m)),
                A("f", Call("IntegerPolynomial", n), body)))));
    }
}
