using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class MinimalBinaryUnimodularBreakDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/GoldenCoding/MinimalBinaryUnimodularBreak."
            + "minimal_binary_unimodular_break";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonnegative integral binary matrices have sharp expansion floors determined by "
            + "the sign of their unimodular determinant.",
        H("Minimal Binary Unimodular Expansion"),
        Blocks(Describe.Lean(
            DescribeId.Create("minimal-binary-unimodular-break"),
            DeclarationHandle.Create(Declaration),
            H("The Fibonacci matrix realizes both sharp determinant-sign bounds"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The matrix M has nonnegative integral entries, and lambda is a real "
                        + "characteristic root above one. In determinant sign minus one, "
                        + "the integral trace is at least one; in determinant sign one, it "
                        + "is at least three. Factoring the corresponding quadratics gives "
                        + "the two displayed lower bounds.")),
                Paragraph(Text(
                    "The public equality clauses use the integral Fibonacci matrix itself. "
                        + "Its real cast is the repository's canonical Fibonacci "
                        + "substitution, while direct finite arithmetic identifies its "
                        + "square and verifies both determinants and characteristic roots."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula integer = Seq(Mathbb, Grp(F.Id("Z")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula finTwo = Call("Fin", D(2));
        Formula matrixType = Call("Matrix", finTwo, finTwo, natural);
        Formula matrix = F.Id("M");
        Formula lambda = F.Id("lambda");
        Formula phiSquared = Seq(Varphi, Caret, Grp(D(2)));
        Formula castRealMatrix = Call("cast", real, matrix);
        Formula castIntegerMatrix = Call("cast", integer, matrix);
        Formula matrixRoot = Call(
            "IsRoot", Call("charpoly", castRealMatrix), lambda);
        Formula fibonacci = F.Id("F");
        Formula fibonacciSquared = F.Id("F2");
        Formula fibonacciLiteral = Call("matrix2", D(1), D(1), D(1), D(0));
        Formula squareLiteral = Call("matrix2", D(2), D(1), D(1), D(1));
        Formula castRealFibonacci = Call("cast", real, fibonacci);
        Formula castIntegerFibonacci = Call("cast", integer, fibonacci);
        Formula castIntegerSquare = Call("cast", integer, fibonacciSquared);
        Formula castRealSquare = Call("cast", real, fibonacciSquared);

        Formula negativeBound = Seq(
            Call("det", castIntegerMatrix), Sp, Eq, Sp, Minus, D(1), Sp,
            Rightarrow, Sp, Varphi, Sp, Leq, Sp, lambda);
        Formula positiveBound = Seq(
            Call("det", castIntegerMatrix), Sp, Eq, Sp, D(1), Sp,
            Rightarrow, Sp, phiSquared, Sp, Leq, Sp, lambda);
        Formula fibonacciWitness = Seq(
            F.Id("let"), Sp, fibonacci, Sp, Colon, Eq, Sp, fibonacciLiteral, Comma, Sp,
            Call("det", castIntegerFibonacci), Sp, Eq, Sp, Minus, D(1), Sp, Land, Sp,
            castRealFibonacci, Sp, Eq, Sp, F.Id("fibonacciSubstitution"), Sp, Land, Sp,
            D(1), Sp, Lt, Sp, Varphi, Sp, Land, Sp,
            Call("IsRoot", Call("charpoly", castRealFibonacci), Varphi));
        Formula squareWitness = Seq(
            F.Id("let"), Sp, fibonacci, Sp, Colon, Eq, Sp, fibonacciLiteral, Comma, Sp,
            F.Id("let"), Sp, fibonacciSquared, Sp, Colon, Eq, Sp,
            fibonacci, Caret, Grp(D(2)), Comma, Sp,
            fibonacciSquared, Sp, Eq, Sp, squareLiteral, Sp, Land, Sp,
            Call("det", castIntegerSquare), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            D(1), Sp, Lt, Sp, phiSquared, Sp, Land, Sp,
            Call("IsRoot", Call("charpoly", castRealSquare), phiSquared));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(matrix, matrixType), Comma, Sp,
                Typed(lambda, real), Comma),
            Seq(
                Grp(), D(1), Sp, Lt, Sp, lambda, Sp, Land, Sp,
                matrixRoot, Sp, Rightarrow),
            Seq(Grp(), Open, negativeBound, Close, Sp, Land),
            Seq(Grp(), Open, positiveBound, Close, Sp, Land),
            Seq(Grp(), Open, fibonacciWitness, Close, Sp, Land),
            Seq(Grp(), Open, squareWitness, Close, Dot),
        ]));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) pieces.AddRange([Comma, Sp]);
            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq([.. pieces]);
    }
}
