using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor;

internal sealed class SmoothPredecessorMainDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/makowskischinzel1964totient");
    private static readonly LibraryNoteRef Cohen =
        LibraryNoteRef.Create("D5/L/ArithUnits/cohen1997makowski");
    private static readonly LibraryNoteRef Pomerance =
        LibraryNoteRef.Create("D5/L/ArithUnits/pomerance2026makowski");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sigma-totient inequality for smooth prime predecessors",
        H("The sigma-totient inequality for smooth prime predecessors"), Blocks(
            Describe.Lean(DescribeId.Create("smooth-predecessor-sigma-totient"),
                DeclarationHandle.Create(Prefix + "makowski_schinzel_of_smooth_predecessors"),
                H("Both inequalities under the predecessor condition"),
                StatementSource.FromAuthor(Disp(MainStatement())),
                AssessedProvenance.FromRepo(Source, Cohen, Pomerance),
                Blocks(Paragraph(Text(
                    "For every natural n, suppose every prime divisor q of n has q-1 " +
                    "in the 98-smooth positive integers, so all prime divisors of q-1 " +
                    "are at most 97. Then n<=2 sigma(1,phi(n)), and odd n satisfies " +
                    "n<=sigma(1,phi(n)). There is no bound on n, q, or their exponents. " +
                    "The finite table covers the non-Fermat prime predecessors through " +
                    "one million. For a larger predecessor, its largest odd prime " +
                    "factor supplies a label; division by twice that label produces " +
                    "a smooth number beyond the corresponding finite cutoff. A common " +
                    "Euler-product estimate bounds the actual finite tail after the " +
                    "small smooth contribution is subtracted. Checked prefix products " +
                    "and this tail bound control each group. Fermat prime factors use " +
                    "the separate power-of-two totient inequality, without assuming " +
                    "that all Fermat primes are known. Radical and parity lifting " +
                    "recover both conclusions. Integers with an unrestricted " +
                    "predecessor prime factor above 97 are outside this statement; " +
                    "no conclusion about the unrestricted conjecture is asserted."))),
                DescribeRole.Theorem))));

    private static Formula MainStatement()
    {
        var n = V("n"); var sigma = Call("sigma", D(1), Call("totient", n));
        return All("n", Nat(), Imp(Smooth(n),
            And(Le(n, Mul(D(2), sigma)), Imp(Call("Odd", n), Le(n, sigma)))));
    }

    private static Formula Smooth(Formula n)
    {
        var q = V("q");
        return All("q", Nat(), Imp(In(q, Call("primeFactors", n)),
            In(Sub(q, D(1)), Call("smoothNumbers", D(9,8)))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula In(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
}
