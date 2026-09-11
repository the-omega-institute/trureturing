using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class DiagonalExponentSelfDivisibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Residue/DiagonalExponentSelfDivisibility.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/hanna2026a395833div");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Affine vanishing-diagonal exponents divide their own integer coefficients.",
        H("Exponent Divisibility for Vanishing Diagonals"),
        Blocks(
            Paragraph(Text("The note hanna2026a395833div quotes Hanna's A395833 "
                + "generating equation and divisibility conjecture. Write a(p,n) for "
                + "NegativePowerDiagonalModPrime.a(p,n), the coefficient of its unique "
                + "normalized integer series A(p). The normalization is a(p,0)=a(p,1)=1, "
                + "and for n>1 the coefficient of x^n in "
                + "A(p)(x/A(p)(x)^((p-1)*(n-1)+1)) vanishes. The quotient uses "
                + "the formal unit inverse. Thus slope d corresponds to p=d+1, "
                + "and A395833 corresponds to p=3.")),
            Paragraph(Text("The parameters d and n are natural numbers. In the general "
                + "formula, n-1 and the expression inside intCast are computed in the "
                + "natural numbers; intCast is the embedding into the integers. In the "
                + "A395833 formula, 2*intCast(n)-1 is integer arithmetic. Both "
                + "divisibility conclusions are integer divisibility.")),
            Node("exponent_self_divisibility", "Every positive slope", GeneralFormula(),
                "Put e(n)=d*(n-1)+1. Expanding the vanishing diagonal expresses a(d+1,n) "
                + "as the negative sum of a(d+1,m)*c for 1<=m<n, where c is the "
                + "coefficient of degree n-m in A(d+1)^(-e(n)*m). The derivative "
                + "coefficient identity gives e(n)*m dividing (n-m)*c. The affine "
                + "difference e(m)=e(n)-d*(n-m) therefore gives e(n) dividing e(m)*c. "
                + "Strong induction supplies e(m) dividing a(d+1,m), so every summand "
                + "is divisible by e(n). The initial divisor e(1) is one.",
                AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a395833-diagonal-exponent-self-divisibility"),
                    ResolutionKind.Proved)),
            Node("hanna_conjecture_a395833", "The A395833 divisibility conjecture",
                InstanceFormula(),
                "Set d=2 in the general theorem. For n>=1 the exponent "
                + "2*(n-1)+1 equals 2*n-1, proving the quoted divisibility conjecture.",
                AssessedProvenance.FromLiterature(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("diagonal-exponent-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Theorem, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula N() => F.Id("n");
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Bound(string name) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, Naturals(), Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Positive(Formula value) => Seq(D(1), Sp, Le, Sp, value);
    private static Formula Divides(Formula left, Formula right) => Seq(left, Sp, Mid, Sp, right);

    private static Formula GeneralFormula()
    {
        var d = F.Id("d");
        return Disp(Seq(Bound("d"), Implication(Positive(d), Seq(Bound("n"),
            Implication(Positive(N()), Divides(
                Call("intCast", Add(Mul(d, Subtract(N(), D(1))), D(1))),
                Call("a", Add(d, D(1)), N())))))));
    }

    private static Formula InstanceFormula() => Disp(Seq(Bound("n"),
        Implication(Positive(N()), Divides(
            Parenthesized(Subtract(Mul(D(2), Call("intCast", N())), D(1))),
            Call("a", D(3), N())))));
}
