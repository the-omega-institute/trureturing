using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class KurkovWeightProductBinomialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/KurkovWeightProductBinomial.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/karttunen2017a284005");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary-weight products satisfy Kurkov's binomial identity at every natural index.",
        H("Kurkov's Binary-Weight Product Identity"),
        Blocks(
            Paragraph(Text("The variables m, n, and k range over the natural numbers N, including zero. "
                + "The functions wt and a take natural values: wt is the frozen binary-weight "
                + "definition of D5/S1/Digit/DyadicRowPolynomialRecurrence (A000120), reused "
                + "by import, and a is A284005. The operator div is natural floor "
                + "division, and binom(r,k) is Nat.choose r k. All additions, products, "
                + "powers, and sums are in N. Only Kurkov's April 24, 2023 binomial conjecture "
                + "is asserted here. The 2019 bit-flip recursion, the 2023 mod-2 binomial "
                + "transform of A329369, and the representation A000005(A283477(n)) are "
                + "outside this statement.")),
            Node("a", "The binary-weight product sequence", SequenceFormula(),
                "Starting with a(0)=1, each positive index contributes one plus its "
                + "binary weight before the index is divided by two. The OEIS NAME "
                + "states the recurrence for indices greater than one; the data supplies "
                + "a(1)=2, also obtained from the displayed successor clause.",
                DescribeRole.Definition),
            Node("result", "Kurkov's binomial identity", ResultFormula(),
                "Multiplication by a power of two preserves binary weight. Induction "
                + "gives a(2^k*n)=(1+wt(n))^k*a(n), including n=0. At odd indices a "
                + "second induction gives a(2^m*(2*n+1))=(wt(n)+2)^(m+1)*a(n). "
                + "The binomial expansion of ((1+wt(n))+1)^(m+1), followed by the "
                + "first identity in each summand, gives the result. The sum includes "
                + "both endpoints k=0 and k=m+1, exactly Finset.range(m+2).",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a284005-kurkov-weight-product-binomial"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a284005-" + name),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Universal(Formula variables, Formula body) =>
        Seq(Forall, Sp, variables, Sp, InMacro, Sp, Naturals(), Comma, Sp, body);

    private static Formula SequenceFormula()
    {
        Formula n = F.Id("n");
        Formula successor = Add(n, D(1));
        Formula step = Equal(Call("a", successor),
            Mul(Parenthesized(Add(D(1), Call("wt", successor))),
                Call("a", Call("div", successor, D(2)))));
        return Disp(Seq(Parenthesized(Equal(Call("a", D(0)), D(1))), Sp, Land, Sp,
            Parenthesized(Universal(n, step))));
    }

    private static Formula ResultFormula()
    {
        Formula m = F.Id("m"), n = F.Id("n"), k = F.Id("k");
        Formula left = Call("a", Mul(new Formula.Power(D(2), m),
            Parenthesized(Add(Mul(D(2), n), D(1)))));
        Formula summand = Mul(Call("binom", Add(m, D(1)), k),
            Call("a", Mul(new Formula.Power(D(2), k), n)));
        Formula sum = Seq(new Formula.Subscript(Sum, Equal(k, D(0))),
            Caret, Grp(Add(m, D(1))), Sp, summand);
        return Disp(Universal(Seq(m, Comma, Sp, n), Equal(left, sum)));
    }
}
