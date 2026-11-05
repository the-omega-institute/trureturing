using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class KurkovLowerBitRecurrenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary prefix products give the complete lower-bit recurrence for A284005.",
        H("Kurkov's Lower-Bit Recurrence"),
        Blocks(
            Paragraph(Text("The sequence a is the imported A284005 function from "
                + "KurkovWeightProductBinomial, and wt is the imported binary digit sum from "
                + "DyadicRowPolynomialRecurrence. All variables and operations below are natural: "
                + "div is floor division, mod is remainder, and log is Nat.log. For n>1 put "
                + "L=log(2,n) and m=n-2^L. The sum is over every k in Finset.range L. "
                + "Its bit is div(n,2^k) mod 2. At an existing one bit its summand is a(m), "
                + "so repeated existing-one contributions are included. The statement is the "
                + "lower-bit formula attributed to Mikhail Kurkov in A284005, November 10, 2019.")),
            Describe.Lean(DescribeId.Create("a284005-lower-bit-result"),
                DeclarationHandle.Create("D5/S1/Digit/KurkovLowerBitRecurrence.result"),
                H("The full lower-bit identity and initial data"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Digit/kurkov2019a284005")),
                Blocks(Paragraph(Text("For an arbitrary depth L and m<2^L define "
                    + "P(L,c,m) as the product, for i<L, of c+wt(div(m,2^i)). "
                    + "The native recurrence gives a(m)=P(L,1,m) and "
                    + "a(2^L+m)=2*P(L,2,m), including m=0 and leading zero padding. "
                    + "Setting a zero bit at position k increases each prefix weight "
                    + "through position k by one and preserves all higher prefix weights. "
                    + "Induction on binary depth gives "
                    + "(c+1)*P(L,c+1,m)=(c+1+wt(m))*P(L,c,m)+Z(L,c,m), "
                    + "where Z is the sum of P(L,c,m+2^k) over the zero positions. "
                    + "The remaining positions contribute wt(m)*P(L,c,m). "
                    + "Taking c=1 and the exact logarithmic leading-power bounds gives "
                    + "the displayed whole sum. The original domain includes n=2 and "
                    + "every power of two; no identity at n=0 or n=1 is asserted. "
                    + "The initial values and defining recurrence are included separately. "
                    + "The source supplies the question; the native proof is a repository result. Importing the sequence from KurkovWeightProductBinomial does not use its two-parameter binomial theorem. No literature proof, global openness or priority is asserted."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a284005-kurkov-lower-bit-recurrence"),
                    ResolutionKind.Proved)))));

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula All(Formula n, Formula body) =>
        Seq(Forall, Sp, n, Sp, InMacro, Sp, N(), Comma, Sp,
            D(1), Sp, Lt, Sp, n, Sp, Rightarrow, Sp, body);

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        Formula l = Call("log", D(2), n);
        Formula m = Sub(n, new Formula.Power(D(2), l));
        Formula bit = Call("mod", Call("div", n, new Formula.Power(D(2), k)), D(2));
        Formula sum = Seq(new Formula.Subscript(Sum, Eqn(k, D(0))), Caret,
            Grp(Sub(l, D(1))), Sp,
            Call("a", Add(m, Mul(new Formula.Power(D(2), k), Par(Sub(D(1), bit))))));
        Formula recurrence = All(n, Eqn(Call("a", n),
            Mul(Par(Add(D(1), Call("wt", n))), Call("a", Call("div", n, D(2))))));
        Formula identity = All(n, Eqn(Call("a", n), Add(Mul(D(2), Call("a", m)), sum)));
        return Disp(Seq(Par(Eqn(Call("a", D(0)), D(1))), Sp, Land, Sp,
            Par(Eqn(Call("a", D(1)), D(2))), Sp, Land, Sp,
            Par(recurrence), Sp, Land, Sp, Par(identity)));
    }
}
