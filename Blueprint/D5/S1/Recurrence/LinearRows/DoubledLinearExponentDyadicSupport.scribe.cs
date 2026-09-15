using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.LinearRows;

internal sealed class DoubledLinearExponentDyadicSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/LinearRows/DoubledLinearExponentDyadicSupport.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/hanna2026a397592");
    private static readonly DeclarationHandle SourcePredicate =
        DeclarationHandle.Create(Prefix + "SourceA397592");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer existence and uniqueness for the literal source of A397592, together with its dyadic-neighbor parity assertion for every source solution.",
        H("The Integer Source and Dyadic Parity of OEIS A397592"),
        Blocks(
            Paragraph(Text("The source predicate is "), Ref(SourcePredicate.Value),
                Text(". For A in Z[[X]], A_Q denotes A.map (Int.castRingHom Rat), "
                    + "its coefficientwise integer-to-rational image in Q[[X]]: "
                    + "coeff j(A_Q) is the rational image of coeff j(A) for every natural j. "
                    + "The sequence starts at index zero, with a(n)=coeff n(A) and a(0)=1. "
                    + "The operation rescale(1/m,A_Q) means A_Q(X/m). Its mth power "
                    + "is ordinary multiplication of formal series, with no factorial "
                    + "normalization or convergence premise.")),
            Describe.Lean(DescribeId.Create("a397592-source"), SourcePredicate,
                H("The literal rational-rescaling source"),
                StatementSource.FromAuthor(SourceDefinition()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The sum contains exactly the first m coefficients, "
                    + "at indices j=0 through m-1, for every natural m>0. "
                    + "The equality is in Q and the unknown series has integer coefficients. "
                    + "This is the NAME equation with the constant term specified by "
                    + "the source's ordinary generating series and offset zero."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a397592-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Integer well-posedness and Hanna's parity assertion"),
                StatementSource.FromAuthor(ResultStatement()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The first conjunct asserts existence of an integer "
                    + "source and uniqueness among all integer series satisfying the literal "
                    + "equation. The second applies to every such series and every natural "
                    + "n>3. Oddness is equivalent in both directions to one of the two "
                    + "indices 2^k-1 and 2^k+1 for a natural k>1. The A397591 series "
                    + "starts at index one with zero constant term and has a different "
                    + "defining equation; it is not the source named here."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a397592-dyadic-parity"),
                    ResolutionKind.Proved)))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula NatType() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula SeriesType() => Call("PowerSeries", Seq(Mathbb, Grp(F.Id("Z"))));
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Def(Formula a) => Call("SourceA397592", a);
    private static Formula Coeff(Formula n, Formula a) => Call("coeff", n, a);

    private static Formula SourceDefinition()
    {
        var a = F.Id("A");
        var m = F.Id("m");
        var j = F.Id("j");
        var rationalImage = new Formula.Subscript(a, Seq(Mathbb, Grp(F.Id("Q"))));
        var scaled = Call("rescale", new Formula.Fraction(D(1), m), rationalImage);
        var summation = Seq(Sum, Underscore, Grp(Equal(j, D(0))),
            Caret, Grp(Sub(m, D(1))), Sp, Coeff(j, Pow(Par(scaled), m)));
        var rows = Seq(Bound("m", NatType()), D(0), Sp, Lt, Sp, m, Sp, Implies, Sp,
            Equal(summation, Pow(D(2), Sub(m, D(1)))));
        return Disp(Seq(Bound("A", SeriesType()), Def(a), Sp, Iff, Sp,
            Par(Seq(Equal(Call("constantCoeff", a), D(1)), Sp, Land, Sp, Par(rows)))));
    }

    private static Formula ResultStatement()
    {
        var a = F.Id("A");
        var n = F.Id("n");
        var k = F.Id("k");
        var power = Pow(D(2), k);
        var unique = Seq(Exists, Bang, Sp, a, Colon, Sp, SeriesType(), Comma, Sp, Def(a));
        var support = Seq(Exists, Sp, k, Colon, Sp, NatType(), Comma, Sp,
            D(1), Sp, Lt, Sp, k, Sp, Land, Sp,
            Par(Seq(Equal(n, Sub(power, D(1))), Sp, Lor, Sp, Equal(n, Add(power, D(1))))));
        var parity = Seq(Bound("A", SeriesType()), Def(a), Sp, Implies, Sp,
            Bound("n", NatType()), D(3), Sp, Lt, Sp, n, Sp, Implies, Sp,
            Par(Seq(Call("Odd", Coeff(n, a)), Sp, Iff, Sp, Par(support))));
        return Disp(Seq(Par(unique), Sp, Land, Sp, Par(parity)));
    }
}
