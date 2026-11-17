using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class WilsonPisotL67RecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/WilsonPisotL67Recurrence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native rational-ceiling sequence L(6,7) has positive terms and obeys Wilson's signed recurrence at every index at least four.",
        H("Wilson's Pisot Sequence L(6,7)"),
        Blocks(
            Paragraph(Text("David W. Wilson's OEIS A048585, revision 18, defines L(6,7) by ordinary upward ceiling and states the four-lag recurrence as holding through index 50000 but unknown in general. The fixed source is https://raw.githubusercontent.com/oeis/oeisdata/72c53dd50967ac7166f7d31bf79be95174ec5bc6/seq/A048/A048585.seq . The elementary proof below follows the preexisting public outline at https://github.com/the-omega-institute/trureturing/issues/21793 . This attribution makes no priority claim beyond that project source.")),
            Paragraph(Text("All indices are natural numbers and all sequence values are integers. The notation rat casts an integer to the rational numbers before division. The function ceil is the least integer greater than or equal to its rational argument; an integer argument stays unchanged. Subtraction of sequence values is integer subtraction; subtraction inside an index is natural subtraction.")),
            Describe.Lean(DescribeId.Create("wilson-pisot-l67-native"),
                DeclarationHandle.Create(Prefix + "a"), H("The defining ceiling recursion"),
                StatementSource.FromAuthor(Definition()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The initial values are six and seven. Every later value is obtained from the preceding two by the displayed rational quotient and upward ceiling. No linear recurrence or auxiliary identification is assumed in this definition."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("wilson-pisot-l67-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Positivity and the full four-lag recurrence"),
                StatementSource.FromAuthor(Result()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Define the integer reference sequence v by v(0)=3, v(1)=4, v(2)=6 and v(n+3)=v(n+2)+v(n). Set u(n)=v(n)+3, s(n)=v(n+2)-2v(n+1)+v(n), and d(n)=v(n)v(n+2)-v(n+1)^2. Three-step induction proves v and s positive. The second differences satisfy s(n+3)=s(n+2)+s(n); a second induction proves s(n) at most s(n+1).")),
                    Paragraph(Text("Expanding the quadratic determinant gives d(n+3)=d(n)-d(n+1). At indices 7,8,9 the triples (v,s,d) are (41,9,8), (60,13,-4), and (88,19,-9). Three-step induction, using monotonicity of s, proves -s(n) at most d(n) at most s(n) for all n at least seven. Another three-step induction gives 4s(n)<v(n) in that range.")),
                    Paragraph(Text("The ceiling error u(n)u(n+2)-u(n+1)^2 is d(n)+3s(n). These inequalities put it between zero and u(n), strictly below the latter. At indices zero through six its exact pairs with u(n) are (5,6), (3,7), (0,9), (8,12), (12,16), (7,22), and (17,31). Thus the window holds at every index, including the zero error at index two.")),
                    Paragraph(Text("Divide the window by the positive u(n): the rational quotient lies strictly above u(n+2)-1 and at most u(n+2). The ceiling characterization identifies its ceiling with u(n+2). Two-step induction therefore identifies the native sequence a with u at every index. Finally subtract the shifted identities u(n+3)=u(n+2)+u(n)-3 to obtain the signed order-four recurrence, and translate n+4 to the required natural lag indices. The same window proves positivity of every native denominator.")))))));

    private static Formula N() => F.Id("n");
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(Formula body) => Seq(Forall, Sp, Par(Seq(N(), Colon, Sp, Naturals())), Comma, Sp, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula A(Formula n) => Call("a", n);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Definition()
    {
        var numerator = new Formula.Power(Par(Call("rat", A(Add(N(), D(1))))), D(2));
        var quotient = new Formula.Fraction(numerator, Call("rat", A(N())));
        return Disp(And(Equal(A(D(0)), D(6)), And(Equal(A(D(1)), D(7)),
            All(Equal(A(Add(N(), D(2))), Call("ceil", quotient))))));
    }
    private static Formula Result()
    {
        var positive = All(Seq(D(0), Sp, Lt, Sp, A(N())));
        var rhs = Sub(Add(Sub(Mul(D(2), A(Sub(N(), D(1)))), A(Sub(N(), D(2)))),
            A(Sub(N(), D(3)))), A(Sub(N(), D(4))));
        var recurrence = All(Seq(Par(Seq(D(4), Sp, Le, Sp, N())), Sp, Implies, Sp,
            Par(Equal(A(N()), rhs))));
        return Disp(And(positive, recurrence));
    }
}
