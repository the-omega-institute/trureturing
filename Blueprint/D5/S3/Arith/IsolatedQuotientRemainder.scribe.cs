using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class IsolatedQuotientRemainderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/IsolatedQuotientRemainder.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ratajczak2024a375007");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every isolated quotient-remainder value t greater than 24, t+1 is prime.",
        H("The prime-successor conjecture of A375007"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a375007-isolation"),
                DeclarationHandle.Create(Prefix + "P"),
                H("Isolation in the natural interval"),
                StatementSource.FromAuthor(IsolationFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "All variables are natural numbers. The symbols mod, natDiv and natSub "
                    + "denote natural remainder, floor division and truncated subtraction. "
                    + "The bounds 1<=k<=t ensure that subtraction agrees with ordinary "
                    + "subtraction. P asserts only that the displayed equality can occur "
                    + "at the two endpoints."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a375007-prime"),
                DeclarationHandle.Create(Prefix + "a375007_prime"),
                H("Every isolated value above 24 has prime successor"),
                StatementSource.FromAuthor(PrimeFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "If t+1 is composite, its least prime factor a and complementary "
                    + "factor b satisfy 2<=a<=b. When a<b, set k=b-1. Then "
                    + "t=a*k+(a-1), with a-1<k, so both remainders equal a-1. "
                    + "When a=b=u, the threshold implies u>=6. Set k=u-2; then "
                    + "t=(u+2)*k+3 and 3<k. Subtracting k lowers the quotient by one, "
                    + "and (u+1) mod (u-2)=3. Each case gives 1<k<t, contradicting P. "
                    + "This proves the value formulation of the first OEIS conjecture; "
                    + "the first six listed values end at 24. The sequence enumeration "
                    + "and the separate conjecture about products of successive differences "
                    + "are outside this statement."))), DescribeRole.Theorem))));

    private static Formula T() => F.Id("t");
    private static Formula K() => F.Id("k");
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Bound(string name) => Seq(
        Forall, Sp, F.Id(name), Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp);
    private static Formula Paren(Formula value) => Seq(Open, value, Close);
    private static Formula Equality() => Seq(
        new Formula.Modulo(T(), K()), Sp, Eq, Sp,
        new Formula.Modulo(Call("natDiv", Call("natSub", T(), K()), K()), K()));
    private static Formula IsolationFormula() => Disp(Seq(
        Bound("t"), Call("P", T()), Sp, Iff, Sp, Paren(Seq(
            Bound("k"), D(1), Sp, Le, Sp, K(), Sp, Implies, Sp,
            K(), Sp, Le, Sp, T(), Sp, Implies, Sp, Paren(Seq(
                Equality(), Sp, Implies, Sp, Paren(Seq(
                    K(), Sp, Eq, Sp, D(1), Sp, Lor, Sp, K(), Sp, Eq, Sp, T()))))))));
    private static Formula PrimeFormula() => Disp(Seq(
        Bound("t"), D(2, 4), Sp, Lt, Sp, T(), Sp, Implies, Sp,
        Call("P", T()), Sp, Implies, Sp,
        Call("Prime", new Formula.Binary(T(), FormulaBinaryOperator.Add, D(1)))));
}
