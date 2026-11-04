using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class BalaA295431DivisibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/BalaA295431Divisibility.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Factorization/mazhang2026baladivisibilities");

    public DocumentDefinition Create()
    {
        Formula n=V("n"), r=V("R"), k=V("k"), i=V("i");
        Formula ratio = Div(Mul(Fact(Mul(D(1,2),n)),Fact(n)),
            Mul(Mul(Fact(Mul(D(6),n)),Fact(Mul(D(4),n))),Fact(Mul(D(3),n))));
        Formula rising = Product("i",Call("Icc",D(1),r),Add(Mul(k,n),i));
        Formula units = Call("filter",Lambda("i",Call("Coprime",i,D(1,2))),Call("Icc",D(1),r));
        Formula signed = Product("i",units,Sub(Mul(D(1,2),Cast(n,Int())),Cast(i,Int())));
        Formula factorial = App(Named("factorial"),Call("NatSub",r,D(1)));
        Formula c = Mul(Mul(D(3,6),factorial),Call("lcmUpto",Mul(D(1,2),r)));
        Formula d = Mul(factorial,Call("lcmUpto",r));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Actual T divisibilities.", H("Bala A295431: five fixed quotients and two uniform families"), Blocks(
            Node("ratio", All("n",Nat(),Eq(Call("ratio",n),ratio)),
                "T(n) is the actual rational factorial ratio (12n)! n! / ((6n)! (4n)! (3n)!). Every index is natural, including zero. The existing even_dvd producer at OeisA347854BalaHalfIndexIntegral supplies its integrality; that prior result is not new content here.", DescribeRole.Definition),
            Node("rising_denominator", All("k",Nat(),All("n",Nat(),All("R",Nat(),Eq(Call("rising_denominator",k,n,r),rising)))),
                "The natural product of k*n+i over 1 <= i <= R is positive whenever the interval is nonempty and equals one for R=0. Its rational cast is the denominator of the first uniform family.", DescribeRole.Definition),
            Node("signed_denominator", All("n",Nat(),All("R",Nat(),Eq(Call("signed_denominator",n,r),signed))),
                "This integer product runs over 1 <= i <= R with gcd(i,12)=1. Subtraction takes place in the integers before the rational cast. None of its factors is zero, even when R exceeds 12n. A product over an empty set equals one.", DescribeRole.Definition),
            Node("first_constant", All("R",Nat(),Eq(Call("first_constant",r),c)),
                "C(R)=36*(R-1)!*lcm(1,...,12R), independently of k. NatSub denotes natural subtraction, which occurs only in the factorial index; the theorem assumes R>=1. The constant is sufficient, with no minimality assertion.", DescribeRole.Definition),
            Node("second_constant", All("R",Nat(),Eq(Call("second_constant",r),d)),
                "D(R)=(R-1)!*lcm(1,...,R). The least common multiple is mathlib Nat.lcmUpto. This is a sufficient constant for the signed family.", DescribeRole.Definition),
            Node("claim", Eq(Call("claim"),Par(ClaimBody())),
                "Corollary 5 of Ma and Zhang, revision 3, states all five fixed expressions and both families for all natural n. The family quantifiers preserve every R>=1 and each k=1,2,3. Integer realizations concern the actual rational expressions, with nonzero denominator assertions for both products and the signed value -1 at zero.", DescribeRole.Definition),
            Node("result", ClaimBody(),
                "All seven outcomes hold. Legendre valuations reuse the original h854 and h854_nonneg floor producer, reduced modulo each prime power. At a level dividing k*n+i with modulus at least 12*i, the left floor cells give defect one for every prime, including 2 and 3. For 12*n-i, the right cells and coprimality give defect one beyond R. Removing a factor of maximal valuation bounds the remaining product by valuations of index differences; their product divides (R-1)!. The lcm valuations supply the logarithmic losses. The required factor 36 is retained without a minimality claim. For the fixed constants, the only large-prime missing first levels are 5,7,11 for n+1 and 5 for 2n+1. At 2 and 3, factorial multiplication identities identify the needed valuations with those of binomial coefficients, and the adjacent-binomial identity supplies the lower bounds. The first two denominators are coprime, and gcd((n+1)*(2n+1),3n+1) divides 2, giving constant 770. The fifth fixed assertion is obtained internally from the signed family at R=1; it is not a separately discovered result. At n=0 its denominator is -1 and T(0)=1. Attribution is to the supplied Corollary 5 and earlier literature; no priority, world novelty, converse, congruence, Gamma, moment-density or other-ratio claim is made.", DescribeRole.Theorem))));
    }

    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("bala-t-" + name.Replace('_', '-')), DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
    private static Formula V(string n) => F.Id(n);
    private static Formula Named(string n) => Seq(Operatorname, Grp(F.Id(n.Replace("_", ""))));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string n, params Formula[] args) => args.Length == 0 ? Named(n) : App(Named(n), args);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Int() => new Formula.Integers();
    private static Formula Rat() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Cast(Formula f, Formula t) => Par(Seq(f, Colon, Sp, t));
    private static Formula Fact(Formula n) => Cast(App(Named("factorial"), n), Rat());
    private static Formula All(string n, Formula t, Formula f) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, f);
    private static Formula Ex(string n, Formula t, Formula f) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, f);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula And(params Formula[] terms) => terms.Aggregate((a,b) => Seq(Par(a), Sp, Land, Sp, Par(b)));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula Product(string i, Formula set, Formula body) => Seq(
        new Formula.Subscript(Prod, Seq(V(i), Sp, InMacro, Sp, set)), Sp, Par(body));
    private static Formula Integral(Formula f) => Ex("z", Int(), Eq(Cast(V("z"), Rat()), f));
    private static Formula Lambda(string i, Formula body) => Seq(Named("fun"),Sp,V(i),Sp,Mapsto,Sp,body);
    private static Formula ClaimBody()
    {
        Formula n=V("n"), r=V("R"), k=V("k"), t=Call("ratio",n);
        Formula a=Add(Cast(n,Rat()),D(1));
        Formula b=Add(Mul(D(2),Cast(n,Rat())),D(1));
        Formula c=Add(Mul(D(3),Cast(n,Rat())),D(1));
        Formula fixedPart = And(Integral(Div(Mul(D(3,8,5),t),a)),
            Integral(Div(Mul(D(5),t),b)), Integral(Div(t,c)),
            Integral(Div(Mul(D(7,7,0),t),Mul(Mul(a,b),c))),
            Integral(Div(t,Sub(Mul(D(1,2),Cast(n,Rat())),D(1)))));
        Formula rising = Call("rising_denominator",k,n,r);
        Formula signed = Call("signed_denominator",n,r);
        Formula u1Body = And(Ne(rising,D(0)),
            Integral(Div(Mul(Cast(Call("first_constant",r),Rat()),t),Cast(rising,Rat()))));
        Formula u1 = All("R",Nat(),Imp(Le(D(1),r),All("k",Nat(),
            Imp(And(Le(D(1),k),Le(k,D(3))),u1Body))));
        Formula u2Body = And(Ne(signed,D(0)),
            Integral(Div(Mul(Cast(Call("second_constant",r),Rat()),t),Cast(signed,Rat()))));
        Formula u2 = All("R",Nat(),Imp(Le(D(1),r),u2Body));
        Formula zero = Eq(Div(Call("ratio",D(0)),Sub(Mul(D(1,2),Cast(D(0),Rat())),D(1))),Sub(D(0),D(1)));
        return And(All("n",Nat(),And(fixedPart,u1,u2)),zero);
    }
}
