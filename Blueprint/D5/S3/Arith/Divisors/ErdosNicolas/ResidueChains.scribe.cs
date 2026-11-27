using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.ErdosNicolas;

internal sealed class ErdosNicolasResidueChainsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/ErdosNicolas/ResidueChains.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/erdosnicolas1989functions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "ResidueChains estimates", H("ResidueChains estimates"), Blocks(
            Node("residueProfile_antitone", "Comparison up to the symmetric residue", Antitone(),
                "For rational parameters, 0<r, r<=s and r+s<=p imply that the profile at s is " +
                "at most the profile at r. For each nonnegative offset a, the denominator " +
                "product increases by (s-r)(p-r-s). The reciprocal numerator is unchanged. " +
                "The two offsets zero and p give the comparison. Equality holds exactly when r=s " +
                "or r+s=p; the comparison is strict between these endpoints."),
            Node("residueProfile_small", "Exact polynomial criterion", PolynomialCriterion(),
                "Write D=p*(p-r)*(p+r)*(2p-r) and P=p^3-r*p^2-5*r^2*p+3*r^3. " +
                "For D!=0, both profile<=1/r iff P*D>=0 and profile<1/r iff P*D>0 " +
                "hold. For D>0 these reduce to the signs of P. The domain includes -p<r<p and " +
                "r=0. " +
                "The reciprocal 1/r cancels before clearing denominators; no r!=0 is needed. " +
                "All components away from the poles are covered. For D<0 the " +
                "sign reverses: p=1,r=3/2 has P=-13/8,D=-5/8. At poles the polynomial test " +
                "fails, " +
                "p=r=1 has P*D=0 although the profile is -1/2<1/r. " +
                "For k=1,2 and p>=7, or k=4 and p>=41/4, the strict polynomial margins " +
                "give profile<1/k at distance at least k from both ends. Pair and triple " +
                "bounds are strict. Modulo 7 a triple cannot have both endpoints at +/-1; " +
                "a middle square would be +/-1, whereas 2^2 and 3^2 are neither. " +
                "Thus every modulus p>=2 other than 4,5 and nonzero m with a divisor q of m " +
                "and q not congruent to +/-1 has divisor average strictly below 3/4. " +
                "Zero residues are included in the orbit comparisons, so p may divide m. " +
                "A divisor outside +/-1 has a prime factor outside +/-1, since products of " +
                "signed ones stay signed one. Thus q need not be prime. The threshold is " +
                "exact: p=5,q=2,m=4 gives 5939/2520>9/4, and p=4,m=2 gives 317/210>3/2. " +
                "The profile formula includes r=0,p with the correction +1/p (also p=0). " +
                "The constant is a sharp supremum: q=m=2 and primes p tending to infinity " +
                "give average tending to 3/4 from below. Conversely, if all divisor residues are " +
                "signed ones, every weight equals profile(p,1)>3/4. Thus the strict average " +
                "bound is equivalent to the existence of a divisor outside the signed classes. " +
                "The empty divisor set at m=0 makes both sides false. For p=0 or p=1, m=1 " +
                "makes the strict bound true with no divisor outside the signed classes. " +
                "For p in {2,3,6,7,8,9,10}, the complete finite ring comparisons give strict " +
                "pair and triple bounds, including zero residues. For p>=11 the symbolic " +
                "weight bounds give the same comparisons without any field assumption."),
            Node("residue_average_three_quarters", "Complete average classification",
                AverageCriterion(),
                "For every natural p>=2 other than 4 and 5, the strict divisor bound is " +
                "equivalent " +
                "to the existence of a divisor outside the two signed residue classes. No " +
                "coprimality condition on m or primality condition on either parameter is " +
                "needed. " +
                "Equality with three quarters of the divisor count holds exactly for m=0. " +
                "The weak bound holds exactly when m=0 or such a divisor exists. " +
                "For nonzero m with only signed-one residues, the sum is " +
                "card(divisors(m))*profile(p,1), strictly above the threshold."))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose) => Describe.Lean(
        DescribeId.Create("erdosnicolas-residuechains-" +
            name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))),
        DescribeRole.Theorem);
    private static Formula Antitone()
    {
        var p=V("p"); var r=V("r"); var s=V("s");
        var comparison=Le(Call("residueProfile",p,s),Call("residueProfile",p,r));
        var equality=new Formula.Logic(Eq(Call("residueProfile",p,s),
            Call("residueProfile",p,r)),FormulaLogicOperator.Iff,
            new Formula.Logic(Eq(r,s),FormulaLogicOperator.Or,Eq(Add(r,s),p)));
        var body=new Formula.Logic(comparison,FormulaLogicOperator.And,equality);
        return All("p","Q",All("r","Q",All("s","Q",
            Imp(Lt(D(0),r),Imp(Le(r,s),Imp(Le(Add(r,s),p),body))))));
    }

    private static Formula PolynomialCriterion()
    {
        var p=V("p"); var r=V("r");
        var polynomial=Add(Sub(Sub(new Formula.Power(p,D(3)),
            Mul(r,new Formula.Power(p,D(2)))),Mul(Mul(D(5),new Formula.Power(r,D(2))),p)),
            Mul(D(3),new Formula.Power(r,D(3))));
        var denominator=Mul(Mul(Mul(p,Sub(p,r)),Add(p,r)),Sub(Mul(D(2),p),r));
        var weak=new Formula.Logic(Le(Call("residueProfile",p,r),new Formula.Fraction(D(1),r)),
            FormulaLogicOperator.Iff,Le(D(0),Mul(polynomial,denominator)));
        var strict=new Formula.Logic(Lt(Call("residueProfile",p,r),new Formula.Fraction(D(1),r)),
            FormulaLogicOperator.Iff,Lt(D(0),Mul(polynomial,denominator)));
        var body=new Formula.Logic(weak,FormulaLogicOperator.And,strict);
        var regular=new Formula.Relation(denominator,FormulaRelationOperator.NotEqual,D(0));
        return All("p","Q",All("r","Q",Imp(regular,body)));
    }

    private static Formula AverageCriterion()
    {
        var p=V("p"); var m=V("m"); var d=V("d"); var q=V("q");
        var divisors=Call("divisors",m);
        var sum=Seq(Sum,Underscore,
            Grp(new Formula.Relation(d,FormulaRelationOperator.MemberOf,divisors)),
            Call("f",p,Mul(D(2),p),new Formula.Modulo(d,p)));
        var threshold=Mul(new Formula.Fraction(D(3),D(4)),Call("card",divisors));
        var cast=Seq(Open,q,Colon,Call("ZMod",p),Close);
        var residue=new Formula.Logic(
            new Formula.Relation(cast,FormulaRelationOperator.NotEqual,D(1)),
            FormulaLogicOperator.And,
            new Formula.Relation(cast,FormulaRelationOperator.NotEqual,new Formula.Negate(D(1))));
        var member=new Formula.Relation(q,FormulaRelationOperator.MemberOf,divisors);
        var support=new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create("q"),
            Seq(Mathbb,Grp(V("N"))),new Formula.Logic(member,FormulaLogicOperator.And,residue));
        var strict=new Formula.Logic(Lt(sum,threshold),FormulaLogicOperator.Iff,support);
        var equality=new Formula.Logic(Eq(sum,threshold),FormulaLogicOperator.Iff,Eq(m,D(0)));
        var emptyOrSupport=new Formula.Logic(Eq(m,D(0)),FormulaLogicOperator.Or,support);
        var weak=new Formula.Logic(Le(sum,threshold),FormulaLogicOperator.Iff,emptyOrSupport);
        var body=new Formula.Logic(strict,FormulaLogicOperator.And,
            new Formula.Logic(equality,FormulaLogicOperator.And,weak));
        var notFour=new Formula.Relation(p,FormulaRelationOperator.NotEqual,D(4));
        var notFive=new Formula.Relation(p,FormulaRelationOperator.NotEqual,D(5));
        return All("p","N",All("m","N",Imp(Le(D(2),p),Imp(notFour,Imp(notFive,body)))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, string type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
            Seq(Mathbb, Grp(V(type))), body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
