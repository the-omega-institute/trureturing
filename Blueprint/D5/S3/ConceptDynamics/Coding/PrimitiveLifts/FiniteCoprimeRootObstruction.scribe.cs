using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PrimitiveLifts;

internal sealed class FiniteCoprimeRootObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteCoprimeRootObstruction.";
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n),t);
    private static Formula Q(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,[..v],f);
    private static Formula Ex(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.Exists,[..v],f);
    private static Formula And(Formula a,Formula b) => Seq(Open,Open,a,Close,Sp,Land,Sp,Open,b,Close,Close);
    private static Formula Imp(Formula a,Formula b) => Seq(Open,Open,a,Close,Sp,Implies,Sp,Open,b,Close,Close);
    private static Formula Pow(Formula x,byte n) => new Formula.Power(x,D(n));
    private static Formula Pair(Formula q,byte r) => Call("pair",q,Call("ofAdd",D(r)));
    private static Formula Root(byte n) => Ex(Equal(Pow(I("x"),n),I("h")),B("x",I("H")));
    private static Formula Claim => Imp(Root(2),Imp(Root(3),Root(6)));
    private static Formula NoSixth => Q(Seq(Pow(I("x"),6),Sp,Neq,Sp,I("h")),B("x",I("H")));
    private static Formula Noncommutative => Ex(Seq(Call("mul",I("x"),I("y")),Sp,Neq,Sp,
        Call("mul",I("y"),I("x"))),B("x",I("H")),B("y",I("H")));
    private static Formula Exact => And(Equal(Call("NatCard",I("H")),D(7,2)),
        And(Equal(Call("orderOf",I("h")),D(6)),
        And(Equal(Pow(Pair(Call("a",D(1)),6),2),I("h")),
        And(Equal(Pow(Pair(Call("a",D(2)),1),3),I("h")),And(NoSixth,Noncommutative)))));
    private static DocumentBlock Item(string selector,string title,Formula f,string text,DescribeRole role) =>
        Describe.Lean(DescribeId.Create("finite-coprime-root-"+(selector == "H" ? "group" : selector.Replace("_","-").ToLowerInvariant())),
            DeclarationHandle.Create(Prefix+selector),H(title),StatementSource.FromAuthor(Disp(f)),
            AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square and cube roots can coexist without a sixth root in an explicit finite nonabelian group.",
        H("Coprime roots and a finite holonomy obstruction"),Blocks(
        Item("H","The actual semidirect product",Equal(I("H"),
            Call("SemidirectProduct",Call("QuaternionGroup",D(2)),
                Call("Multiplicative",Call("ZMod",D(9))),I("rho"))),
            "Write Q8={1,-1,i,-i,j,-j,k,-k} and C9=<t>. In Mathlib coordinates i=a(1), j=xa(0), k=xa(3), and -1=a(2). The automorphism alpha cycles i to j, j to k, and k to i. Its complete coordinate map is a(0)->a(0), a(1)->xa(0), a(2)->a(2), a(3)->xa(2), xa(0)->xa(3), xa(1)->a(3), xa(2)->xa(1), xa(3)->a(1). Its inverse is alpha squared. The action rho sends ofAdd(r) to alpha raised to the least nonnegative representative of r in ZMod 9. Multiplication is (q,t^r)(s,t^u)=(q*alpha^r(s),t^(r+u)). The upstream QuaternionGroup and SemidirectProduct group structures supply associativity, identity and inverses; this construction does not replace Q8 by a new multiplication table. The public Fintype instance is transported from Q8 times C9 using SemidirectProduct.equivProd.",DescribeRole.Definition),
        Item("h","The order-six holonomy",Equal(I("h"),Pair(Call("a",D(2)),3)),
            "Thus h=(-1,t^3). The specified square root is (i,t^6), and the specified cube root is (-1,t). All coordinates are elements of the actual semidirect product H.",DescribeRole.Definition),
        Item("claim","Coprime-root sufficiency at this element",Equal(I("claim"),Claim),
            "The assertion says that existence of a square root and existence of a cube root of this h imply existence of a sixth root in the same group H. There are no assumptions of commutativity or of compatibility between the two roots.",DescribeRole.Definition),
        Item("result","Failure of coprime-root sufficiency",Seq(Neg,Sp,I("claim")),
            "Both antecedents hold, using (i,t^6) and (-1,t). Evaluation of the actual semidirect-product sixth power for every one of its 72 elements proves that none equals h. The finite calculation is checked by the Lean kernel with decide; it uses neither native_decide nor a compiler-trust axiom. This refutes the asserted sufficiency rather than assuming a root obstruction as a premise.",DescribeRole.Theorem),
        Item("finite72_obstruction","The exact finite nonabelian obstruction",Exact,
            "The group has exactly 72 elements, h has exact order six, the displayed elements have square and cube equal to h, every sixth power differs from h, and there exist noncommuting elements. The cardinality follows from SemidirectProduct.card and QuaternionGroup.card. Exact order is proved by h^6=1 and the five positive smaller powers differing from 1. The two noncommuting elements can be chosen as (i,1) and (j,1), so noncommutativity already occurs inside the embedded upstream Q8.",DescribeRole.Theorem),
        Paragraph(Text("For return-chart arithmetic, take positive exponent k=6, period d=1 and holonomy h. The prospective block equation at a divisor ell of 6 asks for b^(6/ell)=h. The verified cube root supplies ell=2, the verified square root supplies ell=3, and h itself supplies ell=6. The missing sixth root excludes ell=1. Thus the permitted divisor lengths are exactly 2,3,6, whose additive monoid is {0} union {n>=2}: every even n>=2 is a sum of twos, and every odd n>=3 is three plus a sum of twos. Their gcd is one, yet multiplicity one is absent. This arithmetic explains why a gcd condition loses finite multiplicity information. The group theorem proves the concrete root facts only; interpreting that monoid as a complete classification of finite atlas families additionally requires the general finite-family theorem and its hypotheses. No such atlas-family classification is assumed or proved here.")),
        Paragraph(Text("The construction is repository-derived, using the classical quaternion group and semidirect-product operations provided by pinned Mathlib. QuaternionGroup is attributed upstream to Julian Kuelshammer and SemidirectProduct to Chris Hughes, under Mathlib's Apache 2.0 license. The quaternion-group background is also described in Groupprops, Quaternion group, https://groupprops.subwiki.org/wiki/Quaternion_group. The Q8-by-C9 semidirect-product family also occurs in the Math StackExchange question Semi directProduct and Maximal subgroup in gap, https://math.stackexchange.com/questions/291350/semi-directproduct-and-maximal-subgroup-in-gap; that question concerns maximal subgroups, rather than the root assertion here. No priority, minimal-order, or exhaustive literature-absence claim is made for this finite counterexample."))
        )));
}
