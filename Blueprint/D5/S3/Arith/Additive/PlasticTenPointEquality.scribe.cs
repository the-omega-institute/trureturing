using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive;

internal sealed class PlasticTenPointEqualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exactly four integer patterns, up to translation, attain the ten-point plastic-template bound and its corresponding real-power sumset size.",
        H("The four ten-point equality patterns"),
        Blocks(
            Paragraph(Text("Let E be any finite subset of the integers with exactly ten elements. Write C(E) for the total number of translates contained in E of "
                + "{0,2,3,4}, {0,3,5,6}, {0,5,7}, and {0,5,8,9}. These copies can equivalently be counted by their unique right endpoints. "
                + "All intervals below contain integers. Define S₀=[0,9], S₁={0}∪[2,10], S₂={0,1}∪[3,10], and S₃={0,3}∪[5,12]. "
                + "The notation translate(a,S) means {a+z : z ∈ S}, with a an arbitrary integer. "
                + "For a real r, let A(r,E)={rᶻ : z ∈ E}; its sumset is an actual finite subset of the reals. "
                + "Negative exponents, negative translations, and arbitrarily large initial gaps are allowed. The statement concerns ten points only.")),
            Describe.Lean(DescribeId.Create("plastic-ten-point-complete-equality"),
                DeclarationHandle.Create("D5/S3/Arith/Additive/PlasticTenPointEquality.whole_ten_point_equality"),
                H("Complete ten-point classification"), StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/ArithUnits/berczes2010geometric")),
                Blocks(Paragraph(Text("The finite-memory upper bound assigns a potential to every actual prefix. "
                    + "If a ten-point set has fourteen copies, its last potential is fourteen. "
                    + "At each removal of the maximum, the actual increment identity and the transition upper bound force the preceding prefix and its transition to be tight. "
                    + "The tight-predecessor constraints reduce the possibilities to prefixes of the four displayed models. "
                    + "For each model separately, the extension calculation identifies the entire new prefix, rather than only its memory state. "
                    + "Thus distinct histories sharing a state are not identified. This yields an induction on the actual finite set and its maximum, not a check of four examples alone. "
                    + "Every allowed clipped gap is at most three, so it equals the original gap; clipping therefore introduces no restriction on the input set. "
                    + "This argument uses upper-bound potentials and tightness, without requiring that every table entry be reachable or be an exact optimum. "
                    + "Conversely, each of the four complete models has total count fourteen, and translation preserves the count. "
                    + "For r>1 with r³=r+1, the collision identity gives |A(r,E)+A(r,E)|+C(E)=55. "
                    + "Consequently the real sumset has cardinality forty-one exactly for those same four translated patterns."))),
                DescribeRole.Theorem)),
        []));

    private static Formula V(string x) => F.Id(x);
    private static Formula P(Formula x) => Seq(Open,x,Close);
    private static Formula Call(string x, params Formula[] a) => new Formula.Apply(Seq(Operatorname,Grp(V(x))),[..a]);
    private static Formula All(string x, Formula t, Formula b) => Seq(Forall,Sp,P(Seq(V(x),Sp,Colon,Sp,t)),Comma,Sp,b);
    private static Formula Ex(string x, Formula t, Formula b) => Seq(Exists,Sp,P(Seq(V(x),Sp,Colon,Sp,t)),Comma,Sp,b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a,op,b);
    private static Formula Eq(Formula a, Formula b) => Rel(a,FormulaRelationOperator.Equal,b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Card(Formula a) => Seq(Lvert,Sp,a,Rvert,Sp);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(P(a),FormulaLogicOperator.Implies,P(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(P(a),FormulaLogicOperator.And,P(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(P(a),FormulaLogicOperator.Or,P(b));
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(P(a),FormulaLogicOperator.Iff,P(b));
    private static Formula Statement()
    {
        var e=V("E"); var a=V("a"); var r=V("r");
        var integers=Seq(Mathbb,Grp(V("Z"))); var reals=Seq(Mathbb,Grp(V("R")));
        Formula Shape(byte j) => Eq(e,Call("translate",a,new Formula.Subscript(V("S"),D(j))));
        var classified=Ex("a",integers,Or(Shape(0),Or(Shape(1),Or(Shape(2),Shape(3)))));
        var countCase=IffF(Eq(Call("C",e),D(1,4)),classified);
        var powers=Call("A",r,e);
        var sumCase=IffF(Eq(Card(Add(powers,powers)),D(4,1)),classified);
        var realCase=All("r",reals,Imp(Rel(D(1),FormulaRelationOperator.LessThan,r),
            Imp(Eq(new Formula.Power(r,D(3)),Add(r,D(1))),sumCase)));
        return Disp(All("E",Call("Finset",integers),Imp(Eq(Card(e),D(1,0)),And(countCase,realCase))));
    }
}
