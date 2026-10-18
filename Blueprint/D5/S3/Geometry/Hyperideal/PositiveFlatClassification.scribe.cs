using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class PositiveFlatClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Hyperideal/PositiveFlatClassification.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The entire positive six-coordinate domain has precisely the native genuine or closed flat angle patterns.",
        H("Positive generalized lengths and flat sectors"), Blocks(
            Paragraph(Text("The six coordinates vary independently over the open interval (1,infinity), in the original order (12,13,14,34,24,23). Write phi(x,q)=TwoLengthAngleSum.rawCos(x,q) and alpha(x,q)=TwoLengthAngleSum.extendedAngle(x,q). The latter is arccos(max(-1,min(phi(x,q),1))). Both functions use FourCycleCurvature.frame and FourCycleEnvelopes.cosine. No upper coordinate bound, paired transverse lengths, coloring or symmetry is assumed.")),
            Paragraph(Text("Genuine(x) means -1<phi(x,q)<1 at all six positions. For k in Fin(3), first(k)=k and second(k)=k+3 in Fin(6). Sector(x,k) means phi(x,first(k))<=-1. These are the three opposite pairs. The equality fibers phi=-1 and phi=1 are included in the flat patterns.")),
            Node("positive-classification", "Complete native classification", "positive_classification", Classification(),
                "The common polynomial delta satisfies rawNum(x,q)^2-leftRad(x,q)rightRad(x,q)=(x(q)^2-1)delta(x) for every original frame. Positive radicands fix the square-root branches. Negative delta puts all raw values strictly inside (-1,1). For nonnegative delta, the cofactor triangle identity forces a negative numerator. Such a numerator forces its opposite coordinate product to dominate the other two opposite products, making the four adjacent numerators positive. A second cofactor triangle identity then makes the opposite numerator negative. The common square-gap identity places exactly that opposite pair at or below -1 and the other four values at or above 1. Clipping and the principal arccos endpoint laws give the stated complete angle pattern. The selected sector is unique."),
            Paragraph(Text("The classification is an analytic statement about the original formula. It does not construct a hyperideal polyhedron or assert existence of a common zero-curvature global length. The positive-domain and closed-sector conclusions are those required from the length theory attributed in CFMP_GEOMETRIC_REALIZATION.md Sections 50 and 64 to Luo-Yang, arXiv:1404.5365v2, Propositions 4.4-4.5 and Lemma 4.6. The Lean proof establishes the formula statement directly; the attribution is not an imported proof.")),
            Node("native-flat-budget", "Strict local logarithmic budget", "native_flat_budget", Budget(),
                "Let R=r^2-1, A=rad(r,a,d), B=rad(r,b,c). Apply finite Cauchy-Schwarz to U=(sqrt(R),a-d,sqrt(2(r+1)ad)) and V=(sqrt(R),c-b,sqrt(2(r+1)bc)). Their squared norms are A and B, and their inner product is R+(a-d)(c-b)+2(r+1)sqrt(abcd). Thus this inner product is at most sqrt(A)sqrt(B). Combining this bound with the original negative-cosine inequality gives (r-1)(o-1)>=ac+bd+2sqrt(abcd)>=4sqrt(abcd). Squaring nonnegative sides gives (r-1)^2(o-1)^2>=16abcd. Positive logarithm arguments and the exact product, quotient and power laws give the displayed budget. Both correction logarithms are strictly positive. The inclusive flat boundary remains in scope. No sharpness-at-infinity or equality characterization is asserted."))));

    private static DocumentBlock Node(string id, string title, string decl, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + decl), H(title),
            StatementSource.FromAuthor(F.Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Classification()
    {
        var x=F.Id("x"); var q=F.Id("q"); var k=F.Id("k"); var j=F.Id("j");
        var zero=F.D(0); var one=F.D(1); var pi=F.Id("pi"); var fin=Call("Fin",F.D(6));
        var three=Call("Fin",F.D(3)); var real=F.Id("Real");
        var positive=All([("q",fin)],Lt(one,Call("value",x,q)));
        Formula Sector(Formula n) => Call("Sector",x,n);
        var unique=Exists("k",three,And(Sector(k),All([("j",three)],Imp(Sector(j),Eq(j,k)))));
        var atPair=Or(Eq(q,Call("first",k)),Eq(q,Call("second",k)));
        var offPair=And(Ne(q,Call("first",k)),Ne(q,Call("second",k)));
        var pattern=All([("q",fin)],And(Imp(atPair,Eq(Call("alpha",x,q),pi)),Imp(offPair,Eq(Call("alpha",x,q),zero))));
        var clauses=And(
            Iff(Call("Genuine",x),All([("q",fin)],And(Lt(zero,Call("alpha",x,q)),Lt(Call("alpha",x,q),pi)))),
            Or(Call("Genuine",x),unique),
            All([("k",three)],And(Iff(Sector(k),Le(Call("phi",x,Call("second",k)),Neg(one))),Iff(Sector(k),pattern))));
        return All([("x",Call("Function",fin,real))],Imp(positive,clauses));
    }

    private static Formula Budget()
    {
        string[] names=["r","a","b","o","c","d"];
        var v=names.Select(F.Id).ToArray(); var r=v[0];var a=v[1];var b=v[2];var o=v[3];var c=v[4];var d=v[5];
        var one=F.D(1); var two=F.D(2);
        var correction=Add(Add(Call("log",F.D(1,6)),Mul(two,Call("log",Div(r,Sub(r,one))))),Mul(two,Call("log",Div(o,Sub(o,one)))));
        var lhs=Sub(Sub(Sub(Sub(Add(Mul(two,Call("log",r)),Mul(two,Call("log",o))),Call("log",a)),Call("log",b)),Call("log",c)),Call("log",d));
        return All(names.Select(n=>(n,(Formula)F.Id("Real"))).ToArray(),
            Imp(And([..v.Select(t=>Lt(one,t)),Le(Call("cosine",v),Neg(one))]),
                And(Le(correction,lhs),Lt(Call("log",F.D(1,6)),correction))));
    }
    private static Formula All((string Name,Formula Type)[] v,Formula b)=>new Formula.BindMany(FormulaQuantifier.ForAll,[..v.Select(t=>new Formula.BoundVariable(FormulaIdentifier.Create(t.Name),t.Type))],b);
    private static Formula Exists(string n,Formula t,Formula b)=>new Formula.BindMany(FormulaQuantifier.Exists,[new Formula.BoundVariable(FormulaIdentifier.Create(n),t)],b);
    private static Formula Call(string n,params Formula[] a)=>new Formula.Apply(F.Id(n),[..a]);
    private static Formula And(params Formula[] a)=>a.Aggregate((x,y)=>new Formula.Logic(x,FormulaLogicOperator.And,y));
    private static Formula Or(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Or,b);
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Ne(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.NotEqual,b);
    private static Formula Lt(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Le(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Add(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Mul(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Div(Formula a,Formula b)=>new Formula.Fraction(a,b);
    private static Formula Neg(Formula a)=>Sub(F.D(0),a);
}
