using System;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class PairedFaceChartsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local signed charts for the quotient of face-paired truncated coefficient simplices.",
        H("Paired face charts"),
        Blocks(
            Paragraph(Text("Let I=Fin(4), R3=Fin(3)->Real, and X consist of a:I->Real with "
                + "a(j)>=0, sum_j a(j)=1, and a(j)<=3/4 for every j; threeQuarters=3/4. DiscTopType is the class "
                + "of types T equipped with a discrete topology. Occ(T)=T times X.")),
            Paragraph(Text("Pairing(T) consists of an involution mate on T times I, with "
                + "mate(f)!=f for every face occurrence f, and full vertex permutations sigma(f). "
                + "They satisfy sigma(f)(f.2)=mate(f).2 and sigma(mate(f))=sigma(f)^(-1). "
                + "Transport sends a to the coefficient vector whose k-coordinate is "
                + "a(sigma(f)^(-1)(k)). A generating identification crosses face i precisely "
                + "when a(i)=0, and uses mate(t,i) and sigma(t,i). Q(P) is the raw quotient "
                + "by these generating identifications, with its quotient topology; q(P,a) "
                + "is its quotient projection.")),
            Paragraph(Text("Sets(Y) denotes subsets of Y. Open(U) means open in the topology "
                + "of its specified carrier, and Homeomorph(U,B) means homeomorphisms between "
                + "the two subsets with their induced topologies. coeff(a,j) is the j-coordinate "
                + "of the occurrence a. HSpace={w:R3 | w(0)>=0}. Cap(P,q) means that some "
                + "coefficient of a representative of q equals 3/4, and Seam(P,q) means "
                + "that some coefficient equals zero. Vertex permutations make both "
                + "predicates independent of the representative. eval(h,q,j) is coordinate j "
                + "of the image under h of the point q in its domain subset.")),
            Describe.Lean(
                DescribeId.Create("literal-paired-face-bicollar"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/PairedFaceCharts.literal_paired_face_bicollar"),
                H("Open bicollars at the interior of a paired face"),
                StatementSource.FromAuthor(F.Disp(Bicollar())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Choose positive depth smaller than each of the three "
                        + "positive coordinates. The two collars are disjoint, including when "
                        + "the paired faces belong to the same occurrence label. Every possible "
                        + "crossing in a collar uses its unique zero-coordinate face. The actual "
                        + "inverse pairing therefore proves saturation under the generated "
                        + "equivalence relation, and the quotient image is open.")),
                    Paragraph(Text("Use positive face depth on one side and negative depth on "
                        + "its mate, with two remaining coefficients as transverse coordinates. "
                        + "Reconstruction uses the absolute signed depth and the sum-one "
                        + "equation. The two inverse branches agree at zero depth by the "
                        + "literal face identification, and continuous pasting and the restricted "
                        + "quotient topology give continuity in both directions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("literal-paired-cap-halfchart"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/PairedFaceCharts.literal_paired_cap_halfchart"),
                H("Marked half-space charts where a cap meets a paired face"),
                StatementSource.FromAuthor(F.Disp(CapChart())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The zero label and cap label differ. The sum-one equation "
                        + "and nonnegativity make every other cap strict. Order the zero and cap "
                        + "coordinates first, and use cap slack b=3/4-a(c), one positive "
                        + "coefficient u, and signed depth s. The inverse vector in that order "
                        + "is (abs(s),3/4-b,u,1/4+b-abs(s)-u). Actual vertex transport "
                        + "supplies the mate branch.")),
                    Paragraph(Text("The two cap collars are saturated and have open quotient "
                        + "image. Reconstruction and continuous pasting yield the half-space "
                        + "homeomorphism. Within this neighborhood only the distinguished cap "
                        + "can be active and only the distinguished face depth can vanish. "
                        + "Thus the cap is exactly coordinate zero of the half-space and "
                        + "the seam is exactly zero signed depth.")),
                    Paragraph(Text("These charts concern the literal uniformly truncated "
                        + "coefficient quotient with the stated face pairing. Applying them "
                        + "to a hyperideal block requires a marked correspondence with its "
                        + "physical faces. Points on two zero-coordinate faces, metric angles, "
                        + "orientation and global geometric properties require further results."))),
                DescribeRole.Theorem))));

    private static Formula Bicollar()
    {
        var t=F.Id("T"); var p=F.Id("P"); var a=F.Id("a"); var i=F.Id("i");
        var j=F.Id("j"); var u=F.Id("U"); var b=F.Id("B");
        var assumptions=And(Eq(Call("coeff",a,i),F.D(0)),
            All("j",I,Imp(Ne(j,i),Lt(F.D(0),Call("coeff",a,j)))),
            All("j",I,Lt(Call("coeff",a,j),Call("threeQuarters"))));
        var result=Exists("U",Call("Sets",Call("Q",p)),And(Call("Open",u),
            In(Call("q",p,a),u),Exists("B",Call("Sets",R3),And(Call("Open",b),
                Call("Nonempty",Call("Homeomorph",u,b))))));
        return All("T",Call("DiscTopType"),All("P",Call("Pairing",t),
            All("a",Call("Occ",t),All("i",I,Imp(assumptions,result)))));
    }

    private static Formula CapChart()
    {
        var t=F.Id("T"); var p=F.Id("P"); var a=F.Id("a"); var i=F.Id("i");
        var c=F.Id("c"); var j=F.Id("j"); var u=F.Id("U"); var b=F.Id("B");
        var h=F.Id("h"); var q=F.Id("z");
        var assumptions=And(Eq(Call("coeff",a,i),F.D(0)),
            Eq(Call("coeff",a,c),Call("threeQuarters")),
            All("j",I,Imp(Ne(j,i),Lt(F.D(0),Call("coeff",a,j)))));
        var markings=And(All("z",u,Iff(Call("Cap",p,q),Eq(Call("eval",h,q,F.D(0)),F.D(0)))),
            All("z",u,Iff(Call("Seam",p,q),Eq(Call("eval",h,q,F.D(2)),F.D(0)))));
        var result=Exists("U",Call("Sets",Call("Q",p)),And(Call("Open",u),
            In(Call("q",p,a),u),Exists("B",Call("Sets",Call("HSpace")),And(Call("Open",b),
                Exists("h",Call("Homeomorph",u,b),markings)))));
        return All("T",Call("DiscTopType"),All("P",Call("Pairing",t),
            All("a",Call("Occ",t),All("i",I,All("c",I,Imp(assumptions,result))))));
    }

    private static Formula I => Call("Fin",F.D(4));
    private static Formula R3 => Call("R3");
    private static Formula Call(string n,params Formula[] a) => new Formula.FunctionCall(FormulaIdentifier.Create(n),[..a]);
    private static Formula Eq(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Ne(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.NotEqual,b);
    private static Formula Lt(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula In(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.MemberOf,b);
    private static Formula Iff(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula All(string v,Formula d,Formula b) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(v),d,b);
    private static Formula Exists(string v,Formula d,Formula b) => new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(v),d,b);
    private static Formula And(params Formula[] a)
    {
        if(a.Length==0)throw new ArgumentException("Empty conjunction");
        var r=a[^1];for(var i=a.Length-2;i>=0;i--)r=new Formula.Logic(a[i],FormulaLogicOperator.And,r);return r;
    }
}
