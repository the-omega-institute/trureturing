using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Gluing;

internal sealed class RadialProfileSimplexHomeomorphDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit radial interpolation on the actual closed tetrahedron and its original face-generated quotient.",
        H("Radial profiles on the closed tetrahedron"),
        Blocks(
            Paragraph(Text("Let I=Fin 4, and let K be the standard real simplex: nonnegative coordinate functions whose sum is one. The vertex e(i) is the coordinate unit vector. O(i) is the actual opposite face, consisting of u in K with coordinate i equal to zero. The radius type is the closed interval [0,1/2], and A is [1/4,23/48]. A profile family alpha gives a map O(i) to A for each i. No differentiability or Lipschitz condition on these profiles is assumed.")),
            Paragraph(Text("Write R(i,u,r)=(1-r)e(i)+ru. The central region consists of x in K with every coordinate at most 1/2. For a in A, f(a,r) equals 4ar for r at most 1/4, a+4(1/2-a)(r-1/4) for r between 1/4 and 1/2, and r above 1/2. The inverse g(a,s) equals s/(4a) for s at most a, 1/4+(s-a)/(4(1/2-a)) between a and 1/2, and s above 1/2. Both formulas are continuous jointly in the parameter and scalar, including the moving inverse interface s=a. The proof establishes both inverse identities on the real line; their restrictions preserve [0,1/2].")),
            Paragraph(Text("Phi(alpha) sends R(i,u,r) to R(i,u,f(alpha(i,u),r)); Psi(alpha) uses g on the same ray. Both fix the central region. The chart construction uses the disjoint union of all O(i) times [0,1/2] and the entire central region. Its projection onto K is a continuous surjection from a compact space. Equality of projections implies equality of the transformed projections: zero radius collapses to the same old vertex, equal nonzero rays recover their directions, distinct corners overlap only at radius 1/2, and a corner meets the central region in the entire triangle with coordinate i equal to 1/2. Thus no continuous corner selection is used. Continuity descends through that compact quotient map, including all directions at each apex. This does not replace the original face generator used below.")),
            Describe.Lean(DescribeId.Create("radial-homeomorph-formulas"),
                DeclarationHandle.Create("D5/S3/Geometry/Gluing/RadialProfileSimplexHomeomorph.radial_homeomorph_spec"),
                H("Constructed homeomorphism, faces, naturality and apex estimates"),
                StatementSource.FromAuthor(F.Disp(Generic())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("H(alpha,h) is the constructed homeomorphism for a continuous profile family; its forward function is Phi and inverse is Psi. P(rho) acts by coordinate j equal to the old coordinate rho inverse(j). U(rho,i,u) is this action on the opposite face. The displayed covariance condition transports an arbitrary profile family alpha to beta; equivariance is proved from the actual ray formulas. Zero preservation applies to every coordinate and every set J of zero coordinates, including the empty and full sets. The coordinate estimates near each vertex are uniform in direction and remain valid while directions oscillate. There is no global Lipschitz assertion for continuous profiles."))), DescribeRole.Theorem),
            Paragraph(Text("The concrete source profile uses only the three non-i coordinates, enumerated by Fin.succAbove. Let M be their maximum, m their minimum, w=1-M-m, and B=max(2(M-w),max(3(w-m),4m)). Then a(i,u)=1/(1+M+B). Weak inequalities and tied or zero coordinates are retained. From the sum-one and nonnegativity conditions the proof derives 0<=m<=w<=M<=1, then B<=3-M and 48/23<=1+M+B; hence 1/4<=a<=23/48. Finite maxima and minima are continuous. Their order characterizations show that a is covariant under every vertex permutation. The source homeomorphism is H instantiated with this derived continuous bounded profile.")),
            Describe.Lean(DescribeId.Create("radial-original-relation"),
                DeclarationHandle.Create("D5/S3/Geometry/Gluing/RadialProfileSimplexHomeomorph.source_original_relation"),
                H("Exact original face generator and its complete equivalence closure"),
                StatementSource.FromAuthor(F.Disp(Original())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any topological tag type T, next:T times I to T and sigma:T times I to Perm(I), seam(a,b) means that some original face f has a's coordinate f equal to zero and b=(next(a.tag,f),P(sigma(a.tag,f),a.point)). No adjacency, inverse-pairing, freeness or distinctness assumption is imposed. TaggedH(t,x)=(t,Hsource(x)). The same source homeomorphism preserves the exact generator in both directions. Induction on Relation.EqvGen proves both directions for arbitrary finite generating chains, using the actual inverse for the reverse implication. Face witnesses, labels, self-pairings and repeated occurrences are preserved.")),
                    Paragraph(Text("originalQuotientHomeomorph is the direct application of Homeomorph.Quotient.congr to TaggedH and the proved equivalence-closure biconditional. It is not a theorem assuming an arbitrary homeomorphism or relation compatibility. The tagged type need not be finite for this topological quotient construction, so in particular it covers every finite tagged family."))), DescribeRole.Theorem),
            Paragraph(Text("The source method is classical and no novelty is claimed. This result concerns the standard simplex formulas and the unmarked original face-generated quotient. It does not prove the literal second-subdivision star descriptions of source 70.3–70.4, identify those stars with the radial sublevel sets in 70.9, or supply the marked identification with the specified source (N,boundary N). Restricted star quotients require those geometric inputs and a saturation proof before restricting EqvGen. No completion of section 70 or of CFMP sections 1–125 is asserted.")))));

    private static Formula Generic()
    {
        var a=F.Id("alpha"); var h=F.Id("h"); var i=F.Id("i"); var u=F.Id("u");
        var r=F.Id("r"); var x=F.Id("x"); var j=F.Id("j"); var rho=F.Id("rho");
        var beta=F.Id("beta"); var J=F.Id("J");
        Formula H(Formula y)=>Call("H",a,h,y);
        Formula G(Formula y)=>Call("Hinverse",a,h,y);
        Formula Ray(Formula radius)=>Call("R",i,u,radius);
        Formula Co(Formula y)=>Call("coord",y,j);
        var ai=Call("profile",a,i,u);
        var zero=F.D(0); var q=Call("rational",F.D(1),F.D(4));
        var cov=All("i",F.Id("I"),All("u",Call("O",i),
            Eq(Call("profile",beta,Call("apply",rho,i),Call("U",rho,i,u)),ai)));
        Formula Natural(string map)=>All("beta",F.Id("Profiles"),All("rho",Call("Perm",F.Id("I")),
            Implies(cov,All("x",F.Id("K"),Eq(Call(map,beta,Call("P",rho,x)),
                Call("P",rho,Call(map,a,x)))))));
        var near=All("i",F.Id("I"),All("u",Call("O",i),All("r",F.Id("Radius"),
            Implies(Le(r,q),All("j",F.Id("I"),And(
                Le(Call("abs",Sub(Co(Call("Phi",a,Ray(r))),Co(Call("e",i)))),
                    Mul(Call("rational",F.D(2,3),F.D(1,2)),r)),
                Le(Call("abs",Sub(Co(Call("Psi",a,Ray(r))),Co(Call("e",i)))),r)))))));
        var statements=And(
            All("i",F.Id("I"),Eq(H(Call("e",i)),Call("e",i))),
            All("i",F.Id("I"),All("u",Call("O",i),All("r",F.Id("Radius"),
                Eq(H(Ray(r)),Ray(Call("f",ai,r)))))),
            All("i",F.Id("I"),All("u",Call("O",i),All("r",F.Id("Radius"),
                Eq(G(Ray(r)),Ray(Call("g",ai,r)))))),
            All("x",F.Id("Central"),And(Eq(H(x),x),Eq(G(x),x))),
            All("x",F.Id("K"),All("j",F.Id("I"),Iff(Eq(Co(H(x)),zero),Eq(Co(x),zero)))),
            All("x",F.Id("K"),All("j",F.Id("I"),Iff(Eq(Co(G(x)),zero),Eq(Co(x),zero)))),
            All("J",Call("Sets",F.Id("I")),All("x",F.Id("K"),Iff(
                All("j",F.Id("I"),Implies(In(j,J),Eq(Co(H(x)),zero))),
                All("j",F.Id("I"),Implies(In(j,J),Eq(Co(x),zero)))))),
            Natural("Phi"),Natural("Psi"),near,
            All("i",F.Id("I"),All("u",Call("O",i),Eq(H(Ray(q)),Ray(ai)))));
        return All("alpha",F.Id("Profiles"),All("h",Call("ContinuousProfiles",a),statements));
    }

    private static Formula Original()
    {
        var t=F.Id("T");var next=F.Id("next");var sigma=F.Id("sigma");
        var a=F.Id("a");var b=F.Id("b");var rho=F.Id("rho");var i=F.Id("i");var u=F.Id("u");
        var X=Product(t,F.Id("K"));var ports=Product(t,F.Id("I"));
        Formula H(Formula z)=>Call("TaggedH",z);
        Formula S(Formula x,Formula y)=>Call("seam",next,sigma,x,y);
        Formula R(Formula x,Formula y)=>Call("EqvGen",Call("seam",next,sigma),x,y);
        return All("T",F.Id("Types"),Implies(Call("TopologicalSpace",t),
            All("next",new Formula.TypeArrow(ports,t),
            All("sigma",new Formula.TypeArrow(ports,Call("Perm",F.Id("I"))),And(
                All("rho",Call("Perm",F.Id("I")),All("i",F.Id("I"),All("u",Call("O",i),
                    Eq(Call("sourceProfile",Call("apply",rho,i),Call("U",rho,i,u)),Call("sourceProfile",i,u))))),
                All("a",X,All("b",X,Iff(S(H(a),H(b)),S(a,b)))),
                All("a",X,All("b",X,Iff(R(H(a),H(b)),R(a,b)))))))));
    }
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(name),domain,body);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name),[..args]);
    private static Formula And(params Formula[] clauses)
    { var r=clauses[^1]; for(var i=clauses.Length-2;i>=0;i--)r=new Formula.Logic(clauses[i],FormulaLogicOperator.And,r);return r; }
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Le(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula In(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.MemberOf,b);
    private static Formula Iff(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Implies(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Mul(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Sub(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Product(Formula a,Formula b)=>F.Seq(F.Open,a,F.Close,F.Sp,F.Times,F.Sp,F.Open,b,F.Close);
}
