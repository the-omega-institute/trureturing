using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class AsynchronousMassRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create("Positive asynchronous invariance forces every real multilinear mass to factor.",H("Asynchronous rigidity of all multilinear masses"),Blocks(
        Paragraph(Text("At a global maximum on K to the power I, strict positivity of the scalar weights forces every updated scalar term to equal that maximum. For each slot, its maximizing section is a nonempty compact convex invariant subset of K. The Markov–Kakutani theorem supplies a fixed point in that section, and the full real fixed dual identifies it with the same mass-one fixed vector sigma. Replacing finitely many slots by sigma preserves the maximum. Apply the argument to minus F to obtain the same minimum. The normalized cube is therefore constant. Since K spans the real carrier, Mathlib MultilinearMap.ext_of_span_eq_top applied to the subtype of K extends this equality to every real tuple. This applies to periodic maps and boundary sigma. It asserts neither convergence of Phi iterates nor convergence of asynchronous iterates, rates, physical copies, or a tensor cone.")),
        Describe.Lean(DescribeId.Create("mass-asynchronousmassrigidity-entire-base-geometry"),DeclarationHandle.Create("D5/S3/Quantum/Analysis/AsynchronousMassRigidity.entire_base_geometry"),H("The original compact convex spanning base"),StatementSource.FromAuthor(Disp(BaseGeometry())),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("For any nonzero finite-dimensional real normed space, a closed generating proper cone C and a real linear mass u strictly positive on every nonzero element of C, the entire set of x in C with u(x)=1 is nonempty, compact, convex and spans the real carrier. This set is CircuitBalancedConfirmation.base on C.toPointedCone and the same u. CircuitBalancedConfirmation.base_compact and base_convex give compactness and convexity directly. Its pure_span gives full span of the extreme points; their inclusion in the base gives full base span, and a spanning base in a nonzero carrier is nonempty. No new compactness or normalization argument is needed. This combination supplies the base used by the algebraic tensor fixed-dual theorem and both original mass results."))),DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("mass-asynchronousmassrigidity-exists-fixed-mem"),DeclarationHandle.Create("D5/S3/Quantum/Analysis/AsynchronousMassRigidity.exists_fixed_mem"),H("Fixed points inside invariant compact convex sets"),StatementSource.FromAuthor(Disp(Existence())),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("Phi is any real linear endomorphism of a finite-dimensional real normed space. Each nonempty compact convex invariant B contains a fixed point. Apply D5.S3.Geometry.FixedPoint.MarkovKakutani.exists_common_fixed_point to the constant Unit family of the continuous affine map induced by Phi. Finite dimensionality supplies continuity; invariance is unchanged and commutation is reflexive. No mixing premise is needed."))),DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("mass-asynchronousmassrigidity-fixed-eq-mass-smul"),DeclarationHandle.Create("D5/S3/Quantum/Analysis/AsynchronousMassRigidity.fixed_eq_mass_smul"),H("Every fixed vector has its original scalar mass"),StatementSource.FromAuthor(Disp(Uniqueness())),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("The original mass u is preserved by Phi, and every real linear functional fixed by precomposition with Phi is a scalar multiple of u. Apply rank-nullity to Phi minus the identity and to its real dual; equality of their ranks bounds the real fixed space by one dimension. A fixed sigma of mass one spans it, and applying the original u determines the scalar: every fixed x equals u(x) times sigma. Sigma may be on the cone boundary; this statement needs no cone or interior hypothesis."))),DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("mass-asynchronousmassrigidity-multilinear-mass-factorization"),DeclarationHandle.Create("D5/S3/Quantum/Analysis/AsynchronousMassRigidity.multilinear_mass_factorization"),H("Factorization on all real inputs"),StatementSource.FromAuthor(Disp(Factorization())),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("I is any finite index type. Alpha is strictly positive at every index and sums to one. K is a compact convex spanning normalized set, and Phi preserves K and u. The original-cone applications supply the entire normalized base. The full real fixed dual is the line of u. F is an arbitrary real multilinear form; its continuity is proved by a finite basis expansion. Its asynchronous identity need only hold on every normalized tuple. The conclusion holds on all real inputs, with no additional factorization or fixed-tensor hypothesis."))),DescribeRole.Theorem))));

    private static Formula V(string s)=>F.Id(s);
    private static Formula R=>Call("Real");
    private static Formula One=>D(1);
    private static Formula Zero=>D(0);
    private static Formula Call(string s,params Formula[] a)=>new Formula.FunctionCall(FormulaIdentifier.Create(s),[..a]);
    private static Formula At(Formula f,params Formula[] a)=>new Formula.Apply(f,[..a]);
    private static Formula App(string s,params Formula[] a)=>At(V(s),a);
    private static Formula All(string s,Formula t,Formula b)=>new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),t,b);
    private static Formula Ex(string s,Formula t,Formula b)=>new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(s),t,b);
    private static Formula Lam(string s,Formula t,Formula b)=>Seq(Grp(V(s),Colon,t),Mapsto,Sp,b);
    private static Formula And(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Eqf(Formula a,Formula b)=>Equal(a,b);
    private static Formula Lt(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Mul(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Smul(Formula a,Formula b)=>Call("smul",a,b);
    private static Formula Arrow(Formula a,Formula b)=>new Formula.TypeArrow(a,b);
    private static Formula In(Formula x,Formula s)=>Call("Mem",x,s);
    private static Formula Assuming(Formula b,params Formula[] p){for(var i=p.Length-1;i>=0;i--)b=Imp(p[i],b);return b;}
    private static Formula Lm(Formula a,Formula b)=>Call("LinearMap",R,a,b);
    private static Formula Dual(Formula a)=>Call("Dual",R,a);
    private static Formula Span(Formula s)=>Call("span",R,s);
    private static Formula Top(Formula a)=>Call("top",Call("Submodule",R,a));
    private static Formula Space(string n,Formula b,bool nontrivial=false){var a=V(n);var body=Seq(OpenBracket,Call("NormedAddCommGroup",a),CloseBracket,Sp,OpenBracket,Call("NormedSpace",R,a),CloseBracket,Sp,OpenBracket,Call("FiniteDimensional",R,a),CloseBracket,Sp,nontrivial?Seq(OpenBracket,Call("Nontrivial",a),CloseBracket,Sp,b):b);return All("v"+n,Call("Universe"),All(n,Call("Type",V("v"+n)),body));}
    private static Formula Indices(Formula b)=>All("vI",Call("Universe"),All("I",Call("Type",V("vI")),Seq(OpenBracket,Call("Fintype",V("I")),CloseBracket,Sp,OpenBracket,Call("DecidableEq",V("I")),CloseBracket,Sp,b)));
    private static Formula FullDual(string p,string u,string a)=>All("f",Dual(V(a)),Imp(Eqf(Call("comp",V("f"),V(p)),V("f")),Ex("c",R,Eqf(V("f"),Smul(V("c"),V(u))))));
    private static Formula Cube=>Call("pi",Call("univ",V("I")),Lam("i",V("I"),V("K")));
    private static Formula WeightPos=>All("i",V("I"),Lt(Zero,App("alpha",V("i"))));
    private static Formula WeightSum=>Eqf(Call("sum",V("alpha")),One);
    private static Formula ProductMass(string u,Formula a)=>Call("prod",Lam("i",V("I"),App(u,At(a,V("i")))));
    private static Formula Update(Formula a,Formula i)=>Call("update",a,i,App("Phi",At(a,i)));

    private static Formula BaseGeometry()
    {
        var b=Call("base",Call("toPointedCone",V("C")),V("u"));
        var positive=All("x",V("A"),Assuming(Lt(Zero,App("u",V("x"))),In(V("x"),V("C")),Seq(V("x"),Sp,Neq,Sp,Zero)));
        var result=And(Call("Nonempty",b),And(Call("IsCompact",b),And(Call("Convex",R,b),Eqf(Span(b),Top(V("A"))))));
        return Space("A",All("C",Call("ProperCone",R,V("A")),All("u",Dual(V("A")),Assuming(result,Eqf(Span(V("C")),Top(V("A"))),positive))),true);
    }
    private static Formula Existence()=>Space("A",All("Phi",Lm(V("A"),V("A")),All("B",Call("Set",V("A")),Assuming(Ex("x",V("A"),And(In(V("x"),V("B")),Eqf(App("Phi",V("x")),V("x")))),Call("IsCompact",V("B")),Call("Nonempty",V("B")),Call("Convex",R,V("B")),Call("MapsTo",V("Phi"),V("B"),V("B"))))));
    private static Formula Uniqueness()=>Space("A",All("Phi",Lm(V("A"),V("A")),All("u",Dual(V("A")),Assuming(All("sigma",V("A"),Assuming(All("x",V("A"),Imp(Eqf(App("Phi",V("x")),V("x")),Eqf(V("x"),Smul(App("u",V("x")),V("sigma"))))),Eqf(App("Phi",V("sigma")),V("sigma")),Eqf(App("u",V("sigma")),One))),Eqf(Call("comp",V("u"),V("Phi")),V("u")),FullDual("Phi","u","A")))));

    private static Formula Harmonic=>All("a",Arrow(V("I"),V("A")),Imp(In(V("a"),Cube),Eqf(App("F",V("a")),Call("sum",Lam("i",V("I"),Mul(App("alpha",V("i")),App("F",Update(V("a"),V("i")))))))));
    private static Formula Factorization()=>Space("A",Indices(All("Phi",Lm(V("A"),V("A")),All("u",Dual(V("A")),All("K",Call("Set",V("A")),All("alpha",Arrow(V("I"),R),All("F",Call("MultilinearMap",R,Call("constantFamily",V("I"),V("A")),R),Assuming(Ex("c",R,All("a",Arrow(V("I"),V("A")),Eqf(App("F",V("a")),Mul(V("c"),ProductMass("u",V("a")))))),Eqf(Call("comp",V("u"),V("Phi")),V("u")),FullDual("Phi","u","A"),Call("IsCompact",V("K")),Call("Nonempty",V("K")),Call("Convex",R,V("K")),Eqf(Span(V("K")),Top(V("A"))),Call("MapsTo",V("Phi"),V("K"),V("K")),All("x",V("A"),Imp(In(V("x"),V("K")),Eqf(App("u",V("x")),One))),WeightPos,WeightSum,Harmonic))))))));

}
