using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class OrderUnitNormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A closed salient cone and its specified interior unit determine the original order norm, positive-functional mass bounds, and exact bounds for the original linear operator.",
        H("The original order-unit norm"),
        Blocks(
            Paragraph(Text("Let E be any finite-dimensional real normed vector space. Its auxiliary norm supplies the usual topology only. The data A consist of a convex cone C containing zero, a closedness proof, salience, and a specified vector u in its interior. Salience means that a vector and its negative can both belong to C only when the vector vanishes. No inner product, lattice, Jordan product, self-duality or nonzero-dimension assumption is used.")),
            Paragraph(Text("Put B equal to the vectors v for which u-v and u+v belong to C. For each v, let S(v) be the nonnegative real radii r for which r u-v and r u+v belong to C, and let n(v) be inf S(v). In particular, zero is retained among the radii. The order relation is exactly w-v in C.")),
            Describe.Lean(
                DescribeId.Create("constructed-order-norm-core"),
                DeclarationHandle.Create("D5/S3/Topology/OrderUnitNorm.norm_core"),
                H("The norm axioms follow from the original cone"),
                StatementSource.FromAuthor(F.Disp(CoreStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The symbols R and Types denote the real scalars and the type universe. ConeUnitData denotes precisely the original cone and unit data stated above. The displayed norm laws apply to the copy of E with norm n; this first assertion does not require finite dimension. They are proved rather than supplied as an extra hypothesis. The interior-unit assumption makes B a neighborhood of zero and hence absorbent. Each S(v) is nonempty, closed and bounded below by zero, so its infimum is attained.")),
                    Paragraph(Text("The symmetric interval is convex and balanced. Its gauge equals n exactly: every positive gauge radius is an order radius, and every radius just above the attained order radius is a positive gauge radius. This includes v=0, where S(0) contains its infimum zero although the gauge uses strictly positive radii. Mathlib's gaugeSeminorm supplies the seminorm laws. At n(v)=0 the attained inequalities put v and -v in C, so salience supplies definiteness.")))),
            Describe.Lean(
                DescribeId.Create("original-order-unit-norm-interface"),
                DeclarationHandle.Create("D5/S3/Topology/OrderUnitNorm.original_order_unit_norm_interface"),
                H("Positive functionals and the same original operator"),
                StatementSource.FromAuthor(F.Disp(InterfaceStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("PositiveDual denotes all original real-linear functionals nonnegative on C, and Effects denotes all x with x and u-x in C. RealEndomorphisms denotes all original real-linear maps E to E. The notation K abbreviates the norm of the square of the transported operator, and IsLeast includes membership in the displayed bound set as well as its minimality. Here j is the canonical linear wrapping map to the copy E_u, and H_u is defined solely by H_u(j(v))=j(H(v)). The constructed copy is complete. The wrapping map and its inverse are continuous in the original finite-dimensional topology; no equality with the auxiliary ambient norm is asserted.")),
                    Paragraph(Text("For every positive original real-linear functional beta, its evaluation is bounded by its mass beta(u) times n(v). Applying beta to the attained endpoint inequalities proves this without dividing by its mass. Thus mass zero forces the original functional to vanish. The operator norm of beta transported to E_u is exactly beta(u), including in dimension zero.")),
                    Paragraph(Text("The square H_u squared acts on j(v) as j(H(H(v))). Its operator norm is exactly the infimum of all nonnegative c satisfying n(H(H(v))) at most c n(v) for every original v. This infimum is attained. Neither an ambient operator bound nor the square of the norm of H is substituted for this number.")),
                    Paragraph(Text("A positive unital linear map contracts n. A linear equivalence whose inverse is also positive is an isometry; positivity and unitality alone do not imply isometry. Applying this conclusion to exp(tH) uses both the assumed positivity at t and at -t. Conjugation by j carries the actual exponential to exp(tH_u).")),
                    Paragraph(Text("Assume that every original exp(tH) is positive and fixes u. Its order norm is then preserved for every real t. If the separately supplied condition H(u)=0 also holds, an effect x in C with u-x in C has centered vector z=x-u/2 of order norm at most one half, and H(H(x))=H(H(z)). Positive-functional domination and the exact square-operator bound give the displayed all-time centered-orbit estimate.")),
                    Paragraph(Text("The actual scalar orbit f(t)=beta(exp(tH)x) is twice continuously differentiable, with first derivative beta(exp(tH)Hx) and second derivative beta(exp(tH)H(Hx)). Taylor's theorem on the unoriented interval from 0 to any real s gives f(s) at most f(0)+s f'(0)+M s squared divided by two, where M=beta(u)K/2. Positivity makes this quadratic nonnegative on the entire real line. The existing quadratic discriminant theorem then gives f'(0) squared at most 2M f(0), including M=0. This proves the reverse certificate with exactly K=the operator norm of H_u squared, without division by mass or curvature. The positive-generator criterion and the same-constant closure argument remain separate; no full quantitative generator equivalence or optimality of K is asserted here.")),
                    Paragraph(Text("Order-unit norm and positive-functional mass facts are classical; the present concrete interface retains the original cone, unit, functional and linear action in one construction. It asserts no literature priority or physical realization of the mathematical exponential.")))))));

    private static Formula CoreStatement()
    {
        var n = Id("n"); var v = Id("v"); var w = Id("w"); var a = Id("a");
        var laws = All("v", Id("E"), And(
            Le(F.D(0), Apply(n, v)),
            Iff(Eq(Apply(n, v), F.D(0)), Eq(v, F.D(0))),
            All("a", Id("R"), Eq(Apply(n, Scale(a, v)),
                Mul(Call("abs", a), Apply(n, v)))),
            All("w", Id("E"), Le(Apply(n, Add(v, w)),
                Add(Apply(n, v), Apply(n, w))))));
        return All("E", Id("Types"), Implies(Call("RealNormedVectorSpace", Id("E")),
            All("A", Call("ConeUnitData", Id("E")), laws)));
    }

    private static Formula InterfaceStatement()
    {
        var v=Id("v"); var x=Id("x"); var t=Id("t"); var beta=Id("beta");
        var u=Id("u"); var j=Id("j"); var H=Id("H"); var Hu=Id("Hu");
        var B=Id("B"); var C=Id("C"); var Eu=Id("Eu"); var K=Id("K");
        Formula N(Formula y) => Call("n", y);
        Formula Orbit(Formula y) => Apply(Call("exp", Scale(t, H)), y);
        var first=All("v", Id("E"), And(
            Eq(N(v), Call("gauge", B, v)),
            Call("mem", N(v), Call("S", v)),
            Eq(Call("norm", Apply(j,v)), N(v)),
            Iff(Le(Call("norm",Apply(j,v)),F.D(1)),Call("mem",v,B))));
        var dual=All("beta",Id("PositiveDual"),And(
            All("v",Id("E"),Le(Call("abs",Apply(beta,v)),Mul(Apply(beta,u),N(v)))),
            Implies(Eq(Apply(beta,u),F.D(0)),Eq(beta,F.D(0))),
            Eq(Call("norm",Call("transport",beta)),Apply(beta,u))));
        var bounds=Call("Set", Id("c"), And(Le(F.D(0),Id("c")),
            All("v",Id("E"),Le(N(Apply(H,Apply(H,v))),Mul(Id("c"),N(v))))));
        var action=All("v",Id("E"),And(
            Eq(Apply(Hu,Apply(j,v)),Apply(j,Apply(H,v))),
            Eq(Apply(Hu,Apply(Hu,Apply(j,v))),Apply(j,Apply(H,Apply(H,v))))));
        var coefficient=And(Eq(K,Call("norm",Call("square",Hu))),
            Eq(K,Call("inf",bounds)),Call("IsLeast",bounds,K));
        var transport=All("t",Id("R"),All("v",Id("E"),
            Eq(Apply(Call("exp",Scale(t,Hu)),Apply(j,v)),Apply(j,Orbit(v)))));
        var centered = All("beta",Id("PositiveDual"),All("x",Id("Effects"),
            All("t",Id("R"),Le(Call("abs",Apply(beta,Orbit(Apply(H,Apply(H,x))))),
                new Formula.Fraction(Mul(Apply(beta,u),K),F.D(2))))));
        var reverse = All("beta",Id("PositiveDual"),All("x",Id("Effects"),
            Le(Call("square",Call("abs",Apply(beta,Apply(H,x)))),
                Mul(Mul(K,Apply(beta,x)),Apply(beta,u)))));
        var group=Implies(Call("PositiveUnitalAtEveryRealTime",H,C,u),And(
            All("t",Id("R"),All("v",Id("E"),Eq(N(Orbit(v)),N(v)))),
            Implies(Eq(Apply(H,u),F.D(0)),And(centered,reverse))));
        return All("E", Id("Types"),
            Implies(Call("FiniteDimensionalRealNormedSpace", Id("E")),
                All("A", Call("ConeUnitData", Id("E")), And(
                    first, Call("Complete",Eu), Call("Continuous",j),
                    Call("Continuous",Call("inverse",j)), dual,
                    All("H", Call("RealEndomorphisms", Id("E")),
                        And(action, coefficient, transport, group)),
                    Call("PositiveUnitalInverseIsometry",C,u,Id("n"))))));
    }

    private static Formula Id(string s)=>F.Id(s);
    private static Formula Call(string s,params Formula[] a)=>new Formula.Apply(Id(s),[..a]);
    private static Formula Apply(Formula f,params Formula[] a)=>new Formula.Apply(f,[..a]);
    private static Formula All(string s,Formula type,Formula body)=>new Formula.Bind(
        FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),type,body);
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Le(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Add(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Mul(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Scale(Formula a,Formula b)=>Call("smul",a,b);
    private static Formula Implies(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula And(params Formula[] a)
    {
        var r=a[^1];
        for(var i=a.Length-2;i>=0;i--) r=new Formula.Logic(a[i],FormulaLogicOperator.And,r);
        return r;
    }
}
