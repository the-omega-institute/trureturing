using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;

internal sealed class SpectralNonconcavityScalarsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Hiai/SpectralNonconcavityScalars.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pure real root and scale estimates supply the full UNTILDE matrix obstruction.",
        H("Scalar dependencies of the UNTILDE proof"), Blocks(
            Paragraph(Text("These are consumed helpers of SpectralNonconcavity, with their original namespace and parameters. They organize the existing proof and do not assert a separate resolution of Hiai's problem. The matrix owner retains the native geometric mean, spectral CFC powers, density paths, noncommutativity and all endpoint theorems.")),
            Paragraph(Text("For real u,v,w, radius is sqrt(((u-w)/2)^2+v^2), and lowerRoot and upperRoot are (u+w)/2 minus and plus radius. For real alpha,p, interior is min(1/4,(2^(-alpha/(1-alpha))-1/2)^(1/p)). These definitions are total; the theorems state every positivity and interval condition they use.")),
            Paragraph(Text("For real p,s, put z=scale(p,s)=s^(p/2), x=entryX(p,s)=(1-s^2)^p, a=entryA(p,s)=((1-s)^p+z^2)/2, b=entryB(p,s)=((1-s)^p-z^2)/2, e=entryE(p,s)=((1-s^2)(1-s))^(p/2), and c=entryC(p,s)=sqrt(a(x+z^4)+2z^3 e). The entry functions are u=entryU(p,s)=(a+z^3 e/x)/c, v=entryV(p,s)=b/c, w=entryW(p,s)=(a+e/z)/c, and scaledW(p,s)=(za+e)/c. The finite factors are largeScale(p,s)=upperRoot(zu,zv,scaledW), small(p,s)=e/(x largeScale), ratio(p,s)=z small/largeScale, and slope(alpha,p,s)=largeScale^(alpha-1) z^(1-alpha)(1-ratio^alpha)/(1-ratio). Finally k=sqrt(1/2). Every power in this owner is a real scalar power.")),
            Node("root_algebra", "Ordered roots and determinant", RootAlgebra(),
                "Positivity of the radius orders the roots; their product is uw-v squared. The matrix root_power, actual_roots and actual_power proofs consume this algebra."),
            Node("scaled_upperRoot", "Positive root scaling", ScaledRoot(),
                "Nonnegative scaling commutes with the upper root. actual_roots uses this identity to identify the scaled eigenvalue of the actual native mean."),
            Node("slope_factor", "Finite-factor spectral slope", SlopeFactor(),
                "The exact divided difference is written using finite c=zM and the ratio m/M. actual_power uses it in the true matrix spectral power."),
            Node("interior_gap", "Strict scalar gap", InteriorGap(),
                "For every positive p and 0<alpha<1/2, the explicit interior coordinate is positive, at most one quarter, and has the strict gap displayed here. lower_half_witness and both branches of off_midpoint_violation consume it."),
            Node("scale_square", "Square of the scale", ScalePower(2),
                "native_two_scale uses this equality to recover the balanced matrix eigenvalues. entry_facts also consumes it."),
            Node("scale_fourth", "Fourth power of the scale", ScalePower(4),
                "native_two_scale uses this equality to recover the diagonal matrix eigenvalues."),
            Node("entry_facts", "Positive entries and exact identities", EntryFacts(),
                "For every positive p and 0<s<1/2, the six scalar factors are positive, e squared equals x(1-s)^p, a squared minus b squared equals (1-s)^p z squared, and c squared has its defining radicand. native_two_scale, scaled_entries, actual_roots and actual_power consume these facts."),
            Node("small_interval", "The right-hand neighborhood", SmallInterval(),
                "The right-hand neighborhood of zero eventually lies in (0,1/2). fixed_diagonal_limit, two_scale_matrix_limit, two_scale_trace_limit and lower_half_witness consume the same event."),
            Node("entry_limits", "Limits of finite scalar entries", EntryLimits(),
                "For every p>0 as s approaches zero from the right, z tends to zero, x and e to one, c,u,v to k, and scaledW to 1/k. weightedColumns_limit consumes the result; finite_factor_limits also uses it."),
            Node("finite_factor_limits", "Limits of the scaled root and slope", FactorLimits(),
                "For every 0<alpha<1 and p>0, largeScale tends to 1/k, small to k, ratio and slope to zero. weightedColumns_limit uses these finite factors; the divergent native mean is not asserted continuous."),
            Node("k_square_power", "Normalization of the matrix limit", KPower(),
                "For every real alpha, k^alpha k^alpha=2^(-alpha). two_scale_matrix_limit consumes this exact normalization."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("untilde-scalar-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula V(string n) => F.Id(n);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Call(string n, params Formula[] a) => new Formula.FunctionCall(
        FormulaIdentifier.Create(n), [.. a]);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula Pow(Formula a, Formula b) => Call("rpow",a,b);
    private static Formula Neg(Formula a) => Sub(D(0),a);
    private static Formula Group(Formula a) => Seq(Open,a,Close);
    private static Formula And(params Formula[] a) => a.Aggregate((x,y) =>
        new Formula.Logic(Group(x),FormulaLogicOperator.And,Group(y)));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Group(a),FormulaLogicOperator.Implies,Group(b));
    private static Formula All(string n, Formula b) => Seq(Forall,Sp,V(n),Colon,Sp,Real,Comma,Sp,b);
    private static Formula For(string[] ns, Formula b) => ns.Reverse().Aggregate(b,(x,n)=>All(n,x));
    private static Formula Half => Div(D(1),D(2));
    private static Formula R(string n) => Call(n,V("u"),V("v"),V("w"));
    private static Formula E(string n) => Call(n,V("p"),V("s"));
    private static Formula Limit(string n, Formula target, bool alpha = false) =>
        Call("Tendsto", alpha ? Call(n,V("alpha"),V("p")) : Call(n,V("p")),
            Call("nhdsWithin",D(0),Call("Ioi",D(0))), Call("nhds",target));

    private static Formula RootAlgebra() => For(["u","v","w"],Imp(Lt(D(0),V("v")),And(
        Lt(D(0),R("radius")),Lt(R("lowerRoot"),R("upperRoot")),
        Eq(Mul(R("upperRoot"),R("lowerRoot")),Sub(Mul(V("u"),V("w")),Pow(V("v"),D(2)))))));
    private static Formula ScaledRoot() => For(["z","u","v","w"],Imp(Le(D(0),V("z")),
        Eq(Mul(V("z"),R("upperRoot")),Call("upperRoot",Mul(V("z"),V("u")),Mul(V("z"),V("v")),Mul(V("z"),V("w"))))));
    private static Formula SlopeFactor()
    {
        var m=V("m");var M=V("M");var z=V("z");var c=V("c");var a=V("alpha");
        return For(["M","m","z","c","alpha"],Imp(And(Lt(D(0),M),Lt(D(0),m),Lt(D(0),z),
            Eq(c,Mul(z,M)),Seq(m,Sp,Neq,Sp,M)),Eq(Div(Sub(Pow(M,a),Pow(m,a)),Sub(M,m)),
            Div(Mul(Mul(Pow(c,Sub(a,D(1))),Pow(z,Sub(D(1),a))),Sub(D(1),Pow(Div(m,M),a))),Sub(D(1),Div(m,M))))));
    }
    private static Formula InteriorGap()
    {
        var a=V("alpha");var p=V("p");var t=Call("interior",a,p);
        return For(["alpha","p"],Imp(And(Lt(D(0),a),Lt(a,Half),Lt(D(0),p)),And(
            Lt(D(0),t),Le(t,Div(D(1),D(4))),Lt(Pow(Div(Add(Pow(Sub(D(1),t),p),Pow(t,p)),D(2)),
                Div(Sub(D(1),a),p)),Pow(D(2),Div(Neg(a),p))))));
    }
    private static Formula ScalePower(byte n) => For(["p","s"],Imp(Le(D(0),V("s")),
        Eq(Pow(E("scale"),D(n)),Pow(n==2 ? V("s") : Pow(V("s"),D(2)),V("p")))));
    private static Formula EntryFacts()
    {
        var z=E("scale");var x=E("entryX");var a=E("entryA");var b=E("entryB");
        var e=E("entryE");var c=E("entryC");var h=Pow(Sub(D(1),V("s")),V("p"));
        return For(["p","s"],Imp(And(Lt(D(0),V("p")),Lt(D(0),V("s")),Lt(V("s"),Half)),And(
            Lt(D(0),z),Lt(D(0),x),Lt(D(0),a),Lt(D(0),b),Lt(D(0),e),Lt(D(0),c),
            Eq(Pow(e,D(2)),Mul(x,h)),Eq(Sub(Pow(a,D(2)),Pow(b,D(2))),Mul(h,Pow(z,D(2)))),
            Eq(Pow(c,D(2)),Add(Mul(a,Add(x,Pow(z,D(4)))),Mul(Mul(D(2),Pow(z,D(3))),e))))));
    }
    private static Formula SmallInterval() => Call("Eventually",Call("nhdsWithin",D(0),Call("Ioi",D(0))),
        Seq(V("s"),Sp,Mapsto,Sp,And(Lt(D(0),V("s")),Lt(V("s"),Half))));
    private static Formula EntryLimits() => All("p",Imp(Lt(D(0),V("p")),And(
        Limit("scale",D(0)),Limit("entryX",D(1)),Limit("entryE",D(1)),Limit("entryC",V("k")),
        Limit("entryU",V("k")),Limit("entryV",V("k")),Limit("scaledW",Div(D(1),V("k"))))));
    private static Formula FactorLimits() => For(["alpha","p"],Imp(And(Lt(D(0),V("alpha")),
        Lt(V("alpha"),D(1)),Lt(D(0),V("p"))),And(Limit("largeScale",Div(D(1),V("k"))),
        Limit("small",V("k")),Limit("ratio",D(0)),Limit("slope",D(0),true))));
    private static Formula KPower() => All("alpha",Eq(Mul(Pow(V("k"),V("alpha")),Pow(V("k"),V("alpha"))),
        Pow(D(2),Neg(V("alpha")))));
}
