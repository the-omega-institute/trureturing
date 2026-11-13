using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Fourier.PositiveDefinite;

internal sealed class UniformFourPointPrecisionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform four-point real precision criterion, with arbitrary positive consecutive gaps and both positive endpoint terms.",
        H("Uniform four-point precision on a logarithmic cusp window"), Blocks(
            Node("L", "Logarithmic envelope", Envelope(), DescribeRole.Definition,
                "L(t)=log(exp(1)/t). Every use of logarithm identities in the proofs has t>0. The scale t*L(t)^2 tends to zero at the right endpoint 0."),
            Node("psi", "Concavity deficit", Deficit(), DescribeRole.Definition,
                "psi(v,a,b)=v(a)+v(b)-v(a+b), for an arbitrary real function v and arbitrary real a,b. Positivity is proved later for positive arguments in the controlled window."),
            Node("interaction", "Mixed increment", Interaction(), DescribeRole.Definition,
                "interaction(v,p,q,r)=v(p+q)+v(q+r)-v(q)-v(p+q+r). Its lower bounds come from the actual differential inequality g(t)>=1/(4*t), rather than a desired cofactor premise."),
            Node("weight", "Both positive endpoint terms", Weight(), DescribeRole.Definition,
                "weight(v,p,q,r) is interaction(v,p,q,r)+psi(v,p,q)*psi(v,q,r)/v(q). Both summands remain in every endpoint estimate. Dropping the quotient loses control of extreme ratios."),
            Node("CuspControl", "Raw local analytic control", Control(), DescribeRole.Definition,
                "CuspControl(v,h,g,delta) requires 0<delta<=exp(-1), v(0)=0, global continuity of v, v'=h and h'=-g at every 0<t<=delta, continuity of g on this half-open window, h>0, h<=log(1/t), and 1/(4*t)<=g<=1/t. No inverse entry, Schur sign, or deficit-ratio monotonicity is assumed. Global continuity is stronger than needed away from this window but is paid by the actual K."),
            Node("uniform_outer_deficit_bound", "All three gap regimes", UniformBound(), DescribeRole.Theorem,
                "Under CuspControl and p,q,r>0 with s=p+q+r<=delta, v(p)*v(r)<=64*(1+log(3))^2*s*L(s)^2*weight(v,p,q,r). By reflection assume p<=r. The three exhaustive regimes are q>=r>=p, r>=p>=q, and r>=q>=p. The three regime estimates retain the logarithmic variables and positive-denominator cancellations in each regime. They prove log(1+z)>=(1+log(z))/2 for z>=1 and log(1+exp(y)/2)>=(1+y)/3 for y>=0. The largest gap m satisfies s/3<=m<=s, which gives the final factor (1+log(3))^2. There is no separation-ratio cutoff and no finite-sample argument."),
            Node("deficit_integrals", "Exact integrals at the singular corner", Integrals(), DescribeRole.Theorem,
                "Both outer integrands are interval integrable. The first iterated integral equals psi(v,p,q); the shifted one equals interaction(v,p,q,r). For u>0 the inner integral is h(u)-h(u+q), or h(q+u)-h(q+u+r), by the ordinary fundamental theorem. At u=0 the inner singular integral is irrelevant on a singleton of measure zero. The outer improper endpoint is justified by 0<h(u)<=log(1/u), integrability of the logarithm, and continuity of v at 0. No continuity of h at 0 is assumed. The quantitative lower estimates in uniform_outer_deficit_bound use the equivalent derivative-comparison argument, with the same primitive h+log(t)/4."),
            Node("real_posDef_of_complex", "Restrict complex coefficients to real ones", RealPosDef(), DescribeRole.Theorem,
                "For every natural n, positivity of the entrywise complex cast of a real Fin(n) matrix implies real Matrix.PosDef. Hermitian symmetry is read through Complex.re; the positive quadratic form is evaluated on the embedded real coefficient vector. This pays the actual supplier's complex-to-real boundary explicitly."),
            Node("schurCross", "Two-point conditioning", Cross(), DescribeRole.Definition,
                "schurCross(k,d,a,b,c,e,f)=f-[k*(a*c+b*e)-d*(a*e+b*c)]/(k^2-d^2). Division is the total real field division. Positive definiteness and the scalar window estimates provide nonzero positive denominators at every sign use."),
            Node("schurCross_eq_matrix", "Literal finite inverse formula", CrossMatrix(), DescribeRole.Theorem,
                "The scalar expression equals f minus the row [a,b], the real inverse of [[k,d],[d,k]], and the column [c,e]. This identity uses the actual pinned Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two, and Matrix.det_fin_two. It holds also for a singular conditioning matrix because both inverses use the same total definition."),
            Node("gapGram", "Ordered covariance matrix", GapMatrix(), DescribeRole.Definition,
                "gapGram(v,k,p,q,r) is the displayed symmetric real 4 by 4 matrix. Its diagonal is exactly k. For v(0)=0 it is the Gram matrix on 0,p,p+q,p+q+r of the even kernel t -> k-v(abs(t))."),
            Node("exists_uniform_endpoint_cross_pos", "One endpoint window for all ratios", Endpoint(), DescribeRole.Theorem,
                "CuspControl and k>0 produce one smaller delta>0 giving a strictly positive endpoint Schur cross for every positive p,q,r with total at most delta. Put P=v(p), Q=v(q), R=v(r), alpha=psi(v,p,q), beta=psi(v,q,r), D=P-alpha, E=R-beta and I=interaction(v,p,q,r). The exact private identity is (2*k-Q)*C=(2*k-Q)*I+k*alpha*beta/Q-(P*R+D*E). Since Q<k, I>0, and 0<D<P and 0<E<R, it bounds the cross below by k*weight-2*P*R. The uniform estimate and t*L(t)^2 -> 0 finish it. The choice uses an eventual bound on the entire interval, so the same delta covers all totals below it."),
            Node("strictAntiOn_deficit_ratio", "Weighted-ratio monotonicity", Ratio(), DescribeRole.Theorem,
                "Strict convexity of log(h) on (0,delta) makes h(p+u)/h(u) strictly increasing on 0<u<=delta-p. Integrating h(p+t)*h(u)-h(t)*h(p+u)>0 over 0<u<t proves the strict sign of the quotient derivative. Both integrals are proved integrable and v(t)>0 is proved. The theorem assumes no extra monotonicity premise for psi/v."),
            Node("exists_uniform_four_point_precision", "Six strict real inverse signs for all distinct nodes", Criterion(), DescribeRole.Theorem,
                "In addition to CuspControl, assume k>0, k-v(t)>0 on [0,delta0], strict convexity of log(k-v) on that closed interval, strict convexity of log(h) on its open interior, and real Matrix.PosDef for every injective four-node map of diameter at most delta0. Then one delta>0 works for every such four-node map: all off-diagonal real inverse entries are strictly negative. The window is chosen before the nodes, with no bound on gap ratios.",
                "The private adjacent-pair proofs use G(x,y)=k-v(y-x)-(k-v(x))*(k-v(y))/k. For 0<x<y, G increases strictly in x and decreases strictly in y; continuity extends the comparisons to the diagonal. For the distance-two pair the exact identity is C=alpha-(Q/V)*U+(k*U/V-P)*beta/(2*k-V), with V=v(q+r) and U=psi(v,p,q+r). The first summand is positive by strictAntiOn_deficit_ratio; the second is positive by the three-point strict log-convex inequality k*U>P*V.",
                "The endpoint theorem supplies the sixth sign. Six explicit real adjugate identities give adj(A)(i,j)=-(k^2-d^2)*C for the appropriate conditioning correlation d. Real positive definiteness supplies det(A)>0, and Matrix.inv_def turns these into strict inverse signs. Finset.orderIsoOfFin sorts any injective Fin 4 node map; Matrix.inv_submatrix_equiv transports the signs through the resulting permutation. Translation of the sorted nodes gives the three positive gaps.",
                "The arithmetic substitution is v(t)=K(0)-K(t), h(t)=-D1(t) and g(t)=D2(t). Intersecting the derivative-control window with the positive-definite window pays every scalar and matrix hypothesis. Restricting the complex positive quadratic form to real coefficients gives the real input. The resulting conclusion concerns all four distinct nodes in one common window. An arbitrary-dimensional precision theorem remains open."))));

    private static DocumentBlock Node(string name, string title, Formula statement,
        DescribeRole role, params string[] prose) =>
        Describe.Lean(DescribeId.Create("uniform-four-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(F.Disp(statement)),
            AssessedProvenance.FromRepo(), Blocks(prose.Select(p => Paragraph(Text(p))).ToArray()), role);

    private static Formula I(string x) => F.Id(x);
    private static Formula N(long n) => new Formula.Number(n);
    private static Formula R => F.Seq(F.Mathbb, F.Grp(I("R")));
    private static Formula Nat => F.Seq(F.Mathbb, F.Grp(I("N")));
    private static Formula Fun => new Formula.TypeArrow(R,R);
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula Exists(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), domain, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Op(name), [.. args]);
    private static Formula Op(string name) => F.Seq(F.Operatorname,
        F.Grp(name.Split('.').SelectMany((s,i) => i == 0 ? new[] { I(s) } : new[] { F.Dot,I(s) }).ToArray()));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a,b);
    private static Formula Neg(Formula a) => new Formula.Negate(a);
    private static Formula Abs(Formula a) => new Formula.Absolute(a);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a,op,b);
    private static Formula Eq(Formula a, Formula b) => Rel(a,FormulaRelationOperator.Equal,b);
    private static Formula Lt(Formula a, Formula b) => Rel(a,FormulaRelationOperator.LessThan,b);
    private static Formula Le(Formula a, Formula b) => Rel(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Ne(Formula a, Formula b) => Rel(a,FormulaRelationOperator.NotEqual,b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula And(params Formula[] xs) => xs.Aggregate((a,b) => new Formula.Logic(a,FormulaLogicOperator.And,b));
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f,[.. args]);
    private static Formula Interval(string kind, Formula d) => Call("Set."+kind,N(0),d);
    private static Formula On(string f, Formula d, Formula body) => All("t",Interval(f,d),body);
    private static Formula Fin(Formula n) => Call("Fin",n);
    private static Formula Nodes => new Formula.TypeArrow(Fin(N(4)),R);
    private static Formula MatrixType(Formula n, Formula field) => Call("Matrix",Fin(n),Fin(n),field);
    private static Formula Pos(Formula a) => Lt(N(0),a);
    private static Formula P => I("p"); private static Formula Q => I("q"); private static Formula T => I("t");
    private static Formula V => I("v"); private static Formula HH => I("h"); private static Formula GG => I("g");
    private static Formula D => I("delta"); private static Formula D0 => I("delta0"); private static Formula K => I("k");
    private static Formula RR => I("r"); private static Formula S => Add(Add(P,Q),RR);
    private static Formula Psi(Formula a, Formula b) => Call("psi",V,a,b);
    private static Formula Inter => Call("interaction",V,P,Q,RR);
    private static Formula W => Call("weight",V,P,Q,RR);
    private static Formula HypGaps(Formula d) => And(Pos(P),Pos(Q),Pos(RR),Le(S,d));
    private static Formula AllGaps(Formula body) => All("p",R,All("q",R,All("r",R,body)));
    private static Formula AllFunctions(Formula body) => All("v",Fun,All("h",Fun,All("g",Fun,body)));
    private static Formula Ctrl(Formula d) => Call("CuspControl",V,HH,GG,d);
    private static Formula Lambda(string name, Formula body) => F.Seq(F.Open,F.LambdaLower,F.Sp,I(name),F.Sp,
        F.Mapsto,F.Sp,body,F.Close);
    private static Formula Mat(params Formula[][] rows)
    {
        var result = new List<Formula> { F.Bang,F.Bang,F.OpenBracket };
        for (var i=0; i<rows.Length; i++)
        {
            if (i>0) result.Add(F.Semi);
            for (var j=0; j<rows[i].Length; j++)
            {
                if (j>0) result.Add(F.Comma);
                result.Add(rows[i][j]);
            }
        }
        result.Add(F.CloseBracket);
        return F.Seq(result.ToArray());
    }
    private static Formula Gram(Formula x) => Lambda("i",Lambda("j",
        Sub(K,At(V,Abs(Sub(At(x,I("i")),At(x,I("j"))))))));
    private static Formula Diameter(Formula x, Formula d) => All("i",Fin(N(4)),All("j",Fin(N(4)),
        Le(Abs(Sub(At(x,I("i")),At(x,I("j")))),d)));
    private static Formula SixSigns(Formula a) => All("i",Fin(N(4)),All("j",Fin(N(4)),
        Imp(Ne(I("i"),I("j")),Lt(At(Pow(a,Neg(N(1))),I("i"),I("j")),N(0)))));
    private static Formula Integral(Formula u, Formula bound, Formula body) => F.Seq(
        F.Int,F.Underscore,F.Grp(N(0)),F.Caret,F.Grp(bound),
        body,F.Sp,I("d"),u);
    private static Formula LogFun(Formula f) => Call("Function.comp",Op("Real.log"),f);

    private static Formula Envelope() => All("t",R,Eq(Call("L",T),Call("Real.log",Div(Call("Real.exp",N(1)),T))));
    private static Formula Deficit() => All("v",Fun,All("a",R,All("b",R,Eq(Call("psi",V,I("a"),I("b")),
        Sub(Add(At(V,I("a")),At(V,I("b"))),At(V,Add(I("a"),I("b"))))))));
    private static Formula Interaction() => All("v",Fun,AllGaps(Eq(Inter,
        Sub(Sub(Add(At(V,Add(P,Q)),At(V,Add(Q,RR))),At(V,Q)),At(V,S)))));
    private static Formula Weight() => All("v",Fun,AllGaps(Eq(W,Add(Inter,Div(Mul(Psi(P,Q),Psi(Q,RR)),At(V,Q))))));
    private static Formula Control()
    {
        var fields = And(Pos(D),Le(D,Call("Real.exp",Neg(N(1)))),Eq(At(V,N(0)),N(0)),Call("Continuous",V),
            On("Ioc",D,Call("HasDerivAt",V,At(HH,T),T)),
            On("Ioc",D,Call("HasDerivAt",HH,Neg(At(GG,T)),T)),Call("ContinuousOn",GG,Interval("Ioc",D)),
            On("Ioc",D,And(Pos(At(HH,T)),Le(At(HH,T),Call("Real.log",Div(N(1),T))),
                Le(Div(N(1),Mul(N(4),T)),At(GG,T)),Le(At(GG,T),Div(N(1),T)))));
        return AllFunctions(All("delta",R,new Formula.Logic(Ctrl(D),FormulaLogicOperator.Iff,fields)));
    }
    private static Formula UniformBound() => AllFunctions(All("delta",R,Imp(Ctrl(D),AllGaps(Imp(HypGaps(D),
        Le(Mul(At(V,P),At(V,RR)),Mul(Mul(Mul(Mul(N(64),Pow(Add(N(1),Call("Real.log",N(3))),N(2))),S),Pow(Call("L",S),N(2))),W)))))));
    private static Formula Integrals()
    {
        var u=I("u"); var w=I("w");
        var f=Lambda("u",Integral(w,Q,At(GG,Add(u,w))));
        var f2=Lambda("u",Integral(w,RR,At(GG,Add(Add(Q,u),w))));
        return AllFunctions(All("delta",R,Imp(Ctrl(D),AllGaps(Imp(HypGaps(D),And(
            Call("IntervalIntegrable",f,Op("volume"),N(0),P),
            Eq(Psi(P,Q),Integral(u,P,Integral(w,Q,At(GG,Add(u,w))))),
            Call("IntervalIntegrable",f2,Op("volume"),N(0),P),
            Eq(Inter,Integral(u,P,Integral(w,RR,At(GG,Add(Add(Q,u),w)))))))))));
    }
    private static Formula RealPosDef() => All("n",Nat,All("A",MatrixType(I("n"),R),Imp(
        Call("Matrix.PosDef",Call("Matrix.map",I("A"),Op("Complex.ofReal"))),Call("Matrix.PosDef",I("A")))));
    private static Formula AllSeven(Formula body) => All("k",R,All("d",R,All("a",R,All("b",R,All("c",R,All("e",R,All("f",R,body)))))));
    private static Formula CrossCall => Call("schurCross",K,I("d"),I("a"),I("b"),I("c"),I("e"),I("f"));
    private static Formula Cross() => AllSeven(Eq(CrossCall,Sub(I("f"),Div(
        Sub(Mul(K,Add(Mul(I("a"),I("c")),Mul(I("b"),I("e")))),Mul(I("d"),Add(Mul(I("a"),I("e")),Mul(I("b"),I("c"))))),
        Sub(Pow(K,N(2)),Pow(I("d"),N(2)))))));
    private static Formula CrossMatrix() => AllSeven(Eq(CrossCall,Sub(I("f"),
        At(Mul(Mul(Mat(new[] { I("a"),I("b") }),Pow(Mat(new[] { K,I("d") },new[] { I("d"),K }),Neg(N(1)))),
            Mat(new[] { I("c") },new[] { I("e") })),N(0),N(0)))));
    private static Formula GapMatrix()
    {
        var a=Sub(K,At(V,P)); var b=Sub(K,At(V,Add(P,Q))); var c=Sub(K,At(V,Q));
        var d=Sub(K,At(V,Add(Q,RR))); var e=Sub(K,At(V,RR)); var f=Sub(K,At(V,S));
        return All("v",Fun,All("k",R,AllGaps(Eq(Call("gapGram",V,K,P,Q,RR),
            Mat(new[] { K,a,b,f },new[] { a,K,c,d },new[] { b,c,K,e },new[] { f,d,e,K })))));
    }
    private static Formula Endpoint() => AllFunctions(All("delta0",R,All("k",R,Imp(And(Ctrl(D0),Pos(K)),
        Exists("delta",R,And(Pos(D),Le(D,D0),AllGaps(Imp(HypGaps(D),Pos(Call("schurCross",K,
            Sub(K,At(V,Q)),Sub(K,At(V,P)),Sub(K,At(V,Add(P,Q))),Sub(K,At(V,Add(Q,RR))),Sub(K,At(V,RR)),Sub(K,At(V,S))))))))))));
    private static Formula Ratio() => AllFunctions(All("delta",R,All("p",R,Imp(And(Ctrl(D),Pos(P),
        Call("StrictConvexOn",R,Interval("Ioo",D),LogFun(HH))),
        Call("StrictAntiOn",Lambda("t",Div(Psi(P,T),At(V,T))),Interval("Ioc",Sub(D,P)))))));
    private static Formula Criterion()
    {
        var x=I("x");
        var pos=On("Icc",D0,Pos(Sub(K,At(V,T))));
        var logK=Call("StrictConvexOn",R,Interval("Icc",D0),Lambda("t",Call("Real.log",Sub(K,At(V,T)))));
        var logh=Call("StrictConvexOn",R,Interval("Ioo",D0),LogFun(HH));
        var spd=All("x",Nodes,Imp(And(Call("Function.Injective",x),Diameter(x,D0)),Call("Matrix.PosDef",Gram(x))));
        var conclusion=Exists("delta",R,And(Pos(D),Le(D,D0),All("x",Nodes,
            Imp(And(Call("Function.Injective",x),Diameter(x,D)),SixSigns(Gram(x))))));
        return AllFunctions(All("delta0",R,All("k",R,Imp(And(Ctrl(D0),Pos(K),pos,logK,logh,spd),conclusion))));
    }
}
