using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PBWeightedZeroBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive original pair tables and balancing constrain both directions of the same weighted response.",
        H("Zero product-square budgets for a total response"),
        Blocks(
            Paragraph(Text("Let E be any real vector space, including the zero space. No completeness, finite dimension or closure of response outputs in a smaller subspace is required. Let S:E x E -> E be real bilinear and symmetric, and let D:E x E -> E be a total map. Write x^2=S(x,x). An arbitrary indexed family e_i:E -> R of real linear evaluations separates E and determines exactly the cone C: x belongs to C if and only if e_i(x)>=0 for every i. A mathematical positive read is any real linear f with f(C)>=0. No normalization, mass restriction or additional actual preparation is introduced.")),
            Paragraph(Text("OriginalTables(S,D,C,e) consists exactly of this symmetry, exact-cone and separation data and the following original constraints. For all a,b and i the directed complex table [[e_i(a^2),e_i(S(a,b))-i e_i(D(a,b))],[e_i(S(b,a))-i e_i(D(b,a)),e_i(b^2)]] is positive semidefinite. For every a,b,c and i, set r_+=b+D(a,b)-S(a,c), r_-=b-D(a,b)+S(a,c), s_+=c+S(a,b)+D(a,c), and s_-=c-S(a,b)-D(a,c). The complete balancing constraint is e_i(r_+^2+s_+^2+2D(r_+,s_+))=e_i(r_-^2+s_-^2+2D(r_-,s_-)). These are the pair and balancing constraints on the inherited Jordan product; the statements below need no further Jordan identities or norm assumptions. In particular D is not assumed linear, homogeneous, continuous or covariant.")),
            Describe.Lean(
                DescribeId.Create("two-swapped-zero-budget-directions"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBWeightedZeroBudget.zero_budget_directions"),
                H("Both directions from the actual swapped balancing instances"),
                StatementSource.FromAuthor(F.Disp(ZeroStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Hermitian symmetry of the original pair tables and separation first imply D(b,a)=-D(a,b). For any complex column z, the real quadratic expression of that same table is the evaluation of one element of E. Its nonnegative readings under all original evaluations place that element in C. Hence every mathematical positive f reads the same pair table positively. This proves the positive-read extension from the exact cone, rather than adding it as another response law.")),
                    Paragraph(Text("If f(b^2)=0, the mature positive-semidefinite kernel theorem applied to the second coordinate column gives f(D(a,b))=0. In particular the original evaluations and separation give D(a,0)=0. Expanding only S in the complete balancing equality gives the element identity D(b+nu,c+omega)-D(b-nu,c-omega)=-2S(b,nu)-2S(c,omega), where nu=D(a,b)-S(a,c) and omega=S(a,b)+D(a,c). Unknown outer D values are never expanded.")),
                    Paragraph(Text("Put d=D(a,b) and g=S(a,b). The actual triple (a,b,0) gives D(b+d,g)-D(b-d,-g)=-2S(b,d). When f(g^2)=0, both outer response readings vanish by their original positive pair tables, forcing f(S(b,d))=0. Apply the actual swapped triple (b,a,0), symmetry of S and the proved skewness of D to obtain f(S(a,d))=0. The two statements concern one and the same original d."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("same-weighted-value-rotated-directions"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBWeightedZeroBudget.weighted_rotated_directions"),
                H("A conditional rotated consumer keeps the weighted old value"),
                StatementSource.FromAuthor(F.Disp(WeightedStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("RotationInvariant(D) is a separate hypothesis, quantified over every original a,b and every real theta: D(cos(theta)a-sin(theta)b,sin(theta)a+cos(theta)b)=D(a,b). It is not a field of OriginalTables, and these results do not derive it from the original constraints. With any original P,F, any real 0<alpha<=beta, and any real theta, define r=cos(theta)alpha P-sin(theta)beta F and s=sin(theta)alpha P+cos(theta)beta F. If a positive f has f(S(r,s)^2)=0, the preceding theorem and this independent rotation hypothesis constrain the literal T=D(alpha P,beta F). Inverting the known real rotation and cancelling the two positive weights gives f(S(P,T))=f(S(F,T))=0. No equality with alpha beta D(P,F) is used.")),
                    Paragraph(Text("For a projection-flip pair in an arbitrary complex C* background, this supplies the two null-read equations inside the weighted-shape argument, provided the chosen compressed positive reads have the displayed zero product-square budget. It does not construct the corner coordinates, prove that those compressed reads have zero budget, separate their operator blocks, bound a coefficient, or prove its square is the corner unit. Consequently it supplies neither the full weighted shape and upper bound nor saturation, an involutory seed, the two endogenous row values or their common-residual conclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-response-ambient-compression"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBWeightedZeroBudget.response_compression_of_annihilation"),
                H("A null input forces an actual zero compressed response"),
                StatementSource.FromAuthor(F.Disp(CompressionStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let A be an arbitrary unital complex C* algebra with its star order, including the zero algebra. Let iota:E -> A be real linear, with x in C if and only if 0<=iota(x), and iota(S(x,x))=iota(x)iota(x) for every original x. These are precisely the cone and square parts of an inherited Jordan inclusion; no completion of E, faithful state or predual is required. If iota(a)z=0 for any ambient multiplier z, the conclusion is z* iota(D(a,b))z=0. The multiplier is not passed to D.")),
                    Paragraph(Text("For every positive continuous real functional g on A, compose g with x maps to z*iota(x)z. Positivity of star conjugation makes this a mathematical positive read on the original E. Its reading of a^2 vanishes, so its reading of D(b,a) vanishes by the original pair table. Proved skewness gives the same conclusion for D(a,b). The norm-closed positive cone separates points by ProperCone.hyperplane_separation_point: a compression whose every positive continuous reading vanishes is both nonnegative and nonpositive, hence zero. The proof uses the ambient real normed space and does not require a Hilbert representation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-original-compression-and-directions"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBWeightedZeroBudget.weighted_compressed_directions"),
                H("Support and two compressed directions for the same weighted old value"),
                StatementSource.FromAuthor(F.Disp(AmbientWeightedStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Keep OriginalTables, the independent RotationInvariant hypothesis and the ambient inclusion conditions just stated. Take original P,F with iota(P) a selfadjoint projection, arbitrary 0<alpha<=beta, any real theta, and any ambient z satisfying iota(S(r,s))z=0 for the exact r,s above. Put T=D(alpha P,beta F) and Q=1-iota(P). Then Q iota(T)Q=0 and both z*iota(S(P,T))z and z*iota(S(F,T))z are zero. The support conclusion uses the preceding theorem at the actual inputs alpha P,beta F and multiplier Q. The two directional conclusions apply the weighted rotated theorem to every positive compressed read and separate the norm-positive cone.")),
                    Paragraph(Text("This statement applies to arbitrary projection-flip pairs in the original full C* carrier once the explicit rotated-product kernel is verified. It proves no existence or uniqueness of a corner coefficient W, no contraction or square upper bound, no same-W reverse budget and no involutory seed. The projection-flip theorem below supplies the kernel for the exact angle; full corner reconstruction, the saturation step and both endogenous rows remain additional mathematical obligations. No output-span premise, crossweight comparison or scaling of D occurs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-projection-flip-weighted-kernel"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBWeightedZeroBudget.projection_flip_weighted_compressions"),
                H("The projection-flip identities supply the kernel at all ordered positive weights"),
                StatementSource.FromAuthor(F.Disp(ProjectionFlipStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Keep OriginalTables, the independent RotationInvariant hypothesis, and a real linear iota into an arbitrary unital complex C* algebra with its star order. Now require the complete inherited product formula iota(S(x,y))=(iota(x)iota(y)+iota(y)iota(x))/2 and the exact inherited cone. For original P,F put p=iota(P), v=iota(F), and assume p is a selfadjoint projection, v^2=1 and pv+vp=v. For every 0<alpha<=beta define theta(alpha,beta)=arcsin(alpha/beta)/2, k=cos(theta)^2-sin(theta)^2 and z=p+k vp. The conclusion gives Q iota(T)Q=0 and both z*iota(S(P,T))z=z*iota(S(F,T))z=0 for the literal same T=D(alpha P,beta F). No compressed-kernel hypothesis is left in this theorem.")),
                    Paragraph(Text("The relation pv+vp=v and p^2=p give pvp=0. Set c=cos(theta), s=sin(theta). The exact angle gives alpha=2 beta s c, including alpha=beta. The inherited product computes the rotated product as beta^2 s c times ((4s^2 c^2)p+(c^2-s^2)v-1). Since 4s^2 c^2+(c^2-s^2)^2=1, this product annihilates z by pvp=0 and v^2=1. All of these multiplications are ambient calculations, and the rotated D labels remain real linear combinations in E. Applying the preceding compression theorem therefore pays the actual support and two directional compression equations for every original projection-flip pair and every allowed weight. Identifying the full corner coefficient, its contraction and its same-value saturation remain separate obligations; no involutory seed or endogenous row value follows from this partial result alone."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => Id(name);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula S(Formula a, Formula b) => Call("S", a, b);
    private static Formula D(Formula a, Formula b) => Call("D", a, b);
    private static Formula Read(Formula a) => Call("f", a);
    private static Formula Zero(Formula a) => Equal(a, Num(0));
    private static Formula Scope(Formula body) => All("E", V("RealVectorSpaces"),
        All("S", Call("RealBilinearMaps", V("E")), All("D", Call("TotalBinaryMaps", V("E")),
        All("C", Call("Subsets", V("E")), All("I", V("Types"),
        All("e", Call("IndexedRealLinearEvaluations", V("I"), V("E")),
        Imp(Call("OriginalTables", V("S"), V("D"), V("C"), V("e")), body)))))));
    private static Formula ZeroStatement()
    {
        var a = V("a"); var b = V("b"); var d = D(a,b); var g = S(a,b);
        return Scope(All("f", Call("PositiveRealLinearReads", V("E"), V("C")),
            All("a", V("E"), All("b", V("E"), Imp(Zero(Read(S(g,g))),
                And(Zero(Read(S(a,d))), Zero(Read(S(b,d)))))))));
    }
    private static Formula WeightedStatement()
    {
        var p = V("P"); var f = V("F"); var alpha = V("alpha"); var beta = V("beta");
        var theta = V("theta"); var a = Multiply(alpha,p); var b = Multiply(beta,f);
        var r = Subtract(Multiply(Call("cos",theta),a),Multiply(Call("sin",theta),b));
        var s = Add(Multiply(Call("sin",theta),a),Multiply(Call("cos",theta),b));
        var g = S(r,s); var t = D(a,b);
        return Scope(Imp(Call("RotationInvariant",V("D")), All("P",V("E"), All("F",V("E"),
            All("alpha",V("R"), All("beta",V("R"), All("theta",V("R"),
            Imp(Call("PositiveOrderedWeights",alpha,beta),
                All("f",Call("PositiveRealLinearReads",V("E"),V("C")),
                    Imp(Zero(Read(S(g,g))), And(Zero(Read(S(p,t))),Zero(Read(S(f,t))))))))))))));
    }
    private static Formula Compress(Formula z, Formula x) =>
        Multiply(Multiply(Call("star",z),Call("iota",x)),z);
    private static Formula AmbientScope(Formula body) =>
        All("A",V("UnitalComplexCStarAlgebrasWithStarOrder"),
            All("iota",Call("RealLinearMaps",V("E"),V("A")),
                Imp(Call("ExactConeAndSquares",V("iota"),V("S"),V("C")),body)));
    private static Formula CompressionStatement() => Scope(AmbientScope(
        All("a",V("E"),All("b",V("E"),All("z",V("A"),
            Imp(Zero(Multiply(Call("iota",V("a")),V("z"))),
                Zero(Compress(V("z"),D(V("a"),V("b"))))))))));
    private static Formula AmbientWeightedStatement()
    {
        var p=V("P"); var f=V("F"); var alpha=V("alpha"); var beta=V("beta");
        var theta=V("theta"); var z=V("z"); var a=Multiply(alpha,p); var b=Multiply(beta,f);
        var r=Subtract(Multiply(Call("cos",theta),a),Multiply(Call("sin",theta),b));
        var s=Add(Multiply(Call("sin",theta),a),Multiply(Call("cos",theta),b));
        var t=D(a,b); var q=Subtract(Num(1),Call("iota",p));
        var result=And(Zero(Multiply(Multiply(q,Call("iota",t)),q)),
            And(Zero(Compress(z,S(p,t))),Zero(Compress(z,S(f,t)))));
        return Scope(Imp(Call("RotationInvariant",V("D")),AmbientScope(
            All("P",V("E"),All("F",V("E"),Imp(Call("IsStarProjection",Call("iota",p)),
                All("alpha",V("R"),All("beta",V("R"),All("theta",V("R"),
                    Imp(Call("PositiveOrderedWeights",alpha,beta),All("z",V("A"),
                        Imp(Zero(Multiply(Call("iota",S(r,s)),z)),result))))))))))));
    }
    private static Formula ProjectionFlipStatement()
    {
        var p=V("P"); var f=V("F"); var alpha=V("alpha"); var beta=V("beta");
        var ip=Call("iota",p); var iff=Call("iota",f);
        var theta=Call("theta",alpha,beta); var c=Call("cos",theta); var ss=Call("sin",theta);
        var k=Subtract(Multiply(c,c),Multiply(ss,ss));
        var z=Add(ip,Multiply(k,Multiply(iff,ip))); var q=Subtract(Num(1),ip);
        var t=D(Multiply(alpha,p),Multiply(beta,f));
        Formula result=And(Zero(Multiply(Multiply(q,Call("iota",t)),q)),
            And(Zero(Compress(z,S(p,t))),Zero(Compress(z,S(f,t)))));
        result=Imp(Call("PositiveOrderedWeights",alpha,beta),result);
        result=All("beta",V("R"),result); result=All("alpha",V("R"),result);
        result=Imp(Equal(Add(Multiply(ip,iff),Multiply(iff,ip)),iff),result);
        result=Imp(Equal(Multiply(iff,iff),Num(1)),result);
        result=Imp(Call("IsStarProjection",ip),result);
        result=All("F",V("E"),result); result=All("P",V("E"),result);
        result=Imp(Call("ExactConeAndJordanProduct",V("iota"),V("S"),V("C")),result);
        result=All("iota",Call("RealLinearMaps",V("E"),V("A")),result);
        result=All("A",V("UnitalComplexCStarAlgebrasWithStarOrder"),result);
        return Scope(Imp(Call("RotationInvariant",V("D")),result));
    }

}
