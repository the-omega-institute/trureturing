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
                    Imp(Zero(Read(S(g,g))), And(Zero(Read(S(p,t))),Zero(Read(S(f,t)))))))))))));
    }
}
