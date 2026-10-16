using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.WhiteBoxLossFiberLaw;

internal sealed class PartialAbsorptionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Estimation/WhiteBoxLossFiberLaw/PartialAbsorption.";
    private static Formula Flow(params Formula[] xs) => Seq(xs.SelectMany((x,i) => i == 0 ? new[]{x} : new[]{Sp,x}).ToArray());
    private static Formula Call(string name, params Formula[] xs) => xs.Length == 0
        ? Flow(Operatorname,Grp(F.Id(name)))
        : new Formula.Apply(Flow(Operatorname,Grp(F.Id(name))), [.. xs]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),t,b);
    private static Formula Ex(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(n),t,b);
    private static Formula And(params Formula[] xs) => Flow(xs.SelectMany((x,i) =>
        i == 0 ? new[]{Open,x,Close} : new[]{Land,Open,x,Close}).ToArray());
    private static Formula Eqn(Formula a, Formula b) => Flow(a,Eq,b);
    private static Formula LtN(Formula a, Formula b) => Flow(a,Lt,b);
    private static Formula LeN(Formula a, Formula b) => Flow(a,Le,b);
    private static Formula Implies(Formula a, Formula b) => Flow(Open,a,Close,Rightarrow,Open,b,Close);
    private static Formula In(Formula a, Formula s) => Flow(a,InMacro,s);
    private static Formula R => Flow(Mathbb,Grp(F.Id("R")));
    private static Formula E => F.Id("E");
    private static Formula u => F.Id("u");
    private static Formula v => F.Id("v");
    private static Formula l => F.Id("lambda");
    private static Formula alpha => F.Id("alpha");
    private static Formula pzero => F.Id("pzero");
    private static Formula pa => F.Id("pA");
    private static Formula pab => F.Id("pAB");
    private static Formula pb => F.Id("pB");
    private static Formula q => Flow(Frac,Grp(Pi),Grp(D(4)));
    private static Formula r => Flow(Frac,Grp(Pi),Grp(D(2)));
    private static Formula k => Flow(Frac,Grp(D(1)),Grp(Flow(Sqrt,Grp(D(2)))));
    private static Formula Norm(Formula x) => Flow(Vert,x,Vert);
    private static Formula Dict(Formula a) => Call("rotatingDictionary",u,v,a);
    private static Formula J => Call("objective",l,pzero,pa,pab,pb,u,v);
    private static Formula At(Formula a) => new Formula.Apply(J,[a]);
    private static Formula dl => Flow(Minus,pb,Open,k,Minus,l,Close,k);
    private static Formula dr => Flow(pab,l,Open,D(1),Minus,l,Close);
    private static Formula interval => Call("Icc",q,r);
    private static Formula interior => Call("Ioo",q,r);
    private static Formula Geometry => And(Eqn(Norm(u),D(1)),Eqn(Norm(v),D(1)),Eqn(Call("inner",u,v),D(0)));
    private static Formula BindGeometry(Formula b) => All("E",Call("RealInnerProductSpace"),All("u",E,All("v",E,b)));
    private static Formula BindParameters(Formula b)
    {
        foreach (var n in new[]{"pB","pAB","pA","pzero","lambda"}) b = All(n,R,b);
        return BindGeometry(b);
    }
    private static Formula Neighborhood(string name, Formula endpoint)
    {
        var s = F.Id(name);
        return Ex(name,Call("Set",R),And(Call("IsOpen",s),In(endpoint,s),
            All("alpha",R,Implies(In(alpha,s),Call("DifferentiableAt",R,J,alpha)))));
    }
    private static Formula TheoremFormula()
    {
        var c = F.Id("c"); var x = F.Id("x");
        var assumptions = And(Geometry,LeN(D(0),pzero),LeN(D(0),pa),LeN(D(0),pab),LeN(D(0),pb),
            Eqn(Flow(pzero,Plus,pa,Plus,pab,Plus,pb),D(1)),LtN(D(0),l),LtN(l,k),LtN(D(0),pab),LtN(D(0),pb));
        var attainment = All("alpha",R,All("x",E,Ex("c",new Formula.TypeArrow(Call("Fin",D(2)),R),
            And(Call("FeasibleCode",c),Eqn(Call("codeCost",l,x,Dict(alpha)),Call("codeEnergy",l,x,Dict(alpha),c))))));
        var conclusion = And(Eqn(Call("atom",Dict(q),D(1)),Call("bisector",u,v)),Eqn(Call("atom",Dict(r),D(1)),v),
            attainment,Neighborhood("U",q),Neighborhood("V",r),
            Call("HasDerivAt",J,dl,q),Call("HasDerivAt",J,dr,r),
            Call("HasDerivWithinAt",J,dl,interval,q),Call("HasDerivWithinAt",J,dr,interval,r),LtN(dl,D(0)),LtN(D(0),dr),
            All("alpha",R,Implies(And(In(alpha,interval),Call("IsMinOn",J,interval,alpha)),In(alpha,interior))),
            Ex("alpha",R,And(In(alpha,interior),LtN(At(alpha),At(q)),LtN(At(alpha),At(r)))));
        return Disp(BindParameters(Implies(assumptions,conclusion)));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact nonnegative-code objective decreases inward at both canonical dictionaries.",
        H("Partial Absorption for the Actual Optimized Cost"),
        Blocks(
            Paragraph(Text("Let E be any real inner-product space, and let u and v be orthogonal unit vectors. The dictionary D(alpha) has first atom u and second atom cos(alpha)u+sin(alpha)v, for every real alpha. Its entries have unit norm on the entire real line. At pi/4 the second atom is (u+v)/sqrt(2); at pi/2 it is v.")),
            Paragraph(Text("For a coordinatewise nonnegative code c:Fin(2)->R, codeEnergy is norm(x-Dc)^2/2+lambda(c(0)+c(1)). codeCost is the existing infimum over all such real codes. The objective J is pzero codeCost(0,D)+pA codeCost(u,D)+pAB codeCost(u+v,D)+pB codeCost(v,D). The probabilities are nonnegative and sum to one. The theorem allows pA=0 and every positive pB compatible with those probabilities.")),
            Describe.Lean(DescribeId.Create("partial-absorption"),DeclarationHandle.Create(Prefix+"partial_absorption"),
                H("Exact endpoint derivatives and one common improvement"),StatementSource.FromAuthor(TheoremFormula()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume 0<lambda<1/sqrt(2), pAB>0 and pB>0. Every signal and every real angle have an attained optimum over all nonnegative two-coordinate real codes. There are open subsets of the ambient real line containing pi/4 and pi/2 on which J is differentiable at every point. The ambient derivatives, and hence the derivatives within the closed slice, are the displayed negative and positive values. Every point belonging to the closed slice and minimizing J there lies in its interior. A single interior angle has objective strictly below both endpoint objectives.")),
                    Paragraph(Text("The energy difference from a feasible candidate code is a sum of squared reconstruction differences and nonnegative complementary-gradient terms. This certifies each local optimizer against every feasible code. Near pi/4 the u+v and v samples use the second atom alone. Near pi/2 the u+v sample uses both atoms, with coefficients obtained by solving its two normal equations; the v sample still uses the second atom alone. Strict feasibility and inactive-gradient inequalities persist on ambient neighborhoods. Differentiating these certified values gives the two endpoint derivatives. Inward descent at whichever endpoint has smaller cost supplies the same dictionary for both strict comparisons. No existence of a slice minimizer, uniqueness, variation with probability ratios, or optimum over two freely moving atoms is asserted."))),DescribeRole.Theorem))));
}
