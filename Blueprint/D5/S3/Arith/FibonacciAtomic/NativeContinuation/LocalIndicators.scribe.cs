using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.NativeContinuation;

internal sealed class LocalIndicatorsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LtOf(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula And(params Formula[] clauses) => Seq([.. clauses.SelectMany(
        (c, i) => i == 0 ? new Formula[] { Par(c) } : [Sp, Land, Sp, Par(c)])]);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Natural => Seq(Mathbb, Grp(V("N")));
    private static Formula Integer => Seq(Mathbb, Grp(V("Z")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static DocumentBlock Definition(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("native-local-indicator-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every original position has a positive five-mode marginal and three noncentered normalized indicators in that marginal's one L2 space.",
        H("Actual Native Marginal Indicators and Strict Local Gram"), Blocks(
            Paragraph(Text("The source and laws are the original JointLaw.Source(n) and law(n,t,e). The initial seam is false, each printed triple is read from high bit to low bit, and the window list keeps its chronological order. The terminal seam is unrestricted. Null prefixes and the all-null source belong to this same domain. Position i in Fin n corresponds to the original position j=i.val+1.")),
            Definition("isolated", "A source realizing each local mode",
                "isolated(i,a) places a at position i and the null mode everywhere else. It is legal for every finite length, position and one of the five modes. A null suffix is legal at either incoming seam, including the true seam left by a low or endpoint mode."),
            Definition("modeMass", "Mass from the original full source",
                "modeMass(n,t,e,i,a) is mass(law(n,t,e),w(i)=a), summed over the entire original Source(n). It is not a product-law or Markov approximation."),
            Definition("marginalMeasure", "The actual marginal probability measure",
                "For n at least three, 0<t<1 and e equal to minus one or one, marginalMeasure(n,t,e,i) is the discrete probability measure whose singleton masses are modeMass(n,t,e,i,a). The theorem identifies its mass on every set with the corresponding original-source event mass."),
            Definition("marginal_finite", "Probability and finite event measures",
                "The actual marginal has total mass one. Every occupancy event therefore has finite measure and defines a constant indicator in L2."),
            Definition("occupancy", "The three original occupancy events",
                "occupancy(0) is the set containing low and ends, occupancy(1) contains high and ends, and occupancy(2) contains middle. These are x,y,z respectively. The endpoint event is their first two sets' intersection, while the third is disjoint from both."),
            Definition("normalizedIndicator", "Noncentered vectors in one actual L2",
                "normalizedIndicator(n,t,e,i,r) is the constant-one indicator of occupancy(r), multiplied by the reciprocal square root of its actual marginal event mass. All three vectors belong to Lp(R,2,marginalMeasure(n,t,e,i)); no mean is subtracted."),
            Definition("localGram", "The three-index actual Gram",
                "localGram(n,t,e,i)(r,s) is the real L2 inner product of normalizedIndicator(n,t,e,i,r) and normalizedIndicator(n,t,e,i,s). Its two indices both range over Fin 3."),
            Definition("means", "The actual X,Y,Z means",
                "means(n,t,e,i,0)=modeMass(low)+modeMass(ends), means(n,t,e,i,1)=modeMass(high)+modeMass(ends), and means(n,t,e,i,2)=modeMass(middle), with the same n,t,e,i in every term."),
            Definition("coupling", "The normalized same-window endpoint mass",
                "coupling(n,t,e,i)=modeMass(n,t,e,i,ends)/sqrt(means(n,t,e,i,0)*means(n,t,e,i,1)). The numerator is the original kappa. Strict positivity of the low, high and endpoint modes makes this ratio strictly between zero and one."),
            Describe.Lean(DescribeId.Create("native-local-indicator-gram"),
                DeclarationHandle.Create(Prefix + "native_local_indicator_gram"),
                H("Positive actual marginal and exact normalized Gram"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In the formula, mu(n,t,e,i) abbreviates marginalMeasure, event(i,E) is the predicate w(i) in E on Source(n), and U(c) is the three-by-three matrix with rows (1,c,0), (c,1,0), (0,0,1). Every auxiliary expression retains the same original position and source law.")),
                    Paragraph(Text("A legal source with only the chosen local mode makes every singleton event nonempty. Strict positivity of the full source law gives positive mass to all five modes. Summing these masses gives the actual marginal probability measure. The L2 indicator inner product is the measure of the intersection, so the three normalized vectors have the displayed Gram. The positive low and high masses give X*Y greater than kappa squared.")),
                    Paragraph(Text("The statement ranges over every original position and both signs separately. Equality between the two signs, the eigenvalue multiset, the original piecewise Psi functional, independence from t, and the all-position Fibonacci quotient are additional assertions."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var n = V("n"); var t = V("t"); var e = V("e"); var i = V("i");
        var c = Call("coupling", n, t, e, i);
        var signs = Seq(EqOf(e, Seq(Minus, D(1))), Sp, Lor, Sp, EqOf(e, D(1)));
        var conclusion = And(
            All("E", Call("Set", V("Window")), EqOf(
                Call("real", Call("mu", n, t, e, i), V("E")),
                Call("mass", Call("law", n, t, e), Call("event", i, V("E"))))),
            All("a", V("Window"), LtOf(D(0), Call("modeMass", n, t, e, i, V("a")))),
            All("r", Call("Fin", D(3)), LtOf(D(0), Call("means", n, t, e, i, V("r")))),
            And(LtOf(D(0), c), LtOf(c, D(1))),
            EqOf(Call("localGram", n, t, e, i), Call("U", c)));
        return All("n", Natural, Imp(LeOf(D(3), n), All("t", Real,
            Imp(And(LtOf(D(0), t), LtOf(t, D(1))), All("e", Integer,
                Imp(signs, All("i", Call("Fin", n), conclusion)))))));
    }
}
