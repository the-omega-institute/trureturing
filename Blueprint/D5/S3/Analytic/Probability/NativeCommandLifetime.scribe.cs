using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class NativeCommandLifetimeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform lifetime estimates for finite native commands driven by unreweighted fair signs.",
        H("Native command lifetimes"),
        Blocks(
            Paragraph(Text("A model fixes r>0, 0<l<u<r/2 and an interior source. Its raw density is smooth and positive, and its horizontal covariance is smooth, symmetric and positive definite on an open neighbourhood of the closed height cylinder. Both phase lifts are periodic under integer multiples of 2π. The drift is the density-divergence drift of these raw coefficients, and sigma is the positive square root of the covariance.")),
            Paragraph(Text("The source map sends a control triple (a,b,j) to height k_o+a and the actual phase classes of alpha_o+b/2 and beta_o+(1/2-k_o/r)b-j/r. The two phase circles have period 2π. On each cell of duration delta=1/n², the increment is d(q)delta+sqrt(2delta)sigma(q)xi. Each of the four sign pairs has probability 1/4 independently of every preceding pair.")),
            Paragraph(Text("A chord with increment v has controls a+theta v1 and b+theta v2, and chronological area j+theta a v2+theta²v1v2/2. Its first contact with either height wall cuts the chord and starts a hold. The complete word has n³ cells. If all cells survive, a final cell of the same original duration moves the height linearly to the upper wall while the second control stays constant. The control lifts and the area are translated at joins, without a reset.")),
            Describe.Lean(
                DescribeId.Create("command-area"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/NativeCommandLifetime.commandArea"),
                H("Ordinary chronological area"),
                StatementSource.FromAuthor(Disp(AreaDefinition())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integral is the ordinary integral of the first control against the derivative of the absolutely continuous second control. It includes a partial final chord and all elapsed original durations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tail-probability"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/NativeCommandLifetime.tailProbability"),
                H("Uniform finite-word tail probability"),
                StatementSource.FromAuthor(Disp(LawDefinition(false))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sum ranges over every sign-pair word, including words with unused suffixes after killing. No word is rejected or reweighted. The first wall time zeta is computed from the actual held state, whose third coordinate is the physical beta phase class. The ordinary chronological integral is the third coordinate of the command/control triple (commandArea), and the theorem identifies it with the corresponding input of physicalState."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("excess-expectation"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/NativeCommandLifetime.excessExpectation"),
                H("Expected excess lifetime"),
                StatementSource.FromAuthor(Disp(LawDefinition(true))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same uniform finite-word law defines the expectation of the positive part of the excess lifetime."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-lifetime-estimates"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/NativeCommandLifetime.actual_lifetime_estimates"),
                H("Uniform full-lifetime estimates"),
                StatementSource.FromAuthor(Disp(MainStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The constants depend only on the fixed raw model and interval. Every sufficiently fine mesh satisfies both estimates for every nonnegative real time and every real cutoff at least one. The theorem also identifies the ordinary integral with the recursively computed chronological area at every nonnegative prefix, identifies the held state on the actual torus, and certifies the original control and the finite positive first-wall lifetime.")),
                    Paragraph(Text("Compactness of one phase fundamental domain bounds the derivative-defined height drift and gives a positive lower bound for the first diagonal covariance entry. A positive exponential test of height has a uniformly positive expected increment for sufficiently small mesh. The exact fair-sign exponential average is the exponential drift factor times two hyperbolic cosines. The public even-factorial-sum inequality supplies the required quadratic lower bounds.")),
                    Paragraph(Text("Summing the stopped increments over an arbitrary finite horizon bounds delta times the sum of endpoint survival probabilities. The last comparison endpoint retains its exit overshoot; bounded raw increments bound the exponential test there. Thus the occupation estimate is derived from the raw model rather than imposed as a drift, tail or contraction hypothesis.")),
                    Paragraph(Text("The occupation bound gives a common mean bound from every alive triple. Markov's inequality then bounds survival across a block by one half. Fresh fair signs give geometric decay over successive blocks. Finite-prefix arguments bound both the tail and excess lifetime, with the terminal upper-wall cell accounted for by the time shift of at most one.")),
                    Paragraph(Text("For each cut chord, absolute continuity and the fundamental theorem of calculus identify its polynomial area with its ordinary integral. Public original-control concatenation gives integral additivity with the translated real control lift. Induction establishes the identification at every prefix. The chord height is affine, so the recursive killing fraction is exactly the first hit of either wall. These identities transfer both estimates to the actual executed law."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula D(int n) => new Formula.Number(n);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula>();
        foreach (var word in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(F.Id(word));
        }
        var op = Seq(Operatorname, Grp([.. parts]));
        return args.Length == 0 ? op : new Formula.Apply(op, [.. args]);
    }
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Fn(string name, Formula type, Formula body) =>
        Par(Seq(V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Pow(Formula a, int n) => new Formula.Power(Par(a), D(n));
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula Words => new Formula.TypeArrow(Call("Fin", Pow(V("n"),3)), Call("SignPair"));
    private static Formula Cmd(Formula t, int i) => App(Call("command", V("B"), V("n"), V("w"), t), D(i));
    private static Formula Zeta => Call("zeta", V("B"), V("n"), V("w"));
    private static Formula Area(Formula t) => Call("commandArea", V("B"), V("n"), V("w"), t);
    private static Formula State(Formula t) => Call("heldState", V("B"), V("n"), V("w"), t);
    private static Formula BindWord(Formula body) =>
        All("B", Call("Model"), All("n", N, All("w", Words, body)));
    private static Formula AreaDefinition() => BindWord(All("T", R,
        Eq(Area(V("T")), Call("intervalIntegral", D(0), V("T"),
            Fn("s", R, Multiply(Cmd(V("s"),0),
                Call("deriv", Fn("x", R, Cmd(V("x"),1)), V("s"))))))));
    private static Formula LawDefinition(bool excess)
    {
        var x = V(excess ? "R" : "t");
        var term = excess ? Call("max", Subtract(Zeta,x),D(0))
            : Call("ite", Lt(x,Zeta),D(1),D(0));
        var sum = Seq(new Formula.Subscript(Sum,
            Seq(V("w"),Colon,Sp,Words)),Sp,Par(term));
        var mass = new Formula.Power(Par(Div(D(1),D(4))),Pow(V("n"),3));
        return All("B",Call("Model"),All("n",N,All(excess ? "R" : "t",R,
            Eq(Call(excess ? "excessExpectation" : "tailProbability",V("B"),V("n"),x),
                Multiply(mass,sum)))));
    }
    private static Formula MainStatement()
    {
        var n=V("n"); var h=V("h"); var t=V("t"); var cutoff=V("R"); var T=V("T");
        var tail=All("t",R,Imp(Le(D(0),t),
            Le(Call("tailProbability",V("B"),n,t),
                new Formula.Power(Par(Div(D(1),D(2))),
                    Call("Nat.floor",Div(Call("max",Subtract(t,D(1)),D(0)),h))))));
        var excess=All("R",R,Imp(Le(D(1),cutoff),
            Le(Call("excessExpectation",V("B"),n,cutoff),
                Multiply(Multiply(D(2),h),new Formula.Power(Par(Div(D(1),D(2))),
                    Call("Nat.floor",Div(Subtract(cutoff,D(1)),h)))))));
        var control=Call("OriginalControl",Call("nativeBase",V("B")),T,
            Fn("t",R,Call("Prod.fst",State(t))),Fn("t",R,Cmd(t,1)));
        var prefix=All("T",R,Imp(Le(D(0),T),And(control,
            And(Eq(Area(T),Cmd(T,2)),Eq(State(T),
                Call("physicalState",V("B"),Call("command",V("B"),n,V("w"),T)))))));
        var paths=All("w",Words,And(Lt(D(0),Zeta),And(
            Le(Zeta,Multiply(Add(Pow(n,3),D(1)),Call("mesh",n))),prefix)));
        return All("B",Call("Model"),Some("h",R,Some("M",R,Some("n0",N,
            And(Lt(D(0),h),And(Lt(D(0),V("M")),And(Le(D(1),V("n0")),
                All("n",N,Imp(Le(V("n0"),n),And(tail,And(excess,paths)))))))))));
    }
}
