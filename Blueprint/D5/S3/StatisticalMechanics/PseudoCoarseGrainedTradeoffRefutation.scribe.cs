using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class PseudoCoarseGrainedTradeoffRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/PseudoCoarseGrainedTradeoffRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/gu2023dissipationtimetradeoff");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive three-state cyclic chain violates the proposed two-state lower bound on non-adiabatic entropy production.",
        H("A counterexample to the pseudo-coarse-grained dissipation-time trade-off"),
        Blocks(
            Paragraph(Text(
                "The states are Fin n, the indices 0 through n − 1. The real entry a(i,j) is the transition rate "
                    + "from j to i. Write W = generator(a): its off-diagonal entries are a(i,j), and its jth "
                    + "diagonal entry is minus the sum of a(i,j) over i distinct from j. Thus each column sums "
                    + "to zero. For finite real vectors, klDivergence(v,w) is the sum of v(i) log(v(i)/w(i)). "
                    + "The notation ![x,1 − x] denotes the function on Fin 2 with those two real coordinates. "
                    + "These are the master equation, total-rate convention and divergence in the source's "
                    + "TeX lines 159–184.")),
            Describe.Lean(
                DescribeId.Create("binary-steady-state"),
                DeclarationHandle.Create(Prefix + "binarySteadyState"),
                H("The steady-state coordinate determined by two endpoints"),
                StatementSource.FromAuthor(Disp(BinarySteadyStateFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a two-state process whose first-coordinate endpoints are x and y, total rate k and "
                        + "elapsed time τ, the first steady-state coordinate is x + (y − x)/(1 − exp(−kτ)). "
                        + "The other coordinate is its complement. This is the equation labelled eq:p1 in TeX "
                        + "lines 191–196. The real-valued definition allows arbitrary real inputs; division "
                        + "is total, so a zero denominator has the usual real-field value zero for the quotient."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The proposed bound for every nontrivial two-part partition"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural n, choose an array a, a positive normalized vector u annihilated by W, "
                        + "a real-time curve p and a positive time τ. All off-diagonal entries of a are positive. "
                        + "At every real t, p has derivative Wp(t). The initial vector p(0) is positive and "
                        + "normalized, and the final vector p(τ) is positive. The finite set ω and its "
                        + "complement are both nonempty. Sum the initial and final probabilities over ω to "
                        + "obtain x and y, take k = −trace(W), and compute s with binarySteadyState. "
                        + "Whenever 0 < s < 1, the proposed inequality bounds the binary divergence drop "
                        + "relative to ![s,1 − s] by the full divergence drop relative to u. "
                        + "This is a reading of the source's Eq. (13), TeX lines 327–337, restricted to "
                        + "strictly positive off-diagonal entries and endpoints and an interior binary "
                        + "steady state. Detailed balance is not required. The derivative hypothesis ranges "
                        + "over all real times; the statement imposes positivity only at the two endpoints."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A three-state cyclic counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Qualified("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Use n = 3 and the off-diagonal array a = [[0,1/100,1],[1,0,1/100],[1/100,1,0]]. "
                            + "Every entry between distinct states is positive. Its generator is "
                            + "W = [[−101,1,100],[100,−101,1],[1,100,−101]]/100. "
                            + "The vector u = (1/3,1/3,1/3) satisfies Wu = 0.")),
                    Paragraph(Text(
                        "Set A = 303/200, B = 99√3/200, v = (2,−1,−1) and w = (0,√3,−√3). "
                            + "Direct multiplication gives Wv = −Av + Bw and Ww = −Bv − Aw. "
                            + "Define P(t) = u + exp(−At)(cos(Bt)v + sin(Bt)w)/12. "
                            + "Differentiate the exponential, cosine and sine coordinate by coordinate. "
                            + "The two matrix identities and Wu = 0 give P′(t) = WP(t) for every real t.")),
                    Paragraph(Text(
                        "Choose τ = π/B and put r = exp(−Aτ). At zero the curve is "
                            + "P(0) = (1/2,1/4,1/4). Since Bτ = π, cos(Bτ) = −1 and sin(Bτ) = 0, "
                            + "its other endpoint is P(τ) = ((2 − r)/6,(4 + r)/12,(4 + r)/12).")),
                    Paragraph(Text(
                        "The inequalities √3 > 17/10 and π > 3 imply B > 0, τ > 0 and "
                            + "Aτ = 101√3π/99 > 3. The exponential inequality exp(Aτ) ≥ 1 + Aτ > 4 "
                            + "then gives 0 < r < 1/4. The total rate is −trace(W) = 303/100 = 2A. "
                            + "Therefore exp(−(303/100)τ) = r². Substituting this identity into "
                            + "binarySteadyState(1/2,(2 − r)/6,303/100,τ) and clearing the nonzero "
                            + "denominators 1 − r and 1 − r² gives s = (2 − 3r)/(6(1 − r)). "
                            + "For every r in (0,1/4), its denominator is positive and 0 < s < 1/3 < 1.")),
                    Paragraph(Text(
                        "Write d(z,b) = klDivergence(![z,1 − z],![b,1 − b]). "
                            + "Splitting the second coordinate into two equal parts gives "
                            + "klDivergence(![z,(1 − z)/2,(1 − z)/2],u) = d(z,1/3): "
                            + "the two equal summands have the same probability ratio and add to the "
                            + "single binary summand. For 0 < x,y,s < 1, expanding the logarithms of "
                            + "quotients and products gives "
                            + "(d(x,1/3) − d(y,1/3)) − (d(x,s) − d(y,s)) "
                            + "= (x − y) log(2s/(1 − s)).")),
                    Paragraph(Text(
                        "Take x = 1/2, y = (2 − r)/6 and s = (2 − 3r)/(6(1 − r)). "
                            + "Both three-coordinate endpoints have the split form just described. "
                            + "The logarithm's argument simplifies to (4 − 6r)/(4 − 3r). "
                            + "For 0 < r < 1/4 this ratio is strictly between zero and one, so its "
                            + "logarithm is negative. Also x − y = (1 + r)/6 > 0. "
                            + "Consequently the full divergence drop is strictly smaller than the "
                            + "binary divergence drop.")),
                    Paragraph(Text(
                        "Finally, u and P(0) are positive normalized vectors, and the displayed "
                            + "endpoint and the bounds on r make P(τ) positive. Take ω = {0}; its "
                            + "complement contains 1. All hypotheses of claim now hold for a, u, P and τ, "
                            + "with aggregate endpoints x = 1/2 and y = (2 − r)/6 and the interior value "
                            + "s above. The asserted non-strict inequality contradicts the strict reverse "
                            + "inequality, proving the negation of claim."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gu-2023-pseudo-coarse-grained-tradeoff"),
                    ResolutionKind.Refuted))
        )));

    private static Formula BinarySteadyStateFormula()
    {
        Formula value = Add(V("x"), Fraction(Subtract(V("y"), V("x")),
            Subtract(RealNumber(1), Call("Real.exp", Negate(Multiply(V("k"), V("τ")))))));
        return All("x", Reals(), All("y", Reals(), All("k", Reals(), All("τ", Reals(),
            Equal(Typed(Call("binarySteadyState", V("x"), V("y"), V("k"), V("τ")), Reals()), value)))));
    }

    private static Formula ClaimFormula()
    {
        Formula conclusion = LessOrEqual(
            Subtract(Divergence(BinaryVector(V("x")), BinaryVector(V("s"))),
                Divergence(BinaryVector(V("y")), BinaryVector(V("s")))),
            Subtract(Divergence(At(V("p"), RealNumber(0)), V("u")),
                Divergence(At(V("p"), V("τ")), V("u"))));
        Formula aggregate = Let("x", SumOver("i", At(V("p"), RealNumber(0), V("i")), V("ω")),
            Let("y", SumOver("i", At(V("p"), V("τ"), V("i")), V("ω")),
                Let("k", Negate(Call("Matrix.trace", Generator())),
                    Let("s", Call("binarySteadyState", V("x"), V("y"), V("k"), V("τ")),
                        Arrow(Less(RealNumber(0), V("s")),
                            Arrow(Less(V("s"), RealNumber(1)), conclusion))))));
        Formula[] hypotheses =
        [
            All("i", Indices(), All("j", Indices(),
                Arrow(NotEqual(V("i"), V("j")), Less(RealNumber(0), At(V("a"), V("i"), V("j")))))),
            All("i", Indices(), Less(RealNumber(0), At(V("u"), V("i")))),
            Equal(SumOver("i", At(V("u"), V("i"))), RealNumber(1)),
            Equal(Call("Matrix.mulVec", Generator(), V("u")),
                At(Qualified("Function", "const"), Indices(), RealNumber(0))),
            All("t", Reals(), Call("HasDerivAt", V("p"),
                Call("Matrix.mulVec", Generator(), At(V("p"), V("t"))), V("t"))),
            Less(RealNumber(0), V("τ")),
            All("i", Indices(), Less(RealNumber(0), At(V("p"), RealNumber(0), V("i")))),
            Equal(SumOver("i", At(V("p"), RealNumber(0), V("i"))), RealNumber(1)),
            All("i", Indices(), Less(RealNumber(0), At(V("p"), V("τ"), V("i")))),
            Call("Finset.Nonempty", V("ω")),
            Call("Finset.Nonempty", Call("Compl.compl", V("ω"))),
        ];
        for (var index = hypotheses.Length - 1; index >= 0; index--)
            aggregate = Arrow(hypotheses[index], aggregate);
        return Equivalence(Qualified("claim"),
            All("n", Naturals(), All("a", new Formula.TypeArrow(Indices(), Vector()),
                All("u", Vector(), All("p", new Formula.TypeArrow(Reals(), Vector()),
                    All("τ", Reals(), All("ω", Call("Finset", Indices()), aggregate)))))));
    }

    private static Formula V(string name) => name switch
    {
        "τ" => Tau,
        "ω" => Omega,
        _ => F.Id(name),
    };
    private static Formula Qualified(params string[] names)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        foreach (var part in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. parts])));
    }
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Qualified(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Indices() => Call("Fin", V("n"));
    private static Formula Vector() => new Formula.TypeArrow(Indices(), Reals());
    private static Formula RealNumber(byte value) => Typed(D(value), Reals());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Let(string name, Formula value, Formula body) =>
        Seq(Qualified("let"), Sp, Typed(V(name), Reals()), Sp, Colon, Eq, Sp,
            Parenthesized(value), Semi, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula body, Formula? set = null) =>
        Seq(new Formula.Subscript(Sum, set is null ? Typed(V(name), Indices())
            : Seq(Typed(V(name), Indices()), Sp, InMacro, Sp, set)), Sp, Parenthesized(body));
    private static Formula BinaryVector(Formula value) => Typed(
        Seq(Bang, OpenBracket, value, Comma, Sp, Subtract(RealNumber(1), value), CloseBracket),
        new Formula.TypeArrow(Call("Fin", D(2)), Reals()));
    private static Formula Generator() => Call("D5.S3.StatisticalMechanics.MarkovMpembaTripletRefutation.generator", V("a"));
    private static Formula Divergence(Formula left, Formula right) =>
        Call("D5.S3.Divergence.ClassicalDPI.klDivergence", left, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Fraction(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Negate(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessOrEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Arrow(Formula premise, Formula conclusion) =>
        new Formula.TypeArrow(Parenthesized(premise), Parenthesized(conclusion));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
