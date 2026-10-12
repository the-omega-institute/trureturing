using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class AlternativeMeanLinearizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/AlternativeMeanLinearization.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/dumitrufrancomerino2026alternative");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A scalar characterization of alternative means whose linearizability detects commutation and at most two spectral values.",
        H("Characterizing rigid alternative means"),
        Blocks(
            SourceQuotation(),
            Entry("geometric-mean", "gmInv", "The inverse geometric mean", GeometricMean(),
                "For complex n×n matrices, gmInv A B is A⁻¹ᐟ²(A¹ᐟ²BA¹ᐟ²)¹ᐟ²A⁻¹ᐟ². "
                + "Each real matrix power displayed here is the continuous functional calculus of x↦xᵖ. "
                + "For positive definite A and B this is A⁻¹♯B, is positive definite, and is the unique "
                + "positive definite solution Y of YAY=B, as in equation (1). The definition also exists "
                + "for other complex matrices through Mathlib's total continuous functional calculus; "
                + "the geometric interpretation here is restricted to positive definite matrices.",
                DescribeRole.Definition, true),
            Entry("alternative-mean", "altMean", "The alternative mean", AlternativeMean(),
                "Definition 2.3 gives Aσ̂_fB=f(Y)Af(Y), where Y=A⁻¹♯B. The definition uses "
                + "the real continuous functional calculus on complex Hermitian matrices. "
                + "The theorem assumes f continuous and positive on (0,∞), with f(1)=1.",
                DescribeRole.Definition, true),
            Entry("linearizable", "Linearizable", "Linearizability", Linearizable(),
                "Remark 2.2 calls the alternative mean linearizable when it equals aA+bB for "
                + "some real a and b. The coefficients may depend on A and B and need not be positive.",
                DescribeRole.Definition, true),
            Entry("rigidity", "Rigid", "The property in the Question", Rigidity(),
                "Rigid f requires, for every finite dimension n and every pair of complex positive "
                + "definite matrices A and B, that the alternative mean be linearizable exactly when "
                + "A and B commute and the real spectrum of A⁻¹♯B has at most two values. "
                + "The quantifier includes dimension zero; its spectrum is empty and its matrices are unique.",
                DescribeRole.Definition, true),
            Entry("characterization", "result", "Necessary and sufficient scalar conditions", Result(),
                "Let g(s)=f(√s)². Rigidity is equivalent to injectivity of f and x↦f(x)/x on (0,∞), "
                + "together with strict convexity or strict concavity of g there. To prove sufficiency, "
                + "diagonalize Y=U diag(t) U* and put C=U*AU. Linearizability gives "
                + "(f(tᵢ)f(tⱼ)−a−btᵢtⱼ)Cᵢⱼ=0. Positivity of Cᵢᵢ gives f(tᵢ)²=a+btᵢ², "
                + "so strict convexity or concavity excludes three distinct spectral values. "
                + "For distinct x,y, writing u=f(x), v=f(y), the coefficient is "
                + "uv−a−bxy=−(u−v)(yu−xv)/(x+y). The two injectivity conditions make it nonzero. "
                + "Thus C has zero entries between distinct eigenspaces, A commutes with Y, "
                + "and A commutes with B=YAY. Conversely, commutation of A and B propagates "
                + "through the functional calculus defining Y. On at most two spectral values, "
                + "interpolation gives f(t)²=a+bt² and hence f(Y)Af(Y)=aA+bB. "
                + "For necessity, take A=[[2,1],[1,2]], Y=diag(x,y), and B=YAY. "
                + "Equal values f(x)=f(y)=c give the mean c²A; equal quotients f(x)/x=f(y)/y=c "
                + "give c²B. Both are linearizable, while (AB−BA)₁₂=2(y²−x²) is nonzero for "
                + "distinct positive x,y. Finally, a collinear triple (s,g(s)),(t,g(t)),(u,g(u)) "
                + "with 0<s<t<u yields the linearizable pair A=I, B=diag(s,t,u), "
                + "with three distinct values in the spectrum of Y=diag(√s,√t,√u). "
                + "The adjacent-slope difference is therefore nonzero. Continuity on the "
                + "convex domain 0<s<t<u makes its sign constant, giving strict convexity or "
                + "strict concavity of g. The theorem concerns D=ℂ. The same spectral argument "
                + "over real or quaternionic matrices is mathematical reasoning and is not formalized here. "
                + "The supplied quotation is tied to arXiv:2606.25150v1; agreement with the author "
                + "text is ASSUMED-UNVERIFIED. No exhaustive literature or priority claim is established.",
                DescribeRole.Theorem, false))));

    private static DocumentBlock SourceQuotation() => Paragraph(Text(
        "Dumitru, Franco, and Merino, On The Linearization of Alternative Means, arXiv:2606.25150v1, "
        + "§1, with the Question restated in Remark 4.4, supplied verbatim: “Question : Can we "
        + "characterize all functions f : (0, ∞) → (0, ∞) such that Aσ̂_f B is linearizable if and "
        + "only if AB = BA and |Spec(A⁻¹♯B)| ≤ 2 ?” Definition 2.3 specifies the alternative "
        + "mean f(A⁻¹♯B) A f(A⁻¹♯B), and Remark 2.2 specifies real coefficients in aA+bB."));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("dumitru-franco-merino-2026-alternative-mean-linearization"),
                ResolutionKind.Proved) : null);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Function => Seq(Real, Sp, To, Sp, Real);
    private static Formula Positive => Call("Ioi", D(0));
    private static Formula Mat => Call("Matrix", Call("Fin", V("n")), Call("Fin", V("n")), Complex);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Scale(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
    private static Formula Half => new Formula.Fraction(D(1), D(2));
    private static Formula NegativeHalf => new Formula.Negate(Half);
    private static Formula Y => Call("gmInv", V("A"), V("B"));
    private static Formula FY => Call("cfc", V("f"), Y);
    private static Formula Parameters(Formula body) =>
        All("n", Nat, All("A", Mat, All("B", Mat, body)));
    private static Formula Coefficients =>
        Add(Scale(V("a"), V("A")), Scale(V("b"), V("B")));

    private static Formula GeometricMean() => Disp(Parameters(Eq(Y,
        Mul(Mul(Pow(V("A"), NegativeHalf),
            Pow(Mul(Mul(Pow(V("A"), Half), V("B")), Pow(V("A"), Half)), Half)),
            Pow(V("A"), NegativeHalf)))));

    private static Formula AlternativeMean() => Disp(All("f", Function, Parameters(
        Eq(Call("altMean", V("f"), V("A"), V("B")), Mul(Mul(FY, V("A")), FY)))));

    private static Formula Linearizable() => Disp(All("f", Function, Parameters(
        Iff(Call("Linearizable", V("f"), V("A"), V("B")), Ex("a", Real, Ex("b", Real,
            Eq(Call("altMean", V("f"), V("A"), V("B")), Coefficients)))))));

    private static Formula Rigidity() => Disp(All("f", Function,
        Iff(Call("Rigid", V("f")), Parameters(Imp(Call("PosDef", V("A")),
            Imp(Call("PosDef", V("B")), Iff(Call("Linearizable", V("f"), V("A"), V("B")),
                And(Eq(Mul(V("A"), V("B")), Mul(V("B"), V("A"))),
                    Le(Call("ncard", Call("spectrum", Real, Y)), D(2))))))))));

    private static Formula Result()
    {
        Formula assumptions = And(Call("ContinuousOn", V("f"), Positive),
            And(All("x", Real, Imp(Lt(D(0), V("x")), Lt(D(0), Call("f", V("x"))))),
                Eq(Call("f", D(1)), D(1))));
        Formula quotient = Seq(LambdaLower, Sp, V("x"), Comma, Sp,
            new Formula.Fraction(Call("f", V("x")), V("x")));
        Formula g = Seq(LambdaLower, Sp, V("s"), Comma, Sp,
            Pow(Call("f", Call("sqrt", V("s"))), D(2)));
        Formula conditions = And(Call("InjOn", V("f"), Positive),
            And(Call("InjOn", Parenthesized(quotient), Positive),
                Or(Call("StrictConvexOn", Real, Positive, Parenthesized(g)),
                    Call("StrictConcaveOn", Real, Positive, Parenthesized(g)))));
        return Disp(All("f", Function, Imp(assumptions, Iff(Call("Rigid", V("f")), conditions))));
    }
}
