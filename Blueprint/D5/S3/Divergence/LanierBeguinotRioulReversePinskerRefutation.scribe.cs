using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class LanierBeguinotRioulReversePinskerRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Divergence/LanierBeguinotRioulReversePinskerRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Divergence/lanier2025maximal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A noncommuting qubit pair violates the maximal reverse Pinsker bound.",
        H("A counterexample to the maximal reverse Pinsker bound"),
        Blocks(
            Paragraph(Text("Lanier, Béguinot and Rioul, arXiv:2501.14340v1, §III-C, p. 5: "
                + "“We conjecture that (49) is in fact not necessary for (50) to hold.” "
                + "The same paragraph states: “Our bound holds in general for any f-divergence, "
                + "in particular for the maximal f-divergence.”")),
            Entry("maximal", "maxDivergence", "The maximal spectral divergence", DivergenceDefinition(),
                "Equation (4), p. 1, is the real part of the trace of the displayed product. "
                + "The matrix function is Mathlib's continuous functional calculus. "
                + "For the operator-convex generator f(x)=(x−1)², its status as a quantum "
                + "f-divergence satisfying Definition 2 uses the Matsumoto theorem cited in the source. "
                + "That general data-processing theorem is not proved here.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Entry("bound", "reversePinskerBound", "The proposed right-hand side", BoundDefinition(),
                "Equation (50), p. 4, uses the least and greatest points of the real spectrum "
                + "of the relative matrix and the trace norm of the state difference. "
                + "The numerical example below has spectral endpoints 4/5 and 6/5, so both denominators are nonzero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("conjecture", "claim", "The conjectured maximal-divergence inequality", ClaimDefinition(false),
                "“We conjecture that (49) is in fact not necessary for (50) to hold.” (§III-C, p. 5.) "
                + "The displayed proposition is its maximal-divergence instance: every dimension, "
                + "every real generator convex on the nonnegative half-line and zero at one, "
                + "and every pair of positive semidefinite states with the second positive definite. "
                + "Each state has trace one. No matrix-order condition on the absolute difference is imposed.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("refutation", "result", "A qubit counterexample", Disp(Seq(Neg, Sp, Parenthesized(ClaimBody(false)))),
                "Let σ=diag(9/25,16/25) and ρ=((9/25,12/125),(12/125,16/25)). "
                + "Both matrices have trace one; σ is positive definite and ρ is positive semidefinite. "
                + "The positive square root of σ is diag(3/5,4/5), and the relative matrix "
                + "is ((1,1/5),(1/5,1)), with spectrum {4/5,6/5}. For f(x)=(x−1)² its "
                + "matrix function is I/25, giving maxDivergence=1/25=25/625. "
                + "The absolute difference is (12/125)I, with trace norm 24/125, "
                + "so reversePinskerBound=24/625. This contradicts the proposed inequality. "
                + "The matrix ρ+σ−|ρ−σ|=((78/125,12/125),(12/125,148/125)) is positive definite. "
                + "Thus the same pair also contradicts the conditional maximal-divergence statement "
                + "of Theorem 4. The proof checks that stronger failure before deriving the displayed negation. "
                + "The result concerns the spectral formula (4); the Definition 2 admissibility "
                + "theorem and the source's other choices of quantum divergence remain separate.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("lanier-beguinot-rioul-2025-reverse-pinsker-condition-refutation"),
                ResolutionKind.Refuted) : null);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Inverse(Formula value) => new Formula.Power(Parenthesized(value), Seq(Minus, D(1)));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Mat => Call("Matrix", Call("Fin", V("n")), Call("Fin", V("n")), Complex);
    private static Formula Rho => V("rho");
    private static Formula Sigma => V("sigma");
    private static Formula Gen => V("f");
    private static Formula Relative => Mul(Mul(Inverse(Call("sqrt", Sigma)), Rho), Inverse(Call("sqrt", Sigma)));
    private static Formula MinSpectrum => Call("sInf", Call("spectrum", Real, Relative));
    private static Formula MaxSpectrum => Call("sSup", Call("spectrum", Real, Relative));
    private static Formula Generator(Formula body) => All("f", Seq(Real, Sp, To, Sp, Real), body);

    private static Formula DivergenceDefinition() => Disp(All("n", Nat, Generator(
        All("rho", Mat, All("sigma", Mat, Eq(Call("maxDivergence", Gen, Rho, Sigma),
            Call("re", Call("trace", Mul(Mul(Call("sqrt", Sigma),
                Call("cfc", Gen, Relative)), Call("sqrt", Sigma))))))))));
    private static Formula BoundDefinition() => Disp(All("n", Nat, Generator(
        All("rho", Mat, All("sigma", Mat, Eq(Call("reversePinskerBound", Gen, Rho, Sigma),
            Mul(new Formula.Fraction(Call("traceNorm", Sub(Rho, Sigma)), D(2)), Parenthesized(Add(
                new Formula.Fraction(Call("f", MinSpectrum), Sub(D(1), MinSpectrum)),
                new Formula.Fraction(Call("f", MaxSpectrum), Sub(MaxSpectrum, D(1))))))))))));
    private static Formula ClaimBody(bool conditional)
    {
        Formula conclusion = Le(Call("maxDivergence", Gen, Rho, Sigma), Call("reversePinskerBound", Gen, Rho, Sigma));
        if (conditional) conclusion = Imp(Le(Call("abs", Sub(Rho, Sigma)), Add(Rho, Sigma)), conclusion);
        return All("n", Nat, Generator(Imp(Call("ConvexOn", Real, Call("Ici", D(0)), Gen),
            Imp(Eq(Call("f", D(1)), D(0)), All("rho", Mat, All("sigma", Mat,
                Imp(Call("PosSemidef", Rho), Imp(Eq(Call("trace", Rho), D(1)),
                    Imp(Call("PosDef", Sigma), Imp(Eq(Call("trace", Sigma), D(1)), conclusion))))))))));
    }
    private static Formula ClaimDefinition(bool conditional) => Disp(Iff(
        V(conditional ? "claimTheorem4" : "claim"), ClaimBody(conditional)));
}
