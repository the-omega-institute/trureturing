using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.MeasurementGeometry;

internal sealed class WStateBellMeasurementOptimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/MeasurementGeometry/WStateBellMeasurementOptimum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/chakrabartykundu2026network");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The W-state Bell-measurement network optimum is sqrt(13)/3.",
        H("Exact W-state Bell-measurement optimum"), Blocks(
            Paragraph(Text("The three tensor factors are ordered Alice, end node, Charlie. "
                + "Pauli coordinates k : Fin 3 are X, Y, Z in that order. "
                + "The function pauli1 is D5.S3.Quantum.QuantumChannels.SicKFidelity."
                + "SicKFidelityPauliWeight.pauli1; its arguments 1, 2, 3 give X, Y, Z. "
                + "Central indices lie in Fin 4; index 0 is the identity and indices 1, 2, 3 "
                + "select the three members of the frame. Every real coefficient is embedded "
                + "in the complex scalars by Complex.ofReal. The maxima are represented by sSup.")),
            Definition("tau", "The W-state conditional correlation vector", TauFormula(),
                "PDF page 4 defines τμν = (Tr[ρ Aμ ⊗ σₖ ⊗ Cν])ₖ₌₁,₂,₃. "
                + "It states: “We write Aᵢ = eᵢ · σ and Cⱼ = fⱼ · σ, and set A₀ = C₀ = 𝕀.” "
                + "For a nonzero central index μ its frame index has natural value μ.val − 1; "
                + "Nat.sub denotes truncated natural subtraction. "
                + "PDF page 3 defines |W⟩ = 1/√3 (|001⟩ + |010⟩ + |100⟩). "
                + "Here ρ is Matrix.vecMulVec w (star w), with the displayed literal W ket w. "
                + "The real part is taken after the trace.", AssessedProvenance.FromLiterature(Source)),
            Definition("lambda", "Optimization over orthogonal unit directions", LambdaFormula(),
                "PDF page 4: “The network value therefore depends on how much of τμν and τμ′ν′ "
                + "two perpendicular directions can capture. For two vectors τ, τ′ this is” "
                + "Λ(τ, τ′) = max over n ⟂ n′ of (τ · n)² + (τ′ · n′)². "
                + "Both directions have squared Euclidean length one. Every scalar product "
                + "and squared length is displayed as its three-coordinate sum.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("claim", "The exact optimum assertion", IffTo(Named("claim"), ClaimBody()),
                SourceQuote() + " Proposition 1 on PDF page 4 maximizes Λ over both orthonormal "
                + "frames and all four central indices. The assertion below includes index 0 "
                + "and repeated index pairs; it concerns Bell-state measurements.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("wbsm-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The exact Bell-state-measurement optimum"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "For unit a and c the W correlation T(a,c) satisfies "
                    + "9‖T(a,c)‖² = (2a₀c₀ + 2a₁c₁ − a₂c₂)² + 4a₂² + 4c₂². "
                    + "Parseval's equality for each complete orthonormal frame bounds the selected "
                    + "pairs by 13/9. Identity indices give a squared length at most 4/9; "
                    + "identical nonidentity pairs satisfy Bessel's bound. The standard frames "
                    + "give τ₃₃ = −ẑ and τ₁₃ = (2/3)x̂, which are orthogonal and attain 13/9. "
                    + "Taking the nonnegative square root gives √13/3. "
                    + "This statement does not optimize over the larger product-projective class."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("w-state-bsm-optimum"), ResolutionKind.Proved))
        )));

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance) => Describe.Lean(DescribeId.Create("wbsm-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static string SourceQuote() => "PDF page 5: “For the W state, τ₃₃ = −ẑ and τ₁₃ = ⅔x̂ "
        + "are orthogonal, which gives N_c ≥ √13/3 ≈ 1.202. The numerical optimization over frames "
        + "finds no larger value.”";
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Qualified(string owner, string name, params Formula[] arguments) => new Formula.Apply(
        Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name))), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula R() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula C() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(byte n) => Call("Fin", D(n));
    private static Formula RealVector() => new Formula.TypeArrow(Fin(3), R());
    private static Formula Frame() => new Formula.TypeArrow(Fin(3), Call("EuclideanSpace", R(), Fin(3)));
    private static Formula KetIndex() => Parenthesized(Seq(Parenthesized(Seq(Fin(2), Times, Fin(2))), Times, Fin(2)));
    private static Formula KetType() => new Formula.TypeArrow(KetIndex(), C());
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula IffTo(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula All(Formula variable, Formula type, Formula body) => Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula variable, Formula type, Formula body) => Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Fun(Formula variable, Formula type, Formula body) => Parenthesized(Seq(LambdaLower, Sp, Typed(variable, type), Mapsto, Sp, body));
    private static Formula If(Formula condition, Formula yes, Formula no) => Seq(Named("if"), Sp, Parenthesized(condition), Sp, Named("then"), Sp, yes, Sp, Named("else"), Sp, no);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Sq(Formula value) => new Formula.Power(value, D(2));
    private static Formula Sum(Formula variable, Formula type, Formula body) => Seq(new Formula.Subscript(F.Sum, Typed(variable, type)), Parenthesized(body));
    private static Formula SetOf(Formula variable, Formula type, Formula body) => Seq(OpenBrace, Typed(variable, type), Sp, Bar, Sp, body, CloseBrace);
    private static Formula DotSum(Formula u, Formula n) => Parenthesized(Sum(F.Id("i"), Fin(3), Mul(new Formula.Apply(u, [F.Id("i")]), new Formula.Apply(n, [F.Id("i")]))));
    private static Formula NormSum(Formula n) => Sum(F.Id("coord"), Fin(3), Sq(new Formula.Apply(n, [F.Id("coord")])));
    private static Formula TripleIndex(byte a, byte b, byte c) => Parenthesized(Seq(Parenthesized(Seq(D(a), Comma, Sp, D(b))), Comma, Sp, D(c)));
    private static Formula WBody() => Fun(F.Id("i"), KetIndex(), If(
        Or(Equal(F.Id("i"), TripleIndex(0, 0, 1)), Or(Equal(F.Id("i"), TripleIndex(0, 1, 0)), Equal(F.Id("i"), TripleIndex(1, 0, 0)))),
        Typed(new Formula.Fraction(D(1), Qualified("Complex", "sqrt", D(3))), C()), D(0)));
    private static Formula Pauli(Formula k) => Call("pauli1", Qualified("Fin", "succ", k));

    private static Formula CentralBody(Formula frame, Formula index)
    {
        var k = F.Id("k");
        var predecessor = If(Equal(index, D(0)), D(0), Qualified("Fin", "mk",
            Qualified("Nat", "sub", Call("val", index), D(1)), Seq(Named("by"), Sp, Named("omega"))));
        var summand = Qualified("HSMul", "hSMul",
            Qualified("Complex", "ofReal", new Formula.Apply(frame, [predecessor, k])), Pauli(k));
        return If(Equal(index, D(0)), D(1), Sum(k, Fin(3), summand));
    }

    private static Formula TauFormula()
    {
        var e = F.Id("e");
        var f = F.Id("f");
        var w = F.Id("w");
        var k = F.Id("k");
        var tensor = Qualified("Matrix", "kronecker",
            Qualified("Matrix", "kronecker", Parenthesized(CentralBody(e, Mu)), Pauli(k)), Parenthesized(CentralBody(f, Nu)));
        var density = Qualified("Matrix", "vecMulVec", w, Call("star", w));
        var trace = Qualified("Complex", "re", Qualified("Matrix", "trace", Mul(density, tensor)));
        var body = Fun(k, Fin(3), Seq(Named("let"), Sp, Typed(w, KetType()), Sp,
            Seq(Colon, Eq), Sp, WBody(), Semi, Sp, trace));
        return All(e, Frame(), All(f, Frame(), All(Mu, Fin(4), All(Nu, Fin(4),
            Equal(Call("tau", e, f, Mu, Nu), body)))));
    }

    private static Formula LambdaFormula()
    {
        var u = F.Id("u");
        var v = F.Id("v");
        var n = F.Id("n");
        var nPrime = Seq(F.Id("n"), Apos);
        var q = F.Id("q");
        var value = Add(Sq(DotSum(u, n)), Sq(DotSum(v, nPrime)));
        var admissible = And(Equal(NormSum(n), D(1)), And(Equal(NormSum(nPrime), D(1)),
            And(Equal(DotSum(n, nPrime), D(0)), Equal(q, value))));
        var set = SetOf(q, R(), Some(n, RealVector(), Some(nPrime, RealVector(), admissible)));
        return All(u, RealVector(), All(v, RealVector(), Equal(Call("lambda", u, v), Call("sSup", set))));
    }

    private static Formula ClaimBody()
    {
        var e = F.Id("e");
        var f = F.Id("f");
        var muPrime = Seq(Mu, Apos);
        var nuPrime = Seq(Nu, Apos);
        var q = F.Id("q");
        var value = Call("lambda", Call("tau", e, f, Mu, Nu), Call("tau", e, f, muPrime, nuPrime));
        var indices = Some(Mu, Fin(4), Some(Nu, Fin(4), Some(muPrime, Fin(4), Some(nuPrime, Fin(4), Equal(q, value)))));
        var set = SetOf(q, R(), Some(e, Frame(), Some(f, Frame(),
            And(Call("Orthonormal", R(), e), And(Call("Orthonormal", R(), f), indices)))));
        return Equal(Qualified("Real", "sqrt", Call("sSup", set)),
            new Formula.Fraction(Qualified("Real", "sqrt", D(1, 3)), D(3)));
    }
}
