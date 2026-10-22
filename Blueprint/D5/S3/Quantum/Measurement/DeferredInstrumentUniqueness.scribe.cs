using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class DeferredInstrumentUniquenessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/carmeliheinosaaritoigo2025postponing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The upper-boundary joint instrument of a noisy sharp meter and a depolarizing channel is unique.",
        H("Uniqueness of the upper-boundary deferred-measurement instrument"), Blocks(
            Node("q", "The sharp meter", "Q", SharpFormula(),
                "The columns of U form the orthonormal basis of the sharp meter. Its x-th effect is the conjugate of the standard rank-one projection. This is the sharp meter underlying Eq. (eq:QsPt).",
                AssessedProvenance.FromLiterature(Source)),
            Node("qs", "The noisy meter", "Qs", NoisyFormula(),
                "Equation (eq:QsPt) mixes each sharp effect with the uniform effect. The definition is a matrix formula for every real s; its use as a meter is subject to positivity. Every displayed cast specifies its target field.",
                AssessedProvenance.FromLiterature(Source)),
            Node("it", "The depolarizing map", "It", ChannelFormula(),
                "Equation (eq:Ir) defines the depolarizing map. Its action is specified on every complex matrix, without a positivity or trace-one restriction on the argument. The trace factor is complex, while the noise coefficient is formed in ℝ before being cast to ℂ.",
                AssessedProvenance.FromLiterature(Source)),
            Node("smax", "The upper-boundary noise", "sMax", BoundaryFormula(),
                "Solving the upper equality in Eq. (eq:QI_comp_neg) for s gives this expression. The compatibility theorem uses d ≥ 2 and −1/(d²−1) ≤ t ≤ 1. The real-valued definition itself is total and imposes none of these restrictions.",
                AssessedProvenance.FromLiterature(Source)),
            Node("a2", "The second square-root coefficient", "a2", CoefficientFormula(),
                "This is the k = 2 coefficient in Eq. (eq:ab_bis), with √(d²) replaced by d for a natural dimension. All arithmetic inside the square roots and the quotient takes place in ℝ.",
                AssessedProvenance.FromLiterature(Source)),
            Node("b", "The noise square root", "b", NoiseRootFormula(),
                "The coefficient b in Eq. (eq:ab_bis) is the nonnegative real square root of 1 − t. As a real square-root expression it is defined for every real t.",
                AssessedProvenance.FromLiterature(Source)),
            Node("itilde", "The boundary instrument", "Itilde", InstrumentFormula(),
                "Equation (eq:tildeJ) gives this outcome map. The three terms respectively contain the Born trace, the symmetrized product with the sharp effect, and the input matrix. Each real coefficient is cast to ℂ after its indicated product or square is formed, and the outer denominator is the direct cast of d to ℂ.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The full uniqueness assertion", "claim", Equal(V("claim"), Parenthesized(ClaimBody())),
                "The question following the proof of the W-covariant upper-boundary result asks whether there exist other, necessarily noncovariant, joint instruments. This proposition states uniqueness among all completely positive outcome maps in every dimension d ≥ 2 and throughout the closed upper boundary. The two marginal conditions are those of Eq. (eq:joint_J), with the meter condition written as a trace identity on every complex matrix. The biconditional also asserts that the displayed instrument has these marginals; it assumes no covariance of a competitor.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("Uniqueness without a covariance assumption"),
                StatementSource.FromAuthor(Disp(V("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Work first in the standard basis, and put α = a₂(d,t), β = b(t), "
                        + "γ = √(t(d²−1)+1) = β+dα and κ = α+β. Write eⱼᵢ for the tensor "
                        + "basis with output index j and input index i, Ω = ∑ᵢ eᵢᵢ, and "
                        + "vₓ = αΩ+βeₓₓ. The Choi matrix of the displayed outcome map is "
                        + "Aₓ = (vₓvₓ* + β²∑ⱼ≠ₓ eⱼₓeⱼₓ*)/d. These matrices are positive "
                        + "semidefinite, sum to B = tΩΩ*+(β²/d)1, and have output partial "
                        + "traces Qs(1,sMax(d,t),x). Thus they give the instrument described "
                        + "in Eq. (eq:tildeJ) of Carmeli, Heinosaari and Toigo.")),
                    Paragraph(Text(
                        "For −1/(d²−1) < t < 1, the quadratic certificate on a complex "
                        + "array w is qₓ(w) = ∑ᵢ≠ₓ ∑ⱼ≠ᵢ |wⱼᵢ|² + "
                        + "(κ/β)(∑ᵢ |wᵢᵢ|² − (α/γ)|∑ᵢ wᵢᵢ|²) − |wₓₓ|². "
                        + "Here β, γ and κ are positive. Subtracting (wₓₓ/κ)vₓ from "
                        + "the diagonal reduces its diagonal part to κ/β times "
                        + "∑ᵢ |zᵢ|² − (α/γ)|∑ᵢ zᵢ|². If α ≥ 0, Cauchy–Schwarz "
                        + "bounds this last expression below by (β/γ)∑ᵢ |zᵢ|²; if "
                        + "α < 0, it bounds itself below by ∑ᵢ |zᵢ|². Consequently "
                        + "qₓ is nonnegative and vanishes exactly when w lies in "
                        + "Sₓ = span{vₓ} ⊕ span{eⱼₓ : j ≠ x}.")),
                    Paragraph(Text(
                        "For a competitor write Cₓ = Bₓ*Bₓ. The fixed channel and "
                        + "trace marginals make the sum of qₓ over all conjugate Gram "
                        + "rows of all Bₓ equal to zero. Nonnegativity makes each term "
                        + "zero, so every such row belongs to Sₓ and Cₓ is supported "
                        + "there. Set Hₓ = Cₓ−Aₓ. The channel condition gives ∑ₓHₓ = 0. "
                        + "For j ≠ x, eⱼₓ is orthogonal to Sᵧ whenever y ≠ x, so this "
                        + "sum forces the corresponding rows and columns of Hₓ to "
                        + "vanish. The remaining Hermitian difference is a multiple "
                        + "of vₓvₓ*. Its output partial trace is zero by the trace "
                        + "condition, and vₓ ≠ 0, so that multiple is zero. Choi "
                        + "injectivity then identifies every outcome map.")),
                    Paragraph(Text(
                        "At t = −1/(d²−1), γ = 0 and BΩ = 0. Positivity and the "
                        + "channel sum force CₓΩ = 0, so each conjugate Gram row has "
                        + "zero diagonal sum. On this subspace the certificate is "
                        + "∑ᵢ≠ₓ ∑ⱼ≠ᵢ |wⱼᵢ|² + (κ/β)∑ᵢ |wᵢᵢ|² − |wₓₓ|². "
                        + "Subtracting its component along vₓ proves nonnegativity "
                        + "with the same zero space Sₓ, and the same elimination "
                        + "applies. At t = 1, B = ΩΩ* has rank one. Each positive "
                        + "Cₓ is therefore a nonnegative multiple of ΩΩ*, and the "
                        + "trace marginal fixes that multiple as 1/d, which is Aₓ.")),
                    Paragraph(Text(
                        "For a general unitary U, the transformed outcome map "
                        + "ρ ↦ U*Jₓ(UρU*)U is completely positive and has the "
                        + "standard-basis marginals. Unitary invariance of the "
                        + "depolarizing map and cyclicity of the trace preserve the "
                        + "two marginal conditions. Standard-basis uniqueness and "
                        + "conjugation back by U give Itilde(U,t,x). Conversely the "
                        + "positive Choi formula and its unitary transport establish "
                        + "complete positivity of Itilde, while its channel sum and "
                        + "trace identity give both required marginals. This proves "
                        + "the biconditional, including both endpoints."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("carmeli-heinosaari-toigo-2025-upper-boundary-instrument-uniqueness"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula At(string name, params Formula[] arguments) => At(V(name), arguments);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula PlusOf(Formula left, Formula right) => Parenthesized(Seq(left, Sp, Plus, Sp, right));
    private static Formula MinusOf(Formula left, Formula right) => Parenthesized(Seq(left, Sp, Minus, Sp, right));
    private static Formula TimesOf(Formula left, Formula right) => Parenthesized(Seq(left, Sp, Cdot, Sp, right));
    private static Formula Over(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Square(Formula value) => new Formula.Power(Parenthesized(value), D(2));
    private static Formula Root(Formula value) => Seq(Sqrt, Grp(value));
    private static Formula And(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula ImpliesThat(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, To, Sp, Parenthesized(conclusion));
    private static Formula IffThat(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Iff, Sp, Parenthesized(right));
    private static Formula LeqTo(Formula left, Formula right) => Seq(left, Sp, Leq, Sp, right);
    private static Formula Naturals => Seq(Mathbb, Grp(V("N")));
    private static Formula Reals => Seq(Mathbb, Grp(V("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(V("C")));
    private static Formula Dimension => V("d");
    private static Formula FinD => At("Fin", Dimension);
    private static Formula Matrices => At("Matrix", FinD, FinD, Complexes);
    private static Formula Unitaries => At(Qualified("Matrix", "unitaryGroup"), FinD, Complexes);
    private static Formula Maps => At("MatrixMap", FinD, FinD, Complexes);
    private static Formula RealD => Typed(At(Qualified("Nat", "cast"), Dimension), Reals);
    private static Formula ComplexD => Typed(At(Qualified("Nat", "cast"), Dimension), Complexes);
    private static Formula ToComplex(Formula real) => Typed(At(Qualified("Complex", "ofReal"), real), Complexes);
    private static Formula MatrixU => Typed(V("U"), Matrices);
    private static Formula TraceOf(Formula matrix) => At(Qualified("Matrix", "trace"), matrix);
    private static Formula Sharp => At("Q", V("U"), V("x"));
    private static Formula Alpha => At("a2", Dimension, V("t"));
    private static Formula BetaNoise => At("b", V("t"));

    private static Formula SharpFormula() => All("d", Naturals, All("U", Unitaries, All("x", FinD,
        Equal(Sharp, TimesOf(TimesOf(MatrixU,
            At(Qualified("Matrix", "single"), V("x"), V("x"), Typed(D(1), Complexes))),
            At(Qualified("Matrix", "conjTranspose"), MatrixU))))));

    private static Formula NoisyFormula() => All("d", Naturals, All("U", Unitaries,
        All("s", Reals, All("x", FinD, Equal(At("Qs", V("U"), V("s"), V("x")),
            PlusOf(TimesOf(ToComplex(V("s")), Sharp),
                TimesOf(ToComplex(Over(MinusOf(D(1), V("s")), RealD)), Typed(D(1), Matrices))))))));

    private static Formula ChannelFormula() => All("d", Naturals, All("t", Reals, All("rho", Matrices,
        Equal(At("It", V("t"), V("rho")), PlusOf(TimesOf(ToComplex(V("t")), V("rho")),
            TimesOf(TimesOf(ToComplex(Over(MinusOf(D(1), V("t")), RealD)), TraceOf(V("rho"))),
                Typed(D(1), Matrices)))))));

    private static Formula BoundaryFormula()
    {
        Formula squareD = Square(RealD);
        Formula radicand = PlusOf(PlusOf(TimesOf(MinusOf(D(1), squareD), Square(V("t"))),
            TimesOf(MinusOf(squareD, D(2)), V("t"))), D(1));
        return All("d", Naturals, All("t", Reals, Equal(At("sMax", Dimension, V("t")),
            Over(PlusOf(TimesOf(MinusOf(squareD, D(2)), MinusOf(D(1), V("t"))),
                TimesOf(D(2), Root(radicand))), squareD))));
    }

    private static Formula CoefficientFormula() => All("d", Naturals, All("t", Reals,
        Equal(Alpha, Over(MinusOf(Root(PlusOf(TimesOf(V("t"), MinusOf(Square(RealD), D(1))), D(1))),
            Root(MinusOf(D(1), V("t")))), RealD))));

    private static Formula NoiseRootFormula() => All("t", Reals,
        Equal(BetaNoise, Root(MinusOf(D(1), V("t")))));

    private static Formula InstrumentFormula()
    {
        Formula rightProduct = TimesOf(V("rho"), Sharp);
        Formula leftProduct = TimesOf(Sharp, V("rho"));
        Formula bornTerm = TimesOf(TimesOf(ToComplex(Square(BetaNoise)), TraceOf(rightProduct)), Typed(D(1), Matrices));
        Formula mixedTerm = TimesOf(ToComplex(TimesOf(Alpha, BetaNoise)), PlusOf(rightProduct, leftProduct));
        Formula inputTerm = TimesOf(ToComplex(Square(Alpha)), V("rho"));
        return All("d", Naturals, All("U", Unitaries, All("t", Reals, All("x", FinD, All("rho", Matrices,
            Equal(At("Itilde", V("U"), V("t"), V("x"), V("rho")),
                TimesOf(Over(Typed(D(1), Complexes), ComplexD), PlusOf(PlusOf(bornTerm, mixedTerm), inputTerm))))))));
    }

    private static Formula ClaimBody()
    {
        Formula completePositivity = All("x", FinD,
            At(Qualified("MatrixMap", "IsCompletelyPositive"), At("J", V("x"))));
        Formula channelSum = Equal(
            Parenthesized(Seq(new Formula.Subscript(Sum, Seq(V("x"), Sp, Colon, Sp, FinD)),
                Sp, At("J", V("x")))),
            At("It", V("t")));
        Formula meterTrace = All("x", FinD, All("rho", Matrices,
            Equal(TraceOf(At(At("J", V("x")), V("rho"))), TraceOf(TimesOf(V("rho"),
                At("Qs", V("U"), At("sMax", Dimension, V("t")), V("x")))))));
        Formula unique = All("x", FinD, Equal(At("J", V("x")), At("Itilde", V("U"), V("t"), V("x"))));
        Formula lower = Over(Seq(Minus, D(1)), MinusOf(Square(RealD), D(1)));
        return All("d", Naturals, ImpliesThat(LeqTo(D(2), Dimension),
            All("U", Unitaries, All("t", Reals, ImpliesThat(LeqTo(lower, V("t")),
                ImpliesThat(LeqTo(V("t"), D(1)), All("J", new Formula.TypeArrow(FinD, Maps),
                    IffThat(And(completePositivity, And(channelSum, meterTrace)), unique))))))));
    }
}
