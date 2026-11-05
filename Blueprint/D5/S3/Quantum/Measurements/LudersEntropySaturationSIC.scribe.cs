using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class LudersEntropySaturationSICDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Measurements/LudersEntropySaturationSIC";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Entropy/debrotastacey2019luders");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Saturation of the Haar-averaged output entropy of a Lüders MIC channel forces a SIC.",
        H("Entropy saturation forces a symmetric informationally complete measurement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("is-mic"),
                DeclarationHandle.Create(Module + ".IsMIC"),
                H("Minimal informational completeness"),
                StatementSource.FromAuthor(Disp(MicDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A MIC consists of d squared positive semidefinite complex matrices summing to the identity, "
                    + "linearly independent over the complex numbers. This is the source's definition in "
                    + "lmc.tex, lines 80–84. The predicate is defined for every natural dimension; "
                    + "positivity of the dimension is imposed in the entropy statement."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("is-sic"),
                DeclarationHandle.Create(Module + ".IsSIC"),
                H("Rank-one equiangular MICs"),
                StatementSource.FromAuthor(Disp(SicDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A SIC is a MIC whose effects are real scalar multiples of Hermitian, idempotent, "
                    + "trace-one matrices, and whose trace inner products have one common diagonal value "
                    + "and one common off-diagonal value. A Hermitian idempotent of trace one is a rank-one "
                    + "orthogonal projector. The scalars are quantified over all real numbers; the MIC "
                    + "conditions force them to be positive. The two common trace values are quantified "
                    + "as complex numbers, as are the traces. This restates lmc.tex, lines 84–90."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typical-entropy"),
                DeclarationHandle.Create(Module + ".typicalEntropy"),
                H("Haar-averaged Lüders output entropy"),
                StatementSource.FromAuthor(Disp(TypicalEntropyDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "The unitary group carries its normalized Haar probability measure, "
                        + "Measure.haarMeasure of the top positive compact set. Conjugating the coordinate "
                        + "projector at zero by a Haar unitary gives the pure input. For a MIC, its output is "
                        + "the unread measurement state with the positive square roots of the effects:")),
                    new DocumentBlock.DisplayFormula(ChannelDefinition()),
                    Paragraph(Text(
                        "This is the Lüders channel of lmc.tex, lines 104–114. Integrating its von Neumann "
                        + "entropy gives the pure-input average used in Theorem 2, lines 385–390. "
                        + "The displayed definition expands the entropy as minus the real part of the trace "
                        + "of the density times its matrix logarithm. CStarMatrix.ofMatrix makes the matrix "
                        + "conversion explicit. To define the function also on families that are not MICs, "
                        + "the conditional uses the coordinate density at zero in that case; its entropy is zero. "
                        + "This extension supplies no additional hypothesis to the saturation implication."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The entropy-saturation conjecture"),
                StatementSource.FromAuthor(Disp(IffOf(Local("claim"), ClaimProposition()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every positive natural dimension and every MIC, equality with the stated "
                    + "Haar-averaged entropy bound implies that a SIC exists in that dimension. "
                    + "This is Conjecture 1 in lmc.tex, lines 416–420, with the Haar average taken over "
                    + "unitary conjugates of the fixed coordinate projector. All logarithms are natural. "
                    + "The premise requires entropy saturation; the conclusion does not assert SIC "
                    + "existence in dimensions where that premise is unavailable."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Entropy saturation forces SIC existence"),
                StatementSource.FromAuthor(Disp(ClaimProposition())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix a positive dimension and a MIC e attaining the entropy value in the premise. "
                        + "For a unitary u let P be the conjugate of the coordinate projector at zero, "
                        + "let Aᵢ be the positive square root of e i, and put ρ = ∑ᵢ Aᵢ P Aᵢ. "
                        + "Thus ρ is Conditioning.unreadState applied to those square roots and P. "
                        + "The projector P is positive, idempotent and has trace one. Positivity of each "
                        + "sandwich and the identity ∑ᵢ Aᵢ² = I make ρ a density matrix. "
                        + "Write S for von Neumann entropy and D for Umegaki relative entropy. "
                        + "Set σₚ = (I + P)/(d + 1), c = 2/(d + 1), and let B be the entropy value in the premise. "
                        + "The density σₚ is strictly positive. Functional calculus on the two eigenspaces "
                        + "of P gives log σₚ = −log(d + 1) I + log 2 P. Expanding relative entropy therefore gives:")),
                    new DocumentBlock.DisplayFormula(EntropyGap()),
                    Paragraph(Text(
                        "Write t for the sum of the squares of the real traces of the Aᵢ, and a for "
                        + "the Haar average of the real trace of Pρ. Apply "
                        + "D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.pure_quadratic to each Aᵢ. "
                        + "Its trace is real and Aᵢ² = e i, so the Haar second moment, summed over the effects, gives:")),
                    new DocumentBlock.DisplayFormula(SecondMoment()),
                    Paragraph(Text(
                        "For a positive matrix A, its squared trace is at least the trace of A². "
                        + "Applied to the Aᵢ, this gives t at least d and a at least c. The equality case "
                        + "also identifies the rank. If A is nonzero and the two traces agree, dividing A "
                        + "by its positive trace produces a mixed state with purity one. By "
                        + "MState.pure_iff_purity_one this state is pure, and MState.pure_mul_self "
                        + "makes its matrix p idempotent. The matrix p is Hermitian and has trace one. "
                        + "Multiplying p by tr A recovers A. Consequently, equality "
                        + "for Aᵢ makes e i a real scalar multiple of such a p. Linear independence "
                        + "of the MIC effects ensures that no Aᵢ is zero.")),
                    Paragraph(Text(
                        "The strong Klein bound supplies nonnegativity and rigidity of relative entropy. "
                        + "Every density matrix is bounded above by I, and strict positivity of σₚ "
                        + "supplies the support condition. The bound with spectral ceiling one is:")),
                    new DocumentBlock.DisplayFormula(StrongKlein()),
                    Paragraph(Text(
                        "The output and its entropy are continuous in u; continuity of the entropy follows "
                        + "from continuity of x log x, including at zero. The entropy-gap identity then "
                        + "also makes the relative entropy continuous. Compactness of the unitary group "
                        + "makes these functions integrable. Integrate the entropy-gap identity. "
                        + "Saturation gives zero as the sum of the nonnegative average relative entropy "
                        + "and (a − c) log 2. Since log 2 is positive, a = c, t = d, and the relative "
                        + "entropy is zero almost everywhere. The nonnegative individual trace gaps "
                        + "sum to zero, so each vanishes. The rank argument above therefore makes every "
                        + "effect rank one.")),
                    Paragraph(Text(
                        "Where the relative entropy is zero, the strong Klein bound forces the "
                        + "Hilbert–Schmidt square of ρ − σₚ to vanish, hence ρ = σₚ. Both sides "
                        + "are continuous functions of u, and normalized Haar measure gives positive "
                        + "measure to every nonempty open set. Their almost-everywhere equality thus "
                        + "holds everywhere.")),
                    Paragraph(Text(
                        "The Lüders map and the following depolarizing map are complex linear. "
                        + "They agree on every unitary conjugate of the coordinate projector at zero. "
                        + "Permutation unitaries give agreement for each coordinate projector; spectral "
                        + "decomposition then gives agreement on every Hermitian matrix. Decomposing "
                        + "an arbitrary complex matrix into its Hermitian real and imaginary parts gives:")),
                    new DocumentBlock.DisplayFormula(DepolarizingIdentity()),
                    Paragraph(Text(
                        "Choose the rank-one representation e i = c i · p i obtained above. Taking "
                        + "traces gives c i nonnegative. Each p i is positive, and the square root "
                        + "of e i is sqrt(c i) · p i. The trace-one projector sandwich identity "
                        + "p i · x · p i = tr(p i · x) · p i therefore writes the Lüders output "
                        + "as ∑ᵢ tr(p i · x) · e i. Apply the depolarizing identity with x = e j, "
                        + "replace I by ∑ᵢ e i, and compare coefficients in the linearly independent "
                        + "family e:")),
                    new DocumentBlock.DisplayFormula(CoefficientIdentity()),
                    Paragraph(Text(
                        "At i = j, idempotence and trace one give c j = (1 + c j)/(d + 1), "
                        + "so c j = 1/d. Substituting these weights back gives the two trace values:")),
                    new DocumentBlock.DisplayFormula(SicTraceValues()),
                    Paragraph(Text(
                        "The original MIC is therefore rank one and equiangular. It satisfies IsSIC, "
                        + "and choosing f = e proves the existential conclusion."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("debrota-stacey-2019-luders-entropy-saturation-sic"),
                    ResolutionKind.Proved)))));

    private static Formula MicDefinition() => OverEffects(IffOf(LocalCall("IsMIC", X("d"), X("e")),
        And(All("i", Outcomes(), At(Qualified("Matrix", "PosSemidef"), Effect(X("i")))),
            And(Equal(SumOver("i", Outcomes(), Effect(X("i"))), OneMatrix()),
                At(Qualified("LinearIndependent"), Complexes(), X("e"))))));

    private static Formula SicDefinition()
    {
        Formula p = X("p");
        Formula rankOne = All("i", Outcomes(), Some("c", Reals(), Some("p", Matrices(),
            And(At(Qualified("Matrix", "IsHermitian"), p),
                And(Equal(Multiply(p, p), p),
                    And(Equal(Trace(p), Typed(D(1), Complexes())),
                        Equal(Effect(X("i")), Smul(ComplexOfReal(X("c")), p))))))));
        Formula equiangular = Some("a", Complexes(), Some("b", Complexes(),
            All("i", Outcomes(), All("j", Outcomes(),
                Equal(Trace(Multiply(Effect(X("i")), Effect(X("j")))),
                    If(Equal(X("i"), X("j")), X("a"), X("b")))))));
        return OverEffects(IffOf(LocalCall("IsSIC", X("d"), X("e")),
            And(LocalCall("IsMIC", X("d"), X("e")), And(rankOne, equiangular))));
    }

    private static Formula TypicalEntropyDefinition() => OverPositiveEffects(
        Equal(LocalCall("typicalEntropy", X("d"), X("e")),
            Integral(EntropyOfMatrix(If(LocalCall("IsMIC", X("d"), X("e")),
                Channel(PureInput()), At(Qualified("Matrix", "diagonal"),
                    LambdaOf("j", FinOf(X("d")), If(Equal(X("j"), Typed(D(0), FinOf(X("d")))),
                        Typed(D(1), Complexes()), Typed(D(0), Complexes())))))))));

    private static Formula ClaimProposition() => OverPositiveEffects(
        Imp(LocalCall("IsMIC", X("d"), X("e")),
            Imp(Equal(LocalCall("typicalEntropy", X("d"), X("e")), EntropyBound()),
                Some("f", Effects(), LocalCall("IsSIC", X("d"), X("f"))))));

    private static Formula EntropyBound() => Subtract(
        At(Qualified("Real", "log"), Add(NatCast(Reals()), D(1))),
        Multiply(Div(D(2), Add(NatCast(Reals()), D(1))), At(Qualified("Real", "log"), D(2))));

    private static Formula ChannelDefinition() => OverPositiveEffects(All("x", Matrices(),
        Equal(At(Qualified("D5", "S3", "Observer", "Conditioning", "unreadState"),
            LambdaOf("i", Outcomes(), SquareRoot(Effect(X("i")))), X("x")), Channel(X("x")))));

    private static Formula Channel(Formula x) => SumOver("i", Outcomes(),
        Multiply(Multiply(SquareRoot(Effect(X("i"))), x), SquareRoot(Effect(X("i")))));

    private static Formula PureInput()
    {
        Formula u = Seq(X("u"), Dot, D(1));
        return Multiply(Multiply(u, At(Qualified("Matrix", "single"),
                Typed(D(0), FinOf(X("d"))), Typed(D(0), FinOf(X("d"))), Typed(D(1), Complexes()))),
            At(Qualified("Matrix", "conjTranspose"), u));
    }

    private static Formula EntropyOfMatrix(Formula matrix)
    {
        Formula density = At(Qualified("CStarMatrix", "ofMatrix"), matrix);
        return new Formula.Negate(RealPart(Trace(Multiply(density, At(Qualified("CFC", "log"), density)))));
    }

    private static Formula Integral(Formula integrand) => Seq(
        new Formula.Subscript(Int, Typed(X("u"), Unitaries())), Sp, Parenthesized(integrand),
        Sp, Mathrm, Grp(F.Id("d")), Sp, At(Qualified("MeasureTheory", "Measure", "haarMeasure"),
            Typed(Qualified("Top", "top"), At(Qualified("TopologicalSpace", "PositiveCompacts"), Unitaries()))));

    private static Formula EntropyGap() => Equal(Subtract(X("B"), At(X("S"), Rho)),
        Add(At(X("D"), Rho, new Formula.Subscript(SigmaLower, X("P"))),
            Multiply(Parenthesized(Subtract(RealPart(Trace(Multiply(X("P"), Rho))), X("c"))),
                At(Qualified("Real", "log"), D(2)))));

    private static Formula SecondMoment() => Equal(X("a"),
        Div(Add(X("t"), NatCast(Reals())), Multiply(NatCast(Reals()), Parenthesized(Add(NatCast(Reals()), D(1))))));

    private static Formula StrongKlein()
    {
        Formula difference = Parenthesized(Subtract(Rho, new Formula.Subscript(SigmaLower, X("P"))));
        return new Formula.Relation(Div(RealPart(Trace(Multiply(
                At(Qualified("Matrix", "conjTranspose"), difference), difference))), D(2)),
            FormulaRelationOperator.LessThanOrEqual, At(X("D"), Rho, new Formula.Subscript(SigmaLower, X("P"))));
    }

    private static Formula DepolarizingIdentity() => All("x", Matrices(), Equal(Channel(X("x")),
        Smul(Div(D(1), Add(NatCast(Complexes()), D(1))), Add(X("x"), Smul(Trace(X("x")), OneMatrix())))));

    private static Formula CoefficientIdentity() => All("j", Outcomes(), All("i", Outcomes(),
        Equal(Trace(Multiply(At(X("p"), X("i")), Effect(X("j")))),
            Multiply(Div(D(1), Add(NatCast(Complexes()), D(1))),
                Parenthesized(Add(If(Equal(X("i"), X("j")), Typed(D(1), Complexes()), Typed(D(0), Complexes())),
                    ComplexOfReal(At(X("c"), X("j")))))))));

    private static Formula SicTraceValues() => All("i", Outcomes(), All("j", Outcomes(),
        Equal(Trace(Multiply(Effect(X("i")), Effect(X("j")))), If(Equal(X("i"), X("j")),
            new Formula.Power(Parenthesized(Div(D(1), NatCast(Complexes()))), D(2)),
            Div(new Formula.Power(Parenthesized(Div(D(1), NatCast(Complexes()))), D(2)),
                Add(NatCast(Complexes()), D(1)))))));

    private static Formula OverEffects(Formula body) => All("d", Naturals(), All("e", Effects(), body));
    private static Formula OverPositiveEffects(Formula body) => All("d", Naturals(),
        Imp(At(Qualified("NeZero"), X("d")), All("e", Effects(), body)));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Outcomes() => FinOf(new Formula.Power(X("d"), D(2)));
    private static Formula Matrices() => At(Qualified("Matrix"), FinOf(X("d")), FinOf(X("d")), Complexes());
    private static Formula Effects() => new Formula.TypeArrow(Outcomes(), Matrices());
    private static Formula Unitaries() => At(Qualified("Matrix", "unitaryGroup"), FinOf(X("d")), Complexes());
    private static Formula OneMatrix() => Typed(D(1), Matrices());
    private static Formula Effect(Formula i) => At(X("e"), i);
    private static Formula SquareRoot(Formula x) => Seq(Sqrt, Grp(x));
    private static Formula Trace(Formula x) => At(Qualified("Matrix", "trace"), x);
    private static Formula RealPart(Formula x) => At(Qualified("Complex", "re"), x);
    private static Formula ComplexOfReal(Formula x) => At(Qualified("Complex", "ofReal"), x);
    private static Formula NatCast(Formula type) => Typed(At(Qualified("Nat", "cast"), X("d")), type);
    private static Formula Div(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula If(Formula condition, Formula yes, Formula no) => At(Qualified("ite"), condition, yes, no);
    private static Formula Smul(Formula scalar, Formula vector) => Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(vector));
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.TypeArrow(Parenthesized(left), Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) => Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula X(string name) => F.Id(name);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Measurements", "LudersEntropySaturationSIC", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
}
