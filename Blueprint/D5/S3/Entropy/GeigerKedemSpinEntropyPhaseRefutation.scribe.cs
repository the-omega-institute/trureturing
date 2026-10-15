using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class GeigerKedemSpinEntropyPhaseRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/geigerkedem2022spinentropy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The spin-one entropy in equations (15)–(18) depends on a relative phase.",
        H("Relative phases can change the Geiger–Kedem spin entropy"), Blocks(
            Paragraph(Text(
                "The spin-one state has three real amplitude magnitudes determined by thetaAlpha "
                    + "and thetaBeta, and two relative phases phaseX and phaseZ. The common global "
                    + "phase cancels from its squared complex modulus. All logarithms are natural.")),
            Node("density", "The polarization-angle density", DensityFormula(),
                "Proposition 2 takes Complex.normSq of the sum of the three amplitudes, "
                    + "with frequencies +2, +1 and -2, and divides by twice Real.pi. "
                    + "Complex.ofReal displays each real-to-complex cast explicitly. The two outer "
                    + "amplitudes are the products of Real.sin thetaAlpha with Real.cos thetaBeta "
                    + "and Real.sin thetaBeta, respectively.",
                AssessedProvenance.FromLiterature(Source)),
            Node("spinEntropy", "The spin-one entropy", SpinEntropyFormula(),
                "Equation (17) adds the differential entropy of the density to the Shannon "
                    + "entropy of the three spin-component probabilities. The intervalIntegral "
                    + "is taken from zero to twice Real.pi with respect to MeasureTheory.volume. "
                    + "The density times its real logarithm is continuous, including at density zero. "
                    + "The qualified Mathlib function Real.binEntropy is defined by "
                    + "p log p⁻¹ + (1 − p) log (1 − p)⁻¹ for every real p.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The phase-independence assertion", ClaimFormula(),
                "Conjecture 1 asserts that equation (17) equals the zero-phase expression (18). "
                    + "Both angles range over Set.Icc zero (Real.pi divided by two), and both "
                    + "relative phases range over Set.Ico zero (twice Real.pi). Equality with the "
                    + "zero-phase value is asserted for every such choice. The Shannon terms in "
                    + "spinEntropy use the qualified Mathlib function Real.binEntropy.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("geiger-kedem-spin-entropy-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A relative phase produces an entropy gap"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Choose thetaAlpha = Real.arctan (Real.sqrt 10) and "
                            + "thetaBeta = Real.arctan (1/3). These angles lie in the required "
                            + "interval and give the three amplitudes (3, 1, 1)/Real.sqrt 11. "
                            + "Set phaseX = 0 and compare phaseZ = 0 with phaseZ = Real.pi.")),
                    Paragraph(Text(
                        "For s equal to 1 or -1, the polynomial 3 + z + s z^4 has real part "
                            + "at least one on the closed unit disc. Its product with its principal "
                            + "complex logarithm has value 3 Real.log 3, first derivative "
                            + "Real.log 3 + 1, and fourth derivative "
                            + "24 s (Real.log 3 + 1) + 2/27 at zero. Cauchy's coefficient formula "
                            + "at orders zero, one and four gives the circle mean of the polynomial's squared "
                            + "modulus as 11, and the circle mean of that squared modulus times "
                            + "the real logarithm of that squared modulus as "
                            + "22 Real.log 3 + 4 + s/162.")),
                    Paragraph(Text(
                        "After division of the polynomial's squared modulus by 22 Real.pi, the integral "
                            + "of the density times its logarithm is "
                            + "2 Real.log 3 + 4/11 + s/1782 - Real.log (22 Real.pi). "
                            + "The Shannon terms agree for the two phases, so the entropy at "
                            + "phaseZ = Real.pi minus the entropy at phaseZ = 0 is 1/891. "
                            + "This nonzero difference contradicts the universal phase-independence assertion."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("geiger-kedem-2022-spin-one-entropy-phase-independence-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("geiger-kedem-spin-entropy-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula DensityFormula()
    {
        Formula first = Multiply(
            ComplexCast(Multiply(RealCall("sin", V("thetaAlpha")), RealCall("cos", V("thetaBeta")))),
            PhaseExponential(Add(V("phaseX"), Multiply(D(2), V("phi")))));
        Formula middle = Multiply(ComplexCast(RealCall("cos", V("thetaAlpha"))),
            PhaseExponential(V("phi")));
        Formula last = Multiply(
            ComplexCast(Multiply(RealCall("sin", V("thetaAlpha")), RealCall("sin", V("thetaBeta")))),
            PhaseExponential(Subtract(V("phaseZ"), Multiply(D(2), V("phi")))));
        return ParameterBinders(All("phi", Reals(),
            Equal(Typed(LocalCall("density", Parameters(V("phi"))), Reals()),
                new Formula.Fraction(At(Qualified("Complex", "normSq"), Add(Add(first, middle), last)),
                    TwoPi()))));
    }

    private static Formula SpinEntropyFormula()
    {
        Formula density = LocalCall("density", Parameters(V("phi")));
        Formula integral = At(Qualified("intervalIntegral"),
            LambdaOf("phi", Reals(), Multiply(density, RealCall("log", density))),
            Typed(D(0), Reals()), TwoPi(), Qualified("MeasureTheory", "volume"));
        Formula shannonAlpha = BinEntropy(Square(RealCall("cos", V("thetaAlpha"))));
        Formula shannonBeta = Multiply(Square(RealCall("sin", V("thetaAlpha"))),
            BinEntropy(Square(RealCall("cos", V("thetaBeta")))));
        return ParameterBinders(Equal(Typed(LocalCall("spinEntropy", Parameters()), Reals()),
            Add(Add(Negate(integral), shannonAlpha), shannonBeta)));
    }

    private static Formula ClaimFormula()
    {
        Formula angles = At(Qualified("Set", "Icc"), Typed(D(0), Reals()),
            new Formula.Fraction(Qualified("Real", "pi"), D(2)));
        Formula phases = At(Qualified("Set", "Ico"), Typed(D(0), Reals()), TwoPi());
        Formula equality = Equal(LocalCall("spinEntropy", Parameters()),
            LocalCall("spinEntropy", V("thetaAlpha"), V("thetaBeta"), D(0), D(0)));
        return Equivalence(Local("claim"), ParameterBinders(
            Imp(Member(V("thetaAlpha"), angles), Imp(Member(V("thetaBeta"), angles),
                Imp(Member(V("phaseX"), phases), Imp(Member(V("phaseZ"), phases), equality))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(V(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Entropy", "GeigerKedemSpinEntropyPhaseRefutation", name);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula RealCall(string name, Formula arg) => At(Qualified("Real", name), arg);
    private static Formula BinEntropy(Formula value) => At(Qualified("Real", "binEntropy"), value);
    private static Formula ComplexCast(Formula value) => At(Qualified("Complex", "ofReal"), value);
    private static Formula PhaseExponential(Formula phase) => At(Qualified("Complex", "exp"),
        Multiply(ComplexCast(phase), Qualified("Complex", "I")));
    private static Formula TwoPi() => Multiply(D(2), Qualified("Real", "pi"));
    private static Formula[] Parameters(params Formula[] extra) =>
        [V("thetaAlpha"), V("thetaBeta"), V("phaseX"), V("phaseZ"), .. extra];
    private static Formula ParameterBinders(Formula body) =>
        All("thetaAlpha", Reals(), All("thetaBeta", Reals(),
            All("phaseX", Reals(), All("phaseZ", Reals(), body))));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Square(Formula value) => new Formula.Power(Parenthesized(value), D(2));
    private static Formula Negate(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
