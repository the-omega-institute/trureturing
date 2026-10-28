using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class DequantumnessPowerStrictGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/DequantumnessPowerStrictGap.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Entropy/songli2022dequantumness");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A translated qubit contraction has strictly greater unrestricted two-state dequantumness power than its restriction to maximally quantum inputs.",
        H("A strict gap between two dequantumness powers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quantumness"),
                DeclarationHandle.Create(Prefix + "quantumness"),
                H("Quantumness of two weighted matrices"),
                StatementSource.FromAuthor(Disp(QuantumnessFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Equation (1) of Song and Li, Section 2 (XML lines 427-480), measures ensemble quantumness by the negative weighted sum of traces of squared commutators. "
                    + "Here the weights are p and 1-p and the matrices are ρ and σ. Matrix products and squares are over the complex numbers, and Complex.re takes the real part after the trace. "
                    + "The expression is defined for every real p and every pair of complex two-by-two matrices; density and probability conditions enter through IsEnsemble below."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dequantumness-power"),
                DeclarationHandle.Create(Prefix + "dequantumnessPower"),
                H("Unrestricted two-state dequantumness power"),
                StatementSource.FromAuthor(Disp(PowerFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "This is D₂ from Section 3 (XML lines 1518-1558 and 2060-2098): take the real supremum of the decrease of quantumness over all two-state qubit ensembles. "
                    + "IsEnsemble requires nonnegative weights summing to one and positive semidefinite matrices of trace one, equivalently 0 ≤ p ≤ 1 with both ρ and σ density matrices. "
                    + "MatrixMap denotes a complex-linear map on the matrix space. This definition accepts every such map; complete positivity and trace preservation are imposed in the equality question."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("max-quantumness"),
                DeclarationHandle.Create(Prefix + "maxQuantumness"),
                H("Maximal initial two-state quantumness"),
                StatementSource.FromAuthor(Disp(MaximumFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The maximal initial quantumness is the real supremum over all two-state qubit ensembles. "
                    + "This specializes the maximal-quantumness condition in Section 3 (XML lines 1559-1700) to two ingredients. Its value is one quarter, attained by equal weights and orthogonal unit Bloch vectors."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("restricted-dequantumness-power"),
                DeclarationHandle.Create(Prefix + "restrictedDequantumnessPower"),
                H("Dequantumness power on maximally quantum inputs"),
                StatementSource.FromAuthor(Disp(RestrictedFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "This is the two-state restriction D₂′ of Section 3 (XML lines 1559-1688). The same loss is optimized only over input ensembles whose quantumness equals maxQuantumness. "
                    + "Both the ensemble condition and the equality to that supremum are required. The supremum is taken in the real numbers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Universal equality for qubit channels"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The assertion is that every completely positive trace-preserving complex-linear qubit map has equal unrestricted and restricted two-state dequantumness powers. "
                    + "At the end of Section 3 (XML lines 4393-4460), Song and Li conjecture that this equality can fail and ask for a strict separation. Thus negating the displayed universal equality establishes the failure they seek."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A qubit map with a strict gap"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For two weights p and 1-p, the ensemble condition is precisely 0 ≤ p ≤ 1 together with positive semidefiniteness and unit trace of ρ and σ. "
                        + "Consider the map φ(X) = X/2 + tr(X) diag(3/4,1/4)/2. On Bloch vectors it will act by the translated contraction f(r) = r/2 + e_z/4, where e_z = (0,0,1).")),
                    Paragraph(Text(
                        "First take orthonormal real three-vectors r and s, and put w = r × s. Then w has squared norm one, and "
                        + "(f(r) × f(s)) · w = 1/4 + (r₂+s₂)/8. Cauchy-Schwarz applied to r+s and e_z gives (r₂+s₂)² ≤ 2, hence r₂+s₂ ≥ −√2. "
                        + "The projection is therefore at least 1/4−√2/8, which is positive because √2 < 2. Applying Cauchy-Schwarz again, now to f(r) × f(s) and w, yields "
                        + "‖f(r) × f(s)‖² ≥ (1/4)(1/2−√2/4)².")),
                    Paragraph(Text(
                        "Every qubit density matrix has the form B(r) = (I+r₀σₓ+r₁σᵧ+r₂σ_z)/2 for a real Bloch vector r of norm at most one, where σₓ, σᵧ and σ_z are the Pauli matrices. "
                        + "Expanding the commutators gives Q = p(1-p)‖r × s‖². Lagrange's identity shows 0 ≤ ‖r × s‖² ≤ 1 whenever r and s lie in the unit ball. "
                        + "A Hermitian idempotent of trace one is a density matrix. Since 0 ≤ p(1-p) ≤ 1/4, every valid two-state ensemble satisfies 0 ≤ Q ≤ 1/4.")),
                    Paragraph(Text(
                        "Equal weights with ρ = diag(1,0) and σ = (1/2)[[1,1],[1,1]] attain Q = 1/4; these matrices are Hermitian idempotents of trace one. "
                        + "The quantumness values form a nonempty set bounded above by 1/4, so their supremum is exactly 1/4. "
                        + "If an ensemble attains it, saturation of p(1-p)‖r × s‖² ≤ 1/4 forces p = 1/2 and ‖r × s‖² = 1. "
                        + "Using ‖r × s‖² = (r·r)(s·s)−(r·s)² with each squared norm at most one then forces r·r = s·s = 1 and r·s = 0.")),
                    Paragraph(Text(
                        "Direct substitution in the Bloch matrix gives φ(B(r)) = B(f(r)). "
                        + "Complete positivity follows from five complex Kraus matrices: (√2/2)I, diag(√6/4,0), (√6/4)E₀₁, (√2/4)E₁₀ and (√2/4)E₁₁. "
                        + "Here Eᵢⱼ has its only nonzero entry, equal to one, at row i and column j, with zero-based indices. "
                        + "Their Kraus sum is φ. Also tr(φ(X)) = tr(X)/2 + tr(X)(3/4+1/4)/2 = tr(X), so φ is trace preserving.")),
                    Paragraph(Text(
                        "Next put q = √145 and take p = 1/2, ρ = (1/34)[[5,q],[q,29]] and σ = (1/34)[[5,−q],[−q,29]]. "
                        + "The identity q² = 145 shows that both matrices are Hermitian idempotents of trace one. They therefore form a valid ensemble, "
                        + "and direct expansion of its quantumness loss under φ gives L = 1329215/5345344.")),
                    Paragraph(Text(
                        "For any ensemble with maximal initial quantumness, the preceding characterization supplies equal weights and orthonormal unit Bloch vectors. "
                        + "The bound for the translated cross product then gives Q(input)−Q(output) ≤ U, where U = (29+2√2)/128.")),
                    Paragraph(Text(
                        "All unrestricted losses are bounded above by 1/4: input quantumness is at most 1/4, and output quantumness is nonnegative by its Bloch expression. "
                        + "The explicit ensemble contributes L to this bounded set, hence L ≤ dequantumnessPower(φ). "
                        + "The restricted loss set is nonempty because an ensemble attaining maximal quantumness exists; every member is at most U, so restrictedDequantumnessPower(φ) ≤ U.")),
                    Paragraph(Text(
                        "Finally √2 is nonnegative, its square is two, and rational comparison of squares gives √2 < 236321/167042. "
                        + "It follows that U < L. If the universal equality held, applying it to the completely positive trace-preserving map φ would identify the two suprema, "
                        + "contradicting L ≤ dequantumnessPower(φ) = restrictedDequantumnessPower(φ) ≤ U < L. "
                        + "Thus this map has strictly greater unrestricted two-state dequantumness power."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("song-li-2022-dequantumness-power-strict-gap"),
                    ResolutionKind.Refuted)))));

    private static Formula QuantumnessFormula()
    {
        Formula weights = Vector2(X("p"), Subtract(Typed(D(1), Reals()), X("p")));
        Formula states = Vector2(X("ρ"), X("σ"));
        Formula commutator = Subtract(
            Multiply(At(states, X("i")), At(states, X("j"))),
            Multiply(At(states, X("j")), At(states, X("i"))));
        Formula realTrace = At(Qualified("Complex", "re"), At(Qualified("Matrix", "trace"),
            new Formula.Power(Parenthesized(commutator), Typed(D(2), Naturals()))));
        Formula summand = Multiply(
            Parenthesized(Multiply(At(weights, X("i")), At(weights, X("j")))), realTrace);
        return All("p", Reals(), All("ρ", MatrixType(), All("σ", MatrixType(),
            Equal(Typed(Q(X("p"), X("ρ"), X("σ")), Reals()),
                new Formula.Negate(Parenthesized(SumOver("i", SumOver("j", summand))))))));
    }

    private static Formula PowerFormula() => All("φ", MapType(),
        Equal(Typed(LocalCall("dequantumnessPower", X("φ")), Reals()),
            At(Qualified("sSup"), Values(Ensembles(Conjunction(Ensemble(),
                Equal(X("x"), Loss())))))));

    private static Formula MaximumFormula() => Equal(Typed(Local("maxQuantumness"), Reals()),
        At(Qualified("sSup"), Values(Ensembles(Conjunction(Ensemble(),
            Equal(X("x"), Q(X("p"), X("ρ"), X("σ"))))))));

    private static Formula RestrictedFormula() => All("φ", MapType(),
        Equal(Typed(LocalCall("restrictedDequantumnessPower", X("φ")), Reals()),
            At(Qualified("sSup"), Values(Ensembles(Conjunction(Ensemble(),
                Conjunction(Equal(Q(X("p"), X("ρ"), X("σ")), Local("maxQuantumness")),
                    Equal(X("x"), Loss()))))))));

    private static Formula ClaimFormula() => Equal(Typed(Local("claim"), Qualified("Prop")),
        Parenthesized(All("φ", MapType(), Arrow(
            At(Qualified("D5", "S3", "QuantumChannels", "CoPRelativeQuantumnessRefutation", "IsCPTP"), X("φ")),
            Equal(LocalCall("dequantumnessPower", X("φ")),
                LocalCall("restrictedDequantumnessPower", X("φ")))))));

    private static Formula Ensemble() => At(Qualified("D5", "S3", "Quantum", "Measurement",
        "AdaptiveQueryQubitFourStateRefutation", "IsEnsemble"),
        Vector2(X("p"), Subtract(Typed(D(1), Reals()), X("p"))), Vector2(X("ρ"), X("σ")));
    private static Formula Loss() => Subtract(Q(X("p"), X("ρ"), X("σ")),
        Q(X("p"), At(X("φ"), X("ρ")), At(X("φ"), X("σ"))));
    private static Formula Q(Formula p, Formula rho, Formula sigma) => LocalCall("quantumness", p, rho, sigma);
    private static Formula Ensembles(Formula body) =>
        Some("p", Reals(), Some("ρ", MatrixType(), Some("σ", MatrixType(), body)));
    private static Formula Values(Formula predicate) =>
        Seq(OpenBrace, Typed(X("x"), Reals()), Sp, Mid, Sp, predicate, CloseBrace);
    private static Formula Vector2(Formula a, Formula b) =>
        Seq(Bang, OpenBracket, a, Comma, Sp, b, CloseBracket);
    private static Formula SumOver(string name, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, FinOf(D(2)))), Sp, Parenthesized(body));
    private static Formula MatrixType() => At(Qualified("Matrix"), FinOf(D(2)), FinOf(D(2)), Complexes());
    private static Formula MapType() => At(Qualified("D5", "S3", "Quantum", "Foundation",
        "FiniteKrausChannel", "PhyslibLeaf", "MatrixMap"), FinOf(D(2)), FinOf(D(2)), Complexes());
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula X(string name) => name switch
    {
        "ρ" => Rho,
        "σ" => SigmaLower,
        "φ" => Varphi,
        _ => F.Id(name),
    };
    private static Formula Local(string name) => Qualified("D5", "S3", "QuantumChannels", "DequantumnessPowerStrictGap", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
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
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
}
