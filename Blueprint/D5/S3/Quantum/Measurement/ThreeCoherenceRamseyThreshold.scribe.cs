using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class ThreeCoherenceRamseyThresholdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/dive2020multilevelcoherence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The greatest third-moment Ramsey ratio for finite mixtures of unit vectors with at most three nonzero coordinates, over all finite dimensions, integer spectra and unit measurement vectors, is an attained algebraic value.",
        H("The exact three-coherence Ramsey threshold"),
        Blocks(
            Node("signal", "signal", "The pure Ramsey signal", SignalFormula(),
                "For integer energy labels n and complex amplitude vectors chi and psi, the signal is p(t) = |Σ_j χ̄_j exp(−i n_j t) ψ_j|². Here chi denotes χ, psi denotes ψ, and i is the imaginary unit. The expressions val(n(j)) : ℂ and val(t) : ℂ are the canonical embeddings ℤ → ℂ and ℝ → ℂ, respectively. With unit vectors this is the probability of the rank-one measurement onto χ after the evolution of ψ. The expression itself is defined for arbitrary vectors. This is the pure-state interference pattern of page 2 with the Hamiltonian of Eq. (1).",
                AssessedProvenance.FromLiterature(Source)),
            Node("mixed-signal", "mixedSignal", "Finite mixtures of pure signals", MixedSignalFormula(),
                "The function is the finite sum Σ_l w_l p_l(t), where p_l(t) = signal n chi (psi l) t. For nonnegative weights summing to one it is the interference pattern of the state Σ_l w_l |ψ_l⟩⟨ψ_l| with the same χ and Hamiltonian throughout. The definition also permits arbitrary real weights. This restates the mixed-state signal in Eq. (2).",
                AssessedProvenance.FromLiterature(Source)),
            Node("moment", "moment", "Moments over one period", MomentFormula(),
                "Write M_q(p) = moment q p. Eq. (2) defines M_q(p) = (1/(2π))∫₀^{2π} p(t)^q dt. The definition has a natural exponent and an arbitrary real function; continuity and positivity are properties of the Ramsey signals used below, rather than assumptions of this definition.",
                AssessedProvenance.FromLiterature(Source)),
            Node("ratio3", "ratio3", "The third-moment ratio", RatioFormula(),
                "Write R₃(p) = ratio3 p. This is M₃(p)/M₁(p)², the case n = 3 of Eq. (3). The quotient is defined for every real function. Only signals with M₁ > 0 enter the set of values to be maximized.",
                AssessedProvenance.FromLiterature(Source)),
            Node("is-three-sparse", "IsThreeSparse", "At most three occupied coordinates", SparseFormula(),
                "The vertical bars on the finite set denote its cardinality. At most three coordinates of ψ are nonzero. By the page-1 definition of k-coherence, mixtures of such vectors are the states that are not four-coherent, as used in the k = 3 row of Table I.",
                AssessedProvenance.FromLiterature(Source)),
            Node("is-unit-vector", "IsUnitVector", "Unit amplitude vectors", UnitFormula(),
                "The squared complex moduli sum to one. This is the normalization of the state and measurement vectors in the interference pattern of Eqs. (1)–(3).",
                AssessedProvenance.FromLiterature(Source)),
            Node("admissible-values", "admissibleValues", "All admissible third-moment ratios", AdmissibleFormula(),
                "The set ranges over every finite dimension d, every finite mixture size L, every integer energy assignment n, every unit measurement vector χ, and every mixture of unit vectors with at most three nonzero coordinates. Its weights are nonnegative and sum to one, and its first moment is positive. Repeated energy labels are allowed. This is the optimization in the k = 3 row of Table I, using Eqs. (1)–(3) and the page-1 definition of coherence. In that table the row k concerns states that are not (k + 1)-coherent.",
                AssessedProvenance.FromLiterature(Source)),
            Node("threshold-n", "thresholdN", "The numerator polynomial", NumeratorFormula(),
                "Write N(r) = thresholdN r. This polynomial is the numerator of the ratio for the equally spaced, symmetric three-level family, extending the optimization of Table I.",
                AssessedProvenance.FromRepo(Source)),
            Node("threshold-d", "thresholdD", "The denominator polynomial", DenominatorFormula(),
                "Write D(r) = thresholdD r. It is positive for r ≥ 0 and is the denominator of the symmetric family's third-moment ratio.",
                AssessedProvenance.FromRepo(Source)),
            Node("threshold-p", "thresholdP", "The stationary-point polynomial", PolynomialFormula(),
                "Write P(r) = thresholdP r. For r ≥ 0, differentiation gives (N/D)′(r) = 4P(r)/((r + 2)³(r² + 2)³). Its root in the stated rational interval determines the exact maximum sought in Table I.",
                AssessedProvenance.FromRepo(Source)),
            Node("claim", "claim", "The attained algebraic maximum", ClaimFormula(),
                "There is an α in (6169/5000, 12339/10000) with P(α) = 0 such that N(α)/D(α) is the greatest element of admissibleValues. Being greatest includes both membership and an upper bound for every member. Table I gives the analytic upper bound 179/96 and a numerical value 1.77 for this row; the present value specifies the attained maximum exactly.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("three-coherence-ramsey-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The sharp threshold is attained"),
                StatementSource.FromAuthor(Disp(Named("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Convexity of x ↦ x³ reduces the mixture bound to pure inputs. Weighting by the first moments gives the bound M₃ ≤ T M₁² for a mixture whenever it holds for each pure signal. Replacing each first moment by M₁ + ε and taking ε down to zero includes components whose first moment vanishes.")),
                    Paragraph(Text("For a pure input put z_j = χ̄_j ψ_j, and combine equal energies into Z_e = Σ_{j:n_j=e} z_j. Cauchy–Schwarz and the unit-vector assumptions give Σ_e |Z_e| ≤ Σ_j |z_j| ≤ 1, with at most three nonzero grouped coefficients. Fourier orthogonality gives M₁ = Σ_e |Z_e|² and M₃ = Σ_h |Σ_{e₁+e₂+e₃=h} Z_{e₁}Z_{e₂}Z_{e₃}|². Taking absolute values and normalizing their sum to one can only increase the ratio; a zero sum gives the zero signal. Thus consider a, b, c ≥ 0 with a + b + c = 1.")),
                    Paragraph(Text("For three distinct ordered energies with gaps x and z, collisions between different cubic monomials occur only when x = z, x = 2z or z = 2x. The inequalities 3a² + 2b² + 3c² ≥ ab and 3a² + 2b² + 3c² ≥ bc show that the equal-spacing case bounds both other collision cases and the case with no extra collision. One or two distinct energies give a ratio at most 5/4.")),
                    Paragraph(Text("At equal spacing put u = a² + b² + c², X = b(a + c) and Y = ac. The ratio is u + 6(X² + Y²)/u + 6X²Y/u². At fixed b, set A = (1 − b)² + b² and B = b²(1 − b)². The same expression is (5/2)u − 3A + (3/2)(A² + 2B)/u + 3AB/u², convex for u > 0. Its feasible interval has endpoints u = b² + (1 − b)²/2 and u = A. The first has a = c; the second has ac = 0 and ratio at most 5/4. In the symmetric case a = c = 1/(r + 2), b = r/(r + 2), the ratio is N(r)/D(r). The case b = 1 has ratio one.")),
                    Paragraph(Text("The intermediate value theorem supplies α in the stated interval with P(α) = 0. Put T = N(α)/D(α). Rational estimates give T > 177/100 > 5/4 and the identity T D(r) − N(r) = (r − α)²Q(r), where Q(r) = (T − 1)r⁴ + (4T + 2α(T − 1))r³ + (8T − 30 + 8αT + 3α²(T − 1))r² + (16T + 16αT − 60α + 12α²T + 4α³(T − 1))r + 20T − 90 + 32αT + (24T − 90)α² + 16Tα³ + 5(T − 1)α⁴. The bounds 123/100 < α < 31/25 and T > 177/100 make all five coefficients positive. Hence Q(r) > 0 for r ≥ 0 and N(r)/D(r) ≤ T.")),
                    Paragraph(Text("For attainment take the energies 0, 1, 2 and ψ = χ with populations (1, α, 1)/(α + 2), namely amplitudes (√(1/(α + 2)), √(α/(α + 2)), √(1/(α + 2))). A single pure component of weight one has positive first moment and ratio T. Thus T belongs to admissibleValues and bounds every admissible value above."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("dive-koukoulekidis-mousafeiris-mintert-2020-three-coherence-ramsey-threshold"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string declaration, string title, Formula formula, string prose,
        AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("three-coherence-ramsey-" + id),
        DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => F.Id(name);
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(V("C")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Vectors(Formula size) => Arrow(Fin(size), Complexes());
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula SetOf(string name, Formula type, Formula body) =>
        Seq(OpenBrace, V(name), Sp, Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula SumFin(string name, Formula size, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(V(name), Sp, Colon, Sp, Fin(size))),
            Sp, Parenthesized(body));

    private static Formula SignalFormula()
    {
        Formula d = V("d"), n = V("n"), chi = V("chi"), psi = V("psi"), t = V("t");
        Formula nj = Parenthesized(Seq(Call("val", At(n, V("j"))), Colon, Sp, Complexes()));
        Formula tc = Parenthesized(Seq(Call("val", t), Colon, Sp, Complexes()));
        Formula phase = At(Exp, new Formula.Negate(
            Multiply(Multiply(nj, tc), Named("i"))));
        Formula amplitude = SumFin("j", d,
            Multiply(Multiply(Seq(Overline, Grp(At(chi, V("j")))), phase), At(psi, V("j"))));
        Formula body = Equal(Call("signal", n, chi, psi, t),
            Power(new Formula.Absolute(amplitude), D(2)));
        return Disp(All("d", Naturals(), All("n", Arrow(Fin(d), Integers()),
            All("chi", Vectors(d), All("psi", Vectors(d), All("t", Reals(), body))))));
    }

    private static Formula MixedSignalFormula()
    {
        Formula d = V("d"), l = V("L"), n = V("n"), chi = V("chi"), psi = V("psi"),
            w = V("w"), t = V("t");
        Formula body = Equal(Call("mixedSignal", n, chi, psi, w, t),
            SumFin("l", l, Multiply(At(w, V("l")),
                Call("signal", n, chi, At(psi, V("l")), t))));
        return Disp(All("d", Naturals(), All("L", Naturals(),
            All("n", Arrow(Fin(d), Integers()), All("chi", Vectors(d),
            All("psi", Arrow(Fin(l), Vectors(d)), All("w", Arrow(Fin(l), Reals()),
            All("t", Reals(), body))))))));
    }

    private static Formula MomentFormula()
    {
        Formula q = V("q"), p = V("p"), period = Multiply(D(2), Pi);
        Formula integral = Seq(Seq(Int, Underscore, Grp(D(0)), Caret, Grp(period)),
            Sp, Power(At(p, V("t")), q), Sp, Mathrm, Grp(V("d")), V("t"));
        return Disp(All("q", Naturals(), All("p", Arrow(Reals(), Reals()),
            Equal(Call("moment", q, p), Multiply(Fraction(D(1), period), integral)))));
    }

    private static Formula RatioFormula()
    {
        Formula p = V("p");
        return Disp(All("p", Arrow(Reals(), Reals()), Equal(Call("ratio3", p),
            Fraction(Call("moment", D(3), p), Power(Call("moment", D(1), p), D(2))))));
    }

    private static Formula SparseFormula()
    {
        Formula d = V("d"), psi = V("psi");
        Formula support = SetOf("j", Fin(d), NotEqual(At(psi, V("j")), D(0)));
        return Disp(All("d", Naturals(), All("psi", Vectors(d),
            Equivalence(Call("IsThreeSparse", psi), AtMost(new Formula.Absolute(support), D(3))))));
    }

    private static Formula UnitFormula()
    {
        Formula d = V("d"), psi = V("psi");
        return Disp(All("d", Naturals(), All("psi", Vectors(d),
            Equivalence(Call("IsUnitVector", psi), Equal(
                SumFin("j", d, Power(new Formula.Absolute(At(psi, V("j"))), D(2))), D(1))))));
    }

    private static Formula AdmissibleFormula()
    {
        Formula d = V("d"), l = V("L"), n = V("n"), chi = V("chi"), psi = V("psi"), w = V("w");
        Formula mixture = Call("mixedSignal", n, chi, psi, w);
        Formula conditions = And(Call("IsUnitVector", chi),
            And(All("l", Fin(l), And(Call("IsUnitVector", At(psi, V("l"))),
                    Call("IsThreeSparse", At(psi, V("l"))))),
            And(All("l", Fin(l), AtMost(D(0), At(w, V("l")))),
            And(Equal(SumFin("l", l, At(w, V("l"))), D(1)),
            And(Less(D(0), Call("moment", D(1), mixture)),
                Equal(V("v"), Call("ratio3", mixture)))))));
        Formula members = Ex("d", Naturals(), Ex("L", Naturals(),
            Ex("n", Arrow(Fin(d), Integers()), Ex("chi", Vectors(d),
            Ex("psi", Arrow(Fin(l), Vectors(d)), Ex("w", Arrow(Fin(l), Reals()), conditions))))));
        return Disp(Equal(Named("admissibleValues"), SetOf("v", Reals(), members)));
    }

    private static Formula NumeratorFormula()
    {
        Formula r = V("r");
        return Disp(All("r", Reals(), Equal(Call("thresholdN", r),
            Add(Add(Add(Power(r, D(6)), Multiply(D(3, 0), Power(r, D(4)))),
                Multiply(D(9, 0), Power(r, D(2)))), D(2, 0)))));
    }

    private static Formula DenominatorFormula()
    {
        Formula r = V("r");
        return Disp(All("r", Reals(), Equal(Call("thresholdD", r),
            Multiply(Power(Add(r, D(2)), D(2)), Power(Add(Power(r, D(2)), D(2)), D(2))))));
    }

    private static Formula PolynomialFormula()
    {
        Formula r = V("r");
        Formula value = Subtract(Add(Subtract(Add(Subtract(Add(
            Subtract(Power(r, D(7)), Multiply(D(1, 3), Power(r, D(6)))),
            Multiply(D(6), Power(r, D(5)))), Multiply(D(6, 0), Power(r, D(4)))),
            Multiply(D(3, 0), Power(r, D(3)))), Multiply(D(3, 0), Power(r, D(2)))),
            Multiply(D(1, 4, 0), r)), D(2, 0));
        return Disp(All("r", Reals(), Equal(Call("thresholdP", r), value)));
    }

    private static Formula ClaimFormula()
    {
        Formula alpha = V("alpha");
        Formula body = Ex("alpha", Reals(),
            And(Less(Fraction(D(6, 1, 6, 9), D(5, 0, 0, 0)), alpha),
            And(Less(alpha, Fraction(D(1, 2, 3, 3, 9), D(1, 0, 0, 0, 0))),
            And(Equal(Call("thresholdP", alpha), D(0)),
                Call("IsGreatest", Named("admissibleValues"),
                    Fraction(Call("thresholdN", alpha), Call("thresholdD", alpha)))))));
        return Disp(Equivalence(Named("claim"), body));
    }
}
