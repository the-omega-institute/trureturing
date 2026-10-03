using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class ThreeQubitGeometricTangleRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/benedito2025visualizing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A type-4c canonical state on the Bloch-norm diagonal refutes the Benedito–Sierra geometric tangle ansatz.",
        H("Refutation of the geometric tangle ansatz"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("three-qubit-canonical-state"),
                DeclarationHandle.Create(Prefix + "CanonicalState"),
                H("Canonical five-term three-qubit state"),
                StatementSource.FromAuthor(StateFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The paper prints verbatim: “|ψ⟩ overset{CD}{→} |λ₀, λ⃗, λ₄; φ⟩ := [ λ₀|000⟩ + "
                        + "λ₁ e^{iφ}|100⟩ + λ₂|101⟩ + λ₃|110⟩ + λ₄|111⟩ ] where "
                        + "λⱼ ∈ [0,1] ∀ j; Σⱼ₌₀⁴ λⱼ² = 1; φ ∈ [0,π].” (arXiv v2, p. 3, Eqs. (3)–(4)). "
                        + "This is the six-parameter canonical state carrier used below."))),
                DescribeRole.Definition),
            Node("isCanonical", "Canonical parameter conditions", IsCanonicalFormula(),
                "The five amplitudes lie in [0,1], their squares sum to one, and the phase lies in [0,π].",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("amplitudes", "Complex coefficient tensor", AmplitudesFormula(),
                "The eight coefficients are listed in lexicographic qubit order A, B, C. The phase occurs only in the coefficient λ₁ exp(iφ).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("jointDensity", "Pure-state density matrix", JointFormula(),
                "The outer product |ψ⟩⟨ψ| has entries t_ijk conjugate(t_i'j'k') on A × (B × C).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rhoA", "The A marginal", RhoFormula("rhoA", "partialTraceRight", false),
                "Tracing B and C means summing t_ijk conjugate(t_i'jk) over j,k ∈ Fin 2.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rhoB", "The B marginal", RhoFormula("rhoB", "partialTraceRight", true),
                "First trace A, then C: the entries are the sum of t_ijk conjugate(t_ij'k) over i,k ∈ Fin 2.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rhoC", "The C marginal", RhoFormula("rhoC", "partialTraceLeft", true),
                "First trace A, then B: the entries are the sum of t_ijk conjugate(t_ijk') over i,j ∈ Fin 2.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("blochVectors", "Reduced-state Bloch vectors", BlochVectorsFormula(),
                "The frozen bloch map extracts (2 Re ρ₀₁, −2 Im ρ₀₁, Re ρ₀₀ − Re ρ₁₁), the coordinates in ρ = (I + r·σ)/2. For the canonical state, A has y = 2λ₀λ₁ sin φ, while B and C have y = −2λ₁λ₃ sin φ and −2λ₁λ₂ sin φ. The coordinate identities are established inside the refutation.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("cayley", "Cayley hyperdeterminant", CayleyFormula(),
                "The quartic has four square-product terms, six mixed terms with coefficient −2 and two mixed terms with coefficient 4.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("jInvariants", "The five J invariants", JFormula(),
                "Entry k is J_(k+1). These are the Acín invariants cited by the source: J₁ = |λ₁λ₄ exp(iφ) − λ₂λ₃|², J₂ = λ₀²λ₂², J₃ = λ₀²λ₃², J₄ = λ₀²λ₄² and J₅ = λ₀²(J₁ + λ₂²λ₃² − λ₁²λ₄²).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("isGHZ", "The GHZ-class condition", IsGHZFormula(),
                "The GHZ class condition is λ₀ λ₄ ≠ 0.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("isType5", "The type-5 exclusion", IsType5Formula(),
                "Type 5 requires every λⱼ and every Jₖ to be nonzero. The witness has λ₁ = 0, so the full predicate excludes it without evaluating the J invariants.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("blochLengths", "Bloch-norm coordinates", BlochLengthsFormula(),
                "The three coordinates are the Euclidean lengths of the Bloch vectors obtained from the literal reduced density matrices. Each finite sum is the squared Euclidean norm.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("normSquared", "Squared Bloch-vector norm", NormSquaredFormula(),
                "The squared norm of (r_A,r_B,r_C) is the sum of the three squared Bloch lengths.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("V_line", "The main diagonal line", DiagonalLineFormula(),
                "The main diagonal is the range of t ↦ WithLp.toLp 2 ![t,t,t] in EuclideanSpace ℝ (Fin 3).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("euclideanVector", "The Euclidean Bloch-length vector", EuclideanVectorFormula(),
                "The real triple (r_A,r_B,r_C) is embedded as WithLp.toLp 2 ![r_A,r_B,r_C] in EuclideanSpace ℝ (Fin 3), which carries the Euclidean metric.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("distanceToDiagonal", "Distance to the main diagonal", DistanceFormula(),
                "The paper defines d(r⃗,V_line) as the Euclidean distance from r⃗ to the diagonal line. Metric.infDist takes the infimum of the Euclidean distances from euclideanVector(r) to points of V_line.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("tangle", "Canonical three-tangle", TangleFormula(),
                "The paper prints verbatim: “τ(ψ) = 4 |Hdet(t_ijk)| = 4 λ₀² λ₄².” (arXiv v2, p. 5, Eq. (10)). The definition uses the full Cayley quartic of the coefficient tensor. On this canonical family the quartic is λ₀²λ₄²; hence the three-tangle is 4λ₀²λ₄².",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The Benedito–Sierra geometric ansatz", ClaimFormula(),
                "The paper states verbatim: “τ ( r⃗ ) = 1 − |r⃗|²/3 − d( r⃗, V_line ) · 𝓕(r⃗) where |ψ⟩ ∈ GHZ excluding type 5 and 𝓕(r⃗) ≥ 0.” (arXiv v2, p. 7, Eq. (15)). The formal encoding quantifies a nonnegative real function over all normalized canonical states in the GHZ class that are not type 5, with the one-qubit Bloch lengths and diagonal distance defined above.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A type-4c diagonal counterexample", ResultFormula(),
                "For ψ = (|000⟩ + |101⟩ + |110⟩ + |111⟩)/2, the canonical parameters are (1/2,0,1/2,1/2,1/2;0). Its reduced states have Bloch lengths (1/2,1/2,1/2), so the distance to V_line is zero. The ansatz therefore gives 3/4, while τ = 4(1/2)²(1/2)² = 1/4. Hence no nonnegative F can satisfy the universal claim." ,
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("benedito-sierra-2025-geometric-tangle-ansatz-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("three-qubit-geometric-tangle-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula State() => F.Id("CanonicalState");
    private static Formula Vector3() => Prod(Real(), Prod(Real(), Real()));
    private static Formula Prod(Formula left, Formula right) => Call("Prod", left, right);
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Field(Formula ψ, string name) => Call(name, ψ);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Pow(Formula value, byte exponent) =>
        new Formula.Power(value, D(exponent));
    private static Formula Div(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula And(params Formula[] terms) =>
        terms.Reverse().Aggregate((right, left) => new Formula.Logic(left, FormulaLogicOperator.And, right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Sqrt(Formula value) => Call("sqrt", value);
    private static Formula Tuple3(Formula a, Formula b, Formula c) =>
        Parenthesized(Seq(a, Comma, Sp, b, Comma, Sp, c));

    private static Formula IsCanonicalFormula()
    {
        var ψ = F.Id("psi");
        var λ0 = Field(ψ, "lambda0");
        var λ1 = Field(ψ, "lambda1");
        var λ2 = Field(ψ, "lambda2");
        var λ3 = Field(ψ, "lambda3");
        var λ4 = Field(ψ, "lambda4");
        var ranges = And(
            And(Le(D(0), λ0), Le(λ0, D(1))),
            And(Le(D(0), λ1), Le(λ1, D(1))),
            And(Le(D(0), λ2), Le(λ2, D(1))),
            And(Le(D(0), λ3), Le(λ3, D(1))),
            And(Le(D(0), λ4), Le(λ4, D(1))));
        var sum = Add(Add(Add(Add(Pow(λ0, 2), Pow(λ1, 2)), Pow(λ2, 2)), Pow(λ3, 2)), Pow(λ4, 2));
        var body = And(ranges, Eq(sum, D(1)),
            Le(D(0), Field(ψ, "phi")), Le(Field(ψ, "phi"), Pi));
        return Disp(All("psi", State(), Iff(Call("isCanonical", ψ), body)));
    }

    private static Formula IsGHZFormula()
    {
        var ψ = F.Id("psi");
        return Disp(All("psi", State(), Iff(Call("isGHZ", ψ),
            Ne(Mul(Field(ψ, "lambda0"), Field(ψ, "lambda4")), D(0)))));
    }

    private static Formula IsType5Formula()
    {
        var ψ = F.Id("psi");
        var body = And(
            Ne(Field(ψ, "lambda0"), D(0)), Ne(Field(ψ, "lambda1"), D(0)),
            Ne(Field(ψ, "lambda2"), D(0)), Ne(Field(ψ, "lambda3"), D(0)),
            Ne(Field(ψ, "lambda4"), D(0)),
            All("k", Call("Fin", D(5)), Ne(Call("jInvariants", ψ, F.Id("k")), D(0))));
        return Disp(All("psi", State(), Iff(Call("isType5", ψ), body)));
    }

    private static Formula BlochLengthsFormula()
    {
        var ψ = F.Id("psi");
        Formula Length(byte q) => Sqrt(FiniteSum("i", Call("Fin", D(3)),
            Pow(Call("blochVectors", ψ, D(q), F.Id("i")), 2)));
        return Disp(All("psi", State(), Eq(Call("blochLengths", ψ),
            Tuple3(Length(0), Length(1), Length(2)))));
    }

    private static Formula NormSquaredFormula()
    {
        var a = F.Id("rA");
        var b = F.Id("rB");
        var c = F.Id("rC");
        return Disp(All("rA", Real(), All("rB", Real(), All("rC", Real(),
            Eq(Call("normSquared", Tuple3(a, b, c)),
                Add(Add(Pow(a, 2), Pow(b, 2)), Pow(c, 2)))))));
    }

    private static Formula DiagonalLine() => Seq(F.Id("V"), Underscore, Grp(F.Id("line")));
    private static Formula Qualified(string scope, string name) => Seq(F.Id(scope), Dot, F.Id(name));
    private static Formula Apply(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Euclidean() => Call("EuclideanSpace", Real(), Call("Fin", D(3)));
    private static Formula LpVector(Formula a, Formula b, Formula c) =>
        Apply(Qualified("WithLp", "toLp"), D(2),
            Seq(Bang, OpenBracket, a, Comma, Sp, b, Comma, Sp, c, CloseBracket));

    private static Formula DiagonalLineFormula()
    {
        var t = F.Id("t");
        var diagonalMap = Seq(Open, t, Colon, Sp, Real(), Close, Sp, Mapsto, Sp,
            LpVector(t, t, t));
        return Disp(Eq(Seq(DiagonalLine(), Colon, Sp, Call("Set", Euclidean())),
            Apply(Qualified("Set", "range"), diagonalMap)));
    }

    private static Formula EuclideanVectorFormula()
    {
        var ra = F.Id("rA");
        var rb = F.Id("rB");
        var rc = F.Id("rC");
        return Disp(All("rA", Real(), All("rB", Real(), All("rC", Real(),
            Eq(Seq(Call("euclideanVector", Tuple3(ra, rb, rc)), Colon, Sp, Euclidean()),
                LpVector(ra, rb, rc))))));
    }

    private static Formula DistanceFormula()
    {
        var r = F.Id("r");
        return Disp(All("r", Vector3(), Eq(Call("distanceToDiagonal", r),
            Apply(Qualified("Metric", "infDist"), Call("euclideanVector", r), DiagonalLine()))));
    }

    private static Formula TangleFormula()
    {
        var ψ = F.Id("psi");
        return Disp(All("psi", State(), Eq(Call("tangle", ψ),
            Mul(D(4), new Formula.Absolute(Call("cayley", Call("amplitudes", ψ)))))));
    }

    private static Formula StateFormula() => Disp(Eq(State(), Seq(
        OpenBrace, F.Id("lambda0"), Colon, Real(), Comma, Sp,
        F.Id("lambda1"), Colon, Real(), Comma, Sp,
        F.Id("lambda2"), Colon, Real(), Comma, Sp,
        F.Id("lambda3"), Colon, Real(), Comma, Sp,
        F.Id("lambda4"), Colon, Real(), Comma, Sp,
        F.Id("phi"), Colon, Real(), CloseBrace)));

    private static Formula Phase(Formula ψ) =>
        Call("exp", Mul(Field(ψ, "phi"), F.Id("i")));

    private static Formula AmplitudesFormula()
    {
        var ψ = F.Id("psi");
        var terms = new List<Formula>();
        for (byte i = 0; i < 2; i++)
        for (byte j = 0; j < 2; j++)
        for (byte k = 0; k < 2; k++)
        {
            Formula value = i == 0 ? (j == 0 && k == 0 ? Field(ψ, "lambda0") : D(0))
                : j == 0 ? (k == 0 ? Mul(Field(ψ, "lambda1"), Phase(ψ)) : Field(ψ, "lambda2"))
                : k == 0 ? Field(ψ, "lambda3") : Field(ψ, "lambda4");
            terms.Add(Eq(Call("amplitudes", ψ, D(i), D(j), D(k)), value));
        }
        return Disp(All("psi", State(), And([.. terms])));
    }

    private static Formula JointFormula()
    {
        var ψ = F.Id("psi");
        Formula Entry(string a, string b, string c) =>
            Call("amplitudes", ψ, F.Id(a), F.Id(b), F.Id(c));
        Formula Pair(string a, string b, string c) =>
            Parenthesized(Seq(F.Id(a), Comma, Parenthesized(Seq(F.Id(b), Comma, F.Id(c)))));
        var body = Eq(Call("jointDensity", ψ, Pair("a", "b", "c"), Pair("d", "e", "f")),
            Mul(Entry("a", "b", "c"), Call("conj", Entry("d", "e", "f"))));
        foreach (var v in new[] { "f", "e", "d", "c", "b", "a" })
            body = All(v, Call("Fin", D(2)), body);
        return Disp(All("psi", State(), body));
    }

    private static Formula RhoFormula(string name, string trace, bool firstTraceA)
    {
        var ψ = F.Id("psi");
        var joint = Call("jointDensity", ψ);
        var input = firstTraceA ? Call("partialTraceLeft", joint) : joint;
        return Disp(All("psi", State(), Eq(Call(name, ψ), Call(trace, input))));
    }

    private static Formula BlochVectorsFormula()
    {
        var ψ = F.Id("psi");
        return Disp(All("psi", State(), And(
            Eq(Call("blochVectors", ψ, D(0)), Call("bloch", Call("rhoA", ψ))),
            Eq(Call("blochVectors", ψ, D(1)), Call("bloch", Call("rhoB", ψ))),
            Eq(Call("blochVectors", ψ, D(2)), Call("bloch", Call("rhoC", ψ))))));
    }

    private static Formula FiniteSum(string name, Formula domain, Formula term) =>
        Seq(new Formula.Subscript(Sum, Grp(Seq(F.Id(name), Colon, domain))), Parenthesized(term));

    private static Formula CayleyFormula()
    {
        var t = F.Id("t");
        Formula T(byte a, byte b, byte c) => Call("t", D(a), D(b), D(c));
        Formula Product(params Formula[] xs) => xs.Aggregate(Mul);
        Formula Total(params Formula[] xs) => xs.Aggregate(Add);
        var squares = Total(
            Mul(Pow(T(0,0,0),2), Pow(T(1,1,1),2)),
            Mul(Pow(T(0,0,1),2), Pow(T(1,1,0),2)),
            Mul(Pow(T(0,1,0),2), Pow(T(1,0,1),2)),
            Mul(Pow(T(1,0,0),2), Pow(T(0,1,1),2)));
        var mixed = Total(
            Product(T(0,0,0),T(0,0,1),T(1,1,0),T(1,1,1)),
            Product(T(0,0,0),T(0,1,0),T(1,0,1),T(1,1,1)),
            Product(T(0,0,0),T(1,0,0),T(0,1,1),T(1,1,1)),
            Product(T(0,0,1),T(0,1,0),T(1,0,1),T(1,1,0)),
            Product(T(0,0,1),T(1,0,0),T(0,1,1),T(1,1,0)),
            Product(T(0,1,0),T(1,0,0),T(0,1,1),T(1,0,1)));
        var last = Total(Product(T(0,0,0),T(0,1,1),T(1,0,1),T(1,1,0)),
            Product(T(0,0,1),T(0,1,0),T(1,0,0),T(1,1,1)));
        var fin2 = Call("Fin", D(2));
        var complex = Seq(Mathbb, Grp(F.Id("C")));
        return Disp(All("t", Arrow(fin2, Arrow(fin2, Arrow(fin2, complex))),
            Eq(Call("cayley", t), Add(Sub(squares, Mul(D(2), mixed)), Mul(D(4), last)))));
    }

    private static Formula JFormula()
    {
        var ψ = F.Id("psi");
        Formula L(string n) => Field(ψ, n);
        var j1 = Pow(new Formula.Absolute(Sub(Mul(Mul(L("lambda1"), L("lambda4")), Phase(ψ)),
            Mul(L("lambda2"), L("lambda3")))), 2);
        var j5 = Mul(Pow(L("lambda0"), 2),
            Sub(Add(j1, Mul(Pow(L("lambda2"),2), Pow(L("lambda3"),2))),
                Mul(Pow(L("lambda1"),2), Pow(L("lambda4"),2))));
        return Disp(All("psi", State(), And(
            Eq(Call("jInvariants",ψ,D(0)),j1),
            Eq(Call("jInvariants",ψ,D(1)),Mul(Pow(L("lambda0"),2),Pow(L("lambda2"),2))),
            Eq(Call("jInvariants",ψ,D(2)),Mul(Pow(L("lambda0"),2),Pow(L("lambda3"),2))),
            Eq(Call("jInvariants",ψ,D(3)),Mul(Pow(L("lambda0"),2),Pow(L("lambda4"),2))),
            Eq(Call("jInvariants",ψ,D(4)),j5))));
    }

    private static Formula ClaimFormula()
    {
        var ψ = F.Id("psi");
        var r = F.Id("r");
        var f = F.Id("F");
        var admissible = Imp(Call("isCanonical", ψ),
            Imp(Call("isGHZ", ψ),
                Imp(new Formula.Not(Call("isType5", ψ)),
                    Eq(Call("tangle", ψ),
                        Sub(Sub(D(1), Div(Call("normSquared", Call("blochLengths", ψ)), D(3))),
                            Mul(Call("distanceToDiagonal", Call("blochLengths", ψ)),
                                Call("F", Call("blochLengths", ψ))))))));
        var universal = All("psi", State(), admissible);
        var body = Exists("F", Arrow(Vector3(), Real()),
            And(All("r", Vector3(), Le(D(0), Call("F", r))), universal));
        return Disp(Iff(F.Id("claim"), body));
    }

    private static Formula ResultFormula() => Disp(new Formula.Not(F.Id("claim")));
}
