using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class PauliFisherGHZRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Tomography/PauliFisherGHZRefutation";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Estimation/acharyakypraiosguta2016lowranktomography");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "GHZ phase tangents refute a uniform lower bound for mean Pauli Fisher information.",
        H("Pauli Fisher information along a GHZ phase family"),
        Blocks(
            Definition("pauli-eigen", "pauliEigen", "Single-qubit Pauli eigenvectors", PauliEigenFormula(),
                AssessedProvenance.FromLiterature(Source),
                "A setting s in Fin 3 encodes X, Y, Z by 0, 1, 2, respectively. "
                    + "The outcome o in Fin 2 encodes the eigenvalue (−1)^o, and b is a computational-basis coordinate. "
                    + "The chosen eigenvectors fix the phases of the Pauli eigenvectors used in "
                    + "Efficient-Ion-Tomography.tex, lines 114–121."),
            Definition("product-vector", "productVector", "Product measurement vectors", ProductVectorFormula(),
                AssessedProvenance.FromLiterature(Source),
                "For n qubits, s chooses one Pauli basis at each site and o chooses one eigenvector in each basis. "
                    + "The value at the bit string b is the product of the corresponding single-qubit coordinates. "
                    + "The product map takes a constant family of two-element coordinate types and a unit input at each site. "
                    + "This is the tensor-product measurement vector of Efficient-Ion-Tomography.tex, lines 118–121."),
            Definition("outcome-prob", "outcomeProb", "Outcome probabilities", OutcomeProbFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The real readout of ρ in the product measurement vector is the Born probability when ρ is a density matrix. "
                    + "The readout is the real part of the conjugate-vector quadratic form. "
                    + "The definition is also meaningful for arbitrary complex matrices. "
                    + "It expresses equation (1) of Efficient-Ion-Tomography.tex, lines 114–121."),
            Definition("setting-fisher", "settingFisher", "Fisher information of a setting", SettingFisherFormula(),
                AssessedProvenance.FromLiterature(Source),
                "For a state ρ and a matrix direction v, sum the squared real directional readouts divided by "
                    + "the outcome probabilities over all bit-string outcomes. This is the directional quadratic form "
                    + "of the Fisher matrix in Efficient-Ion-Tomography.tex, lines 173–176. "
                    + "Real division assigns zero to a term whose denominator is zero; the definition itself "
                    + "does not require density or tangency assumptions."),
            Definition("average-fisher", "averageFisher", "Mean Fisher information over Pauli settings", AverageFisherFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Take the uniform finite average over every setting s : Fin n → Fin 3. "
                    + "There are 3^n settings, including one empty setting when n is zero. "
                    + "Finite expectation divides the sum by the real cast of the cardinality of the setting set. "
                    + "The average over all Pauli settings is given in Efficient-Ion-Tomography.tex, line 335."),
            Definition("is-rank-tangent", "IsRankTangent", "Tangents represented by curves of fixed rank", IsRankTangentFormula(),
                AssessedProvenance.FromRepo(Source),
                "A matrix v is a rank-r tangent at ρ if a curve γ of complex matrices passes through ρ at zero, "
                    + "has real derivative v there, and is a density matrix of rank r at every real parameter t. "
                    + "Only differentiability at zero is required. This curve formulation expresses the directions "
                    + "used with the local Frobenius metric of Efficient-Ion-Tomography.tex, lines 157–173."),
            Definition("claim", "claim", "A uniform lower bound at each positive rank", ClaimFormula(),
                AssessedProvenance.FromRepo(Source),
                "For each natural rank r at least one, the assertion asks for a positive real c independent of n, ρ and v. "
                    + "Every rank-r density matrix on n qubits and every rank-r tangent must then have mean Pauli Fisher "
                    + "information at least c times the real part of trace(vv). The quantifier over n includes zero. "
                    + "This is a tangent formulation of the conjecture in Efficient-Ion-Tomography.tex, line 360. "
                    + "For a tangent v = Σₐ wₐ ∂ₐρ in local coordinates, trace(v²) = wᵀGw and the directional Fisher "
                    + "form is wᵀĪw, relating the inequality to the normalized minimum eigenvalue in that conjecture."),
            Describe.Lean(
                DescribeId.Create("pauli-fisher-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Rank-one GHZ states violate the uniform lower bound"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For n > 0, let a = 0ⁿ and b = 1ⁿ be the two distinct constant bit strings, "
                            + "with computational-basis vectors |a⟩ and |b⟩. "
                            + "Let E = exp(iθ), ψ = (|a⟩ + E|b⟩)/√2, ρ = |ψ⟩⟨ψ| and "
                            + "V = (i/2)(E|b⟩⟨a| − conjugate(E)|a⟩⟨b|). "
                            + "The identity E conjugate(E) = 1 gives the four nonzero corner entries of ρ. "
                            + "Its diagonal entries at a and b are 1/2, so its trace is one; "
                            + "the outer-product form is positive semidefinite and has rank one. "
                            + "Entrywise differentiation of exp(i(θ+t)) and its conjugate shows that "
                            + "the curve t ↦ ρ(θ+t) has derivative V at zero.")),
                    Paragraph(Text(
                        "Expanding a quadratic form supported on the four corners indexed by a and b "
                            + "expresses its expectation using only the two coordinates u(a) and u(b). "
                            + "For V the expectation is (i/2)(E conjugate(u(b))u(a) − "
                            + "conjugate(E) conjugate(u(a))u(b)). For ρ it is one half of "
                            + "|u(a)|² + |u(b)|² + E conjugate(u(b))u(a) + conjugate(E) conjugate(u(a))u(b). "
                            + "Squaring V gives diagonal entries 1/4 at a and b and zero elsewhere. "
                            + "Thus the real part of trace(V²) is 1/2.")),
                    Paragraph(Text(
                        "If a setting contains Z at some site, each product measurement vector u has "
                            + "u(a) = 0 or u(b) = 0, according to its outcome at that site. "
                            + "The expectation of V is therefore zero for every outcome, "
                            + "and this setting contributes zero Fisher information, including at zero-probability outcomes.")),
                    Paragraph(Text(
                        "For a setting using only X and Y, the single-qubit spectral projectors give "
                            + "|uⱼ(0)|² = |uⱼ(1)|² = 1/2 and "
                            + "conjugate(uⱼ(1))uⱼ(0) = (−1)^(oⱼ)(1 if sⱼ = 0, otherwise −i)/2. "
                            + "Multiplying these identities over the sites gives "
                            + "|u(a)|² = |u(b)|² = 2^(−n) and conjugate(u(b))u(a) = q/2^n, "
                            + "where q = ∏ⱼ (−1)^(oⱼ)(1 if sⱼ = 0, otherwise −i). "
                            + "Consequently the probability is (1 + Re(Eq))/2^n "
                            + "and the directional readout is −Im(Eq)/2^n.")),
                    Paragraph(Text(
                        "Every factor in q has fourth power one, hence q⁴ = 1 and q is one of 1, −1, i, −i. "
                            + "At θ = π/4, both Re(Eq)² and Im(Eq)² equal 1/2. "
                            + "It follows that every X/Y outcome probability is positive. "
                            + "The sum of q over all outcomes factors into the product of the single-site sums; "
                            + "each such sum is zero, and n > 0 supplies a site. Thus Σₒ q = 0. "
                            + "The Fisher summand simplifies to (1 − Re(Eq))/2^n, "
                            + "so summing over the 2^n outcomes gives Fisher information one for every X/Y setting.")),
                    Paragraph(Text(
                        "The indicator that every site uses X or Y factors over sites. "
                            + "Summing it over all settings gives 2^n, since each site allows exactly two choices. "
                            + "Averaging the setting contributions over the 3^n Pauli settings therefore gives (2/3)^n. "
                            + "For every c > 0, geometric decay supplies n > 0 with 2(2/3)^n < c. "
                            + "If the asserted bound held, specialize it to r = 1, this n, the state at θ = π/4, "
                            + "and its phase derivative V. The curve above consists entirely of rank-one density matrices, "
                            + "so V satisfies the tangent condition. The bound would imply c/2 ≤ (2/3)^n, "
                            + "contradicting the chosen n. This disproves the universal assertion already at rank one; "
                            + "it makes no assertion about a lower bound restricted to higher ranks or to random measurement bases."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("acharya-kypraios-guta-2016-pauli-fisher-ghz-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string id, string declaration, string title, Formula formula,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create("pauli-fisher-" + id),
            DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula PauliEigenFormula()
    {
        Formula pauli = At(Qualified("ite"), Equal(X("s"), Typed(D(2), FinOf(D(3)))),
            Pauli("Z"), At(Qualified("ite"), Equal(X("s"), Typed(D(0), FinOf(D(3)))),
                Pauli("X"), Pauli("Y")));
        return All("s", FinOf(D(3)), All("o", FinOf(D(2)), All("b", FinOf(D(2)),
            Equal(Typed(LocalCall("pauliEigen", X("s"), X("o"), X("b")), Complexes()),
                At(Qualified("D5", "S3", "Quantum", "Magic", "WignerDistanceMinimum", "eigenVector"),
                    pauli, X("o"), X("b"))))));
    }

    private static Formula ProductVectorFormula()
    {
        Formula family = Constant(FinOf(X("n")), FinOf(D(2)));
        Formula vectors = LambdaOf("j", FinOf(X("n")), Constant(Qualified("Unit"),
            LocalCall("pauliEigen", At(X("s"), X("j")), At(X("o"), X("j")))));
        Formula units = Constant(FinOf(X("n")), Qualified("Unit", "unit"));
        Formula product = At(Qualified("D5", "S3", "Quantum", "Recovery", "ProductPrefixRigidity", "productMap"),
            family, vectors, units, X("b"));
        return All("n", Naturals(), All("s", Settings(), All("o", Bits(), All("b", Bits(),
            Equal(Typed(LocalCall("productVector", X("s"), X("o"), X("b")), Complexes()), product)))));
    }

    private static Formula OutcomeProbFormula() => All("n", Naturals(), All("ρ", MatrixType(),
        All("s", Settings(), All("o", Bits(),
            Equal(Typed(LocalCall("outcomeProb", Rho, X("s"), X("o")), Reals()),
                Readout(Rho, LocalCall("productVector", X("s"), X("o"))))))));

    private static Formula SettingFisherFormula()
    {
        Formula numerator = new Formula.Power(Readout(X("v"), LocalCall("productVector", X("s"), X("o"))),
            Typed(D(2), Naturals()));
        return MatrixBinders(All("s", Settings(),
            Equal(Typed(LocalCall("settingFisher", Rho, X("v"), X("s")), Reals()),
                SumOver("o", Bits(), new Formula.Fraction(numerator,
                    LocalCall("outcomeProb", Rho, X("s"), X("o")))))));
    }

    private static Formula AverageFisherFormula() => MatrixBinders(
        Equal(Typed(LocalCall("averageFisher", Rho, X("v")), Reals()),
            At(Qualified("Finset", "expect"),
                Typed(Qualified("Finset", "univ"), At(Qualified("Finset"), Settings())),
                LocalCall("settingFisher", Rho, X("v")))));

    private static Formula IsRankTangentFormula()
    {
        Formula gamma = At(GammaLower, X("t"));
        Formula curve = Some("γ", Arrow(Reals(), MatrixType()), Conjunction(
            Equal(At(GammaLower, Typed(D(0), Reals())), Rho), Conjunction(
                At(Qualified("HasDerivAt"), GammaLower, X("v"), Typed(D(0), Reals())),
                All("t", Reals(), Conjunction(Density(gamma), Equal(Rank(gamma), X("r")))))));
        return All("n", Naturals(), All("r", Naturals(), All("ρ", MatrixType(), All("v", MatrixType(),
            Equivalence(LocalCall("IsRankTangent", X("r"), Rho, X("v")), curve)))));
    }

    private static Formula ClaimFormula()
    {
        Formula norm = At(Qualified("Complex", "re"), At(Qualified("Matrix", "trace"),
            Multiply(X("v"), X("v"))));
        Formula bound = MatrixBinders(Arrow(Density(Rho), Arrow(Equal(Rank(Rho), X("r")),
            Arrow(LocalCall("IsRankTangent", X("r"), Rho, X("v")),
                LE(Multiply(X("c"), norm), LocalCall("averageFisher", Rho, X("v")))))));
        return Equivalence(Local("claim"), All("r", Naturals(), Arrow(LE(Typed(D(1), Naturals()), X("r")),
            Some("c", Reals(), Conjunction(LT(Typed(D(0), Reals()), X("c")), bound)))));
    }

    private static Formula MatrixBinders(Formula body) => All("n", Naturals(),
        All("ρ", MatrixType(), All("v", MatrixType(), body)));
    private static Formula Bits() => Arrow(FinOf(X("n")), FinOf(D(2)));
    private static Formula Settings() => Arrow(FinOf(X("n")), FinOf(D(3)));
    private static Formula MatrixType() => At(Qualified("Matrix"), Bits(), Bits(), Complexes());
    private static Formula Readout(Formula matrix, Formula vector) =>
        At(Qualified("D5", "S3", "Quantum", "Recovery", "ProductPrefixRigidity", "readout"), matrix, vector);
    private static Formula Density(Formula matrix) =>
        At(Qualified("D5", "S3", "Quantum", "Information", "SLDSpectralEnergy", "IsDensity"), matrix);
    private static Formula Rank(Formula matrix) => At(Qualified("Matrix", "rank"), matrix);
    private static Formula Pauli(string name) =>
        Qualified("D5", "S3", "Quantum", "Information", "StabilizerPairLocalUnitaryInequivalence", "Pauli", name);
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Quantum", "Tomography", "PauliFisherGHZRefutation", name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula Constant(Formula domain, Formula value) => At(Qualified("Function", "const"), domain, value);
    private static Formula X(string name) => name switch
    {
        "ρ" => Rho,
        "γ" => GammaLower,
        _ => F.Id(name)
    };
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
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
