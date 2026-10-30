using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class UnifiedEntropyTriangleRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/UnifiedEntropyTriangleRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/bosyketal2016unifiedcorrelations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A two-qubit density matrix violates the unified-entropy correlation triangle inequality at q = 2 and s = -1.",
        H("A triangle inequality fails for unified-entropy correlations"),
        Blocks(
            Definition("genPurity", "The spectral power trace", PurityFormula(),
                "The generalized purity is the real part of the trace of the real spectral power of σ. "
                    + "For positive semidefinite σ this is the sum of the qth powers of its eigenvalues, "
                    + "the quantity Tr ρ^q in Unifiedarxiv.tex, lines 187–194. "
                    + "The spectral power uses the continuous functional calculus with the real power function. "
                    + "Its total definition also accepts matrices and indices outside the density-matrix setting."),
            Definition("unifiedEntropy", "Unified entropy", EntropyFormula(),
                "This is the unified entropy of Unifiedarxiv.tex, lines 187–194. "
                    + "The source assumes a density matrix and q > 0, q ≠ 1 and s ≠ 0. "
                    + "The displayed function is defined for all real q and s and all complex square matrices; "
                    + "real powers and division use their total real definitions. "
                    + "The limits q = 1 and s = 0 are not defined by taking limits here."),
            Definition("measureA", "An unread measurement on the first factor", MeasureFormula("measureA"),
                "The columns of the unitary u give a complete orthonormal basis on the first factor. "
                    + "For column i, rankOneDensity forms its outer product with its conjugate, "
                    + "and tensoring with the identity on the second factor gives the corresponding projector. "
                    + "The unread state is the sum of projector–state–projector products over all outcomes. "
                    + "This is the first measurement in Unifiedarxiv.tex, lines 371–382. "
                    + "Subtype.val explicitly exposes the complex matrix underlying the unitary."),
            Definition("measureB", "An unread measurement on the second factor", MeasureFormula("measureB"),
                "The columns of the unitary v give the rank-one projectors on the second factor. "
                    + "Tensor each with the identity on the first factor and sum the projector–state–projector "
                    + "products without retaining an outcome. This is the second measurement in "
                    + "Unifiedarxiv.tex, lines 371–385. Subtype.val exposes the matrix underlying v."),
            Definition("measureAB", "Unread measurements on both factors", MeasureFormula("measureAB"),
                "Take the tensor product of each column projector of u with each column projector of v. "
                    + "The outer sum over i and the unread-state sum over j include every pair of local outcomes. "
                    + "This is the bilocal measurement in Unifiedarxiv.tex, lines 374–391. "
                    + "Both unitary-to-matrix coercions are displayed as Subtype.val."),
            Definition("disturbance", "Normalized entropic disturbance", DisturbanceFormula(),
                "Subtract the original entropy from the entropy of σ and divide by the sth power "
                    + "of the original generalized purity. For σ equal to a measured state, this is the "
                    + "disturbance in equation (16), Unifiedarxiv.tex, lines 416–424. "
                    + "The definition itself permits arbitrary σ and ρ."),
            Definition("correlationA", "Correlation from measurements on the first factor", CorrelationFormula("correlationA"),
                "Take the real infimum of the range of disturbances over every unitary basis on the first factor. "
                    + "This expresses the first local correlation of equation (17), Unifiedarxiv.tex, lines 426–433, "
                    + "using an infimum. The definition alone makes no assertion that the infimum is attained."),
            Definition("correlationB", "Correlation from measurements on the second factor", CorrelationFormula("correlationB"),
                "Take the real infimum over every unitary basis on the second factor. "
                    + "This is the infimum form of the second local correlation in equation (17), "
                    + "Unifiedarxiv.tex, lines 426–433."),
            Definition("correlationAB", "Correlation from measurements on both factors", CorrelationFormula("correlationAB"),
                "Take the real infimum over all pairs uv of local unitary bases. "
                    + "The projections Prod.fst and Prod.snd select the two bases from the same pair. "
                    + "This is the infimum form of the bilocal correlation in equation (17), "
                    + "Unifiedarxiv.tex, lines 426–433."),
            Describe.Lean(
                DescribeId.Create("unified-entropy-triangle-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The universal triangle-like inequality"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The proposition asks whether the bilocal correlation is at most the sum of the two "
                        + "unilocal correlations for every q > 0 with q ≠ 1, every s ≠ 0 and every positive "
                        + "trace-one matrix on a product of finite complex coordinate spaces. "
                        + "It interprets equation (38), Unifiedarxiv.tex, lines 697–701, universally over "
                        + "the defined two-parameter entropy family. The question for other entropic measures "
                        + "appears at lines 940–951. The quantified types need only be finite and have decidable "
                        + "equality; they are not separately required to be inhabited. "
                        + "The trace equation is an equality in the complex numbers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unified-entropy-triangle-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A two-qubit counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "On the coordinate basis 00, 01, 10, 11, let ρ₀ be one sixteenth of the real symmetric "
                            + "matrix with rows (6,1,1,0), (1,2,0,1), (1,0,2,1), (0,1,1,6), regarded as a complex matrix. "
                            + "It is Hermitian. For every complex coordinate vector z, sixteen times z*ρ₀z is "
                            + "|z₀₀+z₀₁|² + |z₀₀+z₁₀|² + |z₀₁+z₁₁|² + |z₁₀+z₁₁|² + 4|z₀₀|² + 4|z₁₁|². "
                            + "Each summand is nonnegative, so ρ₀ is positive semidefinite. "
                            + "Its trace is (6+2+2+6)/16 = 1, and its purity is Tr(ρ₀²) = 11/32.")),
                    Paragraph(Text(
                        "For a Hermitian matrix σ the spectral square is the matrix square. "
                            + "At q = 2 and s = -1 the entropy is the inverse purity minus one. "
                            + "For Hermitian σ and ρ with nonzero original purity, the normalized disturbance "
                            + "therefore equals Re Tr(ρ²) / Re Tr(σ²) - 1.")),
                    Paragraph(Text(
                        "For any unitary qubit basis, its first column projector is Hermitian, trace one and idempotent. "
                            + "The Bloch representation consequently expresses it as (I+n·σ)/2 for a real unit vector n. "
                            + "The two column projectors sum to I, so the second projector is the complement of the first. "
                            + "Apply this construction to u and v to obtain unit vectors n and m. "
                            + "Here σ in the Bloch expression denotes the three Pauli matrices. "
                            + "All three measured states are Hermitian: each tensor projector is Hermitian, "
                            + "conjugating the Hermitian state by it preserves Hermiticity, and finite sums preserve Hermiticity.")),
                    Paragraph(Text(
                        "Expand the unread measurements as finite sums of projector–state–projector products. "
                            + "The traces of the squares (the purities) of the first and second measured states are respectively "
                            + "(1 + 1/16 + n(0)²/16 + n(2)²/4)/4 and "
                            + "(1 + 1/16 + m(0)²/16 + m(2)²/4)/4. "
                            + "For the bilocal measurement the trace of the square is "
                            + "(1 + (n(0)²+m(0)²)/16 + n(2)²m(2)²/4)/4. "
                            + "These identities follow by expanding the two outcomes on each factor and using "
                            + "n(2)² = 1-n(0)²-n(1)² and m(2)² = 1-m(0)²-m(1)².")),
                    Paragraph(Text(
                        "The unit-vector identities bound each unilocal purity between 1/4 and 21/64. "
                            + "For the joint term, n(2)² ≤ 1-n(0)² and m(2)² ≤ 1-m(0)² give "
                            + "n(2)²m(2)² ≤ (1-n(0)²)(1-m(0)²). "
                            + "Together with 0 ≤ n(0)² ≤ 1 and 0 ≤ m(0)² ≤ 1, this bounds the bilocal purity "
                            + "between 1/4 and 5/16. Direct evaluation at u = v = I attains both unilocal "
                            + "upper bounds 21/64 and the bilocal upper bound 5/16.")),
                    Paragraph(Text(
                        "Since every measured purity is positive, substituting the upper bounds into "
                            + "(11/32)/Re Tr(σ²)-1 bounds every unilocal disturbance below by 1/21 "
                            + "and every bilocal disturbance below by 1/10. The identity bases attain these lower bounds. "
                            + "Each bound is therefore the least element of its disturbance range, hence its real infimum. "
                            + "Thus correlationA 2 (-1) ρ₀ = correlationB 2 (-1) ρ₀ = 1/21, "
                            + "whereas correlationAB 2 (-1) ρ₀ = 1/10.")),
                    Paragraph(Text(
                        "If the universal proposition held, apply it at q = 2, s = -1, α = β = Fin 2 and ρ = ρ₀. "
                            + "The parameter conditions, positivity and trace-one condition all hold. "
                            + "It would give 1/10 ≤ 1/21 + 1/21, which is false because their difference is 1/210 > 0. "
                            + "The universal proposition is therefore false. This counterexample concerns the "
                            + "nonlimiting unified entropy at (2,-1); it does not assert a classification of other indices."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bosyk-et-al-2016-unified-entropy-triangle-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("unified-entropy-triangle-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula PurityFormula() => SingleBinders(All("q", Reals(),
        All("σ", Mat(Alpha), Equal(LocalCall("genPurity", X("q"), SigmaLower),
            At(Qualified("Complex", "re"), At(Qualified("Matrix", "trace"),
                At(Qualified("D5", "S3", "Quantum", "Matrix", "SpectralPower", "mpow"), SigmaLower, X("q"))))))));

    private static Formula EntropyFormula() => SingleBinders(Indices(All("σ", Mat(Alpha),
        Equal(LocalCall("unifiedEntropy", X("q"), X("s"), SigmaLower),
            new Formula.Fraction(Subtract(PurityPower(SigmaLower), Typed(D(1), Reals())),
                Multiply(Parenthesized(Subtract(Typed(D(1), Reals()), X("q"))), X("s")))))));

    private static Formula MeasureFormula(string name)
    {
        Formula projectorA = At(Qualified("D5", "S3", "Quantum", "PureState", "PureStateHandshake", "rankOneDensity"),
            LambdaOf("a", Alpha, At(Val(X("u"), Alpha), X("a"), X("i"))));
        Formula projectorB = At(Qualified("D5", "S3", "Quantum", "PureState", "PureStateHandshake", "rankOneDensity"),
            LambdaOf("b", Beta, At(Val(X("v"), Beta), X("b"), X("j"))));
        Formula projects = name == "measureA" ? Tensor(projectorA, Typed(D(1), Mat(Beta)))
            : name == "measureB" ? Tensor(Typed(D(1), Mat(Alpha)), projectorB)
            : Tensor(projectorA, projectorB);
        Formula body = At(Qualified("D5", "S3", "Observer", "Conditioning", "unreadState"),
            LambdaOf(name == "measureA" ? "i" : "j", name == "measureA" ? Alpha : Beta, projects), Rho);
        if (name == "measureAB") body = SumOver("i", Alpha, body);
        Formula equation = All("ρ", Mat(PairType(Alpha, Beta)),
            Equal(LocalCall(name, name == "measureB" ? [X("v"), Rho]
                : name == "measureA" ? [X("u"), Rho] : [X("u"), X("v"), Rho]), body));
        if (name != "measureA") equation = All("v", Unitary(Beta), equation);
        if (name != "measureB") equation = All("u", Unitary(Alpha), equation);
        return BipartiteBinders(equation);
    }

    private static Formula DisturbanceFormula() => SingleBinders(Indices(All("σ", Mat(Alpha),
        All("ρ", Mat(Alpha), Equal(LocalCall("disturbance", X("q"), X("s"), SigmaLower, Rho),
            new Formula.Fraction(Subtract(LocalCall("unifiedEntropy", X("q"), X("s"), SigmaLower),
                LocalCall("unifiedEntropy", X("q"), X("s"), Rho)), PurityPower(Rho)))))));

    private static Formula CorrelationFormula(string name)
    {
        string basis = name == "correlationA" ? "u" : name == "correlationB" ? "v" : "uv";
        Formula type = name == "correlationA" ? Unitary(Alpha) : name == "correlationB" ? Unitary(Beta)
            : PairType(Unitary(Alpha), Unitary(Beta));
        Formula measured = name == "correlationAB"
            ? LocalCall("measureAB", At(Qualified("Prod", "fst"), X("uv")), At(Qualified("Prod", "snd"), X("uv")), Rho)
            : LocalCall(name == "correlationA" ? "measureA" : "measureB", X(basis), Rho);
        return BipartiteBinders(Indices(All("ρ", Mat(PairType(Alpha, Beta)),
            Equal(LocalCall(name, X("q"), X("s"), Rho), At(Qualified("InfSet", "sInf"),
                At(Qualified("Set", "range"), LambdaOf(basis, type,
                    LocalCall("disturbance", X("q"), X("s"), measured, Rho))))))));
    }

    private static Formula ClaimFormula()
    {
        Formula inequality = LE(LocalCall("correlationAB", X("q"), X("s"), Rho),
            Add(LocalCall("correlationA", X("q"), X("s"), Rho), LocalCall("correlationB", X("q"), X("s"), Rho)));
        Formula states = BipartiteBinders(All("ρ", Mat(PairType(Alpha, Beta)),
            Arrow(At(Qualified("Matrix", "PosSemidef"), Rho),
                Arrow(Equal(At(Qualified("Matrix", "trace"), Rho), Typed(D(1), Complexes())), inequality))));
        return Equivalence(Local("claim"), Indices(Arrow(LT(Typed(D(0), Reals()), X("q")),
            Arrow(NotEqual(X("q"), Typed(D(1), Reals())), Arrow(NotEqual(X("s"), Typed(D(0), Reals())), states)))));
    }

    private static Formula SingleBinders(Formula body) => All("α", Qualified("Type"), Instances(Alpha, body));
    private static Formula BipartiteBinders(Formula body) => All("α", Qualified("Type"), All("β", Qualified("Type"),
        Instances(Alpha, Instances(Beta, body))));
    private static Formula Instances(Formula type, Formula body) => Seq(
        OpenBracket, At(Qualified("Fintype"), type), CloseBracket, Sp,
        OpenBracket, At(Qualified("DecidableEq"), type), CloseBracket, Comma, Sp, Parenthesized(body));
    private static Formula Indices(Formula body) => All("q", Reals(), All("s", Reals(), body));
    private static Formula PurityPower(Formula matrix) => new Formula.Power(
        Parenthesized(LocalCall("genPurity", X("q"), matrix)), X("s"));
    private static Formula Mat(Formula type) => At(Qualified("Matrix"), type, type, Complexes());
    private static Formula Unitary(Formula type) => At(Qualified("Matrix", "unitaryGroup"), type, Complexes());
    private static Formula Val(Formula unitary, Formula type) => Typed(At(Qualified("Subtype", "val"), unitary), Mat(type));
    private static Formula PairType(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Times, Sp, b));
    private static Formula Tensor(Formula a, Formula b) => At(Qualified("Matrix", "kronecker"), a, b);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula X(string name) => name switch { "α" => Alpha, "β" => Beta, "σ" => SigmaLower, "ρ" => Rho, _ => F.Id(name) };
    private static Formula Local(string name) => Qualified("D5", "S3", "Entropy", "UnifiedEntropyTriangleRefutation", name);
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
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula LT(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Equivalence(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
}
