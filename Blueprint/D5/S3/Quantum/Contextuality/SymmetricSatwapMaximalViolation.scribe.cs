using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Contextuality;

internal sealed class SymmetricSatwapMaximalViolationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/hsuetal2026tradingsymmetry");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Identical TW measurements attain the symmetric SATWAP value 2(d−1) on a swap-invariant maximally entangled vector in every dimension d at least two.",
        H("Symmetric SATWAP attainment in every dimension"),
        Blocks(
            Paragraph(Text(
                "Fin d indexes the computational basis from zero to d−1. Both parties use the same measurement function. "
                + "Settings zero and one below correspond respectively to settings one and two in the symmetric SATWAP expression. "
                + "Nat.cast carries a natural number to its displayed target type, Complex.ofReal includes a real scalar in the complex numbers, "
                + "and Fin.val extracts a natural index. WithLp.ofLp and WithLp.toLp change between the Euclidean vector and its coordinate function.")),
            Definition("omega", "omegaPow", "Real powers of the root of unity", OmegaFormula(),
                "The phase is the complex exponential with real exponent t. It extends the root of unity in the source's TeX lines 519–520 "
                + "to the fractional exponents used in line 530. The definition is total also at dimension zero, using division in the complex field.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("tw", "twMatrix", "The TW change of measurement basis", TwFormula(),
                "The diagonal factor T has first entry −1 and every other entry 1. The second factor W has the reciprocal sine entries "
                + "of Eq. (TW), TeX lines 488–495. Their product is the source's U=TW. The sine is evaluated over the reals and then included "
                + "in the complex denominator; each row and column index is first extracted from Fin d and cast to a real number.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("measurement", "measurement", "Identical measurements for the two parties", MeasurementFormula(),
                "Setting zero uses the computational basis projector at outcome a. Setting one conjugates that projector by TW. "
                + "These are the two measurements of Eq. (CGLMP-Opt), TeX lines 488–497; the same matrices are used at either party.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("prob", "prob", "The Born quadratic form", ProbFormula(),
                "Apply the tensor product of the two outcome operators to the coordinate function of ψ, return to Euclidean space, "
                + "and take its inner product with ψ. This is the pure-vector form of Born's rule in Eq. (Born), TeX lines 179–189. "
                + "The function is complex-valued and is defined for every vector, without a normalization assumption.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("correlator", "correlator", "The equal negative-power correlator", CorrelatorFormula(),
                "Sum the outcome quadratic forms with phase ω raised to −k(a+b). This is the case with both exponents equal to −k "
                + "in Eq. (Correlators:d), TeX lines 513–520. The natural index k and the two natural outcome values are cast to the reals "
                + "before forming the phase exponent.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("value", "satwapValue", "The symmetric SATWAP expression", ValueFormula(),
                "The finite sum and the complex coefficient a reproduce Eq. (symSATWAP), TeX lines 523–530, with the stated change of setting labels. "
                + "The first three correlators carry the phase ω raised to −2k; the last carries ω raised to −3k. "
                + "The coefficient is (1−i)ω raised to k/4, divided by two, and starRingEnd is complex conjugation. "
                + "Nat.sub is truncated natural subtraction, so the interval is empty when d is zero or one.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("reduced", "reducedState", "The reduced rank-one operator", ReducedFormula(),
                "Form the rank-one operator of the coordinate function of ψ and trace out its second factor. "
                + "The resulting d by d matrix is the first party's reduced operator. For a unit vector it is a density matrix.",
                AssessedProvenance.FromRepo(Source)),
            Definition("claim", "claim", "Attainment with a symmetric maximally entangled vector",
                Equivalence(Local("claim"), ClaimBody()),
                "For every natural dimension d at least two, one Euclidean vector ψ has norm one, is fixed by exchanging its two indices, "
                + "has reduced operator equal to the identity divided by d, and gives the complex SATWAP value 2(d−1). "
                + "This is the attainment question in the source's TeX line 532, with symmetry as in lines 285–297. "
                + "The reduced-operator identity expresses maximal entanglement of the pure vector.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("symmetric-satwap-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Attainment for every dimension at least two"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix d at least two and write ωᵗ for omegaPow d t. Multiplication adds phase exponents, conjugation negates them, "
                        + "and ω⁰=1. Put α₀=7/8 and α₁=11/8, and let Vₓ have entries ω raised to j(a+αₓ), divided by √d. "
                        + "In Vₓ†Vₓ the offsets cancel. Orthogonality of the finite exponential sum gives d on the diagonal and zero elsewhere, "
                        + "so Vₓ†Vₓ=I.")),
                    Paragraph(Text(
                        "Let D be diagonal with entries ω raised to a/2 and F diagonal with entries −i times ω raised to −(b+1/2)/2. "
                        + "For δ=b−a+1/2 the phase q=ωᵟ satisfies qᵈ=−1, hence q≠1. The geometric sum is therefore −2/(q−1). "
                        + "With θ=(a−b−1/2)π/d, the exponential formula for sine rewrites this as −iω raised to −δ/2, divided by sin θ. "
                        + "The same identity and the nonzero exponential show sin θ≠0. Entrywise multiplication now gives V₀†V₁=DWF.")),
                    Paragraph(Text(
                        "The diagonal matrices D and T are unitary. Thus L=TD†V₀† is unitary and LL†=I. "
                        + "Define ψ at the pair (i,j) to be the sum over m of LᵢₘLⱼₘ, divided by √d. Its coefficient matrix is A=LLᵀ/√d. "
                        + "The matrix LLᵀ is symmetric, so exchanging i and j fixes ψ. Since L and its transpose are unitary, "
                        + "the reduced rank-one operator is AA†=I/d. Taking the trace identifies the squared norm of ψ with one; "
                        + "nonnegativity of the norm gives norm one.")),
                    Paragraph(Text(
                        "Let B₀=I and B₁=TW be the matrices of measurement columns. The diagonal entries of D and F have modulus one, "
                        + "as do all phases ωᵗ. Each outcome operator is consequently the rank-one operator of its column in Bₓ. "
                        + "For G₀=TD† and G₁=F the identities LV₀=B₀G₀ and LV₁=B₁G₁ follow respectively from V₀†V₀=I "
                        + "and V₀†V₁=DWF. Both Gₓ are diagonal unitary, and these identities imply Bₓ†L=GₓVₓ†.")),
                    Paragraph(Text(
                        "The tensor product of the two rank-one outcome operators is again rank one. Its quadratic form is the squared modulus "
                        + "of the overlap with ψ. Writing Q=LLᵀ, that overlap is the (a,b) entry of Bₓ†Q(Bᵧ†)ᵀ, divided by √d. "
                        + "The preceding identities turn this matrix into Gₓ[Vₓ†(Vᵧ†)ᵀ]Gᵧ. Its diagonal phases disappear on taking the norm. "
                        + "Thus, with s=αₓ+αᵧ, the outcome value is d⁻³ times the squared modulus of the sum over j of ω raised to −j(a+b+s).")),
                    Paragraph(Text(
                        "For an integer n, the sum over a from zero to d−1 of ω raised to an is d when d divides n and zero otherwise. "
                        + "Identify Fin d with ZMod d, express the summands using its standard additive character, and apply character orthogonality. "
                        + "Next fix 0≤k<d. For each l, the divisibility condition d divides j−l−k selects exactly j=l+k if l+k<d, "
                        + "and j=l+k−d otherwise. There are d−k indices in the first case and k in the second. "
                        + "The corresponding double sum of ω raised to (j−l)s is (d−k)ω raised to ks plus k times ω raised to (k−d)s.")),
                    Paragraph(Text(
                        "Expand the squared modulus in the outcome value into a sum over j and l, multiply by the correlator phase, "
                        + "and interchange the finite sums. The two sums over outcomes vanish unless d divides j−l−k; when it does, each contributes d. "
                        + "For 1≤k≤d−1 the preceding count therefore gives the correlator as ω raised to ks, multiplied by "
                        + "[(d−k)+kω raised to −ds]/d. The three possible values of s are 7/4, 9/4 and 11/4. "
                        + "Periodicity of the complex exponential gives ω raised to −ds equal to i, −i and i respectively.")),
                    Paragraph(Text(
                        "Substitute these correlators into each summand of satwapValue. The phases cancel because "
                        + "−2k+k/4+7k/4=0, −2k−k/4+9k/4=0 and −3k+k/4+11k/4=0. "
                        + "The two equal-setting terms each have coefficient (1−i)/2 and numerator d−k+ki; the two mixed-setting terms "
                        + "together have coefficient 1+i and numerator d−k−ki. Dividing by d and using i²=−1 gives exactly two. "
                        + "The interval from one to d−1 has d−1 elements, so its sum is 2(d−1). The vector ψ thus satisfies all four required identities."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hsu-et-al-2026-symmetric-satwap-maximal-violation"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string id, string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("symmetric-satwap-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula OmegaFormula() => All("d", N(), All("t", R(),
        Equal(Typed(LocalCall("omegaPow", X("d"), X("t")), C()),
            At(Qualified("Complex", "exp"), Div(
                Multiply(Multiply(Multiply(D(2), RealToComplex(Qualified("Real", "pi"))),
                    Qualified("Complex", "I")), RealToComplex(X("t"))), NatToComplex(X("d")))))));

    private static Formula TwFormula()
    {
        var diagonal = At(Qualified("Matrix", "diagonal"), LambdaOf("i", FinOf(X("d")),
            If(Equal(Val(X("i")), Typed(D(0), N())), new Formula.Negate(Typed(D(1), C())), Typed(D(1), C()))));
        var angle = Div(Multiply(Subtract(Subtract(NatToReal(Val(X("i"))), NatToReal(Val(X("j")))),
            Div(Typed(D(1), R()), D(2))), Qualified("Real", "pi")), NatToReal(X("d")));
        var entries = At(Qualified("Matrix", "of"), LambdaOf("i", FinOf(X("d")), LambdaOf("j", FinOf(X("d")),
            Div(Typed(D(1), C()), Multiply(NatToComplex(X("d")), RealToComplex(At(Qualified("Real", "sin"), angle)))))));
        return All("d", N(), Equal(Typed(LocalCall("twMatrix", X("d")), MatrixType()), Multiply(diagonal, entries)));
    }

    private static Formula MeasurementFormula()
    {
        var projector = At(Qualified("D5", "S3", "Quantum", "Decoherence", "ProjectedUnistochasticDynamics", "basisProjector"), X("a"));
        var tw = LocalCall("twMatrix", X("d"));
        return All("d", N(), All("x", FinOf(D(2)), All("a", FinOf(X("d")),
            Equal(Typed(LocalCall("measurement", X("d"), X("x"), X("a")), MatrixType()),
                If(Equal(X("x"), Typed(D(0), FinOf(D(2)))), projector,
                    Multiply(Multiply(tw, projector), At(Qualified("Matrix", "conjTranspose"), tw)))))));
    }

    private static Formula ProbFormula()
    {
        var product = At(Qualified("Matrix", "kroneckerMap"),
            LambdaOf("x1", C(), LambdaOf("x2", C(), Multiply(X("x1"), X("x2")))),
            LocalCall("measurement", X("d"), X("x"), X("a")),
            LocalCall("measurement", X("d"), X("y"), X("b")));
        var image = At(Qualified("WithLp", "toLp"), D(2),
            At(Qualified("Matrix", "mulVec"), product, At(Qualified("WithLp", "ofLp"), Psi)));
        return All("d", N(), All("ψ", VectorType(), All("x", FinOf(D(2)), All("y", FinOf(D(2)),
            All("a", FinOf(X("d")), All("b", FinOf(X("d")),
                Equal(Typed(LocalCall("prob", X("d"), Psi, X("x"), X("y"), X("a"), X("b")), C()),
                    At(Qualified("Inner", "inner"), C(), Psi, image))))))));
    }

    private static Formula CorrelatorFormula()
    {
        var exponent = new Formula.Negate(Multiply(NatToReal(X("k")),
            Add(NatToReal(Val(X("a"))), NatToReal(Val(X("b"))))));
        var sum = SumOver("a", FinOf(X("d")), SumOver("b", FinOf(X("d")),
            Multiply(LocalCall("omegaPow", X("d"), exponent),
                LocalCall("prob", X("d"), Psi, X("x"), X("y"), X("a"), X("b")))));
        return All("d", N(), All("ψ", VectorType(), All("x", FinOf(D(2)), All("y", FinOf(D(2)), All("k", N(),
            Equal(Typed(LocalCall("correlator", X("d"), Psi, X("x"), X("y"), X("k")), C()), sum))))));
    }

    private static Formula ValueFormula()
    {
        var coefficient = Multiply(Div(Subtract(Typed(D(1), C()), Qualified("Complex", "I")), D(2)),
            LocalCall("omegaPow", X("d"), Div(NatToReal(X("k")), D(4))));
        var conjugate = At(At(Qualified("starRingEnd"), C()), X("a"));
        var first = Multiply(LocalCall("omegaPow", X("d"), Multiply(new Formula.Negate(Typed(D(2), R())), NatToReal(X("k")))),
            Add(Add(Multiply(X("a"), Corr(0, 0)), Multiply(conjugate, Corr(0, 1))), Multiply(conjugate, Corr(1, 0))));
        var last = Multiply(Multiply(LocalCall("omegaPow", X("d"),
            Multiply(new Formula.Negate(Typed(D(3), R())), NatToReal(X("k")))), X("a")), Corr(1, 1));
        var summand = Seq(Qualified("let"), Sp, Typed(X("a"), C()), Sp, Eq, Sp, coefficient,
            Semi, Sp, Parenthesized(Add(first, last)));
        var interval = At(Qualified("Finset", "Icc"), Typed(D(1), N()), At(Qualified("Nat", "sub"), X("d"), D(1)));
        return All("d", N(), All("ψ", VectorType(),
            Equal(Typed(LocalCall("satwapValue", X("d"), Psi), C()), SumIn("k", N(), interval, summand))));
    }

    private static Formula ReducedFormula() => All("d", N(), All("ψ", VectorType(),
        Equal(Typed(LocalCall("reducedState", Psi), MatrixType()),
            At(Qualified("D5", "S3", "Quantum", "Information", "PartialTraceMutualInformation", "partialTraceRight"),
                At(Qualified("D5", "S3", "Quantum", "PureState", "PureStateHandshake", "rankOneDensity"),
                    At(Qualified("WithLp", "ofLp"), Psi))))));

    private static Formula ClaimBody()
    {
        var swap = At(Qualified("LinearIsometryEquiv", "piLpCongrLeft"), D(2), C(), C(),
            At(Qualified("Equiv", "prodComm"), FinOf(X("d")), FinOf(X("d"))), Psi);
        var reduced = Equal(LocalCall("reducedState", Psi),
            Smul(Div(Typed(D(1), C()), NatToComplex(X("d"))), Typed(D(1), MatrixType())));
        var value = Equal(LocalCall("satwapValue", X("d"), Psi),
            Multiply(Typed(D(2), C()), Subtract(NatToComplex(X("d")), Typed(D(1), C()))));
        return All("d", N(), Arrow(LE(Typed(D(2), N()), X("d")), Some("ψ", VectorType(),
            And(Equal(new Formula.Norm(Psi), Typed(D(1), R())),
                And(Equal(swap, Psi), And(reduced, value))))));
    }

    private static Formula Corr(byte x, byte y) => LocalCall("correlator", X("d"), Psi,
        Typed(D(x), FinOf(D(2))), Typed(D(y), FinOf(D(2))), X("k"));
    private static Formula X(string name) => name == "ψ" ? Psi : F.Id(name);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Contextuality", "SymmetricSatwapMaximalViolation", name);
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
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula C() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula d) => At(Qualified("Fin"), d);
    private static Formula MatrixType() => At(Qualified("Matrix"), FinOf(X("d")), FinOf(X("d")), C());
    private static Formula VectorType() => At(Qualified("EuclideanSpace"), C(),
        Parenthesized(Seq(FinOf(X("d")), Sp, Times, Sp, FinOf(X("d")))));
    private static Formula Val(Formula value) => At(Qualified("Fin", "val"), value);
    private static Formula NatToReal(Formula value) => Typed(At(Qualified("Nat", "cast"), value), R());
    private static Formula NatToComplex(Formula value) => Typed(At(Qualified("Nat", "cast"), value), C());
    private static Formula RealToComplex(Formula value) => At(Qualified("Complex", "ofReal"), value);
    private static Formula Div(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula If(Formula condition, Formula yes, Formula no) => At(Qualified("ite"), Parenthesized(condition), yes, no);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula SumIn(string name, Formula type, Formula set, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(Typed(X(name), type), Sp, InMacro, Sp, set)), Sp, Parenthesized(body));
    private static Formula Smul(Formula scalar, Formula vector) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(vector));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
