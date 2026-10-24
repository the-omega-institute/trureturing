using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Witness;

internal sealed class MirroredOptimalWitnessSumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/Witness/MirroredOptimalWitnessSum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/seongberahiesmayrchruscinskibae2026mirrored");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct optimal witnesses have an optimal sum and overlapping detection sets.",
        H("Optimal witnesses with an optimal sum"),
        Blocks(
            Definition("is-witness", "IsWitness", "Entanglement witnesses", WitnessFormula(),
                "An entanglement witness A is a Hermitian operator on the tensor product of two "
                    + "d-dimensional complex spaces. It is block positive, meaning that its complex "
                    + "expectation is nonnegative on every product vector, and it has strictly negative "
                    + "real trace pairing with some density matrix ρ. IsDensity means positive "
                    + "semidefinite with trace one. This is the witness notion in mn_revision_clean.tex, "
                    + "lines 276–281, with nonnegativity on separable states expressed as block positivity."),
            Definition("detects", "Detects", "The detection set", DetectsFormula(),
                "Detects A ρ means that ρ is a density matrix and the real part of the trace of Aρ "
                    + "is strictly negative. It expresses membership in the detection set defined in "
                    + "mn_revision_clean.tex, lines 392–396. The predicate itself places no Hermiticity "
                    + "or block positivity condition on A."),
            Definition("is-optimal-witness", "IsOptimalWitness", "Optimality under positive subtraction",
                OptimalFormula(),
                "An optimal witness is an entanglement witness A for which every positive real ε "
                    + "and every nonzero positive semidefinite operator P make A − εP fail block "
                    + "positivity. The real scalar ε is explicitly included in the complex numbers "
                    + "before scalar multiplication. This expresses the absence of a positive "
                    + "subtraction improving a witness in mn_revision_clean.tex, lines 388–396."),
            Definition("claim", "claim", "Two optimal witnesses and an optimal sum",
                IffTo(Call("claim"), ClaimBody()),
                "Generalized mirroring is the relation W + M = K in mn_revision_clean.tex, "
                    + "lines 1688–1696. The question in line 1749 asks whether W, M and K can all "
                    + "be optimal witnesses. The displayed assertion requires such a pair in every "
                    + "local dimension d at least three, together with a state detected only by W, "
                    + "a state detected only by M, and a state detected by both. Thus the two "
                    + "detection sets are incomparable and have nonempty intersection."),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A common spanning family gives an optimal sum"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For a nonzero index r in Fin d, let Aᵣ have four nonzero entries: "
                            + "+1 at (0r,0r) and (r0,r0), and −1 at (00,rr) and (rr,00). "
                            + "Let ψᵣ = (|00⟩ + |rr⟩)/√2. Swapping the two negative entries "
                            + "under conjugate transpose proves that Aᵣ is Hermitian. Its quadratic "
                            + "form at a vector v is |v(0,r)|² + |v(r,0)|² "
                            + "− conjugate(v(0,0))v(r,r) − conjugate(v(r,r))v(0,0). "
                            + "For v = x ⊗ y this equals |x(0)conjugate(y(r)) "
                            + "− x(r)conjugate(y(0))|², proving block positivity.")),
                    Paragraph(Text(
                        "The two distinct coordinate vectors in ψᵣ are orthogonal, so the "
                            + "outer product ψᵣψᵣ* is positive semidefinite with trace one. "
                            + "The rank-one trace identity converts its trace pairing with Aᵣ "
                            + "to the quadratic form above. For any index s this pairing with "
                            + "ψₛψₛ* is −1 if r = s and zero otherwise; the computation uses "
                            + "that the complex image of √2 is nonzero and has square two. "
                            + "The maximally entangled vector Ω = d⁻¹⁄² ∑ᵢ |ii⟩ also defines "
                            + "a density matrix ΩΩ*. Its trace pairing with each Aᵣ is −2/d, "
                            + "using that the complex image of √d is nonzero and has square d.")),
                    Paragraph(Text(
                        "Next the conjugate product vectors x ⊗ conjugate(x) span the whole "
                            + "complex tensor product. To see this, put q(x) = x ⊗ conjugate(x). "
                            + "Polarization gives x ⊗ conjugate(y) = "
                            + "(q(x + y) − q(x) − q(y) + i(q(x + iy) − q(x) − q(y)))/2. "
                            + "Taking x and y to be coordinate vectors therefore puts every "
                            + "coordinate vector |ij⟩ in the span of the q(x). Expanding an "
                            + "arbitrary vector in those coordinate vectors proves the spanning assertion.")),
                    Paragraph(Text(
                        "For any witness A with a spanning set S of zero product vectors, "
                            + "suppose ε > 0, P is positive semidefinite and A − εP is block "
                            + "positive. At each v in S, block positivity gives "
                            + "0 ≤ −ε⟨v,Pv⟩, while positive semidefiniteness gives ⟨v,Pv⟩ ≥ 0. "
                            + "The imaginary part is zero and the real part must vanish. "
                            + "The zero quadratic form criterion for a positive semidefinite "
                            + "matrix then gives Pv = 0. Since S spans, the linear map defined "
                            + "by P is zero, hence P = 0. This excludes every nonzero such P.")),
                    Paragraph(Text(
                        "For each Aᵣ the product expectation vanishes at every "
                            + "q(x) = x ⊗ conjugate(x), since x(0)x(r) − x(r)x(0) = 0. "
                            + "The negative pairing −2/d with ΩΩ* makes Aᵣ a witness, and "
                            + "the spanning zero vectors make it optimal. For nonzero r and s, "
                            + "Aᵣ + Aₛ is Hermitian and block positive by addition, and its "
                            + "pairing with ΩΩ* is −4/d. The same spanning product vectors "
                            + "have zero expectation for the sum, so the sum is optimal as well.")),
                    Paragraph(Text(
                        "If r and s are distinct and nonzero, ψᵣψᵣ* has pairings "
                            + "(−1,0) with (Aᵣ,Aₛ), and ψₛψₛ* has pairings (0,−1). "
                            + "They give a state in each difference of detection sets. "
                            + "The state ΩΩ* has pairing −2/d with both operators and lies "
                            + "in their intersection. Finally, for d ≥ 3 choose r = 1 and "
                            + "s = 2 in Fin d. These indices are nonzero and distinct. "
                            + "Taking W = Aᵣ and M = Aₛ proves all six conjuncts of claim."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("seong-bae-2026-optimal-mirrored-witness-sum"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string id, string declaration, string title,
        Formula formula, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            declaration == "claim" ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula WitnessFormula() => WithOperator(IffTo(Call("IsWitness", X("A")),
        And(Call("IsHermitian", X("A")), And(Call("blockPositive", X("A")),
            Some("ρ", Mat(), And(Call("IsDensity", Rho), NegativeTrace(X("A"), Rho)))))));

    private static Formula DetectsFormula() => All("d", Naturals(), All("A", Mat(), All("ρ", Mat(),
        IffTo(Call("Detects", X("A"), Rho),
            And(Call("IsDensity", Rho), NegativeTrace(X("A"), Rho))))));

    private static Formula OptimalFormula()
    {
        Formula subtraction = Subtract(X("A"),
            Smul(Typed(ComplexOfReal(Varepsilon), Complexes()), X("P")));
        Formula noSubtraction = All("ε", Reals(),
            Imp(Less(Typed(D(0), Reals()), Varepsilon), All("P", Mat(),
                Imp(Call("PosSemidef", X("P")), Imp(NotEqual(X("P"), Typed(D(0), Mat())),
                    Not(Call("blockPositive", subtraction)))))));
        return WithOperator(IffTo(Call("IsOptimalWitness", X("A")),
            And(Call("IsWitness", X("A")), noSubtraction)));
    }

    private static Formula ClaimBody()
    {
        Formula onlyW = Some("ρ", Mat(), And(Call("Detects", X("W"), Rho),
            Not(Call("Detects", X("M"), Rho))));
        Formula onlyM = Some("ρ", Mat(), And(Call("Detects", X("M"), Rho),
            Not(Call("Detects", X("W"), Rho))));
        Formula both = Some("ρ", Mat(), And(Call("Detects", X("W"), Rho),
            Call("Detects", X("M"), Rho)));
        Formula properties = And(Call("IsOptimalWitness", X("W")),
            And(Call("IsOptimalWitness", X("M")),
                And(Call("IsOptimalWitness", Add(X("W"), X("M"))),
                    And(onlyW, And(onlyM, both)))));
        return All("d", Naturals(), Imp(LessEqual(Typed(D(3), Naturals()), X("d")),
            Some("W", Mat(), Some("M", Mat(), properties))));
    }

    private static Formula NegativeTrace(Formula A, Formula ρ) =>
        Less(Call("re", Call("trace", Multiply(A, ρ))), Typed(D(0), Reals()));
    private static Formula WithOperator(Formula body) => All("d", Naturals(), All("A", Mat(), body));
    private static Formula Mat() => Call("Matrix", Index(), Index(), Complexes());
    private static Formula Index() => Parenthesized(Seq(Call("Fin", X("d")), Sp, Times, Sp,
        Call("Fin", X("d"))));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula X(string name) => name switch
    {
        "ρ" => Rho,
        "ε" => Varepsilon,
        _ => F.Id(name),
    };
    private static Formula Call(string name, params Formula[] arguments) =>
        arguments.Length == 0 ? Seq(Operatorname, Grp(F.Id(name)))
            : new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula ComplexOfReal(Formula value) => new Formula.Apply(
        Seq(Operatorname, Grp(Seq(F.Id("Complex"), Dot, F.Id("ofReal")))), [value]);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffTo(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Not(Formula body) => new Formula.Not(Parenthesized(body));
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Smul(Formula scalar, Formula vector) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(vector));
}
