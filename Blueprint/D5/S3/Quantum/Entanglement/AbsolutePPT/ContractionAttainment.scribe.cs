using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

// Candidate Scribe source. This DSL and its rendering remain uncompiled and unvalidated.
internal sealed class ContractionAttainmentDocument : IScribeDocumentDefinition
{
    private static Formula I(string s) => F.Id(s);
    private static Formula Z(long n) => StrataLint.Scribe.DefinitionDsl.Num(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string s, params Formula[] a) => new Formula.Apply(
        s.Contains('.') ? Seq(I(s.Split('.')[0]), Dot, I(s.Split('.')[1])) : I(s), [.. a]);
    private static Formula All(string s, Formula t, Formula p) =>
        Seq(Forall, Sp, Par(Seq(I(s), Colon, t)), Comma, Sp, p);
    private static Formula Lam(string s, Formula t, Formula p) =>
        Par(Seq(I("fun"), Sp, Par(Seq(I(s), Colon, t)), Sp, Mapsto, Sp, p));
    private static Formula Eq(Formula a, Formula b) => Seq(a, F.Eq, b);
    private static Formula Add(Formula a, Formula b) => Par(Seq(a, Plus, b));
    private static Formula Sub(Formula a, Formula b) => Par(Seq(a, Minus, b));
    private static Formula Mul(Formula a, Formula b) => Par(Seq(a, Cdot, Sp, b));
    private static Formula Smul(Formula a, Formula b) => Call("SMul.smul", a, b);
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula And(params Formula[] xs) => Seq(xs.SelectMany((x,i) =>
        i == 0 ? new[] {Par(x)} : new[] {Land, Sp, Par(x)}).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Rightarrow, Sp, b);
    private static Formula Adj(Formula a) => Call("Matrix.conjTranspose", a);
    private static Formula PSD(Formula a) => Call("Matrix.PosSemidef", a);
    private static Formula Trace(Formula a) => Call("Matrix.trace", a);
    private static Formula Sum(string s, Formula t, Formula p) =>
        Seq(new Formula.Subscript(F.Sum, Seq(I(s), Colon, t)), Sp, p);
    private static Formula R => Seq(Mathbb, Grp(I("R")));
    private static Formula C => Seq(Mathbb, Grp(I("C")));
    private static Formula N => Seq(Mathbb, Grp(I("N")));
    private static Formula J => Par(Seq(I("A"), Times, Sp, I("B")));
    private static Formula Mat(Formula j) => Call("Matrix", j, j, C);
    private static Formula Cast(Formula x, Formula t) => Par(Seq(x, Colon, t));
    private static Formula Coeff => Sub(Cast(Call("Fintype.card", I("A")), C), Z(1));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula FiveJ => Par(Seq(Fin(Z(5)), Times, Sp, Fin(I("n"))));
    private static Formula E => Call("blockUnit", I("a"), I("b"));
    private static Formula Er => Call("blockUnit", I("b"), I("a"));
    private static Formula P => Call("fiveRowProjector", I("n"));
    private static Formula D => Call("fiveRowDensity", I("n"));
    private static Formula Systems(Formula p) => All("A", I("Type"), All("B", I("Type"),
        Seq(OpenBracket, Call("Fintype", I("A")), CloseBracket, Sp,
            OpenBracket, Call("Fintype", I("B")), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", I("A")), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", I("B")), CloseBracket, Sp, p)));
    private static Formula Pair(Formula p) => Systems(All("a", I("A"), All("b", I("A"), p)));
    private static Formula XAll(Formula p) => Systems(All("X", Mat(J), p));
    private static Formula Contraction(Formula p) => XAll(Imp(
        And(PSD(I("X")), PSD(Sub(Z(1), I("X")))), p));
    private static Formula Numerator => Add(Smul(Z(4), Z(1)), Smul(Z(2), P));
    private static Formula KrausDefinition()
    {
        var s = Call("symBlock", I("a"), I("b"));
        var a = Call("antiBlock", I("a"), I("b"));
        return XAll(Eq(Call("krausSum", I("X")), Smul(Frac(Z(1), Z(2)),
            Sum("a", I("A"), Sum("b", I("A"), Add(
                Mul(Mul(s, I("X")), Adj(s)), Mul(Mul(a, Sub(Z(1), I("X"))), Adj(a))))))));
    }
    private static Formula FiveStatement() => All("n", N, Imp(Seq(Z(0), F.Lt, I("n")),
        And(Eq(Call("Matrix.rank", P), Mul(Z(2), I("n"))), PSD(D), Eq(Trace(D), Z(1)),
            Call("APPT", D), Eq(Call("Complex.re", Trace(Mul(D,D))),
                Frac(Z(5), Mul(Z(24), Cast(I("n"), R)))))));
    private static DocumentBlock Desc(string name, string title, Formula statement, string prose,
        DescribeRole role = DescribeRole.Definition) => Describe.Lean(
        DescribeId.Create("appt-contraction-attainment-" + name.ToLowerInvariant().Replace("_", "-")),
        DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment." + name),
        H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive contraction decomposition in arbitrary finite local dimensions supplies a literal five-row APPT attainer.",
        H("Dimension-general APPT contraction attainment"), Blocks(
        Paragraph(Text("A positive contraction yields an APPT operator in arbitrary finite local dimensions. In five rows, a rank-2n coordinate projection gives a normalized state of purity 5/(24n). This is a lower-bound construction; a maximum-purity upper bound is not asserted.")),
        Paragraph(Text("Attribution boundary: the existing ContractionBlocks.separableCone_scalar_add_of_opNorm_le_one theorem gives a stronger separable-cone scalar-shift result for Hermitian Euclidean contractions, and the existing QuadbitMaximumPurity.separableCone_partialTranspose_posSemidef theorem turns that separability into partial-transpose positivity. The Ahiable--Kothakonda--Winter Eq. (31) result and the published Corollary 6.4/Eq. (44) lower-bound and attaining constructions are prior mathematics. This source records the ordered-pair identity and its five-row application without a maximum, uniqueness, or novelty claim; this recovery remains source-only until later validation.")),
        Desc("blockUnit", "Elementary local operator", Pair(Eq(E,
            Call("Matrix.kronecker", Call("Matrix.single", I("a"), I("b"), Cast(Z(1), C)),
                Cast(Z(1), Call("Matrix", I("B"), I("B"), C))))),
            "This is E_ab tensor I_B. Both local index types are arbitrary finite types, including empty types."),
        Desc("symBlock", "Symmetric local operator", Pair(Eq(
            Call("symBlock", I("a"), I("b")), Add(E,Er))),
            "Both orientations are allowed. On the diagonal the operator equals twice E_aa."),
        Desc("antiBlock", "Antisymmetric local operator", Pair(Eq(
            Call("antiBlock", I("a"), I("b")), Sub(E,Er))),
            "On the diagonal the operator is zero; reversing a pair changes its sign."),
        Desc("firstTranspose", "First-subsystem transpose", XAll(Eq(
            Call("firstTranspose", I("X")), Call("Matrix.transpose", Call("partialTranspose", I("X"))))),
            "The project's partialTranspose transposes the second subsystem. Full transpose converts it to first-subsystem transpose, with entry X((k,j),(i,l))."),
        Desc("krausSum", "Positive ordered-pair sum", KrausDefinition(),
            "Each ordered pair has weight one half. Combining the two orientations gives one unordered off-diagonal pair. The diagonal contributes 2 E_aa X E_aa, exactly as in the caller's formula."),
        Desc("kraus_identity", "Dimension-general Kraus identity", XAll(Eq(
            Call("krausSum", I("X")), Add(Smul(Coeff,Z(1)), Smul(Z(2), Call("firstTranspose", I("X")))))),
            "No Hermitian assumption is used. Expanding a pair leaves the two transpose sandwiches and its constant antisymmetric Gram term. Summing matrix units yields (card A minus one) I plus twice firstTranspose X. All subtractions in the coefficient are complex subtraction, not truncated natural subtraction.", DescribeRole.Theorem),
        Desc("partial_transpose_posSemidef", "PSD contraction consequence", Contraction(PSD(
            Add(Smul(Coeff,Z(1)), Smul(Z(2), Call("partialTranspose", I("X")))))),
            "For X PSD and I minus X PSD, every summand is a nonnegative congruence. Taking the full transpose of the Kraus identity gives the project's second-subsystem convention. Zeros, ties and singular contractions are retained. The existing QuadbitMaximumPurity.separableCone_partialTranspose_posSemidef implication is stronger when separability is already available; this declaration supplies the direct PSD-contraction route.", DescribeRole.Theorem),
        Desc("contraction_appt", "All-global-unitary APPT", Contraction(Call("APPT",
            Add(Smul(Coeff,Z(1)),Smul(Z(2),I("X"))))),
            "APPT is the existing literal predicate over every unitary on A times B. For an arbitrary global U, both UXU* and I minus UXU* are PSD by congruence. Apply the preceding theorem to this conjugated contraction. No supplied unitary family replaces the quantifier. For the five-row reflection, the stronger ContractionBlocks separability theorem together with QuadbitMaximumPurity.separableCone_partialTranspose_posSemidef and the existing Ahiable--Kothakonda--Winter Eq. (31) result supplies a prior separability route; this generic APPT consequence is not presented as unique.", DescribeRole.Theorem),
        Desc("fiveRowProjector", "Two-row coordinate projection", All("n", N, Eq(P,
            Call("Matrix.diagonal", Lam("p", FiveJ, Call("ite",
                Seq(Call("Fin.val", Call("Prod.fst", I("p"))), F.Lt, Z(2)), Z(1), Z(0)))))),
            "Exactly the first two of the five rows are selected, for every coordinate of Fin n. The proof establishes idempotence, positivity of both complementary projections, trace 2n and rank 2n."),
        Desc("fiveRowDensity", "Normalized five-row state", All("n", N, Eq(D,
            Smul(Call("Complex.ofReal", Frac(Z(1),Mul(Z(24),Cast(I("n"),R)))), Numerator))),
            "For n positive the denominator 24n is the numerator's trace: 4 times 5n plus 2 times 2n."),
        Desc("five_row_attainment", "Literal five-row attaining family", FiveStatement(),
            "The numerator square is 16 I plus 20 P and has trace 120n. Normalization gives purity 5/(24n). The theorem applies to every positive n, hence to the original n at least five and to its n at least nineteen branch. It proves attainment only. The generic normalized_ray and normalized_basis_diagonal results already cover the other rank-one family and are reused, not duplicated. The published Ahiable--Kothakonda--Winter Corollary 6.4/Eq. (44) already supplies the corresponding lower bound and attainers, so this family is not a new maximum or unique construction. Upper bounds, the physical five-row necessity bridge and classification remain outside this phase.", DescribeRole.Theorem))));
}
