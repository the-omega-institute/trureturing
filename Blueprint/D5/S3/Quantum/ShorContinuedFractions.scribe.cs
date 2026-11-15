using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;
internal sealed class ShorContinuedFractionsDocument : IScribeDocumentDefinition
{
    private static Formula Q() => Pow(Num(2), X("n"));
    private static Formula R() => C("period", X("c"));
    private static Formula Fraction() => C("reduced", C("val", X("s")), R());
    private static Formula Candidates() => C("candidates", C("val", X("y")), Q(), C("modulus", X("c")));
    private static Formula Near() => C("Nearest", Q(), Div(C("val", X("s")), R()), X("y"));
    private static Formula Size() => Rel(Pow(C("modulus", X("c")), Num(2)), FormulaRelationOperator.LessThanOrEqual, Q());
    private static Formula Quantify(Formula f) => All(f, ("c", X("Parameters")), ("n", X("Nat")),
        ("s", C("Fin", R())), ("y", C("Fin", Q())));
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional continued-fraction membership for actual modular phase estimation",
        H("Conditional Shor candidate membership"), Blocks(
            Paragraph(Text("Parameters is the actual padded modular-multiplication model: modulus N at least two, base coprime to N, and an independently chosen target width whose dimension holds the residues. The counting width n gives Q equal to two to the n. The true order r is positive and strictly smaller than N. The candidate algorithm takes only y.val, Q and N; s and r occur in the theorem's conditions, not as algorithm inputs.")),
            Describe.Lean(DescribeId.Create("nearest-reduced-candidate"),
                DeclarationHandle.Create("D5/S3/Quantum/ShorContinuedFractions.shor_nearest_candidate"), H("Reduced phase candidate"),
                StatementSource.FromAuthor(Disp(Quantify(Imp(Size(), Imp(Near(), new Formula.Logic(
                    Rel(Fraction(), FormulaRelationOperator.MemberOf, Candidates()), FormulaLogicOperator.And,
                    C("Dvd", C("den", Fraction()), R()))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HilbertOperators/aicyberg2026shor")),
                Blocks(Paragraph(Text("For every c, n, hsize : N squared at most Q, s : Fin r and y : Fin Q, the hypothesis is the existing circular Nearest Q (s.val / r) y. The conclusion places the distinguished reduced s/r in candidates and says that this fraction's denominator divides r. Its denominator is exactly r divided by gcd(s.val,r), by the generic rational denominator formula. No assertion is made that every list entry divides the order.")),
                    Paragraph(Text("Nearest means that some integer z makes the absolute difference s.val/r minus y.val/Q minus z at most 1/(2Q). Since s.val is below r, y.val is below Q and r is below N, the resolution N squared at most Q excludes nonzero z. This includes s equal to zero and either non-strict rounding tie. The reduced denominator is at most r and its square is strictly below Q, converting the non-strict grid error into the strict Legendre bound. Mathlib's existing Legendre theorem supplies a real-convergent index. The exact finite-list correspondence supplies membership, and the denominator bound passes the observable filter."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coprime-order-candidate"),
                DeclarationHandle.Create("D5/S3/Quantum/ShorContinuedFractions.shor_coprime_candidate"), H("Coprime true-order membership"),
                StatementSource.FromAuthor(Disp(Quantify(Imp(Size(), Imp(Near(), Imp(C("Coprime", C("val", X("s")), R()),
                    Rel(R(), FormulaRelationOperator.MemberOf, C("mapRatDen", Candidates())))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HilbertOperators/aicyberg2026shor")),
                Blocks(Paragraph(Text("Under the same hypotheses and Nat.Coprime s.val r, the true order r belongs to the list obtained by mapping Rat.den over candidates. mapRatDen in the displayed statement denotes this map. The proof consumes reduced-phase membership and the exact denominator formula with gcd equal to one. This establishes existence within observable candidates; it does not provide an observable certified selector of the exact order."))), DescribeRole.Theorem),
            Paragraph(Text("The generic list admits zero and integer rationals, and the recovery theorem admits r equal to one and s equal to zero. Since N is at least two, the recovery resolution excludes n equal to zero; the existing QPE marginal still admits that counting width. No assumption r divides Q is used. A passing modular exponentiation test alone says that the tested exponent is a multiple of the order, by the pinned orderOf_dvd_iff_pow_eq_one theorem. Exactness needs additional information.")),
            Paragraph(Text("For a single actual counting measurement, fix any c : QuantumShorOrderFindingCore.Parameters and n : Nat with N squared at most Q, where N = c.modulus, r = c.period and Q = 2^n. Use exactly the existing modularOperator and input of c: the target starts in computational basis state one, the residue permutation fixes padding, and the counting and target widths remain independent. Let E be the finite set of y : Fin Q for which r belongs to (candidates y.val Q N).map Rat.den. Thus E records that the observable candidate list contains the true order. The algorithm still takes only y.val, Q and N; r defines its success event and is not supplied to it.")),
            Paragraph(Text("Write p(y) for the actual complete target-register marginal normSquared (runQPE c.modularOperator n c.input y), k(s,y) for probability Q (s.val / r) y, and A for 4 / Real.pi squared. All quotients and probability sums below are real after casting natural values. The notation sum(i,T,f) means the finite sum of f over i in T. Normalization of the actual marginal makes its sum over E the probability of this single-run list-membership event. The resulting application of the existing results is")),
            Paragraph(Math(Disp(Rel(C("sum", X("y"), X("E"), C("p", X("y"))), FormulaRelationOperator.GreaterThanOrEqual,
                Multiply(Div(Num(4), Pow(X("pi"), Num(2))), Div(C("totient", X("r")), X("r"))))))),
            Paragraph(Text("To obtain an admissible label for each s : Fin r, round the real number Q times s.val / r to an integer m. The pinned abs_sub_round gives absolute rounding error at most one half. Here 0 < r < N and N squared at most Q imply r < Q. Since 0 is at most s.val and s.val + 1 is at most r, these inequalities give 0 at most m and m < Q. Taking y.val = m and the integer shift zero in Nearest gives the required circular error at most 1/(2Q). The argument permits s equal to zero and either non-strict midpoint tie; it does not require a unique nearest label.")),
            Paragraph(Text("Let C be the finite set of s : Fin r with Nat.Coprime s.val r. For each s in C, "), Ref("D5/S3/Quantum/ShorContinuedFractions.shor_coprime_candidate"),
                Text(" puts the chosen nearest label in E, and "), Ref("D5/S3/Quantum/ShorCountingMarginal.shor_phase_accuracy_bound"),
                Text(" gives k(s,y) at least A there. Each kernel value is a squared complex norm and hence nonnegative, so sum(y,E,k(s,y)) is at least A for s in C and at least zero for every other phase. This bounds event mass within each component before combining the components; no distinctness of the chosen labels is needed.")),
            Paragraph(Text("The exact actual-input identity "), Ref("D5/S3/Quantum/ShorCountingMarginal.shor_qpe_probability_mixture"),
                Text(" and interchange of finite sums give")),
            Paragraph(Math(Disp(Equal(C("sum", X("y"), X("E"), C("p", X("y"))),
                Multiply(Div(Num(1), X("r")), C("sum", X("s"), C("Fin", X("r")),
                    C("sum", X("y"), X("E"), C("k", X("s"), X("y"))))))))),
            Paragraph(Text("Summing the component bounds and multiplying by the positive weight 1/r therefore gives")),
            Paragraph(Math(Disp(Rel(C("sum", X("y"), X("E"), C("p", X("y"))), FormulaRelationOperator.GreaterThanOrEqual,
                Multiply(Div(Num(1), X("r")), C("sum", X("s"), X("C"), X("A"))))))),
            Paragraph(Text("Fin.sum_univ_eq_sum_range identifies the phase sum with the range from zero to r exclusive. Nat.coprime_comm matches the predicate to the pinned Nat.totient definition, so C has exactly Nat.totient r elements. The last constant sum is therefore (Nat.totient r) times A, giving the displayed bound. This is a count in the actual spectral mixture, with no independently sampled latent-phase hypothesis. The derivation includes r equal to one and phase zero, needs no divisibility between r and Q, and adds no restriction on n to the original resolution; N at least two and N squared at most Q already exclude widths zero and one.")),
            Paragraph(Text("The supplied actual QPE uses the inverse final Fourier transform. Using the chapter's positive Fourier convention reflects the observed grid label through negation modulo Q, as described by the owning counting-marginal result. One must apply the nearest condition to the reflected label before using this recovery statement. More explicitly, let rho be finEquiv.symm applied to negative finEquiv of the label. For a positive-Fourier output b, the corresponding success event is rho(b) in E, so candidates is evaluated at rho(b).val. The existing target-vector correspondence and this involutive permutation give that reflected event the same probability sum and lower bound. The formula above uses the supplied inverse-QFT labels; it does not identify the unreflected positive-Fourier candidate event with E. The normalization and existing pointwise peak lower bound are unchanged.")),
            Paragraph(Text("The deterministic membership theorems supply the conditional recovery step; the single-run event bound follows from their composition with the actual mixture, the phase peak bound and the finite coprime count. It establishes list membership success only. It supplies no exact-order selector, assertion that all candidate denominators divide r, repeated-sample independence, ideal least-common-multiple product law, factoring reduction, full bit or gate complexity, hardware guarantee or empirical performance. A finite recursively generated list alone supplies no such complexity claim. The general supplied-R clock statement remains broader than this actual modular N-bound specialization.")))));
    private static Formula X(string s) => DefinitionDsl.Id(s);
    private static Formula C(string s, params Formula[] xs) => DefinitionDsl.Call(s, xs);
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula All(Formula f, params (string Name, Formula Type)[] xs)
    {
        for (var i = xs.Length - 1; i >= 0; --i)
            f = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(xs[i].Name), xs[i].Type, f);
        return f;
    }
}
