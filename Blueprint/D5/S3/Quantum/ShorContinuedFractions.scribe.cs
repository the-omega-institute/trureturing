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
            Paragraph(Text("The supplied actual QPE uses the inverse final Fourier transform. Using the chapter's positive Fourier convention reflects the observed grid label through negation modulo Q, as described by the owning counting-marginal result. One must apply the nearest condition to the reflected label before using this recovery statement. The normalization and existing pointwise peak lower bound are unchanged.")),
            Paragraph(Text("This conditional deterministic theorem does not establish an aggregate quantum success probability, a random coprimality rate, repeated-sample independence, the ideal least-common-multiple product law, a factoring reduction, a certified selection procedure, full bit or gate complexity or empirical performance. A finite recursively generated list alone supplies no such complexity claim. The general supplied-R clock statement remains broader than this actual modular N-bound specialization.")))));
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
