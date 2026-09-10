using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class BaezDuarteQBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/SeriesInequalities/BaezDuarteQBounds.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/baezduarte2003criterion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original unsigned Q series bounds the actual Baez-Duarte coefficients "
        + "unconditionally, with an explicit all-index half-power estimate.",
        H("Baez-Duarte Q Bounds"),
        Blocks(
            Entry("q", "baezDuarteQ", "The original unsigned series", DescribeRole.Definition,
                "Q is exactly the source series with positive integer index shifted by one. "
                + "The original n equals one term is retained, including zero to the zeroth power."),
            Entry("summable", "baez_duarte_q_summable", "Summability at every index", DescribeRole.Theorem,
                "Nonnegative original summands have bounded partial sums by the finite split "
                + "at cutoff one. No convergence hypothesis is imposed."),
            Entry("nonneg", "baez_duarte_q_nonneg", "Nonnegativity", DescribeRole.Theorem,
                "Every original summand is nonnegative; the closed interval endpoints are retained."),
            Entry("bound", "baez_duarte_q_le_three_div_sqrt", "The all-index bound", DescribeRole.Theorem,
                "The private live escape finite_q_split_bound bounds every partial sum through M "
                + "by N divided by k plus one, plus one divided by N, for every natural k, M and "
                + "positive natural N, including M less than N. Its geometric_weight_bound "
                + "prerequisite proves t times the kth power of one minus t is at most one divided "
                + "by k plus one on the entire closed unit interval, using the finite geometric "
                + "identity. The tail uses mathlib's inverse-square interval bound. "
                + "The live Q proof applies that finite split with N equal to Nat.sqrt(k+1); "
                + "it is an intermediate estimate, not a restatement of the final conclusion. "
                + "The explicit constant three, shifted all-index estimate and finite split are "
                + "repo-derived refinements of Lemma 2.1, not literal statements in the source."),
            Entry("c-q", "abs_baez_duarte_le_q", "Comparison with the actual coefficients", DescribeRole.Theorem,
                "c denotes the imported D5.S3.Weil.RieszBaezDuarte.baezDuarte, whose existing "
                + "baez_duarte_hasSum_moebius is the sole arithmetic owner. Its signed sum is "
                + "compared with the original Q using the integer Mobius absolute bound. "
                + "The arithmetic owner's private q is not this Q."),
            Entry("c-bound", "abs_baez_duarte_le_three_div_sqrt", "Unconditional coefficient decay", DescribeRole.Theorem,
                "This thin companion consumes the actual-c comparison and Q bound. Remark 1.1 "
                + "and equations (2.7)-(2.8) acknowledge the source of the unconditional half-power result."),
            Entry("rpow", "baez_duarte_q_le_rpow", "The positive-index power form", DescribeRole.Theorem,
                "For every positive index this is a thin consequence of the shifted bound; "
                + "the all-index theorem continues to control index zero."),
            Entry("c-rpow", "abs_baez_duarte_le_rpow", "The actual-c power form", DescribeRole.Theorem,
                "This companion consumes the actual-c comparison and the positive-index Q estimate."),
            Entry("zero", "baez_duarte_q_zero_le_two", "The full zero-index prefix", DescribeRole.Theorem,
                "The finite split at cutoff one also gives Q at zero at most two. "
                + "The original first summand is one, so it cannot be discarded."),
            Paragraph(Text("Source standing is user-requested formalization of known literature with "
                + "repo-derived quantitative refinements and the typed Library acknowledgement. "
                + "Utility none applies to general analytic estimates and their thin companions; "
                + "no bounded enumeration, checker, numerical reduction or certified finite instance "
                + "is introduced. Neither RH direction nor the original Newton identity is proved. "
                + "The future absolute double-series consumer of Q times P remains unimplemented. "
                + "The Library note retains the epsilon versus epsilon/2 discrepancy, the printed "
                + "positive 3/4 on page five, and the Lemma 2.2 cross-reference distinction.")))));

    private static DocumentBlock Entry(string id, string declaration, string title,
        DescribeRole role, string commentary) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Statement(id)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(commentary))), role);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(FormulaDsl.Id(name), [.. args]);
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula All(string x, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x),
            Seq(Mathbb, Grp(FormulaDsl.Id("N"))), body);
    private static Formula Statement(string id)
    {
        Formula k = FormulaDsl.Id("k"), n = FormulaDsl.Id("n");
        Formula q = Call("Q", k), c = new Formula.Absolute(Call("c", k));
        Formula w = Frac(D(1), Pow(Seq(Open, n, Plus, D(1), Close), D(2)));
        Formula term = Seq(w, Sp, Pow(Seq(Open, D(1), Minus, w, Close), k));
        Formula rootBound = Frac(D(3), Call("sqrt", Seq(k, Plus, D(1))));
        Formula powerBound = Seq(D(3), Sp, Pow(k, Seq(Minus, Frac(D(1), D(2)))));
        Formula body = id switch
        {
            "q" => Seq(q, Eq, Seq(Sum, Underscore, Grp(n, Eq, D(0)), Caret,
                Grp(Infty), Sp, term)),
            "summable" => Call("Summable", Seq(Open, n, Mapsto, term, Close)),
            "nonneg" => Seq(D(0), Le, Sp, q),
            "bound" => Seq(q, Le, Sp, rootBound),
            "c-q" => Seq(c, Le, Sp, q),
            "c-bound" => Seq(c, Le, Sp, rootBound),
            "rpow" => Seq(D(1), Le, Sp, k, Rightarrow, Sp, q, Le, Sp, powerBound),
            "c-rpow" => Seq(D(1), Le, Sp, k, Rightarrow, Sp, c, Le, Sp, powerBound),
            "zero" => Seq(Call("Q", D(0)), Le, Sp, D(2)),
            _ => throw new System.ArgumentException("Unknown statement", nameof(id))
        };
        return Disp(id == "zero" ? body : All("k", body));
    }
}
