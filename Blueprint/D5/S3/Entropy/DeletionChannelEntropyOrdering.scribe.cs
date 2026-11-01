using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class DeletionChannelEntropyOrderingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/DeletionChannelEntropyOrdering.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/atashpendar2018deletionentropy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positional autocorrelation does not determine the finite entropy order of binary deletion-channel outputs.",
        H("Finite Deletion-Channel Entropy Ordering"),
        Blocks(
            PublishedNode("embeddings_eq_count", Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("x"), Colon, Sp, Seq(Parenthesized(Seq(PublishedName("Fin"), Sp, F.Id("m"))), Sp, To, Sp, Parenthesized(PublishedName("Bool"))))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("y"), Colon, Sp, Seq(Parenthesized(Seq(PublishedName("Fin"), Sp, F.Id("n"))), Sp, To, Sp, Parenthesized(PublishedName("Bool"))))), Comma, Sp, Parenthesized(Seq(PublishedName("embeddings"), Sp, F.Id("x"), Sp, F.Id("y"), Sp, Eq, Sp, PublishedName("scatteredCount"), Sp, Parenthesized(Seq(Seq(PublishedName("List"), Dot, PublishedName("ofFn")), Sp, F.Id("x"))), Sp, Parenthesized(Seq(Seq(PublishedName("List"), Dot, PublishedName("ofFn")), Sp, F.Id("y"))))))))))))), DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Paragraph(Text("Binary strings of length k are functions Fin k to Bool, with false representing 0 "
                + "and true representing 1. List.ofFn reads positions in increasing order. List.sublists "
                + "counts index subsets with multiplicity: equal subwords from distinct masks remain separate. "
                + "Natural subtraction is truncated at zero. The sum defining kappa2 uses zero-based "
                + "positions, corresponding to the source's one-based Eq. (11). All binomial coefficients "
                + "and embedding counts are natural numbers; the explicitly typed casts in entropyBits are real.")),
            Node("embeddings", "Embedding count", EmbeddingsFormula(),
                "Section III-A.f, p. 3: \"Let ωx(y) denote the number of distinct ways that y can project to x:\" "
                + "The number of ways the word y deletes to x is counted by index subsequences. "
                + "Distinct index subsequences are counted separately even when their letters agree.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("deletion-channel-total-mass"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionWordCounts.pref"),
                H("Total embedding mass"), StatementSource.FromAuthor(PrefFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The source's mu indexed by n and m is the binomial factor "
                    + "D5.S3.Arith.FibonacciAtomic.CommonPrediction.Capacity.pref(n,m). "
                    + "Equation (1), p. 4, gives this factor as C(n,m) times 2 to the power n minus m. "
                    + "For the lengths used in the comparison, m is positive and strictly less than n."))),
                DescribeRole.Definition),
            Node("entropyBits", "Posterior entropy in bits", EntropyFormula(),
                "Section III-A.f, p. 3: \"Let ωx(y) denote the number of distinct ways that y can project to x:\" "
                + "The displayed expression counts the masks with y projected to x. The following sentence is: "
                + "\"we refer to the number of masks associated with a pair (y, x) as the weight of y, i.e., "
                + "the number of times x can be embedded in y as a subsequence.\" "
                + "Equation (3), p. 4, takes the base-two Shannon entropy of these counts divided by pref(n,m). "
                + "The formula sums over all binary words; incompatible words contribute zero. "
                + "D5.S3.Entropy.MaxEntropy.shannonEntropy sums Real.negMulLog, and division by Real.log 2 converts nats to bits.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("kappa2", "Positional autocorrelation", KappaFormula(),
                "Equation (11), p. 7, weights each equal pair of letters by two positional binomial coefficients. "
                + "The variables r and s range over Fin m; val supplies their natural-number indices.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The proposed finite entropy order", ClaimFormula(),
                "Section V, p. 10: \"Beyond establishing this maximization, proving the entropy ordering of x strings "
                + "determined by κ2(x) for finite n and m represents another open problem.\" "
                + "Section IV-E.3, p. 10: \"our numerical results indicate that κ2(x) predicts the entropy ordering perfectly "
                + "in the finite length domain as well, i.e., for small and comparable fixed values of n and m. "
                + "An example obtained from empirical data is presented in Table I to illustrate the correlation between "
                + "Hn(x) and κ2(x) for n = 8 and m = 5.\" "
                + "The formula expresses the order of Table I: strictly larger kappa2 implies no larger entropyBits. "
                + "It compares any two words of the same positive length m at every input length n greater than m.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The finite entropy order fails", Disp(Seq(Neg, Sp, F.Id("claim"))),
                "At m = 5 and n = 8, the words 00100 and 01110 have kappa2 values 450 and 410. "
                + "Their entropies have the reverse of the proposed order: entropyBits(8,01110) is strictly less "
                + "than entropyBits(8,00100). Both embedding histograms have total mass 448. "
                + "The sum of w log(w) is the logarithm of the integer product of w to the power w. "
                + "A strict product comparison gives the strict entropy comparison, hence the negation of claim. "
                + "This finite comparison leaves the source's asymptotic minimization theorem unchanged.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("atashpendar-mestel-roscoe-ryan-2018-kappa2-entropy-ordering"),
                    ResolutionKind.Refuted)),
            OddFamilyApplication())));

    private static DocumentBlock OddFamilyApplication()
    {
        Formula r = F.Id("r"), x = new Formula.Subscript(F.Id("x"), r),
            y = new Formula.Subscript(F.Id("y"), r);
        Formula twice = Multiply(D(2), r), length = Add(twice, D(2));
        Formula b = Q("Nat", "choose", twice, r),
            c = Q("Nat", "choose", Multiply(D(4), r), twice);
        Formula bSquare = new Formula.Power(b, D(2));
        Formula kappaGap = Subtract(CastReal(Call("kappa2", y)), CastReal(Call("kappa2", x)));
        Formula entropyGap = Subtract(Call("entropyBits", length, y), Call("entropyBits", length, x));
        Formula entropyValue = new Formula.Fraction(
            Subtract(Add(Call("f", twice), Call("f", D(2))), Multiply(D(2), Call("f", Add(r, D(1))))),
            Multiply(D(4), Parenthesized(Add(r, D(1)))));
        Formula asymptoticValue = Subtract(Subtract(new Formula.Fraction(D(1), D(2)),
            new Formula.Fraction(Q("Real", "logb", D(2), r), Multiply(D(2), Parenthesized(Add(r, D(1)))))),
            Multiply(new Formula.Fraction(D(1), D(2)),
                Q("Real", "logb", D(2), Add(D(1), new Formula.Fraction(D(1), r)))));
        return new DocumentBlock.Section(H("An odd family with a half-bit entropy gap"), Blocks(
            Paragraph(Text("For every integer r at least 1, set m = 2r + 1 and n = 2r + 2. "
                + "The word x_r is 0 followed by 2r - 1 ones and then 0; y_r is r zeros, "
                + "one 1, and r zeros. In native Fin coordinates, x_r(i) is true exactly when "
                + "0 < i.val < 2r, and y_r(i) is true exactly when i.val = r. "
                + "List.ofFn gives runWord false [1, 2r - 1, 1] and runWord false [r, 1, r], respectively. "
                + "These lists have length 2r + 1. Natural indices correspond to source positions i.val + 1; "
                + "substitution in both binomial weights gives the source's one-based formula.")),
            Paragraph(Text("The source word and the increasing m-position mask are independent and uniform. "
                + "Each mask-word pair has mass 1/(2^n C(n,m)). Summing precisely the masks "
                + "that output x gives joint mass omega_x(y)/(2^n C(n,m)). "
                + "The identity embeddings_eq_count and the fixed-length sublists count retain each index "
                + "embedding separately, even when the selected letters coincide. The generic deletion_total "
                + "in TwoDeletionChannelEntropy gives total mass C(n,m) times 2^(n-m). Conditioning this joint "
                + "law gives the exact posterior used by entropyBits. The inherited definitions include the "
                + "empty pattern and all zero-weight words; zero entropy summands remain zero.")),
            Paragraph(Text("Write f(t) = t log_2(t), with f(0) = 0. "
                + "For positive consecutive run lengths a_1 through a_s, BinaryRunSupersequenceCounts.oneWordSum_runs "
                + "applied to f gives the sum of weight times log_2(weight) as the sum of f(a_i + 1): "
                + "its remaining term is a multiple of f(1) = 0. The generic entropy_eq_log_sub_phi in "
                + "TwoDeletionChannelEntropy then gives the single-deletion run formula, with "
                + "normalizer 2(m + 1). Thus the two displayed run lists give the following exact bit gap.")),
            new DocumentBlock.DisplayFormula(Disp(Equal(entropyGap, entropyValue))),
            Paragraph(Text("For r at least 2 the numerator is strictly positive. Indeed, strict convexity "
                + "of t log(t) at the distinct positive points 2 and 2r gives "
                + "f(2) + f(2r) > 2 f(r + 1), since log(2) is positive. The denominator 4(r + 1) is positive.")),
            Paragraph(Text("For autocorrelation, let M be the source's positional weight matrix, "
                + "B = C(2r,r), C = C(4r,2r), and S = C(4r + 1,2r). "
                + "The coefficient identity PowerSeries.mk_one_pow_eq_mk_choose_add, multiplication of powers, "
                + "and coefficient convolution show that each row sum of M is S. The matrix is symmetric. "
                + "For a word, the equal-letter sum is the total matrix sum minus twice the zero-one cross sum. "
                + "The endpoint entries are C, C, 1, 1; the middle diagonal entry is B squared. "
                + "Consequently the cross sums of x_r and y_r are 2(S - C - 1) and S - B squared. "
                + "Using S = (4r + 1) C / (2r + 1) gives the exact difference below. "
                + "Both kappa2 values are cast to the reals before subtraction.")),
            new DocumentBlock.DisplayFormula(Disp(Equal(kappaGap,
                Multiply(D(2), Parenthesized(Subtract(Subtract(bSquare,
                    new Formula.Fraction(c, Add(twice, D(1)))), D(2))))))),
            Paragraph(Text("Its sign can also be read from the pinned binomial square-sum and central-maximum "
                + "identities. They give C at most 2 + (2r - 1) B squared: the two endpoint terms are 1, "
                + "and each of the other 2r - 1 terms is at most B squared. Also B is at least 2r. "
                + "For r at least 2 this implies B squared > 2r + 2, so "
                + "B squared - C/(2r + 1) - 2 is at least "
                + "2(B squared - 2r - 2)/(2r + 1), which is strictly positive. "
                + "Thus the autocorrelation and entropy comparisons hold simultaneously for these same words.")),
            Paragraph(Text("Logarithm multiplication and division rules rewrite the same entropy gap as")),
            new DocumentBlock.DisplayFormula(Disp(Equal(entropyGap, asymptoticValue))),
            Paragraph(Text("Along the integer family r tending to infinity, log_2(r)/(2(r + 1)) tends to zero "
                + "by Real.tendsto_pow_logb_div_mul_add_atTop, and log_2(1 + 1/r) tends to zero by continuity "
                + "at 1. Hence the entropy gap tends to one half bit. At r = 1 both words are 010 and both "
                + "differences are zero; r = 0 is outside the family. This application concerns one deletion "
                + "with both lengths growing together. It does not imply a capacity statement or alter the "
                + "fixed-m, n tending to infinity regime."))));
    }

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("deletion-channel-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role,
            openProblemResolutionClaim: resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Q(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Named(owner), Dot, Named(name)), [.. args]);
    private static Formula Shannon(Formula law) => new Formula.Apply(
        Seq(Named("D5"), Dot, Named("S3"), Dot, Named("Entropy"), Dot,
            Named("MaxEntropy"), Dot, Named("shannonEntropy")), [law]);
    private static Formula Pref(Formula n, Formula m) => new Formula.Apply(
        Seq(Named("D5"), Dot, Named("S3"), Dot, Named("Arith"), Dot,
            Named("FibonacciAtomic"), Dot, Named("CommonPrediction"), Dot,
            Named("Capacity"), Dot, Named("pref")), [n, m]);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Word(Formula length) =>
        new Formula.TypeArrow(Call("Fin", length), Named("Bool"));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Named("fun"), Sp,
            Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula CastReal(Formula value) => Parenthesized(Seq(value, Colon, Sp, Reals()));
    private static Formula EmbeddingBody(Formula x, Formula y) =>
        Q("List", "length", Q("List", "filter",
            Lam("z", Call("List", Named("Bool")), Equal(F.Id("z"), Q("List", "ofFn", x))),
            Q("List", "sublists", Q("List", "ofFn", y))));

    private static Formula EmbeddingsFormula()
    {
        Formula m = F.Id("m"), n = F.Id("n"), x = F.Id("x"), y = F.Id("y");
        return Disp(All("m", Naturals(), All("n", Naturals(), All("x", Word(m), All("y", Word(n),
            Equal(Call("embeddings", x, y), EmbeddingBody(x, y)))))));
    }

    private static Formula PrefFormula()
    {
        Formula n = F.Id("n"), m = F.Id("m");
        return Disp(All("n", Naturals(), All("m", Naturals(), Equal(Pref(n, m),
            Multiply(Q("Nat", "choose", n, m), new Formula.Power(D(2), Subtract(n, m)))))));
    }

    private static Formula EntropyFormula()
    {
        Formula n = F.Id("n"), m = F.Id("m"), x = F.Id("x"), y = F.Id("y");
        Formula law = Lam("y", Word(n), new Formula.Fraction(
            CastReal(Call("embeddings", x, y)), CastReal(Pref(n, m))));
        return Disp(All("n", Naturals(), All("m", Naturals(), All("x", Word(m),
            Equal(Call("entropyBits", n, x), new Formula.Fraction(Shannon(law), Q("Real", "log", D(2))))))));
    }

    private static Formula KappaFormula()
    {
        Formula m = F.Id("m"), x = F.Id("x"), r = F.Id("r"), s = F.Id("s");
        Formula rv = Call("val", r), sv = Call("val", s);
        Formula coefficient = Multiply(Q("Nat", "choose", Add(rv, sv), rv),
            Q("Nat", "choose", Subtract(Subtract(Subtract(Multiply(D(2), m), D(2)), rv), sv),
                Subtract(Subtract(m, D(1)), rv)));
        Formula term = Parenthesized(Seq(Named("if"), Sp, Equal(Call("x", r), Call("x", s)),
            Sp, Named("then"), Sp, coefficient, Sp, Named("else"), Sp, D(0)));
        Formula sum = Seq(Sum, Underscore, Grp(r, Colon, Sp, Call("Fin", m)), Sp,
            Sum, Underscore, Grp(s, Colon, Sp, Call("Fin", m)), Sp, term);
        return Disp(All("m", Naturals(), All("x", Word(m), Equal(Call("kappa2", x), sum))));
    }

    private static Formula ClaimFormula()
    {
        Formula m = F.Id("m"), n = F.Id("n"), u = F.Id("u"), v = F.Id("v");
        Formula comparison = Seq(Call("kappa2", v), Sp, Lt, Sp, Call("kappa2", u), Sp, Rightarrow, Sp,
            Call("entropyBits", n, u), Sp, Le, Sp, Call("entropyBits", n, v));
        return Disp(Equal(F.Id("claim"), All("m", Naturals(), All("n", Naturals(),
            Seq(D(1), Sp, Le, Sp, m, Sp, Rightarrow, Sp, m, Sp, Lt, Sp, n, Sp, Rightarrow, Sp,
                All("u", Word(m), All("v", Word(m), comparison)))))));
    }

    private static DocumentBlock PublishedNode(string name, Formula formula, DescribeRole role,
        AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("singhvi-owner-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/Entropy/DeletionChannelEntropyOrdering." + name), H(name), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text("The formula relates a word's constant runs and its scattered-subword counts."))), role);
    private static Formula PublishedName(string name) => Seq(Operatorname, Grp(F.Id(name)));
}
