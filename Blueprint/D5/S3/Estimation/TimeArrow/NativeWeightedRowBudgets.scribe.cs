using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class NativeWeightedRowBudgetsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/TimeArrow/NativeWeightedRowBudgets.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full native weighted sums retain their actual and reference tail budgets.",
        H("Native row tails, full moments and environment anchors"),
        Blocks(
            Paragraph(Text(
                    "For natural M, q and L, S is any subset of Fin M of cardinality q, and e is either the pair experiment or "
                    + "the uniform-start path experiment. Write c = compensation M q r = rq/(M-q), with the natural difference M-q; "
                    + "the number of transitions is T = 2ML. The mass p(o) is probability r e S o on the complete history type Obs "
                    + "M T e. Set nplus(i,o) = count e o i 1 and nminus(i,o) = count e o i (-1). These counts use the same complete "
                    + "history, including adjacent path visits and terminal coordinates.")),
            Paragraph(Text(
                    "Write Q_i(a,b) = rowReference S r L i (a,b). This is the product of Poisson masses with means L(1+d_i)/2 and "
                    + "L(1-d_i)/2, where d_i is r on S and -c outside S. All infinite reference sums range over the full natural "
                    + "count-pair space, including zero counts. E[X] denotes the finite sum of p(o)X(o), and P[A] denotes the "
                    + "finite sum of p(o) over the indicated event.")),
            Paragraph(Text(
                    "The combined native moment and environment-anchor relations are repository-derived. Classical Poisson "
                    + "approximation and finite Markov comparison are acknowledged in the cited Library notes; absolute Poisson "
                    + "approximation alone does not supply the relative one-row and two-row native estimates.")),
            Describe.Lean(
                DescribeId.Create("native-row-count-tail"),
                DeclarationHandle.Create(Module + "NativeRowCountTail.native_row_count_tail"),
                H("Exponential tail for one native row"),
                StatementSource.FromAuthor(Formula1()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/lecam1960poissonbinomial"), LibraryNoteRef.Create("D5/L/Estimation/grinsteadsnell2006probability")),
                Blocks(
                Paragraph(Text(
                    "For every natural M, q, L, every r and support S, assume 1 <= q < M, 0 < r < 1, c < 1, 6 <= M, 1 <= L, and "
                    + "L/M <= 1/45. For either experiment and every i in Fin M the displayed tail bound holds.")),
                Paragraph(Text(
                    "The pair generating function factors over transitions. The path estimate uses its full marked generating "
                    + "function with tilt 4 in both parity counts. Exponential Markov comparison gives the common exponent."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-all-row-count-cut"),
                DeclarationHandle.Create(Module + "NativeRowCountTail.native_all_row_count_cut"),
                H("Simultaneous cutoff for all rows"),
                StatementSource.FromAuthor(Formula2()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/grinsteadsnell2006probability")),
                Blocks(
                Paragraph(Text(
                    "Under exactly the one-row tail hypotheses, the displayed bound holds for every support and either "
                    + "experiment. All M elements of Fin M are included; no row is discarded.")),
                Paragraph(Text(
                    "The complement is bounded by the sum of the M one-row failure masses. The normalization of the original "
                    + "complete-history probability then gives the lower bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reference-pos"),
                DeclarationHandle.Create(Module + "NativeRowMomentTransfer.reference_pos"),
                H("Strict positivity of every reference count mass"),
                StatementSource.FromAuthor(Formula3()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/lecam1960poissonbinomial")),
                Blocks(
                Paragraph(Text(
                    "For every M, q, L, S, r and real kappa assume kappa > 0, r > 0, r <= 1-kappa, c <= 1-kappa and 1 <= L. No "
                    + "further population or density hypothesis is imposed by this theorem.")),
                Paragraph(Text(
                    "Both Poisson means are strictly positive because every native row drift lies strictly between -1 and 1. "
                    + "Exponentials and factorial denominators are positive, including at zero counts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-truncated-weighted-moments"),
                DeclarationHandle.Create(Module + "NativeRowMomentTransfer.native_truncated_weighted_moments"),
                H("Mean and second moment on a finite count set"),
                StatementSource.FromAuthor(Formula4()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/lecam1960poissonbinomial")),
                Blocks(
                Paragraph(Text(
                    "Fix 0 < kappa < 1. There exist real A > 0, a natural Mzero >= 1 and real etazero > 0 depending only on "
                    + "kappa. For every M, q, L and r assume Mzero <= M, 1 <= q < M, 0 < r <= 1-kappa, c <= 1-kappa, 1 <= L, L/M <= "
                    + "etazero, and A L^2/M <= 1/2. The same constants work for every true support S, either experiment e, every "
                    + "finite row set I and every admitted weight function g.")),
                Paragraph(Text(
                    "Choose any finite count-pair set D with a <= 8L and b <= 8L for every (a,b) in D. Require 0 <= g(i,a,b) <= 1 "
                    + "on D for every row. Here a_i is the finite sum over D of g(i,a,b)Q_i(a,b), B is the sum over I of a_i, and "
                    + "Z(o) sums the truncatedRow values over I. A truncatedRow is g at the observed count pair when that pair lies "
                    + "in D and zero otherwise.")),
                Paragraph(Text(
                    "The native one-row relative comparison controls the mean. The two-row comparison controls off-diagonal "
                    + "products on the same actual history; diagonal terms use weights between zero and one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-full-weighted-moments"),
                DeclarationHandle.Create(Module + "NativeWeightedRowBudgets.native_full_weighted_moments"),
                H("Full-row mean and second moment with both tails restored"),
                StatementSource.FromAuthor(Formula5()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/lecam1960poissonbinomial"), LibraryNoteRef.Create("D5/L/Estimation/grinsteadsnell2006probability")),
                Blocks(
                Paragraph(Text(
                    "Fix 0 < kappa < 1. There exist real A > 0, a natural Mzero >= 1 and real etazero > 0 depending only on "
                    + "kappa. For every M, q, L and r assume Mzero <= M, 1 <= q < M, 0 < r <= 1-kappa, c <= 1-kappa, 1 <= L, L/M <= "
                    + "etazero, and A L^2/M <= 1/2. The same constants work for every true support S, either experiment e, every "
                    + "finite row set I and every admitted weight function g.")),
                Paragraph(Text(
                    "For the complete-row bounds also assume 6 <= M and L/M <= 1/45, and 0 <= g(i,a,b) <= 1 for every row and "
                    + "natural count pair. Define a_i as the complete reference sum of g(i,a,b)Q_i(a,b), B as the sum of a_i over "
                    + "I, and Z(o) as the sum of g(i,nplus(i,o),nminus(i,o)) over I. Put zeta = exp(-(8 log 4 - 6)L).")),
                Paragraph(Text(
                    "The finite count-box comparison is combined with the original all-row tail and the complete Poisson "
                    + "reference tail. Both actual and reference tails are restored, so B and Z are the full quantities."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-square-markov"),
                DeclarationHandle.Create(Module + "NativeWeightedRowBudgets.finite_square_markov"),
                H("Finite square-moment Markov comparison"),
                StatementSource.FromAuthor(Formula6()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/grinsteadsnell2006probability")),
                Blocks(
                Paragraph(Text(
                    "For every finite type Omega, every p and X from Omega to the reals, and every real a, h, B, assume p(o) >= 0 "
                    + "for all o, h > 0 and sum over Omega of p(o)(X(o)-a)^2 <= B. The displayed inequality holds without requiring "
                    + "the masses p to sum to one.")),
                Paragraph(Text(
                    "This is the finite nonnegative square-moment form of Markov inequality; using a as the mean gives the usual "
                    + "Chebyshev estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-full-weighted-deviation"),
                DeclarationHandle.Create(Module + "NativeWeightedRowBudgets.native_full_weighted_deviation"),
                H("Deviation from the complete reference mean"),
                StatementSource.FromAuthor(Formula7()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/grinsteadsnell2006probability")),
                Blocks(
                Paragraph(Text(
                    "Fix 0 < kappa < 1. There exist real A > 0, a natural Mzero >= 1 and real etazero > 0 depending only on "
                    + "kappa. For every M, q, L and r assume Mzero <= M, 1 <= q < M, 0 < r <= 1-kappa, c <= 1-kappa, 1 <= L, L/M <= "
                    + "etazero, and A L^2/M <= 1/2. The same constants work for every true support S, either experiment e, every "
                    + "finite row set I and every admitted weight function g.")),
                Paragraph(Text(
                    "For the complete-row bounds also assume 6 <= M and L/M <= 1/45, and 0 <= g(i,a,b) <= 1 for every row and "
                    + "natural count pair. Define a_i as the complete reference sum of g(i,a,b)Q_i(a,b), B as the sum of a_i over "
                    + "I, and Z(o) as the sum of g(i,nplus(i,o),nminus(i,o)) over I. Put zeta = exp(-(8 log 4 - 6)L).")),
                Paragraph(Text(
                    "For every real h > 0, the full second-moment estimate and finite square-moment comparison give the displayed "
                    + "probability bound. The constants are chosen before h, I, g, the support and the experiment."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-environment-anchor-budget"),
                DeclarationHandle.Create(Module + "NativeEnvironmentAnchors.finite_environment_anchor_budget"),
                H("An anchor budget when the good event varies inside fibers"),
                StatementSource.FromAuthor(Formula8()),
                AssessedProvenance.FromRepo(),
                Blocks(
                Paragraph(Text(
                    "Let Omega be any finite type and E any type with decidable equality. Let env map Omega to E, let p be a "
                    + "nonnegative real mass function, and let G and C be decidable predicates on Omega. No normalization of p is "
                    + "required.")),
                Paragraph(Text(
                    "For every z satisfying G(z), assume that the mass of y with env(y)=env(z) and not C(y) is at most 1/16 of "
                    + "the whole env(z) fiber mass. Then the displayed bound holds. Neither G nor C is assumed constant on a fiber.")),
                Paragraph(Text(
                    "Every fiber without a point satisfying both G and C either has no G point, or its G points lie in the small "
                    + "central-event complement. Summing these fiber contributions yields the factor 16/15."))),
                DescribeRole.Theorem)
        )));

    private static Formula Formula1() => Disp(Seq(
            F.Id("P"), OpenBracket, F.Id("nplus"), Open, F.Id("i"), Close, Plus, F.Id("nminus"), Open, F.Id("i"), Close, Gt,
            D(8), F.Id("L"), CloseBracket, Le, Exp, Open, Minus, Open, D(8), Log, D(4), Minus, D(6), Close, F.Id("L"), Close));

    private static Formula Formula2() => Disp(Seq(
            F.Id("P"), OpenBracket, Forall, F.Id("i"), InMacro, Mathrm, Grp(F.Id("Fin")), Open, F.Id("M"), Close, Comma,
            F.Id("nplus"), Open, F.Id("i"), Close, Plus, F.Id("nminus"), Open, F.Id("i"), Close, Le, D(8), F.Id("L"),
            CloseBracket, Ge, D(1), Minus, F.Id("M"), Exp, Open, Minus, Open, D(8), Log, D(4), Minus, D(6), Close, F.Id("L"),
            Close));

    private static Formula Formula3() => Disp(Seq(
            Forall, F.Id("i"), InMacro, Mathrm, Grp(F.Id("Fin")), Open, F.Id("M"), Close, Comma, Forall, Open, F.Id("a"),
            Comma, F.Id("b"), Close, InMacro, Mathbb, Grp(F.Id("N")), Caret, D(2), Comma, Quad, F.Id("Q"), Underscore,
            F.Id("i"), Open, F.Id("a"), Comma, F.Id("b"), Close, Gt, D(0)));

    private static Formula Formula4() => Disp(Seq(
            Bar, F.Id("E"), OpenBracket, F.Id("Z"), CloseBracket, Minus, F.Id("B"), Bar, Le, Frac,
            Grp(F.Id("AL"), Caret, D(2)), Grp(F.Id("M")), F.Id("B"), Quad, Land, Quad, F.Id("E"), OpenBracket, Open, F.Id("Z"),
            Minus, F.Id("B"), Close, Caret, D(2), CloseBracket, Le, Frac, Grp(D(3)), Grp(D(2)), F.Id("B"), Plus, D(3), Frac,
            Grp(F.Id("AL"), Caret, D(3)), Grp(F.Id("M")), F.Id("B"), Caret, D(2)));

    private static Formula Formula5() => Disp(Seq(
            Bar, F.Id("E"), OpenBracket, F.Id("Z"), CloseBracket, Minus, F.Id("B"), Bar, Le, Frac,
            Grp(F.Id("AL"), Caret, D(2)), Grp(F.Id("M")), F.Id("B"), Plus, D(2), Bar, F.Id("I"), Bar, Zeta, Quad, Land, Quad,
            F.Id("E"), OpenBracket, Open, F.Id("Z"), Minus, F.Id("B"), Close, Caret, D(2), CloseBracket, Le, D(3), F.Id("B"),
            Plus, D(8), Frac, Grp(F.Id("AL"), Caret, D(3)), Grp(F.Id("M")), F.Id("B"), Caret, D(2), Plus, D(1, 0), Bar,
            F.Id("I"), Bar, Caret, D(2), Zeta));

    private static Formula Formula6() => Disp(Seq(
            Sum, Underscore,
            Grp(F.Id("o"), Colon, Bar, F.Id("X"), Open, F.Id("o"), Close, Minus, F.Id("a"), Bar, Gt, F.Id("h")), F.Id("p"),
            Open, F.Id("o"), Close, Le, Frac, Grp(F.Id("B")), Grp(F.Id("h"), Caret, D(2))));

    private static Formula Formula7() => Disp(Seq(
            Forall, F.Id("h"), Gt, D(0), Comma, Quad, F.Id("P"), OpenBracket, Bar, F.Id("Z"), Minus, F.Id("B"), Bar, Gt,
            F.Id("h"), CloseBracket, Le, Frac,
            Grp(D(3), F.Id("B"), Plus, D(8), Frac, Grp(F.Id("AL"), Caret, D(3)), Grp(F.Id("M")), F.Id("B"), Caret, D(2), Plus, D(1, 0), Bar, F.Id("I"), Bar, Caret, D(2), Zeta),
            Grp(F.Id("h"), Caret, D(2))));

    private static Formula Formula8() => Disp(Seq(
            Sum, Underscore,
            Grp(F.Id("y"), Colon, Neg, Exists, F.Id("z"), Comma, F.Id("env"), Open, F.Id("z"), Close, Eq, F.Id("env"), Open, F.Id("y"), Close, Land, F.Id("G"), Open, F.Id("z"), Close, Land, F.Id("C"), Open, F.Id("z"), Close),
            F.Id("p"), Open, F.Id("y"), Close, Le, Frac, Grp(D(1, 6)), Grp(D(1, 5)), Sum, Underscore,
            Grp(F.Id("y"), Colon, Neg, F.Id("G"), Open, F.Id("y"), Close), F.Id("p"), Open, F.Id("y"), Close));

}
