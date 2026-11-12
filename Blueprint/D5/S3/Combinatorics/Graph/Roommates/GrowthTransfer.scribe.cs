using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Roommates;

internal sealed class GrowthTransferDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform exponential probability bounds for Mertens d=1, r=2.",
        H("Growth transfer"), Blocks(
            Describe.Lean(DescribeId.Create("same-q-probability-of-counts"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/GrowthTransfer.same_q_probability_of_counts"),
                H("One base for both parities"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Open, Forall, Sp, F.Id("m"), Comma, F.Id("k"), Colon, Mathbb, Grp(F.Id("N")), Comma,
                    D(0), Lt, Sp, F.Id("m"), Rightarrow, D(0), Lt, Sp, F.Id("k"), Rightarrow,
                    F.Id("b"), Open, F.Id("m"), Close, F.Id("b"), Open, F.Id("k"), Close, Le, Sp,
                    F.Id("b"), Open, F.Id("m"), Plus, F.Id("k"), Plus, D(6), Close, Close, Land, RowBreak,
                    Open, Forall, Sp, F.Id("m"), Colon, Mathbb, Grp(F.Id("N")), Comma,
                    D(0), Lt, Sp, F.Id("m"), Rightarrow,
                    F.Id("b"), Open, F.Id("m"), Close, Le, Sp, F.Id("a"), Open, F.Id("m"), Plus, D(1), Close, Close, Land,
                    F.Id("b"), Open, D(3), Close, Lt, D(2,4), Caret, Grp(D(3)), Rightarrow, RowBreak,
                    Exists, Sp, F.Id("q"), Comma, F.Id("c"), Comma, F.Id("C"), Colon, Mathbb, Grp(F.Id("R")), Comma,
                    D(0), Lt, Sp, F.Id("q"), Lt, D(1), Land,
                    D(0), Lt, Sp, F.Id("c"), Land, D(0), Lt, Sp, F.Id("C"), Land, RowBreak,
                    Forall, Sp, F.Id("n"), Colon, Mathbb, Grp(F.Id("N")), Comma,
                    D(2), Le, Sp, F.Id("n"), Rightarrow,
                    F.Id("c"), F.Id("q"), Caret, Grp(F.Id("n"), Plus, D(5)), Le, Sp,
                    F.Id("p"), Open, F.Id("n"), Close, Le, Sp,
                    F.Id("C"), F.Id("q"), Caret, Grp(F.Id("n"), Plus, D(5)),
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Here b(m) is OpenCertificates.count m, the number of ranking words admitting a certificate, counted once per word. The quantity a(t) counts the successful labelled SourceModel.Profile t profiles, and p(t) is SourceModel.solutionProbability t = a(t)/24^(t+5). The source parameter is N=t+5. Singles are allowed, and each of the N agents independently chooses one of 24 strict neighbor rankings.")),
                    Paragraph(Text("The conditional transfer isolates three concrete premises: padded concatenation with six added sites for positive lengths, injective six-site cyclic closure, and count 3 < 24^3. The final result supplies all three from PaddedCompletion.count_padded_supermultiplicative, CyclicClosure.count_le_successful_profile_count, and TriangleCount.count_three_bound, respectively. The upper cyclic comparison is the existing CyclicBridge.source_count_le_open_count, with the unchanged source probability normalization.")),
                    Paragraph(Text("For f(m)=log b(m), the existing count lower bound makes every logarithm positive-domain and f nonnegative; the empty word has count one. Existing submultiplicativity gives subadditivity of f. Apply FixedGapGrowth.fixed_gap_log_bounds with gap six to obtain h*m <= f(m) <= h*m+f(6). Exponentiation yields exp(h)^m <= b(m) <= exp(h)^m*b(6). The strict count-at-three premise gives h < log 24. Thus q=exp(h)/24 lies strictly between zero and one, c=exp(h)^(-6) is positive, and C=b(6) is positive. Closure at m=n-1 supplies the lower bound, and cutting at N=n+5 supplies the upper bound, for every n>=2 without a parity split.")),
                    Paragraph(Text("The estimate synthesizes the proved count components; global novelty and priority remain unproved. The original statement is Mertens, cond-mat/0509221v2, Conjecture 3, DOI 10.1088/1742-5468/2005/10/P10008, restricted to d=1,r=2. The Apache-2.0 supplier attribution and license remain in SourceModel and docs/reports/licenses/formal-conjectures-mertens/LICENSE.txt. The unfinished escape audit is tracked by issue 29645."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Roommates/GrowthTransfer.result"),
                H("Unconditional exact source probability"), StatementSource.FromAuthor(ProbabilityFormula()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/mertens2005stable")),
                Blocks(
                    Paragraph(Text("Here p(n) is exactly SourceModel.solutionProbability n, the number of labelled profiles admitting an acceptable stable partial matching divided by 24^(n+5). The N=n+5 ranking permutations are independent and uniform. Fixed points of the involution are singles; every acceptable neighbor is preferred to being single. The event is existential in matchings, so each successful profile is counted once.")),
                    Paragraph(Text("There are no count, completion, rate, parity or analytic hypotheses. All n>=2, equivalently all N>=7, share the same positive q<1 and positive constants c,C. The concrete strict input is count 3<=13808<13824=24^3; the sixteen excluded words feed the analytic estimate on its live proof path. The proof applies the transfer above to the actual padded and cyclic injections. Its admissibility candidate is open-problem-resolution for the source's d=1,r=2 specialization, with no separate problem credit for the transfer or finite count helpers. General d,r, complete-graph asymptotics and worldwide priority remain outside this conclusion."))),
                DescribeRole.Theorem, new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mertens-2005-range-two-stable-matching"), ResolutionKind.Proved)))));

    private static Formula ProbabilityFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Exists, Sp, F.Id("q"), Comma, F.Id("c"), Comma, F.Id("C"), Colon, Mathbb, Grp(F.Id("R")), Comma,
        D(0), Lt, Sp, F.Id("q"), Lt, D(1), Land,
        D(0), Lt, Sp, F.Id("c"), Land, D(0), Lt, Sp, F.Id("C"), Land, RowBreak,
        Forall, Sp, F.Id("n"), Colon, Mathbb, Grp(F.Id("N")), Comma,
        D(2), Le, Sp, F.Id("n"), Rightarrow,
        F.Id("c"), F.Id("q"), Caret, Grp(F.Id("n"), Plus, D(5)), Le, Sp,
        F.Id("p"), Open, F.Id("n"), Close, Le, Sp,
        F.Id("C"), F.Id("q"), Caret, Grp(F.Id("n"), Plus, D(5)),
        End, Grp(F.Id("gathered"))));
}
