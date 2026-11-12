using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.ZeroDivisor;

internal sealed class RatherProblemOneDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original native three-prime independence-polynomial question with its full support.",
        H("Rather's three-prime graph"),
        Blocks(Describe.Lean(DescribeId.Create("rather-native-problem-one"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne.rather_problem_one"),
            H("All primes, attained independence number and weak unimodality"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature("rather2026zerodivisor"),
            Blocks(
                Paragraph(Text("For every three natural-number primes p<q<r, including p=2, let G be the actual zero divisor graph of ZMod(p*q*r). Its vertices are nonzero elements with a nonzero annihilator, and two distinct vertices are adjacent precisely when their product is zero. Let s(k) be the integer coefficient at natural rank k of the native independence polynomial on the full actual vertex set. Set a=p-1, b=q-1, c=r-1 and N=max(ab+ac+bc,c+ac+bc). Then N is at least fourteen and equals the graph's independence number. There exists an actual independent finite vertex set of cardinality N. Every coefficient through N is strictly positive and every coefficient after N is zero. For every k at least one, s(k-1)s(k+1) is at most s(k) squared. There is a peak m at most N such that s is weakly increasing on all natural indices at most m and weakly decreasing on all natural indices at least m, including the zero tail.")),
                Paragraph(Text("Distinct primes give Mathlib's native Chinese remainder equivalence. Its three finite fields satisfy the ordered-cardinality hypotheses of the general native coefficient theorem. Coefficient positivity at N supplies a nonempty family of actual independent N-subsets. Conversely, an independent set above N would give a positive coefficient in the zero tail. A maximum independent set therefore has cardinality exactly N.")),
                Paragraph(Text("Cast the positive coefficients to the reals and choose a maximum on the finite interval from zero through N. The existing strict log-concavity peak lemmas give strict adjacent steps away from the two immediate boundaries of this selected peak; maximality gives the weak inequalities at those boundaries. Chaining adjacent steps gives weak monotonicity on each side. At every log-concavity center at least N, the right neighboring coefficient vanishes, so the endpoint and the whole zero tail satisfy the same inequality.")),
                Paragraph(Text("The statement is Problem 1 of arXiv:2606.04789v1 on printed page 24. The native support formula is Theorem 4.1 on printed pages 18–20. This consumer and its coefficient argument are repository derivations; no assumed coefficient formula, finite prime bound or exclusion of the prime two is used."))),
            DescribeRole.Theorem))));
}
