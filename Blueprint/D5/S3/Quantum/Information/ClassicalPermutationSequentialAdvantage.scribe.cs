using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class ClassicalPermutationSequentialAdvantageDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/ClassicalPermutationSequentialAdvantage";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/bavarescomuraoquintino2022unitarydiscrimination");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two adaptive queries distinguish four permutations with success one, while parallel success is at most three quarters.",
        H("A sequential advantage for classical permutation discrimination"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("classical-permutation-parallel-success"),
                DeclarationHandle.Create(Module + ".parallelSuccess"),
                H("Average success for two parallel queries"),
                StatementSource.FromAuthor(Disp(ParallelFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The prior p assigns probabilities to m permutations of Fin n. A probability vector q selects an ordered pair of inputs before either output is observed. "
                    + "For each input pair and output pair, the probability vector δ specifies the distribution of the guessed label. "
                    + "The average probability of a correct guess sums over the true label and the chosen input pair. "
                    + "This is the classical two-query form of the average-success objective and parallel strategy described in main.tex, lines 178–186 and 232, "
                    + "for the permutation setting of line 514. The simplex weights are evaluated through Finsupp.toFun, and each permutation through Equiv.toFun."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("classical-permutation-sequential-success"),
                DeclarationHandle.Create(Module + ".sequentialSuccess"),
                H("Average success for two sequential queries"),
                StatementSource.FromAuthor(Disp(SequentialFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The first input has distribution q₁. After observing the first input x₁ and its output π i x₁, the second input has distribution q₂ x₁ (π i x₁). "
                    + "The decision distribution δ depends on both inputs and both outputs in transcript order. "
                    + "Multiplying these conditional probabilities and averaging over the prior gives the success probability. "
                    + "This specializes the discrimination objective of main.tex, lines 178–186, and the sequential strategy of line 243 to the classical permutation setting of line 514. "
                    + "All probability vectors and all such conditional probability vectors are allowed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("classical-permutation-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("A strict advantage over every parallel strategy"),
                StatementSource.FromAuthor(Disp(Equal(
                    Typed(Local("claim"), Qualified("Prop")), Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "There are natural numbers n and m, a prior p on m permutations π of Fin n, a sequential strategy q₁, q₂, δ, and a real number c "
                    + "such that every parallel input distribution q and every parallel decision distribution d have success at most c, "
                    + "whereas the chosen sequential strategy has success strictly greater than c. "
                    + "The same unknown permutation is queried twice in both strategies. "
                    + "This is an existential two-query formulation of the classical permutation question in main.tex, line 514. "
                    + "A single ensemble with two uses suffices for this existence question."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("classical-permutation-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Perfect adaptive discrimination and a parallel upper bound"),
                StatementSource.FromAuthor(Disp(Local("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take n = 6 and m = 4 with the uniform prior. The four permutations, in label order, are the identity, "
                        + "the transposition (2 3), the transposition (0 1), and the product (0 1)(4 5). "
                        + "First query 0. When its output is 0, query 2; otherwise query 4. "
                        + "If the first output is 0, guess label 0 when the second output is 2 and label 1 otherwise. "
                        + "If the first output is not 0, guess label 2 when the second output is 4 and label 3 otherwise. "
                        + "The four possible output transcripts are (0,2), (0,3), (1,4), and (1,5), respectively. "
                        + "Thus the decision is correct for each label and the average sequential success is 1.")),
                    Paragraph(Text(
                        "For every fixed input pair x, at least one of three equalities of output pairs holds: "
                        + "labels 0 and 1 give the same pair, labels 0 and 2 give the same pair, or labels 2 and 3 give the same pair. "
                        + "Indeed, two input symbols cannot meet all three disjoint blocks {0,1}, {2,3}, and {4,5}. "
                        + "Omitting {2,3} gives the first equality, omitting {0,1} gives the second, and omitting {4,5} gives the third.")),
                    Paragraph(Text(
                        "For any probability vector, the weights of two distinct labels sum to at most 1, because all weights are nonnegative and their total is 1. "
                        + "Now fix x and an arbitrary parallel decision rule. Each of the four correct-label probabilities is at most 1. "
                        + "Choose one of the three equalities above. The two coinciding output pairs use the same decision distribution, "
                        + "so their correct-label probabilities sum to at most 1; the other two probabilities contribute at most 1 each. "
                        + "The sum of the four correct-label probabilities is therefore at most 3.")),
                    Paragraph(Text(
                        "Under the uniform prior each label has weight 1/4. Interchanging the finite sums expresses parallel success as the q-weighted average, "
                        + "over input pairs x, of one quarter of the sum just bounded. "
                        + "Nonnegativity of each q weight preserves the bound 3/4, and the weights of q sum to 1. "
                        + "Hence every randomized parallel strategy has success at most 3/4. "
                        + "Choose c = 3/4. The sequential success is 1 and 3/4 < 1, giving the asserted strict advantage."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bavaresco-murao-quintino-2022-classical-permutation-sequential-advantage"),
                    ResolutionKind.Proved)))));

    private static Formula ParallelFormula()
    {
        Formula output = Pair(Permute(X("i"), At(Qualified("Prod", "fst"), X("x"))),
            Permute(X("i"), At(Qualified("Prod", "snd"), X("x"))));
        Formula sum = SumOver("i", FinOf(X("m")), Multiply(Weight(X("p"), X("i")),
            SumOver("x", InputPair(), Multiply(Weight(X("q"), X("x")),
                Weight(At(DeltaLower, X("x"), output), X("i"))))));
        return EnsembleBinders(All("q", Simplex(InputPair()), All("δ", ParallelDecision(),
            Equal(Typed(LocalCall("parallelSuccess", X("p"), Pi, X("q"), DeltaLower), Reals()), sum))));
    }

    private static Formula SequentialFormula()
    {
        Formula firstOutput = Permute(X("i"), X("x₁"));
        Formula secondOutput = Permute(X("i"), X("x₂"));
        Formula decision = At(DeltaLower, X("x₁"), firstOutput, X("x₂"), secondOutput);
        Formula sum = SumOver("i", FinOf(X("m")), Multiply(Weight(X("p"), X("i")),
            SumOver("x₁", FinOf(X("n")), Multiply(Weight(X("q₁"), X("x₁")),
                SumOver("x₂", FinOf(X("n")), Multiply(
                    Weight(At(X("q₂"), X("x₁"), firstOutput), X("x₂")), Weight(decision, X("i"))))))));
        return EnsembleBinders(All("q₁", Simplex(FinOf(X("n"))), All("q₂", SecondDistribution(),
            All("δ", SequentialDecision(), Equal(
                Typed(LocalCall("sequentialSuccess", X("p"), Pi, X("q₁"), X("q₂"), DeltaLower), Reals()), sum)))));
    }

    private static Formula ClaimBody()
    {
        Formula bound = All("q", Simplex(InputPair()), All("d", ParallelDecision(),
            new Formula.Relation(LocalCall("parallelSuccess", X("p"), Pi, X("q"), X("d")),
                FormulaRelationOperator.LessThanOrEqual, X("c"))));
        Formula advantage = new Formula.Relation(X("c"), FormulaRelationOperator.LessThan,
            LocalCall("sequentialSuccess", X("p"), Pi, X("q₁"), X("q₂"), DeltaLower));
        return Some("n", Naturals(), Some("m", Naturals(), Some("p", Simplex(FinOf(X("m"))),
            Some("π", PermutationFamily(), Some("q₁", Simplex(FinOf(X("n"))),
                Some("q₂", SecondDistribution(), Some("δ", SequentialDecision(), Some("c", Reals(),
                    new Formula.Logic(Parenthesized(bound), FormulaLogicOperator.And, Parenthesized(advantage))))))))));
    }

    private static Formula EnsembleBinders(Formula body) => All("n", Naturals(), All("m", Naturals(),
        All("p", Simplex(FinOf(X("m"))), All("π", PermutationFamily(), body))));
    private static Formula PermutationFamily() => Arrow(FinOf(X("m")),
        At(Qualified("Equiv", "Perm"), FinOf(X("n"))));
    private static Formula InputPair() =>
        Parenthesized(Seq(FinOf(X("n")), Sp, Times, Sp, FinOf(X("n"))));
    private static Formula ParallelDecision() => Arrow(InputPair(), Arrow(InputPair(), Simplex(FinOf(X("m")))));
    private static Formula SecondDistribution() =>
        Arrow(FinOf(X("n")), Arrow(FinOf(X("n")), Simplex(FinOf(X("n")))));
    private static Formula SequentialDecision() => Arrow(FinOf(X("n")), Arrow(FinOf(X("n")),
        Arrow(FinOf(X("n")), Arrow(FinOf(X("n")), Simplex(FinOf(X("m")))))));
    private static Formula Permute(Formula i, Formula x) =>
        At(Qualified("Equiv", "toFun"), At(Pi, i), x);
    private static Formula Weight(Formula p, Formula i) => At(Qualified("Finsupp", "toFun"),
        At(Qualified("Convexity", "StdSimplex", "weights"), p), i);
    private static Formula Simplex(Formula index) => At(Qualified("Convexity", "StdSimplex"), Reals(), index);
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Information",
        "ClassicalPermutationSequentialAdvantage", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula X(string name) => name switch
    {
        "π" => Pi,
        "δ" => DeltaLower,
        "q₁" => new Formula.Subscript(F.Id("q"), D(1)),
        "q₂" => new Formula.Subscript(F.Id("q"), D(2)),
        "x₁" => new Formula.Subscript(F.Id("x"), D(1)),
        "x₂" => new Formula.Subscript(F.Id("x"), D(2)),
        _ => F.Id(name),
    };
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
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
}
