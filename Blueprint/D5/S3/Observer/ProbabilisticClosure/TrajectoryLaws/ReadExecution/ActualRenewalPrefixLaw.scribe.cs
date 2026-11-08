using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution;

internal sealed class ActualRenewalPrefixLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual renewal words and exact raw-past freshness.",
        H("Actual source prefix law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-renewal-word-execution"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalPrefixLaw.actual_words"),
                H("Finite words of the saved raw execution"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use exactly ActualRenewalStopping.run, sourceBit, clock and epoch. The effective update holds every terminal state fixed and otherwise calls the same raw sampler with the next bit and raw coin. The finite zero-word recursion uses the first k coins in chronological order and the word applies the closing tick using coin k. Induction on the original raw recursion proves that the first epoch is the initial wait word and that the next epoch is the next gap word starting from the same previous epoch. No transition law or replacement chain is assumed. Wait zero, gap zero, an initially terminal state and stopping within any zero segment remain in scope."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-renewal-random-cut-freshness"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalPrefixLaw.random_cut_freshness"),
                H("Freshness after the exact raw history"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Primitive is an explicit realization interface for deterministic coordinates: for every finite gap tuple, fixed initial wait, fixed coin prefix length l and fixed adjacent block length r, their joint rectangle has the product mass from the initial measure eta, first-wait PMF w, iid-gap PMF f and iid base measure rho. Its statement contains neither a random cut nor an observer trajectory. Deriving this interface from the original source PMFs and a full product realization remains a separate obligation.")),
                    Paragraph(Text("The raw past retains the initial wait, exactly K(0) through K(n-1), the actual initial state and every coin strictly before c(n). It excludes K(n) and the next coin. For each finite source tuple a, cut(a)=u+1+sum(K(j)+1) equals the saved clock; a past event is any measurable initial-state and coin-prefix event D(a) on that slice. The coin space can be arbitrary measurable and non-atomic.")),
                    Paragraph(Text("The proof partitions over the countable finite source tuples. On each piece it proves the cut equality before applying Primitive at a deterministic offset. Appending K(n)=k multiplies the piece mass by f(k); its following k+1 original coins contribute their finite product measure. Countable additivity and nonnegative series factorization establish the displayed raw-past freshness equation. There is no conditioning by division, so null histories and zero entries are included.")),
                    Paragraph(Text("This source checkpoint does not yet prove the effective sampler row law, the finite-word integration yielding A^k C, actual initialization eta A^u C mixed by w, all-m actual cylinders, the ordinary-past Markov integral identity, or the original source PMF specialization. Those remain mathematical obligations, together with occupation, predictable payment, harmonic comparison and full original E4. No auxiliary W termination is used. Common eta, sampler, labels and rows must be retained when the theorem is applied to both targets; only w, f and the source probability law may vary."))), DescribeRole.Theorem))));
}
