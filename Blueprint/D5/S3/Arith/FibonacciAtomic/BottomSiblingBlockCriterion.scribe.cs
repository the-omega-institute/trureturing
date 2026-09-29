using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class BottomSiblingBlockCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/BottomSiblingBlockCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Fibonacci prefixes and globally attached words define the target; an actual bounded-word nonconverse is proved.",
        H("Actual Sources and Bottom Sibling Blocks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-fibonacci-reset-prefix"),
                DeclarationHandle.Create(Prefix + "ActualPrefix"),
                H("One actual prefix is fixed through every reset"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An ActualPrefix consists of an initialization bit epsilon and a finite "
                        + "word past over the literal window alphabet 000, 100, 010, 101, 001. "
                        + "The original transition run, starting from (epsilon,epsilon), must "
                        + "return the live tag (true,true). Its integer is epsilon plus the "
                        + "low-to-high Fibonacci value of flatten(past), with initial next "
                        + "weights (2,3). Its next row is advance(length(flatten(past)),(2,3)). "
                        + "The KnownRowFiber at modulus H and row (u,v) contains precisely "
                        + "these actual prefixes whose computed next row reduces to (u,v). "
                        + "No residue or surjectivity witness is stored in a source.")),
                    Paragraph(Text(
                        "For natural H and a selected source, rawGcd resets to that exact "
                        + "initialization and past, appends one literal suffix, and applies "
                        + "the original End operation to return gcd(N,H) or the common error. "
                        + "rawIndex uses the same operation with H/gcd(N,H). A zero residue "
                        + "therefore still denotes a positive actual integer, never a zero "
                        + "source. The two initializations belong to the candidate family; "
                        + "a selected source does not change between queries."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("globally-attached-word-family"),
                DeclarationHandle.Create(Prefix + "FiniteIdentifiable"),
                H("A finite adaptive protocol uses only available global words"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix natural window limit t, modulus H, an actual known row (u,v) "
                        + "in ZMod H, and a finite subset available of SuccessfulWord t. "
                        + "A member of available is a complete successful literal word, "
                        + "including the empty word when selected. Its global center is "
                        + "minus its Fibonacci value modulo H. The centers set is the image "
                        + "of available, so duplicate centers are permitted. The local center "
                        + "set for each prime factor p of H is the projection of this same "
                        + "global image to ZMod(p^factorization(H,p)); independently chosen "
                        + "prime-axis centers are not added.")),
                    Paragraph(Text(
                        "A protocol's query type is the subtype of available words, and its "
                        + "answer type is Option Nat. At each node it may branch on the full "
                        + "raw gcd or the common error. FiniteIdentifiable means that the "
                        + "actual source residue modulo H factors through the complete "
                        + "transcript of some finite such protocol. The empty available set "
                        + "is included in the definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bottom-sibling-block-target"),
                DeclarationHandle.Create(Prefix + "Target"),
                H("The complete bottom sibling block claim remains open"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix H at least 2, t at least 0, a known row (u,v) in ZMod H, "
                        + "and an actual prefix computing that row. Target is the conjunction "
                        + "of seven propositions. First, one common past length realizes every "
                        + "residue in ZMod H by an actual source in that known-row fiber. "
                        + "Second, every actual "
                        + "source has positive integer value. Third, on the known-row fiber "
                        + "equality of all original raw gcd End answers over every literal "
                        + "suffix is exactly equality of source residues. Fourth, equality "
                        + "of all original H/gcd End answers is equivalent to equality of "
                        + "all original gcd End answers. Fifth, for every finite available "
                        + "family of successful literal words, finite adaptive "
                        + "identification by raw gcd is equivalent to BottomBlocks.")),
                    Paragraph(Text(
                        "BottomBlocks requires that, for each prime factor p of H, with "
                        + "e=factorization(H,p), every fiber of reduction from ZMod(p^e) "
                        + "to ZMod(p^(e-1)) contain at least p-1 projected centers. This "
                        + "includes e=1, and the available set may be empty. Sixth, when "
                        + "BottomBlocks holds for all successful words of length at most t, "
                        + "p^(e-1)(p-1) is at most Fibonacci(3t+1) for every such prime p. "
                        + "The seventh clause requires an actual source of integer value "
                        + "five and an available "
                        + "SuccessfulWord family at H=4 and t=2 whose centers have cardinality "
                        + "two but fail BottomBlocks. This declaration is a proposition "
                        + "definition and supplies no proof of the full conjunction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-common-depth-fullness"),
                DeclarationHandle.Create(Prefix + "actual_common_depth_fullness"),
                H("One returned actual row contains every residue at a shared depth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For H at least two and a row (u,v) computed by an actual literal "
                    + "prefix, there is one positive window depth j such that every "
                    + "residue modulo H is realized by a positive actual prefix of that "
                    + "same depth, computed row and terminal tag (true,true). The proof "
                    + "uses the successor graph to realize every integer in the "
                    + "Fibonacci interval [F_(3j+2), F_(3j+3)), packs its legal digits "
                    + "into original three-bit windows with a computed terminal tag, "
                    + "and returns the modular row by a finite permutation period. "
                    + "The initialization bit may vary across candidate sources. "
                    + "This establishes the actual-source fullness clause; it does not "
                    + "establish the raw gcd, future, adaptive or count clauses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-bounded-word-nonconverse"),
                DeclarationHandle.Create(Prefix + "actual_nonconverse"),
                H("A real successful-word family misses a sibling block"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At H=4, epsilon=false and past=[001] give an actual source of value "
                    + "five, hence positive with residue one modulo four, "
                    + "with computed next row (0,1) modulo four and live tag (true,true). "
                    + "The available successful words are the empty word and [010,001], "
                    + "both bounded by two windows. Their global centers are exactly "
                    + "{0,2}. This set has the necessary cardinality two, but the odd "
                    + "bottom sibling block contains no available center. The statement "
                    + "does not establish the general finite-identification criterion."))),
                DescribeRole.Theorem))));
}
