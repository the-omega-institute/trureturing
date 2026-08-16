using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.Tribonacci;

internal sealed class TribonacciRepresentationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var q = Id("Q");
        var n = Id("n");
        var name = Id("name");
        var naturals = Id("N");
        Formula Weight(Formula index) => Call("T", Add(index, Num(2)));
        Formula Names(Formula length) => Call("TribonacciName", length);
        Formula Bound(Formula length) => Call("Fin", Weight(length));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Admissible Tribonacci words uniquely encode their full initial natural intervals.",
            H("Tribonacci Representation"),
            Blocks(
                Paragraph(Text(
                    "Position i carries the frozen Tribonacci weight T(i+2), fixing the basis "
                    + "as 1, 2, 4, 7, 13, and so on. The no-111 condition makes every fixed "
                    + "length layer a canonical integer representation system.")),
                Describe.Lean(
                    DescribeId.Create("tribonacci-integer-decoding"),
                    DeclarationHandle.Create("D5/S0/Tower/Tribonacci/Representation.decode"),
                    H("Tribonacci integer decoding"),
                    StatementSource.FromAuthor(Equal(
                        Call("decode", name),
                        Call("weightedTribonacciSum", name))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The definition sums T(i+2) exactly at the true positions of an "
                        + "admissible word and reuses the frozen Tribonacci sequence."))),
                    DescribeRole.Definition
                ),
                Describe.Lean(
                    DescribeId.Create("tribonacci-decoding-upper-bound"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Representation.decode_lt_tribonacci"),
                    H("Tribonacci decoding upper bound"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("name"),
                            Names(q),
                            Call("LessThan", Call("decode", name), Weight(q))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Removing three highest positions leaves a shorter admissible prefix. "
                        + "At most two of the removed positions are true, and the frozen "
                        + "three-term recurrence closes the strict bound."))),
                    DescribeRole.Theorem
                ),
                Describe.Lean(
                    DescribeId.Create("exact-maximum-tribonacci-decoding-value"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Representation.decode_max_value"),
                    H("Exact maximum Tribonacci decoding value"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        Equal(
                            Call("Maximum", Call("decodeAtLength", q)),
                            Subtract(Weight(q), Num(1))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The upper bound is attained because bounded decoding is surjective; "
                        + "therefore the largest legal value is exactly T(Q+2) minus one."))),
                    DescribeRole.Theorem
                ),
                Describe.Lean(
                    DescribeId.Create("tribonacci-decoding-is-injective"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Representation.decode_injective"),
                    H("Tribonacci decoding is injective"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        Call("Injective", Call("decodeAtLength", q)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Induction compares the highest digits. Unequal highest digits are "
                        + "separated by the strict prefix bound; equal digits cancel and reduce "
                        + "to the shorter names."))),
                    DescribeRole.Theorem
                ),
                Describe.Lean(
                    DescribeId.Create("every-bounded-natural-has-a-tribonacci-name"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Representation.exists_decode_eq"),
                    H("Every bounded natural has a Tribonacci name"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("n"),
                            Bound(q),
                            new Formula.Bind(
                                FormulaQuantifier.Exists,
                                FormulaIdentifier.Create("name"),
                                Names(q),
                                Equal(Call("decode", name), n))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The injective bounded decoder has the same finite cardinality on both "
                        + "sides by the frozen Tribonacci name-count theorem, so it is "
                        + "surjective onto the complete initial interval."))),
                    DescribeRole.Theorem
                ),
                Describe.Lean(
                    DescribeId.Create("bounded-tribonacci-decoding-is-bijective"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Representation.decode_bijective"),
                    H("Bounded Tribonacci decoding is bijective"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        Call("Bijective", Call("decodeFin", q)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Combining injectivity with the exact cardinality identity gives the "
                        + "full existence-and-uniqueness statement at every length."))),
                    DescribeRole.Theorem
                ),
                Describe.Lean(
                    DescribeId.Create("tribonacci-decoding-equivalence"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Representation.decodeEquiv"),
                    H("Tribonacci decoding equivalence"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        Call("Equiv", Names(q), Bound(q)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The equivalence packages the bounded decoder and its proved inverse "
                        + "without choosing a second ordering of the admissible words."))),
                    DescribeRole.Definition
                ),
                Describe.Lean(
                    DescribeId.Create("tribonacci-encoder-makes-the-greedy-choice"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Representation.encode_last_eq_true_iff"),
                    H("Tribonacci encoder makes the greedy choice"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("n"),
                            Call("Fin", Weight(Add(q, Num(1)))),
                            Call(
                                "Iff",
                                Equal(Call("highestDigit", Call("encode", n)), Num(1)),
                                Call("LessEqual", Weight(q), n))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The inverse selects the highest available weight exactly when that "
                        + "weight does not exceed the target, recording the usual greedy "
                        + "construction as a theorem."))),
                    DescribeRole.Theorem
                )),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Tribonacci/Names")),
            ]));
    }
}
