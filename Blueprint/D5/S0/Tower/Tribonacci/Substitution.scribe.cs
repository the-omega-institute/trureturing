using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.Tribonacci;

internal sealed class TribonacciSubstitutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var q = Id("Q");
        var i = Id("i");
        var j = Id("j");
        var naturals = Id("N");

        return DocumentDefinition.Create(ScribeNode.Create(
            "One-level refinement of Tribonacci names realizes a three-letter gap substitution.",
            H("Tribonacci Substitution"),
            Blocks(
                Paragraph(Text(
                    "Appending a final zero embeds every old admissible name at the same real "
                    + "value. Deleting the final digit controls all fine names between two "
                    + "embedded endpoints and forces any inserted value to one exact position.")),
                Describe.Lean(
                    DescribeId.Create("level-embedding-of-tribonacci-names"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Substitution.levelEmbedding"),
                    H("Level embedding of Tribonacci names"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("i"),
                            Call("coarseIndex", q),
                            Equal(
                                Call("levelEmbedding", q, i),
                                Call("indexOf", Add(q, Num(1)),
                                    Call("appendZero", Call("nameAt", q, i))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The embedding is the fine-level index of the old word with one final "
                        + "false digit. Admissibility is preserved because no new terminal run "
                        + "of three true digits can be created."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("level-embedding-preserves-value"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Substitution.levelEmbedding_value"),
                    H("Level embedding preserves value"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("i"),
                            Call("coarseIndex", q),
                            Equal(
                                Call("indexedValue", Add(q, Num(1)),
                                    Call("levelEmbedding", q, i)),
                                Call("indexedValue", q, i))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The final false digit contributes zero, while every prior digit keeps "
                        + "the same exponent. Strict increase of indexed values then makes the "
                        + "embedding strictly monotone."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("inserted-tribonacci-name-indices"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Substitution.insertedNameIndices"),
                    H("Inserted Tribonacci name indices"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        Equal(
                            Call("insertedNameIndices", q, i),
                            Call("openIndexInterval",
                                Call("levelEmbedding", q, Call("gapLeft", q, i)),
                                Call("levelEmbedding", q, Call("gapRight", q, i)))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For a coarse adjacent interval, the inserted set is exactly the open "
                        + "finite-index interval between its two embedded endpoints."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("inserted-indices-are-between-values"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Substitution.mem_insertedNameIndices_iff"),
                    H("Inserted indices are exactly the intermediate values"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("j"),
                            Call("fineIndex", q),
                            Equal(
                                Call("member", j, Call("insertedNameIndices", q, i)),
                                Call("strictlyBetweenEndpointValues", q, i, j))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Strict monotonicity converts membership in the open index interval to "
                        + "strict inequalities between the corresponding real values."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("tribonacci-gap-insertion-count"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Substitution.tribonacci_gap_insertion_count"),
                    H("Exact Tribonacci gap insertion count"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        Equal(
                            Call("insertedCount", q, i),
                            Call("tribonacciInsertionCount", Call("gapType", q, i))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "A small coarse gap inserts no name. Large and combined coarse gaps each "
                        + "insert exactly one. Truncating a fine name proves uniqueness; the "
                        + "next-level three-gap spectrum proves existence in both non-small cases."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("tribonacci-three-letter-gap-substitution"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Substitution.tribonacci_gap_substitution"),
                    H("Tribonacci three-letter gap substitution"),
                    StatementSource.FromAuthor(new Formula.Logic(
                        Equal(
                            Call("substitute", Id("small")),
                            Call("gapWord", Id("large"))),
                        FormulaLogicOperator.And,
                        new Formula.Logic(
                            Equal(
                                Call("substitute", Id("large")),
                                Call("gapWord", Id("large"), Id("combined"))),
                            FormulaLogicOperator.And,
                            Equal(
                                Call("substitute", Id("combined")),
                                Call("gapWord", Id("large"), Id("small")))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "At level Q plus one the new large length is t^-(Q+1), the new small "
                            + "length is t^-(Q+2), and the new combined length is the sum of "
                            + "t^-(Q+2) and t^-(Q+3). The unique inserted point, when present, "
                            + "always lies one new-large length from the left endpoint.")),
                        Paragraph(Text(
                            "Pinned mathlib was searched first. Fin.snoc, Fin.init, "
                            + "Fin.sum_univ_castSucc, and Fin.card_Ioo provide the tuple, value, "
                            + "and interval infrastructure; the Tribonacci-specific dynamics are "
                            + "proved in this repository."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Tribonacci/Gaps")),
            ]));
    }
}
