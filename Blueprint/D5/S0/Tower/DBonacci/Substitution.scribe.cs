using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacci;

internal sealed class DBonacciSubstitutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var d = Id("d");
        var q = Id("Q");
        var f = Id("f");
        var i = Id("i");
        var j = Id("j");
        var naturals = Id("N");

        return DocumentDefinition.Create(ScribeNode.Create(
            "One-level refinement of d-bonacci names realizes a uniform finite gap substitution.",
            H("D-Bonacci Substitution"),
            Blocks(
                Paragraph(Text(
                    "Appending a final false digit embeds the old layer without changing values. "
                    + "Deleting the final digit shows that every genuinely new name ends in true "
                    + "and that at most one such value lies inside a coarse adjacent interval.")),
                Describe.Lean(
                    DescribeId.Create("d-bonacci-level-embedding"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/Substitution.levelEmbedding"),
                    H("D-bonacci level embedding"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("d"),
                        naturals,
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("Q"),
                            naturals,
                            Equal(
                                Call("levelEmbedding", d, q, i),
                                Call("indexOf", Add(q, Num(1)),
                                    Call("appendZero", Call("nameAt", d, q, i))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The fine index is obtained by adjoining one final false digit to the "
                        + "coarse name and applying the canonical fine-level index equivalence."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("d-bonacci-level-embedding-preserves-value"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/Substitution.levelEmbedding_value"),
                    H("Level embedding preserves value"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("d"),
                        naturals,
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("Q"),
                            naturals,
                            Equal(
                                Call("indexedValue", d, Add(q, Num(1)),
                                    Call("levelEmbedding", d, q, i)),
                                Call("indexedValue", d, q, i))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The appended false digit contributes zero and every preceding digit "
                        + "retains its exponent."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("new-d-bonacci-indices-end-in-true"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/Substitution.new_index_iff_last_true"),
                    H("New indices end in true"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("j"),
                        Call("fineIndex", d, q),
                        Equal(
                            Call("isNewIndex", d, q, j),
                            Call("lastDigitTrue", Call("nameAt", d, Add(q, Num(1)), j))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "A fine name ending in false is the extension of its truncation. A name "
                        + "ending in true cannot lie in that image, so the characterization is exact."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("d-bonacci-gap-length-replacement"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/Substitution.gapLength_succ_substitution"),
                    H("Positive labels split into top and predecessor"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("f"),
                        naturals,
                        Equal(
                            Call("gapLength", d, q, Add(f, Num(1))),
                            Add(
                                Call("gapLength", d, Add(q, Num(1)),
                                    Add(d, Call("neg", Num(1)))),
                                Call("gapLength", d, Add(q, Num(1)), f))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The reciprocal Perron equation identifies one new top-label segment. "
                        + "The remaining reciprocal-power prefix is exactly label f one level finer."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("general-d-bonacci-gap-substitution"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/Substitution.dbonacci_gap_substitution"),
                    H("General d-bonacci gap substitution"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("f"),
                        naturals,
                        Equal(
                            Call("substitute", d, f),
                            Call("zeroOrSuccessorReplacement", d, f)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "A coarse zero label contains no new name and becomes the single fine "
                            + "label d minus one. A coarse successor label f plus one contains one "
                            + "new name and becomes labels d minus one followed by f.")),
                        Paragraph(Text(
                            "Finite measurements for d in {2,3,4} and Q in {3,4,5} were evaluated "
                            + "by executable prefix-code enumeration, even-code embedded endpoints, "
                            + "and the frozen fine run-budget gap lists before the general proof. The "
                            + "code scan is proved equal to formal run admissibility. The first whole-word "
                            + "flatMap conjecture failed because a trailing fine gap can lie beyond the "
                            + "last embedded coarse name; the local interval law held.")),
                        Paragraph(Text(
                            "Repository search found the frozen Golden and Tribonacci refinement "
                            + "templates. Pinned mathlib supplies Fin.snoc, Fin.init, "
                            + "Fin.snoc_init_self, Fin.sum_univ_castSucc, and Fin.card_Ioo. GitHub "
                            + "Lean-code search found uses of those tuple lemmas but no general "
                            + "d-bonacci gap-substitution theorem."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("order-three-substitution-compatibility"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/Substitution.gapLabelSubstitution_three_compatible"),
                    H("Order-three substitution compatibility"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("f"),
                        Call("Fin", Num(3)),
                        Equal(
                            Call("mapToTribonacci", Call("substitute", Num(3), f)),
                            Call("tribonacciSubstitute", Call("mapToTribonacci", f))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Labels zero, one, and two map respectively to small, combined, and large. "
                        + "Under that explicit map, the general substitution is pointwise equal to "
                        + "the frozen three-letter substitution."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacci/Gaps")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Tribonacci/Substitution")),
            ]));
    }
}
