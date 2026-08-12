using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower;

internal sealed class GoldenSubstitutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var q = Id("Q");
        var naturals = Id("N");

        return DocumentDefinition.Create(ScribeNode.Create("Level refinement inserts one name per large gap at the inverse golden fraction.",
            H("Golden Substitution"),
            Blocks(
                Paragraph(Text(
                    "Refining the golden tower by one level embeds the old names into the new "
                    + "enumeration and inserts fresh names. The insertion pattern is the tower's "
                    + "own substitution dynamics acting on gap types.")),
                Describe.Lean(DescribeId.Create("level-embedding-of-old-names"),
                    DeclarationHandle.Create("D5/S0/Tower/GoldenSubstitution.levelEmbedding"),
                    H("Level embedding of old names"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                                            "Every level-Q name reappears at level Q plus one with the same value, "
                                            + "strictly monotonically, reusing the frozen enumeration vocabulary."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("inserted-name-indices"),
                    DeclarationHandle.Create("D5/S0/Tower/GoldenSubstitution.insertedNameIndices"),
                    H("Inserted name indices"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                                            "The complement of the embedded image: the fresh level-(Q+1) names that "
                                            + "refine the old gaps."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("each-large-gap-gains-exactly-one-name"),
                    DeclarationHandle.Create("D5/S0/Tower/GoldenSubstitution.golden_gap_insertion_count"),
                    H("Each large gap gains exactly one name"),
                    StatementSource.FromAuthor(new Formula.Bind(
                                            FormulaQuantifier.ForAll,
                                            FormulaIdentifier.Create("Q"),
                                            naturals,
                                            Equal(
                                                Call("insertedCount", q, Id("i")),
                                                Call("largeGapIndicator", q, Id("i"))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                                            "From level two onward a refinement step inserts exactly one new name "
                                            + "into each large gap and none into any small gap; the unique insertion "
                                            + "point splits the large gap into a new large then a new small gap at "
                                            + "the inverse-golden fraction from the left. Gap types therefore evolve "
                                            + "by the golden substitution: small becomes large, large becomes large "
                                            + "then small."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/GoldenGaps")),
            ]));
    }
}
