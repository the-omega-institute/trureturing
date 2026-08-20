using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal.Equivariance;

internal sealed class TransitiveEscapeRateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var n = Id("n");
        var k = Id("k");
        var omega = Id("omega");

        var total = Equal(
            Call("card", Id("EquivariantListing")),
            new Formula.Power(n, omega));

        var escaped = Equal(
            Call("card", Call("Escaped", Id("f"))),
            Subtract(new Formula.Power(n, omega), k));

        var rate = Equal(
            Call("P", Id("esc")),
            Subtract(Num(1), new Formula.Fraction(k, new Formula.Power(n, omega))));

        const string declarationPrefix =
            "D5/S0/Diagonal/Equivariance/TransitiveEscapeRate.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "A transitive equivariant ensemble escapes at rate one minus k over n to the omega.",
            H("Transitive Escape Rate"),
            Blocks(
                Paragraph(Text(
                    "An equivariant listing is determined by its orbit coordinates: one value "
                        + "on the diagonal of each row orbit, and the remaining stabilizer "
                        + "orbit coordinates. For a transitive action there is a single row "
                        + "orbit, so the ensemble has exactly as many members as there are "
                        + "assignments to the stabilizer orbits of one address.")),
                Paragraph(Text(
                    "The escaped members of that ensemble were already counted; what was "
                        + "missing was the size of the ensemble itself, without which the "
                        + "quotient the source states cannot be formed. The orbit "
                        + "decomposition carries a bijection but asserts no cardinality, and "
                        + "the corresponding lemma inside the frozen counting module is "
                        + "private, so the count is re-derived here rather than reused.")),
                Paragraph(Text(
                    "Dividing gives the rate the source records. The three readings it lists "
                        + "are instances of that quotient, and all three take the identity "
                        + "twist, so they vary the group and not the twist. The source also "
                        + "records the general nontransitive case as open, and nothing here "
                        + "claims it.")),
                Describe.Lean(
                    DescribeId.Create("every-stabilizer-orbit-index-carries-the-diagonal"),
                    DeclarationHandle.Create(declarationPrefix + "stabilizerOrbit_card_pos"),
                    H("Every stabilizer orbit index carries the diagonal"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(
                        new Formula.Relation(
                            Num(0),
                            FormulaRelationOperator.LessThan,
                            Call("card", Call("StabilizerOrbit", Id("i")))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The diagonal orbit is a member, so the stabilizer orbit count is "
                            + "positive and the exponent arithmetic below never underflows."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("orbit-coordinates-number-n-to-the-orbit-count"),
                    DeclarationHandle.Create(declarationPrefix + "orbitParameters_card"),
                    H("Orbit coordinates number n to the orbit count"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(total)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "A diagonal value together with the off-diagonal stabilizer orbit "
                            + "coordinates gives one factor of the alphabet size for every "
                            + "stabilizer orbit of the index."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("the-transitive-ensemble-has-n-to-the-omega-members"),
                    DeclarationHandle.Create(
                        declarationPrefix + "transitive_equivariant_listing_card"),
                    H("The transitive ensemble has n to the omega members"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(total)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Transitivity makes the row orbit index unique, so the product over "
                            + "row orbits collapses to the single factor at any chosen index."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("the-escaped-fraction-is-one-minus-the-fixed-fraction"),
                    DeclarationHandle.Create(declarationPrefix + "escaped_fraction"),
                    H("The escaped fraction is one minus the fixed fraction"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(rate)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Dividing a difference of naturals by the larger one is the same as "
                            + "subtracting the quotient from one, which is the arithmetic step "
                            + "carrying the count into the rate the source writes."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("the-three-recorded-readings"),
                    DeclarationHandle.Create(declarationPrefix + "worked_rates"),
                    H("The three recorded readings"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(rate)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The regular three point, regular four point, and nonregular "
                            + "three point readings, each written as one minus the fixed "
                            + "fraction. All three take the identity twist."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("the-transitive-escape-rate-packaged"),
                    DeclarationHandle.Create(
                        declarationPrefix + "transitive_equivariant_escape_rate_package"),
                    H("The transitive escape rate packaged"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(
                        new Formula.Logic(
                            total,
                            FormulaLogicOperator.And,
                            new Formula.Logic(escaped, FormulaLogicOperator.And, rate)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "One conjunction carrying the exact rate: the ensemble size, the "
                            + "escaped count, the quotient identity, and the three recorded "
                            + "readings. The displayed formula shows the first three; the "
                            + "fourth conjunct is the readings named above."))),
                    DescribeRole.Theorem))));
    }
}
