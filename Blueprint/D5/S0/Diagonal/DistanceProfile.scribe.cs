using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal;

internal sealed class DistanceProfileDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var cardA = Call("card", Id("A"));
        var cardY = Call("card", Id("Y"));
        var fixedPoints = Call("card", Call("Fix", Id("f")));
        var rowCount = Call("rowDistanceCount", Id("f"), Id("j"));
        var profileCount = Call("card", Call("distanceProfileFiber", Id("f"), Id("r")));
        var profileProduct = Call("productRows", Call("rowDistanceCount", Id("f"), Id("r")));
        var rowTail = Call("sum", rowCount, Id("j"), Id("r"), cardA);
        var tailCount = Call("card", Call("minimumDistanceListings", Id("f"), Id("r")));
        var escapedCount = Call("card", Call("positiveDistanceListings", Id("f")));
        var escapeFormula = new Formula.Power(
            Subtract(new Formula.Power(cardY, cardA), fixedPoints),
            cardA);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Diagonal Hamming-distance profiles and lower tails have exact finite counts.",
            H("Diagonal Distance Profiles"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("exact-distance-profiles-factor-rowwise"),
                    DeclarationHandle.Create("D5/S0/Diagonal/DistanceProfile.distance_profile_card"),
                    H("Exact distance profiles factor rowwise"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(Equal(profileCount, profileProduct))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For each row, the diagonal entry contributes either zero or one to "
                        + "the distance. The remaining coordinates form a finite Hamming "
                        + "sphere, whose choice count is a binomial coefficient times a power "
                        + "of one fewer than the value-set cardinality. Summing the fixed and "
                        + "nonfixed diagonal cases gives the explicit rowDistanceCount, and "
                        + "the rows then multiply independently."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("common-distance-lower-tails-are-row-powers"),
                    DeclarationHandle.Create("D5/S0/Diagonal/DistanceProfile.min_distance_tail"),
                    H("Common distance lower tails are row powers"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(Equal(
                        tailCount,
                        new Formula.Power(rowTail, cardA)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every row distance lies between zero and the address cardinality. "
                        + "Summing the exact row counts over the closed lower-tail interval and "
                        + "then multiplying over all rows yields the stated finite count."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("positive-distance-recovers-the-escape-count"),
                    DeclarationHandle.Create("D5/S0/Diagonal/DistanceProfile.min_distance_one"),
                    H("Positive distance recovers the escape count"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(Equal(escapedCount, escapeFormula))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "A listing is escaped exactly when every row has positive distance from "
                        + "the twisted diagonal. The lower-tail formula at one is identified "
                        + "with the previously frozen exact escape count through that "
                        + "equivalence, without recounting escaped listings."))),
                    DescribeRole.Theorem))));
    }
}
