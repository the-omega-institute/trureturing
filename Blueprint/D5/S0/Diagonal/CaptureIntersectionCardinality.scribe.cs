using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal;

internal sealed class CaptureIntersectionCardinalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var addressCard = Call("card", Id("Address"));
        var valueCard = Call("card", Id("Y"));
        var fixedPointCard = Call("card", Call("Fix", Id("f")));
        var selectedCard = Call("card", Id("S"));
        var listingType = new Formula.TypeArrow(
            Id("Address"),
            new Formula.TypeArrow(Id("Address"), Id("Y")));
        var capturedListings = F.Seq(
            F.OpenBrace,
            F.Id("g"), F.Sp, F.Colon, F.Sp, listingType, F.Sp,
            F.Mid, F.Sp,
            F.Forall, F.Sp, F.Id("a"), F.Sp, F.InMacro, F.Sp, F.Id("S"), F.Comma, F.Esc,
            F.Id("g"), F.Open, F.Id("a"), F.Close, F.Sp, F.Eq, F.Sp,
            F.Operatorname, F.Grp(F.Id("diagonal")),
            F.Open, F.Id("f"), F.Comma, F.Sp, F.Id("g"), F.Close,
            F.CloseBrace);
        var assumptions = And(
            Equal(addressCard, Id("A")),
            Equal(valueCard, Id("n")),
            Equal(fixedPointCard, Id("k")),
            Equal(selectedCard, Id("s")),
            AtLeastOne(Id("s")));
        var count = Multiply(
            new Formula.Power(Id("k"), Id("s")),
            new Formula.Power(
                Id("n"),
                Multiply(Id("A"), Subtract(Id("A"), Id("s")))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A nonempty finite row set has an exact simultaneous twisted-diagonal capture count.",
            H("Nonempty Diagonal Capture Intersections"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("nonempty-capture-intersections-have-an-exact-cardinality"),
                    DeclarationHandle.Create(
                        "D5/S0/Diagonal/CaptureIntersectionCardinality.capture_intersection_cardinality"),
                    H("Nonempty capture intersections have an exact cardinality"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(new Formula.Logic(
                        assumptions,
                        FormulaLogicOperator.Implies,
                        Equal(Call("card", capturedListings), count)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let Address and Y be finite types, let f map Y to itself, and let S "
                            + "be a finite set of addresses. Write A for the cardinality of Address, "
                            + "n for the cardinality of Y, k for the number of fixed points of f, "
                            + "and s for the cardinality of S. When s is at least one, the number "
                            + "of listings g whose selected rows all equal the twisted diagonal of "
                            + "g is exactly k^s times n^(A*(A-s)).")),
                        Paragraph(Text(
                            "The proof reuses the general finite capture-count equivalence from "
                            + "CaptureCount and only substitutes the four named cardinalities. "
                            + "The positivity assumption reproduces the source lemma's domain; "
                            + "the underlying count theorem also holds for an empty selection."))),
                    DescribeRole.Lemma)),
            []));
    }

    private static Formula AtLeastOne(Formula value) =>
        new Formula.Relation(value, FormulaRelationOperator.GreaterThanOrEqual, Num(1));

    private static Formula And(Formula first, params Formula[] rest)
    {
        var result = first;
        foreach (var item in rest)
        {
            result = new Formula.Logic(result, FormulaLogicOperator.And, item);
        }

        return result;
    }
}
