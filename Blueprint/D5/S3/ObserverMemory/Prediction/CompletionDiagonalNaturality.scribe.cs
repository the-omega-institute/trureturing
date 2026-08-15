using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class CompletionDiagonalNaturalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Projection to the complete future quotient commutes with twisted diagonalization.",
        H("Completion Diagonal Naturality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("completion-quotient-commutes-with-twisted-diagonalization"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Prediction/CompletionDiagonalNaturality."
                    + "completion_quotient_diagonal_naturality"),
                H("The complete quotient projection commutes with twisted diagonalization"),
                StatementSource.FromAuthor(NaturalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let tau update a state type Y, let q read Y into O, and let E be a "
                        + "Y-valued table on an address type A. The complete itinerary sends a "
                        + "state to all of its future q-readouts. Write brackets for the class "
                        + "in the quotient by equality of complete itineraries, and let Uq be "
                        + "the canonical update transported to that quotient.")),
                    Paragraph(Text(
                        "Projecting the tau-twisted diagonal of E pointwise gives exactly the "
                        + "Uq-twisted diagonal of the pointwise projected table. This is the "
                        + "single equality asserted by the source theorem; no clause is dropped "
                        + "and no commutation hypothesis is added.")),
                    Paragraph(Text(
                        "The proof derives the quotient projection's commutation with tau from "
                        + "the frozen complete-itinerary construction, then applies the exact "
                        + "repository theorem coordinate_restriction_naturality at the identity "
                        + "address embedding. The result needs no finiteness assumption, so it "
                        + "specializes to the source section's finite state setting.")),
                    Paragraph(Text(
                        "Repository search found those two supporting declarations but no "
                        + "duplicate of this quotient diagonal identity. Loogle found the exact "
                        + "Quotient.map_mk computation; the existing transported quotient update "
                        + "is reused instead. LeanSearch's query endpoint returned HTTP 404."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Apply2(Formula function, Formula first, Formula second) =>
        Apply(Apply(function, first), second);

    private static Formula ClassOf(Formula value) =>
        Seq(OpenBracket, value, CloseBracket);

    private static Formula NaturalityFormula()
    {
        Formula aType = F.Id("A");
        Formula yType = F.Id("Y");
        Formula outputType = F.Id("O");
        Formula tau = F.Id("tau");
        Formula q = F.Id("q");
        Formula table = F.Id("E");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula projectedDiagonal = Seq(
            Open, a, Sp, Mapsto, Sp,
            ClassOf(Apply(tau, Apply2(table, a, a))), Close);
        Formula projectedTable = Seq(
            Open, a, Comma, Sp, b, Sp, Mapsto, Sp,
            ClassOf(Apply2(table, a, b)), Close);

        return Disp(Seq(
            Forall, Sp, aType, Comma, Sp, yType, Comma, Sp, outputType,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            tau, Colon, Sp, new Formula.TypeArrow(yType, yType), Comma, Sp,
            q, Colon, Sp, new Formula.TypeArrow(yType, outputType), Comma, Esc,
            table, Colon, Sp,
            new Formula.TypeArrow(aType, new Formula.TypeArrow(aType, yType)), Comma, Esc,
            projectedDiagonal, Sp, Eq, Sp,
            Call("diagonal", Call("quotientUpdate", tau, q), projectedTable), Dot));
    }
}
