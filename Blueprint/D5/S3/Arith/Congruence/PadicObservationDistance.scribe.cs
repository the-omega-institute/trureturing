using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class PadicObservationDistanceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first unequal prime-power reading induces the p-adic distance formula.",
        H("P-Adic Observation Distance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("observation-distance-equals-p-adic-valuation-scale"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/PadicObservationDistance."
                        + "observation_distance_eq_padic_valuation"),
                H("Observation distance equals the p-adic valuation scale"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a prime p, the precision-k reading of an integer is its residue "
                            + "modulo p^k. The observation distance between distinct integers "
                            + "is p raised to one minus the first precision at which those "
                            + "readings differ.")),
                    Paragraph(Text(
                        "The frozen precision theorem identifies that first distinguishing "
                            + "precision with one plus the p-adic valuation of x - y. "
                            + "Subtracting it from one gives the negative valuation, yielding "
                            + "the displayed distance identity."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula prime = F.Id("p");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula difference = Subtract(left, right);
        Formula distance = Call("observationDistance", prime, left, right);
        Formula valuation = Call("padicValInt", prime, difference);
        Formula scale = Seq(prime, Caret, Grp(Minus, valuation));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, prime, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma,
            RowBreak, Grp(),
            left, Comma, Sp, right, Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma,
            RowBreak, Grp(),
            Open, Call("Prime", prime), Sp, Land, Sp, left, Sp, Neq, Sp, right, Close,
            Sp, Rightarrow, Sp, distance, Sp, Eq, Sp, scale, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
