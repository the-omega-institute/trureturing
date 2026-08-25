using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Embeddings;

internal sealed class FractionalIdealPrimeValuationFaithfulnessDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Factorization/Embeddings/FractionalIdealPrimeValuationFaithfulness."
            + "prime_valuation_observers_faithful";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All nonzero-prime valuation coordinates faithfully recover a nonzero fractional ideal.",
        H("Fractional-Ideal Prime-Valuation Faithfulness"),
        Blocks(Describe.Lean(
            DescribeId.Create("prime-valuation-observers-faithful"),
            DeclarationHandle.Create(Declaration),
            H("All prime-ideal valuations determine the fractional ideal"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let R be a Dedekind domain and K a fraction field of R. The two "
                        + "objects are nonzero fractional ideals, exactly the carrier on "
                        + "which the prime-ideal exponents form group coordinates.")),
                Paragraph(Text(
                    "Each element of the height-one spectrum represents a nonzero prime "
                        + "ideal. The displayed premise compares the canonical integer "
                        + "count at every such prime.")),
                Paragraph(Text(
                    "The pinned library reconstruction theorem expresses each nonzero "
                        + "fractional ideal as the finite product of those prime powers. "
                        + "Pointwise equality of all exponents therefore identifies the "
                        + "two ideals."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula ring = F.Id("R");
        Formula field = F.Id("K");
        Formula first = F.Id("I");
        Formula second = F.Id("J");
        Formula prime = F.Id("p");

        Formula structures = Seq(
            Call("CommRing", ring), Sp, Land, Sp,
            Call("Field", field), Sp, Land, Sp,
            Call("Algebra", ring, field), Sp, Land, Sp,
            Call("IsFractionRing", ring, field), Sp, Land, Sp,
            Call("IsDedekindDomain", ring));
        Formula carrier = Call("NonzeroFractionalIdeals", ring, field);
        Formula spectrum = Call("HeightOneSpectrum", ring);
        Formula equalCoordinates = Seq(
            Forall, Sp, prime, InMacro, Sp, spectrum, Comma, Sp,
            Call("count", field, prime, first), Sp, Eq, Sp,
            Call("count", field, prime, second));

        return Disp(Seq(
            Forall, Sp, ring, Comma, Sp, field, Colon, Sp, F.Id("Type"), Comma,
            RowBreak, Grp(),
            Grp(structures), Sp, Rightarrow,
            RowBreak, Grp(),
            Forall, Sp, first, Comma, Sp, second, InMacro, Sp, carrier, Comma,
            RowBreak, Grp(),
            Grp(equalCoordinates), Sp, Rightarrow, Sp,
            first, Sp, Eq, Sp, second, Dot));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
