using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class HomometricTripleCollisionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/HomometricTripleCollision";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two nine-point spectra share every directed difference count and have different disjoint triple counts.",
        H("Equal pair differences and unequal disjoint triple collisions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("difference-profile-determination"),
                DeclarationHandle.Create(Owner + ".differencesDetermineTripleMass"),
                H("Determination by the signed difference profile"),
                StatementSource.FromAuthor(Claim()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The maps A and B are injective. For any integer k, D(A,k) counts "
                    + "all ordered pairs of indices in A whose frequency difference is k. "
                    + "R(A) counts ordered pairs of ordered triples in A of equal sum "
                    + "with disjoint index supports. Repeated indices within a triple are allowed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("signed-differences-do-not-determine-triple-mass"),
                DeclarationHandle.Create(Owner + ".differences_do_not_determine_triple_mass"),
                H("The determination claim is false"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, F.Id("Determination")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take the nine pair sums of {0,1,3} and {0,4,9} for A. For B, take "
                        + "the nine pair differences and shift each by 9. Both sets lie in [0,12]. "
                        + "For each ordered pair of grid indices, exchange the two coordinates "
                        + "from the second factor. This is an involution that preserves the signed "
                        + "gap when transferring from A to B.")),
                    Paragraph(Text(
                        "Counting the admissible right triples for every left triple gives "
                        + "5976 for A and 5952 for B. The count uses exact integral sums, so it "
                        + "also gives the unit-weight near-collision mass for each real resolution "
                        + "from zero inclusive to one exclusive."))),
                DescribeRole.Theorem))));

    private static Formula Claim()
    {
        var a = F.Id("A");
        var b = F.Id("B");
        var k = F.Id("k");
        return Disp(new Formula.Aligned([
            Seq(Amp, F.Id("Determination"), Sp, Iff, Sp, Forall, Sp, a, Comma, b, Colon, Sp,
                Call("Fin", D(9)), Sp, Rightarrow, Sp, Mathbb, Grp(F.Id("N")), Comma),
            Seq(Amp, Open, Call("Injective", a), Sp, Land, Sp, Call("Injective", b),
                Sp, Land, Sp, Open, Forall, Sp, k, Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")),
                Comma, Sp, Call("D", a, k), Sp, Eq, Sp, Call("D", b, k), Close, Close),
            Seq(Amp, Quad, Longrightarrow, Sp, Call("R", a), Sp, Eq, Sp, Call("R", b), Dot)
        ]));
    }
}
