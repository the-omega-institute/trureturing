using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class CoordinateColourOrbitDocument : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/ConceptDynamics/Attribution/CoordinateColourOrbit.universally_four_dvd_iff";

    private static Formula V(string value) => F.Id(value);
    private static Formula Apply(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula FlagValue(string profile, string coordinate) =>
        Apply(V(profile), V(coordinate));
    private static Formula HasFalseCoordinate(string profile, string coordinate) =>
        Seq(Open, Exists, Sp, V(coordinate), Sp, InMacro, Sp, V("I"), Comma, Sp,
            FlagValue(profile, coordinate), Sp, Eq, Sp, D(0), Close);
    private static Formula Statement() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, V("m"), Sp, InMacro, Sp, V("M"), Comma, Sp, D(4),
            Sp, Mid, Sp, Sum, Underscore, Grp(V("c"), Comma, V("d")),
            Sp, Apply(V("m"), Seq(Open, V("p"), Comma, V("c"), Close),
                Seq(Open, V("q"), Comma, V("d"), Close))),
        Seq(Iff, Sp, V("p"), Sp, Neq, Sp, V("q"), Sp, Land, Sp,
            HasFalseCoordinate("p", "i"), Sp, Land, Sp, HasFalseCoordinate("q", "j"))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A pair of distinct Boolean profiles with nontrivial colour shifts has four equally weighted colour pairs.",
        H("Fourfold counts for coordinate colour orbits"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coordinate-colour-orbits"),
                DeclarationHandle.Create(Result),
                H("Exactly when every invariant count is divisible by four"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let I be finite and take two Boolean profiles p and q on I. " +
                        "The group of binary vectors acts on an output by keeping its profile " +
                        "and adding to its binary colour the sum of the acting coordinates where " +
                        "that profile is false. The set M consists of natural-number matrices on " +
                        "pairs of coloured outputs invariant under the diagonal action. " +
                        "The sum runs over both binary colours of each profile.")),
                    Paragraph(Text("A coordinate where the profiles differ controls one colour. " +
                        "Choose a false coordinate of the other profile to set its shift, and " +
                        "correct any effect on the first colour using the first coordinate. " +
                        "Surjectivity forces equal matrix entries at all four colour pairs.")),
                    Paragraph(Text("If one profile is everywhere true, its colour does not move. " +
                        "The two pairs with that colour zero give an invariant count of two. " +
                        "If the profiles coincide, the two pairs with equal colours give the " +
                        "same count. In each case the matrix is zero away from the given " +
                        "profile pair."))),
                DescribeRole.Theorem))));
}
