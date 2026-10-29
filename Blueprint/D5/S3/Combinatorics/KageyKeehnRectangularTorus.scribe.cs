using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class KageyKeehnRectangularTorusDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/KageyKeehnRectangularTorus.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/kagey2023rectangulartorus");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A decorated plane lift fixed by a translated transposing right action descends to the square torus whose side is the gcd of the source periods.",
        H("The Kagey--Keehn Rectangular-Torus GCD Descent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gcd-descent"),
                DeclarationHandle.Create(Prefix + "rectangular_torus_gcd_descent"),
                H("Every four-way transposing fixed plane descends to a gcd square"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary positive natural dimensions n and m, let T be any type, let f be a function "
                        + "from ZMod n and ZMod m into T, and let F : Z x Z -> T be its literal decorated plane lift: "
                        + "F(x,y) = f([x]n,[y]m) for every pair of integers. Choose one of the four source right actions "
                        + "r, r3, rf, or r3f. Their linear coordinate maps are respectively (y,-x), (-y,x), (y,x), and (-y,-x).")),
                    Paragraph(Text(
                        "For an arbitrary integer translation t and arbitrary tile-design map rho : T -> T, assume the "
                        + "actual plane covariance F(A z + t) = rho(F z) for every z, where A is the selected map. "
                        + "The free t includes the source cyclic shift and every affine center constant in the finite rectangular "
                        + "representatives, while rho retains an arbitrary decorated right action.")),
                    Paragraph(Text(
                        "Then g = gcd(n,m) is positive and there is a genuine function H : ZMod g -> ZMod g -> T whose "
                        + "plane lift is pointwise equal to F. Thus the original decorated plane is equivalent to a g by g "
                        + "torus with the same tile type and the identical labels at every plane cell. The statement covers "
                        + "equal or unequal dimensions, unit dimensions, nonprimitive presentations, and all four actions; "
                        + "it makes no claim that the square presentation is minimal.")),
                    Paragraph(Text(
                        "The proof records the two source periods as an additive subgroup of Z x Z. Affine covariance transports "
                        + "a period through each signed swap map because its translation cancels after choosing a preimage. "
                        + "The four cases therefore give both coordinate periods n and m. Nat.gcd_eq_gcd_ab supplies the two "
                        + "gcd periods by integer combinations, and canonical ZMod representatives define H; the period subgroup "
                        + "proves representative independence and the exact plane-lift identity. No unequal finite quotient is given "
                        + "a fictitious D8 action, and no color-triviality or extra source hypothesis is used."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kagey-keehn-2023-rectangular-torus"),
                    ResolutionKind.Proved))));
}
