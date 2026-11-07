using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TorusTilings;

internal sealed class KageyKeehnRectangularTorusDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TorusTilings/KageyKeehnRectangularTorus.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/kagey2023rectangulartorus");

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
                        "For arbitrary positive natural dimensions n and m, let T be the actual right R-set of decorated "
                        + "tile designs, let f : ZMod n -> ZMod m -> T, and let F : Z x Z -> T be its literal periodic "
                        + "plane lift, F(x,y) = f([x]n,[y]m) for every pair of integers. The source quantifies over an "
                        + "applicable R <= D8 and over h in {r, r3, rf, r3f} belonging to R. The internal constructors "
                        + "are deliberately separate from those source labels: source r has A_r(x,y)=(-y,x) and uses "
                        + "Lean a=.r3; source r3 has A_r3(x,y)=(y,-x) and uses a=.r; source rf has "
                        + "A_rf(x,y)=(y,x) and uses a=.rf; source r3f has A_r3f(x,y)=(-y,-x) and uses a=.r3f. "
                        + "In every row rho(d) is the original design action d*h. The square constants "
                        + "(q-1,0), (0,q-1), (0,0), and (q-1,q-1) illustrate the source convention for a q by q "
                        + "representative; they do not impose a D8 action on an unequal rectangle.")),
                    Paragraph(Text(
                        "Write u for the chosen integer representative of the source translation and c for the actual integral "
                        + "affine offset after the linear map. The decorated graph is sent by "
                        + "(z,d) -> (A_h(z+u)+c, d*h). Fixedness of that graph, together with uniqueness of its design "
                        + "label, gives exactly F(A_h(z+u)+c) = F(z)·h. Conversely, this covariance and bijectivity of the "
                        + "affine cell map give graph equality. Thus the theorem is instantiated with shift=u, center=c, "
                        + "the internal constructor in the table, and rho(d)=d·h; every allowed translation and center stays "
                        + "in scope, and changing u by a rectangular period is handled by the literal periodic lift.")),
                    Paragraph(Text(
                        "Then g = gcd(n,m) is positive and there is a genuine function H : ZMod g -> ZMod g -> T whose "
                        + "plane lift is pointwise equal to F. Thus the original decorated plane is equivalent to a g by g "
                        + "torus with the same tile type and the identical labels at every plane cell. The statement covers "
                        + "equal or unequal dimensions, unit dimensions, nonprimitive presentations, and all four actions; "
                        + "all quotient representatives and the entire product quotient are included, and it makes no claim "
                        + "that the square presentation is minimal. The same T is retained: no design relabeling, orientation "
                        + "loss, or abstract period-only replacement occurs.")),
                    Paragraph(Text(
                        "The proof records the two source periods as an additive subgroup of Z x Z. Affine covariance transports "
                        + "a period through each signed swap map because the ordered shift and center combine to a fixed affine "
                        + "translation whose constant cancels after choosing a preimage. "
                        + "The four cases therefore give both coordinate periods n and m. Nat.gcd_eq_gcd_ab supplies the two "
                        + "gcd periods by integer combinations, and canonical ZMod representatives define H; the period subgroup "
                        + "proves representative independence and the exact plane-lift identity. No unequal finite quotient is given "
                        + "a fictitious D8 action, and no color-triviality or extra source hypothesis is used."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kagey-keehn-2023-rectangular-torus"),
                    ResolutionKind.Proved))), []));
}
