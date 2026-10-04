using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras;

internal sealed class BareiRemarkThreeFiveDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/EvolutionAlgebras/BareiRemarkThreeFive.";
    private static readonly LibraryNoteRef Question =
        LibraryNoteRef.Create("D5/L/QuadraticForms/barei2026solvable");
    private static readonly LibraryNoteRef Related =
        LibraryNoteRef.Create("D5/L/QuadraticForms/hu2026idempotent");
    private static readonly LibraryNoteRef Embedding =
        LibraryNoteRef.Create("D5/L/QuadraticForms/costoya2026commutative");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A five-dimensional complex evolution algebra contains a three-dimensional "
            + "idempotent subspace with no nonzero proper idempotent subspace. "
            + "This answers the existence search in Barei's Remark 3.5.",
        H("A three-dimensional minimal idempotent subspace"),
        Blocks(
            Describe.Lean(DescribeId.Create("ambient-space"),
                DeclarationHandle.Create(Prefix + "E"), H("The ambient complex vector space"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ambient vector space has five complex coordinates. "
                    + "The product used in the theorem is bilinear and has an actual natural basis; "
                    + "associativity and a unit are not imposed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pair-product-square"),
                DeclarationHandle.Create(Prefix + "Square"), H("The square of a subspace"),
                StatementSource.FromLean(), AssessedProvenance.FromLiterature(Question),
                Blocks(Paragraph(Text("The square is the complex linear span of every product "
                    + "of two vectors from the subspace. Idempotence means equality to the subspace. "
                    + "This is a property of subspaces, rather than a restriction to coordinate spans "
                    + "or to idempotent elements."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("minimal-idempotent-existence"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Affirmative answer to Remark 3.5"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(Question, Related, Embedding),
                Blocks(
                    Paragraph(Text("Choose natural basis e1 through e5. Put u equal to their sum, "
                        + "v equal to e2 minus e3, and w equal to e4 minus e5. The basis squares are "
                        + "4u + 2w, v, -v, v + w, and -v - w; mixed basis products vanish. "
                        + "The injective linear map (a,b,c) to (a,a+b,a-b,a+c,a-c) "
                        + "identifies its range with the span of u,v,w and preserves multiplication.")),
                    Paragraph(Text("In intrinsic coordinates, the products are u squared equal to "
                        + "4u + 2w, uv equal to 2v, uw equal to 2v + 2w, and all products in "
                        + "the plane spanned by v,w equal to zero. These products span the whole "
                        + "three-dimensional space, so its square equals itself.")),
                    Paragraph(Text("Let a multiplication-closed subspace contain x = au + bv + cw "
                        + "with a nonzero. Set s = x squared minus 4ax. Then s = 4acv + 2a squared w "
                        + "and xs - 2as = 4a cubed v. Dividing by nonzero coefficients puts v, "
                        + "then w, then u in the subspace. All remaining subalgebras lie in the "
                        + "square-zero plane. Therefore every nonzero idempotent subspace of "
                        + "the range equals the range. The quantifier includes every complex "
                        + "linear subspace.")),
                    Paragraph(Text("The question is credited to Barei with Muse Spark. Hu and Wen's "
                        + "related counterexamples and Costoya, Fernández Ouaridi and Viruel's "
                        + "evolution-envelope framework are prior literature. The general-dimensional "
                        + "family and its embedding bound are written arguments in the dossier, "
                        + "not additional Lean theorems in this module."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("barei-2026-remark-3-5-minimal-idempotent"),
                    ResolutionKind.Proved))), []));
}
