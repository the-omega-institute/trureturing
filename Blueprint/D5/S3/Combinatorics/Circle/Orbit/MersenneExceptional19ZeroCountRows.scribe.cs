using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.Orbit;

internal sealed class MersenneExceptional19ZeroCountRowsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal integer-floor row classification used by the exact exceptional19 physical zero-subset count.",
        H("The exceptional19 row arithmetic library"),
        Blocks(
            Paragraph(Text("This private arithmetic library is consumed by MersenneExceptional19ZeroCount.actual_zero_subsets_card. For every natural M>=27, it defines the exact rational row expression with B=152M-8 and proves its equality to the five normalized integer quotients. Every denominator is proved positive; signed quotients are taken in the integers, before subtraction.")),
            Paragraph(Text("Writing M=n+27 for an arbitrary natural n makes the 260 exhaustive half-open cells affine in n with nonnegative endpoints. On each cell the lower and strict upper endpoint bounds for each of the five floors are proved by expanding the relevant polynomial in n and checking nonnegative coefficients. The generic monotonicity lemma floor_on_cell transports these endpoint bounds to every integer in the cell. Thus no finite sample of M is used.")),
            Paragraph(Text("The mirrored Basic module owns the shared definitions and generic floor proof; Row00 through Row18 each own one complete natural residue row, and the root module retains row_zero_count. For each residue 0 through 18, extensional equality identifies the actual zero filter with the union of its zero cells. Explicit disjointness and natural Ico cardinalities establish the row counts and their sum 1882M-93. The canonical physical-count exposition records all 19 row coefficients and the separate full-mask endpoint. These private lemmas are arithmetic ingredients of that connected proof, not a substitute physical-subset theorem. The mathematical input was the supplied ordinary all-M proof and exact symbolic certificate; no novelty or official acceptance is claimed."))), []));
}
