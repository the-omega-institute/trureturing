using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class BajnokBeattyCayleyNecessityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/bajnokbeatty2025diameter");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Necessary congruences for arbitrary signed covering pairs in the even-radius top strip.",
        H("An affine odd square detects the necessary congruences"),
        Blocks(Describe.Lean(
            DescribeId.Create("arbitrary-pair-top-strip-necessity"),
            DeclarationHandle.Create("D5/S3/FiniteGroups/BajnokBeattyCayleyNecessity.top_strip_necessity"),
            H("Every covering pair forces an even deficit"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "Let t,r be integers and k a natural number with t ≥ 1, 0 ≤ r < t and "
                    + "k=2t²−r. For any a,b in Z/2 × Z/(2k), suppose every g can be written "
                    + "as x•a+y•b for integers x,y with |x|+|y| ≤ 2t. Then 2 divides r; "
                    + "if t is odd, 4 divides r. No distinctness assumption or prescribed form "
                    + "of the pair is needed.")),
                Paragraph(Text(
                    "Write f(x,y)=x•a+y•b. Coverage makes f surjective, and reduction to the "
                    + "two-dimensional quotient modulo 2 forces every relation in ker f to have "
                    + "even coordinates. The odd affine coefficient class is a torsor: its "
                    + "sum-and-difference coordinates give an exact square of side 2t after "
                    + "translation. Its relation lattice is ker(f composed with (u,v)↦(u+v,u−v)), "
                    + "whose actual quotient index is 2k=(2t)²−2r. The strict top-strip bound "
                    + "permits near-square rigidity with n=2t and δ=2r.")),
                Paragraph(Text(
                    "The resulting basis has displacement parameters a₀,b₀ with a₀b₀=2r. "
                    + "Relation parity makes both parameters even, so r is even. If t is odd "
                    + "and r is not divisible by 4, both half-displacements are odd. The "
                    + "sum-and-difference images of the basis then force all of ker f into 4Z². "
                    + "This contradicts 2-primary primitivity: a preimage of (1,0) has a double "
                    + "in ker f, and divisibility of that double by 4 would make the preimage "
                    + "even, impossible in the first Z/2 coordinate.")),
                Paragraph(Text(
                    "This supplies the necessary congruences for arbitrary pairs in the stated "
                    + "top strip of Bajnok–Beatty Conjecture 4.1. The source comparison is "
                    + "arXiv:2406.04045v1, Theorems 4.2–4.4; the revised paper has not been read. "
                    + "The theorem alone is not the full conjecture or a classification outside "
                    + "this range, and it makes no claim of literature novelty."))),
            DescribeRole.Theorem))));
}
