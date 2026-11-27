using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiSingleFibreInventoryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CharacterSums/PascadiSingleFibreInventory.";
    private static Formula P => F.Id("p");
    private static Formula Hwidth => F.Id("H");
    private static Formula R => F.Id("R");
    private static Formula Dpivot => F.Id("d");
    private static Formula Q => Call("N", R, Dpivot);
    private static Formula Length => Ell;
    private static Formula ShortDirections => Call("Short", R);
    private static Formula Hpower(byte k) => Seq(Hwidth, Caret, D(k));
    private static Formula Quotient(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The stationary count in a literal short frequency box is controlled by a Euclidean lattice minimum; only a bounded number of projective directions have a small minimum.",
        H("Single-fibre inventory of stationary frequencies"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pascadi-literal-stationary-count"),
                DeclarationHandle.Create(Prefix + "stationaryCount"),
                H("Count the actual lower stationary quadruples"),
                StatementSource.FromAuthor(Disp(Seq(
                    Q, Eq, Call("card", Call("StationaryFibre", R, Dpivot))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A frequency quadruple is grouped as (w₁,n₁),(w₂,n₂). Its entries lie in four translated closed integer intervals [Lᵢ,Lᵢ+H]. The theorem uses a nonzero lower pivot d=(alpha,beta) modulo p. Write u(a,b)=alpha a+beta b mod p.")),
                    Paragraph(Text(
                        "For the lower point z=(x,y), the actual gradient of xy(h−x−y) is G=(y(h−2x−y),x(h−x−2y)). The count is of exactly those quadruples in the box with u(w₁,n₁)G₂=u(w₂,n₂)G₁. This is the lower parallelism condition, including zero reading; no numerical approximation or extra rank filter is applied."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pascadi-single-fibre-inventory"),
                DeclarationHandle.Create(Prefix + "single_fibre_inventory"),
                H("The stationary bound, long-direction volume estimate, and short-direction count"),
                StatementSource.FromAuthor(InventoryStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here p is prime, 1≤H<p, and G is nonzero. The length ell is the Euclidean minimum of the nonzero integer kernel of u. Short(R) is the set of projective directions whose own Euclidean minimum is less than p/H. Its representatives are (0,1) and (1,t) for t modulo p, so each direction is counted once.")),
                    Paragraph(Text(
                        "A square grid yields a primitive minimum in the sup norm with length at most floor(sqrt(p)). Compare this with the attained Euclidean minimum. In a fixed residue, determinant rows are separated by multiples of p and each row is traversed in steps of the primitive vector. Since one gradient coordinate is nonzero, one free coordinate pair fixes the other pair's residue.")),
                    Paragraph(Text(
                        "In the long-direction case, ell²≤2p and ell≥p/H imply p≤2H²; this absorbs the quadratic term without assuming H≥sqrt(p). For short directions, choosing one short nonzero kernel vector is injective up to the chosen projective direction: its nonzero reduction determines the unique projective annihilator.")),
                    Paragraph(Text(
                        "The formal statement is the literal width-H normalization. If the four coordinate intervals have widths at most C H for a fixed C≥1, cover each interval by at most ceil(C) closed width-H intervals and sum over at most ceil(C)⁴ boxes. This preserves H and the threshold p/H; overlapping endpoints only increase the upper count. This explains the O(H)-width formulation and is not a separate Lean claim.")),
                    Paragraph(Text(
                        "These are counts of stationary frequencies at one lower point. They are not a short-window RMS or a signed energy estimate."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula InventoryStatement() => Disp(Seq(
        Q, Le, D(8), Quotient(Hpower(4), P), Plus, D(2, 4), Quotient(Hpower(3), Length), Plus, D(4), Hpower(2),
        Quad, Land, Quad, Open, Quotient(P, Hwidth), Le, Length, Implies,
        Q, Le, D(4, 0), Quotient(Hpower(4), P), Close,
        Quad, Land, Quad, Call("card", ShortDirections), Le, D(9), Open, Quotient(P, Hwidth), Close, Caret, D(2)));
}
