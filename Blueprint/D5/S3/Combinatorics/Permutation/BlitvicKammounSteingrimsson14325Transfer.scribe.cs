using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class BlitvicKammounSteingrimsson14325TransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Transfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal residue invariants of the grid transfer for the overlap-two 14325 problem.",
        H("The 14325 grid transfer"),
        Blocks(
            Paragraph(Text("For a semiring R define T(f)(k) as the sum of r f(r+2) "
                + "over 1≤r≤k. The rows have b₁(k)=1 and bₙ₊₁=T(bₙ); Lean row R n "
                + "is bₙ₊₁. All arguments k are natural, including the auxiliary values "
                + "zero, one and two. This algebraic definition does not assert a "
                + "packing-count recurrence as a hypothesis of the original problem.")),
            Describe.Lean(DescribeId.Create("bks14325-transfer-mod-five"),
                DeclarationHandle.Create(Prefix + "row_mod_five"),
                H("Every transfer row at argument three is one modulo five"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("n"), Colon, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Sp,
                    new Formula.Apply(F.Id("row"), [new Formula.Apply(F.Id("ZMod"), [D(5)]), F.Id("n"), D(3)]),
                    Sp, Eq, Sp, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The first nonconstant row has period-five profile "
                    + "(0,1,3,1,0). Its image has profile (0,1,1,1,0), which is fixed "
                    + "by T. The weighted increments of both profiles are (1,0,0,4,0). "
                    + "Induction on k proves these identities for every argument; induction "
                    + "on n proves stabilization. The initial row and first nonconstant "
                    + "row both take value one at three."))), DescribeRole.Theorem),
            Paragraph(Text("The source target counts actual permutations of [3j+2], j≥1, "
                + "whose prescribed length-five windows at starts 1+3t, 0≤t<j, have "
                + "pattern 14325. Extra occurrences are allowed. Applying this invariant "
                + "requires a proved insertion/deletion bijection identifying this count "
                + "with row ℕ (j−1) 3 and a coefficient-reduction bridge. Those are separate "
                + "obligations; no equality to the actual count is claimed here.")),
            Paragraph(Text("The full target also requires residue one modulo ten when "
                + "j+1=2ᵏ with k≥1, residue six otherwise, and nondivisibility by four "
                + "if and only if j+1=2ⁱ+2ᵖ with 0≤p≤i. The equal-exponent and p=0 "
                + "boundaries are included. The printed continuation says four divides "
                + "all but these indices; the exact-exception converse is the stronger "
                + "registered interpretation. This contribution does not settle it or "
                + "the full target. The narrower issue 21304 remains unchanged.")))));
}
