using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class BcGhostVacuumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/BcGhostVacuum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/eholzer1997ghost");
    private static Formula Rings() => Seq(
        Forall, Sp, F.Id("K"), Colon, F.Id("Type"), Caret, Grp(F.Id("u")), Comma, Sp,
        OpenBracket, Call("CommRing", F.Id("K")), CloseBracket, Comma, Esc);
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Vacuum() => Call("Omega", F.Id("K"));
    private static Formula Apply(Formula index, Formula state) => Call("L", F.Id("K"), index, state);
    private static Formula IntegerCoefficient() => Seq(
        Open, Open, Minus, D(1, 3), Star,
        Open, F.Id("r"), Caret, Grp(D(3)), Minus, F.Id("r"), Close,
        Slash, D(6), Colon, Integers(), Close, Colon, F.Id("K"), Close);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original ghost vacuum is annihilated by stress modes m>=-1, and positive modes contract its negative-mode image with an exact integral cubic coefficient.",
        H("The Original Ghost Stress Vacuum and Integral Contraction"),
        Blocks(
            Paragraph(Text("Every statement holds at arbitrary universe u, for any "
                + "K : Type u and [CommRing K]. Fock K is the unbounded algebraic "
                + "finite-subset Finsupp carrier. Omega(K) is exactly the original "
                + "BcGhostFockSupport.vacuum = Finsupp.single emptyset 1, not an "
                + "arbitrary highest-weight vector supplied as a premise. L is the "
                + "original linear stress operator, defined by the statewise finite "
                + "sum of (m-k) smul normalPair(m+k,-k). normalPair(p,q) is "
                + "b(p).comp(c(q)) for p<=-2 and -c(q).comp(b(p)) otherwise.")),
            Describe.Lean(
                DescribeId.Create("bc-ghost-vacuum-stress-annihilation"),
                DeclarationHandle.Create(Prefix + "L_vacuum_annihilation"),
                H("Every stress mode at or above minus one annihilates the actual vacuum"),
                StatementSource.FromAuthor(Disp(Seq(Rings(), Forall, Sp, F.Id("m"),
                    Colon, Integers(), Comma, Sp,
                    Forall, Sp, Open, F.Id("hm"), Colon, Minus, D(1), Le, Sp, F.Id("m"), Close,
                    Comma, Esc, Apply(F.Id("m"), Vacuum()), Eq, D(0)))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The complete original telescope is {K : Type u} "
                        + "[CommRing K] (m : Int) (hm : -1 <= m). The exact conclusion "
                        + "is L (K := K) m vacuum = 0. In particular m=-1 and m=0 "
                        + "are included; this is not just a positive-mode statement.")),
                    Paragraph(Text("Signed deletion kills the vacuum, so b_m vacuum=0 "
                        + "for m>=-1 and c_n vacuum=0 for n>=2. Consequently the "
                        + "normal pair on vacuum survives only if p<=-2 and q<=1. "
                        + "L_interval_sum evaluates the original L_m on vacuum in "
                        + "its state-dependent support interval. In a potentially "
                        + "surviving summand, m+k<=-2 and -k<=1 combined with "
                        + "m>=-1 force m=k, making the coefficient m-k zero. "
                        + "Every other summand vanishes by vacuum annihilation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bc-ghost-vacuum-positive-contraction"),
                DeclarationHandle.Create(Prefix + "L_vacuum_contraction"),
                H("A positive stress mode contracts the corresponding negative-mode vacuum vector"),
                StatementSource.FromAuthor(Disp(Seq(Rings(), Forall, Sp, F.Id("r"),
                    Colon, Integers(), Comma, Sp,
                    Forall, Sp, Open, F.Id("hr"), Colon, D(0), Lt, F.Id("r"), Close,
                    Comma, Esc, Apply(F.Id("r"), Apply(Seq(Minus, F.Id("r")), Vacuum())),
                    Eq, IntegerCoefficient(), Cdot, Vacuum()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The complete original telescope is {K : Type u} "
                        + "[CommRing K] (r : Int) (hr : 0 < r). The exact conclusion "
                        + "is L (K := K) r (L (-r) vacuum) = "
                        + "(((-13 * (r^3-r) / 6 : Int) : K)) smul vacuum. "
                        + "The slash inside the Int annotation is INTEGER division "
                        + "before the integer is cast into K. It is neither division "
                        + "by six in K nor a field-only rational coefficient. No "
                        + "invertibility of six, characteristic or nontriviality "
                        + "assumption is present. The input is the actual L(-r) "
                        + "applied to the same original vacuum.")),
                    Paragraph(Text("Expanding L(-r) on vacuum leaves precisely k in "
                        + "the inclusive integer interval [-1,r-2], with term "
                        + "(-r-k) smul b(-r+k)(c(-k)vacuum). This follows by padding "
                        + "the statewise interval and deleting terms outside the "
                        + "double-creator region, not by truncating the carrier. "
                        + "The exterior-coordinate insertion/contraction identity "
                        + "gives b_k(c(-k)vacuum)=vacuum for k>=-1. The original "
                        + "L_b_commutator and L_c_commutator, together with "
                        + "L_vacuum_annihilation, give L_r applied to each surviving "
                        + "pair equal to (2r-k) smul vacuum.")),
                    Paragraph(Text("Thus the contraction is the sum over k in "
                        + "[-1,r-2] of ((-r-k)(2r-k) : K) smul vacuum. The live "
                        + "proof computes the corresponding integer sum: six times "
                        + "that sum is -13(r^3-r). It proves the polynomial sum "
                        + "identity in the rationals using the first and second "
                        + "power sums and casts that identity back to integers. "
                        + "Int.mul_ediv_cancel_left then identifies the sum with "
                        + "the exact integer quotient. Only after this step is "
                        + "the integer equality cast to K and the finite scalar "
                        + "sum collected against vacuum. Rational arithmetic "
                        + "inside that proof does not restrict the target ring."))),
                DescribeRole.Theorem),
            Paragraph(Text("The existing eholzer1997ghost note is acknowledged for "
                + "the Fock and weight-(2,-1) mode conventions. It does not attest "
                + "these exact original signed-Finsupp theorems over arbitrary "
                + "commutative rings; their assessed provenance is repository "
                + "derivation. These two statements supply algebraic ghost "
                + "infrastructure. Neither is the full all-state Virasoro bracket, "
                + "a BRST cohomology computation, a no-ghost theorem, a physical "
                + "string completion or an AdS theorem.")))));
}
