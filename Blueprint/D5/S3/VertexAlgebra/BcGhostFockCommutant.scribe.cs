using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class BcGhostFockCommutantDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/BcGhostFockCommutant.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/eholzer1997ghost");
    private static Formula Rings() => Seq(
        Forall, Sp, F.Id("K"), Colon, F.Id("Type"), Caret, Grp(F.Id("u")), Comma, Sp,
        OpenBracket, Call("CommRing", F.Id("K")), CloseBracket, Comma, Esc);
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Carrier() => Call("Fock", F.Id("K"));
    private static Formula Vacuum() => Call("Omega", F.Id("K"));
    private static Formula Mode(string name, string index) => Call(name, F.Id("K"), F.Id(index));
    private static Formula Commutes(string hypothesis, string mode, string index) => Seq(
        Forall, Sp, Open, F.Id(hypothesis), Colon, Grp(
            Forall, Sp, F.Id(index), Colon, Integers(), Comma, Sp,
            F.Id("T"), Circ, Mode(mode, index), Eq,
            Mode(mode, index), Circ, Sp, F.Id("T")), Close, Comma, Esc);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The common signed-deletion kernel is the vacuum line, and the actual ghost-mode commutant consists of scalars over every commutative ring.",
        H("The Original Infinite Ghost Kernel and Scalar Commutant"),
        Blocks(
            Paragraph(Text("Fix any universe u and any K : Type u with [CommRing K]. "
                + "There is no field, nontriviality, characteristic, irreducibility or "
                + "finite-dimensionality assumption. Fock(K) is (Finset Nat) ->0 K: "
                + "finite superpositions of arbitrary finite subsets of the unbounded "
                + "natural site set. Omega(K) denotes exactly BcGhostFockSupport.vacuum, "
                + "namely Finsupp.single emptyset 1. coeff(v,S) denotes the actual "
                + "Finsupp coefficient v S, not an inner product or a chosen functional.")),
            Paragraph(Text("At site i, annihilate deletes an occupied i with coefficient "
                + "sign(i,S)=(-1)^(card {s in S | s<i}) and vanishes when i is absent. "
                + "The actual integer b and c modes are the signed insertion/deletion "
                + "operators from BcGhostFockSupport. Composition is written with circ; "
                + "End(K,Fock(K)) means Module.End K (Fock K), and id means its "
                + "LinearMap.id. Scalar multiplication in the formulas is K-module "
                + "scalar multiplication.")),
            Describe.Lean(
                DescribeId.Create("bc-ghost-fock-commutant-annihilator-kernel"),
                DeclarationHandle.Create(Prefix + "annihilator_kernel"),
                H("The simultaneous deletion kernel is exactly the original vacuum line"),
                StatementSource.FromAuthor(Disp(Seq(Rings(), Forall, Sp, F.Id("v"),
                    Colon, Carrier(), Comma, Esc,
                    Open, Forall, Sp, F.Id("i"), Colon, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Call("annihilate", F.Id("K"), F.Id("i"), F.Id("v")), Eq, D(0), Close,
                    Sp, Iff, Sp, F.Id("v"), Eq, Call("coeff", F.Id("v"), Emptyset),
                    Cdot, Vacuum()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The complete original telescope is {K : Type u} "
                        + "[CommRing K] (v : Fock K). Its conclusion is "
                        + "(forall i : Nat, annihilate i v = 0) iff v = v emptyset smul vacuum. "
                        + "Both directions concern this same v and the actual original vacuum.")),
                    Paragraph(Text("The live proof first establishes the coefficient identity "
                        + "(annihilate i v)(S.erase i)=sign(i,S)*v(S) whenever i belongs to S. "
                        + "Linear Finsupp induction reduces it to basis states. Among states "
                        + "containing i, equality after erasing i forces equality before "
                        + "erasing, by reinserting i. Thus no other basis coefficient "
                        + "contributes to that coordinate.")),
                    Paragraph(Text("For a nonempty S, choose an occupied i. Common "
                        + "annihilation makes sign(i,S)*v(S) zero. The sign squares to one "
                        + "over every commutative ring, so multiplying by it gives v(S)=0 "
                        + "without cancellation by an arbitrary nonzero element. Finsupp "
                        + "extensionality leaves exactly the empty-subset coefficient. "
                        + "Conversely, signed deletion annihilates the empty-subset vacuum; "
                        + "linearity annihilates each scalar multiple."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bc-ghost-fock-commutant-mode-scalar"),
                DeclarationHandle.Create(Prefix + "mode_commutant_scalar"),
                H("Commuting with every original b and c mode forces a scalar ghost endomorphism"),
                StatementSource.FromAuthor(Disp(Seq(Rings(), Forall, Sp, F.Id("T"),
                    Colon, Call("End", F.Id("K"), Carrier()), Comma, Esc,
                    Commutes("hb", "b", "m"), Commutes("hc", "c", "n"),
                    F.Id("T"), Eq, Call("coeff", Call("T", Vacuum()), Emptyset),
                    Cdot, Sp, F.Id("id")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The complete original telescope is {K : Type u} "
                        + "[CommRing K] (T : Module.End K (Fock K)), "
                        + "(hb : forall m : Int, T.comp (b m) = (b m).comp T), "
                        + "(hc : forall n : Int, T.comp (c n) = (c n).comp T). "
                        + "The exact conclusion is T = (T vacuum) emptyset smul LinearMap.id. "
                        + "Each commutation hypothesis ranges over all integers, not "
                        + "only creators, annihilators or a finite interval.")),
                    Paragraph(Text("For an even natural site i the proof identifies "
                        + "annihilate i with c at integer index (i/2)+2; for an odd site "
                        + "it identifies annihilate i with b at integer index (i/2)-1. "
                        + "Here i/2 is natural-number division before the integer mode "
                        + "index is formed. These branch and parity identities show that "
                        + "T commutes with every deletion. Applying that commutation to "
                        + "vacuum and then annihilator_kernel gives "
                        + "T vacuum = (T vacuum) emptyset smul vacuum.")),
                    Paragraph(Text("Set a=(T vacuum) emptyset and W=ker(T-a smul id). "
                        + "The vacuum belongs to W. The original hb and hc hypotheses "
                        + "and K-linearity make W stable under every b creator at m<=-2 "
                        + "and every c creator at n<=1. The original creation_cyclic "
                        + "theorem makes W the top submodule. Extensionality gives the "
                        + "endomorphism equality on every finite-support state.")),
                    Paragraph(Text("This is a statement in the endomorphism algebra of "
                        + "the ghost carrier itself. It neither supplies nor assumes a "
                        + "bridge from endomorphisms of a matter tensor ghost carrier "
                        + "to tensor products of endomorphism algebras. In particular it "
                        + "does not claim that a ghost-commuting total-state operator "
                        + "must be a scalar on the matter factor."))),
                DescribeRole.Theorem),
            Paragraph(Text("The existing eholzer1997ghost library note supplies background "
                + "for the ghost Fock and shifted mode conventions. It is acknowledged, "
                + "not used as a claim that the paper proves these exact "
                + "ring-parametric signed-Finsupp implementation theorems. Both "
                + "derivations above are assessed as repository-derived. They are "
                + "algebraic infrastructure reused by the original ghost suppliers, "
                + "not literature novelty, BRST cohomology, a no-ghost theorem, "
                + "complete string physics or an AdS result.")))));
}
