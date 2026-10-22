using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeBcGhostBrstVacuumClassDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeBcGhostBrstVacuumClass.";
    private static readonly LibraryNoteRef GhostSource =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/eholzer1997ghost");
    private static readonly LibraryNoteRef MatterSource =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");
    private static Formula Vacuum() => Call("V", F.Id("D"));
    private static Formula Charge(Formula state) => Call("Q", F.Id("D"), F.Id("H"), state);
    private static Formula Coefficient(Formula state) => Call("epsilon", F.Id("D"), state);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual original vacuum is closed, and its tensor coefficient excludes preimages in the entire original State.",
        H("The Original Vacuum Coefficient And Nonexactness"),
        Blocks(
            Paragraph(Text("D is arbitrary original LatticeData: finite rank, an integral symmetric "
                + "Gram matrix and even diagonal entries, with no positivity or nondegeneracy premise. "
                + "H is any complex matrix on Fin(D.rank), not necessarily symmetric or an inverse. "
                + "State(D) remains the original Carrier(D) tensor over Complex with Fock(Complex). "
                + "The vector V(D) is exactly Finsupp.single zero-charge constant-polynomial-one tensor "
                + "the actual BcGhostFockSupport.vacuum. No charge, vacuum or intercept is replaced.")),
            Paragraph(Text("The ghost linear functional extracts the empty finite-subset coefficient. "
                + "The matter linear functional extracts the zero exponent-vector coefficient of the "
                + "polynomial at charge zero. Their bilinear product is extended through the original "
                + "algebraic tensor universal property: epsilon is TensorProduct.map of the two "
                + "coefficient linear maps followed by TensorProduct.lid on Complex tensor Complex. "
                + "Consequently epsilon(u tensor g) is the constant coefficient of u(0) times g(empty). "
                + "This is complex-linear, not a conjugate-linear pairing or a Hilbert-space completion.")),
            Describe.Lean(
                DescribeId.Create("latticebcghostbrst-vacuum-closed"),
                DeclarationHandle.Create(Prefix + "vacuum_closed"),
                H("The actual zero-charge ground vacuum is closed"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("D"), Comma, Sp,
                    F.Id("H"), Comma, Sp, Charge(Vacuum()), Eq, D(0)))),
                AssessedProvenance.FromRepo(GhostSource, MatterSource),
                Blocks(
                    Paragraph(Text("The exact original telescope is (D : LatticeData) "
                        + "(H : Matrix (Fin D.rank) (Fin D.rank) Complex). The conclusion is "
                        + "Q D H (vacuumVector D)=0, without Gram inverse, rank, positivity, "
                        + "nilpotence, grading or highest-weight assumptions.")),
                    Paragraph(Text("For each actual normalSummand(i,j,k,m-k) at m>=-1, the "
                        + "rightmost neutral mode is nonnegative: m-k>=0 when k<0, and k>=0 "
                        + "in the other normal-order branch. Positive modes annihilate constant "
                        + "polynomial one by the original frequency-bound supplier; the zero mode "
                        + "annihilates charge zero by the actual integral bilinear form. Thus every "
                        + "normal summand kills the matter ground vector, including m=-1 and m=0. "
                        + "The exact state-dependent sugawaraMode_interval_sum preserves the "
                        + "matrix H(i,j) and the original inverse-two factor.")),
                    Paragraph(Text("When n>=-1, the matter ground calculation and the existing "
                        + "BcGhostVacuum.L_vacuum_annihilation give A_n V=0. The ghost stress "
                        + "supplier includes its weighted n=-1 boundary: the unweighted term "
                        + "b(-2)c(1)Omega need not vanish, but its coefficient n-k is zero. "
                        + "When n<-1, c(-n) is an actual annihilator and kills Omega. The "
                        + "negative N branch is G(n) composed with C(-n), so it also kills V. "
                        + "The order is never swapped. Finally A_finite at V licenses the "
                        + "finite sum of these original A terms."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostbrst-vacuum-coefficient-annihilation"),
                DeclarationHandle.Create(Prefix + "epsilon_Q"),
                H("The vacuum coefficient annihilates every original charge image"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("D"), Comma, Sp,
                    F.Id("H"), Comma, Sp, F.Id("state"), Comma, Sp,
                    Coefficient(Charge(F.Id("state"))), Eq, D(0)))),
                AssessedProvenance.FromRepo(GhostSource, MatterSource),
                Blocks(
                    Paragraph(Text("The original telescope adds (state : State D) to arbitrary "
                        + "D and H. The conclusion epsilon D (Q D H state)=0 covers every "
                        + "original algebraic tensor superposition, every charge sector and all "
                        + "finite-subset ghost states. It is not restricted by ghost number, energy "
                        + "or a fixed mode bound.")),
                    Paragraph(Text("On a ghost basis single(S,a), signed insertion either gives "
                        + "zero or a scalar multiple of single(insert i S,1); insert i S is never "
                        + "empty. Finite Finsupp induction therefore gives epsilon_g create_i=0 "
                        + "on every ghost input over arbitrary CommRing K. For m<=-2, both actual "
                        + "normalPair branches have a creator on the left: b(m+k) when m+k<=-2, "
                        + "and otherwise c(-k), since k>=1. The swapped branch retains its minus "
                        + "sign. The real L_interval_sum at the specific input g makes "
                        + "epsilon_g(L_m g)=0; no operator-valued global finite-support assertion "
                        + "is used.")),
                    Paragraph(Text("For negative matter mode m, every actual normal summand has "
                        + "a negative oscillator on the left. Its exact multiplication variable "
                        + "is X(i,(-k-1).toNat) when k<0; otherwise m-k<0 and the leftmost "
                        + "variable is X(j,(-(m-k)-1).toNat). The constant coefficient of "
                        + "X times any polynomial vanishes. Original neutralMode_single preserves "
                        + "charge, so nonzero charges cannot contribute and Finsupp induction "
                        + "extends the calculation to arbitrary matter input. The positive "
                        + "derivative index remains (j,(k-1).toNat); no index shift is introduced. "
                        + "The actual finite interval and both original scalar factors are retained.")),
                    Paragraph(Text("In A_n=C(-n) composed with M(n)+(1/2)N_n, n>=-1 has a "
                        + "leftmost c creator in the ghost coefficient of both terms. For n<-1, "
                        + "the matter coefficient of M(n) vanishes, while N_n has the negative "
                        + "ghost stress L_n on the left and is killed on every input. The tensor "
                        + "map formulas give epsilon A_n=0 on pure tensors; tensor induction "
                        + "extends it to the entire State. A_finite at that exact state licenses "
                        + "transporting epsilon through the single original Q finsum. Q is not "
                        + "split into separately unlicensed matter and ghost infinite sums."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostbrst-vacuum-coefficient-normalization"),
                DeclarationHandle.Create(Prefix + "epsilon_vacuum"),
                H("The actual vacuum coefficient is normalized to one"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("D"), Comma, Sp,
                    Coefficient(Vacuum()), Eq, D(1)))),
                AssessedProvenance.FromRepo(GhostSource, MatterSource),
                Blocks(Paragraph(Text("This is the direct coefficient calculation for the "
                    + "actual zero-charge constant-one ground vector and single(empty,1) ghost "
                    + "vacuum. Its exact telescope contains only D. It is a consumed bind-only "
                    + "normalization helper for vacuum_not_mem_range, not a separate new "
                    + "mathematical construction or a finite certified instance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostbrst-vacuum-nonexact"),
                DeclarationHandle.Create(Prefix + "vacuum_not_mem_range"),
                H("No original algebraic state is a vacuum preimage"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("D"), Comma, Sp,
                    F.Id("H"), Comma, Sp, Neg, Open, Vacuum(), Sp, InMacro, Sp,
                    Call("range", Call("Q", F.Id("D"), F.Id("H"))), Close))),
                AssessedProvenance.FromRepo(GhostSource, MatterSource),
                Blocks(
                    Paragraph(Text("For every original D and arbitrary H, vacuumVector D "
                        + "does not belong to LinearMap.range(Q D H). A purported preimage "
                        + "state would give epsilon(Q state)=0 and epsilon(V)=1. The "
                        + "contradiction excludes preimages in the entire original State, "
                        + "not merely within a chosen graded sector or finite truncation.")),
                    Paragraph(Text("For the cohomology interpretation only, additionally assume "
                        + "H times gramComplex(D)=identity, gramComplex(D) times H=identity, "
                        + "and rank(D)=26. Reuse the existing original all-state theorem "
                        + "LatticeBcGhostBrstNilpotence.nilpotent with BOTH inverses and rank26. "
                        + "Its Q squared equals zero puts range Q in ker Q. The closed vector V "
                        + "then represents a nonzero element in ker Q modulo range Q; equivalently "
                        + "the restriction of epsilon descends and takes this class to one. "
                        + "This passage uses mathlib LinearMap.range_le_ker_iff and the "
                        + "Submodule.Quotient.mk_eq_zero criterion. No renamed nilpotence, "
                        + "range-kernel or quotient theorem is retained as a new D5 result.")),
                    Paragraph(Text("This class interpretation is ungraded. A ghost-number "
                        + "commutator alone does not compute cohomology or identify all degree "
                        + "components; the independent ghost-number line is not a premise here. "
                        + "The full BRST cohomology, no-ghost theorem, physical spectrum, "
                        + "string theory and AdS/CFT goal remain open. No positivity, physical "
                        + "realization, literature novelty or holographic correspondence is asserted.")),
                    Paragraph(Text("The derivation is assessed as repo-derived. The existing "
                        + "Eholzer-Feher-Honecker ghost note supplies convention provenance, "
                        + "and the existing Bakalov-Kac lattice note supplies carrier and "
                        + "conformal background. Neither note is cited as already proving "
                        + "nonexactness of this repository's original Q. No additional "
                        + "literature identity or unverified source locator is introduced."))),
                DescribeRole.Theorem))));
}
