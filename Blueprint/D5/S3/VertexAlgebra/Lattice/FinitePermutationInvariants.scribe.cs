using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class FinitePermutationInvariantsDocument : IScribeDocumentDefinition
{
    private static Formula K => F.Id("K");
    private static Formula G => F.Id("G");
    private static Formula X => F.Id("X");
    private static Formula V => F.Id("V");
    private static Formula Rho => F.Id("rho");
    private static Formula Q => Call("Orbits", G, X);
    private static Formula Fixed => Call("Fixed", Rho);

    private static Formula Quantified(Formula conclusion) => Disp(Seq(
        Forall, Sp, K, Comma, G, Comma, X, Comma, V, Comma, Sp,
        Call("Field", K), Sp, Land, Sp, Call("Group", G), Sp, Land, Sp,
        Call("MulAction", G, X), Sp, Land, Sp, Call("Fintype", X), Sp, Land, Sp,
        Call("AddCommGroup", V), Sp, Land, Sp, Call("Module", K, V), Sp, Rightarrow, Sp,
        Forall, Sp, Rho, InMacro, Sp, Call("MonoidHom", G, Call("LinearAut", K, V)), Comma, Sp,
        Forall, Sp, F.Id("b"), InMacro, Sp, Call("Basis", X, K, V), Comma, Sp,
        Open, Forall, Sp, F.Id("g"), InMacro, Sp, G, Comma, Sp,
        Forall, Sp, F.Id("x"), InMacro, Sp, X, Comma, Sp,
        Call("rho", F.Id("g"), Call("b", F.Id("x"))), Eq,
        Call("b", Call("smul", F.Id("g"), F.Id("x"))), Close, Sp,
        Rightarrow, Sp, conclusion));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A representation permuting a finite basis has one invariant dimension per actual basis orbit.",
        H("Invariants of a finite permutation basis"),
        Blocks(
            Paragraph(Text(
                "Let a group act on a finite index set, and let a linear representation permute a basis according to that action. Fixed vectors correspond exactly to scalar functions on the orbit quotient. Here K,G,X,V are types; V is a K-module, b is an X-indexed basis, and rho is a monoid homomorphism from G to its K-linear automorphisms satisfying rho(g)(b(x))=b(g smul x) for every g and x. Orbits(G,X) denotes the quotient by the actual orbit relation, Fun(Q,K) the scalar function space, and Fixed(rho) the submodule of vectors fixed by every group element. The acting group need not be finite, stabilizers may be nontrivial, and the field may have arbitrary characteristic.")),
            Describe.Lean(
                DescribeId.Create("finitepermutationinvariants-fixed-basis-equiv-orbit-functions"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/FinitePermutationInvariants.fixedBasisEquivOrbitFunctions"),
                H("Fixed vectors and orbit coefficients"),
                StatementSource.FromAuthor(Quantified(Call("LinearEquiv", K, Fixed, Call("Fun", Q, K)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The forward linear map descends the basis coefficients of a fixed vector to the actual orbit quotient. Its inverse assigns each basis vector its orbit coefficient and reconstructs the vector through the basis coordinate equivalence. Equivariance proves that the reconstructed vector is fixed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finitepermutationinvariants-fixed-finrank-orbit-card"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/FinitePermutationInvariants.fixed_finrank_eq_orbit_card"),
                H("Invariant dimension equals the number of orbits"),
                StatementSource.FromAuthor(Quantified(Seq(Call("finrank", K, Fixed), Eq, Call("card", Q)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The linear equivalence identifies the fixed submodule with the finite function space on the orbit quotient, so its dimension is exactly the number of orbits. This extends the independent regular-orbit calculation to actions with stabilizers, without dividing by a group or stabilizer order."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "This is a general algebraic bridge for pure permutation bases. A lattice lift carrying nontrivial scalar phases requires an additional stabilizer-character analysis; no assertion about the dimension of an entire lattice C2 quotient follows from this result alone.")))));
}
