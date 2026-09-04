using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class RestrictedScalarFreeMinkowskiLatticeDocument
    : IScribeDocumentDefinition
{
    private const string Gid =
        "D5/S3/Arith/Lattices/RestrictedScalarFreeMinkowskiLattice.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Free restriction of scalars has product rank and a full conjugate Minkowski lattice.",
        H("Restricted-Scalar Free Minkowski Lattice"),
        Blocks(Describe.Lean(
            DescribeId.Create("restricted-scalar-free-minkowski-completion"),
            DeclarationHandle.Create(Gid + "restricted_scalar_free_minkowski_completion"),
            H("All conjugate coordinates complete the finite-free module"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a number field K of rational degree d, the free module with r "
                        + "coordinates over its ring of integers has integer rank r times d.")),
                Paragraph(Text(
                    "The restrictedMinkowskiEmbedding applies the mixed archimedean "
                        + "embedding in every coordinate. Its image is proved equal to the "
                        + "integer span of the product of Mathlib's Minkowski lattice bases. "
                        + "That equality gives discreteness, full real span, and the displayed "
                        + "additive fundamental domain.")),
                Paragraph(Text(
                    "The source theorem was stated for an arbitrary rank-r projective module. "
                        + "Pinned Mathlib has the required lattice theorem for the ring of "
                        + "integers and fractional ideals, but no Steinitz decomposition for "
                        + "arbitrary finite projective modules over that Dedekind domain. The "
                        + "formal statement therefore records the complete finite-free case "
                        + "O_K^r and does not claim the unavailable projective generalization.")),
                Paragraph(Text(
                    "Pinned Mathlib supplies RingOfIntegers.rank, finite-product finrank, the "
                        + "integer Minkowski lattice basis, its discrete full-rank lattice "
                        + "instances, and ZSpan.isAddFundamentalDomain."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula field = F.Id("K");
        Formula rank = F.Id("r");
        Formula degree = F.Id("d");
        Formula lattice = Call("restrictedMinkowskiLattice", field, rank);
        Formula basis = Call("restrictedMinkowskiBasis", field, rank);

        return Disp(Seq(
            Call("degree", field), Sp, Eq, Sp, degree, Sp, Rightarrow, Sp,
            Call("finrankZ", Call("freeModule", field, rank)),
            Sp, Eq, Sp, rank, Sp, Times, Sp, degree, Sp, Land, Sp,
            Call("IsZLattice", lattice), Sp, Land, Sp,
            Call("IsAddFundamentalDomain", lattice, Call("fundamentalDomain", basis)),
            Dot));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(
            Seq(Operatorname, Grp(F.Id(name))),
            [.. arguments]);
}
