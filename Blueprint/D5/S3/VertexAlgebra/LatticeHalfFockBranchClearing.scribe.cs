using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockBranchClearingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both branches of the native contraction", H("Two-Branch Clearing"), Blocks(
            Paragraph(Text("D is an arbitrary finite integral symmetric even-diagonal lattice datum and a,b are unrestricted charges. "
                + "Set g=B(a,b), m=(-g).toNat, n=g.toNat and N=g.natAbs=m+n. "
                + "The exact native halfContraction is binomial_g(-s) times binomial_(-g)(s). "
                + "Native binomial-series exponent addition proves the identities in PowerSeries Complex; "
                + "no equality of rational functions is used to identify unregularized opposite iota expansions.")),
            Describe.Lean(DescribeId.Create("native-two-factor-clearing"),
                DeclarationHandle.Create(Prefix + "half_contraction_two_branch_clearing"), H("Both branch factors"),
                StatementSource.FromAuthor(Disp(Call("TwoBranchClearing", F.Id("D"), F.Id("a"), F.Id("b")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "Exactly (1-s)^m (1+s)^n h_g(s)=(1-s)^n (1+s)^m. "
                    + "The positive-g pole at s=-1 is retained; clearing only the s=1 branch is not sufficient."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("physical-contraction-clearing"),
                DeclarationHandle.Create(Prefix + "half_contraction_physical_clearing"), H("Physical clearing polynomial"),
                StatementSource.FromAuthor(Disp(Call("PhysicalClearing", F.Id("D"), F.Id("a"), F.Id("b")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "Exactly (1-s^2)^N h_g(s)=P_g(s), where P_g=(1-s)^(2n) (1+s)^(2m). "
                    + "With z=x^2 and w=y^2, each physical coordinate shift is two cover-exponent units. "
                    + "This scalar identity is not itself an actual tensor coefficient-locality theorem."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cleared-polynomial-reciprocity"),
                DeclarationHandle.Create(Prefix + "cleared_polynomial_reciprocity"), H("Polynomial branch reversal"),
                StatementSource.FromAuthor(Disp(Call("ClearedReciprocity", F.Id("g")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "The fixed-degree reflection at 2N preserves P_g. Its degree is at most 2N; "
                    + "the physical reversal sign is (-1)^N=paritySign g and must be paired with the actual ground interchange. "
                    + "All-state twisted Jacobi, physical iterates, reconstructed twisted fields, orbifold intertwiners, "
                    + "Monster realization and string/AdS dynamics remain open. Classical provenance, zero novelty claim."))), DescribeRole.Theorem))));
}
