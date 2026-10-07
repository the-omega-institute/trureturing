using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeSugawaraCurrentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeSugawaraCurrents.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The genuine lattice currents obey Heisenberg and compute the finite coefficients of the quadratic field.",
        H("Actual Lattice Currents and Sugawara Coefficients"),
        Blocks(
            Paragraph(Text("Let D be an even integral symmetric lattice of any finite rank, including "
                + "zero. Its carrier is the finite-support sum over all integral charges of the "
                + "complex oscillator polynomial algebra. The quadratic field is one half the "
                + "H-weighted double sum of the actual normalMinusOne current products, with L(m) "
                + "its normalized coefficient at m+1. Positive currents vanish beyond the largest "
                + "frequency appearing in the actual input. Normal summands therefore have "
                + "statewise finite support in [min(0,m-R),R]; this is not a uniform endomorphism "
                + "cutoff.")),
            Describe.Lean(
                DescribeId.Create("lattice-current-heisenberg"),
                DeclarationHandle.Create(Prefix + "neutralMode_heisenberg"),
                H("Actual Heisenberg law in every charge sector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For all integers m,n and all lattice indices i,j, "
                    + "[h_i(m),h_j(n)]=m G(i,j) delta(m+n,0) id. Multiplication and "
                    + "Gram-weighted partial differentiation prove both mixed sign "
                    + "branches; zero currents are the actual charge scalars."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lattice-sugawara-coefficient-sum"),
                DeclarationHandle.Create(Prefix + "sugawaraMode_interval_sum"),
                H("The normal-product coefficient equals the statewise finite sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("At coefficient m+1 the defining subtype equation "
                    + "has terms h_i(-t-1)h_j(m+t+1) and h_j(m-t)h_i(t). "
                    + "Reindexing the two natural sums gives respectively k<0 and "
                    + "k>=0, with N(i,j;k,l)=h_i(k)h_j(l) in the first half and "
                    + "h_j(l)h_i(k) in the second. Thus L(m)v is one half the "
                    + "H-weighted double sum of N(i,j;k,m-k)v over the stated finite "
                    + "interval. This is finite support on v, not on endomorphisms."))),
                DescribeRole.Theorem),
            Paragraph(Text("The weighted partial derivatives directly use the frozen private "
                + "partials_commute of ConditionalPolynomialRigidity. The current contraction "
                + "uses both inverse-Gram equations H Gc=Gc H=1. Bakalov-Kac, arXiv "
                + "math/0402315v1, section 4.1, equations (4.12)-(4.16), supplies the classical "
                + "lattice construction; the finite normal-ordering architecture is adapted from "
                + "Kytola at revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4.")))));
}
