using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class NormFourVacuumNullDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The production norm-four lattice vector satisfies the level-six vacuum null relation.",
        H("The Actual Level-Six Vacuum Null Vector"),
        Blocks(
            Paragraph(Text("Let D have an integral symmetric Gram matrix with even diagonal, let B be its bilinear form, "
                + "and let a be a charge with B(a,a)=4. The oscillator algebra is the complex multivariate polynomial "
                + "ring on Fin(rank(D)) times N; the carrier is its finite-support charge direct sum. "
                + "For s in C with s squared equal to one, use the production vector "
                + "v=(1/16)single(0,P(0) squared)+(s/4)(single(a,1)+single(-a,1)), "
                + "where P(r)=sum_i a_i X(i,r). Write L_m=Y(v)_(m+1) and vacuum=single(0,1).")),
            Describe.Lean(
                DescribeId.Create("normfourvacuumnull-level-six-vacuum-null"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourVacuumNull.level_six_vacuum_null"),
                H("Level-six vacuum relation in the production carrier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every such D,a,s, the actual vector "
                    + "64 L_(-2)(L_(-2)(L_(-2)(vacuum))) +93 L_(-3)(L_(-3)(vacuum)) "
                    + "-264 L_(-4)(L_(-2)(vacuum)) -108 L_(-6)(vacuum) equals zero. "
                    + "No positivity, rootlessness, unimodularity, nondegeneracy, rank restriction "
                    + "or determinant premise is used."))),
                DescribeRole.Theorem),
            Paragraph(Text("The calculation uses the private production calculus in NormFourVacuumNullCalculus "
                + "for the actual current modes, charged-field transport and creation series. "
                + "The creation recurrence determines coefficients through degree six after multiplication by 720. "
                + "Current annihilation bounds give finite support for both unbounded normal-ordering sums. "
                + "Transport of the eight required oscillator monomials gives finite charged coefficients, "
                + "including vanishing same-sign charge channels. Nineteen atom actions and seven descendant "
                + "actions reduce the final relation to polynomial cancellation separately in charges 0,a,-a. "
                + "Integral scaling is cancelled only after these actual carrier equalities.")),
            Paragraph(Text("In the finite coefficient notation, 12288 L_(-2) cubed vacuum=3 V222, "
                + "2880 L_(-3) squared vacuum=V33, 11520 L_(-4)L_(-2)vacuum=V42, "
                + "and 96 L_(-6)vacuum=V6. The coefficient identity is "
                + "15 V222+31 V33-22 V42-1080 V6=0. Multiplying the asserted relation by 960 "
                + "reduces it to this identity. Virasoro commutators alone do not supply the zero vector.")),
            Paragraph(Text("The norm-four vector and its classical attribution are those of NormFourVirasoroVector: "
                + "Shimakura, arXiv:1202.6107, equation (1.3), attributing the Ising-vector assertion to "
                + "Dong-Mason-Zhu, Theorem 6.3. The imported lattice-field construction follows "
                + "Bakalov-Kac, arXiv:math/0402315, section 4.1; imported normal-product and Sugawara "
                + "sources retain their Carnahan and Kytola Apache-2.0 attribution.")),
            Paragraph(Text("This relation establishes a concrete annihilated vacuum vector. Ising simplicity, "
                + "fusion rules, Monster moonshine, string theory and AdS/CFT remain outside its conclusion.")))));
}
