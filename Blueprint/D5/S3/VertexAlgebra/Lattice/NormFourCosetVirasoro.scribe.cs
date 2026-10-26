using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class NormFourCosetVirasoroDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual Sugawara and norm-four fields have the complete mixed OPE and a commuting Virasoro complement.",
        H("The Actual Norm-Four Sugawara Complement"),
        Blocks(
            Paragraph(Text("Let D be the production finite-rank even integral lattice data, G its complex Gram matrix, "
                + "and H a complex matrix satisfying both HG=1 and GH=1. Let B(a,a)=4. On the full "
                + "production Carrier(D), write vacuum for single(0,1), T for the charge-sensitive translation, "
                + "Y for the actual state-field map, omega for the H-Sugawara state, and "
                + "e=(1/16)single(0,chargePolynomial(a)^2)+(s/4)(single(a,1)+single(-a,1)). "
                + "Normalized mode j is the Laurent coefficient at -j-1; Le_m=Y(e)_(m+1) "
                + "and Ltot_m=Y(omega)_(m+1). No positivity, rootlessness or smaller carrier is assumed.")),
            Describe.Lean(
                DescribeId.Create("normfour-coset-mixed-products"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourCosetVirasoro.mixed_products"),
                H("Both mixed OPE orientations and all integer mixed commutators"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex s, both omega_j e and e_j omega equal T(e) at j=0, "
                    + "2e at j=1, vacuum/4 at j=3, and zero at every other nonnegative integer j, "
                    + "including j=2 and every j at least four. Simultaneously, for all integers m,n, "
                    + "[Ltot_m,Le_n]=(m-n)Le_(m+n)+delta_(m+n,0)(m^3-m)I/24, "
                    + "as endomorphisms of the entire production carrier."))),
                DescribeRole.Theorem),
            Paragraph(Text("The actual current commutator gives [Ltot_m,a_(-1)]=a_(m-1). "
                + "Applied twice to the vacuum, it gives 2 times the neutral quadratic state at m=0, "
                + "B(a,a) times the vacuum at m=2, and zero at all other nonnegative m. "
                + "The supplied charged-ground formulas treat both a and -a, while Ltot_(-1)=T. "
                + "Thus the forward mixed OPE follows in the actual lattice carrier. The full integer Ward "
                + "identity reduces to four terms; its integer binomial polynomial includes negative m+1. "
                + "For the reverse orientation, omega=Ltot_(-2)vacuum and creativity give "
                + "Le_m omega=(m+2)Le_(m-2)vacuum+delta_(m,2)vacuum/4 for m at least -1. "
                + "The creation and translation coefficients and vacuum annihilation give all reverse branches and tail.")),
            Describe.Lean(
                DescribeId.Create("normfour-actual-coset-virasoro"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourCosetVirasoro.coset_virasoro"),
                H("The actual complementary field commutes and has center rank minus one half"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If s squared equals one, set c=omega-e and Lc_m=Y(c)_(m+1). "
                    + "The actual field is Y(c)=sugawaraField(D,H)-Y(e), and every integer mode is "
                    + "Lc_m=Ltot_m-Le_m. For all integers m,n, [Lc_m,Le_n]=0 and "
                    + "[Lc_m,Lc_n]=(m-n)Lc_(m+n)+delta_(m+n,0)((rank(D)-1/2)/12)(m^3-m)I. "
                    + "Every operator acts on all of Carrier(D). State-field linearity binds the complement "
                    + "to its actual field before the two supplied Virasoro laws are combined with the proved mixed law."))),
                DescribeRole.Theorem),
            Paragraph(Text("At rank 24 this central charge is 24-1/2=47/2 by substitution. "
                + "The norm-four formula is classical: Shimakura, arXiv:1202.6107, (1.3), attributes "
                + "the Ising-vector assertion to Dong-Mason-Zhu, Theorem 6.3. The lattice fields follow "
                + "Bakalov-Kac, math/0402315, section 4.1. Imported Carnahan and Kytola sources retain "
                + "their licenses and attribution. The mixed calculation and concrete complement here "
                + "establish commuting Virasoro actions, without asserting a whole commutant VOA, "
                + "Baby Monster VOA, Ising simplicity, fusion rules or Monster completion.")))));
}
