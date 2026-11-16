using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class ActualC2CofiniteDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/ActualC2Cofinite.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/popov2026leanvoac2");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive-definite even lattice has finite-dimensional quotient by the literal actual C2 span.",
        H("C2 Cofiniteness of the Actual Positive-Definite Lattice VOA"),
        Blocks(
            Paragraph(Text("Let D be any original LatticeData, including rank zero, with integral symmetric Gram matrix and even diagonal. "
                + "Charges are Charge(D)=Fin(rank(D)) -> Z, oscillators are complex polynomials in Index(D)=Fin(rank(D)) x N, and "
                + "Carrier(D) is the finite-support charge sum of those polynomials. ActualC2.C2(D) is the literal complex span of "
                + "mu(D,a,-2,b) for all original carrier states a and b. Assume only that the real cast of G is positive definite.")),
            Paragraph(Text("For a charge delta, sectorIdeal(D,delta) consists of oscillator polynomials p whose literal single(delta,p) lies in "
                + "ActualC2.C2(D). The proof makes it an ideal using actual minus-one multiplication and all higher neutral modes. "
                + "Creation coefficients satisfy the ground-field relation, and the consumed exponential derivation gives the Newton "
                + "reduction of every chargePolynomial(D,alpha)^d modulo this ideal. Each X(i,0) is therefore nilpotent in a sector "
                + "quotient, while every X(i,k) with k>0 vanishes.")),
            Describe.Lean(
                DescribeId.Create("actual-c2-cofinite-sector-ideal"),
                DeclarationHandle.Create(Prefix + "sectorIdeal"),
                H("The oscillator ideal in one charge sector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("sectorIdeal(D,delta) is the ideal of oscillator polynomials p for which the original basis state "
                    + "single(delta,p) belongs to the literal actual C2 span. Its closure is proved from the actual neutral minus-one "
                    + "and higher-mode suppliers, not from a replacement quotient or an assumed generic interface."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-c2-cofinite-sector-map"),
                DeclarationHandle.Create(Prefix + "sectorMap"),
                H("The actual quotient map of one charge sector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("sectorMap(D,delta) sends an oscillator polynomial p to the quotient class of the original state "
                    + "single(delta,p) in Carrier(D) / ActualC2.C2(D). Its range is finite-generated once the sector ideal quotient "
                    + "is finite-dimensional."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-c2-cofinite-short-charges"),
                DeclarationHandle.Create(Prefix + "shortCharges"),
                H("The closed finite charge box"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("shortCharges(D) is the set of charges delta satisfying |B(e_i,delta)| <= G_ii for every basis index i. "
                    + "Positive definiteness makes the Gram-coordinate map injective, so this closed integer box is finite. A charge "
                    + "outside it has sectorIdeal(D,delta)=top; the boundary is retained."))),
                DescribeRole.Definition),
            Paragraph(Text("The port follows Fedor K. Popov's Lean_VOA source at commit "
                + "013a799ca834a8a6b3afa8129e3e522025b3f45c. Dong, Li, and Mason, "
                + "arXiv:math/0102127v1, DOI 10.1090/conm/297/05093, pp. 24–26, (5.22)–(5.26), Lemma 5.18, and Proposition 5.19 "
                + "give the classical C2 finite-generation mechanism. The local proof retains the Popov Apache-2.0 attribution and "
                + "uses the repository's actual state-field and carrier declarations.")),
            Describe.Lean(
                DescribeId.Create("actual-c2-cofinite-positive-definite"),
                DeclarationHandle.Create(Prefix + "positive_definite_c2_cofinite"),
                H("Finite-dimensionality of the literal actual C2 quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every LatticeData D and hD:PosDef(D.G.map(Int.cast : Z -> R), the quotient "
                        + "Carrier(D) / ActualC2.C2(D) is finite-dimensional over C. The proof sums the finite ranges of sectorMap "
                        + "over the finite closed short-charge box. It includes rank zero, all charge fibers, all oscillator degrees, "
                        + "and zero exponents; it assumes no determinant-unit or unimodularity condition.")),
                    Paragraph(Text("This is algebraic C2 cofiniteness for the literal constructed carrier and state field. It does not prove a "
                        + "full conformal field theory, anomaly cancellation, fusion completeness, string-theory consistency, or an AdS/CFT "
                        + "correspondence."))),
                DescribeRole.Theorem))));
}
