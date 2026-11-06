using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class GenericMatrixIrreducibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full generic determinant and fraction-field characteristic polynomial irreducibility in every positive size.",
        H("Generic Matrix Irreducibility"),
        Blocks(
            Paragraph(Text("For every natural n with 0<n, R is exactly MvPolynomial (Fin n x Fin n) Complex, " +
                "Y is exactly Matrix.mvPolynomialX (Fin n) (Fin n) Complex, and K is FractionRing R. " +
                "There are n squared independent coefficient variables. Both theorems include n=1. " +
                "The determinant conclusion lives in R; the characteristic-polynomial conclusion lives in Polynomial K " +
                "after mapping coefficients by algebraMap R K. No matrix normality, covariance, diagonalizability, " +
                "chosen normal form or extra target premise is imposed.")),
            Describe.Lean(DescribeId.Create("generic-determinant-positive-size"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/GenericMatrixIrreducibility.det_generic_irreducible"),
                H("The full generic determinant"),
                StatementSource.FromAuthor(PositiveSize(Call("Irreducible", Call("det", Generic())))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/etingof2026genericdeterminant")),
                Blocks(
                    Paragraph(Text("The clean Apache-2.0 release theorem det_auxiliaryMatrix_irreducible_of_pos " +
                        "is transplanted faithfully. Its private generic matrix is definitionally Matrix.mvPolynomialX. " +
                        "The exact immutable revision, source digest, full license and NOTICE chain are specified in the library note. " +
                        "Only imports, namespace, source attribute and the public name/signature are adapted; the unused reflexive equality " +
                        "is omitted. Retire this proof when this repository's own pinned Mathlib supplies an equivalent exact theorem, " +
                        "then replace its live uses directly. There is no source novelty claim.")),
                    Paragraph(Text("The proof inducts on positive size. The singleton determinant is one variable. " +
                        "For the induction step, expansion along the first row is linear in the upper left variable. " +
                        "The coefficient is the lower right minor, irreducible by the induction hypothesis and injective renaming. " +
                        "Neither that minor nor the remaining row sum contains the upper left variable. " +
                        "If the minor divided that sum, evaluation of the first row at a single nonzero second entry would force " +
                        "divisibility of a different irreducible minor and hence association. The first minor actually depends on " +
                        "the second diagonal variable: identity evaluation gives one, and setting that entry to zero gives zero. " +
                        "The other minor omits that variable. Association would preserve this variable dependence, a contradiction. " +
                        "The resulting relative primality is the live input of irreducible_mul_X_add.")),
                    Paragraph(Text("The substantive intermediate is minor00_isRelPrime, whose two-minor specialization and " +
                        "variable-dependence contradiction are not supplied by coefficient normalization. " +
                        "The determinant theorem is consumed by charpoly_generic_irreducible_fractionRing in this same module. " +
                        "The source proof contributes mathematical content under the transplantation rule, without claiming research novelty."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("generic-characteristic-fraction-field"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/GenericMatrixIrreducibility.charpoly_generic_irreducible_fractionRing"),
                H("The characteristic polynomial over the exact fraction field"),
                StatementSource.FromAuthor(PositiveSize(Call("Irreducible",
                    Call("map", Call("algebraMap", Ring(), Call("FractionRing", Ring())), Call("charpoly", Generic()))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/bresarspenko2013functional")),
                Blocks(
                    Paragraph(Text("This is the irreducibility assertion of closed Lemma 2.1, specialized to Complex with the full " +
                        "coefficient ring retained. No unused quotient-domain companion is introduced. The local formal bridge first " +
                        "extends the determinant prime to Polynomial R by Polynomial.prime_C_iff. It defines a coefficient " +
                        "evaluation sending each y(i,j) to delta(i,j) times t minus y(i,j), and extends it to a ring homomorphism " +
                        "fixing t. Equality on constants and every generator proves that applying it twice is the identity. " +
                        "The resulting ring equivalence sends the constant determinant to det(tI-Y), which is Matrix.charpoly Y. " +
                        "Irreducibility transports through that equivalence. Matrix.charpoly_monic and " +
                        "Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map then give the exact fraction-field result. " +
                        "The coefficient ring is a unique factorization domain and hence integrally closed.")),
                    Paragraph(Text("After same-delivery dependency inlining, the transplanted determinant induction and its " +
                        "relative-primality intermediate remain on the live proof path. The substitution identities and Gauss transfer " +
                        "are supporting normalization and direct upstream reuse, not separate novelty or escape claims. " +
                        "No new standalone bind-only theorem or unused convenience declaration is retained."))),
                DescribeRole.Theorem),
            Paragraph(Text("Private support is consumed on the live determinant path. genMatrix and genMatrix_apply provide entry access. " +
                "submatrix_eq_rename feeds minor00_eq_rename, submatrix_vars_fst_ne_zero and both minor irreducibility arguments. " +
                "minor00_eq_rename feeds minor00_ne_zero, the relative-primality proof and the final step. " +
                "minor00_vars and rest_vars feed irreducible_mul_X_add. vars_subset_vars_mul_left is used by rename_irreducible " +
                "and the association contradiction; rename_irreducible is used twice by minor00_isRelPrime. " +
                "No private helper is retained only for a promised future consumer.")),
            Paragraph(Text("The source-volume route is 389.1 and 389.2 in AURIC_C128_ORTHOGONAL_TRACE_AND_CORNER_RELATIONS_CONTINUATION. " +
                "These are prerequisites for the closed Lemma 2.1 to Lemma 3.2 route used at equation 320.6 inside that volume's " +
                "theorem 320.1. They do not close the full commuting quadratic trace normal form. The generic centralizer, global " +
                "quadratic reconstruction for all complex bilinear B, Hermitian complexification, real descent, 273/274, direct sums, " +
                "classical sources and complete 320/343/359/361/388 consumers remain unproved here. " +
                "Utility is none: this is uniform ring theory, not a finite checker, numeric reduction or certified instance.")))));

    private static Formula Call(string name, params Formula[] args) =>
        Seq(Operatorname(F.Id(name)), Open, Join(args), Close);
    private static Formula Join(Formula[] args) =>
        Seq(args.SelectMany((a, i) => i == 0 ? new[] { a } : new[] { Comma, Sp, a }).ToArray());
    private static Formula Index() => Call("Fin", F.Id("n"));
    private static Formula Ring() => Call("MvPolynomial", Seq(Index(), Times, Index()), F.Id("Complex"));
    private static Formula Generic() => Call("mvPolynomialX", Index(), Index(), F.Id("Complex"));
    private static Formula PositiveSize(Formula body) => Disp(Seq(
        Forall, Sp, F.Id("n"), Colon, Sp, F.Id("Nat"), Comma, Sp,
        D(0), Sp, Lt, Sp, F.Id("n"), Sp, Implies, Sp, body));
}
