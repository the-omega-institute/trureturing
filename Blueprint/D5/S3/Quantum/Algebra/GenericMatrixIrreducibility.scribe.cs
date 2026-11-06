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
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Factorization/etingof2026genericdeterminant")),
                Blocks(
                    Paragraph(Text("For positive n, the determinant of the generic matrix is irreducible in R. " +
                        "The induction starts with the one-by-one determinant. In the induction step, expansion along the first row " +
                        "is linear in the upper-left variable, and its coefficient is the lower-right minor. " +
                        "The minor is irreducible by the induction hypothesis after injective renaming.")),
                    Paragraph(Text("The proof inducts on positive size. The singleton determinant is one variable. " +
                        "For the induction step, expansion along the first row is linear in the upper left variable. " +
                        "The coefficient is the lower right minor, irreducible by the induction hypothesis and injective renaming. " +
                        "Neither that minor nor the remaining row sum contains the upper left variable. " +
                        "If the minor divided that sum, evaluation of the first row at a single nonzero second entry would force " +
                        "divisibility of a different irreducible minor and hence association. The first minor actually depends on " +
                        "the second diagonal variable: identity evaluation gives one, and setting that entry to zero gives zero. " +
                        "The other minor omits that variable. Association would preserve this variable dependence, a contradiction. " +
                        "The resulting relative primality is the input of irreducible_mul_X_add.")),
                    Paragraph(Text("The key intermediate is minor00_isRelPrime. Its two-minor specialization and the " +
                        "variable-dependence contradiction establish the relative primality needed for the determinant induction, " +
                        "and that irreducibility supplies the starting point for the characteristic-polynomial argument below."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("generic-characteristic-fraction-field"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/GenericMatrixIrreducibility.charpoly_generic_irreducible_fractionRing"),
                H("The characteristic polynomial over the exact fraction field"),
                StatementSource.FromAuthor(PositiveSize(Call("Irreducible",
                    Call("map", Call("algebraMap", Ring(), Call("FractionRing", Ring())), Call("charpoly", Generic()))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Factorization/bresarspenko2013functional")),
                Blocks(
                    Paragraph(Text("For the complex coefficient ring, first extend the determinant prime to Polynomial R by " +
                        "Polynomial.prime_C_iff. Define a coefficient " +
                        "evaluation sending each y(i,j) to delta(i,j) times t minus y(i,j), and extend it to a ring homomorphism " +
                        "fixing t. Equality on constants and every generator proves that applying it twice is the identity. " +
                        "The resulting ring equivalence sends the constant determinant to det(tI-Y), which is Matrix.charpoly Y. " +
                        "Irreducibility transports through that equivalence. Matrix.charpoly_monic and " +
                        "Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map then give the exact fraction-field result. " +
                        "The coefficient ring is a unique factorization domain and hence integrally closed.")),
                    Paragraph(Text("The determinant prime in R becomes prime in Polynomial R. The coefficient substitution " +
                        "sending y(i,j) to delta(i,j) times t minus y(i,j) extends to a ring homomorphism fixing t. " +
                        "Its application twice fixes every coefficient and t, so it is an involution. The resulting ring equivalence " +
                        "carries the constant determinant to det(tI-Y), which is Matrix.charpoly Y, and therefore transports irreducibility. " +
                        "Gauss's lemma then transfers irreducibility from Polynomial R to Polynomial K; monicity identifies the mapped " +
                        "polynomial with the stated fraction-field characteristic polynomial."))),
                DescribeRole.Theorem),
            Paragraph(Text("For every positive n, the determinant over R and the mapped characteristic polynomial over K are therefore " +
                "irreducible. These conclusions provide the generic irreducibility input for the sections 2–3 argument toward Lemma 3.2 " +
                "at equation (320.6) inside theorem 320.1 of AURIC_C128_ORTHOGONAL_TRACE_AND_CORNER_RELATIONS_CONTINUATION. " +
                "They do not by themselves establish the commuting quadratic trace normal form: the generic centralizer, the global " +
                "quadratic reconstruction for every complex-bilinear B, Hermitian complexification, real descent, 273/274, direct sums, " +
                "classical sources, and the complete downstream statements at 320/343/359/361/388 remain separate mathematical obligations.")))));

    private static Formula Call(string name, params Formula[] args) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, Join(args), Close);
    private static Formula Join(Formula[] args) =>
        Seq(args.SelectMany((a, i) => i == 0 ? new[] { a } : new[] { Comma, Sp, a }).ToArray());
    private static Formula Index() => Call("Fin", F.Id("n"));
    private static Formula Ring() => Call("MvPolynomial", Seq(Index(), Times, Index()), F.Id("Complex"));
    private static Formula Generic() => Call("mvPolynomialX", Index(), Index(), F.Id("Complex"));
    private static Formula PositiveSize(Formula body) => Disp(Seq(
        Forall, Sp, F.Id("n"), Colon, Sp, F.Id("Nat"), Comma, Sp,
        D(0), Sp, Lt, Sp, F.Id("n"), Sp, Implies, Sp, body));
}
