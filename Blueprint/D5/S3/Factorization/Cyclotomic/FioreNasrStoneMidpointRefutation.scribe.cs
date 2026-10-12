using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Cyclotomic;

internal sealed class FioreNasrStoneMidpointRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/Cyclotomic/FioreNasrStoneMidpointRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/fiore2026squaresideddice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At the distinct odd primes three, five and eleven, both complete midpoint "
            + "polynomials have nonnegative integer coefficients.",
        H("An odd midpoint counterexample to Fiore-Nasr-Stone Conjecture 6.8"),
        Blocks(
            Paragraph(Text(
                "Fiore, Nasr and Stone define, for distinct primes p, q and r and exponents "
                    + "a, b, c and d in {0,1,2}, A_abcd = X Phi_p^2 Phi_q^2 Phi_pq^a "
                    + "Phi_pr^b Phi_qr^c Phi_pqr^d and B_abcd = X Phi_r^2 Phi_pq^a "
                    + "Phi_pr^b Phi_qr^c Phi_pqr^d. They pair A_abcd with "
                    + "B_(2-a,2-b,2-c,2-d). At a=b=c=d=1 the complementary exponents "
                    + "are also one. Every factor, including the initial X, is retained below.")),
            Paragraph(Text(
                "Conjecture 6.8 states: \"In the remaining 33 pairs of the polynomials "
                    + "A_abcd and B_(2-a,2-b,2-c,2-d) (including the case where p != 2 "
                    + "for when a=b=c=d=1), one of the two polynomials will have a "
                    + "negative coefficient.\"")),
            Paragraph(Text(
                "The closed assertion below is precisely this explicitly included universal "
                    + "midpoint clause. The primes 3, 5 and 11 are pairwise distinct and meet "
                    + "p != 2; they are also all odd and satisfy p<q<r. The source conjecture "
                    + "therefore requires a negative coefficient for this very pair. Showing "
                    + "that both polynomials have no negative coefficient contradicts that "
                    + "required instance and refutes the whole conjecture. This implication "
                    + "does not identify the midpoint clause with the complete remaining-case "
                    + "assertion or classify any other exponent tuple.")),
            Definition("first-midpoint", "The first complete midpoint polynomial", "midpointA",
                "For natural parameters p, q and r, midpointA is the integer polynomial "
                    + "X Phi_p^2 Phi_q^2 Phi_pq Phi_pr Phi_qr Phi_pqr from Definition 6.1."),
            Definition("second-midpoint", "The complementary midpoint polynomial", "midpointB",
                "For the same natural parameters, midpointB is the integer polynomial "
                    + "X Phi_r^2 Phi_pq Phi_pr Phi_qr Phi_pqr. All four complementary "
                    + "mixed exponents equal one."),
            Definition("claim", "The explicit universal midpoint assertion", "claim",
                "For every triple of natural primes p, q and r, pairwise distinct with p != 2, "
                    + "claim requires some natural-index coefficient of midpointA or midpointB "
                    + "to be strictly negative. The two existential indices are independent "
                    + "and range over all natural numbers. There is no prime-order premise."),
            Describe.Lean(
                DescribeId.Create("fiore-nasr-stone-midpoint-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The explicit midpoint assertion is false"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Write G_m(X) for the finite sum of X^j over 0 <= j < m. Cyclotomic "
                            + "factorization and expansion give the complete polynomial identity "
                            + "A(3,5,11) = X G_3(X) G_5(X) G_3(X^11) G_5(X^33). "
                            + "For the second polynomial they give B(3,5,11) = "
                            + "X (Phi_11(X) Phi_15(X)) G_11(X^15).")),
                    Paragraph(Text(
                        "The remaining product Phi_11(X) Phi_15(X) equals the sum of X^s "
                            + "for s in {0,3,5,6,8,9,10,12,13,15,18}. The signed expansion "
                            + "of Phi_15 is the existing identity Counterexample.cyclotomic_15. "
                            + "Multiplication by G_11 cancels all its negative coefficients. "
                            + "Every displayed sum has nonnegative coefficients. The coefficient "
                            + "of a product is a finite sum of products of coefficients, and "
                            + "substitution X -> X^k inserts zeros. These laws establish "
                            + "nonnegativity at every natural index, including the zero tails.")),
                    Paragraph(Text(
                        "The geometric-sum identity is supplied by "
                            + "GeometricSpectrumFactorization.geometric_sum_eq_cyclotomic_product; "
                            + "Polynomial.cyclotomic_expand_eq_cyclotomic_mul supplies each "
                            + "prime expansion. The factor identities and coefficient arguments "
                            + "are all inside this single result.")),
                    Paragraph(Text(
                        "Table 2 repeats the tuple (2,1,1,2), so the printed number 33 does "
                            + "not define a verified remaining domain. Lemma 6.6 asserts an "
                            + "odd-prime obstruction using the claim that sums of odd-prime "
                            + "multiples are always even; 11=2*3+5 disproves that step. Its "
                            + "classification is not used here. The midpoint is explicitly "
                            + "included in Conjecture 6.8 regardless of these defects. "
                            + "The other exponent cases, a corrected classification, and "
                            + "physical realization of dice remain outside this theorem."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("fiore-nasr-stone-2026-midpoint-negativity"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Definition(string id, string title, string name, string prose) =>
        Describe.Lean(DescribeId.Create("fiore-nasr-stone-" + id),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);
}
