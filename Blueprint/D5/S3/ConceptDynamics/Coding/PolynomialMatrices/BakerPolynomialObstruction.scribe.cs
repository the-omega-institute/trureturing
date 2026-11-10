using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PolynomialMatrices;

internal sealed class BakerPolynomialObstructionDocument : IScribeDocumentDefinition
{
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Ex(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Polynomials => Call("Polynomial", Id("Nat"));
    private static Formula Matrices => Call("Matrix", Call("Fin", Num(2)), Call("Fin", Num(2)), Polynomials);
    private static Formula LagClaim()
    {
        Formula a = Id("A"), b = Id("B"), r = Id("R"), s = Id("S"), n = Id("n");
        return All("n", Id("Nat"), new Formula.Not(Ex("R", Matrices, Ex("S", Matrices,
            And(Equal(Mul(a, r), Mul(r, b)), And(Equal(Mul(b, s), Mul(s, a)),
            And(Equal(Mul(r, s), Call("pow", a, n)), Equal(Mul(s, r), Call("pow", b, n)))))))));
    }
    private static Formula ChainClaim() => All("L", Id("Nat"),
        new Formula.Not(Call("ExchangeChain", Polynomials, Id("A"), Id("B"), Id("L"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Baker polynomial pair admits neither coupled lag witnesses nor a finite rectangular exchange chain over the natural-coefficient polynomial semiring.",
        H("Baker polynomial obstruction"), Blocks(
            Paragraph(Text("The coefficient semiring is Polynomial Nat, equivalently polynomials with nonnegative integer coefficients. A and B below are fixed two by two matrices. The source question occurs in Emmanuel Jeandel, Combinatorial Search for Strong Shift Equivalence, arXiv:2609.03567v1, archived SSE.tex lines 731-738, after the end of the rendered document at line 628. It is an externally authored archived draft question, without a published rendered problem number.")),
            Describe.Lean(DescribeId.Create("baker-polynomial-first-matrix"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PolynomialMatrices/BakerPolynomialObstruction.A"),
                H("First endpoint"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/ConceptDynamics/jeandel2026sse")),
                Blocks(Paragraph(Text("A has rows (1, X+1) and (X, 1), with every entry in Polynomial Nat."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("baker-polynomial-second-matrix"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PolynomialMatrices/BakerPolynomialObstruction.B"),
                H("Second endpoint"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/ConceptDynamics/jeandel2026sse")),
                Blocks(Paragraph(Text("B has rows (1, X^2+X) and (1, 1), with every entry in Polynomial Nat."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("baker-polynomial-no-lag"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PolynomialMatrices/BakerPolynomialObstruction.no_lag"),
                H("No coupled lag witnesses"), StatementSource.FromAuthor(LagClaim()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural number n, including zero, there are no two by two matrices R,S over Polynomial Nat satisfying all four equations AR=RB, BS=SA, RS=A^n, SR=B^n. There are no additional positivity, invertibility, degree, nonzero-entry or positive-lag hypotheses.")),
                    Paragraph(Text("The intertwining equations force R to have rows (a,(X+1)c),(c,Xa), and S to have rows (Xh,(X+1)g),(g,h). Map coefficients injectively into the rationals. The determinant of A is p=1-X-X^2. Its irreducibility follows directly from dbonacci_irreducible at order two, the existing negated-indeterminate automorphism, and multiplication by the unit -1. The determinant equation forces both intertwiner determinants to be nonzero divisors of p^n and hence to have even degree.")),
                    Paragraph(Text("Each determinant has the form Xf^2-(X+1)k^2. If it is nonzero of even degree, both inputs are nonzero and have equal degree: otherwise its highest surviving term has odd degree. Back over natural coefficients, sums cannot cancel their leading terms. The two entries in the first row of RS therefore have the same degree and its upper-right entry is nonzero. The recurrence d(n+1)=d(n)+X*u(n), u(n+1)=(X+1)*d(n)+u(n) for the first row of A^n proves their degrees differ by one at every positive n. This contradicts RS=A^n; for n=0 its upper-right entry contradicts the identity matrix.")),
                    Paragraph(Text("The proof combines determinant-degree parity with the positive-coefficient product and power recurrences. It does not require the fourth equation once the other three have been assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("baker-polynomial-no-exchange-chain"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PolynomialMatrices/BakerPolynomialObstruction.no_exchange_chain"),
                H("No finite rectangular exchange chain"), StatementSource.FromAuthor(ChainClaim()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural length L, ExchangeChain (Polynomial Nat) A B L is impossible. The existing exchange_chain_lag theorem supplies the same coupled witnesses at lag L for any such chain, so no restriction on any finite rectangular intermediate dimension is introduced. Zero length remains included.")),
                    Paragraph(Text("The source-qualified negative answer concerns precisely the archived draft polynomial question. It asserts no general result about integer evaluations of Baker matrices, polynomials with real coefficients, priority, uniqueness, or an unqualified solved published problem."))), DescribeRole.Theorem))));
}
