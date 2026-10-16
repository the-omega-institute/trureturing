using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class SortedDivisorPolynomialThreePrimesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integral polynomial represents all increasing divisors of an integer with three distinct prime factors.",
        H("The original OEIS A167857 question"),
        Blocks(Describe.Lean(
            DescribeId.Create("a167857-three-distinct-prime-divisors"),
            DeclarationHandle.Create("D5/S3/Arith/SortedDivisorPolynomialThreePrimes.result"),
            H("A term with three distinct prime divisors exists"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Factorization/noe2009a167857")),
            Blocks(
                Paragraph(Text("Choose three increasing primes p, q, r, each congruent to 1 modulo 5040, "
                    + "using Nat.exists_prime_gt_modEq_one. Their product n is positive, has exactly three "
                    + "distinct prime factors and exactly eight positive divisors. Decomposition of a divisor "
                    + "of p*q*r into divisors of the three primes shows that every divisor is 1 modulo 5040.")),
                Paragraph(Text("Let d_i be entry i in the actual increasing sort of Nat.divisors n. "
                    + "For i=0,...,7 let D_i be the product of i-j over the other seven indices and N_i(X) "
                    + "the product of X-j over those indices. The signed D_i are -5040, 720, -240, 144, "
                    + "-144, 240, -720, 5040; each is nonzero and divides 5040. Thus c_i=(d_i-1)/D_i "
                    + "is an integer and f=1+sum_i c_i*N_i belongs to Polynomial Int. Its rational image "
                    + "is 1 plus the existing Lagrange interpolant of d_i-1. Applying "
                    + "Lagrange.eval_interpolate_at_node and injectivity of the integer-to-rational map "
                    + "gives the required integer evaluation at every original zero-based index.")),
                Paragraph(Text("The sorted finset contains all positive divisors of this same n exactly once. "
                    + "The statement imposes no minimum n, degree bound, prescribed numerical candidate, "
                    + "divisor subset or input shift. Polynomial Int ensures integral coefficients; "
                    + "integer-valued rational interpolation alone would not establish this claim.")),
                Paragraph(Text("The source asks: Are there terms with three distinct prime divisors? "
                    + "The proof applies existing Mathlib results on primes in arithmetic progressions "
                    + "and Lagrange interpolation. No new-method or priority claim is made. "
                    + "Source license: CC-BY-SA-4.0."))),
            DescribeRole.Theorem,
            new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("oeis-a167857-sorted-divisor-polynomial-three-primes"),
                ResolutionKind.Proved)))));

    private static Formula Statement()
    {
        var n = F.Id("n");
        var f = F.Id("f");
        var j = F.Id("j");
        var divisors = Call("divisors", n);
        var tau = Call("card", divisors);
        var positive = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, n);
        var three = new Formula.Relation(Call("card", Call("primeFactors", n)),
            FormulaRelationOperator.Equal, D(3));
        var bound = new Formula.Relation(j, FormulaRelationOperator.LessThan, tau);
        var value = new Formula.Relation(new Formula.Apply(f, [j]),
            FormulaRelationOperator.Equal, Call("get", Call("sortIncreasing", divisors), j));
        return Disp(Seq(Exists, Sp, n, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")),
            Comma, Sp, positive, Sp, Land, Sp, three, Sp, Land, Sp,
            Exists, Sp, f, Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), OpenBracket,
            F.Id("X"), CloseBracket, Comma, Sp, Forall, Sp, j, Sp, InMacro, Sp,
            Mathbb, Grp(F.Id("N")), Comma, Sp, bound, Sp, Rightarrow, Sp, value));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
}
