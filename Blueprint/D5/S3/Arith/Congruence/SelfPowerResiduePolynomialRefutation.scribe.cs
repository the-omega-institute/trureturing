using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class SelfPowerResiduePolynomialRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/SelfPowerResiduePolynomialRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Factorization/englander2020a081215");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original domain of Englander XVII includes three even inputs incompatible with any affine complex polynomial.", H("The full polynomial-existence assertion is false"), Blocks(
            Describe.Lean(DescribeId.Create("self-power-selfpowerresiduepolynomialrefutation-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("One fixed polynomial for every residue class"),
                StatementSource.FromAuthor(Disp(Iff(Call("claim"), ClaimFormula()))), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every positive natural k there is one family P, whose first 2k entries have degree exactly k. The same family must work simultaneously for every natural n greater than k. The coefficient field is C, so real and rational coefficients are included. Entries beyond the first 2k are immaterial. The exact integer sequence a and Euclidean remainder are shared with the cubic theorem."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("self-power-selfpowerresiduepolynomialrefutation-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The literal closed claim is refuted"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Par(Call("claim"))))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("At k=1, inputs 2, 4 and 6 are all even and all satisfy n>k. Their exact quotient values are 1, 41 and 5713, so the remainders modulo n-1 are 0, 2 and 3. Mathlib eq_X_add_C_of_natDegree_le_one expresses the even-class polynomial as an affine polynomial. Its three values must have zero second difference, while these values have second difference -1. The contradiction holds over C, and therefore excludes unrestricted real coefficients as well. The result concerns the full existence claim; the separate printed zero-class formula error is not counted as another problem. No statement about eventual polynomiality or the revised domain k>=2 is asserted."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("englander-a081215-xvii-polynomial-refutation"), ResolutionKind.Refuted)))));
    private static Formula V(string n) => F.Id(n);
    private static Formula Call(string n, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(n), [..args]);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Par(a), b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(Par(a), op, Par(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Ex(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Int() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Complex() => Seq(Mathbb, Grp(V("C")));
    private static Formula Cast(Formula a, Formula t) => Par(Seq(a, Colon, Sp, t));
    private static Formula Mod(Formula a, Formula m) => Call("emod", a, m);

    private static Formula ClaimFormula()
    {
        var k = V("k"); var n = V("n"); var r = V("r");
        var twoK = Seq(D(2), Star, k);
        var poly = Seq(Complex(), OpenBracket, V("X"), CloseBracket);
        var familyType = Seq(Nat(), Sp, To, Sp, poly);
        var degrees = All("r", Nat(), Imp(Lt(r, twoK), Eqn(Call("natDegree", Call("P", r)), k)));
        var modulus = Seq(Pow(Cast(n, Int()), k), Plus, Pow(Seq(Minus, D(1)), k));
        var evaluations = All("n", Nat(), Imp(Lt(k, n), Eqn(Call("eval", Call("P", Call("mod", n, twoK)), Cast(n, Complex())),
            Cast(Mod(Call("a", n), modulus), Complex()))));
        return All("k", Nat(), Imp(Lt(D(0), k), Ex("P", familyType, And(degrees, evaluations))));
    }

}
