using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Percolation;

internal sealed class RomikCylinderPfaffianDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Percolation/RomikCylinderPfaffian.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/akyazizavadski2026romik");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The explicit nested-arch cylinder Pfaffian is regular on the closed integer range and reduces by a unit pair at its boundary.",
        H("Rational cylinder Pfaffians and their boundary"),
        Blocks(
            Describe.Lean(DescribeId.Create("cylinder-matrix"), DeclarationHandle.Create(Prefix + "cylinderMatrix"),
                H("Explicit cylinder matrix"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every natural m and rational x, cylinderMatrix(m,x) is a rational matrix on Fin(2m). The endpoints are in alternating white, black order, with block indices r,s from 0 through m-1. The four entries are the expressions (4.8), (4.10), (4.11), and (4.9) in that order across the two rows of the block. They use (4.12) for the signed p term and (5.1), (5.2), (5.3) for H, extended by antisymmetry and a zero diagonal. The source identifies these blocks with inverse Kasteleyn entries for integer x>m≥1.")),
                    Paragraph(Text("The white summation indices run from r+2 to 2r+2 and the black indices from 1 to 2r+2, with the corresponding bounds for s. The white weight is the binomial coefficient with upper index c-1 and lower index 2r-c+2. The black weight sums the binomial coefficient with upper index c and lower index 2r-c-j+2 over j from 0 through 2r-c+2. Negative lower binomial indices contribute zero. The signed integer products in (5.1) use inclusive endpoints, including zero factors and empty products. The rational paired factors have numerator x²-a² and denominator 4x²-a²."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cylinder-boundary"), DeclarationHandle.Create(Prefix + "cylinder_pfaffian_boundary"),
                H("Boundary unit pair"), StatementSource.FromAuthor(Boundary()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural n, specialize at x=n+1. Every white index c for the last block r=n satisfies n+2≤c≤2(n+1). The product in (4.12) and the outer product in (5.1) then contain a vanishing numerator at a=n+1, with all variable denominator factors nonzero. Hence the last white row vanishes against earlier endpoints and has entry one to its paired black endpoint by the delta term of (4.10). Skew symmetry in the white-white and white-black entries gives a zero penultimate column above the diagonal. Restriction to the first 2n indices is cylinderMatrix(n,n+1), and forced-pair reduction gives the stated equality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("regular-at"), DeclarationHandle.Create(Prefix + "regularAt"),
                H("Regular rational functions"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each rational x, regularAt(x) is the subring of RatFunc over the rationals consisting of functions whose reduced denominator has nonzero evaluation at x. Divisibility of the reduced denominators for sums and products proves closure. Canonical evaluation on this subring is a ring homomorphism."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("rational-cylinder"), DeclarationHandle.Create(Prefix + "rationalCylinder"),
                H("Rational cylinder function"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural m, rationalCylinder(m) is the normalized Pfaffian over RatFunc of the same explicit 2m by 2m matrix expressions, interpreted in the rational-function field with x the indeterminate. The formula uses the same signed products, finite sums, and coefficients as cylinderMatrix."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("evaluate-rational-cylinder"), DeclarationHandle.Create(Prefix + "evaluate_rationalCylinder"),
                H("Closed integer range specialization"), StatementSource.FromAuthor(Specialization()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For all natural m,k with m≤k, including m=k and m=0, the rationalCylinder(m) function belongs to regularAt(k) and its canonical RatFunc.eval with the identity ring homomorphism on the rationals at the rational cast of k equals the normalized Pfaffian of cylinderMatrix(m,k). Every paired-product or summand denominator 4k²-t² has t<2k for a matrix entry, so the entries belong to the regular subring. Evaluation commutes with sums, products and the normalized Pfaffian there. The matrix of evaluated entries equals cylinderMatrix(m,k). This proves both conjuncts without assuming a boundary probability identity."))), DescribeRole.Theorem)
        )));

    private static Formula Boundary()
    {
        Formula n = F.Id("n"), k = Add(n, D(1));
        return Disp(All("n", Nat, Eq(Pf(k, k), Pf(n, k))));
    }
    private static Formula Specialization()
    {
        Formula m = F.Id("m"), k = F.Id("k"), f = Call("rationalCylinder", m);
        return Disp(All("m", Nat, All("k", Nat, Imp(Leq(m, k),
            Both(Member(f, Call("regularAt", k)), Eq(Eval(k, f), Pf(m, k)))))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Both(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Pf(Formula m, Formula x) => Call("pfaffian", Call("cylinderMatrix", m, x));
    private static Formula Eval(Formula x, Formula f) => Call("eval", x, f);

}
