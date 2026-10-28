using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraResolutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraResolution.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/gupta2026miuradegrees");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact residual count satisfies Gupta's total degree bound.",
        H("The uniform residual polynomial"),
        Blocks(
            Paragraph(Text("Gupta, arXiv:2607.05567v3, Conjecture 8.3 asks that the remainder for each positive split a+b=d, a at most b, have total degree at most d-3 when d is at least five. Lemma 8.2 identifies one polynomial on every rectangle with m,n at least 2d-1. The remainder counts precisely the normalized integer unit-edge height functions whose strict minima do not all lie on one common physical side.")),
            Describe.Lean(DescribeId.Create("miura-resolution-fiber-card"),
                DeclarationHandle.Create(Prefix + "fiber_card_eq_positive_vectors"),
                H("Cardinality of each actual fiber"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For all natural a,b,m,n, every K in Core a b, and m,n at least 2(a+b)-1, Nat.card of Fiber a b m n K equals Nat.card of the product PositiveLengths (m-rowOccupied K) (rowRuns K) and PositiveLengths (n-colOccupied K) (colRuns K). The actual equivalence core_positive_vectors_equiv has precisely this fiber as its target, including the complete original height function, JointReduction and the equivalence for every individual physical side. Nat.card_congr therefore applies directly; no quotient, selection of representatives or cardinality assumption is introduced."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miura-resolution-exact-evaluation"),
                DeclarationHandle.Create(Prefix + "core_polynomial_counts_residual"),
                H("The same polynomial counts the original arrays"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For all natural a,b,m,n with a,b positive, a+b at least five, and m,n at least 2(a+b)-1, evaluation of corePolynomial a b at the rational pair (m,n) equals the rational cast of the unchanged residualCount a b m n. The actual partition residualCoreEquiv places every array in exactly one actual Core fiber. residual_count_eq_sum_fibers gives the sum of these cardinalities. The fiber equality above identifies that sum with core_polynomial_eval. Its positive-vector evaluations use positive_lengths_card and the existing binomial polynomial identities, with all feasibility bounds proved for these same cores."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miura-resolution-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The complete original polynomial assertion"),
                StatementSource.FromAuthor(Disp(ClaimBody())), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every natural d at least five and positive natural a,b with a+b=d and a at most b, there exists a rational bivariate polynomial of total degree at most d-3 which counts the exact residual class for every natural m,n at least 2d-1. The polynomial is corePolynomial a b, a finite sum over the individual bounded actual cores; it is chosen before either evaluation dimension. core_polynomial_degree_le gives its strict total degree bound, and core_polynomial_counts_residual supplies every evaluation. The argument also establishes the evaluations without using the order of a and b; the conclusion retains the original ordered-split condition.")),
                    Paragraph(Text("Here residualCount counts every individual function h from Fin m times Fin n to the integers with h(0,0)=0 and absolute difference exactly one across each Manhattan edge. Strict minima and maxima test all existing neighbours, including the two neighbours of a corner and the three neighbours of a noncorner boundary cell. Their exact cardinalities are a and b. The condition is the negation of the existence of one common side containing every minimum: top has first coordinate one, bottom first coordinate m, left second coordinate one, and right second coordinate n in physical coordinates. A corner belongs to both incident sides. The condition permits minima on several boundary sides and introduces no symmetry quotient or orientation identification.")),
                    Paragraph(Text("In the formula, eval uses the assignment i to m if i=0 and to n otherwise, with both dimensions cast to the rationals. The count also has its rational cast. All subtractions in the dimension and degree bounds are natural-number subtractions."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gupta-2026-miura-residual-degree-conjecture-83"),
                    ResolutionKind.Proved)))));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rat() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Cast(Formula a) => Par(Seq(a, Colon, Rat()));

    private static Formula ClaimBody()
    {
        Formula d = F.Id("d"), a = F.Id("a"), b = F.Id("b"), p = F.Id("p"), m = F.Id("m"), n = F.Id("n"), i = F.Id("i");
        Formula assignment = Seq(LambdaLower, Sp, Par(Seq(i, Colon, Call("Fin", D(2)))), Sp, Mapsto, Sp,
            Call("ite", Eq(i, D(0)), Cast(m), Cast(n)));
        Formula evaluation = Eq(Call("eval", Par(assignment), p), Cast(Call("residualCount", a, b, m, n)));
        Formula threshold = Sub(Mul(D(2), d), D(1));
        Formula dimensions = All("m", Nat(), All("n", Nat(), Imp(Le(threshold, m), Imp(Le(threshold, n), evaluation))));
        Formula conclusion = Ex("p", Call("MvPolynomial", Call("Fin", D(2)), Rat()),
            And(Le(Call("totalDegree", p), Sub(d, D(3))), dimensions));
        return All("d", Nat(), All("a", Nat(), All("b", Nat(),
            Imp(Le(D(5), d), Imp(Le(D(1), a), Imp(Le(D(1), b),
                Imp(Eq(Add(a, b), d), Imp(Le(a, b), conclusion))))))));
    }
}
