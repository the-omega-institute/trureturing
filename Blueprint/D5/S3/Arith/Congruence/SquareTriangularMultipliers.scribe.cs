using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class SquareTriangularMultipliersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/SquareTriangularMultipliers.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuadraticForms/ratushnyak2026a400520");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every natural index has a least positive multiplier satisfying the two independent square and triangular alternatives of A400520.",
        H("Positive square-and-triangular multipliers"), Blocks(
            Describe.Lean(DescribeId.Create("square-triangular-multipliers-square"),
                DeclarationHandle.Create(Prefix + "Sq"), H("Natural squares"),
                StatementSource.FromAuthor(Disp(All("x", Nat(), Iff(Call("Sq", V("x")),
                    Some("s", Nat(), Eqn(V("x"), Pow(V("s"), D(2)))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The root is a natural number. In particular, zero is a square."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("square-triangular-multipliers-triangular"),
                DeclarationHandle.Create(Prefix + "Tri"), H("Natural triangular numbers"),
                StatementSource.FromAuthor(Disp(All("x", Nat(), Iff(Call("Tri", V("x")),
                    Some("t", Nat(), Eqn(Mul(D(2), V("x")), Mul(V("t"), Add(V("t"), D(1))))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The triangular index is natural and may be zero. The equation avoids truncated division."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("square-triangular-multipliers-predicate"),
                DeclarationHandle.Create(Prefix + "P"), H("The original independent alternatives"),
                StatementSource.FromAuthor(Disp(All("n", Nat(), All("k", Nat(),
                    Iff(Call("P", V("n"), V("k")), And(
                        Or(Call("Sq", Mul(V("n"), V("k"))), Call("Sq", Add(Mul(V("n"), V("k")), D(1)))),
                        Or(Call("Tri", Mul(V("n"), V("k"))), Call("Tri", Add(Mul(V("n"), V("k")), D(1)))))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A square and a triangular number can be supplied by different members of the pair. Positivity of the multiplier is imposed separately."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("square-triangular-multipliers-sequence"),
                DeclarationHandle.Create(Prefix + "a"), H("The least positive multiplier or minus one"),
                StatementSource.FromAuthor(Disp(All("n", Nat(), And(
                    Imp(ExistsWitness(V("n")), Some("k", Nat(), Least(V("n"), V("k")))),
                    Imp(Not(ExistsWitness(V("n"))), Eqn(Call("a", V("n")), new Formula.Negate(D(1)))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("This characterizes the integer-valued definition: select the least natural k satisfying both 1<=k and P(n,k), if one exists, and use -1 otherwise. The minimum is taken for the original predicate P, rather than only for simultaneous square triangular multiples. The positive-multiplier convention is supported by the listed initial values and source program; the NAME itself says only multiplier."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("square-triangular-multipliers-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Positivity and exact least-witness semantics at every index"),
                StatementSource.FromAuthor(Disp(And(
                    All("n", Nat(), And(Lt(D(0), Call("a", V("n"))), Some("k", Nat(), Least(V("n"), V("k"))))),
                    And(Eqn(Call("a", D(0)), D(1)), Eqn(Call("a", D(1)), D(1)))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("There are no hypotheses on n and no finite cutoff. For n>0, use Mathlib's Pell.xn and Pell.yn at parameter a=3, so the discriminant a^2-1 is 8. Their natural coordinates x(j), y(j) start at (1,0), satisfy x(j)^2=8y(j)^2+1, and obey x(j+1)=3x(j)+8y(j) and y(j+1)=x(j)+3y(j). Mathlib's Pell.yn_ge_n makes y(j)>0 at every positive j.")),
                    Paragraph(Text("Reduce the same pair recurrence modulo n. Its inverse is (u,v) -> (3u-8v,-u+3v), so it is injective on the finite set ZMod(n) x ZMod(n). Function.Injective.mem_periodicPts supplies a positive return time j to (1,0). Induction identifies this finite orbit with the reductions of the actual Pell coordinates, hence n divides y(j). This argument applies to every positive modulus, including one and composite moduli.")),
                    Paragraph(Text("Induction on the x recurrence gives x(j) odd. Write x(j)=2t+1 and y(j)=nq. The Pell identity gives 2y(j)^2=t(t+1). Since y(j)>0, q>0, and k=nq^2 is positive. Then nk=y(j)^2 is both square and triangular, which implies each of the original alternatives. At n=0, k=1 works with square root and triangular index zero. The least-witness principle applied to P gives the displayed positive integer a(n), its witness and its minimality. At n=0 and n=1, k=1 itself satisfies P, so positivity and minimality force both initial values to equal one.")),
                    Paragraph(Text("The source is the OEIS conjecture cited above. The Pell identities, growth bound and finite injective dynamics are reused established results. The conclusion settles the stated multiplier assertion; it supplies no formula for the least multiplier."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("oeis-a400520-positive-square-triangular-multipliers"), ResolutionKind.Proved)))));

    private static Formula V(string n) => F.Id(n);
    private static Formula Call(string n, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. args]);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Int() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Cast(Formula a) => Par(Seq(a, Colon, Sp, Int()));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Par(a), b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(Par(a), op, Par(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Not(Formula a) => Seq(Neg, Sp, Par(a));
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Some(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula ExistsWitness(Formula n) => Some("k", Nat(), And(Le(D(1), V("k")), Call("P", n, V("k"))));
    private static Formula Least(Formula n, Formula k) => And(Le(D(1), k), And(Call("P", n, k),
        And(Eqn(Call("a", n), Cast(k)), All("j", Nat(), Imp(Le(D(1), V("j")), Imp(Call("P", n, V("j")), Le(k, V("j"))))))));
}
