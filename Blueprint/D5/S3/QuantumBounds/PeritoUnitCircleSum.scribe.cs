using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class PeritoUnitCircleSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sum of distances from a unit complex phase to the negatives of the regular d-th roots is at most twice the cosecant of pi over twice d.",
        H("A Regular Unit-Circle Sum Bound"),
        Blocks(
            Paragraph(Text(
                "Let d be an integer at least two and let omega be exp(2 pi i / d). " +
                "For a complex number z of modulus one, consider the sum of |1 + omega^y z| " +
                "over y from zero to d minus one.")),
            Describe.Lean(DescribeId.Create("the-absolute-cosine-sum-bound"), DeclarationHandle.Create("D5/S3/QuantumBounds/PeritoUnitCircleSum.abs_cos_sum_le"), H("The absolute cosine sum"), StatementSource.FromAuthor(Disp(All("d",NatType(),All("s",RealType(),Imp(Leq(new Formula.Number(2),F.Id("d")),Leq(Call("Finset.sum" ,Call("Finset.range" ,F.Id("d")),Lam("y",NatType(),Call("abs" ,Call("Real.cos" ,Add(F.Id("s"),Mul(new Formula.Fraction(Call("Real.pi"),Call("Nat.cast" ,F.Id("d"))),Call("Nat.cast" ,F.Id("y")))))))),new Formula.Fraction(new Formula.Number(1),Call("Real.sin" ,new Formula.Fraction(Call("Real.pi"),Mul(new Formula.Number(2),Call("Nat.cast" ,F.Id("d")))))))))))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every natural d at least two and every real phase s, the sum over y in Finset.range d of the absolute value of Real.cos (s + Real.pi / d * y) is bounded by the half-angle cosecant."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-regular-unit-circle-distance-sum-bound"),
                DeclarationHandle.Create("D5/S3/QuantumBounds/PeritoUnitCircleSum.unit_circle_sum_le"),
                H("The distance sum is bounded uniformly in the phase"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("d"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    D(2), Le, Sp, F.Id("d"), Rightarrow, Sp,
                    Forall, Sp, F.Id("z"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Sp,
                    Vert, Sp, F.Id("z"), Vert, Eq, D(1), Rightarrow, Sp,
                    Sum, Underscore, Grp(F.Id("y"), Eq, D(0)), Caret, Grp(F.Id("d"), Minus, D(1)),
                    Vert, D(1), Plus, F.Id("omega"), Caret, Grp(F.Id("y")), F.Id("z"), Vert,
                    Le, Frac, Grp(D(2)), Grp(Sin, Open, Frac, Grp(Pi), Grp(D(2), F.Id("d")), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Write z as exp(2 i s). Factoring 1 + exp(2 i t) as " +
                        "2 cos(t) exp(i t) shows that the distance sum is " +
                        "twice the sum of |cos(s + pi y / d)|.")),
                    Paragraph(Text(
                        "This absolute cosine sum has period pi / d: shifting the phase " +
                        "cycles the sample indices, and the last sample differs from the " +
                        "first by pi, which preserves the absolute cosine. Reduce s modulo " +
                        "this period to t in [-pi/2, -pi/2 + pi/d). All d sampled angles " +
                        "then lie in [-pi/2, pi/2], where cosine is nonnegative.")),
                    Paragraph(Text(
                        "The finite trigonometric sum identity gives the cosine sum as " +
                        "cos(t + (d - 1) pi / (2 d)) / sin(pi / (2 d)). " +
                        "The denominator is positive and cosine is at most one, giving " +
                        "the stated uniform bound. The same reduction applies to both " +
                        "odd and even values of d."))),
                DescribeRole.Theorem))));
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Q(string name) => Seq(Operatorname, Grp(Seq([.. System.Linq.Enumerable.SelectMany(name.Split('.'), (part, i) => i == 0 ? new[] { F.Id(part) } : new[] { Dot, F.Id(part) })])));
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Q(name) : new Formula.Apply(Q(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Lam(string name, Formula type, Formula body) => Seq(LambdaLower, Sp, Parenthesized(Seq(F.Id(name), Colon, type)), Sp, Mapsto, Sp, body);
    private static Formula NatType() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RealType() => Seq(Mathbb, Grp(F.Id("R")));
}
