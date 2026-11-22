using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.BridgeGraph;

internal sealed class NativeFourStaircaseDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourStaircase";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Width-four scalar column Grams and the exact large-ratio thresholds.",
        H("Width-four scalar column Grams"),
        Blocks(
            Describe.Lean(DescribeId.Create("four-scalar-gram"),
                DeclarationHandle.Create(Owner + ".FourScalarGram"), H("Column Gram"),
                StatementSource.FromAuthor(Disp(GramDefinition())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The left matrices have a rows and b columns. The right matrices have d rows " +
                    "and c columns. The tensor sum acts from b times c input coordinates to a times d " +
                    "output coordinates. A positive scalar Gram makes this map a scaled isometry."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("staircase"),
                DeclarationHandle.Create(Owner + ".Staircase"), H("Dimension bounds for the constructions"),
                StatementSource.FromAuthor(Disp(StaircaseDefinition())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each upper bound on the left ratio includes equality. The inequalities use " +
                    "integer products, so they also specify the cases when a dimension vanishes."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("staircase-sufficient"),
                DeclarationHandle.Create(Owner + ".staircase_sufficient"), H("Sufficiency in both orientations"),
                StatementSource.FromAuthor(Disp(Sufficiency())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each coordinate rectangle contributes one Kronecker term. Its left and right " +
                        "maps carry the rectangle into its assigned output ranges. Disjoint images " +
                        "make the sum a coordinate isometry. Multiplying the left factors by the " +
                        "square root of lambda produces the specified column Gram.")),
                    Paragraph(Text(
                        "At the four-thirds threshold the excess left inputs share the unused right " +
                        "coordinates across three parts of the right input. At the five-thirds threshold " +
                        "the right complement receives one full-height rectangle and two rectangles " +
                        "with common left output and disjoint right output. At the five-halves threshold " +
                        "two full left blocks use separate right ranges. The two remaining rectangles " +
                        "use disjoint left ranges in the right complement.")),
                    Paragraph(Text(
                        "Exchanging the factors permutes the pairs of input and output coordinates. " +
                        "The input permutation preserves the scalar identity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exact-width-four-at-three-four"),
                DeclarationHandle.Create(Owner + ".exact_width_four_at_three_four"), H("Minimum width at the first corner"),
                StatementSource.FromAuthor(Disp(FirstCorner())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The four-thirds construction gives the column Gram. The width-three rectangular " +
                    "bound requires three times the right input dimension to be at most twice the right " +
                    "output dimension. The dimensions three and four violate that bound."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        Apply(Seq(Operatorname, Grp(V(name))), args);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Parens(Formula p) => Seq(Open, p, Close);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parens(a), op, Parens(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Implies(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Times(int n, Formula v) => Mul(D(n), v);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Matrix(Formula rows, Formula cols) =>
        Call("Matrix", rows, cols, V("Complex"));
    private static Formula Factors(int width, Formula rows, Formula cols) =>
        new Formula.TypeArrow(Fin(D(width)), Matrix(Fin(rows), Fin(cols)));
    private static Formula Dimensions(Formula body) =>
        All("a", V("Nat"), All("b", V("Nat"), All("c", V("Nat"), All("d", V("Nat"), body))));
    private static Formula AtWidth(int width, Formula a, Formula b, Formula c, Formula d, Formula lam)
    {
        Formula i = V("i");
        Formula X = V("X"), Y = V("Y");
        Formula sum = Seq(new Formula.Subscript(F.Sum, Seq(i, Colon, Fin(D(width)))), Sp,
            Call("kronecker", Apply(X, i), Apply(Y, i)));
        Formula cols = Call("Prod", Fin(b), Fin(c));
        Formula identity = Parens(Seq(D(1), Colon, Sp, Matrix(cols, cols)));
        Formula gram = Equal(Mul(Call("conjTranspose", sum), sum),
            Call("smul", Call("ofReal", lam), identity));
        return Some("X", Factors(width, a, b), Some("Y", Factors(width, d, c), gram));
    }

    private static Formula GramDefinition()
    {
        Formula a = V("a"), b = V("b"), c = V("c"), d = V("d"), lam = V("lambda");
        return Dimensions(All("lambda", V("Real"),
            Iff(Call("FourScalarGram", a, b, c, d, lam), AtWidth(4, a, b, c, d, lam))));
    }

    private static Formula Rows(Formula a, Formula b, Formula c, Formula d)
    {
        Formula first = And(Le(b, a), Le(c, d));
        Formula second = And(Lt(a, b), And(Le(Times(3, b), Times(4, a)), Le(Times(4, c), Times(3, d))));
        Formula third = And(Lt(Times(4, a), Times(3, b)),
            And(Le(Times(2, b), Times(3, a)), Le(Times(3, c), Times(2, d))));
        Formula fourth = And(Lt(Times(3, a), Times(2, b)),
            And(Le(Times(3, b), Times(5, a)), Le(Times(5, c), Times(3, d))));
        Formula fifth = And(Lt(Times(5, a), Times(3, b)), And(Le(b, Times(2, a)), Le(Times(2, c), d)));
        return Or(first, Or(second, Or(third, Or(fourth, Or(fifth, LargeRows(a, b, c, d))))));
    }

    private static Formula LargeRows(Formula a, Formula b, Formula c, Formula d)
    {
        Formula sixth = And(Lt(Times(2, a), b),
            And(Le(Times(2, b), Times(5, a)), Le(Times(5, c), Times(2, d))));
        Formula seventh = And(Lt(Times(5, a), Times(2, b)), And(Le(b, Times(3, a)), Le(Times(3, c), d)));
        Formula eighth = And(Lt(Times(3, a), b), And(Le(b, Times(4, a)), Le(Times(4, c), d)));
        return Or(sixth, Or(seventh, eighth));
    }

    private static Formula StaircaseDefinition()
    {
        Formula a = V("a"), b = V("b"), c = V("c"), d = V("d");
        return Dimensions(Iff(Call("Staircase", a, b, c, d), Rows(a, b, c, d)));
    }

    private static Formula Sufficiency()
    {
        Formula a = V("a"), b = V("b"), c = V("c"), d = V("d"), lam = V("lambda");
        Formula cases = Or(Equal(b, D(0)), Or(Equal(c, D(0)),
            Or(Call("Staircase", a, b, c, d), Call("Staircase", d, c, b, a))));
        return Dimensions(All("lambda", V("Real"), Implies(Lt(D(0), lam),
            Implies(cases, Call("FourScalarGram", a, b, c, d, lam)))));
    }

    private static Formula FirstCorner()
    {
        Formula lam = V("lambda");
        return All("lambda", V("Real"), Implies(Lt(D(0), lam),
            And(Call("FourScalarGram", D(3), D(4), D(3), D(4), lam),
                Seq(Neg, Parens(AtWidth(3, D(3), D(4), D(3), D(4), lam))))));
    }
}
