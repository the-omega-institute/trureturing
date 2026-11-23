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
                        "the right complement receives one rectangle spanning its full height and two rectangles " +
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
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pure-rank-two-kernel-bound"),
                DeclarationHandle.Create(Owner + ".pure_rank_two_kernel_bound"), H("Pure rank-two kernel bound"),
                StatementSource.FromAuthor(Disp(PureRankTwo())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When the left factor shrinks, a common kernel direction separates one isometric " +
                    "right range. The remaining three factors act on the kernel of the isolated left " +
                    "factor, which has positive dimension. Their right stack is injective and gives " +
                    "c ≤ 3(d − c). A neutral three-dimensional coefficient subspace instead gives " +
                    "three orthogonal isometric right ranges."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-four-scalar-gram-iff"),
                DeclarationHandle.Create(Owner + ".native_four_scalar_gram_iff"), H("Exact thresholds above twice the left output"),
                StatementSource.FromAuthor(Disp(Classification(false))), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A positive eigenspace of dimension at least two would give a subspace of " +
                        "codimension at most twice the left output dimension. Such a subspace meets " +
                        "the image of the left stack, contradicting zero compression. The same " +
                        "argument applied to the negative eigenspace leaves Hermitian rank at most two.")),
                    Paragraph(Text(
                        "The common kernel case gives a residual width-three sum with left input " +
                        "dimension at least b − a and right output dimension d − c. The two " +
                        "width-three rectangular estimates give the first two thresholds. Above " +
                        "three times the left output dimension the coefficient kernel vanishes, " +
                        "and the four right ranges fit precisely when four times c is at most d."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-four-scalar-gram-swap-iff"),
                DeclarationHandle.Create(Owner + ".native_four_scalar_gram_swap_iff"), H("Exact thresholds above twice the right output"),
                StatementSource.FromAuthor(Disp(Classification(true))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The coordinate permutations for the exchange of factors preserve the Gram " +
                    "identity and give the right-hand version of each threshold."))),
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
    private static Formula Times(int n, Formula v) => Mul(D((byte)n), v);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Matrix(Formula rows, Formula cols) =>
        Call("Matrix", rows, cols, V("Complex"));
    private static Formula Factors(int width, Formula rows, Formula cols) =>
        new Formula.TypeArrow(Fin(D((byte)width)), Matrix(Fin(rows), Fin(cols)));
    private static Formula Dimensions(Formula body) =>
        All("a", V("Nat"), All("b", V("Nat"), All("c", V("Nat"), All("d", V("Nat"), body))));
    private static Formula AtWidth(int width, Formula a, Formula b, Formula c, Formula d, Formula lam)
    {
        Formula i = V("i");
        Formula X = V("X"), Y = V("Y");
        Formula sum = Seq(new Formula.Subscript(F.Sum, Seq(i, Colon, Fin(D((byte)width)))), Sp,
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

    private static Formula GramSum(int width, string x, string y)
    {
        Formula i = V("i");
        return Seq(new Formula.Subscript(F.Sum, Seq(i, Colon, Fin(D((byte)width)))), Sp,
            Call("kronecker", Apply(V(x), i), Apply(V(y), i)));
    }

    private static Formula PureRankTwo()
    {
        Formula a = V("a"), b = V("b"), c = V("c"), d = V("d");
        Formula X = V("X"), T = V("T"), i = V("i");
        Formula sum = GramSum(4, "X", "Y");
        Formula leftGram = Seq(new Formula.Subscript(F.Sum, Seq(i, Colon, Fin(D(4)))), Sp,
            Mul(Call("conjTranspose", Apply(X, i)), Apply(X, i)));
        Formula rank = All("T", Matrix(Fin(D(4)), Fin(D(4))),
            Implies(Call("IsHermitian", T),
                Implies(Equal(Call("compression", X, T), D(0)),
                    Implies(new Formula.Relation(T, FormulaRelationOperator.NotEqual, D(0)),
                        Equal(Call("rank", T), D(2))))));
        Formula result = Implies(Lt(a, b), Implies(Call("LinearIndependent", V("Complex"), X),
            Implies(Equal(Mul(Call("conjTranspose", sum), sum), D(1)),
                Implies(Equal(leftGram, D(1)), Implies(rank, Le(Times(4, c), Times(3, d)))))));
        return Dimensions(All("X", Factors(4, a, b), All("Y", Factors(4, d, c), result)));
    }

    private static Formula Classification(bool exchange)
    {
        Formula a = V("a"), b = V("b"), c = V("c"), d = V("d"), lam = V("lambda");
        Formula expandingInput = exchange ? b : c;
        Formula shrinkingInput = exchange ? c : b;
        Formula shrinkingOutput = exchange ? d : a;
        Formula rows = exchange ? LargeRows(d, c, b, a) : LargeRows(a, b, c, d);
        return Dimensions(All("lambda", V("Real"), Implies(Lt(D(0), lam),
            Implies(Lt(D(0), expandingInput), Implies(Lt(Times(2, shrinkingOutput), shrinkingInput),
                Iff(Call("FourScalarGram", a, b, c, d, lam), rows))))));
    }
}
