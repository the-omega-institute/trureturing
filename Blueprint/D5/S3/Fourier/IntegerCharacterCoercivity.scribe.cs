using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class IntegerCharacterCoercivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite integer character defect controls squared Euclidean distance to its full periodic zero set.",
        H("Global Integer Character Coercivity"),
        Blocks(Describe.Lean(
            DescribeId.Create("integer-character-global-euclidean-coercivity"),
            DeclarationHandle.Create("D5/S3/Fourier/IntegerCharacterCoercivity."
                + "integer_character_global_coercivity"),
            H("Uniform quadratic distance bound"),
            StatementSource.FromAuthor(CoercivityFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every natural dimension q, every finite index type I, and every "
                    + "integer row family lambda indexed by I and Fin(q), there is a positive "
                    + "real constant c that works for every vector x in the actual Euclidean "
                    + "space. Each phase is the real sum of lambda(a,i) times x(i). The set "
                    + "inside infDist contains every vector whose phases are all integral "
                    + "multiples of 2 pi; the integer may depend on the row.")),
                Paragraph(Text(
                    "No nonemptiness, rank, injectivity, or primitive-image assumption is "
                    + "required. The assertion includes dimension zero, an empty family, "
                    + "zero rows, rank deficiency, and all disconnected periodic components. "
                    + "For the one-dimensional charge 2, pi is a zero as well as 2 pi.")),
                Paragraph(Text(
                    "A bounded preimage for the linear phase map gives a uniform distance "
                    + "bound to each affine kernel fiber. In a uniform neighborhood of any "
                    + "periodic zero y, the scalar cosine inequality bounds the sum of squared "
                    + "phases of x - y. On a compact cube outside that neighborhood, continuity gives "
                    + "a positive minimum. Translations by 2 pi times integer coordinate vectors "
                    + "preserve both the defect and distance to the full zero set, extending the bound "
                    + "to every vector.")),
                Paragraph(Text(
                    "This is a deterministic analytic inequality for the explicitly displayed "
                    + "periodic zero set. It does not identify that set with a Markov model's "
                    + "gauge subgroup or prove Gaussian decay of Markov powers. Actual-path "
                    + "synchronization and the gauge identification are separate obligations."))),
            DescribeRole.Theorem))));

    private static Formula NumberType(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [Bound(name, domain)], body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [Bound(name, domain)], body);
    private static Formula Relation(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Arrow(Formula left, Formula right) =>
        Seq(left, Sp, Rightarrow, Sp, right);
    private static Formula SumOver(string index, Formula domain, Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id(index), InMacro, Sp, domain), Sp, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula CoercivityFormula()
    {
        Formula q = F.Id("q");
        Formula iType = F.Id("I");
        Formula indices = Call("Fin", q);
        Formula reals = NumberType("R");
        Formula integers = NumberType("Z");
        Formula space = Call("EuclideanSpace", reals, indices);
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula c = F.Id("c");
        Formula Phase(Formula vector) => SumOver("i", indices,
            Multiply(Call("lambda", F.Id("a"), F.Id("i")), Call("coord", vector, F.Id("i"))));
        Formula zeros = Seq(Left, OpenBrace,
            Relation(y, FormulaRelationOperator.MemberOf, space), Sp, Mid, Sp,
            All("a", iType, Some("k", integers,
                Relation(Phase(y), FormulaRelationOperator.Equal,
                    Multiply(Multiply(D(2), Call("pi")), F.Id("k"))))), Right, CloseBrace);
        Formula defect = SumOver("a", iType,
            Parenthesized(new Formula.Binary(
                D(1), FormulaBinaryOperator.Subtract, Call("cos", Phase(x)))));
        Formula inequality = Relation(
            Multiply(c, new Formula.Power(Call("infDist", x, zeros), D(2))),
            FormulaRelationOperator.LessThanOrEqual, defect);
        Formula conclusion = Some("c", reals,
            new Formula.Logic(Relation(D(0), FormulaRelationOperator.LessThan, c),
                FormulaLogicOperator.And, All("x", space, inequality)));
        return Disp(All("q", NumberType("N"), All("I", Call("FiniteType"),
            All("lambda", Arrow(iType, Arrow(indices, integers)), conclusion))));
    }
}
