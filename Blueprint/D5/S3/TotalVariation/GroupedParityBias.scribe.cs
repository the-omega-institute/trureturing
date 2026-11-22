using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class GroupedParityBiasDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bias recovery for independent binary inputs under a fixed affine readout.",
        H("Grouped biases of an affine parity law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("affine-law-iff-grouped-bias"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/GroupedParityBias.affine_law_iff_grouped_bias"),
                H("The output law determines the bias product of each nonzero column"),
                StatementSource.FromAuthor(RecoveryStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite additive group A satisfies x+x=0 for every x. The column "
                    + "map c and the affine offset s are fixed. A bias factor q(i) in (0,1) "
                    + "corresponds to input probability (1-q(i))/2. The mass L(q,y) is the "
                    + "pushforward of the independent input product by the affine readout. "
                    + "The product G(q,a) collects the bias factors of columns equal to a. "
                    + "Two laws agree exactly when these products agree for every nonzero a. "
                    + "The explicit recovery formula takes logarithms of absolute sign "
                    + "moments, so the recovered products do not depend on the offset sign. "
                    + "For section 35.6.8 in Quantum Geometry, take A to be the quotient by "
                    + "the fair-input image. Each c(i) is the projected column of a biased "
                    + "input and s is the projected offset. In Y, the contribution of c(i) "
                    + "is zero when x(i) is false and c(i) when x(i) is true."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("affine-bias-identifiable"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/GroupedParityBias.affine_bias_identifiable_iff"),
                H("Individual identifiability of bias factors"),
                StatementSource.FromAuthor(IdentifiabilityStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On the open interval of bias factors, the map from parameter vectors "
                    + "to laws is injective exactly when every column is nonzero and c is "
                    + "injective. With a zero column, changing the factor of that column "
                    + "keeps the law. For two equal columns, moving a factor of one third "
                    + "between their indices keeps the group product when all other factors "
                    + "are one half. With distinct nonzero columns every group product "
                    + "contains exactly the factor of its own input."))),
                DescribeRole.Theorem))));

    private static Formula RecoveryStatement()
    {
        Formula a = F.Id("a");
        Formula space = F.Id("A");
        Formula q = F.Id("q");
        Formula r = F.Id("r");
        Formula y = F.Id("y");
        Formula g = F.Id("G");
        Formula l = F.Id("L");
        Formula moment = F.Id("m");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula bias = Arrow(F.Id("I"), real);
        Formula chars = At(Name("AddChar"), Seq(space, Comma, Seq(Mathbb, Grp(F.Id("C")))));
        Formula sig = At(F.Id("v"), Seq(Psi, Comma, a));
        return Disp(new Formula.Aligned([
            .. Context(fintype: true),
            .. LawRows(),
            Let(At(F.Id("v"), Seq(Typed(Psi, chars), Comma, Typed(a, space))),
                Seq(Re, Sp, At(Psi, a))),
            Let(At(g, Seq(Typed(q, bias), Comma, Typed(a, space))),
                Seq(new Formula.Subscript(Prod, Seq(F.Id("i"), Colon, Sp, At(F.Id("c"), F.Id("i")),
                    Eq, a)), At(q, F.Id("i")))),
            Let(At(moment, Seq(Typed(q, bias), Comma, Typed(Psi, chars))),
                Seq(new Formula.Subscript(Sum, Seq(y, Sp, InMacro, Sp, space)),
                    At(l, Seq(q, Comma, y)), At(F.Id("v"), Seq(Psi, Comma, y)))),
            Seq(Forall, Sp, Typed(q, bias), Typed(r, bias), Comma, InUnitCube(q), Sp,
                Land, Sp, InUnitCube(r), Sp, Longrightarrow),
            Seq(Open, Open, Forall, Sp, Typed(y, space), Comma,
                At(l, Seq(q, Comma, y)), Eq, At(l, Seq(r, Comma, y)), Close,
                Sp, Leftrightarrow, Sp, Nonzero(a, space),
                At(g, Seq(q, Comma, a)), Eq, At(g, Seq(r, Comma, a)), Close, Sp, Land),
            Seq(Nonzero(a, space), Log, Sp, At(g, Seq(q, Comma, a)), Eq,
                new Formula.Fraction(Seq(Minus, D(2)), new Formula.Absolute(space)),
                new Formula.Subscript(Sum, Seq(Psi, Sp, InMacro, Sp, chars)),
                sig, Sp, Log, Sp, new Formula.Absolute(At(moment, Seq(q, Comma, Psi))))
        ]));
    }

    private static Formula IdentifiabilityStatement()
    {
        Formula c = F.Id("c");
        Formula i = F.Id("i");
        Formula q = F.Id("q");
        return Disp(new Formula.Aligned([
            .. Context(fintype: false),
            .. LawRows(),
            Seq(At(Name("InjOn"), Seq(F.Id("L"), Comma, OpenBrace, q, Bar, InUnitCube(q), CloseBrace)),
                Sp, Leftrightarrow, Sp, Open, Forall, Sp, Typed(i, F.Id("I")), Comma,
                At(c, i), Sp, Neq, Sp, D(0), Close, Sp, Land, Sp, At(Name("Injective"), c))
        ]));
    }

    private static Formula[] Context(bool fintype)
    {
        Formula a = F.Id("A");
        Formula i = F.Id("I");
        Formula x = F.Id("x");
        return [
            Seq(Forall, Sp, Typed(a, Name("Type")), Typed(i, Name("Type")), Comma),
            Seq(Grp(), Instance("AddCommGroup", a), Instance(fintype ? "Fintype" : "Finite", a),
                Instance("Fintype", i), Comma),
            Seq(Typed(F.Id("c"), Arrow(i, a)), Typed(F.Id("s"), a), Comma,
                Open, Forall, Sp, Typed(x, a), Comma, x, Plus, x, Eq, D(0), Close, Sp, Longrightarrow)
        ];
    }

    private static Formula[] LawRows()
    {
        Formula a = F.Id("A");
        Formula i = F.Id("i");
        Formula index = F.Id("I");
        Formula x = F.Id("x");
        Formula q = F.Id("q");
        Formula y = F.Id("y");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula cube = Arrow(index, Name("Bool"));
        Formula readout = Seq(F.Id("s"), Plus, new Formula.Subscript(Sum, i),
            new Formula.Subscript(x, i), At(F.Id("c"), i));
        return [
            Let(At(F.Id("Y"), Typed(x, cube)), readout),
            Let(At(F.Id("L"), Seq(Typed(q, Arrow(index, real)), Comma, Typed(y, a))),
                Seq(new Formula.Subscript(Sum, Seq(x, Sp, InMacro, Sp, Parenthesized(cube),
                    Colon, Sp, At(F.Id("Y"), x), Eq, y)),
                    new Formula.Subscript(Prod, i),
                    new Formula.Fraction(Seq(D(1), Plus,
                        new Formula.Power(Parenthesized(Seq(Minus, D(1))), new Formula.Subscript(x, i)),
                        At(q, i)), D(2))))
        ];
    }

    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula content) => Seq(Open, content, Close);
    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Parenthesized(argument));
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Arrow(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula Instance(string name, Formula type) =>
        Seq(OpenBracket, At(Name(name), type), CloseBracket);
    private static Formula Let(Formula lhs, Formula rhs) =>
        Seq(Name("let"), Sp, lhs, Colon, Eq, rhs, Comma);
    private static Formula InUnitCube(Formula q) =>
        Seq(Open, Forall, Sp, Typed(F.Id("i"), F.Id("I")), Comma,
            D(0), Lt, At(q, F.Id("i")), Lt, D(1), Close);
    private static Formula Nonzero(Formula a, Formula type) =>
        Seq(Forall, Sp, Typed(a, type), Comma, a, Sp, Neq, Sp, D(0), Sp, Implies, Sp);
}
