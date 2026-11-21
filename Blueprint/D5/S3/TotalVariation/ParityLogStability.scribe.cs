using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class ParityLogStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common positive floor for absolute sign moments gives a sharp total-variation bound.",
        H("Sharp stability of logarithmic parity recovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("log-parity-coefficient-stability"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/ParityLogStability.log_parity_coefficient_stability"),
                H("Stability of the log parity coefficient"),
                StatementSource.FromAuthor(StabilityStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The logarithmic divided differences turn the coefficient difference into " +
                        "an expectation difference for a single real test function. At two " +
                        "distinct points, the sum over characters of the absolute sign differences " +
                        "equals the group order by character orthogonality. This bounds the " +
                        "oscillation of the test function. Equal total masses allow centering it " +
                        "at the midpoint of its range, giving the factor two.")),
                    Paragraph(Text(
                        "In Quantum Geometry section 35.6.8, A is the quotient by the fair-input " +
                        "image and the two mass functions are the induced probability laws. For " +
                        "each nonzero projected column a, the grouped-bias recovery formula " +
                        "identifies L(a,p) with the natural logarithm of the product of the " +
                        "positive bias factors in that group. The two laws must have absolute " +
                        "sign moments at least the same positive e. Absolute moments also " +
                        "remove the sign contributed by an affine offset."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("log-bernoulli-bias-sharp"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/ParityLogStability.log_bernoulli_bias_sharp"),
                H("Sharpness on a one-bit law"),
                StatementSource.FromAuthor(SharpnessStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a one-bit input the absolute moments are one and the positive bias " +
                    "factor. For every floor strictly between zero and one, the construction " +
                    "chooses a second bias factor strictly above that floor with enough margin " +
                    "to violate the estimate for any constant below two. The total variation " +
                    "is half the difference of the two bias factors."))),
                DescribeRole.Theorem))));

    private static Formula StabilityStatement()
    {
        Formula a = F.Id("a");
        Formula space = F.Id("A");
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        Formula e = F.Id("e");
        Formula x = F.Id("x");
        Formula f = F.Id("f");
        Formula sign = F.Id("s");
        Formula moment = F.Id("m");
        Formula coefficient = F.Id("L");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula chars = Call("AddChar", space, Seq(Mathbb, Grp(F.Id("C"))));
        Formula masses = Seq(space, Sp, To, Sp, real);
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(space, Name("Type")), Comma,
                Instance("AddCommGroup", space), Instance("Fintype", space), Comma),
            Seq(Open, Forall, Sp, Typed(x, space), Comma, x, Plus, x, Eq, D(0), Close,
                Sp, Longrightarrow),
            Let(At(sign, Typed(Psi, chars), Typed(x, space)), Seq(Re, Sp, At(Psi, x))),
            Let(At(moment, Typed(f, masses), Typed(Psi, chars)),
                Seq(SumOver(x, space), At(f, x), At(sign, Psi, x))),
            Let(At(coefficient, Typed(a, space), Typed(f, masses)),
                Seq(new Formula.Fraction(Seq(Minus, D(2)), new Formula.Absolute(space)),
                    SumOver(Psi, chars), At(sign, Psi, a), Sp, Log, Sp,
                    new Formula.Absolute(At(moment, f, Psi)))),
            Seq(Forall, Sp, Typed(p, masses), Typed(q, masses), Typed(a, space), Typed(e, real),
                Comma, D(0), Lt, e, Sp, Land, Sp,
                SumOver(x, space), At(p, x), Eq, SumOver(x, space), At(q, x), Sp, Land),
            Seq(Open, Forall, Sp, Typed(Psi, chars), Comma,
                e, Le, new Formula.Absolute(At(moment, p, Psi)), Sp, Land, Sp,
                e, Le, new Formula.Absolute(At(moment, q, Psi)), Close, Sp, Longrightarrow),
            Seq(new Formula.Absolute(Seq(At(coefficient, a, p), Minus, At(coefficient, a, q))),
                Le, new Formula.Fraction(Seq(D(2), Call("TV", p, q)), e))
        ]));
    }

    private static Formula SharpnessStatement()
    {
        Formula e = F.Id("e");
        Formula c = F.Id("c");
        Formula q = F.Id("q");
        Formula t = F.Id("t");
        Formula law = F.Id("B");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        return Disp(new Formula.Aligned([
            Seq(Name("let"), Sp, Typed(t, real), Comma, Sp,
                At(law, t, Name("false")), Colon, Eq,
                new Formula.Fraction(Seq(D(1), Plus, t), D(2)), Comma, Sp,
                At(law, t, Name("true")), Colon, Eq,
                new Formula.Fraction(Seq(D(1), Minus, t), D(2)), Comma),
            Seq(Forall, Sp, Typed(e, real), Typed(c, real), Comma,
                D(0), Lt, e, Lt, D(1), Sp, Land, Sp, c, Lt, D(2), Sp, Longrightarrow),
            Seq(Exists, Sp, Typed(q, real), Comma, e, Lt, q, Lt, D(1), Sp, Land, Sp,
                new Formula.Fraction(Seq(c, Call("TV", At(law, q), At(law, e))), e),
                Lt, Log, Sp, q, Minus, Log, Sp, e)
        ]));
    }

    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);
    private static Formula At(Formula function, Formula first, Formula second) =>
        At(function, Seq(first, Comma, Sp, second));
    private static Formula Call(string name, Formula argument) => At(Name(name), argument);
    private static Formula Call(string name, Formula first, Formula second) =>
        At(Name(name), first, second);
    private static Formula Typed(Formula value, Formula type) =>
        Seq(Open, value, Colon, Sp, type, Close);
    private static Formula Instance(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket);
    private static Formula Let(Formula lhs, Formula rhs) =>
        Seq(Name("let"), Sp, lhs, Colon, Eq, rhs, Comma);
    private static Formula SumOver(Formula variable, Formula type) =>
        new Formula.Subscript(Sum, Seq(variable, Sp, InMacro, Sp, type));
}
