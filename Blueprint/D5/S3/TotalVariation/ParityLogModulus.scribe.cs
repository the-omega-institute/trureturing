using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class ParityLogModulusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Averaging the nontrivial sign moments gives a logarithmic stability bound at finite distance.",
        H("Finite-distance stability of logarithmic parity recovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("log-parity-coefficient-modulus"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/ParityLogModulus.log_parity_coefficient_modulus"),
                H("Logarithmic modulus of the parity coefficient"),
                StatementSource.FromAuthor(StabilityStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The signed sum of moment differences is an expectation difference. " +
                    "Equal mass and character orthogonality bound its absolute value by the " +
                    "order of the group times total variation. The trivial character contributes " +
                    "zero. Logarithm concavity on the other characters gives the finite-distance " +
                    "estimate. In Quantum Geometry section 35.6.8, apply it on the quotient by " +
                    "the fair-input image to the log bias product of a nonzero projected column."))),
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
        Formula order = new Formula.Absolute(space);
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula chars = Call("AddChar", space, Seq(Mathbb, Grp(F.Id("C"))));
        Formula masses = Seq(space, Sp, To, Sp, real);
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(space, Name("Type")), Comma,
                Instance("AddCommGroup", space), Instance("Fintype", space), Comma),
            Seq(Open, Forall, Sp, Typed(x, space), Comma, x, Plus, x, Eq, D(0), Close, Sp, Land, Sp, D(1), Lt, order,
                Sp, Longrightarrow),
            Let(At(sign, Typed(Psi, chars), Typed(x, space)), Seq(Re, Sp, At(Psi, x))),
            Let(At(moment, Typed(f, masses), Typed(Psi, chars)),
                Seq(SumOver(x, space), At(f, x), At(sign, Psi, x))),
            Let(At(coefficient, Typed(a, space), Typed(f, masses)),
                Seq(new Formula.Fraction(Seq(Minus, D(2)), new Formula.Absolute(space)),
                    SumOver(Psi, chars), At(sign, Psi, a), Sp, Log, Sp,
                    new Formula.Absolute(At(moment, f, Psi)))),
            Let(Beta, new Formula.Fraction(Seq(order, Minus, D(1)), order)),
            Seq(Forall, Sp, Typed(p, masses), Typed(q, masses), Typed(a, space), Typed(e, real),
                Comma, D(0), Lt, e, Sp, Land, Sp,
                SumOver(x, space), At(p, x), Eq, SumOver(x, space), At(q, x), Sp, Land),
            Seq(Open, Forall, Sp, Typed(Psi, chars), Comma,
                e, Le, new Formula.Absolute(At(moment, p, Psi)), Sp, Land, Sp,
                e, Le, new Formula.Absolute(At(moment, q, Psi)), Close, Sp, Longrightarrow),
            Seq(new Formula.Absolute(Seq(At(coefficient, a, p), Minus, At(coefficient, a, q))),
                Le, D(2), Beta, Sp, Log, Sp,
                Seq(Open, D(1), Plus, new Formula.Fraction(Call("TV", p, q), Seq(Beta, Sp, e)), Close))
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
