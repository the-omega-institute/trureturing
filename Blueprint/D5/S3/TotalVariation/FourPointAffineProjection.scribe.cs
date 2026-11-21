using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class FourPointAffineProjectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact total variation projection onto affine independent-bit laws on four points.",
        H("Nearest affine independent-bit laws on four points"),
        Blocks(Describe.Lean(
            DescribeId.Create("affine-projection-exact"),
            DeclarationHandle.Create(
                "D5/S3/TotalVariation/FourPointAffineProjection.affine_projection_exact"),
            H("The exact distance is attained with three independent bits"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The output space A is the product of two copies of the binary field. " +
                    "The law L is the affine sum of independent bits. Its arguments are the " +
                    "offset s, the column map c, and the Bernoulli rates t. The four masses " +
                    "are read at 00, 10, 01, 11 in that order.")),
                Paragraph(Text(
                    "The rate bounds make each Bernoulli factor a nonnegative unit-mass law, " +
                    "and the finite index set supplies a finite product of these factors. " +
                    "Both probability assumptions on p are needed. Direct arithmetic gives " +
                    "d(p) = 0 for the zero mass function, which has distance one-half from " +
                    "every comparison law. For signed masses (1, -1, 0, 1) of total mass one, " +
                    "the formula gives one-half. The negative atom alone forces distance at " +
                    "least one to every probability law because the total masses agree.")),
                Paragraph(Text(
                    "To evaluate d(p), relabel the atoms by placing their masses in the order " +
                    "largest, smallest, second-smallest, second-largest. The first coordinate " +
                    "and the sum of the coordinates then have moments a and h with 0 <= a <= h. " +
                    "Their product character has signed moment b with |b| <= a.")),
                Paragraph(Math(In(Seq(Call("d", P), Eq, Frac,
                    Grp(Max, Sp, Open, D(0), Comma, Seq(F.Id("a"), F.Id("h")), Minus, F.Id("b"), Close),
                    Grp(D(2), Open, D(1), Plus, F.Id("h"), Close))))),
                Paragraph(Text(
                    "Each atom changes by at most the total variation. Together with the " +
                    "multiplicative and sign inequalities on the moments, this limits " +
                    "how far a competitor can reduce the violated moment constraint. " +
                    "If the constraint is violated, transferring mass between two atoms " +
                    "while preserving h attains the bound with a product law. Otherwise, " +
                    "three bias factors realize the original moments. An affine inverse " +
                    "relabeling preserves the class of laws and the total variation."))),
            DescribeRole.Theorem))));

    private static Formula P => F.Id("p");
    private static Formula I => F.Id("I");
    private static Formula J => F.Id("j");
    private static Formula A => F.Id("A");
    private static Formula S => F.Id("s");
    private static Formula C => F.Id("c");
    private static Formula T => F.Id("t");
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Distance => Call("TV", P, Call("L", S, C, T));

    private static Formula IndexType(byte size) => Call("Fin", D(size));

    private static Formula Rates(Formula domain) =>
        Seq(Forall, Sp, J, Colon, domain, Comma, Call("t", J), Sp,
            InMacro, Sp, OpenBracket, D(0), Comma, D(1), CloseBracket);

    private static Formula LawInputs(Formula domain) =>
        Seq(S, Colon, A, Comma, C, Colon, domain, To, Sp, A, Comma,
            T, Colon, domain, To, Sp, Real);

    private static Formula Statement() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, P, Colon, IndexType(4), To, Sp, Real, Comma,
            Open, Forall, Sp, J, Colon, IndexType(4), Comma, D(0), Le, Sp, Call("p", J), Close, Sp, Land, Sp,
            Sum, Underscore, Grp(J), Sp, Call("p", J), Eq, D(1), Sp, Longrightarrow, Sp),
        Seq(Open, Forall, Sp, I, Sp, OpenBracket, Operatorname, Grp(F.Id("Fintype")),
            Open, I, Close, CloseBracket, Comma, LawInputs(I), Comma,
            Open, Rates(I), Close, Sp, Longrightarrow, Sp, Call("d", P), Le, Sp, Distance, Close, Sp, Land, Sp),
        Seq(Open, Exists, Sp, LawInputs(IndexType(3)), Comma,
            Open, Rates(IndexType(3)), Close, Sp, Land, Sp, Distance, Eq, Call("d", P), Close)
    ]));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        foreach (var arg in args)
        {
            if (items.Count > 3)
                items.Add(Comma);
            items.Add(arg);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
