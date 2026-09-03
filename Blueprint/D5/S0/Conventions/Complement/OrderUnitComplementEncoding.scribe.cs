using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Conventions.Complement;

internal sealed class OrderUnitComplementEncodingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Effect-interval subtraction complement encodes its order-unit total.",
        H("Order-Unit Complement Encoding"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("order-unit-complement-encoding"),
                DeclarationHandle.Create(
                    "D5/S0/Conventions/Complement/OrderUnitComplementEncoding."
                        + "order_unit_complement_encoding"),
                H("Order-unit complement encoding"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V be a real ordered vector space, let u satisfy the explicit "
                            + "order-unit domination condition, and let e lie in the effect "
                            + "interval from zero to u. Define c_u(x) = u - x.")),
                    Paragraph(Text(
                        "The complement sends zero to u and u to zero, is involutive at e, "
                            + "and recovers u by evaluation at zero. These are exactly the four "
                            + "conclusion leaves of the Lean declaration.")),
                    Paragraph(Text(
                        "The declaration imports the repository's canonical complement and "
                            + "projects the endpoint and involution laws from the frozen "
                            + "complement-encoding theorem. The ordered carrier conditions "
                            + "restrict the theorem to the source effect interval."))),
                DescribeRole.Theorem))));

    private static Formula Complement(Formula total, Formula argument) =>
        Seq(F.Id("c"), Underscore, total, Open, argument, Close);

    private static Formula OrderUnit(Formula total)
    {
        Formula x = F.Id("x");
        Formula r = F.Id("r");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));

        return Grp(Seq(
            D(0), Sp, Leq, Sp, total, Sp, Land, Sp,
            Forall, Sp, x, InMacro, Sp, F.Id("V"), Comma, Sp,
            Exists, Sp, r, InMacro, Sp, reals, Comma, Sp,
            D(0), Sp, Lt, Sp, r, Sp, Land, Sp,
            Minus, r, total, Sp, Leq, Sp, x, Sp, Land, Sp,
            x, Sp, Leq, Sp, r, total));
    }

    private static Formula TheoremFormula()
    {
        Formula vectorSpace = F.Id("V");
        Formula u = F.Id("u");
        Formula e = F.Id("e");
        Formula orderedVectorSpace = Seq(
            Operatorname, Grp(F.Id("OrderedVectorSpace")), Underscore,
            Grp(Mathbb, Grp(F.Id("R"))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            vectorSpace, Colon, Sp, orderedVectorSpace, Comma, Sp,
            u, Comma, Sp, e, InMacro, Sp, vectorSpace, Comma, RowBreak, Grp(),
            OrderUnit(u), Sp, Land, Sp,
            e, InMacro, Sp, OpenBracket, D(0), Comma, Sp, u, CloseBracket,
                Sp, Rightarrow, RowBreak, Grp(),
            Complement(u, D(0)), Sp, Eq, Sp, u, Sp, Land, RowBreak, Grp(),
            Complement(u, u), Sp, Eq, Sp, D(0), Sp, Land, RowBreak, Grp(),
            Complement(u, Complement(u, e)), Sp, Eq, Sp, e,
                Sp, Land, RowBreak, Grp(),
            u, Sp, Eq, Sp, Complement(u, D(0)), Comma, RowBreak, Grp(),
            Complement(u, F.Id("x")), Sp, Colon, Eq, Sp,
                u, Sp, Minus, Sp, F.Id("x"), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
