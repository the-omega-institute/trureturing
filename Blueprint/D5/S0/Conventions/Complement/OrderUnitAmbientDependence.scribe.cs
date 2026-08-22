using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Conventions.Complement;

internal sealed class OrderUnitAmbientDependenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An effect complement is relative to an explicit ambient order unit.",
        H("Order-Unit Ambient Dependence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("order-unit-complement-depends-on-ambient"),
                DeclarationHandle.Create(
                    "D5/S0/Conventions/Complement/OrderUnitAmbientDependence."
                        + "order_unit_complement_depends_on_ambient"),
                H("Order-unit complement depends on its ambient total"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V be a real ordered vector space. The public hypotheses state the "
                            + "order-unit role of u and v as two-sided domination by a positive "
                            + "real multiple, and require the effect e to lie in both closed "
                            + "intervals from zero to the corresponding ambient total.")),
                    Paragraph(Text(
                        "For c_u(e) = u - e, the two complement values differ exactly when u and "
                            + "v differ. Thus the operation does not supply an ambient-free notion "
                            + "of complement; the total is an explicit part of its typed data.")),
                    Paragraph(Text(
                        "The repository family definition ComplementEncoding.complement is "
                            + "imported directly. Pinned Mathlib provides IsOrderedModule, "
                            + "IsOrderedAddMonoid, Set.Icc, and sub_left_inj. Exact-name and "
                            + "case-insensitive searches found no OrderUnit or IsOrderUnit "
                            + "predicate, so the order-unit property remains an explicit public "
                            + "hypothesis rather than a silently weakened carrier."))),
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
        Formula v = F.Id("v");
        Formula e = F.Id("e");
        Formula orderedVectorSpace = Seq(
            Operatorname, Grp(F.Id("OrderedVectorSpace")), Underscore,
            Grp(Mathbb, Grp(F.Id("R"))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            vectorSpace, Colon, Sp, orderedVectorSpace, Comma, Sp,
            u, Comma, Sp, v, Comma, Sp, e, InMacro, Sp, vectorSpace, Comma,
                RowBreak, Grp(),
            OrderUnit(u), Sp, Land, Sp, OrderUnit(v), Comma, RowBreak, Grp(),
            e, InMacro, Sp, OpenBracket, D(0), Comma, Sp, u, CloseBracket,
                Sp, Land, Sp,
            e, InMacro, Sp, OpenBracket, D(0), Comma, Sp, v, CloseBracket,
                Sp, Rightarrow, RowBreak, Grp(),
            Open, Complement(u, e), Sp, Neq, Sp, Complement(v, e), Sp, Iff, Sp,
                u, Sp, Neq, Sp, v, Close, Comma, RowBreak, Grp(),
            Complement(u, e), Sp, Colon, Eq, Sp, u, Sp, Minus, Sp, e, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
