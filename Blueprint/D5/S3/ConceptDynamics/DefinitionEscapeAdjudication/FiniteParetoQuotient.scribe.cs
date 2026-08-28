using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeAdjudication;

internal sealed class FiniteParetoQuotientDocument : IScribeDocumentDefinition
{
    private enum OrderClass
    {
        LessOrEqual,
        Preorder,
    }

    private const string Prefix =
        "D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/FiniteParetoQuotient.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The symmetric weak-Pareto kernel on a finite carrier has explicit finite classes, a complete class enumeration, and the required empty and singleton laws.",
        H("Explicit Finite Pareto Quotient"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pareto-class"),
                DeclarationHandle.Create(Prefix + "paretoClass"),
                H("Explicit symmetric-kernel class"),
                StatementSource.FromAuthor(ParetoClassFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The class is computed by filtering the attached finite carrier with the "
                        + "decidable symmetric weak-Pareto kernel."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pareto-class-image"),
                DeclarationHandle.Create(Prefix + "paretoClassImage"),
                H("Finite image of all Pareto classes"),
                StatementSource.FromAuthor(ParetoClassImageFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Taking the finite image removes duplicate classes while retaining an "
                        + "explicit representative-produced enumeration."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-pareto-quotient"),
                DeclarationHandle.Create(Prefix + "FiniteParetoQuotient"),
                H("Finite Pareto quotient carrier"),
                StatementSource.FromAuthor(FiniteQuotientFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The quotient carrier is the subtype of finite classes in the class image; "
                        + "it does not invoke Lean's abstract Quotient type."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quotient-enum"),
                DeclarationHandle.Create(Prefix + "quotientEnum"),
                H("Complete explicit quotient enumeration"),
                StatementSource.FromAuthor(QuotientEnumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Attaching image-membership proofs turns the class image into an enumeration "
                        + "whose elements already have the quotient subtype."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-pareto-quotient-fintype"),
                DeclarationHandle.Create(Prefix + "finiteParetoQuotientFintype"),
                H("Fintype from the explicit class image"),
                StatementSource.FromAuthor(FintypeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The class image supplies a finite type structure directly, including when "
                        + "the quotient is empty; no Nonempty premise is introduced."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-pareto-quotient-exact-complete"),
                DeclarationHandle.Create(Prefix + "finite_pareto_quotient_exact_and_complete"),
                H("Classes are exact and their enumeration is complete"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every carrier element is enumerated; class membership is exactly "
                            + "ParetoEqOn; classes are reflexive, equal exactly for equivalent "
                            + "representatives, nonempty, stable under reclassification, and all "
                            + "occur in quotientEnum.")),
                    Paragraph(Text(
                        "The same declaration verifies both boundary cases: an empty carrier has "
                            + "no quotient element, while a one-element carrier has exactly one "
                            + "quotient class."))),
                DescribeRole.Theorem))));

    private static Formula Carrier(Formula finiteCarrier) =>
        Call("ParetoCarrier", finiteCarrier);

    private static Formula GainVector() => Call(
        "GainVector", F.Id("Information"), F.Id("Residual"), F.Id("Transfer"),
        F.Id("Cost"), F.Id("Risk"));

    private static Formula Kernel(
        Formula value, Formula finiteCarrier, Formula left, Formula right) =>
        Call("ParetoEqOn", value, finiteCarrier, left, right);

    private static Formula ClassOf(
        Formula value, Formula finiteCarrier, Formula representative) =>
        Call("paretoClass", value, finiteCarrier, representative);

    private static Formula ClassImage(Formula value, Formula finiteCarrier) =>
        Call("paretoClassImage", value, finiteCarrier);

    private static Formula Quotient(Formula value, Formula finiteCarrier) =>
        Call("FiniteParetoQuotient", value, finiteCarrier);

    private static Formula DecidableOrder(Formula type) =>
        Seq(
            OpenBracket,
            Forall, Sp, F.Id("a"), Comma, Sp, F.Id("b"), Colon, Sp, type, Comma, Sp,
            Call("Decidable", Seq(F.Id("a"), Sp, Leq, Sp, F.Id("b"))),
            CloseBracket);

    private static Formula OrderConstraint(OrderClass orderClass, Formula type) =>
        orderClass switch
        {
            OrderClass.LessOrEqual => Call("LE", type),
            OrderClass.Preorder => Call("Preorder", type),
            _ => throw new ArgumentOutOfRangeException(nameof(orderClass)),
        };

    private static Formula Header(OrderClass orderClass)
    {
        Formula action = F.Id("Action");
        Formula information = F.Id("Information");
        Formula residual = F.Id("Residual");
        Formula transfer = F.Id("Transfer");
        Formula cost = F.Id("Cost");
        Formula risk = F.Id("Risk");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));

        return Seq(
            Forall, Sp, action, Comma, Sp, information, Comma, Sp, residual, Comma, Sp,
            transfer, Comma, Sp, cost, Comma, Sp, risk, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            OpenBracket, Call("DecidableEq", action), CloseBracket, Comma, Sp,
            OpenBracket, OrderConstraint(orderClass, information), CloseBracket, Comma, Sp,
            OpenBracket, OrderConstraint(orderClass, residual), CloseBracket, Comma, Sp,
            OpenBracket, OrderConstraint(orderClass, transfer), CloseBracket, Comma, Sp,
            OpenBracket, OrderConstraint(orderClass, cost), CloseBracket, Comma, Sp,
            OpenBracket, OrderConstraint(orderClass, risk), CloseBracket, Comma,
            RowBreak, Grp(),
            DecidableOrder(information), Comma, Sp, DecidableOrder(residual), Comma, Sp,
            DecidableOrder(transfer), Comma, RowBreak, Grp(),
            DecidableOrder(cost), Comma, Sp, DecidableOrder(risk), Comma,
            RowBreak, Grp(),
            F.Id("value"), Colon, Sp, action, Sp, To, Sp, GainVector(), Comma, Sp,
            F.Id("F"), Colon, Sp, Call("Finset", action), Comma,
            RowBreak, Grp());
    }

    private static Formula ParetoClassFormula()
    {
        Formula value = F.Id("value");
        Formula finiteCarrier = F.Id("F");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula filterPredicate = Seq(
            LambdaLower, Sp, y, Comma, Sp, Kernel(value, finiteCarrier, y, x));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")), Header(OrderClass.LessOrEqual),
            x, Colon, Sp, Carrier(finiteCarrier), Comma, RowBreak, Grp(),
            ClassOf(value, finiteCarrier, x), Sp, Eq, Sp,
            Call("filter", Call("carrierEnum", finiteCarrier), filterPredicate), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ParetoClassImageFormula()
    {
        Formula value = F.Id("value");
        Formula finiteCarrier = F.Id("F");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")), Header(OrderClass.LessOrEqual),
            ClassImage(value, finiteCarrier), Sp, Eq, Sp,
            Call("image", Call("carrierEnum", finiteCarrier),
                Call("paretoClass", value, finiteCarrier)), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula FiniteQuotientFormula()
    {
        Formula value = F.Id("value");
        Formula finiteCarrier = F.Id("F");
        Formula candidate = F.Id("C");
        Formula classType = Call("Finset", Carrier(finiteCarrier));
        Formula classSubtype = Seq(
            OpenBrace, candidate, Colon, Sp, classType, Sp, Mid, Sp,
            candidate, Sp, InMacro, Sp, ClassImage(value, finiteCarrier), CloseBrace);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")), Header(OrderClass.LessOrEqual),
            Quotient(value, finiteCarrier), Sp, Eq, Sp, classSubtype, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula QuotientEnumFormula()
    {
        Formula value = F.Id("value");
        Formula finiteCarrier = F.Id("F");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")), Header(OrderClass.LessOrEqual),
            Call("quotientEnum", value, finiteCarrier), Sp, Eq, Sp,
            Call("attach", ClassImage(value, finiteCarrier)), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula FintypeFormula()
    {
        Formula value = F.Id("value");
        Formula finiteCarrier = F.Id("F");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")), Header(OrderClass.LessOrEqual),
            Call("finiteParetoQuotientFintype", value, finiteCarrier), Colon, Sp,
            Call("Fintype", Quotient(value, finiteCarrier)), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula TheoremFormula()
    {
        Formula value = F.Id("value");
        Formula finiteCarrier = F.Id("F");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula z = F.Id("z");
        Formula c = F.Id("C");
        Formula d = F.Id("D");
        Formula carrier = Carrier(finiteCarrier);
        Formula quotient = Quotient(value, finiteCarrier);
        Formula cValue = Call("val", c);
        Formula carrierComplete = Seq(
            Forall, Sp, x, Colon, Sp, carrier, Comma, Sp,
            x, Sp, InMacro, Sp, Call("carrierEnum", finiteCarrier));
        Formula membershipExact = Seq(
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, carrier, Comma, Sp,
            y, Sp, InMacro, Sp, ClassOf(value, finiteCarrier, x), Sp, Iff, Sp,
            Kernel(value, finiteCarrier, y, x));
        Formula selfMember = Seq(
            Forall, Sp, x, Colon, Sp, carrier, Comma, Sp,
            x, Sp, InMacro, Sp, ClassOf(value, finiteCarrier, x));
        Formula classExact = Seq(
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, carrier, Comma, Sp,
            ClassOf(value, finiteCarrier, x), Sp, Eq, Sp,
            ClassOf(value, finiteCarrier, y), Sp, Iff, Sp,
            Kernel(value, finiteCarrier, x, y));
        Formula classNonempty = Seq(
            Forall, Sp, c, Colon, Sp, quotient, Comma, Sp,
            Call("Nonempty", cValue));
        Formula classStable = Seq(
            Forall, Sp, c, Colon, Sp, quotient, Comma, Sp,
            Forall, Sp, z, Colon, Sp, carrier, Comma, Sp,
            z, Sp, InMacro, Sp, cValue, Sp, Rightarrow, Sp,
            ClassOf(value, finiteCarrier, z), Sp, Eq, Sp, cValue);
        Formula enumComplete = Seq(
            Forall, Sp, c, Colon, Sp, quotient, Comma, Sp,
            c, Sp, InMacro, Sp, Call("quotientEnum", value, finiteCarrier));
        Formula emptyLaw = Seq(
            finiteCarrier, Sp, Eq, Sp, Emptyset, Sp, Rightarrow, Sp,
            Forall, Sp, c, Colon, Sp, quotient, Comma, Sp, F.Id("False"));
        Formula singletonLaw = Seq(
            Call("card", finiteCarrier), Sp, Eq, Sp, D(1), Sp, Rightarrow, Sp,
            Exists, Sp, c, Colon, Sp, quotient, Comma, Sp,
            Forall, Sp, d, Colon, Sp, quotient, Comma, Sp, d, Sp, Eq, Sp, c);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")), Header(OrderClass.Preorder),
            Open, carrierComplete, Close, Sp, Land, RowBreak, Grp(),
            Open, membershipExact, Close, Sp, Land, RowBreak, Grp(),
            Open, selfMember, Close, Sp, Land, RowBreak, Grp(),
            Open, classExact, Close, Sp, Land, RowBreak, Grp(),
            Open, classNonempty, Close, Sp, Land, RowBreak, Grp(),
            Open, classStable, Close, Sp, Land, RowBreak, Grp(),
            Open, enumComplete, Close, Sp, Land, RowBreak, Grp(),
            Open, emptyLaw, Close, Sp, Land, RowBreak, Grp(),
            Open, singletonLaw, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
