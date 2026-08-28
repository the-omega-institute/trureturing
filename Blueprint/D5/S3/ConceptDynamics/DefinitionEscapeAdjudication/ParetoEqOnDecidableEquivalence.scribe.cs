using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeAdjudication;

internal sealed class ParetoEqOnDecidableEquivalenceDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/"
            + "ParetoEqOnDecidableEquivalence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The symmetric kernel of weak Pareto dominance on a finite action carrier is a decidable equivalence relation.",
        H("Decidable Symmetric Pareto Kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pareto-eq-on-decision-function"),
                DeclarationHandle.Create(DeclarationPrefix + "paretoEqOnDecidable"),
                H("Five coordinate decisions decide the symmetric kernel"),
                StatementSource.FromAuthor(DecisionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The decision procedure unfolds both weak-dominance directions and "
                            + "combines the ten resulting coordinate comparisons. It requires "
                            + "no enumeration of the ambient action or coordinate types."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pareto-eq-on-decidable-equivalence"),
                DeclarationHandle.Create(DeclarationPrefix + "pareto_eq_on_equivalence_laws"),
                H("The symmetric Pareto kernel obeys the three equivalence laws"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The carrier is the subtype selected by the finite action set. "
                            + "ParetoEqOn is defined as weak dominance in both directions; "
                            + "it is not defined by vector equality or an external label.")),
                    Paragraph(Text(
                        "Reflexivity and transitivity reuse the frozen five-coordinate weak "
                            + "Pareto preorder theorem. Symmetry swaps the two kernel conjuncts; "
                            + "the preceding definition supplies the independent decision clause."))),
                DescribeRole.Theorem))));

    private static Formula Kernel(
        Formula value, Formula carrier, Formula left, Formula right) =>
        Call("ParetoEqOn", value, carrier, left, right);

    private static Formula DecidableOrder(Formula type, Formula left, Formula right) =>
        Seq(
            OpenBracket,
            Forall, Sp, left, Comma, Sp, right, Colon, Sp, type, Comma, Sp,
            Call("Decidable", Seq(left, Sp, Leq, Sp, right)),
            CloseBracket);

    private static Formula DecisionFormula()
    {
        Formula action = F.Id("Action");
        Formula information = F.Id("Information");
        Formula residual = F.Id("Residual");
        Formula transfer = F.Id("Transfer");
        Formula cost = F.Id("Cost");
        Formula risk = F.Id("Risk");
        Formula value = F.Id("value");
        Formula finiteCarrier = F.Id("F");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula carrier = Call("ParetoCarrier", finiteCarrier);
        Formula gainVector = Call(
            "GainVector", information, residual, transfer, cost, risk);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, action, Comma, Sp, information, Comma, Sp,
            residual, Comma, Sp, transfer, Comma, Sp, cost, Comma, Sp, risk,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            OpenBracket, Call("DecidableEq", action), CloseBracket, Comma, Sp,
            OpenBracket, Call("LE", information), CloseBracket, Comma, Sp,
            OpenBracket, Call("LE", residual), CloseBracket, Comma, Sp,
            OpenBracket, Call("LE", transfer), CloseBracket, Comma, Sp,
            OpenBracket, Call("LE", cost), CloseBracket, Comma, Sp,
            OpenBracket, Call("LE", risk), CloseBracket, Comma, RowBreak, Grp(),
            DecidableOrder(information, a, b), Comma, Sp,
            DecidableOrder(residual, a, b), Comma, Sp,
            DecidableOrder(transfer, a, b), Comma, RowBreak, Grp(),
            DecidableOrder(cost, a, b), Comma, Sp,
            DecidableOrder(risk, a, b), Comma, RowBreak, Grp(),
            value, Colon, Sp, action, Sp, To, Sp, gainVector, Comma, Sp,
            finiteCarrier, Colon, Sp, Call("Finset", action), Comma, RowBreak, Grp(),
            x, Comma, Sp, y, Colon, Sp, carrier, Comma, RowBreak, Grp(),
            Call("Decidable", Kernel(value, finiteCarrier, x, y)), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula TheoremFormula()
    {
        Formula action = F.Id("Action");
        Formula information = F.Id("Information");
        Formula residual = F.Id("Residual");
        Formula transfer = F.Id("Transfer");
        Formula cost = F.Id("Cost");
        Formula risk = F.Id("Risk");
        Formula value = F.Id("value");
        Formula finiteCarrier = F.Id("F");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula z = F.Id("z");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula carrier = Call("ParetoCarrier", finiteCarrier);
        Formula gainVector = Call(
            "GainVector", information, residual, transfer, cost, risk);
        Formula reflexive = Seq(
            Forall, Sp, x, Colon, Sp, carrier, Comma, Sp,
            Kernel(value, finiteCarrier, x, x));
        Formula symmetric = Seq(
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, carrier, Comma, Sp,
            Kernel(value, finiteCarrier, x, y), Sp, Rightarrow, Sp,
            Kernel(value, finiteCarrier, y, x));
        Formula transitive = Seq(
            Forall, Sp, x, Comma, Sp, y, Comma, Sp, z, Colon, Sp, carrier,
            Comma, Sp,
            Kernel(value, finiteCarrier, x, y), Sp, Rightarrow, Sp,
            Kernel(value, finiteCarrier, y, z), Sp, Rightarrow, Sp,
            Kernel(value, finiteCarrier, x, z));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, action, Comma, Sp, information, Comma, Sp,
            residual, Comma, Sp, transfer, Comma, Sp, cost, Comma, Sp, risk,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            OpenBracket, Call("DecidableEq", action), CloseBracket, Comma, Sp,
            OpenBracket, Call("Preorder", information), CloseBracket, Comma, Sp,
            OpenBracket, Call("Preorder", residual), CloseBracket, Comma, Sp,
            OpenBracket, Call("Preorder", transfer), CloseBracket, Comma, Sp,
            OpenBracket, Call("Preorder", cost), CloseBracket, Comma, Sp,
            OpenBracket, Call("Preorder", risk), CloseBracket, Comma, RowBreak, Grp(),
            value, Colon, Sp, action, Sp, To, Sp, gainVector, Comma, Sp,
            finiteCarrier, Colon, Sp, Call("Finset", action), Comma, RowBreak, Grp(),
            Open, reflexive, Close, Sp, Land, RowBreak, Grp(),
            Open, symmetric, Close, Sp, Land, RowBreak, Grp(),
            Open, transitive, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
