using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscape;

internal sealed class FiniteCoverCountingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula gamma = Gamma;
        Formula delta = Delta;
        Formula state = F.Id("X");
        Formula q = F.Id("q");
        Formula target = F.Id("T");
        Formula definition = F.Id("d");
        Formula nu = F.Id("nu");
        Formula family = Seq(F.Id("d"), Underscore, Grp(F.Id("i")));
        Formula budgetOne = Seq(F.Id("b"), Underscore, Grp(D(1)));
        Formula budgetTwo = Seq(F.Id("b"), Underscore, Grp(D(2)));
        Formula residual = Call("defectRelation", q, target);
        Formula gammaBlind = Call(
            "intersection",
            residual,
            Call("jointKernel", gamma, family));
        Formula cut = Call(
            "intersection",
            residual,
            Call("complement", Call("conceptKernel", definition)));
        Formula cutsCover = Seq(
            Call("union", Seq(definition, Sp, InMacro, Sp, gamma), cut),
            Sp, Eq, Sp, residual);
        Formula finiteSufficient = Call(
            "finiteSelectionSufficientOnRange", gamma, family, q, target);
        Formula finitePremises = new Formula.Logic(
            Call("Finite", state),
            FormulaLogicOperator.And,
            Seq(gammaBlind, Sp, Eq, Sp, Emptyset));
        Formula finiteClause = new Formula.Logic(
            finitePremises,
            FormulaLogicOperator.Implies,
            finiteSufficient);
        Formula coverStatement = Disp(Seq(
            Open, gammaBlind, Sp, Eq, Sp, Emptyset, Close, Sp, Leftrightarrow, Sp,
            cutsCover, Comma, RowBreak, Grp(), finiteClause, Dot));

        Formula singletonDefinition = Seq(OpenBrace, definition, CloseBrace);
        Formula gammaWithDefinition = Call("union", gamma, singletonDefinition);
        Formula deltaWithDefinition = Call("union", delta, singletonDefinition);
        Formula Capture(Formula set) => Call(
            "mass", nu, Call("capturedPairs", set, family, q, target));
        Formula marginalPremises = new Formula.Logic(
            Seq(gamma, Sp, Subseteq, Sp, delta),
            FormulaLogicOperator.And,
            Seq(Neg, Open, definition, Sp, InMacro, Sp, delta, Close));
        Formula marginalConclusion = new Formula.Relation(
            Seq(Capture(gammaWithDefinition), Sp, Minus, Sp, Capture(gamma)),
            FormulaRelationOperator.GreaterThanOrEqual,
            Seq(Capture(deltaWithDefinition), Sp, Minus, Sp, Capture(delta)));
        Formula marginalStatement = Disp(Seq(
            new Formula.Logic(
                marginalPremises,
                FormulaLogicOperator.Implies,
                marginalConclusion), Dot));

        Formula rateOne = Seq(
            Call("budgetedEscapeRate", budgetOne), Underscore, Grp(F.Id("count")));
        Formula rateTwo = Seq(
            Call("budgetedEscapeRate", budgetTwo), Underscore, Grp(F.Id("count")));
        Formula positiveBaselineCount = new Formula.Relation(
            D(0),
            FormulaRelationOperator.LessThan,
            Call("ncard", residual));
        Formula budgetOrdered = new Formula.Relation(
            budgetOne,
            FormulaRelationOperator.LessThanOrEqual,
            budgetTwo);
        Formula countingAntitone = new Formula.Relation(
            rateTwo,
            FormulaRelationOperator.LessThanOrEqual,
            rateOne);
        Formula countingPremises = new Formula.Logic(
            positiveBaselineCount,
            FormulaLogicOperator.And,
            budgetOrdered);
        Formula countingStatement = Disp(Seq(
            new Formula.Logic(
                countingPremises,
                FormulaLogicOperator.Implies,
                countingAntitone), Dot));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Definition cuts cover residuals; two further CAS laws expose missing premises.",
            H("Finite Cover and Counting"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("finite-cover-counting"),
                    DeclarationHandle.Create(
                        "D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting."
                            + "finite_cover_counting"),
                    H("Cut coverage and finite extraction"),
                    StatementSource.FromAuthor(coverStatement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Candidate definitions are indexed by I with dependent codomains "
                                + "V(i). The first conjunct is general in X. Only the second "
                                + "conjunct lists Finite X, exactly where finite_subset_iUnion is "
                                + "used to extract a finite subfamily.")),
                        Paragraph(Text(
                            "finiteSelectionSufficientOnRange is the canonical Refines target "
                                + "relation against Set.rangeFactorization of the selected joint "
                                + "readout. The proof reuses inductive_sufficiency_criterion."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("marginal-capture-law"),
                    DeclarationHandle.Create(
                        "D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting."
                            + "marginalCaptureLaw"),
                    H("CAS marginal-capture statement"),
                    StatementSource.FromAuthor(marginalStatement),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This Prop records the exact DECT section 4.4 difference formula: F(S) is "
                            + "nu.mass of capturedPairs(S), Gamma is contained in Delta, and d is "
                            + "fresh for Delta. It is not claimed as a theorem. EscapeWeight has "
                            + "only zero-empty and nonnegative laws; a checked counterexample shows "
                            + "that these do not imply the displayed diminishing return."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("counting-escape-antitone-law"),
                    DeclarationHandle.Create(
                        "D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting."
                            + "countingEscapeAntitoneLaw"),
                    H("CAS counting escape-rate statement"),
                    StatementSource.FromAuthor(countingStatement),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This Prop keeps only the source premises: positive baseline counting mass "
                            + "and b1 <= b2. It is not claimed as a theorem. With no strategy "
                            + "feasible at b1, the current Real.sInf encoding gives rate(b1)=0, "
                            + "and a checked example falsifies the displayed direction."))),
                    DescribeRole.Definition))));
    }
}
