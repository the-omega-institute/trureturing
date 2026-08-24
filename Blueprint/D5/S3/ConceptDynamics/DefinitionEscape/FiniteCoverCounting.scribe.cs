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
        Formula candidateCost = F.Id("c");
        Formula countingWeight = F.Id("countingWeight");
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
            "capturedEscapeMass", set, family, q, target, nu);
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

        Formula finiteSupplement = Call("finiteSelectionSupplement", gamma, family);
        Formula selectionCost = Call("finiteSelectionCost", gamma, candidateCost);
        Formula rateOne = Call(
            "budgetedEscapeRate",
            q,
            finiteSupplement,
            target,
            selectionCost,
            countingWeight,
            budgetOne);
        Formula rateTwo = Call(
            "budgetedEscapeRate",
            q,
            finiteSupplement,
            target,
            selectionCost,
            countingWeight,
            budgetTwo);
        Formula positiveBaselineCount = new Formula.Relation(
            D(0),
            FormulaRelationOperator.LessThan,
            Call("mass", countingWeight, residual));
        Formula candidateCostsNonnegative = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(
                FormulaIdentifier.Create("d"),
                F.Id("I"))],
            new Formula.Logic(
                Seq(definition, Sp, InMacro, Sp, gamma),
                FormulaLogicOperator.Implies,
                new Formula.Relation(
                    D(0),
                    FormulaRelationOperator.LessThanOrEqual,
                    Call("c", definition))));
        Formula budgetOneNonnegative = new Formula.Relation(
            D(0),
            FormulaRelationOperator.LessThanOrEqual,
            budgetOne);
        Formula groupedCandidateCostsNonnegative = Seq(
            Open, candidateCostsNonnegative, Close);
        Formula budgetOrdered = new Formula.Relation(
            budgetOne,
            FormulaRelationOperator.LessThanOrEqual,
            budgetTwo);
        Formula countingAntitone = new Formula.Relation(
            rateTwo,
            FormulaRelationOperator.LessThanOrEqual,
            rateOne);
        Formula countingPremises = new Formula.Logic(
            groupedCandidateCostsNonnegative,
            FormulaLogicOperator.And,
            new Formula.Logic(
                budgetOneNonnegative,
                FormulaLogicOperator.And,
                new Formula.Logic(
                    budgetOrdered,
                    FormulaLogicOperator.And,
                    positiveBaselineCount)));
        Formula countingStatement = Disp(Seq(
            new Formula.Logic(
                countingPremises,
                FormulaLogicOperator.Implies,
                countingAntitone), Dot));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Two residual-cover clauses are proved; two CAS laws remain open.",
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
                        "This Prop uses the two CAS definitions directly: residualEscapeMass(S) is "
                            + "M(S) = nu.mass(E(q join S; T)), and capturedEscapeMass(S) is "
                            + "F(S) = M(empty) - M(S). Gamma is contained in Delta and d is fresh "
                            + "for Delta. It is not a theorem: identifying this difference with a "
                            + "weighted union of cuts needs an additivity law, and proving diminishing "
                            + "returns needs an appropriate submodularity law absent from EscapeWeight."))),
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
                        "This Prop uses CAS strategies Finset Gamma, finiteSelectionSupplement, and "
                            + "finiteSelectionCost(S) = sum d in S, c(d). Candidate costs and b1 are "
                            + "nonnegative, so the empty selection has cost zero and is feasible; "
                            + "b1 <= b2 gives the displayed antitone direction. Every "
                            + "budgetedEscapeRate occurrence names q, the supplement, T, the summed "
                            + "cost, countingWeight, and its budget. This declaration is not a theorem "
                            + "and no counterexample to the CAS strategy model is claimed."))),
                    DescribeRole.Definition))));
    }
}
