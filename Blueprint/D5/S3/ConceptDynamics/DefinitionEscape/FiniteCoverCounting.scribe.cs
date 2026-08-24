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
        Formula indexType = F.Id("I");
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
        Formula coverEquivalence = Seq(Open,
            Open, gammaBlind, Sp, Eq, Sp, Emptyset, Close, Sp, Leftrightarrow, Sp,
            cutsCover, Close);

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
        Formula countedSet = F.Id("A");
        Formula countingWeightDefinition = Seq(
            Forall, Sp, countedSet, Comma, Sp,
            Call("mass", countingWeight, countedSet), Sp, Eq, Sp,
            Call("ncard", countedSet));
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
        Formula countingLaw = new Formula.Logic(
            countingPremises,
            FormulaLogicOperator.Implies,
            countingAntitone);
        Formula countingContext = Seq(
            Typeclass("Finite", state), Comma, RowBreak,
            countingWeightDefinition, Comma, RowBreak);
        Formula countingStatement = Disp(Seq(countingContext, countingLaw, Dot));
        Formula packagedCountingClause = Seq(
            Forall, Sp, F.Id("finiteX"), Sp, Colon, Sp, Call("Finite", state), Comma,
            RowBreak, countingWeightDefinition, Comma, RowBreak, countingLaw);
        Formula packagedStatement = Disp(Seq(
            new Formula.Logic(
                coverEquivalence,
                FormulaLogicOperator.And,
                new Formula.Logic(
                    finiteClause,
                    FormulaLogicOperator.And,
                    packagedCountingClause)), Dot));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The two residual-cover clauses and counting antitonicity are proved; "
                + "marginal capture needs a stronger weight interface.",
            H("Finite Cover and Counting"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("finite-cover-counting"),
                    DeclarationHandle.Create(
                        "D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting."
                            + "finite_cover_counting"),
                    H("Finite cover and counting package"),
                    StatementSource.FromAuthor(packagedStatement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Candidate definitions are indexed by I with dependent codomains "
                                + "V(i). The packaged theorem has no global instances. Its first "
                                + "conjunct is general in X and I. The second retains the explicit "
                                + "Finite X premise used by finite_subset_iUnion to extract a finite "
                                + "subfamily.")),
                        Paragraph(Text(
                            "finiteSelectionSufficientOnRange is the canonical Refines target "
                                + "relation against Set.rangeFactorization of the selected joint "
                                + "readout. The proof reuses inductive_sufficiency_criterion. The "
                                + "third conjunct quantifies Finite X locally and is backed by "
                                + "counting_escape_antitone_law. finiteSelectionSupplement chooses "
                                + "classical equality only inside its Finset implementation, so no "
                                + "public declaration requires DecidableEq I."))),
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
                            + "for Delta. The theorem "
                            + "marginal_capture_law_not_implied_by_escape_weight gives a counterexample "
                            + "inside this weak Lean interface. Identifying the difference with a "
                            + "weighted union of cuts needs additivity, and the source's diminishing-"
                            + "returns argument needs the stronger measure semantics not carried by "
                            + "EscapeWeight."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("counting-escape-antitone-law"),
                    DeclarationHandle.Create(
                        "D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting."
                            + "counting_escape_antitone_law"),
                    H("CAS counting escape-rate theorem"),
                    StatementSource.FromAuthor(countingStatement),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This Prop uses CAS strategies Finset Gamma, finiteSelectionSupplement, and "
                            + "finiteSelectionCost(S) = sum d in S, c(d). Candidate costs and b1 are "
                            + "nonnegative, so the empty selection has cost zero and is feasible; "
                            + "b1 <= b2 gives the displayed antitone direction. Every "
                            + "budgetedEscapeRate occurrence names q, the supplement, T, the summed "
                            + "cost, countingWeight, and its budget. Here countingWeight is the concrete "
                            + "Lean weight mass(A) = ncard(A), under Finite X; finite-set membership "
                            + "equality is chosen internally. The empty selection proves feasibility at "
                            + "b1, and the generic budget theorem then gives the non-strict direction "
                            + "rate(b2) <= rate(b1). A constant "
                            + "candidate is an elaborating false neighbor for strict decrease, while "
                            + "an identity candidate gives a strict nontrivial model with rate(1) < "
                            + "rate(0)."))),
                    DescribeRole.Theorem))));
    }

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, argument, Close, CloseBracket);
}
