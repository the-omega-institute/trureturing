using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeLaws;

internal sealed class SubmodularCaptureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Clause-local finite selections and additive escape mass satisfy the proved DECT capture laws.",
        H("Submodular Definition-Escape Capture"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("submodular-definition-escape-capture"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DefinitionEscapeLaws/"
                        + "SubmodularCapture.submodular_capture"),
                H("Capture is monotone, submodular, and has diminishing marginal returns"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The displayed implication preserves all source ambient conditions. "
                            + "Finiteness is clause-local: C1 uses finite(S1), C2 finite(S2), C3 "
                            + "finite(S3), C4 finite(A4) and finite(B4), C5 finite(A5) and "
                            + "finite(B5), C6 finite(B6), and the score rewrite finite(S7). C8 "
                            + "has no finiteness premise, and I itself is not required to be "
                            + "finite. nonnegativeCost means zero is below every c(gamma), and "
                            + "disjointAdditive means exactly that mass(left union right) equals "
                            + "mass(left) plus mass(right) whenever left and right are disjoint. "
                            + "It does not assume strictly positive cost, positive baseline mass, "
                            + "countable additivity, measurability, inhabitedness, or decidable "
                            + "equality.")),
                    Paragraph(Text(
                        "The candidate family has the dependent Lean type definitions : "
                            + "forall i : I, Concept X (V i). Thus the formula does not replace "
                            + "the source family by a shared codomain. M is the imported "
                            + "residualEscapeMass and F is the imported capturedEscapeMass, "
                            + "whose definition is M(empty) minus M(S). The canonical "
                            + "defectRelation is the only target residual.")),
                    Paragraph(Text(
                        "C1 through C6 map in order to the first six Lean conjuncts: the exact M "
                            + "formula; the exact two-step F definition; the captured-union "
                            + "expansion; monotonicity; four-term submodularity; and diminishing "
                            + "returns under A subset B and d not in B. "
                            + "supportingLemma(greedyScoreRewrite) maps to Lean conjunct seven, "
                            + "which proves only equivalence of the residual-score and "
                            + "capture-score comparison predicates. C8 maps to Lean conjunct "
                            + "eight, persistence of a baseline-defect pair that every candidate "
                            + "readout identifies. The present and supportingLemma labels are "
                            + "weaker summaries, not extra predicates.")),
                    Paragraph(Text(
                        "The proof reuses capture_weight_submodular for the coverage step and "
                            + "uses finite additivity to identify M(empty) minus M(S) with the "
                            + "mass of the captured union. Nondegeneracy is supplied separately "
                            + "by a named positive model, so the theorem itself still admits the "
                            + "constant-zero weight required by the source's full domain.")),
                    Paragraph(Text(
                        "The clause-local finite premises and nonnegativeCost are retained as "
                            + "source-domain conditions, not advertised as proof guards: deleting "
                            + "them currently produces no named failure. disjointAdditive is a "
                            + "proof guard, with its absence consumed by the named weak-weight "
                            + "countermodel.")),
                    Paragraph(Text(
                        "GREEDY_ARGMAX_RULE_UNRESOLVED: C7 proves equality of the residual and "
                            + "capture score predicates. The source gives no candidate-domain, "
                            + "argmax-existence, tie, zero-cost, or freshness convention, so this "
                            + "module does not strengthen that algebraic identity into an "
                            + "existence claim."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula indexType = F.Id("I");
        Formula state = F.Id("X");
        Formula baselineType = F.Id("C");
        Formula targetType = F.Id("Target");
        Formula codomain = F.Id("V");
        Formula definitions = F.Id("definitions");
        Formula q = F.Id("q");
        Formula target = F.Id("T");
        Formula cost = F.Id("c");
        Formula nu = F.Id("nu");
        Formula premise = new Formula.Logic(
            Call("nonnegativeCost", cost),
            FormulaLogicOperator.And,
            Call("disjointAdditive", nu));
        Formula conclusions = Conjoin(
            Implies(Call("finite", F.Id("S1")), Present(F.Id("C1"))),
            Implies(Call("finite", F.Id("S2")), Present(F.Id("C2"))),
            Implies(Call("finite", F.Id("S3")), Present(F.Id("C3"))),
            Implies(
                new Formula.Logic(
                    Call("finite", F.Id("A4")),
                    FormulaLogicOperator.And,
                    Call("finite", F.Id("B4"))),
                Present(F.Id("C4"))),
            Implies(
                new Formula.Logic(
                    Call("finite", F.Id("A5")),
                    FormulaLogicOperator.And,
                    Call("finite", F.Id("B5"))),
                Present(F.Id("C5"))),
            Implies(Call("finite", F.Id("B6")), Present(F.Id("C6"))),
            Implies(
                Call("finite", F.Id("S7")),
                Call("supportingLemma", F.Id("greedyScoreRewrite"))),
            Present(F.Id("C8")),
            Call("open", F.Id("greedyArgmaxRuleUnresolved")));
        Formula theoremBody = Implies(premise, conclusions);

        return Disp(Seq(
            Forall, Sp, indexType, Comma, Sp, state, Comma, Sp,
            baselineType, Comma, Sp, targetType, Colon, Sp, type, Comma, Esc,
            codomain, Colon, Sp, Arrow(indexType, type), Comma, Esc,
            definitions, Colon, Sp,
            Seq(Forall, Sp, F.Id("i"), Colon, Sp, indexType, Comma, Sp,
                Call("Concept", state, Call("apply", codomain, F.Id("i")))),
            Comma, Esc,
            q, Colon, Sp, Call("Concept", state, baselineType), Comma, Sp,
            target, Colon, Sp, Call("Concept", state, targetType), Comma, Esc,
            cost, Colon, Sp, Arrow(indexType, F.Id("Real")), Comma, Sp,
            nu, Colon, Sp,
            Call("EscapeWeight", Call("Prod", state, state)), Comma, Esc,
            theoremBody, Dot));
    }

    private static Formula Present(Formula clause) => Call("present", clause);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula Conjoin(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
        {
            result = new Formula.Logic(
                clauses[index], FormulaLogicOperator.And, result);
        }

        return result;
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);
}
