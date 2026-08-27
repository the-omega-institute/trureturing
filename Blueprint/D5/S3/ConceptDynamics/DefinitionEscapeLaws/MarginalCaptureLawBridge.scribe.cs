using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeLaws;

internal sealed class MarginalCaptureLawBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite additive escape mass discharges the canonical marginal capture law.",
        H("Finite-Additive Marginal Capture Bridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-additive-marginal-capture-bridge"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DefinitionEscapeLaws/"
                        + "MarginalCaptureLawBridge."
                        + "marginal_capture_law_of_finite_additive_mass"),
                H("Marginal capture decreases as the finite definition set grows"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The formula retains every Lean premise. nonnegativeCost states that "
                            + "zero is below every candidate cost. disjointAdditive states that "
                            + "nu.mass(left union right) equals nu.mass(left) plus nu.mass(right) "
                            + "when left and right are disjoint. Delta is finite, Gamma is a "
                            + "subset of Delta, and the added definition is not in Delta. There "
                            + "is no Finite X, Nonempty, DecidableEq, measurability, monotonicity, "
                            + "or shared-codomain premise.")),
                    Paragraph(Text(
                        "The Lean conclusion is the imported marginalCaptureLaw without any "
                            + "change to its statement. It expands to F(Gamma union singleton d) "
                            + "minus F(Gamma) greater than or equal to F(Delta union singleton d) "
                            + "minus F(Delta), where F is the imported capturedEscapeMass and "
                            + "therefore still means M(empty) minus M(S). The candidate family "
                            + "keeps the dependent codomain V(i), and defectRelation remains the "
                            + "only target residual.")),
                    Paragraph(Text(
                        "The proof is exactly the sixth projection of submodular_capture. The "
                            + "finite-Delta and nonnegative-cost assumptions are retained source-"
                            + "domain conditions, not advertised as local proof guards. Finite "
                            + "additivity is the proof guard that connects the weak EscapeWeight "
                            + "interface to the source weighted-cover reading.")),
                    Paragraph(Text(
                        "Boundary: this bridge proves the law only under the displayed finite-"
                            + "additivity premise. Downstream users must not cite it as proving "
                            + "diminishing marginal capture from the weak EscapeWeight interface "
                            + "alone. FiniteCoverCounting.lean:380 contains the canonical weak-"
                            + "interface countermodel.")),
                    Paragraph(Text(
                        "The named Boolean positive witness supplies a nonempty finite model with "
                            + "strictly decreasing marginal capture. The imported clause-six false "
                            + "neighbor changes only the inequality to a strict inequality in the "
                            + "opposite direction under unchanged premises. The nonvacuity theorem "
                            + "consumes the local positive witness and that existing complete false-"
                            + "neighbor statement directly.")),
                    Paragraph(Text(
                        "Named scope limit MARGINAL_CAPTURE_BRIDGE_DOES_NOT_REPACKAGE_"
                            + "MONOTONICITY_OR_FOUR_TERM_SUBMODULARITY: DECT source line 550 also "
                            + "states monotonicity and four-term submodularity. This bridge covers "
                            + "only the diminishing-return clause at source lines 550-558 because "
                            + "that is the missing FiniteCoverCounting clause. The omitted source "
                            + "claims are already closed by submodular_capture conjuncts four and "
                            + "five; this is a named scope boundary, not an open mathematical gap.")),
                    Paragraph(Text(
                        "scribe_lean_correspondence: the single displayed item present("
                            + "diminishingMarginalCapture) maps to the sole Lean conclusion, "
                            + "marginalCaptureLaw. Every Lean premise appears in the displayed "
                            + "antecedent. The mapping is weaker because present omits the expanded "
                            + "inequality and the definitions of M and F. Equal mappings: zero. "
                            + "Stronger mappings: zero."))),
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
        Formula gamma = F.Id("Gamma");
        Formula delta = F.Id("Delta");
        Formula definition = F.Id("d");
        Formula premise = Conjoin(
            Call("nonnegativeCost", cost),
            Call("disjointAdditive", nu),
            Call("finite", delta),
            Call("subset", gamma, delta),
            Call("notMember", definition, delta));
        Formula conclusion = Call("present", F.Id("diminishingMarginalCapture"));

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
            nu, Colon, Sp, Call("EscapeWeight", Call("Prod", state, state)), Comma, Esc,
            gamma, Comma, Sp, delta, Colon, Sp, Call("Set", indexType), Comma, Sp,
            definition, Colon, Sp, indexType, Comma, Esc,
            Implies(premise, conclusion), Dot));
    }

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
