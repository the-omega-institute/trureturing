using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeLaws;

internal sealed class SubmodularCaptureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive finitely additive escape mass makes DECT capture a submodular coverage law.",
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
                        "The displayed implication preserves both Lean premises. Positive means "
                            + "zero is strictly below nu.mass(defectRelation(q,T)); "
                            + "disjointAdditive means exactly that mass(left union right) equals "
                            + "mass(left) plus mass(right) whenever left and right are disjoint. "
                            + "It does not abbreviate countable additivity, measurability, "
                            + "finiteness, inhabitedness, decidable equality, or monotonicity.")),
                    Paragraph(Text(
                        "The candidate family has the dependent Lean type definitions : "
                            + "forall i : I, Concept X (V i). Thus the formula does not replace "
                            + "the source family by a shared codomain. M is the imported "
                            + "residualEscapeMass and F is the imported capturedEscapeMass, "
                            + "whose definition is M(empty) minus M(S). The canonical "
                            + "defectRelation is the only target residual.")),
                    Paragraph(Text(
                        "C1 through C8 map in order to the eight Lean conjuncts: the exact M "
                            + "formula together with positive M(empty); the exact two-step F "
                            + "definition; the captured-union "
                            + "expansion; monotonicity; four-term submodularity; diminishing "
                            + "returns under A subset B and d not in B; equivalence of the two "
                            + "greedy score formulations; and persistence of a pair lying in "
                            + "the baseline defect while every candidate readout identifies it. "
                            + "The present labels are weaker summaries, not extra predicates.")),
                    Paragraph(Text(
                        "The proof reuses capture_weight_submodular for the coverage step and "
                            + "uses finite additivity to identify M(empty) minus M(S) with the "
                            + "mass of the captured union. The positive premise excludes the "
                            + "constant-zero interpretation; it is not used as a hidden premise "
                            + "for only one selected conclusion."))),
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
            Seq(D(0), Sp, Lt, Sp,
                Call("mass", nu, Call("defectRelation", q, target))),
            FormulaLogicOperator.And,
            Call("disjointAdditive", nu));
        Formula conclusions = Seq(
            Present(F.Id("C1")), Sp, Land, Sp,
            Present(F.Id("C2")), Sp, Land, Sp,
            Present(F.Id("C3")), Sp, Land, Sp,
            Present(F.Id("C4")), Sp, Land, Sp,
            Present(F.Id("C5")), Sp, Land, Sp,
            Present(F.Id("C6")), Sp, Land, Sp,
            Present(F.Id("C7")), Sp, Land, Sp,
            Present(F.Id("C8")));

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
            premise, Sp, Rightarrow, Sp, conclusions, Dot));
    }

    private static Formula Present(Formula clause) => Call("present", clause);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);
}
