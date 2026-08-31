using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscape;

internal sealed class EscapeRefinementAntitoneDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refining an observer family can only shrink its target defect and primitive escape.",
        H("Escape Refinement Antitonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("escape-refinement-antitone"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DefinitionEscape/EscapeRefinementAntitone."
                        + "escape_refinement_antitone"),
                H("Selected observer refinement shrinks target escape"),
                StatementSource.FromAuthor(SelectedEscapeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary index, state, baseline, and target types, V is a "
                            + "dependent observer-codomain family and definitions supplies one "
                            + "concept at each index. The only order datum is S contained in S'.")),
                    Paragraph(Text(
                        "Equality of the refined joint readout restricts pointwise to every "
                            + "index in S, while the target inequality is unchanged. Hence the "
                            + "defect relation for S' is contained in the defect relation for S "
                            + "without finiteness, inhabitedness, or target-side premises."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("primitive-escape-refinement-antitone"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DefinitionEscape/EscapeRefinementAntitone."
                        + "primitive_escape_refinement_antitone"),
                H("Intersection-kernel primitive escape is antitone"),
                StatementSource.FromAuthor(PrimitiveEscapeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Gamma and Delta are homogeneous concept families with Gamma contained "
                            + "in Delta. PrimitiveEscape is the accepted complement of semantic "
                            + "closure, whose relation carrier is the intersection jointKernel.")),
                    Paragraph(Text(
                        "The accepted jointKernel_antitone law sends every Delta-kernel pair to "
                            + "a Gamma-kernel pair. A candidate outside the larger semantic "
                            + "closure is therefore outside the smaller closure. This is the "
                            + "intersection-family form of the finite-window law above."))),
                DescribeRole.Theorem))));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula SelectedEscapeFormula()
    {
        Formula indexType = F.Id("I");
        Formula state = F.Id("X");
        Formula baselineType = F.Id("C");
        Formula targetType = F.Id("Target");
        Formula codomainFamily = F.Id("V");
        Formula smaller = F.Id("S");
        Formula larger = Seq(F.Id("S"), Apos);
        Formula definitions = F.Id("definitions");
        Formula baseline = F.Id("q");
        Formula target = F.Id("target");
        Formula type = F.Id("Type");
        Formula index = F.Id("i");
        Formula selectedReadout(Formula selection) => Call(
            "conceptJoin",
            baseline,
            Call("jointReadout", Call("restrict", definitions, selection)));
        Formula escape(Formula selection) =>
            Call("defectRelation", selectedReadout(selection), target);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(indexType, type), Comma, Sp,
                Typed(state, type), Comma, Sp,
                Typed(baselineType, type), Comma, Sp,
                Typed(targetType, type), Comma),
            Seq(
                Typed(codomainFamily, new Formula.TypeArrow(indexType, type)), Comma),
            Seq(
                Typed(smaller, Call("Set", indexType)), Comma, Sp,
                Typed(larger, Call("Set", indexType)), Comma),
            Seq(
                Typed(
                    definitions,
                    Seq(
                        Forall, Sp, Typed(index, indexType), Comma, Sp,
                        Call("Concept", state, Seq(codomainFamily, Open, index, Close)))),
                Comma),
            Seq(
                Typed(baseline, Call("Concept", state, baselineType)), Comma, Sp,
                Typed(target, Call("Concept", state, targetType)), Comma),
            Seq(
                smaller, Sp, Subseteq, Sp, larger, Sp, Rightarrow, Sp,
                escape(larger), Sp, Subseteq, Sp, escape(smaller), Dot),
        ]));
    }

    private static Formula PrimitiveEscapeFormula()
    {
        Formula state = F.Id("X");
        Formula inputOutput = F.Id("InputOutput");
        Formula output = F.Id("Output");
        Formula gamma = F.Id("Gamma");
        Formula delta = F.Id("Delta");
        Formula candidate = F.Id("candidate");
        Formula conceptFamily = Call("Set", Call("Concept", state, inputOutput));
        Formula candidateType = Call("Concept", state, output);
        Formula escaping(Formula family) => Seq(
            OpenBrace,
            candidate, Colon, Sp, candidateType, Sp, Bar, Sp,
            Call("PrimitiveEscape", family, candidate),
            CloseBrace);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(state, F.Id("Type")), Comma, Sp,
                Typed(inputOutput, F.Id("Type")), Comma, Sp,
                Typed(output, F.Id("Type")), Comma),
            Seq(
                Typed(gamma, conceptFamily), Comma, Sp,
                Typed(delta, conceptFamily), Comma),
            Seq(
                gamma, Sp, Subseteq, Sp, delta, Sp, Rightarrow, Sp,
                escaping(delta), Sp, Subseteq, Sp, escaping(gamma), Dot),
        ]));
    }
}
