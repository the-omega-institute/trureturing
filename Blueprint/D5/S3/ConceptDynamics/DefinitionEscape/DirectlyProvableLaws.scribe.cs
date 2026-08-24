using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscape;

internal sealed class DirectlyProvableLawsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nine direct DECT laws are packaged without duplicating canonical primitives.",
        H("Directly Provable DECT Laws"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("directly-provable-dect-laws"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DefinitionEscape/DirectlyProvableLaws."
                        + "directly_provable_laws"),
                H("Nine direct laws for definition escape and completion"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The nine conjuncts follow the source order exactly: residual "
                            + "intersection; sufficiency-factorization; zero gain from a "
                            + "redundant definition; blind-kernel impossibility; finite-object "
                            + "compactness; submodular capture; the prepared one-step defect "
                            + "identity; the semigroup defect identity; and the approximate "
                            + "cascade triangle bound.")),
                    Paragraph(Text(
                        "The first conjunct applies residual_join_law. The second uses the same "
                            + "fiber-constancy equivalence packaged by target_recovery_criterion, "
                            + "including the empty-state case without adding an inhabitedness "
                            + "premise. The fourth applies blind_kernel_obstruction after its "
                            + "residual witness supplies an inhabited state.")),
                    Paragraph(Text(
                        "The canonical defectRelation is the only target residual throughout. "
                            + "For finite X, each baseline defect pair is assigned a package "
                            + "definition that separates it; enumeration of the finite subtype "
                            + "then gives a finite sufficient extension. No second residual, "
                            + "kernel, or joint readout is introduced.")),
                    Paragraph(Text(
                        "Capture is measured on the residual intersection with a finite union "
                            + "of cuts. Finite-union measurability, measure monotonicity, and the "
                            + "union-intersection measure identity yield submodularity. The last "
                            + "three conjuncts respectively unfold composition, apply the "
                            + "semigroup law, and combine a Lipschitz bound with the metric "
                            + "triangle inequality.")),
                    Paragraph(Text(
                        "Boolean examples witness a nonempty residual, redundant zero gain, a "
                            + "blind obstruction, and finite closure by one identity definition. "
                            + "Counting measure gives a strict capture inequality. Coordinate "
                            + "swap on real pairs gives nonzero prepared and semigroup defects, "
                            + "and the real identity map attains the cascade bound."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula x = F.Id("X");
        Formula q = F.Id("q");
        Formula target = F.Id("T");
        Formula definition = F.Id("d");
        Formula package = F.Id("Gamma");
        Formula a = F.Id("A");
        Formula b = F.Id("B");
        Formula y = F.Id("y");
        Formula projection = F.Id("projection");
        Formula prepare = F.Id("prepare");
        Formula update = F.Id("update");
        Formula evolution = F.Id("evolution");
        Formula second = F.Id("second");
        Formula direct = F.Id("direct");
        Formula k = F.Id("K");
        Formula delta = F.Id("delta");
        Formula eta = F.Id("eta");
        Formula residual = Call("E", q, target);
        Formula joinedResidual = Call("E", Call("join", q, definition), target);
        Formula residualIntersection = Seq(
            joinedResidual, Sp, Eq, Sp,
            Call("intersection", residual, Call("ker", definition)));
        Formula factorization = Seq(
            residual, Sp, Eq, Sp, Emptyset, Sp, Leftrightarrow, Sp,
            Call("FactorsThrough", target, q));
        Formula redundant = Seq(
            Call("Refines", definition, q), Sp, Rightarrow, Sp,
            joinedResidual, Sp, Eq, Sp, residual);
        Formula blind = Seq(
            Call("Nonempty", Call("blindResidual", package, q, target)), Sp,
            Rightarrow, Sp, Neg,
            Call("finiteSelectionSufficient", package, q, target));
        Formula finite = Seq(
            Open, Call("Finite", x), Sp, Land, Sp,
            Call("blindResidual", package, q, target), Sp, Eq, Sp, Emptyset, Close,
            Sp, Rightarrow, Sp, Exists, Sp, F.Id("n"), Comma, Sp, F.Id("defs"),
            Comma, Sp,
            Call("E", Call("languageExtension", q, F.Id("defs")), target),
            Sp, Eq, Sp, Emptyset);
        Formula captureInequality = Seq(
            Call("mu", Call("captured", Call("union", a, b))), Sp, Plus, Sp,
            Call("mu", Call("captured", Call("intersection", a, b))), Sp,
            Leq, Sp, Call("mu", Call("captured", a)), Sp, Plus, Sp,
            Call("mu", Call("captured", b)));
        Formula capture = Seq(
            Open, Call("Measurable", residual), Sp, Land, Sp,
            Call("MeasurableCuts", F.Id("cut")), Close, Sp, Rightarrow, Sp,
            captureInequality);
        Formula preparedEquality = Seq(
            Call("preparedDefect", update, prepare, x), Sp,
            Eq, Sp, Call("oneStepDefect", update, x));
        Formula prepared = Seq(
            Call("RightInverse", prepare, projection), Sp, Rightarrow, Sp,
            preparedEquality);
        Formula semigroupEquality = Seq(
            Call("semigroupDefect",
                Seq(F.Id("t"), Sp, Plus, Sp, F.Id("s")), F.Id("m")),
            Sp, Eq, Sp,
            Call("preparedDefectAfter", F.Id("t"), F.Id("s"), F.Id("m")));
        Formula semigroup = Seq(
            Open, Call("RightInverse", prepare, projection), Sp, Land, Sp,
            Call("SemigroupLaw", evolution), Close, Sp, Rightarrow, Sp,
            semigroupEquality);
        Formula cascade = Seq(
            Open, Call("LipschitzWith", k, second), Sp, Land, Sp,
            Call("dist", Call("first", x), y), Sp, Leq, Sp, delta, Sp, Land, Sp,
            Call("dist", Call("second", y), Call("direct", x)), Sp, Leq, Sp,
            eta, Close, Sp, Rightarrow, Sp,
            Call("dist", Call("second", Call("first", x)), Call("direct", x)),
            Sp, Leq, Sp, k, Sp, Times, Sp, delta, Sp, Plus, Sp, eta);

        return Disp(Seq(
            residualIntersection, Comma, RowBreak, Grp(),
            factorization, Comma, RowBreak, Grp(),
            redundant, Comma, RowBreak, Grp(),
            blind, Comma, RowBreak, Grp(),
            finite, Comma, RowBreak, Grp(),
            capture, Comma, RowBreak, Grp(),
            prepared, Comma, RowBreak, Grp(),
            semigroup, Comma, RowBreak, Grp(),
            cascade, Dot));
    }
}
