using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class PredictionClosureDynamicalRepairDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least invariant observer closure induces dynamics on the visible quotient.",
        H("Prediction Closure as Dynamical Repair"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prediction-closure-minimal-dynamical-repair"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Dynamics/PredictionClosureDynamicalRepair."
                        + "prediction_closure_minimal_dynamical_repair"),
                H("Prediction closure is the least dynamical repair"),
                StatementSource.FromAuthor(RepairFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let K be a linear evolution of observables on a finite-dimensional "
                            + "real Hilbert space, with no invariance assumption on the current "
                            + "visible subspace W. Its prediction closure C is constructed from "
                            + "all forward K-orbits of W, and its final invisible residual R is "
                            + "the orthogonal complement of C.")),
                    Paragraph(Text(
                        "The existing observer-orbit theorem directly proves that C contains W, "
                            + "is K-invariant, and lies in every K-invariant observable extension "
                            + "containing W. Mathlib's exact adjoint-invariance theorem then makes "
                            + "R invariant under the adjoint state evolution.")),
                    Paragraph(Text(
                        "Consequently, differences in R remain in R after state evolution, so "
                            + "final invisibility is a dynamical congruence. Mathlib's quotient "
                            + "map construction supplies the induced linear evolution on V/R and "
                            + "its canonical projection equation.")),
                    Paragraph(Text(
                        "The source compares time evolution with self-reference, contextual, "
                            + "completion, and refinement closures only at the level of a common "
                            + "minimal-stability pattern. This theorem formalizes that pattern for "
                            + "a linear target operation and does not identify objects belonging "
                            + "to those different domains.")),
                    Paragraph(Text(
                        "Repository search found and directly applies "
                            + "observer_closure_is_least_invariant. Pinned Mathlib search found "
                            + "and directly applies Module.End.mem_invtSubmodule_adjoint_iff, "
                            + "Submodule.mapQ, and Submodule.mapQ_mkQ. No theorem was found that "
                            + "packages all of the residual, congruence, quotient, and leastness "
                            + "clauses."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula RepairFormula()
    {
        Formula space = F.Id("V");
        Formula evolution = F.Id("K");
        Formula stateEvolution = Call("adjoint", evolution);
        Formula visible = F.Id("W");
        Formula closure = Call("Cl", evolution, visible);
        Formula residual = Seq(closure, Caret, Grp(Perp));
        Formula first = F.Id("x");
        Formula second = F.Id("y");
        Formula extension = F.Id("U");
        Formula projection = Call("quotientProjection", residual);
        Formula quotientEvolution = Seq(Overline, Grp(stateEvolution));

        Formula extensive = Seq(visible, Sp, Subseteq, Sp, closure);
        Formula closureInvariant = Call("Invariant", evolution, closure);
        Formula residualInvariant = Call("Invariant", stateEvolution, residual);
        Formula congruence = Seq(
            Forall, Sp, first, Comma, Sp, second, InMacro, Sp, space, Comma, Sp,
            first, Sp, Minus, Sp, second, InMacro, Sp, residual,
            Sp, Rightarrow, Sp,
            Apply(stateEvolution, first), Sp, Minus, Sp,
            Apply(stateEvolution, second), InMacro, Sp, residual);
        Formula quotientLaw = Seq(
            quotientEvolution, Sp, Circ, Sp, projection, Sp, Eq, Sp,
            projection, Sp, Circ, Sp, stateEvolution);
        Formula least = Seq(
            Forall, Sp, extension, Colon, Sp, Call("Submodule", space), Comma, Sp,
            Open, visible, Sp, Subseteq, Sp, extension, Sp, Land, Sp,
            Call("Invariant", evolution, extension), Close, Sp, Rightarrow, Sp,
            closure, Sp, Subseteq, Sp, extension);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, space, Colon, Sp,
            Operatorname, Grp(F.Id("FiniteDimensionalRealHilbertSpace")),
            Comma, RowBreak,
            Forall, Sp, evolution, Colon, Sp, Call("End", space), Comma, Sp,
            Forall, Sp, visible, Colon, Sp, Call("Submodule", space), Comma, RowBreak,
            extensive, Sp, Land, Sp,
            closureInvariant, Sp, Land, Sp,
            residualInvariant, Sp, Land, RowBreak,
            Open, congruence, Close, Sp, Land, RowBreak,
            quotientLaw, Sp, Land, RowBreak,
            Open, least, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
