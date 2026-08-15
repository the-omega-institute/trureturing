using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Tomography;

internal sealed class InnovationEnergyRecurrenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nested observation spaces split residual energy into later residual and innovation.",
        H("Innovation-Energy Recurrence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nested-observation-spaces-split-residual-energy"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Tomography/InnovationEnergyRecurrence."
                        + "innovation_energy_recurrence"),
                H("Nested observation spaces split residual energy"),
                StatementSource.FromAuthor(RecurrenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let U be contained in W in a finite-dimensional real inner-product "
                            + "space. The residual energy of x at a subspace is the squared norm "
                            + "of its orthogonal projection onto the subspace complement. The "
                            + "innovation subspace is the intersection of U's orthogonal "
                            + "complement with W.")),
                    Paragraph(Text(
                        "Project the U-residual onto the innovation subspace and its orthogonal "
                            + "complement. Nestedness identifies the first component with the "
                            + "innovation projection of x. Projection uniqueness identifies the "
                            + "second component with the W-residual, because their difference "
                            + "lies in the innovation subspace.")),
                    Paragraph(Text(
                        "Loogle found the exact pinned-Mathlib squared-norm decomposition "
                            + "Submodule.norm_sq_eq_add_norm_sq_starProjection, which is imported "
                            + "and applied. A second Loogle query required a namespace correction; "
                            + "LeanSearch API attempts returned only HTTP capability failures. "
                            + "Repository and formalization searches found no existing "
                            + "innovation-energy recurrence.")),
                    Paragraph(Text(
                        "The result is finite-dimensional and real. It formalizes the exact "
                            + "one-step energy identity for nested observation spaces; it does "
                            + "not add time-indexed observer dynamics or an infinite-dimensional "
                            + "closed-subspace extension."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula>
        {
            Operatorname,
            Grp(F.Id(name)),
            Open,
        };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[i]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula RecurrenceFormula()
    {
        Formula u = F.Id("U");
        Formula w = F.Id("W");
        Formula x = F.Id("x");
        Formula innovation = Call("innovationSubspace", u, w);
        Formula innovationProjection = Seq(
            Operatorname, Grp(F.Id("proj")), Underscore, Grp(innovation), Open, x, Close);
        return Disp(Seq(
            Forall, Sp, u, Comma, Sp, w, InMacro, Sp,
            Operatorname, Grp(F.Id("Sub")), Open, F.Id("V"), Close, Comma, Esc,
            u, Sp, Subseteq, Sp, w, Sp, Rightarrow, Sp,
            Forall, Sp, x, InMacro, Sp, F.Id("V"), Comma, Esc,
            Call("residualEnergy", u, x), Sp, Eq, Sp,
            Call("residualEnergy", w, x), Sp, Plus, Sp,
            Vert, innovationProjection, Vert, Caret, Grp(D(2)), Dot));
    }
}
