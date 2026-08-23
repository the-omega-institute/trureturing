using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class OneStepProbabilityInnovationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One complementary context removes exactly its centered probability energy.",
        H("One-Step Probability Innovation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("one-context-gives-exact-probability-innovation"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/OneStepProbabilityInnovation."
                        + "one_step_probability_innovation"),
                H("One context gives the exact probability innovation"),
                StatementSource.FromAuthor(InnovationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let rho be a density matrix and Xrho its canonical centered coordinate "
                            + "on the real trace-zero Hermitian carrier. Let S be the visible "
                            + "subspace before adding a complete rank-one context and Snext the "
                            + "visible subspace afterward.")),
                    Paragraph(Text(
                        "The added context plane is constructed as the real span of its centered "
                            + "rank-one projectors, and each displayed probability is constructed "
                            + "by the Born trace rule. Assume S is contained in Snext, the new "
                            + "directions are exactly that centered context plane, and its "
                            + "projection energy is the sum of centered probability squares.")),
                    Paragraph(Text(
                        "Then the old residual mass minus the new residual mass is exactly that "
                            + "probability sum. Public companion clauses state that the old "
                            + "residual space is the sum of the context plane and the new "
                            + "residual, and that these two summands are orthogonal.")),
                    Paragraph(Text(
                        "The proof applies the repository's innovation-energy recurrence and "
                            + "Mathlib's exact nested-subspace orthogonal splitting theorem. "
                            + "Repository and pinned-library searches found no existing theorem "
                            + "combining all three clauses on the canonical quantum carrier."))),
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

    private static Formula InnovationFormula()
    {
        Formula rho = Rho;
        Formula dimension = F.Id("d");
        Formula outcome = F.Id("j");
        Formula visible = F.Id("S");
        Formula nextVisible = F.Id("Snext");
        Formula plane = Call("centeredContextPlane", F.Id("B"));
        Formula inverseDimension = Seq(Frac, Grp(D(1)), Grp(dimension));
        Formula probability = Call("contextProbability", rho, F.Id("B"), outcome);
        Formula deviation = Seq(Grp(probability, Minus, inverseDimension), Caret, Grp(D(2)));
        Formula oldResidual = Call("residualMass", visible, Call("densityCoordinate", rho));
        Formula newResidual = Call("residualMass", nextVisible, Call("densityCoordinate", rho));

        return Disp(Seq(
            oldResidual, Sp, Minus, Sp, newResidual, Sp, Eq, Sp,
            Sum, Underscore, Grp(outcome), Sp, deviation, Sp, Land, Sp, RowBreak,
            Call("orthogonal", visible), Sp, Eq, Sp, plane, Sp, Plus, Sp,
            Call("orthogonal", nextVisible), Sp, Land, Sp, RowBreak,
            plane, Sp, Perp, Sp, Call("orthogonal", nextVisible), Dot));
    }
}
