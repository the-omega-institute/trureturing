using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class ProjectedUnistochasticDynamicsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Projected unitary dynamics induces a doubly stochastic transition law.",
        H("Projected Unitary Dynamics"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("projected-unitary-dynamics-is-a-markov-chain"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics."
                        + "projected_dynamics_is_unistochastic"),
                H("Projected unitary dynamics is a Markov chain"),
                StatementSource.FromAuthor(ProjectedDynamicsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let U be a finite unitary matrix written in measurement-basis "
                            + "coordinates. Starting from arbitrary real diagonal weights, form "
                            + "the state orbit by repeatedly conjugating with U and projecting "
                            + "onto the measurement-basis diagonal. The displayed weights are "
                            + "read back from that orbit; they are not defined by the recurrence.")),
                    Paragraph(Text(
                        "Every state in the post-projection orbit is the sum of its weights times "
                            + "the coordinate rank-one projectors. The transition entry from j to "
                            + "k is the squared norm of U at (k,j), and the full weight vector is "
                            + "advanced by multiplication with this matrix.")),
                    Paragraph(Text(
                        "The existing repository theorem "
                            + "normSqMatrix_mem_doublyStochastic_of_unitary is applied directly "
                            + "to prove that the transition matrix is doubly stochastic. Local "
                            + "matrix-entry calculations establish the diagonal decomposition "
                            + "and recurrence."))),
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

    private static Formula ProjectedDynamicsFormula()
    {
        Formula index = F.Id("I");
        Formula unitary = F.Id("U");
        Formula initial = F.Id("p");
        Formula n = F.Id("n");
        Formula j = F.Id("j");
        Formula k = F.Id("k");
        Formula orbit = Call("projectedOrbit", unitary, initial, n);
        Formula weights = Call("projectedWeights", unitary, initial, n);
        Formula nextWeights = Call(
            "projectedWeights", unitary, initial, Seq(n, Plus, D(1)));
        Formula transition = Call("transitionMatrix", unitary);

        Formula decomposition = Seq(
            Forall, Sp, n, Comma, Esc,
            orbit, Sp, Eq, Sp,
            Sum, Underscore, Grp(j), Sp,
            weights, Underscore, Grp(j), Sp,
            Call("basisProjector", j));
        Formula entries = Seq(
            Forall, Sp, k, Comma, Sp, j, Comma, Esc,
            transition, Underscore, Grp(k, j), Sp, Eq, Sp,
            Vert, Sp, unitary, Underscore, Grp(k, j), Sp, Vert, Caret, Grp(D(2)));
        Formula stochastic = Seq(
            transition, Sp, InMacro, Sp, Call("DoublyStochastic", index));
        Formula recurrence = Seq(
            Forall, Sp, n, Comma, Esc,
            nextWeights, Sp, Eq, Sp, transition, Sp, weights);

        return Disp(Seq(
            Forall, Sp, index, Colon, Sp, Operatorname, Grp(F.Id("FiniteType")),
            Comma, Esc,
            Forall, Sp, unitary, InMacro, Sp, Call("UnitaryMatrices", index),
            Comma, Esc,
            Forall, Sp, initial, Colon, Sp, index, To, Mathbb, Grp(F.Id("R")),
            Comma, Esc,
            decomposition, Sp, Land, Sp,
            entries, Sp, Land, Sp,
            stochastic, Sp, Land, Sp,
            recurrence, Dot));
    }
}
