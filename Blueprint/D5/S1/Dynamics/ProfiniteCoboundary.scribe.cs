using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics;

internal sealed class ProfiniteCoboundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "Normalized continuous transfers in all finite quotients assemble into one profinite transfer.",
            H("Continuous profinite transfers from finite quotients"),
            Blocks(
                Paragraph(Text("Fix a topological space with an integer action and a basepoint whose integer orbit is dense. Let P be any profinite group and let c map the space into P. If the equation b(Tx) = c(x)b(x) has a continuous solution after projection to every quotient by an open normal subgroup, it has a unique continuous solution in P with b equal to one at the basepoint. There is no countability, metrizability, commutativity or source compactness hypothesis. The conditional theorem does not need continuity of c or of the action as a separate assumption.")),
                Paragraph(Text("Normalize each finite-quotient solution by multiplying on the right by its basepoint value inverse. Two solutions have invariant difference b(x) inverse times d(x), so density and continuity force normalized solutions to agree. Uniqueness makes the finite solutions compatible with every quotient map. Their coordinatewise continuous thread lies in the existing Mathlib inverse limit; the topological group isomorphism back to P supplies the transfer.")),
                Paragraph(Text("For the same balanced Toeplitz base, the application concerns exactly letter cocycles: choose arbitrary p0 and p1 in P and set c(y) to p0 or p1 according to y(0). In a finite quotient, Balanced.balancedWord_holonomy_eq_one supplies identity returns, and Balanced.continuous_transfer with Balanced.transfer_shift supplies the continuous solution. Applying this bridge yields a unique normalized profinite solution. This application does not establish triviality of arbitrary continuous cocycles depending on longer symbolic windows.")),
                Describe.Lean(DescribeId.Create("finite-quotient-transfer"),
                    DeclarationHandle.Create("D5/S1/Dynamics/ProfiniteCoboundary.exists_unique_continuous_transfer_of_finite_quotients"),
                    H("Finite quotient solutions give a unique normalized profinite solution"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("A specified dense integer orbit fixes the normalization. Continuous solutions in all finite open-normal quotients assemble into a unique continuous solution in the original, possibly noncommutative and nonmetrizable, profinite group."))),
                    DescribeRole.Theorem))));
}
