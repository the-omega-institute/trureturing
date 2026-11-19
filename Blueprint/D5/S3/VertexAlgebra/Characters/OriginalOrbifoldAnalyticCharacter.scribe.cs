using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Characters;

internal sealed class OriginalOrbifoldAnalyticCharacterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Absolute convergence and analytic decomposition of the original Golay–Leech orbifold zero-mode character.",
        H("Original Golay–Leech orbifold character"),
        Blocks(
            Paragraph(Text("For an upper-half-plane parameter tau, set h=exp(pi i tau) and q=h^2. The multiplicity at natural weight n is the complex dimension of the eigenspace of the original conformal zero mode. The central charge is 24, so the character sums each multiplicity against exp(2 pi i tau (n-1)).")),
            Describe.Lean(DescribeId.Create("orbifold-half-nome"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/OriginalOrbifoldAnalyticCharacter.halfNome"),
                H("Half nome"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The half nome is the exponential exp(pi i tau) on the specified parameter tau."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("orbifold-nome"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/OriginalOrbifoldAnalyticCharacter.nome"),
                H("Nome"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ordinary nome is the exponential exp(2 pi i tau)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ambient-leech-character"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/OriginalOrbifoldAnalyticCharacter.ambientCharacter"),
                H("Ambient lattice character"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ambient term is q inverse times the product of the all-charge Leech theta series and the ordinary oscillator occupation series."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("negative-twisted-character"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/OriginalOrbifoldAnalyticCharacter.negativeTwistedCharacter"),
                H("Negative twisted character"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If F is the 24-coloured half-occupation series, the negative twisted trace is 4096 h (F(h)-F(-h))/2. The original twisted ground energy gives the factor h after the central-charge shift."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("orbifold-weight-multiplicity"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/OriginalOrbifoldAnalyticCharacter.multiplicity"),
                H("Weight multiplicity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the finite rank of the original orbifold conformal zero-mode eigenspace at the given natural weight."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("orbifold-shifted-character"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/OriginalOrbifoldAnalyticCharacter.character"),
                H("Shifted character"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The terms use the literal weight multiplicities of the original Golay–Leech orbifold."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("orbifold-analytic-decomposition"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/OriginalOrbifoldAnalyticCharacter.actual_leech_shifted_character"),
                H("Absolute convergence and sector decomposition"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The shifted character at Im(tau)>0 is absolutely summable. Its value is half the sum of the ambient lattice character and (eta(tau)/eta(2 tau))^24, plus the negative twisted character.")),
                    Paragraph(Text("The grade basis identifies the dimension with the cardinal of the full charge and oscillator energy fiber. The positive-definite Gaussian theta estimate and the ordinary occupation norm bound give absolute convergence before grouping that product by grade. The signed trace uses the existing normalized eta identity.")),
                    Paragraph(Text("The twisted coefficient at weight k+2 counts occupation degree 2k+1. The two half-nome evaluations converge absolutely, and their difference cancels the even degrees. The resulting shift is 4096 h times the odd-degree projection.")),
                    Paragraph(Text("Translation by one negates h and preserves q. Applying the normalized half-occupation eta identity at tau and tau+1 evaluates the twisted term as 2048 times the sum of the corresponding eta ratios to power 24. The signs are fixed by the exponential half nome. Each shifted grade term is invariant under translation by one."))),
                DescribeRole.Theorem)
        )));
}
