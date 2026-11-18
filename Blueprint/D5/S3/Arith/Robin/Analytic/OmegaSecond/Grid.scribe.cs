using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaSecond;

internal sealed class GridDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite logistic grids with explicit entropy and cost errors.",
        H("Finite logistic grids"),
        Blocks(
            Paragraph(Text("The grid is fixed before the real cutoff varies. Its occupancy at distance u is q(u)=1/(1+exp(u)); H is Mathlib's binary entropy. The Mellin suppliers at exponents one and two give the integrals of q and u*q as log 2 and pi^2/12. Integration by parts then gives the integral of log(1+exp(-u)) as pi^2/12 and the integral of H(q(u)) as pi^2/6.")),
            Paragraph(Text("This is an analytic ingredient in equal-number exchanges around a primorial cutoff. The method precedent is Erdős–Nicolas 1981, Section 1, including exchanges on both sides of a primorial and the partition-constant mechanism. No claim of a new exchange method is made.")),
            Describe.Lean(DescribeId.Create("logistic"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Grid.logistic"),
                H("Occupancy"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("q(u)=(1+exp(u)) inverse."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fermi-log"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Grid.fermiLog"),
                H("Fermi logarithm"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("J(u)=log(1+exp(-u))."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("entropy"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Grid.entropy"),
                H("Logistic entropy"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("H(q(u))=J(u)+u*q(u)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mesh"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Grid.Mesh"),
                H("Uniform finite mesh"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A positive endpoint U and positive natural number n specify a uniform partition of [0,U]."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("step"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Grid.Mesh.step"),
                H("Mesh width"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The width delta=U/n."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("node"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Grid.Mesh.node"),
                H("Mesh nodes"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The i-th node is i*delta."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cost"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Grid.Mesh.cost"),
                H("Endpoint cost"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Twice the sum delta*t_i*q(t_i), over right endpoints."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mass"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Grid.Mesh.mass"),
                H("Endpoint entropy"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Twice the sum delta*H(q(t_i)), over right endpoints."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("grid-bounds"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Grid.grid_bounds"),
                H("Explicit cost and entropy errors"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cost is at most pi^2/6+2*delta*log 2. The entropy is at least pi^2/3-2*(U+2)*exp(-U)-2*delta*log 2. Monotonicity of q controls cost without assuming monotonicity of u*q; entropy errors telescope along the partition."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("good-grid"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Grid.exists_good_grid"),
                H("A fixed grid with prescribed slack"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive eta and rho there is a finite grid with cost at most (pi^2/6)*(1+eta/2) and entropy at least pi^2/3-rho. Both U and n depend only on those tolerances, not on the real cutoff."))), DescribeRole.Theorem))));
}
