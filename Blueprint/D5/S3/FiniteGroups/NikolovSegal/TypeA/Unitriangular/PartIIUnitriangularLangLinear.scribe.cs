using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class PartIIUnitriangularLangLinearDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Root weights and terminating coordinate dynamics for the unitriangular Lang map.",
        H("Part II Unitriangular Lang Linear"),
        Blocks(
            Paragraph(Text("Let F be any field, n a natural rank and a a unit of F. A matrix has depth r when its entries below the r-th superdiagonal vanish. Multiplication adds depths. On strict-upper matrices, delta multiplies the (i,j) entry by a^(j-i)-1; nonresonance permits division by every such root weight.")),
            Paragraph(Text("Under nonresonance, for a strict-upper target b the coordinate equation delta(a)(X) = b + b*X becomes X = deltaInv(a)(b) + T_b(X), where T_b is deltaInv after left multiplication by b. Division preserves depth and left multiplication by b raises it, so T_b^(n-1) vanishes on strict-upper inputs. The inverse coordinate is therefore the finite sum over range(n-1). In ranks zero and one, strict-upper inputs are zero and this sum is empty.")),
            Describe.Lean(
                DescribeId.Create("typea-unitriangular-lang-nonresonant"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLangLinear.Nonresonant"),
                H("Nonresonant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nonresonance means a^d != 1 for every positive distance d < n over the given field. In ranks zero and one this condition is vacuous."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-unitriangular-lang-finite-solution-equation"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLangLinear.finiteSolution_equation"),
                H("finite solution equation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under nonresonance, for a strict-upper target b put T_b(X) = deltaInv(a)(b*X), with multiplication by b performed first on the left. The sum of T_b^k(deltaInv(a)(b)) over 0 <= k < n-1 solves delta(a)(X) = b + b*X. Each application raises depth by one, so the terminal iterate vanishes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-unitriangular-lang-finite-solution-unique"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLangLinear.finiteSolution_unique"),
                H("finite solution unique"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under nonresonance, every strict-upper solution of the coordinate equation equals the finite Neumann sum. The two geometric telescoping identities give existence and uniqueness on strict-upper inputs."))),
                DescribeRole.Theorem))));
}
