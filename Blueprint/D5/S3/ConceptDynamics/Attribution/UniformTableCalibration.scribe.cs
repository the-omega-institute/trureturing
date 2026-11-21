using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class UniformTableCalibrationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Attribution/UniformTableCalibration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A determinant bound for optimal uniform calibrations of rational finite kernels.",
        H("Equal-weight seeds at the optimal subgroup-fixed mass"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("uniform-kernel-optimum"),
                DeclarationHandle.Create(Prefix + "uniform_kernel_optimum"),
                H("A nonsingular orbit minor gives an optimal uniform calibration"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let a group G act on finite types X and Y, and fix a subgroup H. "
                        + "The kernel P is nonnegative, row normalized, and G-covariant. The positive "
                        + "integer m clears its denominators, with m times each entry specified by "
                        + "an integer z. X and Y may be empty.")),
                    Paragraph(Text("The matrix A has one column for each G-orbit of tables from X "
                        + "to Y. A table is translated by acting on its output and inversely "
                        + "translating its input. The normalization row counts all tables in the "
                        + "orbit. The row indexed by a cell (x,y) counts the orbit's tables "
                        + "that take x to y.")),
                    Paragraph(Text("The theorem gives a real weight function q on the orbits "
                        + "and an injective map r from its positive support to the rows of A. "
                        + "The square submatrix B uses those rows and the supported columns. "
                        + "The positive number N equals m times the absolute determinant "
                        + "of B. The seed type U carries a G-action and has cardinality N.")),
                    Paragraph(Text("UniformCalibration means that evaluation through f gives "
                        + "marginals P with weight 1/N on every seed, and f is pointwise "
                        + "G-equivariant. TableWeights means that the induced table law assigns "
                        + "each table its orbit's weight q. Optimal means that every finite "
                        + "G-set of seeds, with nonnegative invariant weights summing to one "
                        + "and equivariant readout with the same marginals, has H-fixed mass "
                        + "at most the H-fixed mass of the uniform law on U. The seed type U "
                        + "is in the maximum of the input and output universes. The comparison "
                        + "seed type ranges over an independent universe.")),
                    Paragraph(Text("An optimizer with minimum positive support has independent "
                        + "columns. A null direction, oriented to preserve or improve the "
                        + "objective, would otherwise remove a positive coordinate. The "
                        + "adjugate clears denominators on the resulting square minor. Each "
                        + "table then gets an integer number of copies, with the action "
                        + "preserving the copy number."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula q = F.Id("q");
        Formula r = F.Id("r");
        Formula n = F.Id("N");
        Formula u = F.Id("U");
        Formula f = F.Id("f");
        return Disp(Seq(Exists, Sp, q, Comma, Sp, r, Comma, Sp,
            Call("Injective", r), Sp, Land, Sp, Call("PositiveMinorBudget", F.Id("A"), F.Id("m"), q, r, n),
            Sp, Land, Sp, Open, Exists, Sp, u, Comma, Sp, f, Comma, Sp,
            Call("Cardinality", u, n), Sp, Land, Sp, Call("UniformCalibration", u, f, n),
            Sp, Land, Sp, Call("TableWeights", u, f, n, q),
            Sp, Land, Sp, Call("Optimal", u, f, n), Close));
    }

    private static Formula Call(string predicate, params Formula[] arguments)
    {
        var parts = new List<Formula> { Operatorname, Grp(F.Id(predicate)), Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index != 0)
            {
                parts.Add(Comma);
                parts.Add(Sp);
            }
            parts.Add(arguments[index]);
        }
        parts.Add(Close);
        return Seq(parts.ToArray());
    }
}
