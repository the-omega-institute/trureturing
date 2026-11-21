using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.NumericalSemigroup;

internal sealed class TwoWitnessResiduesDocument : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/Combinatorics/NumericalSemigroup/TwoWitnessResidues.nonnegative_at_nearest_residue";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two residue representatives decide feasibility within the span of two integer witnesses.",
        H("Nonnegative vectors in the span of two integer witnesses"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nonnegative-at-nearest-residue"),
                DeclarationHandle.Create(Result),
                H("The nearest two residue coefficients decide nonnegative feasibility"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let p and u be integer-valued functions on an arbitrary index "
                        + "type. Assume p is nonnegative at each index. Let the degrees assigned to p "
                        + "and u be b and 1, with b a positive integer. Fix a nonnegative degree t "
                        + "and write t = bq + r with 0 ≤ r < b.")),
                    Paragraph(Text("There exists a pair of integer coefficients a and c at degree t giving a "
                        + "nonnegative vector if and only if one of the two displayed candidates "
                        + "is nonnegative at every index. Both candidates satisfy the degree "
                        + "equation. Vector inequalities are componentwise.")),
                    Paragraph(Text("At a fixed degree the vector is affine in c. At c = 0 its "
                        + "coordinates equal those of p scaled by t/b. Between zero and an admissible "
                        + "coefficient c of either sign, entrywise nonnegativity is preserved. The "
                        + "proof clears denominators in this interpolation. The candidates use the "
                        + "first eligible coefficient on each side of zero.")),
                    Paragraph(Text("Nonnegativity of t is used at the interpolation endpoint. For "
                        + "b = 2, t = −5, p = 1 and u = 1 on a single coordinate, the nearest "
                        + "representatives give −2 and −3, while a = −6 and c = 7 gives 1."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula c = F.Id("c");
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        Formula r = F.Id("r");
        Formula t = F.Id("t");
        Formula u = F.Id("u");

        return Disp(Seq(
            Open, Exists, Sp, a, Comma, Sp, c, Comma, Sp, a, b, Sp, Plus, Sp, c, Sp, Eq, Sp, t,
            Sp, Land, Sp, a, p, Sp, Plus, Sp, c, u, Sp, Geq, Sp, D(0), Close,
            Sp, Iff, Sp,
            Open, q, p, Sp, Plus, Sp, r, u, Sp, Geq, Sp, D(0), Close,
            Sp, Lor, Sp,
            Open, Open, q, Sp, Plus, Sp, D(1), Close, p, Sp, Plus, Sp,
            Open, r, Sp, Minus, Sp, b, Close, u, Sp, Geq, Sp, D(0), Close));
    }
}
