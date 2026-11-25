using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class FiniteTableCalibrationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Attribution/FiniteTableCalibration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite deterministic tables carry the marginals and fixed mass of equivariant calibrations.",
        H("Probability laws on deterministic readout tables"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("calibration-table-law"),
                DeclarationHandle.Create(Prefix + "calibration_table_law"),
                H("Push a finite calibration to its table law"),
                StatementSource.FromAuthor(Pushforward()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let a group G act on X and Y, with decidable equality on Y "
                        + "and a finite table type from X to Y. Give the tables the action that "
                        + "applies the inverse group element to the input and the group element "
                        + "to the output. Let G also act on a finite seed type S. The weights a on "
                        + "S are nonnegative and have sum one. The function f takes an input and "
                        + "a seed to an output. It commutes with the actions, and every kernel "
                        + "entry P(x,y) equals the sum of a over seeds returning y at x.")),
                    Paragraph(Text("The table law p assigns each table the sum of the weights of "
                        + "seeds giving that entire table. TableLawProperties means that p is "
                        + "nonnegative and sums to one, that G-invariance of a implies "
                        + "G-invariance of p, and that the sum of p over tables giving y at x "
                        + "equals P(x,y) for every x,y. The total weight of seeds fixed by the "
                        + "whole group is at most the total weight of tables fixed by the whole group.")),
                    Paragraph(Text("The table map is equivariant by covariance of f. Summing over "
                        + "its fibers gives the marginal and normalization identities. Equivariance "
                        + "maps fixed seeds into fixed tables and allows reindexing the pushforward "
                        + "by a group element when the weights are invariant."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-table-calibration"),
                DeclarationHandle.Create(Prefix + "positive_table_calibration"),
                H("Realize a table law on its positive support"),
                StatementSource.FromAuthor(Attainment()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let G act on X and Y in universes v and w, with decidable "
                        + "equality on Y and a finite enumeration of the table type. Let H be a "
                        + "subgroup of G. InvariantTableLaw means that p is a nonnegative "
                        + "G-invariant function on tables with sum one and that the sum of p "
                        + "over tables giving y at x equals P(x,y) for every x,y.")),
                    Paragraph(Text("The result supplies a finite seed type U in the maximum of "
                        + "v and w with a G-action, a real weight function q, and a readout f "
                        + "from X times U to Y. PositiveCalibration means that the weights are "
                        + "strictly positive, sum to one and are invariant under G. The readout "
                        + "commutes with G, and every P(x,y) is the total weight of seeds giving y "
                        + "at x. FixedMass uses the total weight fixed by every element of H.")),
                    Paragraph(Text("The positive-weight tables are stable under the action. "
                        + "Use them as seeds and evaluate the table at the input. Every "
                        + "discarded table has zero weight, so normalization, every marginal "
                        + "and the subgroup-fixed mass all survive the restriction."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Pushforward()
    {
        Formula g = F.Id("G");
        Formula a = F.Id("a");
        Formula f = F.Id("f");
        Formula p = Apply("TableLaw", a, f);
        return Disp(Seq(Apply("Calibration", g, F.Id("P"), a, f), Sp, Rightarrow, Sp,
            Apply("TableLawProperties", g, F.Id("P"), a, p), Sp, Land, Sp,
            Apply("FixedMass", g, a), Sp, Le, Sp, Apply("FixedMass", g, p)));
    }

    private static Formula Attainment()
    {
        Formula g = F.Id("G");
        Formula h = F.Id("H");
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        Formula f = F.Id("f");
        Formula u = F.Id("U");
        Formula kernel = F.Id("P");
        return Disp(Seq(Apply("InvariantTableLaw", g, kernel, p), Sp, Rightarrow, Sp,
            Exists, Sp, u, Comma, Sp, q, Comma, Sp, f, Comma, Sp,
            Apply("PositiveCalibration", g, kernel, u, q, f), Sp, Land, Sp,
            Apply("FixedMass", h, q), Eq, Apply("FixedMass", h, p)));
    }
}
