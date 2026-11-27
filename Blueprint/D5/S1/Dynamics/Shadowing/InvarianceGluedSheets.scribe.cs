using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class InvarianceGluedSheetsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/InvarianceGluedSheets.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact positive expansivity of glued sheets", H("Exact positive expansivity of glued sheets"),
        Blocks(
            Paragraph(Text("Gangloff, Guillon and Oprocha ask which one-dimensional continua admit finitely positively expansive systems in Question 3.2 of arXiv:2310.17241v1. The result below determines the expansion order of the finite-sheet construction over a positively expansive base.")),
            Paragraph(Text("For a nonnegative function on the base, take the graphs of its first N nonnegative integer multiples in the product with the real line. Forward invariance of the zero set makes the maps on the graphs agree. Continuous graph maps paste along their closed overlaps. Surjectivity lifts on each sheet, and the union is compact for continuous height over a compact base.")),
            Describe.Lean(
                DescribeId.Create("glued-sheets-forward-distance"),
                DeclarationHandle.Create(Owner + "dist_iterate_lift"),
                H("Forward distance within a fiber"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At each forward time, two points over one base point are separated by the absolute gap of their sheet labels times the height at the corresponding base iterate. This formula includes the time at which the sheets meet and every later time."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("glued-sheets-exact-expansion-order"),
                DeclarationHandle.Create(Owner + "exact_order_infDist"),
                H("The expansion order is one or N"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let the base be positively expansive, let K be nonempty, compact and forward invariant, and use distance to K as the height. For N at least two there is a positive radius at which each strict forward Bowen ball has at most N points, because it lies in one fiber.")),
                    Paragraph(Text("The graph union is positively expansive exactly when some open neighborhood of K contains an entire forward orbit only if that orbit starts in K. In the complementary case, each positive radius admits a fiber with N distinct points whose forward iterates are all pairwise closer than that radius. The least finite expansion order in this case is N.")),
                    Paragraph(Text("This gives the dynamical criterion for the gluing construction. The one-dimensional continuum classification in Question 3.2 remains open."))),
                DescribeRole.Theorem))));
}
