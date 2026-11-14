using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Combinatorics;

internal sealed class SweepDimensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite-poset sweep system has at least as many orders as a maximum three-chain-free set.",
        H("Finite-poset sweep lower bound"),
        Blocks(
            Describe.Lean(DescribeId.Create("three-chain-free"),
                DeclarationHandle.Create("D5/S0/Certificates/Combinatorics/SweepDimension.ThreeChainFree"),
                H("Three-chain-free finite subsets"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite subset is three-chain-free when it contains no three elements a, b, c with a < b < c."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("theta"),
                DeclarationHandle.Create("D5/S0/Certificates/Combinatorics/SweepDimension.theta"),
                H("Maximum three-chain-free cardinality"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Theta is the maximum cardinality of a three-chain-free subset of the finite poset."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("interval"),
                DeclarationHandle.Create("D5/S0/Certificates/Combinatorics/SweepDimension.IsInterval"),
                H("Order-convex intervals"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An interval contains every point between each pair of its points. Empty and full subsets are included."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("convex-hull"),
                DeclarationHandle.Create("D5/S0/Certificates/Combinatorics/SweepDimension.convexHull"),
                H("Order-convex hull"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The convex hull of a finite set consists of all points lying between two of its elements."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("linear-order-relation"),
                DeclarationHandle.Create("D5/S0/Certificates/Combinatorics/SweepDimension.LinearOrderRel"),
                H("A carried linear order"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A carried order relation is a binary relation together with a proof that it is a linear order on the carrier."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sweep-system"),
                DeclarationHandle.Create("D5/S0/Certificates/Combinatorics/SweepDimension.IsSweepSystem"),
                H("Sweep systems"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A family of k carried linear orders is a sweep system when every order-convex interval and every outside point admit one family order in which the outside point precedes every point of the interval."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("theta-le-of-sweep"),
                DeclarationHandle.Create("D5/S0/Certificates/Combinatorics/SweepDimension.theta_le_of_sweep"),
                H("The lower bound for sweep systems"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite poset and every k-order sweep system, theta is at most k. For a maximum three-chain-free set S and each y in S, the convex hull of S minus y omits y. The sweep condition therefore assigns an order putting y before all other members of S. One order cannot serve two distinct y, so the assignments inject S into the k orders.")),
                    Paragraph(Text("The matching upper construction and the endpoint classifications require additional finite chain-cover arguments and are outside this declaration."))),
                DescribeRole.Theorem)
        )));
}
