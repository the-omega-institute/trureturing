using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SweepDimension;

internal sealed class SweepBasicDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/boldi2026sweep");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite-poset sweep system has at least as many orders as a maximum three-chain-free set.",
        H("Finite-poset sweep lower bound"),
        Blocks(
            Describe.Lean(DescribeId.Create("three-chain-free"),
                DeclarationHandle.Create("D5/S3/Combinatorics/SweepDimension/Basic.ThreeChainFree"),
                H("Three-chain-free finite subsets"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A finite subset is three-chain-free when it contains no three elements a, b, c with a < b < c. This encodes the no-three-element-chain condition in Boldi–Vigna, Section 4.3, Proposition 3."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("theta"),
                DeclarationHandle.Create("D5/S3/Combinatorics/SweepDimension/Basic.theta"),
                H("Maximum three-chain-free cardinality"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Theta is the maximum cardinality of a three-chain-free subset of the finite poset, as defined in Boldi–Vigna, Section 4.3, Proposition 3. Here the definition also applies to empty and singleton carriers."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("interval"),
                DeclarationHandle.Create("D5/S3/Combinatorics/SweepDimension/Basic.IsInterval"),
                H("Order-convex intervals"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("An interval contains every point between each pair of its points. Empty and full subsets are included. This is the order-convex interval notion of Boldi–Vigna, Section 2."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("convex-hull"),
                DeclarationHandle.Create("D5/S3/Combinatorics/SweepDimension/Basic.convexHull"),
                H("Order-convex hull"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The convex hull of a finite set consists of all points lying between two of its elements. This is the hull used in the proof of Boldi–Vigna, Section 4.3, Proposition 3(2)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("linear-order-relation"),
                DeclarationHandle.Create("D5/S3/Combinatorics/SweepDimension/Basic.LinearOrderRel"),
                H("A carried linear order"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A carried order relation is a binary relation together with a proof that it is a linear order on the carrier."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sweep-system"),
                DeclarationHandle.Create("D5/S3/Combinatorics/SweepDimension/Basic.IsSweepSystem"),
                H("Sweep systems"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A family of k carried linear orders is a sweep system when every order-convex interval and every outside point admit one family order in which the outside point precedes every point of the interval. This formalizes Boldi–Vigna, Definition 1; the orders need not extend the poset order and may repeat."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("theta-witness"),
                DeclarationHandle.Create("D5/S3/Combinatorics/SweepDimension/Basic.theta_witness"),
                H("A maximum three-chain-free subset exists"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Some three-chain-free finite subset has cardinality exactly theta."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("theta-le-of-sweep"),
                DeclarationHandle.Create("D5/S3/Combinatorics/SweepDimension/Basic.theta_le_of_sweep"),
                H("The lower bound for sweep systems"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Boldi–Vigna, Section 4.3, Proposition 3(3), proves theta at most sweep dimension for posets with at least two points, using the convex-hull restriction argument and distinct sweeps. Here the bound is expressed without taking a minimum: for every finite poset and every k-order sweep system, theta is at most k. The repository proof also covers empty and singleton carriers; those boundary cases extend the published statement's scope.")),
                    Paragraph(Text("For a maximum three-chain-free set S and each y in S, the convex hull of S minus y omits y. The sweep condition therefore assigns an order putting y before all other members of S. One order cannot serve two distinct y, so the assignments inject S into the k orders.")),
                    Paragraph(Text("The matching upper construction uses finite chain covers of the product with the two-element chain."))),
                DescribeRole.Theorem)
        )));
}
