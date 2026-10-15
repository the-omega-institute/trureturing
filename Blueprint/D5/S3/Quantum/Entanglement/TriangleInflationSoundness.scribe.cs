using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class TriangleInflationSoundnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/TriangleInflationSoundness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Measurable stochastic triangle responses generate a finite observable law on genuinely independent continuous source copies.",
        H("A continuous source lift for triangle inflation"),
        Blocks(
            Paragraph(Text("Let Copy and Node be finite types. Sources are pairs (e,i), with e in {alpha,beta,gamma} "
                + "and i in Copy. Each coordinate has Lebesgue measure restricted to [0,1], and the common source carrier "
                + "is the full function space from Sources to Real with the finite product measure. "
                + "An inflation specification assigns each node a party v in {A,B,C} and copies of its two incident "
                + "sources: A reads beta,gamma, B reads gamma,alpha, and C reads alpha,beta. "
                + "The source types are fixed by the party, so the specification cannot wire an A node to alpha.")),
            Paragraph(Text("A response model consists of the three measurable nonnegative stochastic responses with four outcomes. "
                + "For a complete observable assignment o, its conditional weight is the product over nodes of the actual "
                + "response probability evaluated on that node's incident source copies. The inflation mass q(o) is "
                + "the integral of this weight over the common continuous product-source carrier. No finite source "
                + "discretization, supplied lifted law, or premise asserting the desired inflation constraints is used.")),
            Describe.Lean(DescribeId.Create("lift-nonnegative"),
                DeclarationHandle.Create(Prefix + "inflationMass_nonnegative"),
                H("Every observable cell has nonnegative mass"),
                StatementSource.FromAuthor(Disp(Call("Nonnegative", Call("InflationMass", F.Id("S"), F.Id("R"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each response is nonnegative. Its finite product remains nonnegative, "
                    + "and integration over the source product measure preserves the inequality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lift-normalized"),
                DeclarationHandle.Create(Prefix + "inflationMass_normalized"),
                H("The lifted observable cells have total mass one"),
                StatementSource.FromAuthor(Disp(Equal(Call("TotalMass", Call("InflationMass", F.Id("S"), F.Id("R"))), F.D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every response lies between zero and one, so each measurable cell weight is integrable. "
                    + "Interchange the finite sum over observable assignments with integration. Finite distributivity "
                    + "turns the sum of conditional product weights into the product of the individual response sums. "
                    + "Every response sum equals one and the continuous source product measure is a probability measure."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-response-witness"),
                DeclarationHandle.Create(Prefix + "isTriangleLocal_responseModel"),
                H("The original local model supplies the responses"),
                StatementSource.FromAuthor(Disp(Call("Implies", Call("IsTriangleLocal", F.Id("p")),
                    Call("ExistsRepresentingResponseModel", F.Id("p"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Unpack the original continuous local-model witness. Its three measurable, "
                    + "nonnegative normalized responses give the response model R, and their original three-source "
                    + "integral is exactly Represents R p. This covers the existing continuous local predicate "
                    + "without adding a finite hidden-variable restriction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-observable-marginals"),
                DeclarationHandle.Create(Prefix + "inflationMass_marginal"),
                H("Summing the unobserved outcomes gives the retained marginal"),
                StatementSource.FromAuthor(Disp(Equal(Call("SumUnobserved", F.Id("q"), F.Id("J"), F.Id("o")),
                    Call("MarginalMass", F.Id("S"), F.Id("R"), F.Id("J"), F.Id("o"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite retained node block J and every assignment o on J, "
                    + "sum q over all extensions on the complement. Split the finite product into retained "
                    + "and unobserved nodes. Normalization of each unobserved response removes its factor, "
                    + "leaving the integral of the retained response product."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("remove-one-observable"),
                DeclarationHandle.Create(Prefix + "marginalMass_sum_insert"),
                H("A retained observable can also be marginalized"),
                StatementSource.FromAuthor(Disp(Equal(Call("SumInsertedOutcome", F.Id("J"), F.Id("v")),
                    Call("MarginalMass", F.Id("S"), F.Id("R"), F.Id("J"), F.Id("o"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When v is outside J, summing the marginal on J union {v} over v's "
                    + "four outcomes gives the marginal on J. The proof uses actual stochastic-response "
                    + "normalization and finite-sum interchange with integration."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("independent-block-factorization"),
                DeclarationHandle.Create(Prefix + "marginalMass_disjoint_source_factorization"),
                H("Blocks using disjoint sources factor"),
                StatementSource.FromAuthor(Disp(Equal(Call("MarginalMass", Call("Union", F.Id("J"), F.Id("K"))),
                    Multiply(Call("MarginalMass", F.Id("J")), Call("MarginalMass", F.Id("K")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Suppose the node blocks J and K are disjoint and their exact incident "
                    + "source supports are disjoint. Product-source coordinate independence gives independence "
                    + "of the two source groups and hence of their measurable response products. Integrating "
                    + "their product yields the product of the two marginal masses. The second factor can be "
                    + "an unknown retained marginal of the same full inflation law."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("continuous-triple-projection"),
                DeclarationHandle.Create(Prefix + "sourceMeasure_map_triangle"),
                H("One source copy of each type has the original continuous law"),
                StatementSource.FromAuthor(Disp(Equal(Call("MapTriangleSources", F.Id("SourceMeasure")),
                    Call("Product", F.Id("UnitSource"), Call("Product", F.Id("UnitSource"), F.Id("UnitSource")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary chosen alpha, beta and gamma copy labels, the triple "
                    + "of their real source coordinates has the product of three uniform [0,1] measures. "
                    + "All unused source copies disappear under this actual measure pushforward; this also "
                    + "permits unequal copy counts embedded in the common finite Copy type."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("admissible-triangle"),
                DeclarationHandle.Create(Prefix + "marginalMass_triangle"),
                H("A correctly wired copied triangle has distribution p"),
                StatementSource.FromAuthor(Disp(Equal(Call("MarginalMass", F.Id("CopiedTriangle")),
                    Call("p", F.Id("a"), F.Id("b"), F.Id("c"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume R represents p. If A reads the chosen beta,gamma copies, "
                    + "B reads gamma,alpha and C reads alpha,beta, their three-node marginal equals p(a,b,c). "
                    + "Project to the three actual source coordinates, reuse the continuous triple law, "
                    + "and recover exactly the original restricted-volume integral."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("admissible-one-party"),
                DeclarationHandle.Create(Prefix + "marginalMass_singleton_A"),
                H("The A-node marginal is the observed one-party marginal"),
                StatementSource.FromAuthor(Disp(Equal(Call("MarginalMass", F.Id("A")),
                    Call("SumBC", F.Id("p"), F.Id("a"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same correctly wired triangle hypotheses, the A-node "
                    + "marginal equals the sum of p(a,b,c) over b and c. Sum out C and then B from the "
                    + "derived triangle marginal; no one-party distribution is supplied as a premise."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("admissible-b-party"),
                DeclarationHandle.Create(Prefix + "marginalMass_singleton_B"),
                H("The B-node marginal is the observed one-party marginal"),
                StatementSource.FromAuthor(Disp(Equal(Call("MarginalMass", F.Id("B")),
                    Call("SumAC", F.Id("p"), F.Id("b"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a correctly wired copied triangle represented by R, the B-node "
                    + "marginal is the sum of p(a,b,c) over a and c. This follows by summing the actual "
                    + "A and C response factors, with no party symmetry assumption."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("admissible-c-party"),
                DeclarationHandle.Create(Prefix + "marginalMass_singleton_C"),
                H("The C-node marginal is the observed one-party marginal"),
                StatementSource.FromAuthor(Disp(Equal(Call("MarginalMass", F.Id("C")),
                    Call("SumAB", F.Id("p"), F.Id("c"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a correctly wired copied triangle represented by R, the C-node "
                    + "marginal is the sum of p(a,b,c) over a and b. Sum out A and B under the same "
                    + "continuous lift; arbitrary raw responses need not be symmetric."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("source-copy-symmetry"),
                DeclarationHandle.Create(Prefix + "inflationMass_copy_symmetry"),
                H("Reindexing identical source copies preserves q"),
                StatementSource.FromAuthor(Disp(Equal(Call("InflationMass", Call("Compose", F.Id("o"), F.Id("pi"))),
                    Call("InflationMass", F.Id("o"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A node permutation pi preserving party labels, paired with a source-coordinate "
                    + "permutation tau carrying both incident sources to those of each permuted node, preserves "
                    + "every observable cell mass. The finite product-source measure is preserved by coordinate "
                    + "reindexing. This is copy symmetry; no symmetry of arbitrary raw party responses is assumed."))),
                DescribeRole.Theorem))));
}
