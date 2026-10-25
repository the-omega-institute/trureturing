using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Sequenceability;

internal sealed class CayleyNumericalConcentrationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original-label numerical Cayley concentration and all structural readouts.",
        H("A numerical stopping condition for arbitrary finite groups"),
        Blocks(Describe.Lean(
            DescribeId.Create("full-numerical-subgroup-concentration"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Sequenceability/"
                + "CayleyNumericalConcentration.exists_subgroup_concentration"),
            H("An embedded dense subgroup with numerical expansion"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                "D5/L/FiniteGroups/bedertbucickravitzmontgomerymuyesser2025cayley")),
            Blocks(
                Paragraph(Text("Let G be any finite group, let S be any nonempty set of "
                    + "original labels, and put sigma=|S|/|G|. For 0<epsilon<1/2 and "
                    + "eta=epsilon sigma^2/1000 the constructed subgroup H retains exactly "
                    + "T=S intersection H, at least (1-epsilon)|S| labels, and has density "
                    + "tau=|T|/|H| at least sigma. For every real mean-zero f on H its "
                    + "directed adjacency quadratic form is at most "
                    + "(1-eta)|T| sum_x f(x)^2. Neither S nor T is required to be symmetric, "
                    + "and H is not required to be normal.")),
                Paragraph(Text("The proof consumes the proper-stabilizer localization "
                    + "theorem from CayleySubgroupConcentration without modifying it. A "
                    + "genuine failure of the numerical bound supplies a nonzero f. Its "
                    + "Euclidean normalization has unit norm and zero mean and supplies "
                    + "every correlation hypothesis at beta=eta. No eigenvector or "
                    + "terminal numerical certificate is supplied as a hypothesis.")),
                Paragraph(Text("At stage j the subgroup stays embedded in the original G. "
                    + "Its exact retained-label count d satisfies "
                    + "(1-epsilon+epsilon/2^j)|S|<=d, and 2^j|H|<=|G|. Stage zero has "
                    + "H=G, so its density equals sigma. Later stages use 2^j>=2 and "
                    + "2 tau>=2^j sigma to retain the density lower bound. The squared "
                    + "bound gives 50 eta/tau^2<=epsilon/2^(j+1). A proper L inside H "
                    + "is mapped through the actual subgroup inclusion into G. An exact "
                    + "label bijection transports its retained count, and the proper "
                    + "subgroup index gives 2|H'|<=|H|. Strong induction on the natural "
                    + "cardinality terminates this loss-controlled descent.")),
                Paragraph(Text("For every ordered partition X,Y of H, centered "
                    + "indicators and the exact ordered labelled edge bijection "
                    + "(x,t) maps to (x,xt) give e_T(X,Y)>=eta tau |X||Y|, and hence "
                    + "e_T(X,Y)>=epsilon sigma^3 |X||Y|/1000. Regular row and column "
                    + "counts also give e_T(X,Y)=e_T(Y,X). Empty parts and identity "
                    + "loops remain included in these identities.")),
                Paragraph(Text("Right-translation reindexing proves that adjacency "
                    + "preserves the complex mean-zero space. Splitting a nonzero "
                    + "complex eigenvector into real and imaginary parts and applying "
                    + "the numerical inequality twice gives Re(lambda)<=(1-eta)|T|. "
                    + "The positive sum of squared real and imaginary coordinates is "
                    + "cancelled only after proving it is positive. This direction of "
                    + "inference remains valid for nonnormal adjacency operators.")),
                Paragraph(Text("For every left coset aH the actual map h maps to ah "
                    + "is bijective, with inverse x maps to a^-1 x. The full edge iff "
                    + "preserves the original colour s in S precisely when s is the "
                    + "image of a label in T. Exact subgroup cardinality and retention "
                    + "give index(H)<=1/((1-epsilon)sigma)<2/sigma. No quotient group "
                    + "or normality is used.")),
                Paragraph(Text("The full theorem's source-owner information audit remains "
                    + "unfinished: the current full-telescope registration is declared_unresolved "
                    + "at source.dictionary_or_proof_coordinate. Its original Group and Fintype "
                    + "dictionaries are required to reconstruct the typed subgroup and retained "
                    + "labels. The kernel-checked family proofs do not supply an accepted source "
                    + "binding. The theorem-specific disclosure is "
                    + "https://github.com/the-omega-institute/trureturing/issues/21393. "
                    + "Neither registration is claimed to be declared_validated.")),
                Paragraph(Text("This is literature-adapted structural mathematics from "
                    + "Section 4 of Bedert, Bucic, Kravitz, Montgomery and Muyesser, "
                    + "arXiv:2508.18254v1, with no novelty claim. Identity labels are "
                    + "allowed here; a rainbow path consumer must separately discharge "
                    + "its own nonidentity and other hypotheses. The result supplies no "
                    + "connector, coupling, absorption, Good or unrestricted AM claim. "
                    + "The original Good and unrestricted AM questions remain open."))),
            DescribeRole.Theorem))));
}
