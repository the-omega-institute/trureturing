using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class NormExactSequenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/GroupAlgebra/NormExactSequence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual unnormalized native coinvariant norm is bijective in the middle of every equivariant short exact sequence when it is bijective at both ends.",
        H("Coinvariant Norms and Equivariant Short Exact Sequences"),
        Blocks(
            Paragraph(Text(
                "R is an arbitrary commutative ring, G is a finite possibly nonabelian group, and A, B, and C are arbitrary modules with independent carrier universes. "
                + "The maps are native Representation.IntertwiningMap maps i : A → B and q : B → C. "
                + "Injectivity of i, surjectivity of q, and range i = ker q are the exactness assumptions; no chosen quotient or abstract replacement of the native coinvariants is introduced.")),
            Describe.Lean(
                DescribeId.Create("intertwining-map-norm"),
                DeclarationHandle.Create(Prefix + "intertwiningMap_norm"),
                H("The finite norm commutes with an equivariant map"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The actual finite sum defining the native representation norm is transported term by term by an equivariant linear map. "
                    + "This is the compatibility used whenever a norm is lifted or pushed through i or q."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coinvariant-kernel-map-le"),
                DeclarationHandle.Create(Prefix + "coinvariants_ker_map_le"),
                H("Equivariance maps the native difference span into the target"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The native Coinvariants.ker is the span of all differences g • v − v. "
                    + "An equivariant map sends each such generator to a target difference, so the mapped source span lies in the target span."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coinvariant-kernel-map-surjective"),
                DeclarationHandle.Create(Prefix + "coinvariants_ker_map_eq_of_surjective"),
                H("Surjectivity lifts the whole difference span"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When an equivariant map is surjective, lift the representative of each target difference generator and use the native span universal property. "
                    + "Together with the previous inclusion this identifies the mapped source difference span with the target one, without splitting the coefficient module or the representation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coinvariants-norm-short-exact"),
                DeclarationHandle.Create(Prefix + "coinvariantsNorm_bijective_of_shortExact"),
                H("Bijectivity of the actual norm is extension closed"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume the actual native coinvariant norms of A and C are bijective. "
                        + "For injectivity in B, represent a difference of two coinvariant classes, use the quotient norm to show its q-image is a native difference, lift that difference through the surjective span statement, and use exactness to land in i(A). "
                        + "The kernel norm hypothesis then forces the remaining A representative into the source difference span.")),
                    Paragraph(Text(
                        "For surjectivity in B, first take a norm preimage of the invariant q-image in C. "
                        + "Subtract its norm lift; exactness supplies an A representative. The invariance of that representative follows by applying injectivity of i to the equivariance equation. "
                        + "A norm preimage in A then combines with the quotient lift to produce the desired native coinvariant class in B.")),
                    Paragraph(Text(
                        "Every step uses the actual finite-sum norm and the native Coinvariants.mk and Coinvariants.ker/map constructions. "
                        + "No coefficient splitting, projectivity, finite generation, dimension, semilinearity, or group commutativity is assumed. "
                        + "The result concerns extension closure of the actual norm only; it does not assert that a global conjugation-trace-one endomorphism is extension closed. "
                        + "Finite arithmetic checks at trace-one extension bounds are separate evidence and are not formalized here; no full filtration or jet principal-unit application is claimed."))),
                DescribeRole.Theorem))));
}
