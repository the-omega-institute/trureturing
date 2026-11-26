using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Orbifold;

internal sealed class OriginalOrbifoldNormFourCharacterDocument : IScribeDocumentDefinition
{
    private const string VertexAlgebra = "D5/S3/VertexAlgebra/";
    private const string TwistedGround = VertexAlgebra + "TwistedGround/";
    private const string Orbifold = TwistedGround + "Orbifold/";
    private const string Prefix = Orbifold + "OriginalOrbifoldNormFourCharacter.";
    private const string ChargeCharacter = VertexAlgebra + "Lattice/NormFourPeirceInvolution.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The norm-four character on the original orbifold",
        H("The norm-four character on the original orbifold"),
        Blocks(
            Paragraph(Text("Let D be lattice data with hu : IsUnit D.G.det, a : Charge D and s : ℂ. "
                + "Write B for bilinear D and C for the original fixed and negative twisted carrier. "),
                Ref(Orbifold + "OriginalOrbifoldField.Carrier")),
            Describe.Lean(DescribeId.Create("character"), DeclarationHandle.Create(Prefix + "character"),
                H("Block action on the original carrier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The endomorphism A applies the charge character to the fixed sector "
                    + "and inserts (−s) times the lifted ground action in the negative twisted sector. "
                    + "On opposite charges the character phases agree, so the character commutes with reflection. "
                    + "The ground insertion commutes with the oscillator parity operator. "),
                    Ref(ChargeCharacter + "chi_single"))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("character-involutive"),
                DeclarationHandle.Create(Prefix + "character_involutive"),
                H("The normalized action is involutive"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If B(a,a) = 4 and s² = 1, then A(Ax) = x for every x in C. "
                    + "The charge character is involutive, and the norm-four ground action squares "
                    + "to the identity. Tensor insertion preserves the square, and (−s)² = 1. "),
                    Ref(ChargeCharacter + "chi_involutive"), Text(", "),
                    Ref(VertexAlgebra + "HalfFock/NormFourLowestGrades.ground_square"))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("symmetry"), DeclarationHandle.Create(Prefix + "symmetry"),
                H("Linear equivalence on the original carrier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the norm and sign hypotheses, the forward and inverse maps "
                    + "of S : C ≃ₗ[ℂ] C both apply A. "), Ref(Prefix + "character_involutive"))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fixed-source-modes"),
                DeclarationHandle.Create(Prefix + "Y_fixed_character"),
                H("All modes with a fixed source"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)) and "
                    + "write Y for Y D hu hD. For every n : ℤ, u : FixedCarrier D and v : C, "
                    + "A(Y((u, 0))[n] v) = Y(A((u, 0)))[n](Av). The fixed mode uses charge-character "
                    + "covariance and the negative twisted mode uses corrected-field covariance "
                    + "at coefficient 2(−n−1). "),
                    Ref(Orbifold + "OriginalOrbifoldField.Y_fixed_ncoeff_apply"), Text(", "),
                    Ref(ChargeCharacter + "stateField_chi"), Text(", "),
                    Ref(VertexAlgebra + "HalfFock/LatticeHalfFockGroundCharacter.correctedField_ground_character"))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("all-state-mode-covariance"),
                DeclarationHandle.Create(Prefix + "Y_character"),
                H("Intertwining every mode on the original carrier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume hD as above, D.rank = 24, B(a,a) = 4 and s² = 1. "
                        + "For every n : ℤ and all u, v : C, S(Y(u)[n] v) = Y(Su)[n](Sv) "
                        + "at the original normalized mode n.")),
                    Paragraph(Text("The signed insertion commutes with twisted translation, which is "
                        + "the zero mode of the neutral stress state. It therefore commutes with the "
                        + "powers of translation in the original right coefficient. The injective "
                        + "insertion carries the sum to the transformed sum term by term. "),
                        Ref(TwistedGround + "OriginalRightSkew.originalRightCoefficient")),
                    Paragraph(Text("The source pairing pairs opposite charges. The twisted pairing is "
                        + "invariant under the simultaneous signed insertion, by ground pairing "
                        + "invariance and (−s)² = 1. The insertion preserves twisted energy and commutes "
                        + "with L(1). Together with corrected-field covariance these facts preserve "
                        + "each summand of the normalized coefficient on homogeneous inputs. "),
                        Ref(TwistedGround + "MixedIntertwiner.normalizedCoefficient_pairing")),
                    Paragraph(Text("Evaluation of the fixed-grade pairing recovers the homogeneous "
                        + "functional and identifies the transformed output. The finite homogeneous "
                        + "tensor tests extend the identity to both arbitrary twisted inputs. "
                        + "The four blocks then give covariance on C. "),
                        Ref(TwistedGround + "OriginalFourMCoefficients.originalI_homogeneous"), Text(", "),
                        Ref(TwistedGround + "OriginalFourMContraction.sourceGradePairingEquiv_evaluation"),
                        Text(", "), Ref(TwistedGround + "OriginalFourMInputs.input_trilinear_ext"),
                        Text(", "), Ref(Prefix + "Y_fixed_character"),
                        Text(", "), Ref(Orbifold + "OriginalOrbifoldField.Y_ncoeff_apply"))),
                DescribeRole.Theorem))));
}
