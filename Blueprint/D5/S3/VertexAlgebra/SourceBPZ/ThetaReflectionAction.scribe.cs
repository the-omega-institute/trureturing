using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.SourceBPZ;

internal sealed class ThetaReflectionActionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/SourceBPZ/ThetaReflectionAction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The order-two lattice reflection action, energy-grade equivariance, and fixed-grade coevaluation invariants.",
        H("Theta Reflection Action"),
        Blocks(
            Paragraph(Text(
                "D is the existing arbitrary integral even lattice datum. Carrier D is the original finite-charge oscillator carrier, theta D is the literal charge-and-oscillator reflection, sourcePairing D is the original complex bilinear form, and grade D h intersect fixedSpace D is the existing finite-energy theta-fixed submodule. ReflectionGroup is the additive group ZMod 2. thetaRepHom packages the reflection as an additive homomorphism into the permutation group of Carrier D, so its nonzero element is the reflection.")),
            Law("thetaRep_zero", "Identity element acts trivially",
                "For every D, thetaRep D 0 is the identity linear equivalence of Carrier D."),
            Law("thetaRep_one", "Generator is the lattice theta involution",
                "For every D, thetaRep D 1 is exactly the existing theta D linear equivalence."),
            Law("thetaRep_neg_one", "The reflection is the nontrivial order-two element",
                "For every D, thetaRep D (-1) equals theta D, using the equality -1 = 1 in ZMod 2."),
            Law("thetaRep_pairing", "Reflection preserves the source pairing",
                "For every D, g:ZMod 2 and u,v:Carrier D, sourcePairing D (thetaRep D g u) (thetaRep D g v) = sourcePairing D u v."),
            Law("thetaRep_fixed", "The restricted action on fixed vectors is trivial",
                "For every D, g:ZMod 2 and v in fixedSpace D, thetaRep D g v.val = v.val."),
            Law("coevaluation_fixed_under_reflection", "Fixed-grade coevaluation is reflection invariant",
                "For every D, signed grade h and functional on grade D h intersect fixedSpace D, thetaRep D (-1) applied to the coevaluation value equals that value."),
            Law("thetaRep_preserves_energy_grade", "Reflection preserves every energy grade",
                "For every integer n, a state in grade D n remains in that grade under thetaRep D 1; the basis label (a,e) is sent to (-a,e) with only an oscillator sign."),
            Law("thetaRep_charge_energy_neg", "Charge energy is reflection invariant",
                "For every charge a, chargeEnergy D (-a) = chargeEnergy D a."),
            Law("thetaRep_gradeProjection_commute", "Reflection commutes with the grade projection",
                "For every integer n, thetaRep D 1 commutes with gradeProjection D n, preparing gradewise eigenspaces and twined characters."),
            Paragraph(Text(
                "The representation packages the already proved theta involution and source-pairing isometry; it adds no positivity, nondegeneracy or orbit-representative choice. The coevaluation statement is an algebraic consequence of its fixedSpace codomain. It does not claim a complete lattice vertex algebra, modularity, fusion, or analytic completion."))
        ), []));

    private static DocumentBlock Law(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("theta-reflection-action-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
